//! Dedicated immutable memory for column buffers. Heap pages are never protected, because allocator metadata on the
//! same pages must stay writable. A buffer is either copied once into its own anonymous mapping or mapped from an
//! immutable prepared file; projections and later executions share it.

use super::error::{Result, StorageIoError};
use std::{os::fd::AsRawFd, path::Path, ptr::NonNull};

pub struct ReadOnlyBuffer {
    pointer: NonNull<u8>,
    /// Mapped length. An empty buffer still maps one byte, so `pointer` is never dangling.
    len: usize,
    file_backed: bool,
}

// SAFETY: the mapping is PROT_READ for its whole lifetime; no thread can write through it.
unsafe impl Send for ReadOnlyBuffer {}
unsafe impl Sync for ReadOnlyBuffer {}

impl ReadOnlyBuffer {
    /// Copy `bytes` into a private anonymous mapping, then make it read-only.
    pub fn copy(bytes: &[u8]) -> Result<Self> {
        let len = bytes.len().max(1);
        // SAFETY: a fresh anonymous mapping, not aliased by anything else.
        let pointer = unsafe {
            libc::mmap(
                std::ptr::null_mut(),
                len,
                libc::PROT_READ | libc::PROT_WRITE,
                libc::MAP_PRIVATE | libc::MAP_ANONYMOUS,
                -1,
                0,
            )
        };
        if pointer == libc::MAP_FAILED {
            return Err(StorageIoError::Memory(std::io::Error::last_os_error()));
        }
        // SAFETY: `pointer` maps at least `bytes.len()` writable bytes that do not overlap `bytes`.
        unsafe { std::ptr::copy_nonoverlapping(bytes.as_ptr(), pointer.cast::<u8>(), bytes.len()) };
        if unsafe { libc::mprotect(pointer, len, libc::PROT_READ) } != 0 {
            let error = std::io::Error::last_os_error();
            unsafe { libc::munmap(pointer, len) };
            return Err(StorageIoError::Memory(error));
        }
        Ok(Self {
            pointer: NonNull::new(pointer.cast()).expect("mmap never returns null on success"),
            len,
            file_backed: false,
        })
    }

    /// Map an immutable prepared file read-only and shared, so isolated workers share its page cache. Only the file
    /// length is checked against `expected_bytes`; the contents are not read eagerly (pages are read when touched).
    pub fn map_file(path: &Path, expected_bytes: usize) -> Result<Self> {
        let file = std::fs::File::open(path).map_err(StorageIoError::file(path))?;
        let actual = file.metadata().map_err(StorageIoError::file(path))?.len();
        if actual != expected_bytes as u64 {
            return Err(StorageIoError::archive(path, "prepared buffer file extent differs"));
        }
        if expected_bytes == 0 {
            return Self::copy(&[]);
        }
        // SAFETY: a read-only shared mapping of a regular file of exactly `expected_bytes` bytes.
        let pointer = unsafe {
            libc::mmap(
                std::ptr::null_mut(),
                expected_bytes,
                libc::PROT_READ,
                libc::MAP_SHARED,
                file.as_raw_fd(),
                0,
            )
        };
        if pointer == libc::MAP_FAILED {
            return Err(StorageIoError::Memory(std::io::Error::last_os_error()));
        }
        Ok(Self {
            pointer: NonNull::new(pointer.cast()).expect("mmap never returns null on success"),
            len: expected_bytes,
            file_backed: true,
        })
    }

    pub fn as_ptr(&self) -> *const u8 {
        self.pointer.as_ptr()
    }
    pub fn len(&self) -> usize {
        self.len
    }
    pub fn is_empty(&self) -> bool {
        self.len == 0
    }
    pub fn is_file_backed(&self) -> bool {
        self.file_backed
    }

    /// Advise the kernel that this file mapping is read randomly (`madvise(MADV_RANDOM)`): a page fault then reads
    /// that page without readahead, so pages no code touches are not read from the device on its behalf. Advice only;
    /// it changes no content. An anonymous buffer is left as it is.
    pub fn advise_random_access(&self) -> Result<()> {
        if !self.file_backed {
            return Ok(());
        }
        // SAFETY: advice on exactly the region mapped at construction.
        if unsafe { libc::madvise(self.pointer.as_ptr().cast(), self.len, libc::MADV_RANDOM) } != 0 {
            return Err(StorageIoError::Memory(std::io::Error::last_os_error()));
        }
        Ok(())
    }
    /// Whether `[pointer, pointer + len)` lies inside this buffer.
    pub(crate) fn contains(&self, pointer: *const u8, len: usize) -> bool {
        let start = self.as_ptr() as usize;
        let address = pointer as usize;
        address >= start && address.checked_add(len).is_some_and(|end| end <= start + self.len)
    }
}

impl Drop for ReadOnlyBuffer {
    fn drop(&mut self) {
        // SAFETY: unmaps exactly the region mapped at construction.
        unsafe { libc::munmap(self.pointer.as_ptr().cast(), self.len) };
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn read_only_mapping_rejects_native_writes() {
        let mapping = ReadOnlyBuffer::copy(&[11, 22, 33]).unwrap();
        assert_eq!(unsafe { *mapping.as_ptr().add(1) }, 22);
        // The child makes no allocation or lock call after fork.
        let pid = unsafe { libc::fork() };
        assert!(pid >= 0);
        if pid == 0 {
            unsafe {
                let limit = libc::rlimit {
                    rlim_cur: 0,
                    rlim_max: 0,
                };
                libc::setrlimit(libc::RLIMIT_CORE, &limit);
                std::ptr::write_volatile(mapping.as_ptr().cast_mut(), 99);
                libc::_exit(0);
            }
        }
        let mut status = 0;
        assert_eq!(unsafe { libc::waitpid(pid, &mut status, 0) }, pid);
        assert!(libc::WIFSIGNALED(status));
        assert_eq!(libc::WTERMSIG(status), libc::SIGSEGV);
        assert_eq!(unsafe { *mapping.as_ptr() }, 11);
    }
}
