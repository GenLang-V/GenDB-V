//! Stored representation parts: the typed arrays a representation builder produced, written once as read-only files
//! straight from the builder's buffers, and mapped read-only by later executions.
//!
//! Directory format: `part-NNNN.bin` holds part `NNNN` as `len` elements of its element type, with no header;
//! `parts.json` is the [`PartsManifest`]. Every file is created new and then made read-only (mode 0444).
//! `parts.json` is written LAST: it is the commit point, and a directory without it is never mapped.
//!
//! - Format 1 (saved v3 assets, unchanged from the earlier version's `execution_runtime::verus_abi`): host-order elements;
//!   `{"format_version":1,"parts":[["i128",6001215],…],"storage_bytes":…}`. Every saved asset was written on this
//!   little-endian x86-64 host.
//! - Format 2 (storage assets): little-endian elements, stated as `"byte_order":"little"`. Elements are written in
//!   host order, so a format-2 writer is refused on a host that is not little-endian BEFORE any file is written, and
//!   a format-2 directory is mapped only on a little-endian host.
//!
//! Opening a directory for execution reads its manifest and maps the part files; it does not eagerly read or decode
//! part payload (pages are read when code touches them). Optional kernel advice ([`PartAccess`]) is explicit per
//! caller and never a global cache flush.
//!
//! **Free-space reserve.** Every part and manifest write keeps [`STORAGE_MARGIN_BYTES`] free on the filesystem of the
//! directory: bytes are written in chunks of at most [`RESERVE_CHECK_BYTES`], and before each chunk the writer reads the
//! filesystem's free bytes (`statvfs`, one call per chunk, never per row) and refuses the write
//! ([`StorageIoError::StorageReserve`]) if that chunk would leave less than the reserve free. The caller removes the
//! partial directory as for any failed build. The reserve protects the shared device; it is not a size budget of the
//! stored format: a build of any size proceeds while the reserve holds. Race limits: the free figure is the whole
//! filesystem's, so concurrent writers (other builds, other processes) are seen at their next check, but between two
//! checks each writer can consume up to one chunk of the reserve, and an unrelated process can consume any amount;
//! the kernel's own `ENOSPC` stays the final bound. An unreadable free figure refuses nothing.
//!
//! Trusted: file writes and reads, the OS mapping, advice and `statvfs` calls. The contents are never hashed or
//! rescanned; a mapping checks only each file's length against the manifest.

use super::error::{Result, StorageIoError};
use super::read_only::ReadOnlyBuffer;
use serde::{Deserialize, Serialize};
use std::fs;
use std::io::Write;
use std::os::fd::AsRawFd;
use std::os::unix::fs::PermissionsExt;
use std::path::{Path, PathBuf};

const MANIFEST_FILE: &str = "parts.json";
/// Upper bound on `parts.json`, checked before it is read.
const MANIFEST_LIMIT_BYTES: u64 = 1024 * 1024;
const HOST_IS_LITTLE_ENDIAN: bool = cfg!(target_endian = "little");
/// Free bytes every stored-parts write keeps on its filesystem (see the module documentation); also the margin the
/// asset build guard requires before a build (`gendb_verification::admission::storage`).
pub const STORAGE_MARGIN_BYTES: u64 = 4 << 30;
/// Most bytes written between two free-space checks.
pub const RESERVE_CHECK_BYTES: usize = 64 << 20;

/// Element type of one part. `code` is the element code of the Verus ABI part descriptor; the framework shims
/// (`runtime/verus/`, `PART_*`) decode the same codes.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum PartElem {
    I8,
    I16,
    I32,
    I64,
    I128,
    U8,
    U16,
    U32,
    U64,
}

impl PartElem {
    pub const ALL: [Self; 9] = [
        Self::I8,
        Self::I16,
        Self::I32,
        Self::I64,
        Self::I128,
        Self::U8,
        Self::U16,
        Self::U32,
        Self::U64,
    ];

    pub fn code(self) -> u32 {
        match self {
            Self::I8 => 1,
            Self::I16 => 2,
            Self::I32 => 3,
            Self::I64 => 4,
            Self::I128 => 5,
            Self::U8 => 6,
            Self::U16 => 7,
            Self::U32 => 8,
            Self::U64 => 9,
        }
    }

    pub fn from_code(code: u32) -> Option<Self> {
        Self::ALL.into_iter().find(|elem| elem.code() == code)
    }

    /// Bytes per element.
    pub fn width(self) -> usize {
        match self {
            Self::I8 | Self::U8 => 1,
            Self::I16 | Self::U16 => 2,
            Self::I32 | Self::U32 => 4,
            Self::I64 | Self::U64 => 8,
            Self::I128 => 16,
        }
    }

    /// Byte length of `len` elements.
    pub fn extent(self, len: usize) -> Result<usize> {
        len.checked_mul(self.width()).ok_or(StorageIoError::Overflow("part extent"))
    }
}

/// Byte order of the elements of a format-2 parts directory.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum ByteOrder {
    Little,
}

/// The format a [`PartFilesWriter`] writes.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PartsFormat {
    /// Format 1: the saved v3 form (host order, no byte-order field).
    SavedV3,
    /// Format 2: little-endian elements, stated in the manifest.
    LittleEndian,
}

impl PartsFormat {
    fn version(self) -> u32 {
        match self {
            Self::SavedV3 => 1,
            Self::LittleEndian => 2,
        }
    }

    fn byte_order(self) -> Option<ByteOrder> {
        match self {
            Self::SavedV3 => None,
            Self::LittleEndian => Some(ByteOrder::Little),
        }
    }
}

/// `parts.json`: the format, every part's element type and element count in part order, and the total stored bytes.
/// `byte_order` is present exactly in format 2 (so a format-1 manifest keeps its saved bytes).
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct PartsManifest {
    pub format_version: u32,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub byte_order: Option<ByteOrder>,
    pub parts: Vec<(PartElem, u64)>,
    pub storage_bytes: u64,
}

impl PartsManifest {
    /// Refuse a manifest whose format and byte order are not one of the two formats, or whose byte order is not this
    /// host's.
    fn check_format(&self, path: &Path) -> Result<()> {
        match (self.format_version, self.byte_order) {
            (1, None) => Ok(()),
            (2, Some(ByteOrder::Little)) if HOST_IS_LITTLE_ENDIAN => Ok(()),
            (2, Some(ByteOrder::Little)) => Err(StorageIoError::archive(path, "little-endian parts on a host of another byte order")),
            _ => Err(StorageIoError::archive(path, "parts manifest format or byte order differs")),
        }
    }
}

fn part_file(directory: &Path, index: usize) -> PathBuf {
    directory.join(format!("part-{index:04}.bin"))
}

/// Bytes available to an unprivileged writer on the filesystem of `path` (`statvfs`); `None` when unreadable.
pub fn free_bytes_at(path: &Path) -> Option<u64> {
    let c_path = std::ffi::CString::new(path.as_os_str().as_encoded_bytes()).ok()?;
    let mut stat: libc::statvfs = unsafe { std::mem::zeroed() };
    // SAFETY: `c_path` is a NUL-terminated path and `stat` a writable statvfs record for the call's duration.
    (unsafe { libc::statvfs(c_path.as_ptr(), &mut stat) } == 0).then(|| stat.f_bavail * stat.f_frsize)
}

/// The free-space reserve of one writer: `bytes` stay free on the filesystem, read by `free_bytes` before every chunk
/// of at most `chunk_bytes` (the module documentation).
#[derive(Clone, Copy)]
struct SpaceReserve {
    bytes: u64,
    chunk_bytes: usize,
    free_bytes: fn(&Path) -> Option<u64>,
}

impl SpaceReserve {
    const FILESYSTEM: Self = Self { bytes: STORAGE_MARGIN_BYTES, chunk_bytes: RESERVE_CHECK_BYTES, free_bytes: free_bytes_at };

    /// Refuse writing `len` more bytes under `directory` when that would leave less than the reserve free.
    fn check(&self, directory: &Path, len: usize) -> Result<()> {
        match (self.free_bytes)(directory) {
            Some(free) if free < self.bytes.saturating_add(len as u64) => {
                Err(StorageIoError::StorageReserve { path: directory.to_owned(), free, reserve: self.bytes, write: len as u64 })
            }
            _ => Ok(()),
        }
    }

    /// Copy the file `from` (`bytes` long) into the new file `to` in checked chunks and make it read-only (mode 0444).
    fn copy_read_only_file(&self, directory: &Path, from: &Path, to: &Path, bytes: usize) -> Result<()> {
        use std::io::Read;
        let mut source = fs::File::open(from).map_err(StorageIoError::file(from))?;
        let mut file = fs::OpenOptions::new().create_new(true).write(true).open(to).map_err(StorageIoError::file(to))?;
        let mut buffer = vec![0u8; self.chunk_bytes.min(bytes.max(1))];
        let mut left = bytes;
        while left > 0 {
            let chunk = left.min(buffer.len());
            self.check(directory, chunk)?;
            source.read_exact(&mut buffer[..chunk]).map_err(StorageIoError::file(from))?;
            file.write_all(&buffer[..chunk]).map_err(StorageIoError::file(to))?;
            left -= chunk;
        }
        fs::set_permissions(to, fs::Permissions::from_mode(0o444)).map_err(StorageIoError::file(to))
    }

    /// Write the new file `path` in checked chunks and make it read-only (mode 0444).
    fn write_read_only_file(&self, directory: &Path, path: &Path, contents: &[u8]) -> Result<()> {
        let mut file = fs::OpenOptions::new().create_new(true).write(true).open(path).map_err(StorageIoError::file(path))?;
        for chunk in contents.chunks(self.chunk_bytes) {
            self.check(directory, chunk.len())?;
            file.write_all(chunk).map_err(StorageIoError::file(path))?;
        }
        fs::set_permissions(path, fs::Permissions::from_mode(0o444)).map_err(StorageIoError::file(path))
    }
}

/// How [`PartFilesWriter::add_file_part`] placed a part.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum PartPlacement {
    /// A hard link to the source file: one inode, its bytes shared.
    HardLink,
    /// A byte copy of the source file (it lies on another filesystem).
    Copy,
}

/// Writes the parts of one build into a new directory, one part at a time, straight from the caller's buffer (no
/// host copy), keeping the filesystem's free-space reserve (the module documentation). Nothing exists on disk until
/// the first part or [`Self::finish`]; dropping the writer without `finish` leaves no manifest, so the directory (if
/// any part was written) is never mapped.
pub struct PartFilesWriter {
    directory: PathBuf,
    manifest: PartsManifest,
    created: bool,
    reserve: SpaceReserve,
}

impl PartFilesWriter {
    /// A writer of the new directory `directory`. Refused before anything is written when the directory exists, or
    /// when `format` states a byte order this host does not have.
    pub fn new(directory: &Path, format: PartsFormat) -> Result<Self> {
        Self::with_reserve(directory, format, SpaceReserve::FILESYSTEM)
    }

    fn with_reserve(directory: &Path, format: PartsFormat, reserve: SpaceReserve) -> Result<Self> {
        if format == PartsFormat::LittleEndian && !HOST_IS_LITTLE_ENDIAN {
            return Err(StorageIoError::archive(directory, "little-endian parts cannot be written on this host"));
        }
        if directory.exists() {
            return Err(StorageIoError::archive(directory, "stored parts directory already exists"));
        }
        let manifest =
            PartsManifest { format_version: format.version(), byte_order: format.byte_order(), parts: vec![], storage_bytes: 0 };
        Ok(Self { directory: directory.to_owned(), manifest, created: false, reserve })
    }

    /// Parts written so far.
    pub fn part_count(&self) -> usize {
        self.manifest.parts.len()
    }

    /// Write the next part: `bytes` must be exactly `len` host-order elements of `elem`.
    pub fn write_part(&mut self, elem: PartElem, len: usize, bytes: &[u8]) -> Result<()> {
        if bytes.len() != elem.extent(len)? {
            return Err(StorageIoError::Shape("part byte extent differs"));
        }
        let storage_bytes = self.manifest.storage_bytes.checked_add(bytes.len() as u64).ok_or(StorageIoError::Overflow("stored bytes"))?;
        self.create_directory()?;
        self.reserve.write_read_only_file(&self.directory, &part_file(&self.directory, self.part_count()), bytes)?;
        self.manifest.parts.push((elem, len as u64));
        self.manifest.storage_bytes = storage_bytes;
        Ok(())
    }

    /// Link every part of the committed parts directory `source` (its `parts.json` read, nothing else) as the next parts
    /// of this directory: hard links to the source's read-only part files, so their bytes are shared, never copied or
    /// read (the inherited parts of a storage built from an admitted one). Both directories must be on one filesystem
    /// and of the same format.
    pub fn link_parts_of(&mut self, source: &Path) -> Result<()> {
        let manifest = read_manifest(&source.join(MANIFEST_FILE))?;
        if (manifest.format_version, manifest.byte_order) != (self.manifest.format_version, self.manifest.byte_order) {
            return Err(StorageIoError::archive(source, "linked parts have another format or byte order"));
        }
        self.create_directory()?;
        for (index, &(elem, len)) in manifest.parts.iter().enumerate() {
            let from = part_file(source, index);
            let bytes = elem.extent(usize::try_from(len).map_err(|_| StorageIoError::Overflow("part extent"))?)? as u64;
            if fs::metadata(&from).map_err(StorageIoError::file(&from))?.len() != bytes {
                return Err(StorageIoError::archive(source, "linked part file length differs from its manifest"));
            }
            let to = part_file(&self.directory, self.part_count());
            fs::hard_link(&from, &to).map_err(StorageIoError::file(&to))?;
            self.manifest.parts.push((elem, len));
            self.manifest.storage_bytes = self.manifest.storage_bytes.checked_add(bytes).ok_or(StorageIoError::Overflow("stored bytes"))?;
        }
        Ok(())
    }

    /// Add the next part from the existing file `source`, which must hold exactly `len` little-endian elements of `elem`
    /// with no header (the part file format, and the format of a capture's canonical column files): a hard link to the
    /// resolved file (symbolic links followed; its bytes are shared, never read), or, only when that file is on another
    /// filesystem, a byte copy written in reserve-checked chunks and made read-only. The file must be a read-only
    /// regular file of exactly that length (metadata only; contents are not read for a link and not interpreted for a
    /// copy). This writer must write the little-endian format.
    pub fn add_file_part(&mut self, elem: PartElem, len: usize, source: &Path) -> Result<PartPlacement> {
        if self.manifest.byte_order != Some(ByteOrder::Little) {
            return Err(StorageIoError::archive(source, "file parts need the little-endian parts format"));
        }
        let resolved = source.canonicalize().map_err(StorageIoError::file(source))?;
        let metadata = fs::metadata(&resolved).map_err(StorageIoError::file(&resolved))?;
        let bytes = elem.extent(len)?;
        if !metadata.is_file() || metadata.len() != bytes as u64 {
            return Err(StorageIoError::archive(&resolved, "part source is not a regular file of the part's byte extent"));
        }
        if metadata.permissions().mode() & 0o222 != 0 {
            return Err(StorageIoError::archive(&resolved, "part source is writable; only read-only files are shared as parts"));
        }
        let storage_bytes = self.manifest.storage_bytes.checked_add(bytes as u64).ok_or(StorageIoError::Overflow("stored bytes"))?;
        self.create_directory()?;
        let to = part_file(&self.directory, self.part_count());
        let placement = match fs::hard_link(&resolved, &to) {
            Ok(()) => PartPlacement::HardLink,
            Err(e) if e.raw_os_error() == Some(libc::EXDEV) => {
                self.reserve.copy_read_only_file(&self.directory, &resolved, &to, bytes)?;
                PartPlacement::Copy
            }
            Err(e) => return Err(StorageIoError::File { path: to, source: e }),
        };
        self.manifest.parts.push((elem, len as u64));
        self.manifest.storage_bytes = storage_bytes;
        Ok(placement)
    }

    /// Write `parts.json` (the commit point) and return the manifest.
    pub fn finish(mut self) -> Result<PartsManifest> {
        self.create_directory()?;
        let path = self.directory.join(MANIFEST_FILE);
        let encoded = serde_json::to_vec(&self.manifest).map_err(StorageIoError::json(&path))?;
        self.reserve.write_read_only_file(&self.directory, &path, &encoded)?;
        Ok(self.manifest)
    }

    /// Create the directory once; an existing one is refused (parts are written once).
    fn create_directory(&mut self) -> Result<()> {
        if self.created {
            return Ok(());
        }
        if let Some(parent) = self.directory.parent() {
            fs::create_dir_all(parent).map_err(StorageIoError::file(parent))?;
        }
        fs::create_dir(&self.directory).map_err(StorageIoError::file(&self.directory))?;
        self.created = true;
        Ok(())
    }
}

/// Kernel advice for mapping a parts directory. Both are advice, explicit per caller, recorded by the caller.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct PartAccess {
    pub read_advice: ReadAdvice,
    /// Before mapping, `posix_fadvise(POSIX_FADV_DONTNEED)` on every part file of this directory: asks the kernel to
    /// drop their clean cached pages. Pages still mapped or dirty elsewhere and device caches can stay, so it is no
    /// proof of a cold cache; it never touches other files (no global flush).
    pub drop_cached_pages: bool,
}

/// Readahead advice for the part mappings.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum ReadAdvice {
    /// The kernel's default readahead.
    #[default]
    Normal,
    /// `madvise(MADV_RANDOM)` on every part mapping: no readahead around touched pages (so selective reads are not
    /// hidden by it; sequential scans lose it too).
    Random,
}

/// One mapped part: element type, element count and the start of its read-only mapping.
#[derive(Clone, Copy, Debug)]
pub struct MappedPart {
    pub elem: PartElem,
    pub len: u64,
    /// Valid while the owning [`MappedPartFiles`] is alive.
    pub data: *const u8,
}

/// The read-only mappings of a stored parts directory. Every [`MappedPart::data`] pointer borrows a mapping owned
/// here, so the owner must outlive every use of those pointers.
pub struct MappedPartFiles {
    manifest: PartsManifest,
    buffers: Vec<ReadOnlyBuffer>,
}

impl MappedPartFiles {
    /// Read `parts.json` and map each part file read-only and shared, after checking its length against the manifest,
    /// applying `access` first. No part payload is read eagerly.
    pub fn open(directory: &Path, access: &PartAccess) -> Result<Self> {
        let manifest = read_manifest(&directory.join(MANIFEST_FILE))?;
        let buffers = manifest
            .parts
            .iter()
            .enumerate()
            .map(|(index, (elem, len))| {
                let len = usize::try_from(*len).map_err(|_| StorageIoError::Overflow("part extent"))?;
                let path = part_file(directory, index);
                if access.drop_cached_pages {
                    drop_cached_file_pages(&path)?;
                }
                let buffer = ReadOnlyBuffer::map_file(&path, elem.extent(len)?)?;
                if access.read_advice == ReadAdvice::Random {
                    buffer.advise_random_access()?;
                }
                Ok(buffer)
            })
            .collect::<Result<Vec<_>>>()?;
        Ok(Self { manifest, buffers })
    }

    pub fn manifest(&self) -> &PartsManifest {
        &self.manifest
    }

    /// The parts in stored order.
    pub fn parts(&self) -> impl Iterator<Item = MappedPart> + '_ {
        self.manifest.parts.iter().zip(&self.buffers).map(|(&(elem, len), buffer)| MappedPart {
            elem,
            len,
            data: buffer.as_ptr(),
        })
    }
}

fn read_manifest(path: &Path) -> Result<PartsManifest> {
    if fs::metadata(path).map_err(StorageIoError::file(path))?.len() > MANIFEST_LIMIT_BYTES {
        return Err(StorageIoError::archive(path, "parts manifest exceeds limit"));
    }
    let manifest: PartsManifest =
        serde_json::from_slice(&fs::read(path).map_err(StorageIoError::file(path))?).map_err(StorageIoError::json(path))?;
    manifest.check_format(path)?;
    Ok(manifest)
}

/// `posix_fadvise(POSIX_FADV_DONTNEED)` on the whole file at `path`.
fn drop_cached_file_pages(path: &Path) -> Result<()> {
    let file = fs::File::open(path).map_err(StorageIoError::file(path))?;
    // SAFETY: advice on an open file descriptor; it changes no content.
    let code = unsafe { libc::posix_fadvise(file.as_raw_fd(), 0, 0, libc::POSIX_FADV_DONTNEED) };
    if code != 0 {
        return Err(StorageIoError::File { path: path.to_owned(), source: std::io::Error::from_raw_os_error(code) });
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::io::error::STORAGE_RESERVE_REFUSAL;

    fn scratch(name: &str) -> PathBuf {
        let nanos = std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).unwrap().as_nanos();
        std::env::temp_dir().join(format!("gendb-storage-parts-{name}-{}-{nanos}", std::process::id()))
    }

    fn write(directory: &Path, format: PartsFormat, parts: &[(PartElem, usize, &[u8])]) -> Result<PartsManifest> {
        let mut writer = PartFilesWriter::new(directory, format)?;
        for (elem, len, bytes) in parts {
            writer.write_part(*elem, *len, bytes)?;
        }
        writer.finish()
    }

    /// Format 1 keeps the saved manifest bytes; parts are written once, read-only, and map back to the same values.
    #[test]
    fn saved_v3_parts_round_trip_through_read_only_files() {
        let directory = scratch("round-trip").join("asset");
        let values: Vec<i64> = vec![-3, 0, 7, i64::MAX];
        let bytes: Vec<u8> = values.iter().flat_map(|v| v.to_ne_bytes()).collect();
        let parts = [(PartElem::I64, 4, bytes.as_slice()), (PartElem::U8, 0, &[][..])];
        let manifest = write(&directory, PartsFormat::SavedV3, &parts).unwrap();
        assert_eq!(manifest.storage_bytes, 32);
        assert!(matches!(PartFilesWriter::new(&directory, PartsFormat::SavedV3), Err(StorageIoError::Archive { .. })), "parts are written once");
        assert_eq!(
            fs::read_to_string(directory.join(MANIFEST_FILE)).unwrap(),
            r#"{"format_version":1,"parts":[["i64",4],["u8",0]],"storage_bytes":32}"#
        );
        assert_eq!(fs::metadata(part_file(&directory, 0)).unwrap().permissions().mode() & 0o777, 0o444);

        let stored = MappedPartFiles::open(&directory, &PartAccess::default()).unwrap();
        let mapped: Vec<MappedPart> = stored.parts().collect();
        assert_eq!((mapped[0].elem, mapped[0].len, mapped[1].elem, mapped[1].len), (PartElem::I64, 4, PartElem::U8, 0));
        // SAFETY: `stored` owns the mapping of four i64 values for the rest of this test.
        let read = unsafe { std::slice::from_raw_parts(mapped[0].data.cast::<i64>(), 4) };
        assert_eq!(read, values.as_slice());
    }

    /// Format 2 states its byte order; the manifest is the commit point; a writer that never finishes and never
    /// writes creates nothing; both advice options map the same values.
    #[test]
    fn little_endian_parts_commit_with_the_manifest_and_honour_advice() {
        let root = scratch("format-2");
        let unused = root.join("unused");
        drop(PartFilesWriter::new(&unused, PartsFormat::LittleEndian).unwrap());
        assert!(!unused.exists(), "nothing is created before the first part");

        let directory = root.join("asset");
        let values: Vec<u32> = (0..1000).collect();
        let bytes: Vec<u8> = values.iter().flat_map(|v| v.to_le_bytes()).collect();
        let mut writer = PartFilesWriter::new(&directory, PartsFormat::LittleEndian).unwrap();
        writer.write_part(PartElem::U32, 1000, &bytes).unwrap();
        assert!(writer.write_part(PartElem::U32, 3, &bytes[..8]).is_err(), "extent must match");
        assert!(MappedPartFiles::open(&directory, &PartAccess::default()).is_err(), "no manifest yet: never mapped");
        let manifest = writer.finish().unwrap();
        assert_eq!(
            fs::read_to_string(directory.join(MANIFEST_FILE)).unwrap(),
            r#"{"format_version":2,"byte_order":"little","parts":[["u32",1000]],"storage_bytes":4000}"#
        );
        assert_eq!(manifest.storage_bytes, 4000);
        let access = PartAccess { read_advice: ReadAdvice::Random, drop_cached_pages: true };
        let stored = MappedPartFiles::open(&directory, &access).unwrap();
        let part = stored.parts().next().unwrap();
        // SAFETY: `stored` owns the mapping of 1000 u32 values for the rest of this test.
        assert_eq!(unsafe { std::slice::from_raw_parts(part.data.cast::<u32>(), 1000) }, values.as_slice());
    }

    /// A fake filesystem of 1000 bytes holding only the files of `directory`.
    fn fake_free_bytes(directory: &Path) -> Option<u64> {
        let used: u64 = fs::read_dir(directory).ok()?.map(|entry| entry.unwrap().metadata().unwrap().len()).sum();
        Some(1000 - used)
    }

    /// The reserve is kept as bytes are written, chunk by chunk: a part of any size is written while the reserve
    /// holds (no size budget), and the chunk that would cross it is refused, leaving the reserve free and no manifest.
    #[test]
    fn writes_keep_the_free_space_reserve_chunk_by_chunk() {
        let directory = scratch("reserve").join("asset");
        let reserve = SpaceReserve { bytes: 100, chunk_bytes: 16, free_bytes: fake_free_bytes };
        let mut writer = PartFilesWriter::with_reserve(&directory, PartsFormat::LittleEndian, reserve).unwrap();
        writer.write_part(PartElem::U8, 800, &[7; 800]).unwrap();
        let refused = writer.write_part(PartElem::U8, 200, &[7; 200]);
        assert!(
            matches!(refused, Err(StorageIoError::StorageReserve { free: 104, reserve: 100, write: 16, .. })),
            "{refused:?}"
        );
        assert!(refused.unwrap_err().to_string().starts_with(STORAGE_RESERVE_REFUSAL));
        assert_eq!(fake_free_bytes(&directory), Some(104), "stopped before the chunk that would cross the reserve");
        assert_eq!(writer.part_count(), 1, "the refused part is not in the manifest");
        assert!(!directory.join(MANIFEST_FILE).exists(), "never committed");
    }

    /// A read-only source file of the part's exact extent becomes a part by hard link (one inode, a symbolic link to it
    /// followed); a writable or mis-sized source is refused before anything is added. The copy used across filesystems
    /// writes the same bytes read-only and keeps the reserve chunk by chunk.
    #[test]
    fn file_parts_are_linked_or_copied_unchanged() {
        use std::os::unix::fs::MetadataExt;
        let root = scratch("file-parts");
        fs::create_dir_all(&root).unwrap();
        let values: Vec<i64> = vec![5, -1, 9];
        let source = root.join("column-0-values.bin");
        fs::write(&source, values.iter().flat_map(|v| v.to_le_bytes()).collect::<Vec<u8>>()).unwrap();
        let writable = root.join("writable.bin");
        fs::copy(&source, &writable).unwrap();
        fs::set_permissions(&source, fs::Permissions::from_mode(0o444)).unwrap();
        let named = root.join("named.bin");
        std::os::unix::fs::symlink(&source, &named).unwrap();

        let directory = root.join("asset");
        let mut writer = PartFilesWriter::new(&directory, PartsFormat::LittleEndian).unwrap();
        assert_eq!(writer.add_file_part(PartElem::I64, 3, &named).unwrap(), PartPlacement::HardLink);
        assert!(writer.add_file_part(PartElem::I64, 2, &source).is_err(), "the file must be exactly the part's extent");
        assert!(writer.add_file_part(PartElem::I64, 3, &writable).is_err(), "a writable file is not shared");
        let manifest = writer.finish().unwrap();
        assert_eq!((manifest.parts.clone(), manifest.storage_bytes), (vec![(PartElem::I64, 3)], 24));
        assert_eq!(fs::metadata(part_file(&directory, 0)).unwrap().ino(), fs::metadata(&source).unwrap().ino(), "one inode");
        let stored = MappedPartFiles::open(&directory, &PartAccess::default()).unwrap();
        let part = stored.parts().next().unwrap();
        // SAFETY: `stored` owns the mapping of three i64 values for the rest of this test.
        assert_eq!(unsafe { std::slice::from_raw_parts(part.data.cast::<i64>(), 3) }, values.as_slice());

        let copied = root.join("copied.bin");
        SpaceReserve { bytes: 0, chunk_bytes: 5, free_bytes: free_bytes_at }.copy_read_only_file(&root, &source, &copied, 24).unwrap();
        assert_eq!(fs::read(&copied).unwrap(), fs::read(&source).unwrap());
        assert_eq!(fs::metadata(&copied).unwrap().permissions().mode() & 0o777, 0o444);
        let tight = SpaceReserve { bytes: u64::MAX, chunk_bytes: 5, free_bytes: free_bytes_at };
        assert!(matches!(tight.copy_read_only_file(&root, &source, &root.join("refused.bin"), 24), Err(StorageIoError::StorageReserve { .. })));
        fs::remove_dir_all(&root).ok();
    }

    /// A manifest whose format and byte order do not belong together is refused.
    #[test]
    fn inconsistent_manifest_formats_are_refused() {
        let path = Path::new("parts.json");
        let manifest = |format_version, byte_order| PartsManifest { format_version, byte_order, parts: vec![], storage_bytes: 0 };
        assert!(manifest(1, None).check_format(path).is_ok());
        assert!(manifest(2, Some(ByteOrder::Little)).check_format(path).is_ok());
        for bad in [manifest(1, Some(ByteOrder::Little)), manifest(2, None), manifest(3, None)] {
            assert!(bad.check_format(path).is_err(), "{bad:?}");
        }
        let access: PartAccess = serde_json::from_str(r#"{"read_advice":"random","drop_cached_pages":false}"#).unwrap();
        assert_eq!(access.read_advice, ReadAdvice::Random);
    }

    #[test]
    fn part_shapes_and_codes_are_checked() {
        assert!(matches!(PartElem::I128.extent(usize::MAX), Err(StorageIoError::Overflow(_))));
        for elem in PartElem::ALL {
            assert_eq!(PartElem::from_code(elem.code()), Some(elem));
        }
        assert_eq!((PartElem::from_code(0), PartElem::from_code(10)), (None, None));
    }
}
