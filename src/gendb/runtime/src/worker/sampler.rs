//! Profile sampling of engine calls, armed only by a request's `sampling` (profile jobs;
//! serving never sets it).
//!
//! A `SIGPROF` interval timer over the process's CPU time (`setitimer(ITIMER_PROF)`) is set for each call and cleared
//! after it. The kernel sends the signal to a thread that is consuming CPU, so samples fall on the busy threads
//! (the calling thread and the engine's worker threads) roughly in proportion to their CPU time. The handler records
//! only the interrupted instruction pointer into a preallocated buffer with atomic operations (async-signal-safe: no
//! allocation, lock or system call). No stack is walked: the engine libraries are built without frame pointers
//! (checked on a compiled fixture engine: `opt-level` builds keep the `.symtab` symbols but omit frame pointers), so
//! a profile is self time only.
//!
//! After the call the samples are counted per address and placed in the loaded objects (`dl_iterate_phdr`: each
//! object's load bias and `PT_LOAD` segments), as ELF virtual addresses of their files ([`SampledObject`]);
//! symbolization against each file's symbol table happens outside the child (`gendb_synthesis::engine::profile`).
//! Samples are descriptive: the signal and its handler perturb the call slightly, so a profile job's times are never
//! timing evidence.

use super::protocol::{CallSamples, SampledObject};
use std::collections::BTreeMap;
use std::ffi::{CStr, c_int, c_void};
use std::path::Path;
use std::sync::atomic::{AtomicBool, AtomicPtr, AtomicU32, AtomicUsize, Ordering};

/// Samples kept per call (32 MiB of addresses): 64 busy threads at a 1 ms interval for 60 s fit.
const CAPACITY: usize = 1 << 22;

/// The sample buffer (allocated once per process, never freed), the next free slot, the arming flag and the interval.
static BUFFER: AtomicPtr<AtomicUsize> = AtomicPtr::new(std::ptr::null_mut());
static NEXT: AtomicUsize = AtomicUsize::new(0);
static ACTIVE: AtomicBool = AtomicBool::new(false);
static INTERVAL_US: AtomicU32 = AtomicU32::new(0);

/// The installed sampler of this process (at most one: the handler and buffer are process-wide).
pub(super) struct Sampler {
    _installed: (),
}

impl Sampler {
    /// Allocate the buffer and install the `SIGPROF` handler; the timer stays off until [`Sampler::begin_call`].
    pub fn install(interval_us: u32) -> std::io::Result<Self> {
        if BUFFER.load(Ordering::Acquire).is_null() {
            let buffer: Box<[AtomicUsize]> = (0..CAPACITY).map(|_| AtomicUsize::new(0)).collect();
            BUFFER.store(Box::leak(buffer).as_mut_ptr(), Ordering::Release);
        }
        INTERVAL_US.store(interval_us, Ordering::Relaxed);
        // SAFETY: a zeroed `sigaction` with an empty mask, `SA_SIGINFO` and a handler of the three-argument form; the
        // handler is async-signal-safe (atomics only).
        unsafe {
            let mut action: libc::sigaction = std::mem::zeroed();
            action.sa_sigaction = on_sigprof as *const () as usize;
            action.sa_flags = libc::SA_SIGINFO | libc::SA_RESTART;
            libc::sigemptyset(&mut action.sa_mask);
            if libc::sigaction(libc::SIGPROF, &action, std::ptr::null_mut()) != 0 {
                return Err(std::io::Error::last_os_error());
            }
        }
        Ok(Self { _installed: () })
    }

    /// Start sampling the call about to run.
    pub fn begin_call(&self) {
        NEXT.store(0, Ordering::SeqCst);
        ACTIVE.store(true, Ordering::SeqCst);
        set_timer(INTERVAL_US.load(Ordering::Relaxed));
    }

    /// Stop sampling and return the call's samples (empty if the watchdog took them first at a stop).
    pub fn end_call(&self) -> CallSamples {
        stop_active_call().unwrap_or_else(|| CallSamples { interval_us: INTERVAL_US.load(Ordering::Relaxed), ..CallSamples::default() })
    }
}

/// Stop the timer and collect the samples of the call being sampled, or `None` when no call is being sampled (also
/// used by the watchdog when it stops a call). Whoever clears the arming flag collects, so two collectors never read
/// the buffer together.
pub(super) fn stop_active_call() -> Option<CallSamples> {
    if !ACTIVE.swap(false, Ordering::SeqCst) {
        return None;
    }
    set_timer(0);
    let reserved = NEXT.load(Ordering::SeqCst);
    let buffer = BUFFER.load(Ordering::Acquire);
    let mut addresses = Vec::with_capacity(reserved.min(CAPACITY));
    for i in 0..reserved.min(CAPACITY) {
        // SAFETY: `buffer` holds `CAPACITY` slots for the rest of the process; the slot is reset for the next call.
        let ip = unsafe { (*buffer.add(i)).swap(0, Ordering::Acquire) };
        // A zero slot was reserved by a handler that had not stored its address when sampling stopped.
        if ip != 0 {
            addresses.push(ip as u64);
        }
    }
    let interval_us = INTERVAL_US.load(Ordering::Relaxed);
    let dropped = reserved.saturating_sub(CAPACITY) as u64;
    Some(place_in_objects(interval_us, addresses, dropped))
}

/// `setitimer(ITIMER_PROF)` with `interval_us` as both the first expiry and the period (0: off).
fn set_timer(interval_us: u32) {
    let period = libc::timeval { tv_sec: (interval_us / 1_000_000) as libc::time_t, tv_usec: (interval_us % 1_000_000) as libc::suseconds_t };
    let timer = libc::itimerval { it_interval: period, it_value: period };
    // SAFETY: a valid timer value; the previous value is not requested.
    unsafe { libc::setitimer(libc::ITIMER_PROF, &timer, std::ptr::null_mut()) };
}

/// The `SIGPROF` handler: reserve a slot and store the interrupted instruction pointer (atomics only).
extern "C" fn on_sigprof(_signal: c_int, _info: *mut libc::siginfo_t, context: *mut c_void) {
    if !ACTIVE.load(Ordering::Relaxed) {
        return;
    }
    // SAFETY: the kernel passes the interrupted thread's `ucontext_t` to an `SA_SIGINFO` handler.
    let ip = unsafe { instruction_pointer(context) };
    let slot = NEXT.fetch_add(1, Ordering::Relaxed);
    let buffer = BUFFER.load(Ordering::Acquire);
    if slot < CAPACITY && !buffer.is_null() {
        // SAFETY: `slot < CAPACITY` and the buffer lives for the rest of the process.
        unsafe { (*buffer.add(slot)).store(ip, Ordering::Release) };
    }
}

#[cfg(all(target_os = "linux", target_arch = "x86_64"))]
unsafe fn instruction_pointer(context: *mut c_void) -> usize {
    // SAFETY: the caller passes a `ucontext_t` delivered with the signal.
    unsafe { (*context.cast::<libc::ucontext_t>()).uc_mcontext.gregs[libc::REG_RIP as usize] as usize }
}

#[cfg(all(target_os = "linux", target_arch = "aarch64"))]
unsafe fn instruction_pointer(context: *mut c_void) -> usize {
    // SAFETY: the caller passes a `ucontext_t` delivered with the signal.
    unsafe { (*context.cast::<libc::ucontext_t>()).uc_mcontext.pc as usize }
}

/// Other targets record no address (every sample is then unmapped).
#[cfg(not(all(target_os = "linux", any(target_arch = "x86_64", target_arch = "aarch64"))))]
unsafe fn instruction_pointer(_context: *mut c_void) -> usize {
    0
}

/// One loaded object: its path and its `PT_LOAD` segments as absolute `[start, end)` address ranges.
struct LoadedObject {
    path: String,
    bias: u64,
    segments: Vec<(u64, u64)>,
}

/// Count the samples per address and place each in the loaded object whose segment contains it.
fn place_in_objects(interval_us: u32, mut addresses: Vec<u64>, dropped: u64) -> CallSamples {
    let taken = addresses.len() as u64;
    addresses.sort_unstable();
    let objects = loaded_objects();
    let mut by_object: BTreeMap<usize, Vec<(u64, u64)>> = BTreeMap::new();
    let mut unmapped = 0;
    for run in addresses.chunk_by(|a, b| a == b) {
        let (ip, count) = (run[0], run.len() as u64);
        match objects.iter().position(|o| o.segments.iter().any(|&(start, end)| (start..end).contains(&ip))) {
            Some(k) => by_object.entry(k).or_default().push((ip - objects[k].bias, count)),
            None => unmapped += count,
        }
    }
    let objects = by_object.into_iter().map(|(k, addresses)| SampledObject { path: objects[k].path.clone(), addresses }).collect();
    CallSamples { interval_us, taken, dropped, unmapped, objects }
}

/// Every object the dynamic loader has loaded (the main program under its executable path).
fn loaded_objects() -> Vec<LoadedObject> {
    struct Walk {
        executable: String,
        objects: Vec<LoadedObject>,
    }
    unsafe extern "C" fn each(info: *mut libc::dl_phdr_info, _size: libc::size_t, data: *mut c_void) -> c_int {
        // SAFETY: `dl_iterate_phdr` passes a valid entry and the `Walk` given below.
        let (info, walk) = unsafe { (&*info, &mut *data.cast::<Walk>()) };
        let named = !info.dlpi_name.is_null() && unsafe { *info.dlpi_name } != 0;
        let path = if named { unsafe { CStr::from_ptr(info.dlpi_name) }.to_string_lossy().into_owned() } else { walk.executable.clone() };
        let bias = info.dlpi_addr;
        let mut segments = vec![];
        for i in 0..usize::from(info.dlpi_phnum) {
            // SAFETY: `dlpi_phdr` points to `dlpi_phnum` program headers.
            let header = unsafe { &*info.dlpi_phdr.add(i) };
            if header.p_type == libc::PT_LOAD {
                segments.push((bias + header.p_vaddr, bias + header.p_vaddr + header.p_memsz));
            }
        }
        walk.objects.push(LoadedObject { path, bias, segments });
        0
    }
    let executable = std::env::current_exe().ok().as_deref().map(Path::to_string_lossy).map(|p| p.into_owned()).unwrap_or_default();
    let mut walk = Walk { executable, objects: vec![] };
    // SAFETY: `each` matches the callback type and only reads the entries it is given.
    unsafe { libc::dl_iterate_phdr(Some(each), (&mut walk as *mut Walk).cast()) };
    walk.objects
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A busy loop of this process, sampled: the samples fall in this test executable's own code.
    #[test]
    fn samples_fall_in_the_running_object() {
        let sampler = Sampler::install(1000).unwrap();
        sampler.begin_call();
        let started = std::time::Instant::now();
        let mut x = 0u64;
        while started.elapsed() < std::time::Duration::from_millis(300) {
            x = std::hint::black_box(x.wrapping_mul(6364136223846793005).wrapping_add(1));
        }
        let samples = sampler.end_call();
        assert!(samples.taken > 10, "{samples:?}");
        let executable = std::env::current_exe().unwrap().to_string_lossy().into_owned();
        let own: u64 = samples.objects.iter().filter(|o| o.path == executable).flat_map(|o| o.addresses.iter().map(|a| a.1)).sum();
        assert!(own * 2 > samples.taken, "most samples are in this executable: {own} of {}; {:?}", samples.taken,
            samples.objects.iter().map(|o| (&o.path, o.addresses.len())).collect::<Vec<_>>());
        assert!(stop_active_call().is_none(), "nothing is sampled after the call");
    }
}
