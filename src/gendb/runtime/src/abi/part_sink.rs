//! The host part sink of a build call: each part the shim delivers is written straight from the builder's buffer to
//! its read-only file ([`PartFilesWriter`]), with no host copy, so the build's peak memory is the builder's own parts.

use super::error::AbiError;
use super::records::PartSink;
use gendb_storage::io::{PartElem, PartFilesWriter};
use std::ffi::c_void;

/// Receives the builder's parts during one build call.
pub(super) struct PartFileSink {
    writer: PartFilesWriter,
    /// Parts already in the writer before the call (a derived build's inherited parts): delivered index `i` is part
    /// `first + i`.
    first: u64,
    error: Option<AbiError>,
}

impl PartFileSink {
    pub fn new(writer: PartFilesWriter) -> Self {
        let first = writer.part_count() as u64;
        Self { writer, first, error: None }
    }

    /// The C sink record pointing at `self`; valid while `self` is neither moved nor dropped.
    pub fn record(&mut self) -> PartSink {
        PartSink { ctx: (self as *mut Self).cast(), put: Some(put_part) }
    }

    /// The writer and the first delivery refusal, after the call.
    pub fn into_parts(self) -> (PartFilesWriter, Option<AbiError>) {
        (self.writer, self.error)
    }

    /// Write part `index`; parts must arrive in order.
    fn accept(&mut self, index: u64, elem_code: u32, len: u64, data: *const u8) -> Result<(), AbiError> {
        if index.checked_add(self.first) != Some(self.writer.part_count() as u64) {
            return Err(AbiError::PartDelivery("builder part index out of order"));
        }
        let elem = PartElem::from_code(elem_code).ok_or(AbiError::PartDelivery("builder part element type unknown"))?;
        let len = usize::try_from(len).map_err(|_| AbiError::PartDelivery("builder part extent overflow"))?;
        let size = elem.extent(len)?;
        if size > 0 && data.is_null() {
            return Err(AbiError::PartDelivery("builder part data is null"));
        }
        // SAFETY: the shim passes its live Vec buffer of `len` elements of `elem` for the duration of this call.
        let bytes = if size == 0 { &[][..] } else { unsafe { std::slice::from_raw_parts(data, size) } };
        self.writer.write_part(elem, len, bytes)?;
        Ok(())
    }
}

unsafe extern "C" fn put_part(ctx: *mut c_void, index: u64, elem_code: u32, len: u64, data: *const u8) -> i32 {
    // SAFETY: `ctx` is the `PartFileSink` owned by the build call for the duration of the call.
    let sink = unsafe { &mut *ctx.cast::<PartFileSink>() };
    if sink.error.is_some() {
        return 1;
    }
    match sink.accept(index, elem_code, len, data) {
        Ok(()) => 0,
        Err(error) => {
            sink.error = Some(error);
            1
        }
    }
}
