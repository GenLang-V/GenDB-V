
// ---- Storage crate entry, nullable source columns (`runtime/verus/shim_v4/storage_build_nullable.rs`) ----
//
// The storage build shim of a storage crate whose declaration has a nullable column, used instead of
// `storage_build.rs`, which stays the shim of every declaration of NOT NULL columns byte for byte (so the builder
// identity of every such storage, the runtime's golden texts and the digests that pin them do not move; the shim is in
// no storage's closure). It differs only in `input_columns`: a nullable column descriptor delivers its values column,
// then its validity (one byte per row, 1 valid, 0 NULL, from the descriptor's validity buffer) as a `Column::Utf8` with
// no offsets. `gendb_abi.rs` has no byte-column variant, and it is in every storage's closure (a query crate carries
// each storage's closure byte for byte), so a new variant would change every admitted storage's closure; a text column
// always has at least one offset, so the verified binder (`gendb_entry/binder.rs`) tells the two apart.

use crate::gendb_abi::Column;

/// Utf8: `len + 1` absolute offsets; the byte extent is `offsets[len]` (canonical capture). Monotonicity and ranges
/// are decided by the verified binder, not here.
unsafe fn utf8_column(c: &NativeColumn) -> Option<Column> {
    let rows = u64::try_from(c.len).ok()?;
    let offsets: &'static [i64] = unsafe { host_slice(c.offsets.cast::<u8>(), rows.checked_add(1)?)? };
    let extent = u64::try_from(*offsets.last()?).ok()?;
    let bytes: &'static [u8] = unsafe { host_slice(c.bytes, extent)? };
    Some(Column::Utf8 { offsets, bytes })
}

/// The validity of a nullable column of `len` rows: its bytes as a `Column::Utf8` with no offsets.
unsafe fn validity_column(c: &NativeColumn) -> Option<Column> {
    let validity: &'static [u8] = unsafe { host_slice(c.validity, c.len as u64)? };
    Some(Column::Utf8 { offsets: &[], bytes: validity })
}

/// Build input columns: each column's values, and after a nullable column its validity. An unsupported type tag
/// refuses the call.
unsafe fn input_columns(inputs: &CallInputs) -> Option<Vec<Column>> {
    let mut out = Vec::new();
    for c in unsafe { host_records(inputs.columns, inputs.column_count)? } {
        if c.len < 0 {
            return None;
        }
        out.push(match c.type_tag {
            NATIVE_TYPE_I32 => Column::I32(unsafe { host_slice(c.values, c.len as u64)? }),
            NATIVE_TYPE_I64 => Column::I64(unsafe { host_slice(c.values, c.len as u64)? }),
            NATIVE_TYPE_I128 => Column::I128(unsafe { host_slice(c.values, c.len as u64)? }),
            NATIVE_TYPE_UTF8 => unsafe { utf8_column(c)? },
            _ => return None,
        });
        if c.nullable != 0 {
            out.push(unsafe { validity_column(c)? });
        }
    }
    Some(out)
}

/// Storage build entry. Statement arguments are not read: a storage asset is built once for every statement and
/// binding that reads it. On `Ok` every part is handed to the host sink from the builder's own buffer (the host writes
/// it to its file during the call); other statuses deliver nothing.
#[no_mangle]
pub unsafe extern "C" fn gendb_verus_storage_build_v4(
    inputs: *const CallInputs,
    sink: *const PartSink,
    out: *mut CallRecord,
) -> i32 {
    abort_on_panic(|| {
        let Some(out) = (unsafe { out.as_mut() }) else { return -1 };
        reset_call_record(out);
        let (Some(inputs), Some(sink)) = (unsafe { inputs.as_ref() }, unsafe { sink.as_ref() }) else { return 0 };
        let (Some(put), Some(workers), Some(columns)) =
            (sink.put, requested_workers(inputs.workers), unsafe { input_columns(inputs) })
        else {
            return 0;
        };
        let r = crate::gendb_entry::abi_build_storage(&columns, workers);
        unsafe { write_dispatch(out, &r.dispatch) };
        out.status = status_code(&r.status);
        if out.status != STATUS_OK {
            return 0;
        }
        for (i, part) in r.parts.iter().enumerate() {
            let (elem, len, data) = owned_part_raw(part);
            if unsafe { put(sink.ctx, i as u64, elem, len as u64, data) } != 0 {
                out.status = STATUS_SINK_FAILED;
                return 0;
            }
            out.parts_delivered += 1;
        }
        0
    })
}
