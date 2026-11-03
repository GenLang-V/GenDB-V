
// ---- Storage crate entry (`runtime/verus/shim_v4/storage_build.rs`) ----

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

/// Build input columns. A nullable column or an unsupported type tag refuses the call.
unsafe fn input_columns(inputs: &CallInputs) -> Option<Vec<Column>> {
    let mut out = Vec::new();
    for c in unsafe { host_records(inputs.columns, inputs.column_count)? } {
        if c.nullable != 0 || c.len < 0 {
            return None;
        }
        out.push(match c.type_tag {
            NATIVE_TYPE_I32 => Column::I32(unsafe { host_slice(c.values, c.len as u64)? }),
            NATIVE_TYPE_I64 => Column::I64(unsafe { host_slice(c.values, c.len as u64)? }),
            NATIVE_TYPE_I128 => Column::I128(unsafe { host_slice(c.values, c.len as u64)? }),
            NATIVE_TYPE_UTF8 => unsafe { utf8_column(c)? },
            _ => return None,
        });
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
