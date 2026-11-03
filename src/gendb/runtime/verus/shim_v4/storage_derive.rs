
// ---- Derived storage crate entry (`runtime/verus/shim_v4/storage_derive.rs`) ----

/// The part list of every source, in the builder's use order. The count must be the crate's declared source count
/// (`gendb_entry::sources::STORAGE_USES`, the entry's precondition) and no argument is passed; otherwise the call is
/// refused before any verified code runs.
unsafe fn source_uses(inputs: &StorageQueryInputs) -> Option<Vec<Vec<crate::gendb_abi::Part>>> {
    let uses = unsafe { host_records(inputs.uses, inputs.use_count)? };
    if uses.len() != crate::gendb_entry::sources::STORAGE_USES || inputs.argument_count != 0 {
        return None;
    }
    let mut out = Vec::new();
    for u in uses {
        out.push(unsafe { storage_use_parts(u)? });
    }
    Some(out)
}

/// Derived storage build entry: the parts of the source storages in, the new storage's own parts out to the host sink
/// (the host has already placed the inherited parts, if any). On `Ok` every part is handed to the sink from the
/// builder's own buffer, numbered from 0; other statuses deliver nothing.
#[no_mangle]
pub unsafe extern "C" fn gendb_verus_storage_build_derived_v4(
    inputs: *const StorageQueryInputs,
    sink: *const PartSink,
    out: *mut CallRecord,
) -> i32 {
    abort_on_panic(|| {
        let Some(out) = (unsafe { out.as_mut() }) else { return -1 };
        reset_call_record(out);
        let (Some(inputs), Some(sink)) = (unsafe { inputs.as_ref() }, unsafe { sink.as_ref() }) else { return 0 };
        let (Some(put), Some(workers), Some(uses)) = (sink.put, requested_workers(inputs.workers), unsafe { source_uses(inputs) }) else {
            return 0;
        };
        let r = crate::gendb_entry::abi_build_derived_storage(uses, workers);
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
