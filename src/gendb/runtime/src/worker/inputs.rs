//! Child-side inputs of one call, retained until the process exits: source columns, stored parts (of one directory or
//! of every storage use), argument lists and the library. Every owner is leaked (`Box::leak`), so the descriptors the shim turns into `&'static` slices stay
//! valid on every return path; the OS reclaims them when the child exits. Only [`super::child`] calls these, and
//! only inside the worker process.

use super::error::WorkerError;
use super::protocol::{InlineColumn, InlineElem, MappedStorageUse, StorageUseInput, WorkerInput};
use crate::abi::{MappedParts, PartDescriptor, StatementArgument};
use gendb_storage::io::{
    NATIVE_TYPE_I32, NATIVE_TYPE_I64, NATIVE_TYPE_I128, NATIVE_TYPE_UTF8, NativeColumn, PartAccess, SourceColumns,
};
use std::path::Path;

/// The source columns of `input` in ABI order: none, the prepared archive's mapped column files projected table by
/// table (no Arrow decode, no copy), or inline fixture columns.
pub(super) fn retained_columns(input: &WorkerInput) -> Result<&'static [NativeColumn], WorkerError> {
    Ok(match input {
        WorkerInput::None => &[],
        WorkerInput::Tables { path, tables } => {
            let projection: Vec<(String, Vec<usize>)> =
                tables.iter().map(|table| (table.table.clone(), table.ordinals.clone())).collect();
            let columns = SourceColumns::map_archive(path)?.project(&projection)?;
            Box::leak(Box::new(columns)).descriptors()
        }
        WorkerInput::Inline { columns } => &Box::leak(Box::new(InlineColumns::new(columns)?)).descriptors,
        // A derived storage build reads stored parts, never columns (`child::run_derived_storage_build`).
        WorkerInput::StoredParts { .. } => return Err(WorkerError::Request("a derived storage build has no source columns")),
    })
}

/// The stored parts of a query, mapped read-only (none: no part).
pub(super) fn retained_parts(directory: Option<&Path>) -> Result<&'static [PartDescriptor], WorkerError> {
    Ok(match directory {
        Some(directory) => Box::leak(Box::new(MappedParts::open(directory, &PartAccess::default())?)).descriptors(),
        None => &[],
    })
}

pub(super) fn retained_bindings(bindings: &[Vec<StatementArgument>]) -> &'static [Vec<StatementArgument>] {
    Box::leak(bindings.to_vec().into_boxed_slice())
}

/// The part lists of a v4 query's storage uses, in use order, and what each use mapped.
pub(super) struct RetainedStorageUses {
    pub part_lists: &'static [&'static [PartDescriptor]],
    pub mapped: Vec<MappedStorageUse>,
}

/// Map every storage use's parts directory read-only with the kernel advice `access` (no part payload is read
/// eagerly), retained for the rest of the process.
pub(super) fn retained_storage_uses(
    uses: &[StorageUseInput],
    access: &gendb_storage::io::PartAccess,
) -> Result<RetainedStorageUses, WorkerError> {
    let mut part_lists = vec![];
    let mut mapped = vec![];
    for use_input in uses {
        let parts: &'static MappedParts = retained(MappedParts::open(&use_input.parts_directory, access)?);
        let manifest = parts.files().manifest();
        mapped.push(MappedStorageUse {
            name: use_input.name.clone(),
            parts: manifest.parts.len() as u64,
            storage_bytes: manifest.storage_bytes,
        });
        part_lists.push(parts.descriptors());
    }
    Ok(RetainedStorageUses { part_lists: Box::leak(part_lists.into_boxed_slice()), mapped })
}

/// `value` for the rest of the process (loaded libraries are never unloaded; mappings are never released).
pub(super) fn retained<T>(value: T) -> &'static T {
    Box::leak(Box::new(value))
}

/// Owner of inline fixture columns: each column's values (and a Utf8 column's `len + 1` i64 offsets from 0) in
/// 16-byte aligned words, a nullable column's validity bytes, and the descriptors pointing into them.
struct InlineColumns {
    _words: Vec<Vec<u128>>,
    _validity: Vec<Vec<u8>>,
    descriptors: Vec<NativeColumn>,
}

impl InlineColumns {
    fn new(columns: &[InlineColumn]) -> Result<Self, WorkerError> {
        let mut words = vec![];
        let mut validities = vec![];
        let mut descriptors = vec![];
        for column in columns {
            let rows = i64::try_from(column.values.len()).map_err(|_| inline_error("too many inline rows"))?;
            let descriptor = match column.elem {
                InlineElem::Utf8 => {
                    let (bytes, offsets) = utf8_bytes_and_offsets(&column.values)?;
                    let (bytes, offsets) = (aligned_words(&bytes), aligned_words(&offsets));
                    let descriptor = NativeColumn {
                        type_tag: NATIVE_TYPE_UTF8,
                        nullable: 0,
                        len: rows,
                        values: std::ptr::null(),
                        offsets: offsets.as_ptr().cast(),
                        bytes: bytes.as_ptr().cast(),
                        validity: std::ptr::null(),
                    };
                    words.extend([bytes, offsets]);
                    descriptor
                }
                elem => {
                    let (type_tag, values) = fixed_width_values(elem, &column.values)?;
                    let values = aligned_words(&values);
                    let descriptor = NativeColumn {
                        type_tag,
                        nullable: 0,
                        len: rows,
                        values: values.as_ptr().cast(),
                        offsets: std::ptr::null(),
                        bytes: std::ptr::null(),
                        validity: std::ptr::null(),
                    };
                    words.push(values);
                    descriptor
                }
            };
            let descriptor = match &column.validity {
                None => descriptor,
                Some(validity) if validity.len() == column.values.len() => {
                    let validity = validity.clone();
                    let described = NativeColumn { nullable: 1, validity: validity.as_ptr(), ..descriptor };
                    validities.push(validity);
                    described
                }
                Some(_) => return Err(inline_error("inline validity length differs from the column's rows")),
            };
            descriptors.push(descriptor);
        }
        Ok(Self { _words: words, _validity: validities, descriptors })
    }
}

/// Native tag and host-order bytes of an integer column; each text must be an exact value of the element type.
fn fixed_width_values(elem: InlineElem, texts: &[String]) -> Result<(i32, Vec<u8>), WorkerError> {
    let mut bytes = vec![];
    for text in texts {
        let value: i128 = text.parse().map_err(|e| inline_error(format!("inline value {text}: {e}")))?;
        let narrow = |e: std::num::TryFromIntError| inline_error(format!("inline value {text}: {e}"));
        match elem {
            InlineElem::I32 => bytes.extend(i32::try_from(value).map_err(narrow)?.to_ne_bytes()),
            InlineElem::I64 => bytes.extend(i64::try_from(value).map_err(narrow)?.to_ne_bytes()),
            InlineElem::I128 => bytes.extend(value.to_ne_bytes()),
            InlineElem::Utf8 => unreachable!("Utf8 columns have offsets and bytes"),
        }
    }
    let tag = match elem {
        InlineElem::I32 => NATIVE_TYPE_I32,
        InlineElem::I64 => NATIVE_TYPE_I64,
        _ => NATIVE_TYPE_I128,
    };
    Ok((tag, bytes))
}

/// UTF-8 bytes of the texts and their `len + 1` host-order i64 offsets from 0.
fn utf8_bytes_and_offsets(texts: &[String]) -> Result<(Vec<u8>, Vec<u8>), WorkerError> {
    let mut bytes = vec![];
    let mut offsets = 0i64.to_ne_bytes().to_vec();
    for text in texts {
        bytes.extend(text.as_bytes());
        let end = i64::try_from(bytes.len()).map_err(|_| inline_error("inline text extent overflow"))?;
        offsets.extend(end.to_ne_bytes());
    }
    Ok((bytes, offsets))
}

/// `bytes` copied into 16-byte aligned words (at least one word, so an empty column still has a valid pointer).
fn aligned_words(bytes: &[u8]) -> Vec<u128> {
    let mut words = vec![0u128; bytes.len().div_ceil(16).max(1)];
    // SAFETY: `words` holds at least `bytes.len()` bytes and does not overlap `bytes`.
    unsafe { std::ptr::copy_nonoverlapping(bytes.as_ptr(), words.as_mut_ptr().cast::<u8>(), bytes.len()) };
    words
}

fn inline_error(reason: impl Into<String>) -> WorkerError {
    WorkerError::Inline(reason.into())
}
