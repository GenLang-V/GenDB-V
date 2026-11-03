//! The stored asset an admitted package runs over: the asset of its representation published for exactly the
//! current source version and row count of every source table (saved route; `gendb_storage::versions::CurrentCapture::
//! source_versions` gives them for the current capture).

use super::error::ServeError;
use gendb_artifacts::verus::{
    CurrentSource, VERUS_REPRESENTATION_V2_KIND, VerusAssetKeyV2, VerusRepresentationV2, resolve_asset_v2,
};
use gendb_artifacts::{ContentId, ObjectStore};
use std::path::PathBuf;

/// `(asset manifest id, stored parts directory)` of the admitted representation for the current data. Every source
/// table's current version and row count (`current`) must match a published asset; otherwise the asset must be built
/// offline first. Saved v1 representations (`RegisteredViewKey` assets) are served only by the earlier GenDB version.
pub fn current_asset(
    store: &ObjectStore,
    representation_id: ContentId,
    current: &CurrentSource<'_>,
) -> Result<(ContentId, PathBuf), ServeError> {
    let object = store.read(representation_id)?;
    if object.kind != VERUS_REPRESENTATION_V2_KIND {
        return Err(ServeError::RepresentationKind(object.kind));
    }
    let representation: VerusRepresentationV2 = object.decode()?;
    let key = VerusAssetKeyV2::current(representation_id, &representation, current)?;
    let (asset, manifest) = resolve_asset_v2(store, &key)?.ok_or(ServeError::NoAsset)?;
    Ok((asset, manifest.storage_directory))
}
