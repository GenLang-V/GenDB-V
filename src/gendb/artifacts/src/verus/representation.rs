//! Data representations whose builder and reader were checked in a build, and their built assets.
//!
//! A representation names every distinct source table it reads. An asset is the builder's stored parts for exactly
//! one key: the representation plus each source table's current source version (the dataset's file-metadata stamp),
//! fields and row count. A changed version of any table is a different key, so a stale asset is never returned.
//! Each key has its own stream (`verus-asset.<key identity>`), published once.

use super::build::check_build_evidence;
use super::{RecordError, current_subject, read_record, rejected};
use crate::append_only::append_record;
use crate::canonical_json::{CanonError, content_id};
use crate::column::ColumnSpec;
use crate::content_id::ContentId;
use crate::object_store::ObjectStore;
use serde::{Deserialize, Serialize};
use std::collections::BTreeSet;
use std::path::PathBuf;

pub const VERUS_REPRESENTATION_V2_KIND: &str = "gendb.verus.representation.v2";
pub const VERUS_ASSET_V2_KIND: &str = "gendb.verus.asset.v2";
const VERUS_ASSET_KEY_V2_KIND: &str = "gendb.verus.asset-key.v2";
/// Kind of the record that publishes an asset on its key's stream. The name comes from the native source-view
/// records whose format assets reused; saved libraries contain it, so it cannot change.
pub const VERUS_ASSET_PROMOTION_KIND: &str = "gendb.native.source-view-promotion.v1";
/// Gate identity written into every asset publication made by a Verus representation builder.
pub const VERUS_ASSET_GATE: &str = "gendb.verus.asset-build.v1";

/// One distinct source table of a representation: its fields `(original ordinal, column)` in the contract's field
/// order. A table read by several FROM occurrences (a self-join) is listed once.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct VerusSourceTableV2 {
    pub table: String,
    pub fields: Vec<(usize, ColumnSpec)>,
}

/// A representation whose builder and reader were checked in `build`, built from `sources` (contract table order;
/// the ABI column list is their fields, table by table).
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct VerusRepresentationV2 {
    pub build: ContentId,
    pub name: String,
    pub sources: Vec<VerusSourceTableV2>,
    /// Part element types in ABI order (`i8` … `u64`).
    pub parts: Vec<String>,
    pub decode_item: String,
    pub builder_item: String,
}

/// One source table of an asset key.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct VerusAssetSourceV2 {
    pub table: String,
    pub source_version: String,
    pub fields: Vec<(usize, ColumnSpec)>,
    pub rows: usize,
}

/// Gives a source table's current source version and row count (for example from the prepared dataset).
pub type CurrentSource<'a> = dyn Fn(&str) -> Result<(String, usize), String> + 'a;

/// Applicability key of one built asset: every source table of the representation with its source version.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct VerusAssetKeyV2 {
    pub sources: Vec<VerusAssetSourceV2>,
    pub representation: ContentId,
}

impl VerusAssetKeyV2 {
    pub fn identity(&self) -> Result<ContentId, CanonError> {
        content_id(1, VERUS_ASSET_KEY_V2_KIND, self)
    }

    pub fn stream(&self) -> Result<String, CanonError> {
        Ok(format!("verus-asset.{}", self.identity()?.to_hex()))
    }

    /// The key of `representation` for the current data: `current(table)` gives each source table's current source
    /// version and row count. Every source table must be covered; a missing one is an error, never a partial key.
    pub fn current(
        representation_id: ContentId,
        representation: &VerusRepresentationV2,
        current: &CurrentSource<'_>,
    ) -> Result<Self, RecordError> {
        let sources = representation
            .sources
            .iter()
            .map(|source| {
                let (source_version, rows) = current(&source.table).map_err(RecordError::CurrentSource)?;
                Ok(VerusAssetSourceV2 { table: source.table.clone(), source_version, fields: source.fields.clone(), rows })
            })
            .collect::<Result<Vec<_>, RecordError>>()?;
        Ok(Self { sources, representation: representation_id })
    }
}

/// A published asset: the builder's parts for exactly the key's source versions, stored once and never rewritten.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct VerusAssetManifestV2 {
    pub key: VerusAssetKeyV2,
    pub storage_directory: PathBuf,
    pub build_wall_ns: u128,
    pub storage_bytes: u64,
}

/// Publication of one asset manifest on its key's stream, naming the gate and the build evidence.
#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct VerusAssetPromotionV1 {
    pub manifest: ContentId,
    pub gate_identity: String,
    pub evidence: ContentId,
}

/// Publish a representation record after checking its source tables.
pub fn publish_representation_v2(
    store: &ObjectStore,
    representation: &VerusRepresentationV2,
) -> Result<ContentId, RecordError> {
    check_source_tables(&representation.sources)?;
    Ok(store.put(1, VERUS_REPRESENTATION_V2_KIND, representation)?)
}

/// Publish one built asset for exactly the key's source versions. The key's representation must come from a build
/// that passes [`check_build_evidence`]; the key must list exactly the representation's source tables and fields, in
/// order, each with a source version; the parts directory is absolute and is never rewritten; one asset per key.
pub fn publish_asset_v2(
    store: &ObjectStore,
    key: VerusAssetKeyV2,
    storage_directory: PathBuf,
    build_wall_ns: u128,
    storage_bytes: u64,
    evidence: ContentId,
) -> Result<ContentId, RecordError> {
    let representation: VerusRepresentationV2 = read_record(store, key.representation, VERUS_REPRESENTATION_V2_KIND)?;
    check_build_evidence(store, representation.build)?;
    check_source_tables(&representation.sources)?;
    let key_covers_representation = key.sources.len() == representation.sources.len()
        && key.sources.iter().zip(&representation.sources).all(|(keyed, declared)| {
            keyed.table == declared.table && keyed.fields == declared.fields && !keyed.source_version.is_empty()
        });
    if !key_covers_representation || !storage_directory.is_absolute() {
        return Err(rejected("asset key differs from its representation's source tables or lacks a source version"));
    }
    store.read(evidence)?;
    if resolve_asset_v2(store, &key)?.is_some() {
        return Err(rejected("an asset for these source versions and this representation is already published"));
    }
    let stream = key.stream()?;
    let manifest = VerusAssetManifestV2 { key, storage_directory, build_wall_ns, storage_bytes };
    let manifest_id = store.put(1, VERUS_ASSET_V2_KIND, &manifest)?;
    let promotion = VerusAssetPromotionV1 { manifest: manifest_id, gate_identity: VERUS_ASSET_GATE.into(), evidence };
    let promotion_id = store.put(1, VERUS_ASSET_PROMOTION_KIND, &promotion)?;
    append_record(store, &stream, promotion_id)?;
    Ok(manifest_id)
}

/// The published asset for exactly this key, if any: `(manifest id, manifest)`.
pub fn resolve_asset_v2(
    store: &ObjectStore,
    key: &VerusAssetKeyV2,
) -> Result<Option<(ContentId, VerusAssetManifestV2)>, RecordError> {
    let Some(promotion_id) = current_subject(store, &key.stream()?)? else {
        return Ok(None);
    };
    let promotion: VerusAssetPromotionV1 = read_record(store, promotion_id, VERUS_ASSET_PROMOTION_KIND)?;
    if promotion.gate_identity != VERUS_ASSET_GATE {
        return Err(rejected("verus asset stream was not published by the Verus asset gate"));
    }
    let manifest: VerusAssetManifestV2 = read_record(store, promotion.manifest, VERUS_ASSET_V2_KIND)?;
    if &manifest.key != key {
        return Err(rejected("published asset key differs from its stream"));
    }
    Ok(Some((promotion.manifest, manifest)))
}

/// At least one source table; tables distinct; each with at least one field in strictly ascending ordinal order.
fn check_source_tables(sources: &[VerusSourceTableV2]) -> Result<(), RecordError> {
    if sources.is_empty() {
        return Err(rejected("a representation reads at least one source table"));
    }
    let mut seen = BTreeSet::new();
    for source in sources {
        let ordered = !source.fields.is_empty() && source.fields.windows(2).all(|pair| pair[0].0 < pair[1].0);
        if !seen.insert(&source.table) || !ordered {
            return Err(rejected(format!(
                "representation source table {} is repeated or its fields are empty or unordered",
                source.table
            )));
        }
    }
    Ok(())
}
