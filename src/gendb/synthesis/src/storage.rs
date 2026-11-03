//! Storage authoring, shared by the workload storage role and the query role: the storage manifest, the run's shared
//! capture and its extension, the catalog of admitted storages, and registration (admission) of a checked, built
//! storage. Both roles reach these through the same local tools and qualification steps, so a query author can create
//! and register a storage in its own session exactly as a workload author does.
//!
//! - [`manifest`]: `verus-storage.json` and the storage declaration it names;
//! - [`freeze`]: a storage candidate frozen into an immutable storage crate (central source rule on both author roots);
//! - [`family`]: storage families (runs of several workloads): a family's manifest, its part template's expansion and
//!   the composition of one workload's instance as an ordinary workspace storage;
//! - [`budget`]: the storage budget (serving bytes of the admitted storages against the user's `data_allowance`);
//! - [`coverage`]: complete lossless coverage (every column of every table stored by some storage);
//! - [`build`]: the one check-and-build of a storage (verify+compile, checked build recorded, asset built once, tiny
//!   builds);
//! - [`diagnostic`]: unverified diagnostic storage builds (`verification: "not_run"`), never assets;
//! - [`identity`]: the builder identity of a storage build (asset reuse across builds that run the same code);
//! - [`capture`]: the current prepared capture shared by the sessions, extended by exactly the missing columns;
//! - [`catalog`]: admitted storage versions as authors see them (applicability, assets, interfaces, descriptions);
//! - [`reverify`]: applicability by content and re-verification of stale admitted storages against the current framework;
//! - [`registration`]: the one admission path of a storage package;
//! - [`policy`]: the user's stored-data policy (`storage_policy`): declarations, recorded kind and revision, eligible
//!   admitted storages;
//! - [`payload`]: one stored copy of each column's values under that policy (declared payload against the serving storage);
//! - [`exclusion`]: the user's persistent exclusions of storage packages under that policy (library records);
//! - [`flat`]: the fixed flat storages of `storage_policy` `fixed_flat`: eligibility, assets, readiness and their
//!   one-time preparation;
//! - [`engine_library`]: the engine library of a schema-engine run: its seed, and the storage policy of an engine
//!   version's storage uses as the serving storage will stand once that version is selected;
//! - [`asset_release`]: the general engine line's storage assets on a shared host: the heads' assets kept, superseded
//!   derived assets released (rebuilt by their stored builders when used again), and the free-space floor of every
//!   asset build.

pub mod asset_release;
pub mod budget;
pub mod library_lock;
pub mod build;
pub mod capture;
pub mod coverage;
pub mod diagnostic;
pub mod engine_library;
pub mod identity;
pub mod catalog;
pub mod exclusion;
pub mod family;
pub mod flat;
pub mod freeze;
pub mod manifest;
pub mod payload;
pub mod policy;
pub mod registration;
pub mod reverify;
