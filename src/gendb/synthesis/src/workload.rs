//! The workload storage role: one author session, run before the query sessions, designs, proves and builds the
//! storages the workload's statements share.
//!
//! - [`submission`]: `verus-storages.json`, the workload submission (one or more storage manifests), and its freeze;
//! - [`role`]: [`role::StorageAuthorRole`], the `SynthesisRole` and `LocalJobs` of the session.
//!
//! The storage authoring itself (manifest, freeze, check-and-build, registration, capture extension, catalog) is the
//! shared `crate::storage` path, which query authors use too.

pub mod role;
pub mod submission;

pub use role::{StorageAuthorRole, StorageRoleConfig};
