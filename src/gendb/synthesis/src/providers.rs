//! Provider sessions: the adapters that run an author for the controller (`controller::AuthorTransport`).
//!
//! One provider is supported: [`claude_code`], Claude Code CLI sessions (one fresh session per attempt) pinned to one model and effort,
//! with the author's built-in tools, the framework's structured local tools (MCP) and a per-tool activity lease for
//! Bash. The controller owns every accounting decision; the adapter reports what the provider returned, unchanged,
//! with the declared scope of its usage fields.
//!
//! Trust: outside the TCB. Provider receipts are observations for accounting; an author's output is a proposal the
//! role evaluates, never authority.

pub mod claude_code;

pub use claude_code::{AuthorModel, ClaudeCode, InspectionError, LocalToolServer};
