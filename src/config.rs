//! The nanocomparator input configuration.

use serde::Deserialize;
use std::path::PathBuf;

#[derive(Debug, Clone, Deserialize)]
pub struct Config {
    /// Path to the challenge export file.
    pub challenge_export: PathBuf,

    /// Path to the solution export file.
    pub solution_export: PathBuf,

    /// The names of the theorems the solution must prove.
    pub theorem_names: Vec<String>,

    /// The names of the definition holes the challenge leaves open.
    #[serde(default)]
    pub definition_names: Vec<String>,

    /// The axioms the solution is permitted to use.
    pub permitted_axioms: Vec<String>,
}
