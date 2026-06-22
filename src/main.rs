//! nanocomparator command-line entry point.
//!
//! Usage: `nanocomparator <config.json>`.

use nanocomparator::compare::{compare_at, PRIMITIVE_TARGETS};
use nanocomparator::config::Config;
use nanoda_lib::util::{Config as NanodaConfig, ExportFile};
use std::error::Error;
use std::path::Path;

fn main() -> Result<(), Box<dyn Error>> {
    let mut args = std::env::args();
    let _ = args.next();

    let config_path = match args.next() {
        Some(p) => p,
        None => {
            return Err("Expected a path to a configuration file as the first argument.".into());
        }
    };

    let contents = std::fs::read_to_string(&config_path)?;

    let config: Config = serde_json::from_str(&contents)?;

    verify_match(&config)?;

    Ok(())
}

/// `Comparator.verifyMatch` from Comparator.
fn verify_match(config: &Config) -> Result<(), Box<dyn Error>> {
    let challenge = parse_challenge(&config.challenge_export)?;
    let solution = parse_solution(&config.solution_export, &config.permitted_axioms)?;

    let definition_names: Vec<&str> = config.definition_names.iter().map(|n| n.as_str()).collect();
    let targets: Vec<&str> =
        config.theorem_names.iter().chain(config.permitted_axioms.iter()).map(|n| n.as_str()).collect();

    compare_at(&challenge, &solution, &targets, &definition_names, PRIMITIVE_TARGETS)?;
    solution.check_all_declars();

    println!("Your solution is okay!");
    Ok(())
}

fn parse_challenge(path: &Path) -> Result<ExportFile<'static>, Box<dyn Error>> {
    parse_with(serde_json::json!({
        "export_file_path": path,
        "unsafe_permit_all_axioms": true,
        "unpermitted_axiom_hard_error": false,
        "nat_extension": true,
        "string_extension": true,
    }))
}

fn parse_solution(path: &Path, permitted_axioms: &[String]) -> Result<ExportFile<'static>, Box<dyn Error>> {
    parse_with(serde_json::json!({
        "export_file_path": path,
        "permitted_axioms": permitted_axioms,
        "unpermitted_axiom_hard_error": true,
        "nat_extension": true,
        "string_extension": true,
    }))
}

fn parse_with(config_value: serde_json::Value) -> Result<ExportFile<'static>, Box<dyn Error>> {
    let config: NanodaConfig = serde_json::from_value(config_value).unwrap();
    let (export_file, _skipped) = config.to_export_file()?;
    Ok(export_file)
}
