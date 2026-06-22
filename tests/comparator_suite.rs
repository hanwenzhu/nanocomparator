//! Compatibility tests driven by the upstream Comparator fixture projects.
//!
//! Run with:
//!
//! ```text
//! NANOCOMPARATOR_COMPARATOR_DIR=/path/to/comparator \
//!   cargo test --test comparator_suite -- --ignored --nocapture
//! ```

use nanocomparator::compare::PRIMITIVE_TARGETS;
use serde::Deserialize;
use std::collections::HashSet;
use std::ffi::OsStr;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::{Command, Output};
use std::time::{SystemTime, UNIX_EPOCH};

const COMPARATOR_DIR_ENV: &str = "NANOCOMPARATOR_COMPARATOR_DIR";

#[derive(Deserialize)]
struct ComparatorConfig {
    challenge_module: String,
    solution_module: String,
    theorem_names: Vec<String>,
    #[serde(default)]
    definition_names: Vec<String>,
    permitted_axioms: Vec<String>,
}

#[derive(Deserialize)]
struct TestConfig {
    exit_code: i32,
}

struct TempProject(PathBuf);

impl TempProject {
    fn new(fixture: &Path) -> Self {
        let fixture_name =
            fixture.file_name().and_then(OsStr::to_str).expect("fixture directory must have a UTF-8 name");
        let nonce =
            SystemTime::now().duration_since(UNIX_EPOCH).expect("system clock must be after the Unix epoch").as_nanos();
        let path = std::env::temp_dir().join(format!("nanocomparator-{fixture_name}-{}-{nonce}", std::process::id()));
        fs::create_dir(&path).expect("failed to create temporary fixture directory");
        copy_dir_contents(fixture, &path);
        Self(path)
    }
}

impl Drop for TempProject {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.0);
    }
}

#[test]
#[ignore = "requires an external Comparator checkout and Lean toolchain"]
fn all_comparator_fixtures() {
    let comparator_dir = std::env::var_os(COMPARATOR_DIR_ENV)
        .map(PathBuf::from)
        .unwrap_or_else(|| panic!("set {COMPARATOR_DIR_ENV} to the root of a Comparator checkout; see README.md"));
    let comparator_dir = comparator_dir
        .canonicalize()
        .unwrap_or_else(|error| panic!("invalid Comparator directory {comparator_dir:?}: {error}"));
    let projects_dir = comparator_dir.join("tests/projects");
    assert!(projects_dir.is_dir(), "Comparator fixtures not found at {}", projects_dir.display());

    let lean4export = comparator_dir.join(".lake/packages/lean4export/.lake/build/bin/lean4export");
    if !lean4export.is_file() {
        run_checked(
            Command::new("lake").current_dir(&comparator_dir).args(["build", "lean4export"]),
            "building Comparator's lean4export",
        );
    }

    let mut fixtures: Vec<_> = fs::read_dir(&projects_dir)
        .unwrap_or_else(|error| panic!("failed to read {}: {error}", projects_dir.display()))
        .map(|entry| entry.expect("failed to read fixture directory entry").path())
        .filter(|path| path.is_dir())
        .collect();
    fixtures.sort();

    let mut mismatches = Vec::new();
    for fixture in fixtures {
        let fixture_name =
            fixture.file_name().and_then(OsStr::to_str).expect("fixture directory must have a UTF-8 name");
        let config: ComparatorConfig = read_json(&fixture.join("config.json"));
        let expected: TestConfig = read_json(&fixture.join("test.json"));
        let project = prepare_project(&fixture, &comparator_dir);
        let export_targets = export_targets(&config);

        build_module(&project.0, &config.challenge_module);
        let challenge_export = export_module(&project.0, &lean4export, &config.challenge_module, &export_targets);

        build_module(&project.0, &config.solution_module);
        let solution_export = export_module(&project.0, &lean4export, &config.solution_module, &export_targets);
        let challenge_path = project.0.join("challenge.export");
        let solution_path = project.0.join("solution.export");
        fs::write(&challenge_path, challenge_export).expect("failed to write challenge export");
        fs::write(&solution_path, solution_export).expect("failed to write solution export");

        let nanocomparator_config = serde_json::json!({
            "challenge_export": challenge_path,
            "solution_export": solution_path,
            "theorem_names": config.theorem_names,
            "definition_names": config.definition_names,
            "permitted_axioms": config.permitted_axioms,
        });
        let nanocomparator_config_path = project.0.join("nanocomparator.json");
        fs::write(
            &nanocomparator_config_path,
            serde_json::to_vec_pretty(&nanocomparator_config).expect("failed to encode nanocomparator config"),
        )
        .expect("failed to write nanocomparator config");

        let output = Command::new(env!("CARGO_BIN_EXE_nanocomparator"))
            .arg(&nanocomparator_config_path)
            .output()
            .unwrap_or_else(|error| panic!("failed to run nanocomparator for {fixture_name}: {error}"));
        let expected_success = expected.exit_code == 0;
        if output.status.success() == expected_success {
            eprintln!("{fixture_name}: passed");
        } else {
            mismatches.push(format!(
                "{fixture_name}: expected {}, got {}\nstdout:\n{}\nstderr:\n{}",
                if expected_success { "acceptance" } else { "rejection" },
                output.status,
                String::from_utf8_lossy(&output.stdout),
                String::from_utf8_lossy(&output.stderr),
            ));
        }
    }

    assert!(mismatches.is_empty(), "Comparator compatibility mismatches:\n\n{}", mismatches.join("\n\n"));
}

fn prepare_project(fixture: &Path, comparator_dir: &Path) -> TempProject {
    let project = TempProject::new(fixture);
    fs::copy(comparator_dir.join("lean-toolchain"), project.0.join("lean-toolchain"))
        .expect("failed to copy Comparator lean-toolchain");
    let lakefile = project.0.join("lakefile.toml");
    if !lakefile.exists() {
        fs::write(
            lakefile,
            r#"name = "comparatortest"
version = "0.1.0"

[[lean_lib]]
name = "Solution"

[[lean_lib]]
name = "Challenge"
"#,
        )
        .expect("failed to write default fixture lakefile");
    }
    project
}

fn copy_dir_contents(source: &Path, destination: &Path) {
    for entry in fs::read_dir(source).unwrap_or_else(|error| panic!("failed to read {}: {error}", source.display())) {
        let entry = entry.expect("failed to read directory entry");
        let source_path = entry.path();
        let destination_path = destination.join(entry.file_name());
        if source_path.is_dir() {
            fs::create_dir(&destination_path).expect("failed to create copied directory");
            copy_dir_contents(&source_path, &destination_path);
        } else {
            fs::copy(&source_path, &destination_path).unwrap_or_else(|error| {
                panic!("failed to copy {} to {}: {error}", source_path.display(), destination_path.display())
            });
        }
    }
}

fn build_module(project: &Path, module: &str) {
    run_checked(
        Command::new("lake").current_dir(project).args(["build", module]),
        &format!("building module {module}"),
    );
}

fn export_module(project: &Path, lean4export: &Path, module: &str, targets: &[String]) -> Vec<u8> {
    let output = Command::new("lake")
        .current_dir(project)
        .arg("env")
        .arg(lean4export)
        .arg(module)
        .arg("--")
        .args(targets)
        .output()
        .unwrap_or_else(|error| panic!("failed to export module {module}: {error}"));
    assert_output_success(&output, &format!("exporting module {module}"));
    output.stdout
}

fn export_targets(config: &ComparatorConfig) -> Vec<String> {
    let mut targets = vec![
        "Nat".to_owned(),
        "String".to_owned(),
        "String.mk".to_owned(),
        "Char".to_owned(),
        "Char.ofNat".to_owned(),
        "List".to_owned(),
    ];
    if config.permitted_axioms.iter().any(|name| name == "Quot.sound") {
        targets.extend(["Quot", "Quot.mk", "Quot.lift", "Quot.ind"].into_iter().map(str::to_owned));
    }
    targets.extend(config.theorem_names.iter().cloned());
    targets.extend(config.permitted_axioms.iter().cloned());
    targets.extend(PRIMITIVE_TARGETS.iter().map(|name| (*name).to_owned()));
    targets.extend(config.definition_names.iter().cloned());

    let mut seen = HashSet::new();
    targets.retain(|target| seen.insert(target.clone()));
    targets
}

fn read_json<T: for<'de> Deserialize<'de>>(path: &Path) -> T {
    let bytes = fs::read(path).unwrap_or_else(|error| panic!("failed to read {}: {error}", path.display()));
    serde_json::from_slice(&bytes).unwrap_or_else(|error| panic!("failed to decode {}: {error}", path.display()))
}

fn run_checked(command: &mut Command, description: &str) {
    let output = command.output().unwrap_or_else(|error| panic!("failed while {description}: {error}"));
    assert_output_success(&output, description);
}

fn assert_output_success(output: &Output, description: &str) {
    assert!(
        output.status.success(),
        "failed while {description}: {}\nstdout:\n{}\nstderr:\n{}",
        output.status,
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr),
    );
}
