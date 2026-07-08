# nanocomparator

Nanocomparator is a pure-Rust reimplementation of the [Lean Comparator](https://github.com/leanprover/comparator),
built on top of [nanoda](https://github.com/ammkrn/nanoda_lib).

For an overview of what a Lean comparator does, please refer to Comparator's [README](https://github.com/leanprover/comparator).

## Usage

```sh
nanocomparator <config.json>
```

The configuration is a single JSON file:

```json
{
    "challenge_export": "/path/to/challenge/export",
    "solution_export":  "/path/to/solution/export",
    "theorem_names":    ["large_lt"],
    "definition_names": ["large"],
    "permitted_axioms": ["propext", "Quot.sound", "Classical.choice"]
}
```

where `challenge_export` and `solution_export` are [exports](https://github.com/leanprover/lean4export)
of the challenge and solution environments, respectively.

### Producing export files

Export files are produced by [`lean4export`](https://github.com/leanprover/lean4export). The
export must include the theorems, definition holes, permitted axioms, and the kernel
built-ins, such as [here](https://github.com/leanprover/comparator/blob/1b82ba006811f7e25d53858252372e4d85fd3921/Main.lean#L258-L259). For example:

```sh
lake env /path/to/lean4export Challenge -- \
  Nat String String.mk Char Char.ofNat List Quot Quot.mk Quot.lift Quot.ind \
  propext Quot.sound Classical.choice \
  Nat.add Nat.sub Nat.mul Nat.pow Nat.gcd Nat.div Nat.mod Nat.beq Nat.ble \
  Nat.land Nat.lor Nat.xor Nat.shiftLeft Nat.shiftRight String.ofList \
  my_theorem my_def_hole \
  > challenge.export
```

## Nanocomparator vs Comparator

Nanocomparator tries to recreate the logic of Comparator while re-using utilities from nanoda.

- The file [`src/compare.rs`](src/compare.rs) contains a line-by-line translation of Comparator's
Compare.lean (as of writing).
- The file [`src/eq.rs`](src/eq.rs) contains a translation of the Lean kernel's `lean_expr_eqv`.

There are notable divergences:

- Nanocomparator does not compare differences between fields not retained by nanoda.
  It is unclear if these will actually produce corner cases where Comparator rejects and Nanocomparator accepts
  on some pathological input, but such corner cases should not be soundness issues if they exist. These include fields like:
  - The `all` field of definitions: it should be singleton list in exports (is this correct?).
  - The `safety` field of definitions: nanoda asserts it is `safe` at parse time.
  - The `kind` field of quot constants: it is redundant given the name.
  - The `isReflexive` field of inductives: it is redundant given constructor types.
- Similarly, divergences between nanoda and the Lean kernel, such as back-ref continuity, would still surface at Nanocomparator.
- Nanocomparator disallows any unpermitted axiom in the export environment (because it uses nanoda) while Comparator only checks
  the transitive dependencies of the targets. This should be fine if only transitive dependencies are exported anyway.
- The export files are produced by the user prior to running Nanocomparator. Unlike Comparator, this is not done by Nanocomparator.
  Depending on the threat model, this could be:
  - The submitter submits `.lean` files, and the checker exports them by a `lake build` + `lean4export`
    wrapped in a suitable `landrun`, like in Comparator.
  - The submitter is responsible for exporting its solution, and the checker only sees the exported solution.

## Testing

To test against Comparator's test suite:

```sh
NANOCOMPARATOR_COMPARATOR_DIR=/path/to/comparator \
  cargo test --test comparator_suite -- --ignored --nocapture
```

## Notes

Nanocomparator uses a [fork](https://github.com/hanwenzhu/nanoda_lib/tree/nanocomparator) of nanoda with small changes to define and expose certain functionalities.

Nanocomparator does not optimize for speed.
