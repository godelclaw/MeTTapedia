# Mettapedia formalized mathematics encyclopedia

Mettapedia hosts formalizations across probability theory, information theory, logic, set theory, and related areas.

## High-level structure

The package layout is:

```
Mettapedia/
├── Algebra/
├── Bridge/
├── CategoricalLogic/
├── CategoryTheory/
├── CogArch/
├── Computability/
├── Examples/
├── GraphTheory/
├── GSLT/
├── Implementation/
├── InformationTheory/
├── Languages/
├── Logic/
├── MeasureTheory/
├── Metatheory/
├── OSLF/
├── ProbabilityTheory/
├── QuantumTheory/
├── SetTheory/
├── UniversalAI/
└── externals/
```

## Toolchain

- The toolchain uses Lean 4.33.1 (see `lean-toolchain`).
- The Mathlib revision is recorded in `lake-manifest.json`.
- The default local developer configuration is `lakefile.lean`, which uses
  local repos in `../externals/` for Foundation, exchangeability, provenance,
  OrderedSemigroups, Metatheory, CertifyingDatalog, and `mm-lean4`.
- `../bootstrap_local_repos.sh` records published dependency revisions;
  `../upgrades/4.33.1/externals.json` records migration source fingerprints
  and the compatibility overlays applied to fresh checkouts.
  Existing editable dependency checkouts can differ from those revisions and
  must be checked when reproducing a build.

## Build

```bash
./lean/bootstrap_local_repos.sh
cd lean/mettapedia
lake exe cache get
scripts/check_library_sanity.sh
```

- `bootstrap_local_repos.sh` clones the local editable repos into
  `lean/externals/` and `lean/standalone/` if they are missing, then leaves
  existing working trees alone.
- The build runs from `lean/mettapedia`.
- The first build should run `lake exe cache get` to fetch mathlib oleans.
- Prefer targeted `lake update <pkg>` over bare `lake update`; the bare form
  can bump transitive dependencies beyond the pinned toolchain.

### Qualification and source coverage

`scripts/check_library_sanity.sh` builds the library aggregates and comparison
entrypoints, checks their freshness with `lake --no-build build`, and checks
tracked internal imports, source coverage and the required local dependencies'
effective source fingerprints. `--no-build` skips compilation;
`--coverage` checks sources only; `--list` prints the target list. A nonzero
status means qualification is incomplete.

The coverage check reads Lean import headers, including `public` and `meta`
imports and nested comments. It reports modules outside the named roots'
transitive import closure, separately from missing imports and build failures.
Such modules need review: absence from an aggregate does not make a theorem
obsolete or justify its removal. Coverage is not an axiom audit or a proof of
build success. Separate Lake packages, such as `../krenn`, need their own builds.

The complete inventory, coverage lists and current source hashes are written to
`.lake/library-sanity-coverage.json`; set `SANITY_COVERAGE_REPORT` to choose a
different output file. Run the tooling's regression tests with
`python3 scripts/test_library_sanity.py`.

## Notable subprojects

- `Examples/PLN/`
  - Examples/PLN hosts worked PLN and WM-PLN curriculum examples, including
    raven induction, disease abduction, multi-source evidence, estimator
    envelopes, WM-4 introspection, and the LC/BinaryEvidence logic tower.

- `ProbabilityTheory/KnuthSkilling/`
  - ProbabilityTheory/KnuthSkilling hosts Knuth-Skilling Foundations of Inference proofs

- `ProbabilityTheory/Cox/`
  - ProbabilityTheory/Cox hosts Cox-style probability calculus formalization

- `InformationTheory/ShannonEntropy/`
  - InformationTheory/ShannonEntropy hosts Shannon entropy formalization

- `Logic/`
  - Logic hosts PLN, evidence quantales, Solomonoff induction, exchangeability, and world model calculus

- `SetTheory/BorelDeterminacy/`
  - SetTheory/BorelDeterminacy hosts Borel determinacy formalization

- `OSLF/`
  - OSLF hosts core OSLF and GSLT formalizations

- `GSLT/`
  - GSLT hosts the categorical specification layer for OSLF

- `Languages/GF/`
  - Languages/GF hosts GF abstract syntax, Czech morphology, English clause construction, and an NTT semantic bridge

- `Languages/ProcessCalculi/`
  - Languages/ProcessCalculi hosts pi-calculus, rho-calculus, spice calculus, and pi-to-rho encoding

- `CategoryTheory/`
  - CategoryTheory hosts NativeTypeTheory, a PLN categorical instance, and de Finetti categorical development

- `CogArch/`
  - CogArch hosts MetaMo, OpenPsi, MicroPsi, and value-system models

- `Algebra/OrderedSemigroups/`
  - Algebra/OrderedSemigroups hosts ordered semigroup formalization

- `UniversalAI/`
  - UniversalAI hosts Hutter (2005) Chapters 4–7: AIXI agents, value functions, intelligence measure, time-bounded AIXI, problem classes, multi-agent extensions, self-modification, Gödel machines (~27K lines, 71 files)

- `Logic/HOL/`
  - Logic/HOL hosts Church-style higher-order logic: Henkin semantics, classical + intuitionistic soundness, Lindenbaum quotients, Henkinization, logical induction, probabilistic semantics (54 files)

- `Logic/UniversalPrediction/`
  - Logic/UniversalPrediction hosts Solomonoff–Hutter universal prediction theory (Chapters 2–3): prefix measures, enumeration, convergence, loss/error bounds, optimality (37 files, ~12.9K lines)

- `Languages/MeTTa/TwoSortKernel/`
  - Languages/MeTTa/TwoSortKernel hosts the trusted proof kernel for dependently-typed MeTTa Pure: Pi/Sigma/Id/universes, general declaration mechanism, pilot families (Bool, Nat, Unit)

- `Ethics/`
  - Ethics hosts Gewirth PGC formalization (port of Fuenmayor & Benzmüller AFP Isabelle/HOL work into Lean 4; drops 5 of 8 axioms as unnecessary)

- `Conformance/`
  - Conformance hosts runtime/spec boundary testing: kernel-checked I→O derivation proofs matching unit test expectations (6 files, ~2.7K lines)

- `CategoricalLogic/`
  - CategoricalLogic hosts categorical logic formalization

## Lean to mettail-rust example

The roundtrip and benchmark scripts live in the companion ai-agents workspace
(`hyperon/mettail-rust`), outside this repository.

```bash
# in the ai-agents workspace:
cd hyperon/mettail-rust
./scripts/roundtrip_mettaminimal.sh
./scripts/bench_mettaminimal_roundtrip.sh
```

- the exporter is hyperon/mettail-rust/scripts/lean/ExportMeTTaMinimalRoundTrip.lean (same workspace).

## Status review

- Proof completeness varies by subproject.
- Use `rg -n "s[o]rry" Mettapedia/` to find proof gaps.
- `Mettapedia/ProbabilityTheory/KnuthSkilling/README.md` contains the
  Knuth-Skilling structure and build targets.

```bash
rg -n "s[o]rry" Mettapedia/
```

## Contribution

- Contributions require explicit proofs.
- Contributions require documented theorem sources.
- Contributions require frequent `lake build` checks.

## External repo policy

- Use `zariuq` forks as `origin` remotes.
- Use source projects as `upstream` remotes, and use `godelclaw` only as a
  separate named remote when relevant.
- See `EXTERNAL_REPOS.md` for exact commands.
