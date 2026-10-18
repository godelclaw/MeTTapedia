# The Krenn–Gu conjecture: retained search corpus

This branch preserves the Lean 4.31 search corpus and its replay dependencies.
The canonical shared mathematics lives on main in
[matching theory](https://github.com/godelclaw/MeTTapedia/tree/main/lean/mettapedia/Mettapedia/Combinatorics/Matching),
[GHZ weighted matchings](https://github.com/godelclaw/MeTTapedia/tree/main/lean/mettapedia/Mettapedia/Combinatorics/Matching/GHZ),
and [polynomial certificates](https://github.com/godelclaw/MeTTapedia/tree/main/lean/mettapedia/Mettapedia/Algebra/Polynomial).
The older structural modules retained here preserve reproducible proof replay on
the pinned toolchain. Search artifacts remain outside the default shared-library
build.

> **Claim boundary.** Nothing here proves the Krenn–Gu conjecture. The general results
> are *conditional*: each derives the official arbitrary-size statement from an explicit
> structural hypothesis that is itself open. The finite `N = 6` work is a *partial*
> certified corpus with explicit coverage hypotheses, not a complete verification of that
> case. See **What is proved** and **What is open** below.

## The statement

`OfficialConditional.OfficialKrennGu` is

```lean
∀ n : ℕ, 3 ≤ n → ¬ ∃ W : WeightsN (2 * n) 3 ℂ, EqSystemN (2 * n) 3 W
```

— no weight system on `2n ≥ 6` sites in three colours satisfies the GHZ equations.
Every general theorem in this project targets exactly this proposition; none discharges
it unconditionally.

## What is proved

**Reusable matching foundations, for every vertex count** (sources in
`../mettapedia/Mettapedia/Combinatorics/Matching/`). These include perfect-matching
representations and graph bridges, weighted subset sums and two-pivot crossing,
restriction and Kempe exchange, Hall and non-cancellation criteria, loop erasure and
support, gauge and cap incidence, block-rank identities, alternating cycles, and the
four-vertex pairing classification and abstract fourth-matching theorem. They are
independent of the Krenn–Gu equations and
available through the normal MeTTapedia combinatorics umbrella.

**The Krenn structural layer, for every vertex count** (`lake build KrennLib`, sources
in `lib/`). This specializes the shared theory to three-colour GHZ amplitudes, develops
support-minimal systems, and proves the conditional star/crossing, degeneracy, fan, and
descent interfaces. Compatibility modules preserve the historical Krenn import paths
without duplicating the shared proofs. See `lib/README.md`.

**Reductions to the official statement** (`lake build KrennGeneralBridge`). Theorems of
the form

```lean
theorem official_of_X (h : X) (had : AllDegenerate) : OfficialKrennGu
```

for several structural `X`, together with the converse equivalences showing these are
*equivalent structural targets* rather than weaker hypotheses: the conjecture implies
each of them back. That symmetry is the honest reading — the reductions relocate the
difficulty, they do not reduce it.

**A partial certified corpus for the six-site case** (default target, `lake build`).
Machine-checked refutations of finite branch tables reached by an explicit case
decomposition, assembled through interfaces whose remaining obligations are stated as
hypotheses rather than assumed: `KrennCase0ProofAssembly`,
`KrennAllCollapseAssembly`, `KrennX5PartialAssembly`. The last is explicitly partial —
its final theorem's only hypothesis is finite coverage of the 336 representative
ordinals, and that coverage is not complete.

## What is open

- Every structural hypothesis feeding a `official_of_X` reduction.
- Completion of the `X5` representative coverage.
- The remaining branch obligations carried explicitly by the assembly interfaces.

## Build

Lean `4.31.0` with Mathlib pinned in `lake-manifest.json`; no other dependency.

| Target | Command | Contents |
|---|---|---|
| `KrennLib` | `lake build KrennLib` | the Krenn/GHZ structural layer (`lib/`) |
| `KrennGeneralBridge` | `lake build KrennGeneralBridge` | official statement and the conditional reductions |
| `KrennRank` (default) | `lake build` | the `N = 6` certified corpus |
| `KrennType01` | `lake build KrennType01` | the completed type-01 chart closures |
| `KrennChart0Support` | `lake build KrennChart0Support` | kernel-replayed LRAT consequences |
| `KrennCorpus` | `lake build KrennCorpus` | every retained non-library module, including sources outside the default closure |

The default target's module manifest is **fail-closed**. `lakefile.lean` carries the
import closure of its roots explicitly, compressed to a whole-directory glob only where
every tracked module in that directory is reachable. This prevents a stale project
`.olean` from silently satisfying an omitted import.

`corpus-modules.txt` lists every retained non-library proof module. Together,
`lake build KrennLib KrennCorpus` checks the complete retained source inventory;
the historical default target continues to describe only its designated proof
assembly. Including a module in either target does not discharge an assembly's
explicit mathematical hypotheses.

## Axiom footprint

The accepted foundation is exactly

```
[propext, Classical.choice, Quot.sound]
```

`lib/AxiomAudit.lean` prints the dependency cone of each top-level conditional theorem,
and the generated corpus prints its own per-leaf cones during the build. No file in this
project declares an axiom, and none uses `sorry`, `admit`, `native_decide`, or any
compiler-trust escape hatch.

After building, run `lake env lean --run scripts/check_corpus_axioms.lean`.
It imports the full proof manifest and all library sources together, checks every
compiled mathematical declaration, and rejects axioms outside the three above.
The audit program itself is checked separately with
`lake env lean scripts/check_corpus_axioms.lean`.

The 395 activity masks and their 2,868 ordered strata share one global,
kernel-replayed cover certificate. A semantic adapter proves each activity
slice from that certificate and checks the concrete table by reduction.
`KrennCollapseSupportCoverData` preserves the historical Boolean interface
through compatibility wrappers. The concrete tables and theorem statements
are unchanged.

## Provenance and reproducibility

The corpus contains generated search output. Its retained Lean files and
`.cnf`/`.lrat` inputs are sufficient for proof replay; external search generators
and solvers are not build dependencies.

Lean's kernel checks the resulting proof terms. Receipts and content hashes
identify source artifacts and provenance; they do not establish mathematical
truth or replace a kernel-checked proof. A refuted branch also does not establish
coverage of the branches that remain outside an assembly's hypotheses.

This formalization was written independently. It contains no material from any external
Krenn–Gu certificate repository. Licensed under the repository's MIT license.

## Source

Synthesized from four audited development lanes:

| Lane | Commit |
|---|---|
| certified corpus | `512e810c73e109220f5b6af39252e1c840eb32b9` |
| structural / X5 connector | `a5de0c5527145dc6f8f39bec60eea8e7170ccee0` |
| chart-zero | `0abedeca5dc5c4746e1699d07345e5de0742506d` |
| multilinear trace | `75f5532ae7c5e987cadb031de53ccf6613ff8b3b` |

Merging them required one semantic resolution, in `lakefile.lean`: the certified lane's
fail-closed closure machinery is retained and the structural lane's library roots are
added to it, with the module manifest regenerated over the union.

After migration, the conjecture-independent matching theory was extracted without
changing theorem statements used by Krenn. The old module paths are either thin
compatibility imports or contain only Krenn/GHZ consequences; the shared implementations
live under the MeTTapedia combinatorics hierarchy.
