# The Krenn–Gu conjecture: a machine-checked programme

A standalone Lean 4 project. The Krenn development itself is **not** part of the
MeTTapedia default build and is not imported by any MeTTapedia umbrella module. Its
reusable foundations have been promoted to `Mettapedia.Combinatorics.Matching` and
`Mettapedia.Combinatorics.OrbitNormalization`, which are part of the shared library;
this directory retains the conjecture-specific layer and compatibility imports.

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

The default target's module manifest is **fail-closed**. `lakefile.lean` carries the
import closure of its roots explicitly, compressed to a whole-directory glob only where
every tracked module in that directory is reachable. This prevents a stale project
`.olean` from silently satisfying an omitted import.

- `private/audit_lake_module_closure.py` — recomputes the closure from tracked source
  bytes and fails on omissions, extras, missing local imports, or unsafe compression.
- `private/regenerate_lake_module_closure.py` — its inverse; rewrites the manifest from
  the same reachability. Run it after adding or removing a root, then re-run the auditor.

## Axiom footprint

The accepted foundation is exactly

```
[propext, Classical.choice, Quot.sound]
```

`lib/AxiomAudit.lean` prints the dependency cone of each top-level conditional theorem,
and the generated corpus prints its own per-leaf cones during the build. No file in this
project declares an axiom, and none uses `sorry`, `admit`, `native_decide`, or any
compiler-trust escape hatch.

## Provenance and reproducibility

The corpus is generated. Generators and auditors live in `private/` (Python) and
`tools/`; the receipts they emit — `private/*.json`, and the `.cnf`/`.lrat` pairs under
`KrennChart0Support/` and `KrennCollapseSupportCover/` — are proof authority, checked by
content hash. `private/audit_component_promotion.py` re-verifies a promoted component
against its receipts: it resolves each recorded artifact in the current checkout and
authenticates by SHA-256, treating recorded paths as provenance text rather than
authority.

Recorded paths are repository-relative. Two external inputs are named by environment
variable rather than by location: `KRENN_ARTIFACTS` (the artifact tree consumed by the
generators) and `MSOLVE` / `MSOLVE_LIB` (an external solver used by some generators).
Neither is required to build any Lean target.

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
