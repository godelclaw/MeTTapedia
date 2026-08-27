# Godelclaw-Unique Problem Proof State

This file records source-level proof-state evidence for the godelclaw-unique
problem formalizations. It is an organization aid, not a claim that any
headline open problem is solved.

Last checked: 2026-07-14. Cross-branch status is recorded where the latest
proof-state work has not yet merged to `main`; file counts are intentionally
omitted there because they change rapidly. The latest Navier-Stokes repair,
PNP faithful-interface verdict, and Yang-Mills extraction/recombination verdict
must be merged with their corresponding Lean modules.

## Scan Method

The counts below are source scans over the local worktree. They do not replace
real Lean/Lake build gates.

Lean code-level placeholder scan:

```bash
rg -g '*.lean' -n '^\s*axiom\b|\bby\s+(sorry|admit)\b|:=\s*(by\s*)?(sorry|admit)\b|^\s*opaque\b' <dir>
```

Lean English-token scan:

```bash
rg -g '*.lean' --count-matches '\b(sorry|admit|axiom)\b' <dir>
```

Megalodon gap-marker scan:

```bash
rg --count-matches -i '\b(admit|axiom|sorry)\b' megalodon/PNP_crux megalodon/PNP_grassroots
```

## Summary

| Area | Local source | File count | Code-level Lean placeholders | Other gap markers | Status |
|------|--------------|-----------:|-----------------------------:|------------------:|--------|
| Four Color | `lean/mettapedia/Mettapedia/GraphTheory/FourColor/` | see FourColor index | actively classified | actively classified | Canonical modern route; old `lean/fourcolor` is being mined theorem-by-theorem. |
| P versus NP, Lean | `lean/mettapedia/Mettapedia/Computability/PNP/` | branch-dependent | 0 found in the latest faithful-route audit | prose-only hits in comments/docstrings | Adaptive gauge law proved; complete faithful M4 interface uninhabited; route revision required, not a proof of `P != NP`. |
| P versus NP, Megalodon | `megalodon/PNP_crux/`, `megalodon/PNP_grassroots/` | 92 files | n/a | 36 files / 221 `admit`/`axiom`/`sorry` tokens | Direct crux attempts remain assumption-heavy. |
| Navier-Stokes | `lean/mettapedia/Mettapedia/FluidDynamics/NavierStokes/` | branch-dependent | 0 found in the July repair audit | prose-only hits in comments/docstrings | H1 obstruction checked; repaired stochastic-Lagrangian route checked conditionally; one named pancake strain-budget pin remains. |
| Yang-Mills | `lean/mettapedia/Mettapedia/QuantumTheory/YangMills/` | branch-dependent | 0 found in the latest steelman audit | prose-only `axiom` mentions in regression comments | Natural Wilson extraction proved norm one; transfer from v14's range-only projection refuted; actual recursion constant and continuum endpoint open. |

The `True`-surface scan found no matches in the PNP, Navier-Stokes, or
Yang-Mills Lean directories for:

```bash
rg -g '*.lean' -n '(:\s*Prop\s*:=\s*True|:\s*True\b|:=\s*True\b)' <dir>
```

## P Versus NP

Lean entry point:

- `Mettapedia.Computability.PNP.CruxSynthesis`

Important route surfaces:

- `PNPv13CruxLedger.lean`
- `PNPv13RouteSynthesis.lean`
- `CruxSynthesis.lean`

Current reading:

- Ben's v13 proof idea is an upper--lower clash in polytime-capped conditional
  description length on a gauge-buffered locked SAT ensemble. The lower side
  uses CD evidence normalization, an Atomic Evidence Budget, boundary mixing,
  and fixed-clock incompressibility; the upper side uses SAT self-reduction
  under `P = NP`.
- The adaptive hidden-gauge product law is proved exactly on the faithful
  regioned scaffold, together with its positive-rank free action and
  quotient-conditioned uniform lift.
- The later source reconciliation proves a stronger negative verdict:
  `v13M4OpenConstructionObligations_uninhabited`. D.8 message rigidity, D.31
  neutrality of complete public syntax, D.48 opposite-phase coupling,
  Definition 7.4/Hypothesis 7.5 support-wide pair neutrality, full public
  observability, and nonempty switched targets cannot coexist.
- This is independent of max-qSSM, bounded incidence, the Atomic Evidence
  Budget estimate, boundary mixing, and Kpoly hardness. Replacing the lock
  family cannot fix the contradiction without revising at least one manuscript
  role. No P-versus-NP separation is claimed.

Cluster map from the 2026-06-21 source-count scan:

| Cluster | Files | Reading |
|---------|------:|---------|
| ActualSwitchedLocal route and regressions | 97 | Largest current flat family; candidate for a future import-boundary split. |
| v13 ledger and crux synthesis | 58 | Central route ledger and synthesis surfaces. |
| ZAB exact/canonical/BitVec surfaces | 35+ | Strict-prefix count is 35; filename stems also show a large `SharedExactZAB` companion family. |
| AB exact/canonical/visible surfaces | 27+ | Strict-prefix count is 27; `SharedAB` and `SharedExactAB` companions are present. |
| FiniteCoin route | 20 | Finite-coin route surfaces and regressions. |
| ClockedKpoly bridge/obstruction | 12 | Clocked-K-poly bridge and obstruction checks. |
| finite-family/affine recovery base | 13 | Small reusable family and affine recovery base. |
| Other support, ledgers, interfaces, obstructions, and regressions | 140 | Remaining route-audit surface. |

Megalodon status:

- `megalodon/PNP_crux/`: 29 files with 122 gap-marker tokens.
- `megalodon/PNP_grassroots/`: 7 files with 99 gap-marker tokens.
- Sample direct markers include `admit.` in
  `megalodon/PNP_grassroots/13_main_theorem.mg` and `Axiom ...` declarations in
  `megalodon/PNP_crux/verified/uniqueness_sparsification_axioms.mg`.

## Navier-Stokes

Lean entry points:

- `NavierStokesEquationTarget.lean`
- `FeffermanGrassrootsInterface.lean`
- `NavierStokesWitnessConstruction.lean`
- `NavierStokesBKMContinuationTarget.lean`
- `NavierStokesUniformVorticityContinuationTarget.lean`

Current reading:

- The original SG--Cole--Hopf H1 hypothesis is refuted in the normalized
  Fourier-mode shear model by `BenH1Break.lean`.
- The July repair lane replaces the false adjoint bound with a
  stochastic-Lagrangian/cotangent transport skeleton and a vorticity-stretching
  gate. The conditional pushdown-to-BKM route, dyadic absorption algebra,
  frozen-strain obstruction, and plane-wave pancake null-structure canary are
  checked.
- The latest claimed pancake closure is not a complete proof. The aperture
  dichotomy covers all scales only under the pointwise condition
  `gamma <= nu * lambda_q`; this is exactly the self-consistent strain budget
  still to be proved.
- The active named pin is `ScaleLocalPancakeStrainBudget`, cross-referenced
  with the coarser `StochasticStretchingEstimate`. The Millennium global
  regularity endpoint remains open.

Cluster map from the 2026-06-21 source-count scan:

| Cluster | Files | Reading |
|---------|------:|---------|
| Cole-Hopf/Fefferman window package | 86 | Largest route package; includes `WindowedColeHopfHeat*`, `ColeHopf*`, and `Fefferman*`. |
| finite-mode classifications/obstructions | 40 | Finite-mode exact, BKM, uniform, pressure, and velocity-route checks. |
| Schwartz/shear/pressure obstruction family | 28 | Schwartz, heat/linear shear, pressure, transported, and streamwise obstruction surfaces. |
| witness construction/shared-witness route | 16 | Witness-construction interfaces and route blockers. |
| target/core analytic infrastructure | 9 | Equation target, vector calculus, Schwartz data, and energy inequality surfaces. |
| BKM/continuation targets and bridges | 8 | BKM and uniform-vorticity continuation target surfaces. |
| topology countermodels | 2 | Weak/product topology countermodels. |
| Other support/frontier/regression files | 33 | Remaining frontiers, shared packages, and regressions. |

## Yang-Mills

Lean entry points:

- `MassGap.lean`
- `RGCrux.lean`
- `RGBootstrap.lean`
- `ExtractionProjection.lean`
- `ExtractionStateRGCrux.lean`

Related papers:

- `papers/benxiv/goertzel_ym.tex`
- `papers/benxiv/goertzel_ym.pdf`
- `papers/ym_grassroots.tex`
- `papers/ym_grassroots.pdf`

Current reading:

- Ben's v14 route starts with finite Wilson lattice gauge theory, proposes a
  dimension-16 extended-extraction RG bootstrap, invokes a stopping-scale KP
  polymer expansion for clustering, transports clustering to fine scales, and
  uses OS reconstruction to obtain the continuum Hamiltonian and spectral gap.
- The latest steelman branch has no code-level `sorry`. `ProofState.lean`,
  `Roadmap.lean`, and `CompletionSteelman.lean` carry the current status.
- `WilsonBlockMajorant.lean` constructs actual finite Wilson observables and
  proves gauge-invariant coefficient-majorant truncation has constant one.
  `ExtendedExtractionTransfer.lean` refutes any bound derived from projection
  range alone and proves the valid explicit-matrix transfer theorem.
- `WilsonPolymerRecombination.lean` proves union regrouping has constant one,
  refutes a total-contact reading of `14`, and proves its local rooted-branching
  interpretation. `WilsonExtractionRecombinationConstant.lean` checks that
  F.5 gives `33152` while Appendix O gives `11088/5` at block factor two and
  exposes the missing quantitative fluctuation and cumulant estimates.
- Therefore v14's actual Wilson recursion constant is not derived. The exact
  next extraction input is the dimension-16 invariant action basis and dual
  jets with uniform conditioning; the next recombination input is the weighted
  Wilson cumulant/tree/KP estimate in the same norm.
- The conditional OS endpoint and finite `Z2`, `Z3`, and `Q8` landmarks remain
  checked, but the actual recursion, support branch, two-marked glue,
  Wilson-family RP/KP instantiation, continuum measure, and OS construction
  remain open.

Historical cluster map from the 2026-07-03 source-count scan (superseded by the
larger steelman branch, retained only for provenance):

| Cluster | Files | Reading |
|---------|------:|---------|
| live/source modules | 32 | Current Yang-Mills route surfaces imported by `Mettapedia.QuantumTheory.YangMills`. |
| regression companions | 27 | Focused regression modules imported by `Mettapedia.QuantumTheory.YangMills.Regression`. |
| proof-state and roadmap | 2 | `ProofState.lean` and `Roadmap.lean` keep the public verdict and route order explicit. |
| finite strong-coupling canaries | 6+ | `Z2`, `Z3`, `Q8`, and transfer-clustering canaries; finite landmarks only. |
| constructive gate surfaces | 7+ | Continuum measure, covariance, reflection positivity, OS, and Hamiltonian-transfer gate checks. |

## Next Organization Steps

1. Keep the current topical homes for PNP, Navier-Stokes, and Yang-Mills until
   the Lean 4.31/zariuq stream is settled.
2. After the Lean 4.31/zariuq stream is settled, use these cluster maps to
   decide whether any cluster deserves a real import aggregator or directory
   split. Do not move files just to make the tree look tidy.
3. Treat every route theorem as an audit surface unless a real Lean/Lake build
   and theorem-level review establish otherwise.
4. For Navier-Stokes publication, merge the repair modules and the updated paper
   together; the paper now cites the July repair/pancake-closure modules.
