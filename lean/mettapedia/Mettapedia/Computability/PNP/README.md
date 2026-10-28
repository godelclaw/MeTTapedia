# PNP

This directory contains the Lean side of the godelclaw P versus NP route audit.
It is not a proof of `P != NP`.

Ben's current v13 proof idea is an upper--lower clash in fixed-clock
polytime-capped conditional description length on a gauge-buffered locked SAT
ensemble. The lower side normalizes observer executions into CD evidence,
charges safe-buffer and hidden-gauge observations through an Atomic Evidence
Budget, combines this with boundary mixing, and seeks fixed-clock
incompressibility. Under `P = NP`, SAT self-reduction supplies the opposing
constant-description upper bound. V13 replaces v12's “short computation becomes
local” midpoint with this evidence-accounting architecture.

The files are organized mostly as small route surfaces, obstruction lemmas, and
regression checks. A rough reading pattern:

- `PNPv13CruxLedger.lean` - central v13 audit ledger and route obligations.
- `PNPv13RouteSynthesis.lean` - switching-route blocker surface.
- `PNPv13FaithfulM4Spec.lean` and `V13FaithfulQuantitativeFrontiers.lean` -
  source-faithful construction and quantitative statement layers.
- `V13FaithfulM4AdaptiveGaugeProduct.lean` - exact adaptive conditional
  hidden-gauge product law on the regioned scaffold.
- `V13FaithfulM4CouplingObstruction.lean` - D.31 / Definition 7.4 / D.48
  public-syntax coherence obstruction.
- `CruxSynthesis.lean` - broad synthesis ledger over the current packet of
  deterministic and finite-count obstructions.
- `BitVec.lean` - shared local finite Boolean vector surface used by multiple
  route obstructions.
- `*Obstruction.lean` - named route blockers.
- `*Regression.lean` - regression surfaces preserving previously identified
  blockers or reductions.
- `*Interface.lean`, `*Route.lean`, `*Family.lean` - reusable definitions and
  route surfaces.

Related non-Lean work:

- `megalodon/PNP_crux/`
- `megalodon/PNP_grassroots/`

Related papers:

- `lean/mettapedia/papers/pnp_crux.tex`
- `lean/mettapedia/papers/pnp_grassroots.tex`

Cross-problem proof-state scan:

- `lean/mettapedia/Mettapedia/Problems/PROOF_STATE.md`

Area-local proof-state and live build target:

- `lean/mettapedia/Mettapedia/Computability/PNP/PROOF_STATE.md`
- `lake -f lakefile.toml build Mettapedia.Computability.PNP.Live`

## Cluster Map

Source-count scan from 2026-06-21:

- Actual-switched local route and regressions: 97 files. This is the largest
  flat cluster and should be treated as the first candidate for a future
  import-boundary split, after the Lean 4.31 stream is settled.
- v13 ledger and crux synthesis: 58 files. These are the central route-audit
  ledgers and should stay easy to import from small regression surfaces.
- ZAB exact/canonical/BitVec surfaces: at least 35 files by strict prefix, with
  another large `SharedExactZAB` family visible in the filename-stem scan.
- AB exact/canonical/visible surfaces: 27 files by strict prefix, with
  `SharedAB` and `SharedExactAB` companion families.
- FiniteCoin route: 20 files.
- ClockedKpoly bridge/obstruction: 12 files.
- finite-family and affine recovery base: 13 files.
- Other named obstructions, interfaces, ledgers, support files, and regressions:
  the remaining files.

This map is an organizational index only. It is not evidence that any P versus
NP theorem target has been proved.

## Current Status

The Lean files mostly encode audit discipline: which repair classes are blocked,
which hypotheses are still needed, and which examples prevent a route from
being stop-grade. The formal surface is useful because it names exact
obligations, but it does not close the P versus NP problem.

The latest faithful-route verdict is now stronger than a list of open analytic
inputs. The adaptive gauge-product law, positive-rank free action, and
quotient-conditioned uniform gauge lift are proved on the scaffold. But the
complete nonempty M4 construction target is machine-checked uninhabited:

- D.48 supplies an opposite-phase coupling with supported endpoint pairs;
- D.31 and Definition 7.4/Hypothesis 7.5 force every complete neutral public
  syntax valuation to agree on those pairs;
- full public observability then makes the public instances equal;
- D.8 makes the designated message coordinate equal;
- the opposite phases require that coordinate to differ.

This contradiction is independent of max-qSSM, bounded incidence, the Atomic
Evidence Budget estimate, boundary mixing, and Kpoly hardness. No replacement
lock family can inhabit the complete interface without revising at least one
manuscript role. The current mathematical task is route revision, not another
carrier or endpoint wrapper.

Before reorganizing files, keep the existing flat layout stable unless a
cluster has a clear import boundary. Better first steps are:

1. split regression-only imports from route-surface imports;
2. decide whether ActualSwitchedLocal and v13 deserve separate import
   aggregators;
3. keep every move paired with a build log.
