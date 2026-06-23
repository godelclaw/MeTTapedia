import Mettapedia.GraphTheory.FourColor.FrontierPositive
import Mettapedia.GraphTheory.FourColor.FrontierRefutations

/-!
# The current Theorem 4.9 frontier

This file states, over the bundled shells of
`Mettapedia.GraphTheory.FourColor.Shells`, the *maximal* results of the route
audit — the strongest hypothesis packages known not to force the missing
geometry, and the weakest geometric inputs known to force the full
Theorem 4.9 synthesis endpoint.  Everything is a thin wrapper around theorems
proved elsewhere (live route files and the `Legacy` ledger); no new
mathematics happens here.

## The picture

Positive (sufficiency, live route files):
* a `ClosedWalkExactShell` together with repaired previous-boundary witness
  geometry, OR explicit well-founded peel-witness data, OR generic
  interior-dual boundary-root distance-peel data, OR the non-geometric
  projected-generator detector certificate, OR a direct explicit-family
  pairing-kernel certificate, reaches full `Theorem49BoundaryRootSynthesis`.

Negative (maximal refuted shells, `Legacy` benchmarks):
* the wheel-with-inner-triangle inhabits both exact shells while refuting
  generic `InteriorDualBoundaryRootAdjDistancePeelData`;
* the shared-interior-pair inhabits the closed-walk exact shell while
  refuting all four replacement-positive geometry packages;
* every closed-walk shell with an unblocked endpoint must put two distinct
  interior edges on some face boundary, which forbids the facewise
  at-most-one, canonical-choice, and source-preserving one-collar repairs.

So the single open question is exactly the gap between the shells and the
geometric inputs.  More precisely, `Theorem49DetectorStrength.lean` now proves
that on every shell-bearing embedding the full selected-boundary-zero space is
already strictly larger than the theorem-4.9 target `W₀(H)`, so the new
detector/cancellation oracle really is stronger than the manuscript target,
not a mere restatement.  See `ROADMAP.md`.
-/
