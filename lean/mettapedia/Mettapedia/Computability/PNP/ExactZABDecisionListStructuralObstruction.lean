import Mettapedia.Computability.PNP.ExactZABDecisionListStructuralObstructionCore
import Mettapedia.Computability.PNP.ExactZABDecisionListStructuralObstructionActualInterface

/-!
# PNP crux: the raw exact `(zfeat(z), a, b)` decision-list route is structurally
  too weak

The previous exact-ZAB packets lower-bounded the route by cardinality.  This
file records a stronger obstruction for the raw exact decision-list branch
itself.

For positive latent width `n > 0` and positive visible width `k > 0`, every
predictor in the raw exact `(zfeat(z), a, b)` family falls into one of two bad
cases:

* some `z0` activates a `zfeat` bit early, so the predictor is constant across
  the whole `(a,b)` fiber above `z0`;
* or every `zfeat z` is zero, so the predictor ignores `z` entirely.

Either way, the route cannot realize a surjective exact family, hence cannot
support the manuscript's full-rule actual-local interface.
Compatibility umbrella for the raw route obstruction and actual-local wrapper.
-/
