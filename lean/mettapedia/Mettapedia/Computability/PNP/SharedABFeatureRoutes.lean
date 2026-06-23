import Mettapedia.Computability.PNP.SharedABFeatureRoutesExactPullback

/-!
# P vs NP grassroots: quotient routes for shared raw `(a, b)` feature families

This compatibility module preserves the original import surface for routes from
the reduced raw visible surface `(a, b)` to shared-basis exact-surface families.
The declarations live in semantic modules:

* `SharedABFeatureRoutesPredictors`
* `SharedABFeatureRoutesFamilies`
* `SharedABFeatureRoutesExactPullback`

If a switched family factors through the reduced surface and the reduced family
is realized using one shared affine basis on the raw `(a, b)` bits, then the
exact-surface family inherits the corresponding combiner-only budget.
-/
