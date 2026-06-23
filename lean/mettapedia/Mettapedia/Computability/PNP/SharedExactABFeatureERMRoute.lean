import Mettapedia.Computability.PNP.SharedExactABFeatureERMRouteRecovery

/-!
# P vs NP grassroots: ERM over shared-basis raw exact `(a, b)` feature classes

This compatibility module preserves the original import surface for ERM over
shared-basis exact raw `(a,b)` affine-feature and sparse-threshold classes.
The declarations live in semantic modules:

* `SharedExactABFeatureERMRouteCore`
* `SharedExactABFeatureERMRouteTarget`
* `SharedExactABFeatureERMRouteRecovery`

If the wrapper is honestly choosing from one fixed shared affine basis on the
raw exact `(a, b)` bits and one fixed downstream combiner class, then the
selected ERM code is again the route witness.
-/
