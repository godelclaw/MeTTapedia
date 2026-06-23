import Mettapedia.Computability.PNP.SharedABFeatureObstructionFullExactPullback

/-!
# PNP crux: shared raw `(a,b)` feature routes need a strict subclass theorem

This compatibility module preserves the original import surface for shared
raw `(a,b)` feature obstructions.  The declarations live in semantic modules:

* `SharedABFeatureObstructionReducedFullRules`
* `SharedABFeatureObstructionReducedFiniteProbe`
* `SharedABFeatureObstructionExactPullback`
* `SharedABFeatureObstructionFullExactPullback`

If an exact switched family factors through `(a,b)` and the reduced family is
still fully expressive on `ABVisibleSurface k`, then any shared-basis
realization of the exact family forces the reduced truth-table lower bound.  So
the shared-basis route must prove that the actual reduced switched family is a
strict subclass of all Boolean rules on `(a,b)`.
-/
