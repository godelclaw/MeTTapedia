import Mettapedia.Computability.PNP.SharedExactZABAffineDecisionListStructuralObstructionRawBitVec
import Mettapedia.Computability.PNP.SharedExactZABAffineDecisionListStructuralObstructionExactZAB

/-!
# P vs NP crux: shared affine decision-list signatures are structurally
  noninjective on visible width above one

The shared exact affine decision-list branch was reduced earlier to one precise
condition: its first-active signature on the exact visible surface must be
injective.

This file proves a strong structural obstruction on the raw `BitVec` surface.
For any family of affine GF(2)-style probes on `BitVec d`, once `d > 1` the
first-active signature

`x ↦ firstActiveFeature? (affineFeatureVector features x)`

is never injective.  The reason is simple:

* if every affine probe is empty, the signature is constantly `none`;
* otherwise the earliest nonempty probe has a truth set of size at least `2`,
  because an affine parity test on more than one bit can never be true at
  exactly one point.

Pushed back through the exact visible-data bijection for identity extractors,
this closes the identity-extractor shared affine decision-list branch on every
bit-valued exact ZAB surface with visible width `n + 2k > 1`, independently of
the combiner width `p`.
Compatibility umbrella for the raw and exact-ZAB semantic layers.
-/
