import Mettapedia.Computability.PNP.SharedExactZABRecoveryInterfaceData
import Mettapedia.Computability.PNP.SharedExactZABRecoveryInterfaceAffineFeature
import Mettapedia.Computability.PNP.SharedExactZABRecoveryInterfaceSparseThreshold

/-!
# P vs NP grassroots: recovery interfaces for the shared-basis exact `(zfeat(z), a, b)` route

This file packages the remaining generic ingredients for the shared-basis exact
`z+a+b` affine-feature and sparse-threshold routes:

* one shared extractor `zfeat`,
* one shared affine basis on the visible bits `(zfeat(z), a, b)`,
* one corresponding realization of the switched family through that basis, and
* one bad-code agreement bound.

Once those data are supplied, both the exact visible compression target and the
weighted exact-recovery lower bound follow automatically.
Compatibility umbrella for the recovery-data and route-specific consequence
layers.
-/
