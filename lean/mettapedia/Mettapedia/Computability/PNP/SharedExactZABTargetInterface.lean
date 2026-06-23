import Mettapedia.Computability.PNP.SharedExactZABTargetInterfaceData
import Mettapedia.Computability.PNP.SharedExactZABTargetInterfaceAffineFeature
import Mettapedia.Computability.PNP.SharedExactZABTargetInterfaceSparseThreshold
import Mettapedia.Computability.PNP.SharedExactZABTargetInterfaceDecisionList
import Mettapedia.Computability.PNP.SharedExactZABTargetInterfaceDecisionListRecovery

/-!
# P vs NP grassroots: target interfaces for the shared-basis `(zfeat(z), a, b)` route

This file packages the shared-basis route on the full manuscript-facing local
bits `(zfeat(z), a, b)`.

Once one fixed shared extractor and one fixed affine basis are supplied, the
remaining burden is just the choice of downstream combiner family.
Compatibility umbrella for the route-specific semantic layers.
-/
