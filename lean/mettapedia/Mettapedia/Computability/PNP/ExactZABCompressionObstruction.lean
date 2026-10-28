import Mettapedia.Computability.PNP.ExactZABCompressionObstructionAffineFeature
import Mettapedia.Computability.PNP.ExactZABCompressionObstructionSparseThreshold
import Mettapedia.Computability.PNP.ExactZABCompressionObstructionDecisionList
import Mettapedia.Computability.PNP.ExactZABCompressionObstructionFinalERM

/-!
# P vs NP crux: exact `(zfeat(z), a, b)` routes still face truth-table explosion

This file specializes the exact visible compression obstruction to the
non-shared exact `(zfeat(z), a, b)` routes on `BitVec n`.

Even after passing to exact visible data and allowing non-shared affine codes,
any surjective route still has to pay for the full exact visible surface on
`BitVec n`.
-/
