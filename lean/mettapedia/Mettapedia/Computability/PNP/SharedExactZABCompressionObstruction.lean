import Mettapedia.Computability.PNP.SharedExactZABCompressionObstructionFeatureTargets
import Mettapedia.Computability.PNP.SharedExactZABCompressionObstructionFeatureRecovery
import Mettapedia.Computability.PNP.SharedExactZABCompressionObstructionFeatureERM
import Mettapedia.Computability.PNP.SharedExactZABCompressionObstructionDecisionList
import Mettapedia.Computability.PNP.SharedExactZABCompressionObstructionFinalERM

/-!
# P vs NP crux: shared-basis exact `(zfeat(z), a, b)` routes still face truth-table explosion

This file specializes the exact visible compression obstruction to the
shared-basis exact `z+a+b` route on `BitVec n`.

Even if the switched family is represented only through one fixed shared affine
basis on the extracted visible bits `(zfeat(z), a, b)`, surjectivity onto the
full exact rule class still has to pay for the full exact visible surface on
`BitVec n`.

So any shared-basis exact route with budget `p + 1` can only be surjective if
`p + 1` already reaches the truth-table threshold `2^(n + 2k)`.
-/
