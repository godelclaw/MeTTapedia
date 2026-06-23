import Mettapedia.Computability.PNP.ExactZABWidthCollisionObstructionCore
import Mettapedia.Computability.PNP.ExactZABWidthCollisionObstructionExactRoutes
import Mettapedia.Computability.PNP.ExactZABWidthCollisionObstructionSharedRoutes

/-!
# P vs NP crux: width-compressing exact `z+a+b` extractors force visible collisions

The exact and shared exact `z+a+b` routes only see the visible summary
`(zfeat(z), a, b)`.  If the extractor compresses `BitVec n` into `BitVec r`
with `r < n`, then it is automatically noninjective, so every such route falls
into the visible-collision obstruction branch.

This closes the width-compressing extractor branch for the named exact ZAB ERM
surfaces, not only for the raw decision-list presentation.
-/
