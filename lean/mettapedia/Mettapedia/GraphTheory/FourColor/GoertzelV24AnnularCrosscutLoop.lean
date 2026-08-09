import Mettapedia.GraphTheory.FourColor.GoertzelV24OrientedAnnularCrosscut

/-!
# The dual loop between two annular transversals

The source splice is performed between two simple, nonintersecting annular
transversals.  Traversing one from the inner hole to the outer hole and the
other in reverse produces a literal closed walk in the facial dual.  This file
records the source's nonintersection condition at the walk level and derives
the closed dual cycle; it does not replace the open transversals by a primal
chord or a caller-supplied vertex side.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24AnnularCrosscut

open GoertzelV24FaceOrbitIncidence

variable {F E : Type*} [Fintype F] [DecidableEq F]
  [Fintype E] [DecidableEq E]

noncomputable section

/-- Two aligned source transversals which are simple as a pair: apart from
their common endpoint faces, they have no common dual facial cell.  The
nondegeneracy clause is exactly what makes their closed composite a genuine
cycle rather than a doubled single dual edge. -/
structure SeparatedAlignedSimpleDualCrosscuts
    (faceBoundary : F → Finset E) (allFaces : Finset F)
    (start finish : AmbientFace allFaces)
    (hunique : PairwiseUniqueSharedInteriorEdges faceBoundary allFaces)
    extends AlignedSimpleDualCrosscuts faceBoundary allFaces start finish hunique where
  transverse_disjoint :
    left.walk.support.tail.Disjoint right.walk.reverse.support.tail
  nondegenerate : 1 < left.walk.length ∨ 1 < right.walk.length

namespace SeparatedAlignedSimpleDualCrosscuts

/-- Follow the left source transversal outward and return along the right
source transversal.  This is the actual facial-dual loop enclosing the
corridor region between them. -/
def dualLoop
    {faceBoundary : F → Finset E} {allFaces : Finset F}
    {start finish : AmbientFace allFaces}
    {hunique : PairwiseUniqueSharedInteriorEdges faceBoundary allFaces}
    (pair : SeparatedAlignedSimpleDualCrosscuts faceBoundary allFaces
      start finish hunique) :
    (interiorDualGraph faceBoundary allFaces).Walk start start :=
  pair.left.walk.append pair.right.walk.reverse

/-- The source's simple-transversal condition makes the concrete composite a
simple closed facial-dual cycle.  This is the bridge from two open interfaces
to the separator construction; no primal Jordan theorem is assumed here. -/
theorem dualLoop_isCycle
    {faceBoundary : F → Finset E} {allFaces : Finset F}
    {start finish : AmbientFace allFaces}
    {hunique : PairwiseUniqueSharedInteriorEdges faceBoundary allFaces}
    (pair : SeparatedAlignedSimpleDualCrosscuts faceBoundary allFaces
      start finish hunique) :
    pair.dualLoop.IsCycle := by
  exact SimpleGraph.Walk.IsPath.isCycle_append pair.left.isPath
    pair.right.isPath.reverse pair.transverse_disjoint (by
      simpa using pair.nondegenerate)

/-- The loop's length is the sum of the two source-interface widths. -/
theorem dualLoop_length
    {faceBoundary : F → Finset E} {allFaces : Finset F}
    {start finish : AmbientFace allFaces}
    {hunique : PairwiseUniqueSharedInteriorEdges faceBoundary allFaces}
    (pair : SeparatedAlignedSimpleDualCrosscuts faceBoundary allFaces
      start finish hunique) :
    pair.dualLoop.length = pair.left.walk.length + pair.right.walk.length := by
  simp [dualLoop]

end SeparatedAlignedSimpleDualCrosscuts

end

end GoertzelV24AnnularCrosscut

end Mettapedia.GraphTheory.FourColor
