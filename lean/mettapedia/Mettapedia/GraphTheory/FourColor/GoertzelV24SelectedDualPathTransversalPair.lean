import Mettapedia.GraphTheory.FourColor.GoertzelV24AnnularCrosscutLoop
import Mettapedia.GraphTheory.FourColor.GoertzelV24SelectedDualPathTransversal

/-!
# A separated pair of selected facial-dual transversals

The literal source annulus does not satisfy the global condition that every
pair of ambient faces share at most one interior primal edge.  A source
transversal instead selects the actual primal edge crossed at each dual step.
This file packages two such selected transversals with the alignment and
separation data used by the splice.

The resulting dual loop depends only on the two simple facial-dual paths, so
its cycle proof requires no global unique-shared-edge premise.  This is the
target carrier for the source's eventual long, end-capped construction; the
file does not construct those transversals.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24SelectedDualPathTransversal

open GoertzelV24AnnularCrosscut
open GoertzelV24FaceDualConnectedness

variable {F E : Type*} [Fintype F] [DecidableEq F]
  [Fintype E] [DecidableEq E]

noncomputable section

/-- Two equal-width selected transversals which meet only at their common
endpoint faces.  Unlike the older paired-crosscut carrier, this structure
records the actual crossed primal edges and assumes no global uniqueness of
shared face-boundary edges. -/
structure SeparatedAlignedSelectedDualTransversals
    (faceBoundary : F → Finset E) (allFaces : Finset F)
    (start finish : AmbientFace allFaces) where
  left : SelectedDualPathTransversal faceBoundary allFaces start finish
  right : SelectedDualPathTransversal faceBoundary allFaces start finish
  length_eq : left.crosscut.walk.length = right.crosscut.walk.length
  crossing_disjoint : Disjoint left.crossingEdges right.crossingEdges
  transverse_disjoint :
    left.crosscut.walk.support.tail.Disjoint
      right.crosscut.walk.reverse.support.tail
  nondegenerate :
    1 < left.crosscut.walk.length ∨ 1 < right.crosscut.walk.length

namespace SeparatedAlignedSelectedDualTransversals

/-- All literally selected primal edges opened by the two transversals. -/
def crossingSupport
    {faceBoundary : F → Finset E} {allFaces : Finset F}
    {start finish : AmbientFace allFaces}
    (pair : SeparatedAlignedSelectedDualTransversals
      faceBoundary allFaces start finish) : Finset E :=
  pair.left.crossingEdges ∪ pair.right.crossingEdges

/-- Following the left transversal and returning along the right produces the
literal facial-dual loop enclosing the selected strip. -/
def dualLoop
    {faceBoundary : F → Finset E} {allFaces : Finset F}
    {start finish : AmbientFace allFaces}
    (pair : SeparatedAlignedSelectedDualTransversals
      faceBoundary allFaces start finish) :
    (interiorDualGraph faceBoundary allFaces).Walk start start :=
  pair.left.crosscut.walk.append pair.right.crosscut.walk.reverse

/-- Path simplicity and pairwise transverse separation make the selected
composite a genuine dual cycle. -/
theorem dualLoop_isCycle
    {faceBoundary : F → Finset E} {allFaces : Finset F}
    {start finish : AmbientFace allFaces}
    (pair : SeparatedAlignedSelectedDualTransversals
      faceBoundary allFaces start finish) :
    pair.dualLoop.IsCycle := by
  exact SimpleGraph.Walk.IsPath.isCycle_append
    pair.left.crosscut.isPath pair.right.crosscut.isPath.reverse
    pair.transverse_disjoint (by simpa using pair.nondegenerate)

/-- The selected loop length is the sum of its two transversal widths. -/
theorem dualLoop_length
    {faceBoundary : F → Finset E} {allFaces : Finset F}
    {start finish : AmbientFace allFaces}
    (pair : SeparatedAlignedSelectedDualTransversals
      faceBoundary allFaces start finish) :
    pair.dualLoop.length =
      pair.left.crosscut.walk.length + pair.right.crosscut.walk.length := by
  simp [dualLoop]

/-- The selected crossing carrier has exactly the sum of the two widths. -/
theorem card_crossingSupport
    {faceBoundary : F → Finset E} {allFaces : Finset F}
    (hall : ∀ edge, totalIncidenceCount faceBoundary allFaces edge ≤ 2)
    {start finish : AmbientFace allFaces}
    (pair : SeparatedAlignedSelectedDualTransversals
      faceBoundary allFaces start finish) :
    pair.crossingSupport.card =
      pair.left.crosscut.walk.length + pair.right.crosscut.walk.length := by
  rw [crossingSupport, Finset.card_union_of_disjoint pair.crossing_disjoint,
    pair.left.card_crossingEdges_eq_length hall,
    pair.right.card_crossingEdges_eq_length hall]

/-- With aligned widths, the selected simultaneous cut has twice the left
transversal's number of crossed edges. -/
theorem card_crossingSupport_eq_twice_left_length
    {faceBoundary : F → Finset E} {allFaces : Finset F}
    (hall : ∀ edge, totalIncidenceCount faceBoundary allFaces edge ≤ 2)
    {start finish : AmbientFace allFaces}
    (pair : SeparatedAlignedSelectedDualTransversals
      faceBoundary allFaces start finish) :
    pair.crossingSupport.card = 2 * pair.left.crosscut.walk.length := by
  rw [pair.card_crossingSupport hall, pair.length_eq]
  omega

/-- The older globally unique presentation embeds into the selected one.  The
adapter is one-way: selected source geometry does not manufacture global
face-intersection uniqueness. -/
def ofPairwiseUnique
    {faceBoundary : F → Finset E} {allFaces : Finset F}
    {start finish : AmbientFace allFaces}
    (hunique : PairwiseUniqueSharedInteriorEdges faceBoundary allFaces)
    (pair : SeparatedAlignedSimpleDualCrosscuts
      faceBoundary allFaces start finish hunique) :
    SeparatedAlignedSelectedDualTransversals
      faceBoundary allFaces start finish where
  left := SelectedDualPathTransversal.ofPairwiseUnique pair.left hunique
  right := SelectedDualPathTransversal.ofPairwiseUnique pair.right hunique
  length_eq := pair.length_eq
  crossing_disjoint := by
    change Disjoint (pair.left.crossingEdges hunique)
      (pair.right.crossingEdges hunique)
    exact pair.crossing_disjoint
  transverse_disjoint := pair.transverse_disjoint
  nondegenerate := pair.nondegenerate

end SeparatedAlignedSelectedDualTransversals

end

end GoertzelV24SelectedDualPathTransversal

end Mettapedia.GraphTheory.FourColor
