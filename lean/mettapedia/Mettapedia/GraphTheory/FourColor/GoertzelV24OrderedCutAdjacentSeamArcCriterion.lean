import Mettapedia.GraphTheory.FourColor.GoertzelV24ActualSeamReturnOrientation
import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebSpliceSeamArcNoncollision

/-!
# Adjacent-strip criterion for literal seam arcs

Addendum XXVII attributes splice noncrossing to simple ordered transversals and
the homeomorphic gluing of their complementary pieces.  The actual return-map
calculation shows that a completed seam face contains either one ordered root
or two opposite-side roots at adjacent offsets.  This module turns that fact
into an exact interface theorem.

Under either source orientation, full pairwise edge-disjointness of canonical
seam arcs is equivalent to checking only actual adjacent opposite-side pairs.
This is a reduction of the remaining physical Lean-flag L1 obligation, not its
discharge: the source corridor must still construct the crosscuts and prove the
neighboring geometric arcs disjoint.
-/

namespace Mettapedia.GraphTheory.FourColor

open GoertzelV24ActualSeamReturnOrientation
open GoertzelV24OrderedCutFaceReturnProfile
open GoertzelV24OrderedCutRotationSplice
open GoertzelV24RotationCutDartDecomposition
open GoertzelV24RotationSpliceConstructor

variable {V E : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E]

noncomputable section

namespace GoertzelV24SpliceUnification.OrderedCutSpliceData

variable {RS : RotationSystem V E}
  {n terminalCount faceFragmentCount : Nat}

/-- The actual marked seam dart at one ordered seam position. -/
def orderedSeamMarkedRoot
    (data : OrderedCutSpliceData RS n terminalCount faceFragmentCount)
    (position : OrderedSeamPosition n) : data.SeamMarkedDart :=
  ⟨orderedSeamRoot RS data.keep
      data.left.crossingEdge data.right.crossingEdge
      data.leftCrosses data.rightCrosses data.leftInjective
      data.rightInjective position,
    orderedSeamRoot_isSeam RS data.keep
      data.left.crossingEdge data.right.crossingEdge
      data.leftCrosses data.rightCrosses data.leftInjective
      data.rightInjective position⟩

/-- The actual first-return permutation on the fixed ordered seam carrier. -/
def actualSeamReturn
    (data : OrderedCutSpliceData RS n terminalCount faceFragmentCount) :
    Equiv.Perm (OrderedSeamPosition n) :=
  actualOrderedCutFaceReturnSuccessor RS data.keep
    data.left.crossingEdge data.right.crossingEdge
    data.leftCrosses data.rightCrosses data.leftInjective
    data.rightInjective data.cover data.disjoint data.outer_kept

@[simp] theorem seamPositionOf_orderedSeamMarkedRoot
    (data : OrderedCutSpliceData RS n terminalCount faceFragmentCount)
    (position : OrderedSeamPosition n) :
    data.seamPositionOf (data.orderedSeamMarkedRoot position) = position := by
  exact (orderedSeamPositionEquiv RS data.keep
    data.left.crossingEdge data.right.crossingEdge
    data.leftCrosses data.rightCrosses data.leftInjective
    data.rightInjective).symm_apply_apply position

@[simp] theorem orderedSeamMarkedRoot_seamPositionOf
    (data : OrderedCutSpliceData RS n terminalCount faceFragmentCount)
    (root : data.SeamMarkedDart) :
    data.orderedSeamMarkedRoot (data.seamPositionOf root) = root := by
  apply Subtype.ext
  exact data.orderedSeamRoot_seamPositionOf root

/-- The remaining bounded source-geometric receipt: whenever an actual seam
face joins a left root to a right root at adjacent offsets, their two canonical
arcs have disjoint edge supports. -/
def AdjacentOppositeSeamArcsEdgeDisjoint
    (data : OrderedCutSpliceData RS n terminalCount faceFragmentCount) : Prop :=
  ∀ (left right : Fin n),
    data.output.phi.SameCycle
      (data.orderedSeamMarkedRoot (Sum.inl left)).1
      (data.orderedSeamMarkedRoot (Sum.inr right)).1 →
    (left.val = right.val + 1 ∨ right.val = left.val + 1) →
    Disjoint
      (data.seamArcEdges
        (data.orderedSeamMarkedRoot (Sum.inl left)))
      (data.seamArcEdges
        (data.orderedSeamMarkedRoot (Sum.inr right)))

/-- Under the computed return classification, the full pairwise seam-arc
receipt is exactly the neighboring opposite-strip receipt. -/
theorem seamArcsPairwiseEdgeDisjoint_iff_adjacentOpposite
    (data : OrderedCutSpliceData RS n terminalCount faceFragmentCount)
    (hactual :
      data.actualSeamReturn =
          GoertzelV24DeletedRegionBoundaryOrder.oppositeBoundaryCycle n *
            GoertzelV24DeletedRegionBoundaryOrder.orderedPositionSeamSwap n ∨
      data.actualSeamReturn =
          (GoertzelV24DeletedRegionBoundaryOrder.oppositeBoundaryCycle n)⁻¹ *
            GoertzelV24DeletedRegionBoundaryOrder.orderedPositionSeamSwap n) :
    data.SeamArcsPairwiseEdgeDisjoint ↔
      data.AdjacentOppositeSeamArcsEdgeDisjoint := by
  constructor
  · intro hpairwise left right hcycle hadjacent
    apply hpairwise
    · exact hcycle
    · intro heq
      have hposition := congrArg data.seamPositionOf heq
      simp at hposition
  · intro hadjacent first second hcycle hne
    let firstPosition := data.seamPositionOf first
    let secondPosition := data.seamPositionOf second
    have hraw :
        (orderedCutSplicePhi RS data.keep
          data.left.crossingEdge data.right.crossingEdge
          data.leftCrosses data.rightCrosses data.leftInjective
          data.rightInjective data.cover data.disjoint data.outer_kept).SameCycle
            first.1 second.1 := by
      change data.output.phi.SameCycle first.1 second.1
      exact hcycle
    have hreturn : data.actualSeamReturn.SameCycle
        firstPosition secondPosition := by
      apply (actualOrderedCutFaceReturnSuccessor_sameCycle_iff RS data.keep
        data.left.crossingEdge data.right.crossingEdge
        data.leftCrosses data.rightCrosses data.leftInjective
        data.rightInjective data.cover data.disjoint
        data.outer_kept firstPosition secondPosition).2
      simpa [firstPosition, secondPosition] using hraw
    have hfirstRoot : data.orderedSeamMarkedRoot firstPosition = first := by
      exact data.orderedSeamMarkedRoot_seamPositionOf first
    have hsecondRoot : data.orderedSeamMarkedRoot secondPosition = second := by
      exact data.orderedSeamMarkedRoot_seamPositionOf second
    rcases firstPosition with left | right <;>
      rcases secondPosition with left' | right'
    · have hsame : left = left' :=
        (sameCycle_inl_inl_iff_of_eq_forward_or_inverse
          data.actualSeamReturn hactual left left').1 hreturn
      exfalso
      apply hne
      rw [← hfirstRoot, ← hsecondRoot, hsame]
    · rw [← hfirstRoot, ← hsecondRoot]
      apply hadjacent left right'
      · simpa [hfirstRoot, hsecondRoot] using hcycle
      · exact sameCycle_inl_inr_imp_adjacent_of_eq_forward_or_inverse
          data.actualSeamReturn hactual left right' hreturn
    · rw [← hfirstRoot, ← hsecondRoot]
      apply Disjoint.symm
      apply hadjacent left' right
      · simpa [hfirstRoot, hsecondRoot] using hcycle.symm
      · exact sameCycle_inr_inl_imp_adjacent_of_eq_forward_or_inverse
          data.actualSeamReturn hactual right left' hreturn
    · have hsame : right = right' :=
        (sameCycle_inr_inr_iff_of_eq_forward_or_inverse
          data.actualSeamReturn hactual right right').1 hreturn
      exfalso
      apply hne
      rw [← hfirstRoot, ← hsecondRoot, hsame]

end GoertzelV24SpliceUnification.OrderedCutSpliceData

end

end Mettapedia.GraphTheory.FourColor
