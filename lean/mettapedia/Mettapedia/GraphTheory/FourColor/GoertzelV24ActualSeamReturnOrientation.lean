import Mettapedia.GraphTheory.FourColor.GoertzelV24OrderedSeamReturnAdjacency
import Mettapedia.GraphTheory.FourColor.GoertzelV24PlanarBondSpliceEitherOrientation

/-!
# The actual seam return in either source orientation

Addendum XXVII glues complementary annular pieces along two ordered simple
transversals.  The source construction allows either coherent orientation of
the deleted boundary.  Earlier face-count proofs computed the corresponding
actual seam-return permutation internally; this module exposes that calculation
as a reusable API.

For a genuine planar bond, the actual return is exactly one of the two explicit
capped boundary returns.  Hence two distinct roots on one completed seam face
must lie on opposite sides at adjacent offsets.  This is the finite permutation
part of Lean flag L1.  It neither constructs the source crosscuts nor proves
edge-disjointness of the remaining neighboring geometric seam arcs.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ActualSeamReturnOrientation

open GoertzelV24DeletedRegionBoundaryOrder
open GoertzelV24DeletedRegionRotationSplice
open GoertzelV24FaceDualConnectedness
open GoertzelV24OrbitFaceTwoSided
open GoertzelV24OrderedCutFaceReturnProfile
open GoertzelV24OrderedCutRotationSplice
open GoertzelV24OrderedSeamReturnAdjacency
open GoertzelV24OrbitFaceCurvatureBulk
open GoertzelV24PlanarBondBoundaryOrder
open GoertzelV24PlanarBondSpliceEitherOrientation
open GoertzelV24PlanarBondSpliceEuler
open GoertzelV24RetainedRegionBoundaryOrder
open GoertzelV24RotationCutDartDecomposition
open GoertzelV24RotationVertexCutProfile
open GoertzelV24RotationSpliceConstructor
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

local instance graphEdgeSetDecidableEq : DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

noncomputable section

/-- The actual ordered seam-return map of a planar-bond splice is one of the
two explicit capped boundary returns allowed by the source orientation. -/
theorem actualOrderedCutFaceReturnSuccessor_eq_forward_or_inverse
    (data : Data G) (deleted : Finset V)
    (leftCrossing rightCrossing : Fin n → G.edgeSet)
    (hboundary : orderedCut leftCrossing ∪ orderedCut rightCrossing =
      vertexSetCrossingEdges data.toRotationSystem deleted)
    (hleftInjective : Function.Injective leftCrossing)
    (hrightInjective : Function.Injective rightCrossing)
    (hdisjoint : Disjoint (orderedCut leftCrossing)
      (orderedCut rightCrossing))
    (horder : CutsFollowEitherDeletedBoundaryOrientation
      data.toRotationSystem deleted leftCrossing rightCrossing hboundary
      hleftInjective hrightInjective hdisjoint)
    (hsphere : OrbitSphericalCubicMapData data.toRotationSystem)
    (htwoSided : OrbitFacesTwoSided data.toRotationSystem)
    (hconnected : G.Connected)
    (hrotation : VertexRotationCyclic data.toRotationSystem)
    (hretainedConnected :
      (G.induce {vertex | deletedRegionKeep deleted vertex}).Connected)
    (hdeletedConnected :
      (G.induce {vertex |
        Not (deletedRegionKeep deleted vertex)}).Connected)
    (houter : data.toRotationSystem.vertOf data.toRotationSystem.outer ∉
      deleted) :
    let hleftCrosses := leftCrossing_outward data.toRotationSystem deleted
      leftCrossing rightCrossing hboundary
    let hrightCrosses := rightCrossing_outward data.toRotationSystem deleted
      leftCrossing rightCrossing hboundary
    let hcover := deletedRegionBoundaryCover data.toRotationSystem deleted
      leftCrossing rightCrossing hboundary
    let actual := actualOrderedCutFaceReturnSuccessor data.toRotationSystem
      (deletedRegionKeep deleted) leftCrossing rightCrossing
      hleftCrosses hrightCrosses hleftInjective hrightInjective
      hcover hdisjoint houter
    actual = oppositeBoundaryCycle n * orderedPositionSeamSwap n ∨
      actual = (oppositeBoundaryCycle n)⁻¹ * orderedPositionSeamSwap n := by
  dsimp only
  let positionEquiv := orderedRetainedBoundaryPositionEquiv
    data.toRotationSystem (deletedRegionKeep deleted)
      leftCrossing rightCrossing
      (leftCrossing_outward data.toRotationSystem deleted
        leftCrossing rightCrossing hboundary)
      (rightCrossing_outward data.toRotationSystem deleted
        leftCrossing rightCrossing hboundary)
      hleftInjective hrightInjective
      (deletedRegionBoundaryCover data.toRotationSystem deleted
        leftCrossing rightCrossing hboundary) hdisjoint
  let seamSwap := orderedBoundarySeamSwap data.toRotationSystem
    (deletedRegionKeep deleted) leftCrossing rightCrossing
      (leftCrossing_outward data.toRotationSystem deleted
        leftCrossing rightCrossing hboundary)
      (rightCrossing_outward data.toRotationSystem deleted
        leftCrossing rightCrossing hboundary)
      hleftInjective hrightInjective
      (deletedRegionBoundaryCover data.toRotationSystem deleted
        leftCrossing rightCrossing hboundary) hdisjoint
  have hseamCoordinate :
      positionEquiv.symm.permCongr seamSwap =
        orderedPositionSeamSwap n := by
    exact orderedRetainedBoundaryPosition_seamSwap_congr
      data.toRotationSystem deleted leftCrossing rightCrossing hboundary
        hleftInjective hrightInjective hdisjoint
  rcases horder with hforward | hreverse
  · right
    have hretainedBoundary :
        retainedRegionBoundarySuccessor data.toRotationSystem
            (deletedRegionKeep deleted) =
          positionEquiv.permCongr (oppositeBoundaryCycle n)⁻¹ := by
      rw [retained_boundarySuccessor_eq_deleted_inverse_of_planar_bond
        data deleted hsphere htwoSided hconnected hrotation
        hretainedConnected hdeletedConnected, hforward]
      rfl
    rw [actualOrderedCutFaceReturnSuccessor_eq_retainedBoundarySuccessor,
      hretainedBoundary]
    change positionEquiv.symm.permCongr
        (positionEquiv.permCongr (oppositeBoundaryCycle n)⁻¹ * seamSwap) =
      (oppositeBoundaryCycle n)⁻¹ * orderedPositionSeamSwap n
    apply Equiv.ext
    intro position
    simp only [Equiv.permCongr_apply, Equiv.Perm.mul_apply,
      Equiv.symm_symm, Equiv.symm_apply_apply]
    exact congrArg
      (fun point => ((oppositeBoundaryCycle n)⁻¹ :
        Equiv.Perm (OrderedSeamPosition n)) point)
      (DFunLike.congr_fun hseamCoordinate position)
  · left
    have hretainedBoundary :
        retainedRegionBoundarySuccessor data.toRotationSystem
            (deletedRegionKeep deleted) =
          positionEquiv.permCongr (oppositeBoundaryCycle n) := by
      rw [retained_boundarySuccessor_eq_deleted_inverse_of_planar_bond
        data deleted hsphere htwoSided hconnected hrotation
        hretainedConnected hdeletedConnected, hreverse]
      rfl
    rw [actualOrderedCutFaceReturnSuccessor_eq_retainedBoundarySuccessor,
      hretainedBoundary]
    change positionEquiv.symm.permCongr
        (positionEquiv.permCongr (oppositeBoundaryCycle n) * seamSwap) =
      oppositeBoundaryCycle n * orderedPositionSeamSwap n
    apply Equiv.ext
    intro position
    simp only [Equiv.permCongr_apply, Equiv.Perm.mul_apply,
      Equiv.symm_symm, Equiv.symm_apply_apply]
    exact congrArg
      (fun point => (oppositeBoundaryCycle n :
        Equiv.Perm (OrderedSeamPosition n)) point)
      (DFunLike.congr_fun hseamCoordinate position)

/-- Either allowed source orientation has no distinct same-side left roots. -/
theorem sameCycle_inl_inl_iff_of_eq_forward_or_inverse
    (actual : Equiv.Perm (OrderedSeamPosition n))
    (hactual :
      actual = oppositeBoundaryCycle n * orderedPositionSeamSwap n ∨
      actual = (oppositeBoundaryCycle n)⁻¹ * orderedPositionSeamSwap n)
    (first second : Fin n) :
    actual.SameCycle (Sum.inl first) (Sum.inl second) ↔ first = second := by
  rcases hactual with hforward | hinverse
  · rw [hforward]
    exact forward_sameCycle_inl_inl_iff first second
  · rw [hinverse]
    exact inverse_sameCycle_inl_inl_iff first second

/-- Either allowed source orientation has no distinct same-side right roots. -/
theorem sameCycle_inr_inr_iff_of_eq_forward_or_inverse
    (actual : Equiv.Perm (OrderedSeamPosition n))
    (hactual :
      actual = oppositeBoundaryCycle n * orderedPositionSeamSwap n ∨
      actual = (oppositeBoundaryCycle n)⁻¹ * orderedPositionSeamSwap n)
    (first second : Fin n) :
    actual.SameCycle (Sum.inr first) (Sum.inr second) ↔ first = second := by
  rcases hactual with hforward | hinverse
  · rw [hforward]
    exact forward_sameCycle_inr_inr_iff first second
  · rw [hinverse]
    exact inverse_sameCycle_inr_inr_iff first second

/-- If opposite-side roots share an actual seam-return cycle, their offsets
are adjacent; the direction records the source's global orientation. -/
theorem sameCycle_inl_inr_imp_adjacent_of_eq_forward_or_inverse
    (actual : Equiv.Perm (OrderedSeamPosition n))
    (hactual :
      actual = oppositeBoundaryCycle n * orderedPositionSeamSwap n ∨
      actual = (oppositeBoundaryCycle n)⁻¹ * orderedPositionSeamSwap n)
    (left right : Fin n)
    (hcycle : actual.SameCycle (Sum.inl left) (Sum.inr right)) :
    left.val = right.val + 1 ∨ right.val = left.val + 1 := by
  rcases hactual with hforward | hinverse
  · left
    exact (forward_sameCycle_inl_inr_iff left right).1 (hforward ▸ hcycle)
  · right
    exact (inverse_sameCycle_inl_inr_iff left right).1 (hinverse ▸ hcycle)

/-- The same adjacent-offset conclusion holds with the two roots reversed. -/
theorem sameCycle_inr_inl_imp_adjacent_of_eq_forward_or_inverse
    (actual : Equiv.Perm (OrderedSeamPosition n))
    (hactual :
      actual = oppositeBoundaryCycle n * orderedPositionSeamSwap n ∨
      actual = (oppositeBoundaryCycle n)⁻¹ * orderedPositionSeamSwap n)
    (right left : Fin n)
    (hcycle : actual.SameCycle (Sum.inr right) (Sum.inl left)) :
    left.val = right.val + 1 ∨ right.val = left.val + 1 :=
  sameCycle_inl_inr_imp_adjacent_of_eq_forward_or_inverse actual hactual
    left right hcycle.symm

end

end GoertzelV24ActualSeamReturnOrientation

end Mettapedia.GraphTheory.FourColor
