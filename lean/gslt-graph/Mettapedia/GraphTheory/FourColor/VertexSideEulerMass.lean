import Mettapedia.GraphTheory.FourColor.VertexSideCappedComponents
import Mettapedia.GraphTheory.FourColor.OpenTangleReplacementEuler

/-!
# Intrinsic Euler mass of a planar vertex side

The open piece is the literal `ofVertexSide` constructor. Planarity of its
edge restriction is inherited from the ambient spherical map by edge
deletion; no disc or connected-shore assumption is supplied. The Euler
mass is four times the number of induced-side components.
-/

namespace Mettapedia.GraphTheory.FourColor.VertexSideEulerMass

open Equiv Equiv.Perm
open GoertzelV24FaceDualConnectedness GoertzelV24RotationCutDartDecomposition
open GoertzelV24RetainedRegionBoundaryOrder GoertzelV24OpenTangleComposition
open GoertzelV24MapEulerBound GoertzelV24InvolutionEdgeList
open GoertzelV24ConnectedMapEulerBound GoertzelV24PermutationOrbitSurgery
open GoertzelV24StellarDualStructure GoertzelV24OrbitFaceCurvatureBulk
open GoertzelV24FaceOrbitPartitionBridge GoertzelV24RetainedSpliceFaceCount
open SphericalNestedBoundaryOrder VertexSideCappedComponents PlanarMapBoundaryRestriction
open OpenTangleMarkedFace OpenTangleReplacementEuler

noncomputable section
attribute [local instance] Classical.propDecidable

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

def retainedRhoOrbitEquiv (RS : RotationSystem V E) (hrot : VertexRotationCyclic RS)
    (hsurj : Function.Surjective RS.vertOf) (side : V → Prop) :
    Quotient (SameCycle.setoid (retainedRho RS side)) ≃ {v // side v} where
  toFun := Quotient.lift (fun d => ⟨RS.vertOf d.val, d.2⟩)
    (fun _ _ h => Subtype.ext (GoertzelV24StellarRotationSystem.vertOf_eq_of_rho_sameCycle
      RS (sameCycle_subtypePerm.mp h)))
  invFun v := Quotient.mk _ ⟨(hsurj v.val).choose, by
    rw [(hsurj v.val).choose_spec]; exact v.2⟩
  left_inv c := by
    induction c using Quotient.inductionOn with
    | h d =>
      apply Quotient.sound
      apply SameCycle.subtypePerm
      exact hrot _ _ (hsurj (RS.vertOf d.val)).choose_spec
  right_inv v := Subtype.ext (hsurj v.val).choose_spec

theorem cycle_count_retainedRho (RS : RotationSystem V E) (hrot : VertexRotationCyclic RS)
    (hsurj : Function.Surjective RS.vertOf) (side : V → Prop) :
    (retainedRho RS side).partition.parts.card = Fintype.card {v // side v} := by
  rw [← card_permOrbit_eq_card_partition_parts]
  exact Fintype.card_congr (retainedRhoOrbitEquiv RS hrot hsurj side)

/-- Splitting the original dart carrier keeps all outside rotations, but
on the selected side the face walk is exactly the open face walk. -/
def sideSplitEquiv (RS : RotationSystem V E) (side : V → Prop) :
    RetainedDart RS side ⊕ RetainedDart RS (fun v => ¬ side v) ≃ RS.D :=
  Equiv.sumCompl (fun d => side (RS.vertOf d))

theorem cappedPhi_split (RS : RotationSystem V E) (side : V → Prop) :
    cappedPhi RS side = (sideSplitEquiv RS side).permCongr
      (Equiv.sumCongr (retainedCappedFacePerm RS side) (retainedRho RS (fun v => ¬ side v))) := by
  ext d
  obtain ⟨x, rfl⟩ := (sideSplitEquiv RS side).surjective d
  rw [Equiv.permCongr_apply, Equiv.symm_apply_apply]
  rcases x with i | o
  · exact cappedPhi_retained RS side i
  · change cappedPhi RS side o.val = RS.rho o.val
    simp only [cappedPhi, Perm.mul_apply,
      cappedAlpha_apply, InsideEdge, o.2, false_and, if_false]

theorem openPhi_ofVertexSide (RS : RotationSystem V E) (side : V → Prop)
    (outer : RetainedDart RS side) :
    openPhi (OpenTangleData.ofVertexSide RS side outer) =
      (retainedDartEquivInternalSumBoundary RS side).permCongr (retainedCappedFacePerm RS side) := by
  ext d
  rcases d with i | b
  · change retainedDartEquivInternalSumBoundary RS side
        (retainedRho RS side (internalAlpha RS side i).val) =
      retainedDartEquivInternalSumBoundary RS side
        (retainedRho RS side (retainedCappedAlpha RS side i.val))
    congr 2
    exact Subtype.ext (retainedCappedAlpha_apply_internal RS side i.val i.2).symm
  · change retainedDartEquivInternalSumBoundary RS side (retainedRho RS side b.val) =
      retainedDartEquivInternalSumBoundary RS side
        (retainedRho RS side (retainedCappedAlpha RS side b.val))
    rw [retainedCappedAlpha_apply_boundary RS side b.val b.2]

theorem cycle_count_cappedPhi (RS : RotationSystem V E) (hrot : VertexRotationCyclic RS)
    (hsurj : Function.Surjective RS.vertOf) (side : V → Prop) (outer : RetainedDart RS side) :
    orbitCount (cappedPhi RS side) =
      (openPhi (OpenTangleData.ofVertexSide RS side outer)).partition.parts.card +
        Fintype.card {v // ¬ side v} := by
  change Fintype.card (Quotient (SameCycle.setoid _)) = _
  rw [card_permOrbit_eq_card_partition_parts, cappedPhi_split, card_permCongr_partition_parts,
    cycle_count_sum, cycle_count_retainedRho RS hrot hsurj (fun v => ¬ side v),
    openPhi_ofVertexSide, card_permCongr_partition_parts]

def movedCappedEquivInternal (RS : RotationSystem V E) (side : V → Prop) :
    {d // d ∈ movedFinset (cappedAlpha RS side)} ≃ InternalDart RS side where
  toFun d := by
    have hd : InsideEdge RS side d.val := by
      have h := mem_movedFinset.mp d.2
      by_contra hn
      exact h (by rw [cappedAlpha_apply, if_neg hn])
    exact ⟨⟨d.val, hd.1⟩, hd.2⟩
  invFun d := ⟨d.val.val, mem_movedFinset.mpr (by
    rw [cappedAlpha_apply, if_pos (show InsideEdge RS side d.val.val from ⟨d.val.2, d.2⟩)]
    exact RS.alpha_fixfree _)⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem twice_capped_edges (RS : RotationSystem V E) (side : V → Prop) :
    2 * (edgeList (cappedAlpha RS side)).length = Fintype.card (InternalDart RS side) := by
  rw [two_mul_length_edgeList_eq_card_movedFinset _ (cappedAlpha_involutive RS side)]
  have hc := Fintype.card_congr (movedCappedEquivInternal RS side)
  simpa only [Fintype.card_coe] using hc

/-- Planarity is obtained from the complete ambient edge presentation by
deletion, not from an assumed property of the candidate replacement. -/
theorem capped_plane (RS : RotationSystem V E) (hsphere : OrbitSphericalCubicMapData RS)
    (hconn : (rotationPrimalGraph RS).Connected) (hrot : VertexRotationCyclic RS)
    (side : V → Prop) : PlaneEdges RS.rho (edgeList (cappedAlpha RS side)) := by
  obtain ⟨added, _, hn, hp⟩ := exists_capped_edge_extension RS hsphere hconn hrot
    side side (fun _ h => h)
  exact plane_tail RS.rho added _ hn hp

/-- An arbitrary actual vertex side of a connected spherical cubic map.
The selected side and its complement may each be disconnected. -/
theorem mass_eq_four_components (RS : RotationSystem V E)
    (hsphere : OrbitSphericalCubicMapData RS) (hconn : (rotationPrimalGraph RS).Connected)
    (hrot : VertexRotationCyclic RS) (side : V → Prop) (outer : RetainedDart RS side) :
    eulerMass (OpenTangleData.ofVertexSide RS side outer) =
      4 * (Fintype.card (SideGraph RS side).ConnectedComponent : ℤ) := by
  have hsurj : Function.Surjective RS.vertOf := by
    intro v
    obtain ⟨d, hd⟩ := Finset.card_pos.mp (show 0 < (RS.dartsAt v).card by rw [hsphere.cubic]; omega)
    exact ⟨d, (Finset.mem_filter.mp hd).2⟩
  have he := capped_plane RS hsphere hconn hrot side
  unfold PlaneEdges at he
  rw [swapProduct_edgeList _ (cappedAlpha_involutive RS side),
    orbitCount_rho_eq_card_vertex RS hrot hsurj,
    wordOrbitCount_capped RS hrot hsurj side] at he
  change Fintype.card V + orbitCount (cappedPhi RS side) = _ at he
  rw [cycle_count_cappedPhi RS hrot hsurj side outer] at he
  have hi := twice_capped_edges RS side
  have hv := Fintype.card_congr (Equiv.sumCompl side)
  simp only [Fintype.card_sum] at hv
  unfold eulerMass
  omega

theorem mass_range (RS : RotationSystem V E) (hsphere : OrbitSphericalCubicMapData RS)
    (hconn : (rotationPrimalGraph RS).Connected) (hrot : VertexRotationCyclic RS)
    (side : V → Prop) (outer : RetainedDart RS side) (hproper : ∃ v, ¬ side v) :
    0 ≤ eulerMass (OpenTangleData.ofVertexSide RS side outer) ∧
      eulerMass (OpenTangleData.ofVertexSide RS side outer) ≤
        4 * (Fintype.card (BoundaryDart RS side) : ℤ) := by
  rw [mass_eq_four_components RS hsphere hconn hrot]
  have := components_le_boundary RS hconn side hproper
  omega

/-- At most `k` ports give a `k+1`-element structural coordinate, without
a bound on the size or face perimeters of the piece. -/
def componentCode (RS : RotationSystem V E) (hconn : (rotationPrimalGraph RS).Connected)
    (side : V → Prop) (hproper : ∃ v, ¬ side v) (k : ℕ)
    (hwidth : Fintype.card (BoundaryDart RS side) ≤ k) : Fin (k + 1) :=
  ⟨Fintype.card (SideGraph RS side).ConnectedComponent, by
    have := components_le_boundary RS hconn side hproper
    omega⟩

theorem mass_eq_four_code (RS : RotationSystem V E) (hsphere : OrbitSphericalCubicMapData RS)
    (hconn : (rotationPrimalGraph RS).Connected) (hrot : VertexRotationCyclic RS)
    (side : V → Prop) (outer : RetainedDart RS side) (hproper : ∃ v, ¬ side v) (k : ℕ)
    (hwidth : Fintype.card (BoundaryDart RS side) ≤ k) :
    eulerMass (OpenTangleData.ofVertexSide RS side outer) =
      4 * ((componentCode RS hconn side hproper k hwidth).val : ℤ) :=
  mass_eq_four_components RS hsphere hconn hrot side outer

section Replacement
variable {V' E' X I L K M : Type*}
  [Fintype V'] [DecidableEq V'] [Fintype E'] [DecidableEq E']
  [Fintype X] [DecidableEq X] [Fintype I] [DecidableEq I]
  [Fintype L] [DecidableEq L] [Fintype K] [Fintype M]

/-- Equal boundary-return records and component counts preserve actual
sewn Euler characteristic in every fixed exterior. Both pieces are
derived from spherical ambient maps; neither is assumed to be a disc. -/
theorem replacement_euler (RS : RotationSystem V E) (RS' : RotationSystem V' E')
    (hsphere : OrbitSphericalCubicMapData RS) (hsphere' : OrbitSphericalCubicMapData RS')
    (hconn : (rotationPrimalGraph RS).Connected) (hconn' : (rotationPrimalGraph RS').Connected)
    (hrot : VertexRotationCyclic RS) (hrot' : VertexRotationCyclic RS')
    (side : V → Prop) (side' : V' → Prop)
    (outer : RetainedDart RS side) (outer' : RetainedDart RS' side')
    (hc : Fintype.card (SideGraph RS side).ConnectedComponent =
      Fintype.card (SideGraph RS' side').ConnectedComponent)
    (oc : BoundaryDart RS side ≃ K) (nc : BoundaryDart RS' side' ≃ K)
    (oo : M → Option (InternalDart RS side ⊕ BoundaryDart RS side))
    (no : M → Option (InternalDart RS' side' ⊕ BoundaryDart RS' side'))
    (heq : NamedOpenFace.record (OpenTangleData.ofVertexSide RS side outer) oc oo =
      NamedOpenFace.record (OpenTangleData.ofVertexSide RS' side' outer') nc no)
    (left : OpenTangleData X I L) (outside : L ≃ K) :
    OpenTangleRewireFaces.compositeEuler left (OpenTangleData.ofVertexSide RS side outer)
        (outside.trans oc.symm) =
      OpenTangleRewireFaces.compositeEuler left (OpenTangleData.ofVertexSide RS' side' outer')
        (outside.trans nc.symm) := by
  apply (euler_eq_iff_mass left _ _ oc nc oo no heq outside).mpr
  rw [mass_eq_four_components RS hsphere hconn hrot,
    mass_eq_four_components RS' hsphere' hconn' hrot', hc]
end Replacement

end
end Mettapedia.GraphTheory.FourColor.VertexSideEulerMass
