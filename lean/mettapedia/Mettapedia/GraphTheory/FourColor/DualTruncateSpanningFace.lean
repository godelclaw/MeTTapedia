import Mettapedia.GraphTheory.FourColor.DualTruncateCornerSemantics
import Mettapedia.GraphTheory.FourColor.RotationClosedEdgePotential
import Mettapedia.GraphTheory.FourColor.GoertzelV24OrbitFaceCurvatureBulk

/-!
# Spanning-face calibration of arbitrary dual-and-truncate colourings

On a connected spherical source with two-sided faces and cyclic cubic
rotations, every target Tait colouring defines a closed source edge field.
If one actual face touches every source vertex, its corners fix a common
phase of the integrated field. The resulting source colours are nonzero,
proper, and preserve all literal target cross-edge colours.

This is a geometric witness-domain theorem. It supplies a source witness
from an arbitrary target witness without a colouring table or a complete
colouring theorem. It does not assert such a face exists on every source,
preserve polygon-edge colours, or supply a physical recolouring history.
-/

namespace Mettapedia.GraphTheory.FourColor.DualTruncateSpanningFace

open DualTruncateColoring DualTruncateCornerSemantics
open GoertzelV24FaceOrbitIncidence GoertzelV24FaceDualConnectedness
open GoertzelV24OrbitFaceTwoSided GoertzelV24OrbitFaceCurvatureBulk
open GoertzelV24RotationTaitPotential RotationClosedEdgePotential
open scoped BigOperators

noncomputable section
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

variable {V E : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E] (RS : RotationSystem V E)

/-- One actual face reaches every source vertex. Repeated vertex visits
are permitted; no colouring information is stored in the hypothesis. -/
structure SpanningFace where
  seed : RS.D
  covers : ∀ vertex : V, ∃ dart : RS.D,
    RS.vertOf dart = vertex ∧ RS.phi.SameCycle seed dart

/-- A target cross edge retains the identity of its source edge. -/
def crossField (colouring : (rotation RS).EdgeColoring Color) (edge : E) : Color :=
  colouring (.inl edge)

/-- The corner difference telescopes once around each actual facial cycle. -/
theorem sum_crossField_face_eq_zero
    (htwoSided : OrbitFacesTwoSided RS)
    (colouring : (rotation RS).EdgeColoring Color)
    (hTait : (rotation RS).IsTaitEdgeColoring colouring)
    (face : OrbitFace RS) :
    ∑ edge ∈ orbitFaceBoundary RS face, crossField RS colouring edge = 0 := by
  classical
  have hinj : Set.InjOn RS.edgeOf (orbitFaceDarts RS face) :=
    Finset.card_image_iff.mp (orbitFaceBoundarySimple_of_twoSided RS htwoSided face)
  rw [orbitFaceBoundary, Finset.sum_image hinj]
  have hsum : ∑ dart ∈ orbitFaceDarts RS face,
      corner RS colouring (RS.phi dart) =
        ∑ dart ∈ orbitFaceDarts RS face, corner RS colouring dart := by
    refine Finset.sum_bij (fun dart _ => RS.phi dart) ?_ ?_ ?_ (fun _ _ => rfl)
    · intro dart hdart
      rw [mem_orbitFaceDarts_iff, dartOrbitFace_phi_eq]
      exact (mem_orbitFaceDarts_iff RS face dart).1 hdart
    · intro left _ right _ heq
      exact RS.phi.injective heq
    · intro dart hdart
      refine ⟨RS.phi.symm dart, ?_, RS.phi.apply_symm_apply dart⟩
      rw [mem_orbitFaceDarts_iff]
      have h := dartOrbitFace_phi_eq RS (RS.phi.symm dart)
      rw [RS.phi.apply_symm_apply] at h
      exact h.symm.trans ((mem_orbitFaceDarts_iff RS face dart).1 hdart)
  calc
    (∑ dart ∈ orbitFaceDarts RS face, crossField RS colouring (RS.edgeOf dart)) =
        ∑ dart ∈ orbitFaceDarts RS face,
          (corner RS colouring dart + corner RS colouring (RS.phi dart)) := by
      apply Finset.sum_congr rfl
      intro dart _
      exact cross_of_star RS (star_of_tait RS colouring hTait dart)
    _ = (∑ dart ∈ orbitFaceDarts RS face, corner RS colouring dart) +
        (∑ dart ∈ orbitFaceDarts RS face, corner RS colouring (RS.phi dart)) :=
      Finset.sum_add_distrib
    _ = 0 := by rw [hsum, color_add_self]

variable (hsphere : OrbitSphericalCubicMapData RS)
  (htwoSided : OrbitFacesTwoSided RS)
  (hconnected : (rotationPrimalGraph RS).Connected)
  (hrotation : VertexRotationCyclic RS)
  (colouring : (rotation RS).EdgeColoring Color)
  (hTait : (rotation RS).IsTaitEdgeColoring colouring)

include hsphere htwoSided hrotation hTait in
/-- The integrated target cross field has the correct difference on every
source edge, including distinct parallel edges. -/
theorem cross_potential_difference (root : V) (dart : RS.D) :
    potential RS (crossField RS colouring) hconnected root (RS.vertOf dart) +
      potential RS (crossField RS colouring) hconnected root (RS.vertOf (RS.alpha dart)) =
        crossField RS colouring (RS.edgeOf dart) :=
  potential_difference RS htwoSided
    (orbitFaceInteriorDual_connected RS hsphere.cubic hconnected hrotation)
    hconnected hsphere.euler (crossField RS colouring)
    (sum_crossField_face_eq_zero RS htwoSided colouring hTait) root dart

/-- The potential and corner have one common phase along a face. -/
def phase (root : V) (dart : RS.D) : Color :=
  potential RS (crossField RS colouring) hconnected root (RS.vertOf dart) +
    corner RS colouring dart

include hsphere htwoSided hrotation hTait in
theorem phase_phi (root : V) (dart : RS.D) :
    phase RS hconnected colouring root (RS.phi dart) =
      phase RS hconnected colouring root dart := by
  apply (add_eq_zero_iff_eq _ _).1
  unfold phase
  rw [RS.vert_phi_eq_vert_alpha]
  calc
    (potential RS (crossField RS colouring) hconnected root (RS.vertOf (RS.alpha dart)) +
      corner RS colouring (RS.phi dart)) +
      (potential RS (crossField RS colouring) hconnected root (RS.vertOf dart) +
        corner RS colouring dart) =
      (potential RS (crossField RS colouring) hconnected root (RS.vertOf dart) +
        potential RS (crossField RS colouring) hconnected root (RS.vertOf (RS.alpha dart))) +
        (corner RS colouring dart + corner RS colouring (RS.phi dart)) := by abel
    _ = 0 := by
      rw [cross_potential_difference RS hsphere htwoSided hconnected hrotation colouring hTait,
        show crossField RS colouring (RS.edgeOf dart) =
          corner RS colouring dart + corner RS colouring (RS.phi dart) from
          cross_of_star RS (star_of_tait RS colouring hTait dart), color_add_self]

include hsphere htwoSided hrotation hTait in
theorem phase_sameCycle (root : V) {first second : RS.D}
    (hsame : RS.phi.SameCycle first second) :
    phase RS hconnected colouring root first = phase RS hconnected colouring root second := by
  obtain ⟨power, hpower⟩ := hsame.exists_nat_pow_eq
  have hiterate : ∀ n : Nat,
      phase RS hconnected colouring root ((RS.phi ^ n) first) =
        phase RS hconnected colouring root first := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [pow_succ', Equiv.Perm.mul_apply,
        phase_phi RS hsphere htwoSided hconnected hrotation colouring hTait]
      exact ih
  have h := hiterate power
  rw [hpower] at h
  exact h.symm

variable (face : SpanningFace RS)

/-- One phase chosen from the spanning face calibrates every vertex. -/
def sourceValues (vertex : V) : Color :=
  potential RS (crossField RS colouring) hconnected (RS.vertOf face.seed) vertex +
    phase RS hconnected colouring (RS.vertOf face.seed) face.seed

include hsphere htwoSided hrotation hTait in
theorem sourceValues_eq_corner {dart : RS.D} (hdart : RS.phi.SameCycle face.seed dart) :
    sourceValues RS hconnected colouring face (RS.vertOf dart) = corner RS colouring dart := by
  unfold sourceValues
  rw [phase_sameCycle RS hsphere htwoSided hconnected hrotation colouring hTait _ hdart]
  unfold phase
  rw [← add_assoc, color_add_self, zero_add]

include hsphere htwoSided hrotation hTait in
theorem sourceValues_nonzero (vertex : V) :
    sourceValues RS hconnected colouring face vertex ≠ 0 := by
  obtain ⟨dart, hdart, hface⟩ := face.covers vertex
  rw [← hdart, sourceValues_eq_corner RS hsphere htwoSided hconnected hrotation colouring hTait face hface]
  exact (corners_valid RS colouring hTait).1 dart

include hsphere htwoSided hrotation hTait in
theorem sourceValues_difference (dart : RS.D) :
    sourceValues RS hconnected colouring face (RS.vertOf dart) +
      sourceValues RS hconnected colouring face (RS.vertOf (RS.alpha dart)) =
        crossField RS colouring (RS.edgeOf dart) := by
  unfold sourceValues
  calc
    _ = (potential RS (crossField RS colouring) hconnected (RS.vertOf face.seed) (RS.vertOf dart) +
        potential RS (crossField RS colouring) hconnected (RS.vertOf face.seed) (RS.vertOf (RS.alpha dart))) +
        (phase RS hconnected colouring (RS.vertOf face.seed) face.seed +
          phase RS hconnected colouring (RS.vertOf face.seed) face.seed) := by abel
    _ = _ := by
      rw [color_add_self, add_zero]
      exact cross_potential_difference RS hsphere htwoSided hconnected hrotation colouring hTait _ dart

/-- An arbitrary target witness now supplies a genuine nonzero source
witness under the independently stated spanning-face geometry. -/
def sourceColouring : ThreeVertexColoring RS where
  colour := sourceValues RS hconnected colouring face
  nonzero := sourceValues_nonzero RS hsphere htwoSided hconnected hrotation colouring hTait face
  proper := by
    intro dart heq
    have h := sourceValues_difference RS hsphere htwoSided hconnected hrotation colouring hTait face dart
    rw [heq, color_add_self] at h
    exact hTait (.inl (RS.edgeOf dart)) h.symm

include hsphere htwoSided hrotation hTait in
/-- Re-expanding the reconstructed source preserves all cross-edge
observations jointly; polygon-edge values may change. -/
theorem preserves_cross (edge : E) :
    DualTruncateColoring.colouring RS
      (sourceColouring RS hsphere htwoSided hconnected hrotation colouring hTait face) (.inl edge) =
        colouring (.inl edge) := by
  obtain ⟨dart, hdart⟩ := RS.dartsOn_nonempty edge
  have he := RS.mem_dartsOn.mp hdart
  change crossColour RS (sourceValues RS hconnected colouring face) edge = _
  rw [← he, crossColour_edge]
  exact sourceValues_difference RS hsphere htwoSided hconnected hrotation colouring hTait face dart

end
end Mettapedia.GraphTheory.FourColor.DualTruncateSpanningFace
