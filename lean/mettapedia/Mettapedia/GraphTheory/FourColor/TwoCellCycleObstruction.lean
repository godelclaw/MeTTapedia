import Mettapedia.GraphTheory.FourColor.TwoCellBoundaryChoice
import Mettapedia.GraphTheory.FourColor.DualTruncateForestCollapse
import Mettapedia.GraphTheory.FourColor.DualTruncateMapGeometry
import Mettapedia.GraphTheory.FourColor.CubicRotationByteCertificate

/-!
# A genuine exterior obstructing direct two-cell cycle reconstruction

The source is a dodecahedral map with its supplied spherical rotation.
Its dual-and-truncate target has 60 vertices. Selecting two adjacent source
vertices gives a ten-vertex patch, whose eight cut ports occur in the stated
perimeter order. The partial input is proper at every exterior target vertex;
its two selected source values are zero. There is no target colouring that
extends this exact exterior. Nevertheless the literal eight-cycle accepts
precisely the supplied eight-port word.

This refutes direct reconstruction fixing this exterior for this proposed
cycle replacement. It leaves exterior recolouring and other decompositions
available. The actual target has only pentagonal and hexagonal faces; no universal
coverage or recolouring impossibility follows from this fixed-exterior obstruction.
-/

namespace Mettapedia.GraphTheory.FourColor.TwoCellCycleObstruction

open CubicRotationByteCertificate DualTruncateColoring DualTruncateCornerSemantics
open DualTruncateOpenPatch DualTruncateForestCollapse
open GoertzelV24FaceDualConnectedness GoertzelV24FaceOrbitIncidence
open GoertzelV24FaceOrbitPartitionBridge GoertzelV24OrbitFaceCurvatureBulk
open GoertzelV24TwoEdgeCutMinimality DualTruncateMapGeometry

noncomputable section

def code : CubicRotationByteCertificate.Code 20 30 where
  neighbours := { size := 60, pages := fun _ => ByteArray.mk #[
      1,0,10,0,19,0,0,0,2,0,8,0,1,0,3,0,6,0,2,0,19,0,4,0,
      3,0,17,0,5,0,4,0,15,0,6,0,5,0,7,0,2,0,6,0,14,0,8,0,
      7,0,9,0,1,0,8,0,13,0,10,0,9,0,11,0,0,0,10,0,12,0,18,0,
      11,0,13,0,16,0,12,0,9,0,14,0,13,0,7,0,15,0,14,0,5,0,16,0,
      15,0,17,0,12,0,16,0,4,0,18,0,17,0,19,0,11,0,18,0,3,0,0,0] }
  mates := { size := 60, pages := fun _ => ByteArray.mk #[
      3,0,32,0,59,0,0,0,6,0,26,0,4,0,9,0,20,0,7,0,58,0,12,0,
      11,0,52,0,15,0,14,0,46,0,18,0,17,0,21,0,8,0,19,0,43,0,24,0,
      23,0,27,0,5,0,25,0,40,0,30,0,29,0,33,0,1,0,31,0,36,0,56,0,
      34,0,39,0,50,0,37,0,28,0,42,0,41,0,22,0,45,0,44,0,16,0,48,0,
      47,0,51,0,38,0,49,0,13,0,54,0,53,0,57,0,35,0,55,0,10,0,2,0] }
  edges := { size := 60, pages := fun _ => ByteArray.mk #[
      0,0,1,0,2,0,0,0,3,0,4,0,3,0,5,0,6,0,5,0,8,0,7,0,
      7,0,10,0,9,0,9,0,12,0,11,0,11,0,13,0,6,0,13,0,15,0,14,0,
      14,0,16,0,4,0,16,0,18,0,17,0,17,0,19,0,1,0,19,0,20,0,21,0,
      20,0,22,0,23,0,22,0,18,0,24,0,24,0,15,0,25,0,25,0,12,0,26,0,
      26,0,27,0,23,0,27,0,10,0,28,0,28,0,29,0,21,0,29,0,8,0,2,0] }
  representatives := { size := 30, pages := fun _ => ByteArray.mk #[
      0,0,1,0,2,0,4,0,5,0,7,0,8,0,11,0,10,0,14,0,13,0,17,0,
      16,0,19,0,23,0,22,0,25,0,29,0,28,0,31,0,34,0,35,0,37,0,38,0,
      41,0,44,0,47,0,49,0,53,0,55,0] }

theorem valid : code.Valid := by decide +kernel
abbrev source : RotationSystem.{0,0,0} (Fin 20) (Fin 30) := code.rotation valid
abbrev target := rotation source
abbrev graph := rotationPrimalGraph source

instance : DecidableRel graph.Adj := fun v w =>
  inferInstanceAs (Decidable (∃ d : Position 20, d.1 = v ∧ (code.mate d).1 = w))

theorem source_cubic : source.IsCubic := code.cubic valid

theorem source_rotationCyclic : VertexRotationCyclic source := by
  rintro ⟨v,i⟩ ⟨w,j⟩ h
  change v = w at h
  subst w
  have h01 : source.rho.SameCycle (v,0) (v,1) :=
    ⟨1, by simp [CubicRotationByteCertificate.Code.rho]⟩
  have h12 : source.rho.SameCycle (v,1) (v,2) :=
    ⟨1, by simp [CubicRotationByteCertificate.Code.rho]⟩
  have h02 := h01.trans h12
  fin_cases i <;> fin_cases j <;> first
    | exact Equiv.Perm.SameCycle.refl _ _
    | exact h01 | exact h12 | exact h02
    | exact h01.symm | exact h12.symm | exact h02.symm

theorem source_face_count : Fintype.card (OrbitFace source) = 12 := by
  change Fintype.card (Quotient (Equiv.Perm.SameCycle.setoid source.phi)) = 12
  rw [card_permOrbit_eq_card_partition_parts]
  decide +kernel

theorem source_spherical : OrbitSphericalCubicMapData source where
  cubic := source_cubic
  euler := by rw [source_face_count]; decide +kernel

theorem source_reachable (v : Fin 20) : graph.Reachable 0 v := by
  have r0 : graph.Reachable 0 0 := .rfl
  have h1 : graph.Adj 0 1 := by decide +kernel
  have r1 : graph.Reachable 0 1 := r0.trans h1.reachable
  have h10 : graph.Adj 0 10 := by decide +kernel
  have r10 : graph.Reachable 0 10 := r0.trans h10.reachable
  have h19 : graph.Adj 0 19 := by decide +kernel
  have r19 : graph.Reachable 0 19 := r0.trans h19.reachable
  have h2 : graph.Adj 1 2 := by decide +kernel
  have r2 : graph.Reachable 0 2 := r1.trans h2.reachable
  have h8 : graph.Adj 1 8 := by decide +kernel
  have r8 : graph.Reachable 0 8 := r1.trans h8.reachable
  have h9 : graph.Adj 10 9 := by decide +kernel
  have r9 : graph.Reachable 0 9 := r10.trans h9.reachable
  have h11 : graph.Adj 10 11 := by decide +kernel
  have r11 : graph.Reachable 0 11 := r10.trans h11.reachable
  have h3 : graph.Adj 19 3 := by decide +kernel
  have r3 : graph.Reachable 0 3 := r19.trans h3.reachable
  have h18 : graph.Adj 19 18 := by decide +kernel
  have r18 : graph.Reachable 0 18 := r19.trans h18.reachable
  have h6 : graph.Adj 2 6 := by decide +kernel
  have r6 : graph.Reachable 0 6 := r2.trans h6.reachable
  have h7 : graph.Adj 8 7 := by decide +kernel
  have r7 : graph.Reachable 0 7 := r8.trans h7.reachable
  have h13 : graph.Adj 9 13 := by decide +kernel
  have r13 : graph.Reachable 0 13 := r9.trans h13.reachable
  have h12 : graph.Adj 11 12 := by decide +kernel
  have r12 : graph.Reachable 0 12 := r11.trans h12.reachable
  have h4 : graph.Adj 3 4 := by decide +kernel
  have r4 : graph.Reachable 0 4 := r3.trans h4.reachable
  have h17 : graph.Adj 18 17 := by decide +kernel
  have r17 : graph.Reachable 0 17 := r18.trans h17.reachable
  have h5 : graph.Adj 6 5 := by decide +kernel
  have r5 : graph.Reachable 0 5 := r6.trans h5.reachable
  have h14 : graph.Adj 7 14 := by decide +kernel
  have r14 : graph.Reachable 0 14 := r7.trans h14.reachable
  have h16 : graph.Adj 12 16 := by decide +kernel
  have r16 : graph.Reachable 0 16 := r12.trans h16.reachable
  have h15 : graph.Adj 5 15 := by decide +kernel
  have r15 : graph.Reachable 0 15 := r5.trans h15.reachable
  fin_cases v
  · exact r0
  · exact r1
  · exact r2
  · exact r3
  · exact r4
  · exact r5
  · exact r6
  · exact r7
  · exact r8
  · exact r9
  · exact r10
  · exact r11
  · exact r12
  · exact r13
  · exact r14
  · exact r15
  · exact r16
  · exact r17
  · exact r18
  · exact r19

theorem source_connected : graph.Connected where
  nonempty := inferInstance
  preconnected v w := (source_reachable v).symm.trans (source_reachable w)

theorem target_mapClass : BridgelessSphericalCubicMapData target :=
  mapClass_of source source_spherical source_connected source_rotationCyclic

theorem source_face_length (d : source.D) : (source.faceOrbit d).card = 5 := by
  revert d
  decide +kernel

/-- All actual target faces are pentagons or hexagons, derived from the
uniform face law rather than a target face table. -/
theorem target_face_lengths (d : source.D) :
    (target.faceOrbit (d,0)).card = 6 ∧
    (target.faceOrbit (d,1)).card = 6 ∧
    (target.faceOrbit (d,2)).card = 5 := by
  exact ⟨DualTruncateFaceGeometry.vertex_face_length source source_cubic source_rotationCyclic d,
    DualTruncateFaceGeometry.vertex_face_length_one source source_cubic source_rotationCyclic d,
    (DualTruncateFaceGeometry.faceOrbit_two_card source source_rotationCyclic d).trans
      (source_face_length d)⟩

def selected (v : Fin 20) : Prop := v.val < 2
def keep : source.D → Prop := vertexRegion source selected
instance : DecidablePred selected := by unfold selected; infer_instance
instance : DecidablePred keep := by unfold keep vertexRegion selected; infer_instance

def exteriorWord : ByteArray := ByteArray.mk #[0,0,2,3,1,2,1,2,1,3,2,1,3,1,3,1,2,3,2,1]
def exteriorColour (v : Fin 20) : Color :=
  if selected v then 0 else wordColour exteriorWord v.val
def base : Edge source → Color := edgeColour source exteriorColour

theorem simple_source : SimpleSource source := by unfold SimpleSource; decide +kernel
theorem separated : Separated source selected := by unfold Separated; decide +kernel

theorem forest : (graph.induce {v | selected v}).IsAcyclic := by
  apply SimpleGraph.IsAcyclic.of_card_le_two
  rw [ENat.card_eq_coe_fintype_card, Fintype.card_subtype]
  change ((Finset.univ.filter selected).card : ℕ∞) ≤ 2
  have hc : (Finset.univ.filter selected).card = 2 := by decide +kernel
  rw [hc]
  exact le_rfl

theorem exterior_stars (d : source.D) (hd : ¬keep d) : Star source base d := by
  have h : (fun i : Fin 3 => base (target.edgeOf (d,i))) =
      (fun i => if i = 0 then exteriorColour (source.vertOf d) +
        exteriorColour (source.vertOf (source.alpha d))
      else if i = 1 then exteriorColour (source.vertOf (source.alpha d))
      else exteriorColour (source.vertOf d)) := by
    funext i
    fin_cases i
    · exact star_colour_zero source exteriorColour d
    · exact star_colour_one source exteriorColour d
    · exact star_colour_two source exteriorColour d
  unfold DualTruncateCornerSemantics.Star
  change (∀ i, (fun i : Fin 3 => base (target.edgeOf (d,i))) i ≠ 0) ∧
    Function.Injective (fun i : Fin 3 => base (target.edgeOf (d,i)))
  rw [h]
  clear h
  revert d
  decide +kernel

theorem paired : PairedExterior source selected base exteriorColour := by
  intro d _
  exact star_colour_two source exteriorColour d

def fibreEquiv :
    {t : target.EdgeColoring Color // target.IsTaitEdgeColoring t ∧
      Extends source keep base t} ≃ SourceFibre source selected exteriorColour :=
  extensionSourceEquiv source selected simple_source separated
    source_cubic source_rotationCyclic forest base exterior_stars exteriorColour paired

theorem no_source_choice : ¬Nonempty (SourceFibre source selected exteriorColour) := by
  rintro ⟨s⟩
  have neighbours0 : ∀ i : Fin 3,
      source.vertOf (source.alpha (0,i)) = (![1,10,19] i : Fin 20) := by decide +kernel
  have neighbours1 : ∀ i : Fin 3,
      source.vertOf (source.alpha (1,i)) = (![0,2,8] i : Fin 20) := by decide +kernel
  have h10 : s.val.colour 10 = blue := s.property 10 (by decide)
  have h19 : s.val.colour 19 = red := s.property 19 (by decide)
  have h2 : s.val.colour 2 = blue := s.property 2 (by decide)
  have h8 : s.val.colour 8 = red := s.property 8 (by decide)
  have h06 := s.val.proper (0,1)
  have h05 := s.val.proper (0,2)
  have h12 := s.val.proper (1,1)
  have h17 := s.val.proper (1,2)
  have h01 := s.val.proper (0,0)
  rw [neighbours0] at h06 h05 h01
  rw [neighbours1] at h12 h17
  change s.val.colour 0 ≠ s.val.colour 10 at h06
  change s.val.colour 0 ≠ s.val.colour 19 at h05
  change s.val.colour 1 ≠ s.val.colour 2 at h12
  change s.val.colour 1 ≠ s.val.colour 8 at h17
  change s.val.colour 0 ≠ s.val.colour 1 at h01
  rw [h10] at h06
  rw [h19] at h05
  rw [h2] at h12
  rw [h8] at h17
  exact TwoCellBoundaryChoice.equal_forced_colours blue red (by decide) (by decide)
    (by decide) ⟨s.val.colour 0,s.val.colour 1,s.val.nonzero 0,s.val.nonzero 1,
      h06,h05,h12,h17,h01⟩

/-- The rejection concerns every genuine target extension, not only a
particular reconstruction algorithm or a table of corner words. -/
theorem no_fixed_exterior_extension :
    ¬∃ t : target.EdgeColoring Color, target.IsTaitEdgeColoring t ∧
      Extends source keep base t := by
  rintro ⟨t,ht⟩
  exact no_source_choice ⟨fibreEquiv ⟨t,ht⟩⟩

def outerRing : Fin 10 → source.D :=
  ![(0,0),(1,1),(2,0),(1,2),(8,2),(1,0),(0,1),(10,2),(0,2),(19,2)]
def portRingIndex : Fin 8 → Fin 10 := ![1,2,3,4,6,7,8,9]
def boundaryOutside : Fin 8 → target.D :=
  ![((2,1),2),((6,2),1),((8,0),2),((9,0),1),
    ((10,0),2),((11,0),1),((19,0),2),((3,1),1)]

theorem outer_ring_injective : Function.Injective outerRing := by decide +kernel

theorem outer_ring_vertices (d : source.D) : keep d ↔ ∃ i, outerRing i = d := by
  revert d
  decide +kernel

theorem outer_ring_adjacent (i : Fin 10) :
    (rotationPrimalGraph target).Adj (outerRing i) (outerRing (i+1)) := by
  revert i
  change ∀ i : Fin 10, ∃ z : target.D,
    z.1 = outerRing i ∧ (target.alpha z).1 = outerRing (i+1)
  decide +kernel

/-- The patch is exactly the perimeter ten-cycle with its shared chord,
including both dart orientations of every internal edge. -/
theorem patch_internal_edges (z : target.D) :
    (keep z.1 ∧ keep (target.alpha z).1) ↔
      (∃ i : Fin 10,
        (z.1 = outerRing i ∧ (target.alpha z).1 = outerRing (i+1)) ∨
        (z.1 = outerRing (i+1) ∧ (target.alpha z).1 = outerRing i)) ∨
      (z.1 = outerRing 0 ∧ (target.alpha z).1 = outerRing 5) ∨
      (z.1 = outerRing 5 ∧ (target.alpha z).1 = outerRing 0) := by
  revert z
  decide +kernel

theorem ports_are_actual_cut (z : target.D) :
    (¬keep z.1 ∧ keep (target.alpha z).1) ↔ ∃ i, boundaryOutside i = z := by
  revert z
  decide +kernel

theorem boundary_injective : Function.Injective boundaryOutside := by decide +kernel

theorem ports_follow_ring (i : Fin 8) :
    (target.alpha (boundaryOutside i)).1 = outerRing (portRingIndex i) := by
  revert i
  decide +kernel

theorem boundary_colours :
    (fun i => base (target.edgeOf (boundaryOutside i))) =
      TwoCellBoundaryChoice.blockedWord blue red := by
  have h (d : source.D) (j : Fin 3) (hj : j ≠ 0) :
      base (target.edgeOf (d,j)) =
        if j = 1 then exteriorColour (source.vertOf (source.alpha d))
        else exteriorColour (source.vertOf d) := by
    fin_cases j
    · exact (hj rfl).elim
    · exact star_colour_one source exteriorColour d
    · exact star_colour_two source exteriorColour d
  have hz : ∀ i, (boundaryOutside i).2 ≠ 0 := by decide +kernel
  funext i
  change base (target.edgeOf ((boundaryOutside i).1,(boundaryOutside i).2)) = _
  rw [h _ _ (hz i)]
  clear h hz
  revert i
  decide +kernel

/-- The proposed literal cycle admits precisely this exterior's cut word. -/
theorem cycle_accepts_actual_boundary :
    (CycleCap.cap 8 (by decide)).AcceptsBoundaryWords Empty.elim
      (fun i => base (target.edgeOf (boundaryOutside i))) := by
  rw [boundary_colours]
  exact TwoCellBoundaryChoice.cycle_accepts blue red (by decide) (by decide) (by decide)

theorem target_vertices : Fintype.card source.D = 60 := by decide +kernel
theorem patch_vertices : (Finset.univ.filter keep).card = 10 := by decide +kernel
theorem exterior_vertices : (Finset.univ.filter (fun d => ¬keep d)).card = 50 := by
  decide +kernel

theorem nominal_vertex_loss :
    50 + Fintype.card (Fin 8) + 2 = Fintype.card source.D := by
  rw [target_vertices]
  decide +kernel

end
end Mettapedia.GraphTheory.FourColor.TwoCellCycleObstruction
