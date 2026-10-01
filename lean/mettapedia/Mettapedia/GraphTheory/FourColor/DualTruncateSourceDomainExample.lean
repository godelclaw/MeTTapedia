import Mettapedia.GraphTheory.FourColor.DualTruncateInverseRoundTrip
import Mettapedia.GraphTheory.FourColor.CubicRotationByteCertificate
import Mettapedia.GraphTheory.FourColor.CyclicEdgeCutIso

/-!
# A recovered source outside the cyclic-four supplier

The triangular prism is a connected spherical cubic source with a cyclic
three-edge cut. Its eighteen-vertex target is recognized using actual
nonhexagonal faces. Coupled source choices, rather than a source colour word
or a cyclic-four assumption, colour the recovered source and target and
supply every complete GSLT sweep.

This example concerns the broad face-cover class. Its triangles and squares
exclude it from the pentagonal/hexagonal and cyclic-five normal-form domains.
-/

namespace Mettapedia.GraphTheory.FourColor.DualTruncateSourceDomainExample

open _root_.SimpleGraph CubicRotationByteCertificate DualTruncateColoring
open DualTruncateStructuralColoring DualTruncateInverse
open GoertzelV24FaceOrbitIncidence GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitPartitionBridge GoertzelV24OrbitFaceCurvatureBulk
open GoertzelV24CubicSmallBoundaryCycle GoertzelV24OrbitFaceTwoSided
open GoertzelV24TwoEdgeCutMinimality
open TubeSlab.VertexTransfer VertexCodeSourceGeometry SourceVertexCodeTrace
open VertexConstructionGSLT

noncomputable section

/-- Cyclic neighbour order for the embedded triangular prism. -/
def code : CubicRotationByteCertificate.Code 6 9 where
  neighbours := { size := 18, pages := fun _ => ByteArray.mk #[
    1,0,3,0,2,0,2,0,4,0,0,0,0,0,5,0,1,0,5,0,0,0,4,0,3,0,1,0,5,0,4,0,2,0,3,0] }
  mates := { size := 18, pages := fun _ => ByteArray.mk #[
    5,0,10,0,6,0,8,0,13,0,0,0,2,0,16,0,3,0,17,0,1,0,12,0,11,0,4,0,15,0,14,0,7,0,9,0] }
  edges := { size := 18, pages := fun _ => ByteArray.mk #[
    0,0,1,0,2,0,3,0,4,0,0,0,2,0,5,0,3,0,6,0,1,0,7,0,7,0,4,0,8,0,8,0,5,0,6,0] }
  representatives := { size := 9, pages := fun _ => ByteArray.mk #[
    0,0,1,0,2,0,3,0,4,0,7,0,9,0,11,0,14,0] }

theorem valid : code.Valid := by decide +kernel
abbrev original : RotationSystem.{0,0,0} (Fin 6) (Fin 9) := code.rotation valid
abbrev graph := rotationPrimalGraph original

instance : DecidableRel graph.Adj := fun v w =>
  inferInstanceAs (Decidable (∃ d : Position 6, d.1 = v ∧ (code.mate d).1 = w))

theorem source_cubic : original.IsCubic := code.cubic valid

theorem source_rotationCyclic : VertexRotationCyclic original := by
  rintro ⟨v, i⟩ ⟨w, j⟩ h
  change v = w at h
  subst w
  have h01 : original.rho.SameCycle (v, 0) (v, 1) :=
    ⟨1, by simp [CubicRotationByteCertificate.Code.rho]⟩
  have h12 : original.rho.SameCycle (v, 1) (v, 2) :=
    ⟨1, by simp [CubicRotationByteCertificate.Code.rho]⟩
  have h02 := h01.trans h12
  fin_cases i <;> fin_cases j <;>
    first
    | exact Equiv.Perm.SameCycle.refl _ _
    | exact h01
    | exact h12
    | exact h02
    | exact h01.symm
    | exact h12.symm
    | exact h02.symm

abbrev retained := graph.induce {v | v ≠ (1 : Fin 6) ∧ v ≠ (3 : Fin 6)}
def root : CoupledThreeColouring.Retained (1 : Fin 6) 3 := ⟨0, by decide, by decide⟩
def two : CoupledThreeColouring.Retained (1 : Fin 6) 3 := ⟨2, by decide, by decide⟩
def four : CoupledThreeColouring.Retained (1 : Fin 6) 3 := ⟨4, by decide, by decide⟩
def five : CoupledThreeColouring.Retained (1 : Fin 6) 3 := ⟨5, by decide, by decide⟩

theorem retained_reachable (v : CoupledThreeColouring.Retained (1 : Fin 6) 3) :
    retained.Reachable root v := by
  have h02 : retained.Adj root two := by decide +kernel
  have h25 : retained.Adj two five := by decide +kernel
  have h54 : retained.Adj five four := by decide +kernel
  rcases v with ⟨v, hv⟩
  fin_cases v
  · exact .refl _
  · exact (hv.1 rfl).elim
  · exact h02.reachable
  · exact (hv.2 rfl).elim
  · exact h02.reachable.trans (h25.reachable.trans h54.reachable)
  · exact h02.reachable.trans h25.reachable

theorem retained_connected : retained.Connected :=
  { preconnected := fun u v => (retained_reachable u).symm.trans (retained_reachable v)
    nonempty := ⟨root⟩ }

theorem pair_nonadjacent : ¬graph.Adj 1 3 := by decide +kernel
theorem root_adj_one : graph.Adj 0 1 := by decide +kernel
theorem root_adj_three : graph.Adj 0 3 := by decide +kernel

theorem source_connected : graph.Connected := by
  have reach (v : Fin 6) : graph.Reachable 0 v := by
    by_cases h1 : v = 1
    · subst v; exact root_adj_one.reachable
    by_cases h3 : v = 3
    · subst v; exact root_adj_three.reachable
    exact (retained_reachable ⟨v, h1, h3⟩).map
      (SimpleGraph.Embedding.induce (G := graph) {v | v ≠ 1 ∧ v ≠ 3}).toHom
  exact { preconnected := fun u v => (reach u).symm.trans (reach v) }

theorem source_face_count : Fintype.card (OrbitFace original) = 5 := by
  change Fintype.card (Quotient (Equiv.Perm.SameCycle.setoid original.phi)) = 5
  rw [card_permOrbit_eq_card_partition_parts]
  decide +kernel

theorem source_spherical : OrbitSphericalCubicMapData original where
  cubic := source_cubic
  euler := by rw [source_face_count]; decide +kernel

theorem source_face_length (x : original.D) :
    (original.faceOrbit x).card = 3 ∨ (original.faceOrbit x).card = 4 := by
  fin_cases x <;> decide +kernel

def side (v : Fin 6) : Prop := v.val < 3

instance : DecidablePred side := fun v => inferInstanceAs (Decidable (v.val < 3))

def topCycle : graph.Walk (0 : Fin 6) 0 :=
  .cons (by decide +kernel : graph.Adj 0 1)
    (.cons (by decide +kernel : graph.Adj 1 2)
      (.cons (by decide +kernel : graph.Adj 2 0) .nil))

def bottomCycle : graph.Walk (3 : Fin 6) 3 :=
  .cons (by decide +kernel : graph.Adj 3 4)
    (.cons (by decide +kernel : graph.Adj 4 5)
      (.cons (by decide +kernel : graph.Adj 5 3) .nil))

theorem top_cycle : HasCycleOnSide graph side := by
  refine ⟨0, by decide, topCycle, ?_, ?_⟩
  · simp [topCycle, Walk.cons_isCycle_iff, Walk.cons_isPath_iff]
  · intro v hv
    simp only [topCycle, Walk.support_cons, Walk.support_nil, List.mem_cons,
      List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl | rfl <;> decide

theorem bottom_cycle : HasCycleOnSide graph (fun v => ¬side v) := by
  refine ⟨3, by decide, bottomCycle, ?_, ?_⟩
  · simp [bottomCycle, Walk.cons_isCycle_iff, Walk.cons_isPath_iff]
  · intro v hv
    simp only [bottomCycle, Walk.support_cons, Walk.support_nil, List.mem_cons,
      List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl | rfl <;> decide

def boundaryPairs : Finset (Fin 6 × Fin 6) :=
  Finset.univ.filter (fun p => graph.Adj p.1 p.2 ∧ side p.1 ∧ ¬side p.2)

theorem boundaryPairs_card : boundaryPairs.card =
    Fintype.card (CrossingSideDart graph side) := by
  let equiv : CrossingSideDart graph side ≃ {p : Fin 6 × Fin 6 // p ∈ boundaryPairs} :=
    { toFun := fun d => ⟨d.1.toProd, by simp [boundaryPairs, d.1.adj, d.2]⟩
      invFun := fun p =>
        let hp := (Finset.mem_filter.mp p.2).2
        ⟨⟨p.1, hp.1⟩, hp.2⟩
      left_inv := fun d => by apply Subtype.ext; rfl
      right_inv := fun p => rfl }
  have h := Fintype.card_congr equiv
  rw [Fintype.card_coe] at h
  exact h.symm

theorem crossing_count : (crossingEdgeFinset graph side).card = 3 := by
  rw [card_crossingEdgeFinset_eq_card_crossingSideDart, ← boundaryPairs_card]
  decide +kernel

def cyclicThreeCut : SmallCyclicEdgeCut graph where
  edgeCut := crossingEdgeFinset graph side
  side := side
  hcut_eq := mem_crossingEdgeFinset_iff side
  hcard_le_four := by rw [crossing_count]; omega
  hinside_cycle := top_cycle
  houtside_cycle := bottom_cycle

theorem source_not_cyclic_four : ¬CyclicEdgeConnectivityAtLeast graph 4 := by
  intro h
  have bound := h cyclicThreeCut
  change 4 ≤ (crossingEdgeFinset graph side).card at bound
  rw [crossing_count] at bound
  omega

attribute [local instance] Classical.propDecidable Classical.decEq

abbrev target := rotation original

theorem target_mapClass : BridgelessSphericalCubicMapData target :=
  DualTruncateMapGeometry.mapClass_of original source_spherical source_connected source_rotationCyclic

/-- Actual face lengths select the cover, without a saved source-face tag. -/
def nonhexMarked (face : OrbitFace target) : Prop :=
  (orbitFaceDarts target face).card ≠ 6

theorem nonhex_marked_iff (x : target.D) :
    nonhexMarked (dartOrbitFace target x) ↔ x.2 = 2 := by
  rcases x with ⟨v, i⟩
  simp only [nonhexMarked, orbitFaceDarts_dartOrbitFace_eq_faceOrbit]
  fin_cases i
  · change (target.faceOrbit (v, 0)).card ≠ 6 ↔ (0 : Fin 3) = 2
    rw [DualTruncateFaceGeometry.vertex_face_length original source_cubic source_rotationCyclic]
    decide
  · change (target.faceOrbit (v, 1)).card ≠ 6 ↔ (1 : Fin 3) = 2
    rw [DualTruncateFaceGeometry.vertex_face_length_one original source_cubic source_rotationCyclic]
    decide
  · change (target.faceOrbit (v, 2)).card ≠ 6 ↔ (2 : Fin 3) = 2
    rw [DualTruncateFaceGeometry.faceOrbit_two_card original source_rotationCyclic]
    rcases source_face_length v with h | h <;> rw [h] <;> decide

def cover : DualTruncateFaceCoverFrame.Cover target where
  marked := nonhexMarked
  unique v := by
    refine ⟨(v, 2), ⟨rfl, (nonhex_marked_iff _).mpr rfl⟩, ?_⟩
    rintro ⟨w, i⟩ ⟨hv, hm⟩
    change w = v at hv
    exact Prod.ext hv ((nonhex_marked_iff _).mp hm)

theorem cover_eq : cover = DualTruncateInverseRoundTrip.cover original
    source_cubic source_rotationCyclic := by
  have hm : nonhexMarked = DualTruncateInverseRoundTrip.marked original
      source_cubic source_rotationCyclic := by
    funext face
    obtain ⟨x, rfl⟩ := exists_dartOrbitFace_eq target face
    exact propext ((nonhex_marked_iff x).trans
      (DualTruncateInverseRoundTrip.marked_iff original source_cubic source_rotationCyclic x).symm)
  unfold cover DualTruncateInverseRoundTrip.cover
  simp only [hm]

def data : Data target := DualTruncateInverse.fromCover target (cubic original)
  (DualTruncateConstructionGSLT.rotationCyclic original) cover

theorem data_eq : data = DualTruncateInverseRoundTrip.data original
    source_cubic source_rotationCyclic := by
  unfold data
  rw [cover_eq]
  exact DualTruncateInverseRoundTrip.fromCover_data original source_cubic source_rotationCyclic

abbrev recovered := DualTruncateInverse.source target data
  (DualTruncateFaceGeometry.facesTwoSided original)

theorem unmarked_hexagons (x : target.D)
    (hm : ¬data.marked (dartOrbitFace target x)) : (target.faceOrbit x).card = 6 := by
  rw [data_eq] at hm
  exact DualTruncateInverseRoundTrip.unmarked_hexagons original
    source_cubic source_rotationCyclic x hm

def recovered_primalIso : rotationPrimalGraph recovered ≃g graph := by
  unfold recovered
  rw [data_eq]
  exact DualTruncateInverseRoundTrip.primalIso original source_cubic source_rotationCyclic

/-- The cyclic-three obstruction belongs to the source which target-only
recognition constructed, not just to its original labels. -/
theorem recovered_not_cyclic_four :
    ¬CyclicEdgeConnectivityAtLeast (rotationPrimalGraph recovered) 4 := by
  intro h
  exact source_not_cyclic_four
    ((CyclicEdgeCutIso.cyclic_connectivity recovered_primalIso 4).mp h)

theorem recovered_vertex_count : Fintype.card (SourceVertex target data) = 6 := by
  have hs := DualTruncateInverseGeometry.source_size target data
    (DualTruncateFaceGeometry.facesTwoSided original) unmarked_hexagons
  have ht : Fintype.card original.D = 18 := by decide +kernel
  omega

theorem source_shared_colouring :
    ∃ c : ThreeVertexColoring original, c.colour 1 = c.colour 3 :=
  source_of_connected_pair original source_cubic (by decide) pair_nonadjacent
    root_adj_one root_adj_three retained_connected

theorem recovered_colouring : Nonempty (ThreeVertexColoring recovered) := by
  obtain ⟨c, _⟩ := source_shared_colouring
  unfold recovered
  rw [data_eq]
  exact ⟨DualTruncateInverseRoundTrip.colouring original source_cubic source_rotationCyclic c⟩

theorem recognized_coloured_target :
    OrbitSphericalCubicMapData recovered ∧
      (rotationPrimalGraph recovered).Connected ∧
      Fintype.card (SourceVertex target data) < Fintype.card original.D ∧
      RotationSystemTaitColorable target := by
  obtain ⟨c⟩ := recovered_colouring
  exact ⟨DualTruncateInverseGeometry.source_spherical target data
      (DualTruncateFaceGeometry.facesTwoSided original) unmarked_hexagons target_mapClass.spherical,
    DualTruncateInverseGeometry.source_connected target data
      (DualTruncateFaceGeometry.facesTwoSided original) target_mapClass.primalConnected,
    DualTruncateInverseGeometry.source_strictly_smaller target data
      (DualTruncateFaceGeometry.facesTwoSided original) unmarked_hexagons,
    DualTruncateInverseGeometry.tait target data (DualTruncateFaceGeometry.facesTwoSided original) c⟩

/-- Recognition, recovered spherical geometry and successful reconstruction
coexist with a source cyclic-three cut. Thus the broad face-cover hypotheses
cannot justify the stronger cyclic-four supplier. -/
theorem source_domain_obstruction :
    BridgelessSphericalCubicMapData target ∧
      OrbitSphericalCubicMapData recovered ∧
      (rotationPrimalGraph recovered).Connected ∧
      Fintype.card (SourceVertex target data) = 6 ∧
      ¬CyclicEdgeConnectivityAtLeast (rotationPrimalGraph recovered) 4 ∧
      RotationSystemTaitColorable target := by
  obtain ⟨hs, hc, _, ht⟩ := recognized_coloured_target
  exact ⟨target_mapClass, hs, hc, recovered_vertex_count, recovered_not_cyclic_four, ht⟩

theorem every_complete_sweep (order : List original.D) (hn : order.Nodup)
    (he : order ≠ []) (hcover : ∀ d, visited order d) :
    VertexConstructionGSLT.colouring.Supports
      (route (encodeClosed (cubic original)
        (DualTruncateConstructionGSLT.rotationCyclic original) order hn he hcover).trace)
      Fin.elim0 Fin.elim0 := by
  obtain ⟨c⟩ := recovered_colouring
  exact DualTruncateInverseGeometry.every_complete_sweep target data
    (DualTruncateFaceGeometry.facesTwoSided original) c order hn he hcover

end
end Mettapedia.GraphTheory.FourColor.DualTruncateSourceDomainExample
