import Mettapedia.GraphTheory.FourColor.AdjacentPairFaceRegion
import Mettapedia.GraphTheory.FourColor.FaceColourTransfer

/-!
# Supplying the terminal facial path and matching cap

For any adjacent pair in a vertex-minimal Tait counterexample, select the
faces avoiding the pair and then add a face incident with their central edge.
This is an actual facial event. It introduces exactly three original edges
and leaves exactly two original edges missing. Thus the terminal geometry
used by the matching-cap extension test is supplied by the map itself.

This construction supplies uncoloured geometry. It does not assert that an
arbitrary colouring of the earlier region extends through the final cap.
-/

namespace Mettapedia.GraphTheory.FourColor.AdjacentPairFacialTail

open SimpleGraphDartRotation GoertzelV24FaceOrbitIncidence
open GoertzelV24FaceDualConnectedness GoertzelV24PrimalCycleFacialBond
open GoertzelV24TwoEdgeCutMinimality GoertzelV24AdjacentPairBoundary
open SphericalDistanceContours FaceRegionDegree FaceRegionShelling
open PhysicalForkCodeCut FaceRegionComplement

noncomputable section
attribute [local instance] Classical.propDecidable
set_option autoImplicit false

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]
variable (data : Data G) (minimal : GraphBackedVertexMinimalTaitCounterexample data)
variable (pair : AdjacentPairData G)

def centralDart : data.toRotationSystem.D :=
  ⟨(pair.firstVertex, pair.secondVertex), pair.centralAdjacent⟩

def face : OrbitFace data.toRotationSystem :=
  dartOrbitFace data.toRotationSystem (centralDart data pair)

theorem face_at_first : face data pair ∈ vertexFaces data pair.firstVertex :=
  ⟨centralDart data pair, rfl, rfl⟩

theorem face_at_second : face data pair ∈ vertexFaces data pair.secondVertex :=
  ⟨data.toRotationSystem.phi (centralDart data pair),
    data.toRotationSystem.vert_phi_eq_vert_alpha _, dartOrbitFace_phi_eq _ _⟩

local notation "S" => AdjacentPairFaceRegion.region data minimal pair

include minimal

theorem fresh : face data pair ∉ (S).faces := by
  intro h
  exact ((AdjacentPairFaceRegion.mem_faces data _ _ _).mp h).1 (face_at_first data pair)

private theorem next_vertex_retained :
    let a := data.toRotationSystem.phi (centralDart data pair)
    a.snd ≠ pair.firstVertex ∧ a.snd ≠ pair.secondVertex := by
  let d := centralDart data pair
  let a := data.toRotationSystem.phi d
  have haf : a.fst = pair.secondVertex := data.toRotationSystem.vert_phi_eq_vert_alpha d
  refine ⟨?_, ?_⟩
  · intro h
    have he : a = data.toRotationSystem.alpha d := by
      apply SimpleGraph.Dart.ext
      exact Prod.ext haf h
    apply minimal.facesTwoSided d
    exact (dartOrbitFace_phi_eq data.toRotationSystem d).symm.trans
      (congrArg (dartOrbitFace data.toRotationSystem) he)
  · intro h
    exact a.fst_ne_snd (haf.trans h.symm)

/-- A retained vertex on the new face gives an actual old adjacent face. -/
theorem attachment : ∃ f ∈ (S).faces, (orbitFaceDualGraph data).Adj (face data pair) f := by
  let a := data.toRotationSystem.phi (centralDart data pair)
  have hv := (AdjacentPairFaceRegion.touched_iff_retained data minimal pair a.snd).mpr
    (next_vertex_retained data minimal pair)
  obtain ⟨d, hd, hf⟩ := (touched_iff _ _ _).mp hv
  have hc : face data pair ∈ vertexFaces data a.snd :=
    ⟨data.toRotationSystem.phi a, data.toRotationSystem.vert_phi_eq_vert_alpha a,
      (dartOrbitFace_phi_eq _ a).trans (dartOrbitFace_phi_eq _ (centralDart data pair))⟩
  refine ⟨dartOrbitFace data.toRotationSystem d, hf, ?_⟩
  rcases vertexFaces_clique data minimal.spherical.cubic minimal.vertexRotationCyclic
    minimal.facesTwoSided a.snd (face data pair) (dartOrbitFace data.toRotationSystem d)
    hc ⟨d, hd, rfl⟩ with h | h
  · exact (fresh data minimal pair (h.symm ▸ hf)).elim
  · exact h

private theorem outside_after :
    ((orbitFaceDualGraph data).induce (insert (face data pair) ((S).faces : Set _))ᶜ).Connected := by
  let d := centralDart data pair
  let b := dartOrbitFace data.toRotationSystem (data.toRotationSystem.alpha d)
  have hbv : b ∈ vertexFaces data pair.firstVertex :=
    ⟨data.toRotationSystem.rho d, data.toRotationSystem.vert_rho d,
      (dartOrbitFace_alpha_eq_dartOrbitFace_rho _ d).symm⟩
  have hbw : b ∈ vertexFaces data pair.secondVertex := ⟨data.toRotationSystem.alpha d, rfl, rfl⟩
  have hbc : b ≠ face data pair := (minimal.facesTwoSided d).symm
  have pre (v : V) : ((orbitFaceDualGraph data).induce
      (vertexFaces data v \ {face data pair})).Preconnected := by
    intro f g
    rcases vertexFaces_clique data minimal.spherical.cubic minimal.vertexRotationCyclic
      minimal.facesTwoSided v f.val g.val f.property.1 g.property.1 with h | h
    · exact Subtype.ext h ▸ SimpleGraph.Reachable.refl f
    · exact SimpleGraph.Adj.reachable h
  have heq : (insert (face data pair) ((S).faces : Set _))ᶜ =
      (vertexFaces data pair.firstVertex \ {face data pair}) ∪
      (vertexFaces data pair.secondVertex \ {face data pair}) := by
    ext f
    simp only [Set.mem_compl_iff, Set.mem_insert_iff, Finset.mem_coe,
      AdjacentPairFaceRegion.region, AdjacentPairFaceRegion.mem_faces,
      Set.mem_union, Set.mem_sdiff, Set.mem_singleton_iff]
    tauto
  rw [heq]
  exact SimpleGraph.induce_union_connected (pre _) (pre _) ⟨b, ⟨hbv, hbc⟩, ⟨hbw, hbc⟩⟩

/-- The new face leaves both literal facial shores connected. -/
def after : Region data where
  faces := insert (face data pair) (S).faces
  inside := by
    obtain ⟨f, hf, hadj⟩ := attachment data minimal pair
    rw [Finset.coe_insert]
    exact ConnectedBipartitionGrowth.connected_insert_of_adj _ (S).inside hf hadj
  outside := by
    rw [Finset.coe_insert]
    exact outside_after data minimal pair

/-- A genuine one-face operation in the facial GSLT. -/
def event : Event S (after data minimal pair) where
  face := face data pair
  fresh := fresh data minimal pair
  target := rfl
  attachment := attachment data minimal pair

theorem touched_after :
    touched data.toRotationSystem (edges data.toRotationSystem (after data minimal pair).faces) =
      Finset.univ := by
  apply Finset.eq_univ_of_forall
  intro v
  apply (touched_iff _ _ _).mpr
  by_cases hv : v = pair.firstVertex
  · subst v
    obtain ⟨d, hd, hf⟩ := face_at_first data pair
    exact ⟨d, hd, Finset.mem_insert.mpr (Or.inl hf)⟩
  by_cases hw : v = pair.secondVertex
  · subst v
    obtain ⟨d, hd, hf⟩ := face_at_second data pair
    exact ⟨d, hd, Finset.mem_insert.mpr (Or.inl hf)⟩
  have hold := (AdjacentPairFaceRegion.touched_iff_retained data minimal pair v).mpr ⟨hv, hw⟩
  obtain ⟨d, hd, hf⟩ := (touched_iff _ _ _).mp hold
  exact ⟨d, hd, Finset.mem_insert.mpr (Or.inr hf)⟩

theorem touched_before_card :
    (touched data.toRotationSystem (edges data.toRotationSystem (S).faces)).card + 2 =
      Fintype.card V := by
  have ht : touched data.toRotationSystem (edges data.toRotationSystem (S).faces) =
      Finset.univ \ {pair.firstVertex, pair.secondVertex} := by
    ext v
    simpa only [AdjacentPairFaceRegion.region, Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton, not_or] using AdjacentPairFaceRegion.touched_iff_retained data minimal pair v
  rw [ht]
  have hc := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ
    ({pair.firstVertex, pair.secondVertex} : Finset V))
  simpa only [Finset.card_pair pair.centralAdjacent.ne, Finset.card_univ] using hc

/-- The disk Euler laws force exactly three newly exposed original edges. -/
theorem exposed_card : (exposedEdges data (event data minimal pair)).card = 3 := by
  have hs := FaceAttachmentCount.region_euler data minimal.toBridgelessSphericalCubicMapData S
  have hr := FaceAttachmentCount.region_euler data minimal.toBridgelessSphericalCubicMapData
    (after data minimal pair)
  rw [touched_after data minimal pair, Finset.card_univ] at hr
  have hv := touched_before_card data minimal pair
  have hf := (event data minimal pair).card
  have he : (edges data.toRotationSystem (after data minimal pair).faces).card =
      (edges data.toRotationSystem (S).faces).card + (exposedEdges data (event data minimal pair)).card := by
    rw [FaceColourTransfer.shores_union data (event data minimal pair)]
    exact Finset.card_union_of_disjoint (FaceColourTransfer.shores_disjoint data (event data minimal pair))
  omega

/-- The terminal cap contains exactly two original edges. -/
theorem missing_card :
    (Finset.univ \ edges data.toRotationSystem (after data minimal pair).faces).card = 2 := by
  have hs := AdjacentPairFaceRegion.missing_edges_card data minimal pair
  have hsumS := Finset.card_sdiff_add_card_eq_card
    (Finset.subset_univ (edges data.toRotationSystem (S).faces))
  have hsumR := Finset.card_sdiff_add_card_eq_card
    (Finset.subset_univ (edges data.toRotationSystem (after data minimal pair).faces))
  have he : (edges data.toRotationSystem (after data minimal pair).faces).card =
      (edges data.toRotationSystem (S).faces).card + 3 := by
    rw [FaceColourTransfer.shores_union data (event data minimal pair),
      Finset.card_union_of_disjoint (FaceColourTransfer.shores_disjoint data (event data minimal pair)),
      exposed_card data minimal pair]
  omega

open Mettapedia.GSLT.Ultrainfinite

/-- The earlier facial region is reached from a single original face by
actual face additions; no partial sweep is supplied as an assumption. -/
theorem exists_initial_route :
    ∃ root : OrbitFace data.toRotationSystem,
      Nonempty (Route Event
        (FaceRegionSweep.single data minimal.toBridgelessSphericalCubicMapData root) S) := by
  obtain ⟨root, hroot⟩ := (S).nonempty
  refine ⟨root, exists_route data minimal.toBridgelessSphericalCubicMapData _ S ?_⟩
  exact Finset.singleton_subset_iff.mpr hroot

omit pair in
/-- Any directed original edge in a minimal counterexample supplies the
entire uncoloured prefix and the terminal three-edge event, leaving two
edges for the matching-cap extension test. -/
theorem exists_construction {first second : V} (hadj : G.Adj first second) :
    ∃ (P R : Region data) (e : Event P R) (root : OrbitFace data.toRotationSystem),
      Nonempty (Route Event
        (FaceRegionSweep.single data minimal.toBridgelessSphericalCubicMapData root) P) ∧
      (exposedEdges data e).card = 3 ∧
      (Finset.univ \ edges data.toRotationSystem R.faces).card = 2 ∧
      ∀ x : G.edgeSet, x ∈ edges data.toRotationSystem P.faces ↔
        first ∉ x.val ∧ second ∉ x.val := by
  let pair := GoertzelV24RecoveredAdjacentPairData.adjacentPairData data hadj
    minimal.spherical.cubic minimal.vertexRotationCyclic
    (GoertzelV24MinimalTriangleFree.no_common_neighbor_of_vertexMinimalTaitCounterexample
      data minimal hadj)
  obtain ⟨root, hroute⟩ := exists_initial_route data minimal pair
  exact ⟨AdjacentPairFaceRegion.region data minimal pair, after data minimal pair,
    event data minimal pair, root, hroute, exposed_card data minimal pair,
    missing_card data minimal pair, AdjacentPairFaceRegion.retained_edge_iff data minimal hadj⟩

end
end Mettapedia.GraphTheory.FourColor.AdjacentPairFacialTail
