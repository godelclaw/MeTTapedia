import Mettapedia.GraphTheory.FourColor.FaceMatchingCapDeletion
import Mettapedia.GraphTheory.FourColor.GoertzelV24ForkTaitBridge

/-!
# Colouring transport for a final three-edge path and matching cap

The old facial assignment is transported to the existing adjacent-pair
deletion using the actual edge inclusion and the three nonzero Klein-four
colours. Its established bridge criterion then reconstructs a colouring
of the whole ambient graph, preserving every old edge colour.

This identifies the joint-choice problem with adjacent-pair restoration.
It does not assert that an arbitrary old assignment satisfies the criterion.
-/

namespace Mettapedia.GraphTheory.FourColor.FaceMatchingCapColouring

open SimpleGraphDartRotation GoertzelV24RotationVertexCutProfile
open GoertzelV24SimpleGraphTaitBridge GoertzelV24FaceOrbitIncidence
open GoertzelV24TwoEdgeCutMinimality FaceRegionShelling FaceMatchingCapDeletion
open FaceRegionDegree
open PhysicalForkCodeCut PhysicalForkCodeFaces EdgeShoreRotation PermutationSingleExitArc FaceExposedBoundary
open GoertzelV24AdjacentPairBoundary GoertzelV24AdjacentPairInsertion.AdjacentPairData
open GoertzelV24FourDefectBoundary GoertzelV24DeletedEdgeTrail
open GoertzelV24ForkInterfaceSupport GoertzelV24TaitMatchingDecomposition
open GoertzelV24ForkTaitBridge GoertzelV24RouteNativeInterfaceReflection

private theorem third_nonzero_unique : ∀ a b q r : Color,
    a ≠ 0 → b ≠ 0 → a ≠ b → q ≠ 0 → r ≠ 0 →
      q ≠ a → q ≠ b → r ≠ a → r ≠ b → q = r := by
  intro a b q r ha hb hab hq hr hqa hqb hra hrb
  rcases eq_red_or_eq_blue_or_eq_purple_of_ne_zero a ha with rfl | rfl | rfl <;>
    rcases eq_red_or_eq_blue_or_eq_purple_of_ne_zero b hb with rfl | rfl | rfl <;>
    rcases eq_red_or_eq_blue_or_eq_purple_of_ne_zero q hq with rfl | rfl | rfl <;>
    rcases eq_red_or_eq_blue_or_eq_purple_of_ne_zero r hr with rfl | rfl | rfl <;> simp_all

noncomputable section
attribute [local instance] Classical.propDecidable
set_option autoImplicit false
set_option maxHeartbeats 1000000

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

local instance (first second : V) : Fintype (retainedVertexSet first second) :=
  Subtype.fintype _

variable (data : Data G) {S R : Region data} (e : Event S R)
variable (ambient : BridgelessSphericalCubicMapData data.toRotationSystem)
variable (outer : Dart data.toRotationSystem (edges data.toRotationSystem R.faces))
variable (ho : dartOrbitFace data.toRotationSystem outer.val ∉ R.faces)
variable (b : Arc (toMap data.toRotationSystem (edges data.toRotationSystem R.faces) outer).phi
  (exposedDarts data e outer))
variable (hlen : b.length = 3)
variable (hcap : (Finset.univ \ edges data.toRotationSystem R.faces).card = 2)

local notation "pair" => adjacentPair data e ambient outer ho b hlen hcap
local notation "Old" => edges data.toRotationSystem S.faces
local notation "Deleted" => DeletedAdjacentPairGraph G
  (GoertzelV24AdjacentPairBoundary.AdjacentPairData.firstVertex pair)
  (GoertzelV24AdjacentPairBoundary.AdjacentPairData.secondVertex pair)

/-- Inclusion of an induced-deletion edge lands in the exact old facial edge set. -/
theorem included_edge_mem (x : (Deleted).edgeSet) : retainedEdgeToAmbientEdge pair x ∈ Old := by
  apply (retained_iff_avoids_internal data e ambient outer ho b hlen hcap _).mpr
  simp only [mem_simpleGraphRotationSystem_endpoints_iff]
  constructor
  · intro h
    obtain ⟨v, _, hv⟩ := Sym2.mem_map.mp h
    exact v.property.1 hv
  · intro h
    obtain ⟨v, _, hv⟩ := Sym2.mem_map.mp h
    exact v.property.2 hv

/-- The colour function keeps the literal ambient edge identifier before
changing only the palette representation. -/
def deletedColouring (a : G.edgeSet → Fin 3) (ha : Proper data.toRotationSystem.endpoints Old a) :
    (Deleted).EdgeColoring Color :=
  SimpleGraph.Coloring.mk (fun x => taitColor (a (retainedEdgeToAmbientEdge pair x))) (by
    intro x y hxy
    obtain ⟨hne, v, hvx, hvy⟩ := SimpleGraph.lineGraph_adj_iff_exists.mp hxy
    apply taitColor_injective.ne
    apply ha _ (included_edge_mem data e ambient outer ho b hlen hcap x)
      _ (included_edge_mem data e ambient outer ho b hlen hcap y)
    · exact (SimpleGraph.Hom.mapEdgeSet.injective (retainedGraphEmbedding pair).toHom
        (retainedGraphEmbedding pair).injective).ne hne
    · refine ⟨v.val, Finset.mem_inter.mpr ⟨?_, ?_⟩⟩
      · apply (mem_simpleGraphRotationSystem_endpoints_iff data _ _).mpr
        exact Sym2.mem_map.mpr ⟨v, hvx, rfl⟩
      · apply (mem_simpleGraphRotationSystem_endpoints_iff data _ _).mpr
        exact Sym2.mem_map.mpr ⟨v, hvy, rfl⟩)

theorem deletedColouring_tait (a : G.edgeSet → Fin 3)
    (ha : Proper data.toRotationSystem.endpoints Old a) :
    IsTaitEdgeColoring Deleted (deletedColouring data e ambient outer ho b hlen hcap a ha) := by
  intro x
  exact taitColor_ne_zero _

/-- The established four-port boundary word of the actual facial assignment. -/
def requests (a : G.edgeSet → Fin 3) (ha : Proper data.toRotationSystem.endpoints Old a) : Fin 4 → Color :=
  (pair).degreeTwoBoundaryData.colorWord (deletedColouring data e ambient outer ho b hlen hcap a ha)

/-- No new four-contact criterion is assumed: the existing adjacent-pair
theorem applies to the transported original assignment. -/
theorem bridge_exists_iff (a : G.edgeSet → Fin 3)
    (ha : Proper data.toRotationSystem.endpoints Old a) :
    (∃ bridge : Color, IsTwoVertexBridgeExtension
      (requests data e ambient outer ho b hlen hcap a ha) bridge) ↔
      ¬ (requests data e ambient outer ho b hlen hcap a ha 0 =
          requests data e ambient outer ho b hlen hcap a ha 1 ∧
        requests data e ambient outer ho b hlen hcap a ha 2 =
          requests data e ambient outer ho b hlen hcap a ha 3) := by
  have h := (pair).deletedAdjacentPair_not_exists_bridgeExtension_iff
    (incidentEdgeFinset_card_eq_three_of_toRotationSystem_isCubic data ambient.spherical.cubic)
    (deletedColouring data e ambient outer ho b hlen hcap a ha)
    (deletedColouring_tait data e ambient outer ho b hlen hcap a ha)
  simpa only [requests, not_not] using not_congr h

/-- An accepted four-port word reconstructs the full graph and preserves
the given colours of all old facial edges. -/
theorem reconstruct (a : G.edgeSet → Fin 3)
    (ha : Proper data.toRotationSystem.endpoints Old a)
    (hrequests : ¬ (requests data e ambient outer ho b hlen hcap a ha 0 =
          requests data e ambient outer ho b hlen hcap a ha 1 ∧
        requests data e ambient outer ho b hlen hcap a ha 2 =
          requests data e ambient outer ho b hlen hcap a ha 3)) :
    ∃ d : G.edgeSet → Fin 3, Proper data.toRotationSystem.endpoints Finset.univ d ∧
      ∀ x ∈ Old, d x = a x := by
  obtain ⟨bridge, hbridge⟩ := (bridge_exists_iff data e ambient outer ho b hlen hcap a ha).mpr hrequests
  let C := deletedColouring data e ambient outer ho b hlen hcap a ha
  have hC := deletedColouring_tait data e ambient outer ho b hlen hcap a ha
  have hbridge' : IsTwoVertexBridgeExtension ((pair).degreeTwoBoundaryData.colorWord C) bridge := by
    simpa only [requests, C] using hbridge
  have hboundary := (pair).degreeTwoBoundaryData_wellFormed
    (incidentEdgeFinset_card_eq_three_of_toRotationSystem_isCubic data ambient.spherical.cubic)
  let D := insertAdjacentPairColoring pair hboundary C hC bridge hbridge'
  have hD := isTaitEdgeColoring_insertAdjacentPairColoring pair hboundary C hC bridge hbridge'
  have hpiece : IsPieceColoring data.toRotationSystem Finset.univ D := by
    refine ⟨fun x _ => hD x, ?_⟩
    intro x _ y _ hxy
    apply D.valid
    rwa [toRotationSystem_edgeAdjacencyGraph_eq_lineGraph data] at hxy
  obtain ⟨d, hd, heq⟩ := exists_fin3_of_pieceColoring data.toRotationSystem Finset.univ D hpiece
  refine ⟨d, hd, ?_⟩
  intro x hx
  apply taitColor_injective
  rw [heq x (Finset.mem_univ x)]
  have hret := (retained_iff_adjacentPair data e ambient outer ho b hlen hcap x).mp hx
  change insertAdjacentPairColoring pair hboundary C hC bridge hbridge' x = taitColor (a x)
  rw [insertAdjacentPairColoring_retained pair hboundary C hC bridge hbridge' x hret]
  change taitColor (a (retainedEdgeToAmbientEdge pair (ambientEdgeToRetainedEdge pair x hret))) = _
  rw [retainedEdgeToAmbientEdge_ambientEdgeToRetainedEdge]

/-- In every extension, each restored boundary edge carries exactly the
old port's requested colour. -/
theorem request_eq_extension_boundary (a : G.edgeSet → Fin 3)
    (ha : Proper data.toRotationSystem.endpoints Old a)
    (d : G.edgeSet → Fin 3) (hd : Proper data.toRotationSystem.endpoints Finset.univ d)
    (hagrees : ∀ x ∈ Old, d x = a x) (port : Fin 4) :
    requests data e ambient outer ho b hlen hcap a ha port =
      taitColor (d (boundaryEdge pair port)) := by
  let C := deletedColouring data e ambient outer ho b hlen hcap a ha
  have hC := deletedColouring_tait data e ambient outer ho b hlen hcap a ha
  have hboundary := (pair).degreeTwoBoundaryData_wellFormed
    (incidentEdgeFinset_card_eq_three_of_toRotationSystem_isCubic data ambient.spherical.cubic)
  have hnot : boundaryEdge pair port ∉ Old := by
    intro hx
    exact (not_isRetainedAmbientEdge_iff pair _).mpr (Or.inr ⟨port, rfl⟩)
      ((retained_iff_adjacentPair data e ambient outer ho b hlen hcap _).mp hx)
  have avoid (x : (Deleted).edgeSet)
      (hx : x ∈ incidentEdgeFinset Deleted ((pair).retainedPort port)) :
      taitColor (d (boundaryEdge pair port)) ≠ C x := by
    have hxOld := included_edge_mem data e ambient outer ho b hlen hcap x
    have hne : boundaryEdge pair port ≠ retainedEdgeToAmbientEdge pair x :=
      fun h => hnot (h ▸ hxOld)
    have hmem : (pair).retainedPort port ∈ x.val := by
      simpa only [incidentEdgeFinset, Finset.mem_filter, Finset.mem_univ, true_and] using hx
    change taitColor (d (boundaryEdge pair port)) ≠ taitColor (a (retainedEdgeToAmbientEdge pair x))
    rw [← hagrees _ hxOld]
    apply taitColor_injective.ne
    apply hd _ (Finset.mem_univ _) _ (Finset.mem_univ _) hne
    refine ⟨(pair).portVertex port, Finset.mem_inter.mpr ⟨?_, ?_⟩⟩
    · exact (mem_simpleGraphRotationSystem_endpoints_iff data _ _).mpr
        (portVertex_mem_boundaryEdgeValue pair port)
    · apply (mem_simpleGraphRotationSystem_endpoints_iff data _ _).mpr
      exact Sym2.mem_map.mpr ⟨(pair).retainedPort port, hmem, rfl⟩
  obtain ⟨x, y, hne, hset⟩ := Finset.card_eq_two.mp (hboundary.2.1 port)
  change incidentEdgeFinset Deleted ((pair).retainedPort port) = {x, y} at hset
  have hx : x ∈ incidentEdgeFinset Deleted ((pair).retainedPort port) := by rw [hset]; simp
  have hy : y ∈ incidentEdgeFinset Deleted ((pair).retainedPort port) := by rw [hset]; simp
  have hxy : C x ≠ C y := by
    apply C.valid
    refine SimpleGraph.lineGraph_adj_iff_exists.mpr ⟨hne, (pair).retainedPort port, ?_, ?_⟩
    · simpa only [incidentEdgeFinset, Finset.mem_filter, Finset.mem_univ, true_and] using hx
    · simpa only [incidentEdgeFinset, Finset.mem_filter, Finset.mem_univ, true_and] using hy
  exact third_nonzero_unique (C x) (C y) _ _ (hC x) (hC y) hxy
    ((pair).degreeTwoBoundaryData.colorWord_ne_zero hboundary C port)
    (taitColor_ne_zero _)
    ((pair).degreeTwoBoundaryData.colorWord_ne_incidentColor hboundary C hC port x hx)
    ((pair).degreeTwoBoundaryData.colorWord_ne_incidentColor hboundary C hC port y hy)
    (avoid x hx) (avoid y hy)

/-- Exact compatibility of the prescribed old witness with the whole final
path-and-cap construction, in its original three-colour representation. -/
theorem extension_iff (a : G.edgeSet → Fin 3)
    (ha : Proper data.toRotationSystem.endpoints Old a) :
    (∃ d : G.edgeSet → Fin 3, Proper data.toRotationSystem.endpoints Finset.univ d ∧
      ∀ x ∈ Old, d x = a x) ↔
      ¬ (requests data e ambient outer ho b hlen hcap a ha 0 =
          requests data e ambient outer ho b hlen hcap a ha 1 ∧
        requests data e ambient outer ho b hlen hcap a ha 2 =
          requests data e ambient outer ho b hlen hcap a ha 3) := by
  constructor
  · rintro ⟨d, hd, hagrees⟩ ⟨heq, _⟩
    have hne : boundaryEdge pair 0 ≠ boundaryEdge pair 1 := by
      intro h
      exact boundaryEdgeValue_ne pair (by decide : (0 : Fin 4) ≠ 1) (congrArg Subtype.val h)
    have hdifferent : d (boundaryEdge pair 0) ≠ d (boundaryEdge pair 1) := by
      apply hd _ (Finset.mem_univ _) _ (Finset.mem_univ _) hne
      refine ⟨(pair).firstVertex, Finset.mem_inter.mpr ⟨?_, ?_⟩⟩ <;>
        rw [mem_simpleGraphRotationSystem_endpoints_iff] <;> simp [boundaryEdge]
    apply taitColor_injective.ne hdifferent
    rw [← request_eq_extension_boundary data e ambient outer ho b hlen hcap a ha d hd hagrees 0,
      ← request_eq_extension_boundary data e ambient outer ho b hlen hcap a ha d hd hagrees 1]
    exact heq
  · exact reconstruct data e ambient outer ho b hlen hcap a ha

end
end Mettapedia.GraphTheory.FourColor.FaceMatchingCapColouring
