import Mathlib.Combinatorics.SimpleGraph.Tutte
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mettapedia.Combinatorics.Matching.GraphBridge
import Mettapedia.GraphTheory.FourColor.GoertzelV24RotationBoundaryBridge
import Mettapedia.GraphTheory.FourColor.GoertzelV24RotationVertexCutProfile
import Mettapedia.GraphTheory.FourColor.GoertzelV24SimpleGraphRotationBridge
import Mettapedia.GraphTheory.FourColor.GoertzelV24TaitMatchingPair

/-!
# Petersen's starting matching

The two-perfect-matching formulation of Tait colourability needs an initial
graph-supported pairing.  This file derives it for every finite bridge-free
cubic simple graph from Mathlib's Tutte theorem.  The proof is included at the
rotation-system interface used by the compositional route and then discharged
to the ordinary graph statement.
-/

namespace Mettapedia.GraphTheory.FourColor

open scoped BigOperators

namespace GoertzelV24PetersenStartingMatching

open GoertzelV24RotationVertexCutProfile

variable {V E : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E]

noncomputable section

/-- Equality of repeated `red` in the Klein four-group detects parity. -/
theorem nsmul_red_eq_iff_mod_two_eq (m n : Nat) :
    m • red = n • red ↔ m % 2 = n % 2 := by
  simpa [red] using ZMod.natCast_eq_natCast_iff' m n 2

/-- In a cubic rotation system, a vertex set and its edge boundary have the
same parity. -/
theorem cubic_boundary_parity (RS : RotationSystem V E)
    (hCubic : RS.IsCubic) (side : Finset V) :
    (RS.vertexSideEdgeBoundary side).card % 2 = side.card % 2 := by
  have hvertex (v : V) : RS.vertexColorSum (fun _ => red) v = red := by
    rw [RotationSystem.vertexColorSum, Finset.sum_const,
      RS.incidentEdges_card_eq_three_of_isCubic hCubic v]
    change red + red + red = red
    simp
  have hsum :
      side.card • red = (RS.vertexSideEdgeBoundary side).card • red := by
    calc
      side.card • red = ∑ v ∈ side, RS.vertexColorSum (fun _ => red) v := by
        simp [hvertex]
      _ = ∑ e : E, (RS.endpoints e ∩ side).card • red :=
        RS.sum_vertexColorSum_eq_sum_endpointMultiplicity (fun _ => red) side
      _ = ∑ e ∈ RS.vertexSideEdgeBoundary side, red :=
        RS.sum_endpointMultiplicity_eq_sum_vertexSideEdgeBoundary
          (fun _ => red) side
      _ = (RS.vertexSideEdgeBoundary side).card • red := by simp
  exact (nsmul_red_eq_iff_mod_two_eq _ _).mp hsum |>.symm

variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- The graph left after deleting a vertex set. -/
abbrev DeletedGraph (G : SimpleGraph V) (removed : Set V) :=
  ((⊤ : G.Subgraph).deleteVerts removed).coe

/-- The original vertices belonging to a connected component of `G - S`. -/
def componentSide {removed : Set V}
    (component : (DeletedGraph G removed).ConnectedComponent) : Finset V :=
  component.supp.toFinite.toFinset.image fun vertex => vertex.1

omit [DecidableRel G.Adj] in
@[simp] theorem mem_componentSide_iff {removed : Set V}
    (component : (DeletedGraph G removed).ConnectedComponent) (vertex : V) :
    vertex ∈ componentSide component ↔
      ∃ source ∈ component.supp, source.1 = vertex := by
  simp [componentSide]

omit [DecidableRel G.Adj] in
theorem card_componentSide {removed : Set V}
    (component : (DeletedGraph G removed).ConnectedComponent) :
    (componentSide component).card = component.supp.ncard := by
  rw [componentSide, Finset.card_image_of_injective _ (by
    intro first second h
    exact Subtype.ext h)]
  rw [Set.ncard_eq_toFinset_card component.supp component.supp.toFinite]

omit [DecidableRel G.Adj] in
/-- A component of `G - S` is disjoint from `S`. -/
theorem componentSide_disjoint_removed {removed : Set V}
    (component : (DeletedGraph G removed).ConnectedComponent) :
    Disjoint (componentSide component : Set V) removed := by
  rw [Set.disjoint_left]
  intro vertex hside hremoved
  change vertex ∈ componentSide component at hside
  rw [mem_componentSide_iff] at hside
  obtain ⟨source, _, rfl⟩ := hside
  exact source.2.2 hremoved

/-- An odd component of a deleted cubic graph has odd edge boundary. -/
theorem odd_component_boundary_odd
    (data : SimpleGraphDartRotation.Data G)
    (hCubic : data.toRotationSystem.IsCubic)
    {removed : Set V}
    (component : (DeletedGraph G removed).ConnectedComponent)
    (hodd : component ∈ (DeletedGraph G removed).oddComponents) :
    Odd (data.toRotationSystem.vertexSideEdgeBoundary
      (componentSide component)).card := by
  have hparity := cubic_boundary_parity data.toRotationSystem hCubic
    (componentSide component)
  have hsideOdd : Odd (componentSide component).card := by
    rw [card_componentSide]
    exact hodd
  rw [Nat.odd_iff] at hsideOdd ⊢
  omega

/-- In a bridge-free cubic graph, every odd deleted component has at least
three boundary edges. -/
theorem three_le_odd_component_boundary
    (data : SimpleGraphDartRotation.Data G)
    (hCubic : data.toRotationSystem.IsCubic)
    (hfree : GoertzelV24RotationEdgeBridge.EdgeBridgeFree
      data.toRotationSystem)
    {removed : Set V}
    (component : (DeletedGraph G removed).ConnectedComponent)
    (hodd : component ∈ (DeletedGraph G removed).oddComponents) :
    3 ≤ (data.toRotationSystem.vertexSideEdgeBoundary
      (componentSide component)).card := by
  let boundary := data.toRotationSystem.vertexSideEdgeBoundary
    (componentSide component)
  have hboundaryOdd : Odd boundary.card :=
    odd_component_boundary_odd data hCubic component hodd
  have hneOne : boundary.card ≠ 1 := by
    intro hcard
    obtain ⟨edge, hedge⟩ := Finset.card_eq_one.mp hcard
    exact GoertzelV24RotationBoundaryBridge.not_boundary_singleton_of_edgeBridgeFree
      data.toRotationSystem hfree (componentSide component) edge hedge
  rw [Nat.odd_iff] at hboundaryOdd
  change 3 ≤ boundary.card
  omega

/-- An edge cannot lie on the boundaries of two distinct components of a
deleted graph. -/
theorem component_eq_of_common_boundary_edge
    (data : SimpleGraphDartRotation.Data G)
    {removed : Set V}
    {first second : (DeletedGraph G removed).ConnectedComponent}
    {edge : G.edgeSet}
    (hfirst : edge ∈ data.toRotationSystem.vertexSideEdgeBoundary
      (componentSide first))
    (hsecond : edge ∈ data.toRotationSystem.vertexSideEdgeBoundary
      (componentSide second)) :
    first = second := by
  classical
  rw [RotationSystem.mem_vertexSideEdgeBoundary_iff] at hfirst hsecond
  have hfirstNonempty :
      (data.toRotationSystem.endpoints edge ∩ componentSide first).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hempty
    rw [hempty, Finset.card_empty] at hfirst
    omega
  have hsecondNonempty :
      (data.toRotationSystem.endpoints edge ∩ componentSide second).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hempty
    rw [hempty, Finset.card_empty] at hsecond
    omega
  obtain ⟨firstVertex, hfirstMem⟩ := hfirstNonempty
  obtain ⟨hfirstEndpoint, hfirstSide⟩ := Finset.mem_inter.mp hfirstMem
  obtain ⟨secondVertex, hsecondMem⟩ := hsecondNonempty
  obtain ⟨hsecondEndpoint, hsecondSide⟩ := Finset.mem_inter.mp hsecondMem
  rw [mem_componentSide_iff] at hfirstSide hsecondSide
  obtain ⟨firstSource, hfirstSupp, hfirstValue⟩ := hfirstSide
  obtain ⟨secondSource, hsecondSupp, hsecondValue⟩ := hsecondSide
  have hsourceEqOrAdj : firstSource = secondSource ∨
      (DeletedGraph G removed).Adj firstSource secondSource := by
    by_cases hvertices : firstVertex = secondVertex
    · left
      apply Subtype.ext
      exact hfirstValue.trans (hvertices.trans hsecondValue.symm)
    · right
      have hfirstSym : firstVertex ∈ (edge.1 : Sym2 V) :=
        (mem_simpleGraphRotationSystem_endpoints_iff
          data edge firstVertex).1 hfirstEndpoint
      have hsecondSym : secondVertex ∈ (edge.1 : Sym2 V) :=
        (mem_simpleGraphRotationSystem_endpoints_iff
          data edge secondVertex).1 hsecondEndpoint
      have hedgeValue : edge.1 = s(firstVertex, secondVertex) :=
        (Sym2.mem_and_mem_iff hvertices).1 ⟨hfirstSym, hsecondSym⟩
      have hadj : G.Adj firstVertex secondVertex := by
        rw [← SimpleGraph.mem_edgeSet, ← hedgeValue]
        exact edge.2
      have hadjSources : G.Adj firstSource.1 secondSource.1 := by
        simpa [hfirstValue, hsecondValue] using hadj
      change ((⊤ : G.Subgraph).deleteVerts removed).Adj
        firstSource.1 secondSource.1
      simpa [SimpleGraph.Subgraph.deleteVerts_adj] using hadjSources
  rw [SimpleGraph.ConnectedComponent.mem_supp_iff] at hfirstSupp hsecondSupp
  rcases hsourceEqOrAdj with hsource | hadj
  · rw [hsource] at hfirstSupp
    exact hfirstSupp.symm.trans hsecondSupp
  · have hcomponents :=
      SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hadj
    exact hfirstSupp.symm.trans (hcomponents.trans hsecondSupp)

/-- Finite representation of the odd components of `G - S`. -/
def oddComponentsFinset (G : SimpleGraph V) [DecidableRel G.Adj]
    (removed : Set V) :
    Finset (DeletedGraph G removed).ConnectedComponent :=
  (DeletedGraph G removed).oddComponents.toFinite.toFinset

/-- Finite representation of a vertex subset. -/
def removedFinset (removed : Set V) : Finset V :=
  removed.toFinite.toFinset

omit [DecidableEq V] in
@[simp] theorem mem_oddComponentsFinset_iff {removed : Set V}
    (component : (DeletedGraph G removed).ConnectedComponent) :
    component ∈ oddComponentsFinset G removed ↔
      component ∈ (DeletedGraph G removed).oddComponents := by
  simp [oddComponentsFinset]

omit [DecidableEq V] in
@[simp] theorem mem_removedFinset_iff {removed : Set V} (vertex : V) :
    vertex ∈ removedFinset removed ↔ vertex ∈ removed := by
  simp [removedFinset]

omit [DecidableEq V] in
theorem card_oddComponentsFinset {removed : Set V} :
    (oddComponentsFinset G removed).card =
      (DeletedGraph G removed).oddComponents.ncard := by
  rw [oddComponentsFinset,
    Set.ncard_eq_toFinset_card _
      (DeletedGraph G removed).oddComponents.toFinite]

omit [DecidableEq V] in
theorem card_removedFinset {removed : Set V} :
    (removedFinset removed).card = removed.ncard := by
  rw [removedFinset, Set.ncard_eq_toFinset_card _ removed.toFinite]

/-- Boundaries of distinct odd components are pairwise edge-disjoint. -/
theorem oddComponentBoundaries_pairwiseDisjoint
    (data : SimpleGraphDartRotation.Data G) {removed : Set V} :
    ∀ first ∈ oddComponentsFinset G removed,
      ∀ second ∈ oddComponentsFinset G removed,
        first ≠ second →
          Disjoint
            (data.toRotationSystem.vertexSideEdgeBoundary
              (componentSide first))
            (data.toRotationSystem.vertexSideEdgeBoundary
              (componentSide second)) := by
  intro first _ second _ hne
  rw [Finset.disjoint_left]
  intro edge hfirst hsecond
  exact hne (component_eq_of_common_boundary_edge data hfirst hsecond)

/-- Every edge leaving a component of `G - S` is incident to `S`. -/
theorem component_boundary_subset_removed_incidentEdges
    (data : SimpleGraphDartRotation.Data G)
    {removed : Set V}
    (component : (DeletedGraph G removed).ConnectedComponent) :
    data.toRotationSystem.vertexSideEdgeBoundary (componentSide component) ⊆
      (removedFinset removed).biUnion data.toRotationSystem.incidentEdges := by
  intro edge hedge
  have hcross : edgeCrossesVertexSet data.toRotationSystem
      (componentSide component) edge := by
    apply (edgeCrossesVertexSet_iff_card_inter_eq_one
      data.toRotationSystem (componentSide component) edge).2
    exact (data.toRotationSystem.mem_vertexSideEdgeBoundary_iff).1 hedge
  obtain ⟨inner, hinnerEndpoint, hinnerSide,
      outer, houterEndpoint, houterOutside⟩ := hcross
  have houterRemoved : outer ∈ removed := by
    by_contra houterNotRemoved
    have hinnerInSide := hinnerSide
    rw [mem_componentSide_iff] at hinnerSide
    obtain ⟨innerSource, hinnerSupp, hinnerValue⟩ := hinnerSide
    let outerSource : ((⊤ : G.Subgraph).deleteVerts removed).verts :=
      ⟨outer, by simp [houterNotRemoved]⟩
    have hvertices : inner ≠ outer := by
      intro heq
      exact houterOutside (heq ▸ hinnerInSide)
    have hinnerSym : inner ∈ (edge.1 : Sym2 V) :=
      (mem_simpleGraphRotationSystem_endpoints_iff data edge inner).1
        hinnerEndpoint
    have houterSym : outer ∈ (edge.1 : Sym2 V) :=
      (mem_simpleGraphRotationSystem_endpoints_iff data edge outer).1
        houterEndpoint
    have hedgeValue : edge.1 = s(inner, outer) :=
      (Sym2.mem_and_mem_iff hvertices).1 ⟨hinnerSym, houterSym⟩
    have hadj : G.Adj inner outer := by
      rw [← SimpleGraph.mem_edgeSet, ← hedgeValue]
      exact edge.2
    have hadjSources : G.Adj innerSource.1 outerSource.1 := by
      simpa [outerSource, hinnerValue] using hadj
    have hadjDeleted : (DeletedGraph G removed).Adj innerSource outerSource := by
      change ((⊤ : G.Subgraph).deleteVerts removed).Adj
        innerSource.1 outerSource.1
      simpa [SimpleGraph.Subgraph.deleteVerts_adj] using hadjSources
    have houterSupp : outerSource ∈ component.supp :=
      component.mem_supp_of_adj_mem_supp hinnerSupp hadjDeleted
    apply houterOutside
    rw [mem_componentSide_iff]
    exact ⟨outerSource, houterSupp, rfl⟩
  rw [Finset.mem_biUnion]
  refine ⟨outer, (mem_removedFinset_iff outer).2 houterRemoved, ?_⟩
  exact (data.toRotationSystem.mem_endpoints_iff_mem_incidentEdges).1
    houterEndpoint

/-- The cubic boundary count proves Tutte's odd-component inequality. -/
theorem oddComponents_ncard_le_removed_ncard
    (data : SimpleGraphDartRotation.Data G)
    (hCubic : data.toRotationSystem.IsCubic)
    (hfree : GoertzelV24RotationEdgeBridge.EdgeBridgeFree
      data.toRotationSystem)
    (removed : Set V) :
    (DeletedGraph G removed).oddComponents.ncard ≤ removed.ncard := by
  rw [← card_oddComponentsFinset (G := G) (removed := removed),
    ← card_removedFinset (removed := removed)]
  let components := oddComponentsFinset G removed
  let removedVertices := removedFinset removed
  let boundary := fun component : (DeletedGraph G removed).ConnectedComponent =>
    data.toRotationSystem.vertexSideEdgeBoundary (componentSide component)
  change components.card ≤ removedVertices.card
  have hdisjoint : (components : Set _).PairwiseDisjoint boundary := by
    intro first hfirst second hsecond hne
    exact oddComponentBoundaries_pairwiseDisjoint data first hfirst second hsecond hne
  have hunionSubset : components.biUnion boundary ⊆
      removedVertices.biUnion data.toRotationSystem.incidentEdges := by
    intro edge hedge
    rw [Finset.mem_biUnion] at hedge
    obtain ⟨component, _, hedge⟩ := hedge
    exact component_boundary_subset_removed_incidentEdges data component hedge
  have hleft : 3 * components.card ≤ (components.biUnion boundary).card := by
    rw [Finset.card_biUnion hdisjoint]
    calc
      3 * components.card = ∑ _ ∈ components, 3 := by
        simp [Nat.mul_comm]
      _ ≤ ∑ component ∈ components, (boundary component).card := by
        apply Finset.sum_le_sum
        intro component hcomponent
        exact three_le_odd_component_boundary data hCubic hfree component
          ((mem_oddComponentsFinset_iff component).1 hcomponent)
  have hright :
      (removedVertices.biUnion data.toRotationSystem.incidentEdges).card ≤
        3 * removedVertices.card := by
    calc
      (removedVertices.biUnion data.toRotationSystem.incidentEdges).card ≤
          ∑ vertex ∈ removedVertices,
            (data.toRotationSystem.incidentEdges vertex).card :=
        Finset.card_biUnion_le
      _ = ∑ _ ∈ removedVertices, 3 := by
        apply Finset.sum_congr rfl
        intro vertex _
        exact data.toRotationSystem.incidentEdges_card_eq_three_of_isCubic
          hCubic vertex
      _ = 3 * removedVertices.card := by simp [Nat.mul_comm]
  have hscaled : 3 * components.card ≤ 3 * removedVertices.card :=
    hleft.trans ((Finset.card_le_card hunionSubset).trans hright)
  omega

/-- A graph-backed finite cubic graph with no bridges has a supported perfect
matching. -/
theorem exists_supportedPairing_of_cubic_edgeBridgeFree
    (data : SimpleGraphDartRotation.Data G)
    (hCubic : data.toRotationSystem.IsCubic)
    (hfree : GoertzelV24RotationEdgeBridge.EdgeBridgeFree
      data.toRotationSystem) :
    ∃ pairing : MatchingParity.Pairing V, pairing.SupportedBy G := by
  obtain ⟨matching, hmatching⟩ := (SimpleGraph.tutte (G := G)).2 (by
    intro removed
    rw [SimpleGraph.IsTutteViolator]
    exact not_lt_of_ge
      (oddComponents_ncard_le_removed_ncard data hCubic hfree removed))
  exact ⟨MatchingParity.Pairing.ofPerfectMatching hmatching,
    MatchingParity.Pairing.ofPerfectMatching_supportedBy hmatching⟩

/-- **Petersen's perfect-matching theorem for finite simple cubic graphs.**
A bridge-free finite 3-regular simple graph has a graph-supported pairing. -/
theorem petersen_supportedPairing
    (hCubic : G.IsRegularOfDegree 3)
    (hfree : ∀ edge : G.edgeSet, ¬ G.IsBridge edge.1) :
    ∃ pairing : MatchingParity.Pairing V, pairing.SupportedBy G := by
  by_cases hvertices : Nonempty V
  · letI : Nonempty V := hvertices
    let root : V := Classical.choice hvertices
    have hdegreePositive : 0 < G.degree root := by
      rw [hCubic root]
      omega
    obtain ⟨neighbor, hadj⟩ := (G.degree_pos_iff_exists_adj root).1
      hdegreePositive
    let outer : G.Dart := ⟨(root, neighbor), hadj⟩
    let data : SimpleGraphDartRotation.Data G := {
      vertexRotation := 1
      vertexRotation_fst := by intro dart; rfl
      outer := outer
    }
    apply exists_supportedPairing_of_cubic_edgeBridgeFree data
    · exact data.toRotationSystem_isCubic_iff.mpr hCubic
    · rw [GoertzelV24RotationEdgeBridge.edgeBridgeFree_toRotationSystem_iff]
      intro dart
      exact hfree ⟨dart.edge, dart.edge_mem⟩
  · have hempty : IsEmpty V :=
      ⟨fun vertex => hvertices ⟨vertex⟩⟩
    letI : IsEmpty V := hempty
    let pairing : MatchingParity.Pairing V := {
      partner := fun vertex => isEmptyElim vertex
      partner_partner := fun vertex => isEmptyElim vertex
      partner_ne := fun vertex => isEmptyElim vertex
    }
    exact ⟨pairing, fun vertex => isEmptyElim vertex⟩

/-- A bridge-free cubic Tait counterexample has an inhabited family of
supported pairings, and every member overlaps a fixed starting pairing. -/
theorem exists_startingPairing_all_supportedPairings_overlap
    (hCubic : G.IsRegularOfDegree 3)
    (hfree : ∀ edge : G.edgeSet, ¬ G.IsBridge edge.1)
    (hnot : ¬ TaitColorable G) :
    ∃ starting : MatchingParity.Pairing V,
      starting.SupportedBy G ∧
      ∀ other : MatchingParity.Pairing V, other.SupportedBy G →
        ∃ vertex, starting.partner vertex = other.partner vertex := by
  obtain ⟨starting, hstarting⟩ := petersen_supportedPairing hCubic hfree
  refine ⟨starting, hstarting, ?_⟩
  have htriples : HasCubicIncidentEdgeTriples G :=
    hasCubicIncidentEdgeTriples_of_incidentEdgeFinset_card_eq_three fun vertex => by
      rw [incidentEdgeFinset_card_eq_degree, hCubic vertex]
  intro other hother
  exact GoertzelV24TaitMatchingPair.exists_shared_edge_of_not_taitColorable
    htriples hnot starting other hstarting hother

end

end GoertzelV24PetersenStartingMatching

end Mettapedia.GraphTheory.FourColor
