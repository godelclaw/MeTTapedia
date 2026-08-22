import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairAmbientClosureCrossFacePairDifferenceBoundaryFaceFusionChainRebaseFaceCircuitRecoveryTransferPrimalCutAttachment

/-!
# Connected sides behind an exact cubic four-edge boundary

This file isolates the finite graph-theoretic fact used by the source Cell
analysis.  If both sides of a four-edge boundary are connected in a cubic,
cyclically five-edge-connected graph, then one of the two sides consists of
exactly two vertices.

The conclusion deliberately does not orient the separator.  Identifying the
two-vertex side with the literal source Cell, rather than with its retained
outer complement, is a separate geometric theorem.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24CubicFourEdgeConnectedSides

open GoertzelV24CubicSmallBoundaryCycle
open GoertzelV24RotationVertexCutProfile
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance cubicFourEdgeConnectedSidesLocallyFinite : G.LocallyFinite :=
  fun vertex =>
    @Subtype.fintype V (Membership.mem (G.neighborSet vertex))
      (inferInstance : DecidablePred (Membership.mem (G.neighborSet vertex)))
      inferInstance

local instance cubicFourEdgeConnectedSidesEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

/-- Complementing a vertex side does not change its exact crossing-edge
support. -/
theorem crossingEdgeFinset_compl (side : V → Prop) :
    crossingEdgeFinset G (fun vertex ↦ ¬ side vertex) =
      crossingEdgeFinset G side := by
  ext edge
  rw [mem_crossingEdgeFinset_iff, mem_crossingEdgeFinset_iff]
  exact edgeCrossesVertexSide_compl G side edge

/-- A finite vertex side in a cubic rotation system meets at most three
edges per vertex.  This deliberately counts a shared internal edge twice in
the upper bound; the coarse bound is the stable finite carrier needed by the
Cell transition. -/
theorem vertexSetRegionEdges_card_le_three_mul_of_cubic
    (RS : RotationSystem V G.edgeSet) (hcubic : RS.IsCubic)
    (inside : Finset V) :
    (vertexSetRegionEdges RS inside).card ≤ 3 * inside.card := by
  have hsubset : vertexSetRegionEdges RS inside ⊆
      inside.biUnion RS.incidentEdges := by
    intro edge hedge
    rw [mem_vertexSetRegionEdges_iff] at hedge
    rcases hedge with ⟨vertex, hvertexEndpoint, hvertexInside⟩
    rw [Finset.mem_biUnion]
    exact ⟨vertex, hvertexInside,
      RS.mem_endpoints_iff_mem_incidentEdges.mp hvertexEndpoint⟩
  calc
    (vertexSetRegionEdges RS inside).card ≤
        (inside.biUnion RS.incidentEdges).card := Finset.card_le_card hsubset
    _ ≤ inside.card * 3 := by
      apply Finset.card_biUnion_le_card_mul
      intro vertex _hvertex
      exact le_of_eq (RS.incidentEdges_card_eq_three_of_isCubic hcubic vertex)
    _ = 3 * inside.card := Nat.mul_comm _ _

/-- The regional edge-carrier bound needs degree three only at vertices of the
chosen region.  This is the form used by an opened annulus, whose named stubs
have degree one but lie outside the literal Cell side. -/
theorem vertexSetRegionEdges_card_le_three_mul_of_local
    (RS : RotationSystem V G.edgeSet) (inside : Finset V)
    (hlocal : ∀ vertex ∈ inside, (RS.incidentEdges vertex).card = 3) :
    (vertexSetRegionEdges RS inside).card ≤ 3 * inside.card := by
  have hsubset : vertexSetRegionEdges RS inside ⊆
      inside.biUnion RS.incidentEdges := by
    intro edge hedge
    rw [mem_vertexSetRegionEdges_iff] at hedge
    rcases hedge with ⟨vertex, hvertexEndpoint, hvertexInside⟩
    rw [Finset.mem_biUnion]
    exact ⟨vertex, hvertexInside,
      RS.mem_endpoints_iff_mem_incidentEdges.mp hvertexEndpoint⟩
  calc
    (vertexSetRegionEdges RS inside).card ≤
        (inside.biUnion RS.incidentEdges).card := Finset.card_le_card hsubset
    _ ≤ inside.card * 3 := by
      apply Finset.card_biUnion_le_card_mul
      intro vertex hvertex
      exact le_of_eq (hlocal vertex hvertex)
    _ = 3 * inside.card := Nat.mul_comm _ _

/-- A two-vertex side of a cubic rotation system has a regional edge carrier
of size at most six. -/
theorem vertexSetRegionEdges_card_le_six_of_cubic_of_card_eq_two
    (RS : RotationSystem V G.edgeSet) (hcubic : RS.IsCubic)
    (inside : Finset V) (hcard : inside.card = 2) :
    (vertexSetRegionEdges RS inside).card ≤ 6 := by
  have hle := vertexSetRegionEdges_card_le_three_mul_of_cubic RS hcubic inside
  omega

/-- Local-cubic version of the exact attachment count for a connected side
with at most two vertices. -/
theorem card_crossingEdgeFinset_eq_card_add_two_of_local_cubic_of_connected_of_card_le_two
    (side : V → Prop)
    (hdegree : ∀ vertex, side vertex → G.degree vertex = 3)
    (hsideNonempty : ∃ vertex, side vertex)
    (hsideConnected : (G.induce {vertex | side vertex}).Connected)
    (hsideCard : Nat.card {vertex : V // side vertex} ≤ 2) :
    (crossingEdgeFinset G side).card =
      Nat.card {vertex : V // side vertex} + 2 := by
  let sideFintype : Fintype {vertex : V // side vertex} :=
    Fintype.ofInjective (fun vertex => vertex.1) Subtype.val_injective
  letI sideSubtypeFintype : Fintype {vertex : V // side vertex} :=
    sideFintype
  letI sideSetFintype : Fintype ↑({vertex | side vertex} : Set V) :=
    sideFintype
  have hsideCardFintype :
      Fintype.card {vertex : V // side vertex} ≤ 2 := by
    rw [← Nat.card_eq_fintype_card]
    exact hsideCard
  have hsameSideCard :
      Fintype.card ↑({vertex | side vertex} : Set V) =
        Fintype.card {vertex : V // side vertex} := by
    rfl
  have hsideAcyclic :
      (G.induce {vertex | side vertex}).IsAcyclic := by
    apply SimpleGraph.IsAcyclic.of_card_le_two
    rw [ENat.card_eq_coe_fintype_card, hsameSideCard]
    exact_mod_cast hsideCardFintype
  have htree : (G.induce {vertex | side vertex}).IsTree :=
    ⟨hsideConnected, hsideAcyclic⟩
  have htreeCard := htree.card_edgeFinset
  have hpartition := Fintype.card_congr
    (sideDartEquivInternalSumCrossing G side)
  rw [Fintype.card_sum] at hpartition
  have hsideDartCard := card_sideDart_eq_three_mul_of_local side hdegree
  have hinternalDartCard := card_internalSideDart_eq_twice_card_edges
    (G := G) side
  have hcrossingCard := card_crossingEdgeFinset_eq_card_crossingSideDart
    (G := G) side
  have hsidePositive :
      0 < Fintype.card {vertex : V // side vertex} :=
    Fintype.card_pos_iff.mpr
      ⟨⟨hsideNonempty.choose, hsideNonempty.choose_spec⟩⟩
  have hnatCard : Nat.card {vertex : V // side vertex} =
      Fintype.card {vertex : V // side vertex} :=
    Nat.card_eq_fintype_card
  omega

/-- A locally cubic connected side behind exactly four edges is either cyclic
or consists of exactly two vertices. -/
theorem hasCycleOnSide_or_card_eq_two_of_local_cubic_of_connected_of_boundary_card_eq_four
    (side : V → Prop)
    (hdegree : ∀ vertex, side vertex → G.degree vertex = 3)
    (hsideNonempty : ∃ vertex, side vertex)
    (hsideConnected : (G.induce {vertex | side vertex}).Connected)
    (hboundaryCard : (crossingEdgeFinset G side).card = 4) :
    HasCycleOnSide G side ∨ Nat.card {vertex : V // side vertex} = 2 := by
  let removed := crossingEdgeFinset G side
  have hremovedCard : removed.card ≤ 4 := by
    simpa [removed, hboundaryCard]
  have hsideCrossing : ∀ dart : CrossingSideDart G side,
      (⟨dart.1.edge, dart.1.edge_mem⟩ : G.edgeSet) ∈ removed := by
    intro dart
    apply (mem_crossingEdgeFinset_iff side _).2
    exact ⟨dart.1.fst, dart.1.snd,
      (by change dart.1.fst ∈ s(dart.1.fst, dart.1.snd); simp),
      (by change dart.1.snd ∈ s(dart.1.fst, dart.1.snd); simp),
      dart.2.1, dart.2.2⟩
  rcases hasCycleOnSide_or_card_le_two_mul_exception_add_removed_sub_two
      side (fun _ => False)
      (by intro _ _ hfalse; exact False.elim hfalse)
      (by intro vertex hvertex _; exact hdegree vertex hvertex)
      hsideConnected removed hsideCrossing with hcycle | hcard
  · exact .inl hcycle
  · right
    have hremovedCardEq : removed.card = 4 := by
      exact hboundaryCard
    simp only [Finset.filter_false, Finset.card_empty, Nat.mul_zero,
      zero_add, hremovedCardEq] at hcard
    have hsmall : Nat.card {vertex : V // side vertex} ≤ 2 := by
      rw [Nat.card_eq_fintype_card]
      exact hcard
    have hcount :=
      card_crossingEdgeFinset_eq_card_add_two_of_local_cubic_of_connected_of_card_le_two
        side hdegree hsideNonempty hsideConnected hsmall
    rw [hboundaryCard] at hcount
    omega

/-- In a cubic cyclically five-edge-connected graph, an exact four-edge
boundary with connected nonempty sides cuts off exactly two vertices on one
side.  The statement is intentionally unoriented. -/
theorem card_eq_two_or_compl_card_eq_two_of_cubic_of_connected_sides_of_boundary_card_eq_four
    (hregular : G.IsRegularOfDegree 3)
    (hcyclic : CyclicallyFiveEdgeConnected G)
    (side : V → Prop)
    (hsideNonempty : ∃ vertex, side vertex)
    (hsideConnected : (G.induce {vertex | side vertex}).Connected)
    (hcomplNonempty : ∃ vertex, ¬ side vertex)
    (hcomplConnected :
      (G.induce {vertex | ¬ side vertex}).Connected)
    (hboundaryCard : (crossingEdgeFinset G side).card = 4) :
    Nat.card {vertex : V // side vertex} = 2 ∨
      Nat.card {vertex : V // ¬ side vertex} = 2 := by
  let removed := crossingEdgeFinset G side
  have hremovedCard : removed.card ≤ 4 := by
    simpa [removed, hboundaryCard]
  have hsideCrossing : ∀ dart : CrossingSideDart G side,
      (⟨dart.1.edge, dart.1.edge_mem⟩ : G.edgeSet) ∈ removed := by
    intro dart
    apply (mem_crossingEdgeFinset_iff side _).2
    exact ⟨dart.1.fst, dart.1.snd,
      (by change dart.1.fst ∈ s(dart.1.fst, dart.1.snd); simp),
      (by change dart.1.snd ∈ s(dart.1.fst, dart.1.snd); simp),
      dart.2.1, dart.2.2⟩
  have hcomplCrossing : ∀ dart : CrossingSideDart G (fun vertex ↦ ¬ side vertex),
      (⟨dart.1.edge, dart.1.edge_mem⟩ : G.edgeSet) ∈ removed := by
    intro dart
    have hcrossCompl : EdgeCrossesVertexSide G
        (fun vertex ↦ ¬ side vertex)
        (⟨dart.1.edge, dart.1.edge_mem⟩ : G.edgeSet) :=
      ⟨dart.1.fst, dart.1.snd,
        (by change dart.1.fst ∈ s(dart.1.fst, dart.1.snd); simp),
        (by change dart.1.snd ∈ s(dart.1.fst, dart.1.snd); simp),
        dart.2.1, dart.2.2⟩
    apply (mem_crossingEdgeFinset_iff side _).2
    exact (edgeCrossesVertexSide_compl G side _).mp hcrossCompl
  have hsideCases :=
    hasCycleOnSide_or_card_le_two_of_cubic_of_connected_induce_of_crossing_le_four
      hregular side hsideNonempty hsideConnected removed hremovedCard
        hsideCrossing
  have hcomplCases :=
    hasCycleOnSide_or_card_le_two_of_cubic_of_connected_induce_of_crossing_le_four
      hregular (fun vertex ↦ ¬ side vertex) hcomplNonempty
        hcomplConnected removed hremovedCard hcomplCrossing
  rcases hsideCases with hsideCycle | hsideSmall
  · rcases hcomplCases with hcomplCycle | hcomplSmall
    · let realization : CyclicEdgeCutRealization G removed :=
        { side := side
          hcut_eq := fun edge => mem_crossingEdgeFinset_iff side edge
          hinside_cycle := hsideCycle
          houtside_cycle := hcomplCycle }
      exact False.elim
        (hcyclic.noCyclicEdgeCutOfSizeAtMostFour
          ⟨realization.toSmallCyclicEdgeCut hremovedCard, hremovedCard⟩)
    · right
      have hcard :=
        card_crossingEdgeFinset_eq_card_add_two_of_cubic_of_connected_of_card_le_two
          hregular (fun vertex ↦ ¬ side vertex) hcomplNonempty
            hcomplConnected hcomplSmall
      rw [crossingEdgeFinset_compl, hboundaryCard] at hcard
      omega
  · left
    have hcard :=
      card_crossingEdgeFinset_eq_card_add_two_of_cubic_of_connected_of_card_le_two
        hregular side hsideNonempty hsideConnected hsideSmall
    rw [hboundaryCard] at hcard
    omega

end

end GoertzelV24CubicFourEdgeConnectedSides

end Mettapedia.GraphTheory.FourColor
