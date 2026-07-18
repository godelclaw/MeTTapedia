import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairAmbientClosureCrossFacePairDifferenceBoundaryFaceFusionChainRebaseFaceCircuitRecoveryTransferPrimalCutComponent
import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairAmbientClosureCrossFacePairDifferenceBoundaryFaceFusionChainRebaseFaceCircuitRecoveryProperSubcircuit

namespace Mettapedia.GraphTheory.FourColor

open GoertzelV24AdjacentPairBoundary
open GoertzelV24AdjacentPairInsertion
open GoertzelV24CubicSmallBoundaryCycle
open GoertzelV24DualPathTransversal
open GoertzelV24FaceOrbitIncidence
open GoertzelV24FourDefectBoundary
open GoertzelV24MinimalFaceIntersections
open GoertzelV24OrbitFaceCurvatureBulk
open GoertzelV24TwoEdgeCutMinimality
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [decidableAdjacency : DecidableRel G.Adj]

noncomputable section

local instance attachmentFiniteGraphLocallyFinite (G : SimpleGraph V)
    [decidableAdjacency' : DecidableRel G.Adj] :
    G.LocallyFinite := fun vertex =>
  @Subtype.fintype V (Membership.mem (G.neighborSet vertex))
    (decidableAdjacency' vertex) inferInstance

namespace GoertzelV24CubicSmallBoundaryCycle

/-- The exact finite set of graph edges crossing a vertex side. -/
def crossingEdgeFinset (G : SimpleGraph V) (side : V → Prop) :
    Finset G.edgeSet := by
  classical
  exact Finset.univ.filter (EdgeCrossesVertexSide G side)

/-- The two possible attachment profiles of a nonempty connected cubic side
on at most two vertices inside a four-edge deletion. -/
def FourEdgeSmallSideAttachmentProfile (G : SimpleGraph V)
    (removed : Finset G.edgeSet) (side : V → Prop) : Prop :=
  (Nat.card {vertex : V // side vertex} = 1 ∧
      (crossingEdgeFinset G side).card = 3 ∧
      (removed \ crossingEdgeFinset G side).card = 1) ∨
    (Nat.card {vertex : V // side vertex} = 2 ∧
      crossingEdgeFinset G side = removed)

omit [DecidableEq V] decidableAdjacency in
@[simp]
theorem mem_crossingEdgeFinset_iff (side : V → Prop) (edge : G.edgeSet) :
    edge ∈ crossingEdgeFinset G side ↔
      EdgeCrossesVertexSide G side edge := by
  simp [crossingEdgeFinset]

/-- Orienting a crossing edge from the chosen side to its complement is an
equivalence between crossing edges and outgoing side darts. -/
def crossingSideDartEquivCrossingEdge (side : V → Prop) :
    CrossingSideDart G side ≃
      {edge : G.edgeSet // EdgeCrossesVertexSide G side edge} := by
  classical
  let toCrossing : CrossingSideDart G side →
      {edge : G.edgeSet // EdgeCrossesVertexSide G side edge} :=
    fun dart =>
      ⟨⟨dart.1.edge, dart.1.edge_mem⟩,
        ⟨dart.1.fst, dart.1.snd, (by
          change dart.1.fst ∈ s(dart.1.fst, dart.1.snd)
          simp), (by
          change dart.1.snd ∈ s(dart.1.fst, dart.1.snd)
          simp),
          dart.2.1, dart.2.2⟩⟩
  have hinjective : Function.Injective toCrossing := by
    intro left right heq
    apply crossingSideDart_edge_injective side
    exact congrArg (fun edge => edge.1) heq
  refine Equiv.ofBijective toCrossing ⟨hinjective, ?_⟩
  rintro ⟨edge, left, right, hleftEdge, hrightEdge,
    hleftSide, hrightSide⟩
  have hne : left ≠ right := by
    intro heq
    exact hrightSide (heq ▸ hleftSide)
  have hedgeValue : edge.1 = s(left, right) :=
    sym2_eq_mk_of_mem_of_mem_of_ne hleftEdge hrightEdge hne
  have hadj : G.Adj left right :=
    (SimpleGraph.mem_edgeSet G).1 (by simpa [hedgeValue] using edge.2)
  let dart : CrossingSideDart G side :=
    ⟨⟨(left, right), hadj⟩, hleftSide, hrightSide⟩
  refine ⟨dart, ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  exact hedgeValue.symm

/-- The number of exact crossing edges is the number of outgoing side
darts. -/
theorem card_crossingEdgeFinset_eq_card_crossingSideDart
    (side : V → Prop) :
    (crossingEdgeFinset G side).card =
      Fintype.card (CrossingSideDart G side) := by
  classical
  let boundaryEquiv :
      {edge : G.edgeSet // edge ∈ crossingEdgeFinset G side} ≃
        {edge : G.edgeSet // EdgeCrossesVertexSide G side edge} :=
    { toFun := fun edge =>
        ⟨edge.1, (mem_crossingEdgeFinset_iff side edge.1).1 edge.2⟩
      invFun := fun edge =>
        ⟨edge.1, (mem_crossingEdgeFinset_iff side edge.1).2 edge.2⟩
      left_inv := fun edge => by rfl
      right_inv := fun edge => by rfl }
  calc
    (crossingEdgeFinset G side).card =
        Fintype.card {edge : G.edgeSet //
          edge ∈ crossingEdgeFinset G side} :=
      (Fintype.card_coe _).symm
    _ = Fintype.card
        {edge : G.edgeSet // EdgeCrossesVertexSide G side edge} :=
      Fintype.card_congr boundaryEquiv
    _ = Fintype.card (CrossingSideDart G side) :=
      Fintype.card_congr (crossingSideDartEquivCrossingEdge side).symm

/-- A nonempty connected side of a cubic graph on at most two vertices has
exactly two more outgoing edges than vertices. -/
theorem card_crossingSideDart_eq_card_add_two_of_cubic_of_connected_of_card_le_two
    (hregular : G.IsRegularOfDegree 3) (side : V → Prop)
    (hsideNonempty : ∃ vertex, side vertex)
    (hsideConnected : (G.induce {vertex | side vertex}).Connected)
    (hsideCard : Nat.card {vertex : V // side vertex} ≤ 2) :
    Fintype.card (CrossingSideDart G side) =
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
  have hsideDartCard := card_sideDart_eq_three_mul hregular side
  have hinternalDartCard := card_internalSideDart_eq_twice_card_edges
    (G := G) side
  have hsidePositive :
      0 < Fintype.card {vertex : V // side vertex} :=
    Fintype.card_pos_iff.mpr
      ⟨⟨hsideNonempty.choose, hsideNonempty.choose_spec⟩⟩
  have hnatCard : Nat.card {vertex : V // side vertex} =
      Fintype.card {vertex : V // side vertex} :=
    Nat.card_eq_fintype_card
  omega

/-- Exact edge-count form of the preceding cubic attachment identity. -/
theorem card_crossingEdgeFinset_eq_card_add_two_of_cubic_of_connected_of_card_le_two
    (hregular : G.IsRegularOfDegree 3) (side : V → Prop)
    (hsideNonempty : ∃ vertex, side vertex)
    (hsideConnected : (G.induce {vertex | side vertex}).Connected)
    (hsideCard : Nat.card {vertex : V // side vertex} ≤ 2) :
    (crossingEdgeFinset G side).card =
      Nat.card {vertex : V // side vertex} + 2 := by
  rw [card_crossingEdgeFinset_eq_card_crossingSideDart]
  exact
    card_crossingSideDart_eq_card_add_two_of_cubic_of_connected_of_card_le_two
      hregular side hsideNonempty hsideConnected hsideCard

end GoertzelV24CubicSmallBoundaryCycle

namespace GoertzelV24FiniteEdgeDeletion

omit [DecidableEq V] in
/-- The component-boundary finset is the generic exact crossing finset of
its support side. -/
theorem componentCrossingEdges_eq_crossingEdgeFinset
    (removed : Finset G.edgeSet)
    (component :
      (G.deleteEdges (edgeFinsetValueSet removed)).ConnectedComponent) :
    componentCrossingEdges removed component =
      crossingEdgeFinset G (fun vertex => vertex ∈ component.supp) := by
  ext edge
  simp

omit [DecidableEq V] decidableAdjacency in
/-- A finite deletion component is nonempty, so a component containing at
most two vertices contains exactly one or exactly two. -/
theorem component_card_eq_one_or_two_of_card_le_two
    (removed : Finset G.edgeSet)
    (component :
      (G.deleteEdges (edgeFinsetValueSet removed)).ConnectedComponent)
    (hcard : Nat.card {vertex : V // vertex ∈ component.supp} ≤ 2) :
    Nat.card {vertex : V // vertex ∈ component.supp} = 1 ∨
      Nat.card {vertex : V // vertex ∈ component.supp} = 2 := by
  letI : Nonempty {vertex : V // vertex ∈ component.supp} :=
    ⟨⟨component.nonempty_supp.choose,
      component.nonempty_supp.choose_spec⟩⟩
  have hpositive :
      0 < Nat.card {vertex : V // vertex ∈ component.supp} := Nat.card_pos
  omega

/-- The exact boundary size of a cubic deletion component on at most two
vertices is its vertex count plus two. -/
theorem card_componentCrossingEdges_eq_card_add_two_of_cubic_of_card_le_two
    (hregular : G.IsRegularOfDegree 3) (removed : Finset G.edgeSet)
    (component :
      (G.deleteEdges (edgeFinsetValueSet removed)).ConnectedComponent)
    (hcard : Nat.card {vertex : V // vertex ∈ component.supp} ≤ 2) :
    (componentCrossingEdges removed component).card =
      Nat.card {vertex : V // vertex ∈ component.supp} + 2 := by
  rw [componentCrossingEdges_eq_crossingEdgeFinset]
  exact
    card_crossingEdgeFinset_eq_card_add_two_of_cubic_of_connected_of_card_le_two
      hregular (fun vertex => vertex ∈ component.supp)
      component.nonempty_supp
      (connected_induce_delete_component removed component) hcard

/-- Behind an exact four-edge deletion, a small cubic component has one of
two attachment profiles: one vertex and three used boundary edges, leaving
one deleted edge unused there; or two vertices and all four boundary edges. -/
theorem component_attachment_profile_of_cubic_of_removed_card_eq_four
    (hregular : G.IsRegularOfDegree 3)
    (removed : Finset G.edgeSet) (hremovedCard : removed.card = 4)
    (component :
      (G.deleteEdges (edgeFinsetValueSet removed)).ConnectedComponent)
    (hcard : Nat.card {vertex : V // vertex ∈ component.supp} ≤ 2) :
    FourEdgeSmallSideAttachmentProfile G removed
      (fun vertex => vertex ∈ component.supp) := by
  unfold FourEdgeSmallSideAttachmentProfile
  rw [← componentCrossingEdges_eq_crossingEdgeFinset removed component]
  have hboundaryCard :=
    card_componentCrossingEdges_eq_card_add_two_of_cubic_of_card_le_two
      hregular removed component hcard
  have hboundarySubset :=
    componentCrossingEdges_subset_removed removed component
  rcases component_card_eq_one_or_two_of_card_le_two removed component hcard with
    hone | htwo
  · left
    refine ⟨hone, by omega, ?_⟩
    rw [Finset.card_sdiff_of_subset hboundarySubset]
    omega
  · right
    refine ⟨htwo, ?_⟩
    apply Finset.eq_of_subset_of_card_le hboundarySubset
    omega

end GoertzelV24FiniteEdgeDeletion

namespace GoertzelV24DualCycleSeparator

attribute [local instance] graphEdgeSetDecidableEq

/-- A separating simple facial-dual four-cycle in a cubic cyclically
five-edge-connected graph cuts off a side with one of the exact four-edge
small-component attachment profiles. -/
theorem exists_primalCut_component_attachmentProfile_of_isCycle_of_length_eq_four
    (data : Data G) (hregular : G.IsRegularOfDegree 3)
    (hconnected : G.Connected) (hcyclic : CyclicallyFiveEdgeConnected G)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace data.toRotationSystem)))
    {start : AmbientFace
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    (walk : (interiorDualGraph
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace data.toRotationSystem))).Walk start start)
    (hcycle : walk.IsCycle) (hlength : walk.length = 4)
    (hdelete :
      ¬ (G.deleteEdges (dualWalkPrimalCut data hunique walk)).Connected) :
    let removed := dualWalkCrossingEdges
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem)) hunique walk
    ∃ component :
        (G.deleteEdges (dualWalkPrimalCut data hunique walk)).ConnectedComponent,
      FourEdgeSmallSideAttachmentProfile G removed
        (fun vertex => vertex ∈ component.supp) := by
  dsimp only
  let removed := dualWalkCrossingEdges
    (orbitFaceBoundary data.toRotationSystem)
    (Finset.univ : Finset (OrbitFace data.toRotationSystem)) hunique walk
  have hremovedCard : removed.card = 4 := by
    rw [GoertzelV24DualPathTransversal.card_dualWalkCrossingEdges_eq_length_of_isCycle
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))
      (orbitFace_incidence_le_two data.toRotationSystem) hunique walk hcycle,
      hlength]
  have hcutEq :=
    dualWalkPrimalCut_eq_edgeFinsetValueSet_dualWalkCrossingEdges
      data hunique walk
  rw [hcutEq] at hdelete ⊢
  rcases
      GoertzelV24FiniteEdgeDeletion.exists_component_card_le_two_of_cyclicallyFive_of_not_connected
        hregular hconnected hcyclic removed (by omega) hdelete with
    ⟨component, hcomponentCard⟩
  exact ⟨component,
    GoertzelV24FiniteEdgeDeletion.component_attachment_profile_of_cubic_of_removed_card_eq_four
      hregular removed hremovedCard component hcomponentCard⟩

end GoertzelV24DualCycleSeparator

namespace GoertzelV24AdjacentPairInsertion.AdjacentPairData

open GoertzelV24AdjacentPairBoundary.AdjacentPairData
open GoertzelV24FourDefectBoundary.DegreeTwoBoundaryData

attribute [local instance]
  fusionFaceNetworkGraphEdgeSetDecidableEq
  fusionFaceNetworkRetainedVertexFintype
  fusionFaceNetworkRetainedVertexDecidableEq

local instance attachmentCanonicalGraphLocallyFinite (G : SimpleGraph V)
    [decidableAdjacency' : DecidableRel G.Adj] :
    G.LocallyFinite := fun vertex =>
  @Subtype.fintype V (Membership.mem (G.neighborSet vertex))
    (decidableAdjacency' vertex) inferInstance

variable {graphData : Data G}
  {minimal : GraphBackedVertexMinimalTaitCounterexample graphData}
  {baseData : AdjacentPairData G}

namespace ClosureRecoveryFaceTransferCircuit

variable {rebaseCircuit :
  CrossCentralExactFaceCertifiedRebaseCircuit graphData minimal baseData}

/-- Every provenance-retaining transfer circuit supplies an ordinary
recovery circuit; minimizing the latter forces the carrying rebase circuit
to have at least four arcs. -/
theorem four_le_rebase_arcLength
    (circuit : ClosureRecoveryFaceTransferCircuit rebaseCircuit) :
    4 ≤ rebaseCircuit.arcLength := by
  rcases ClosureRecoveryFaceCircuit.exists_lengthMinimal
      (rebaseCircuit := rebaseCircuit)
      ⟨circuit.toRecoveryFaceCircuit⟩ with
    ⟨shortest, hshortest⟩
  exact hshortest.four_le_rebase_arcLength

/-- In the short regime, saturated recovery has rebase length exactly four
and produces a remote four-edge primal separator with an exact one-vertex
or two-vertex attachment profile. -/
theorem exists_remote_primal_separator_with_attachmentProfile_of_arcLength_le_four
    (hcyclic : CyclicallyFiveEdgeConnected G)
    (circuit : ClosureRecoveryFaceTransferCircuit rebaseCircuit)
    (hminimal : circuit.IsLengthMinimal)
    (hlength : circuit.arcLength = rebaseCircuit.arcLength)
    (hshort : rebaseCircuit.arcLength ≤ 4) :
    rebaseCircuit.arcLength = 4 ∧
      ∃ walk :
          (interiorDualGraph
            (orbitFaceBoundary graphData.toRotationSystem)
            (Finset.univ : Finset
              (OrbitFace graphData.toRotationSystem))).Walk
            rebaseCircuit.first.dualFace rebaseCircuit.first.dualFace,
        walk.IsCycle ∧
          ¬ (G.deleteEdges
            (GoertzelV24DualCycleSeparator.dualWalkPrimalCut graphData
              (pairwiseUniqueSharedInteriorEdges graphData minimal)
              walk)).Connected ∧
          (GoertzelV24DualCycleSeparator.dualWalkPrimalCut graphData
            (pairwiseUniqueSharedInteriorEdges graphData minimal) walk).ncard = 4 ∧
          (let removed := dualWalkCrossingEdges
              (orbitFaceBoundary graphData.toRotationSystem)
              (Finset.univ : Finset
                (OrbitFace graphData.toRotationSystem))
              (pairwiseUniqueSharedInteriorEdges graphData minimal) walk
            ∃ component :
                (G.deleteEdges
                  (GoertzelV24DualCycleSeparator.dualWalkPrimalCut graphData
                    (pairwiseUniqueSharedInteriorEdges graphData minimal)
                    walk)).ConnectedComponent,
              FourEdgeSmallSideAttachmentProfile G removed
                (fun vertex => vertex ∈ component.supp)) ∧
          (∀ face ∈ walk.support,
            centralEdge
                (baseData.rotationOrderedData graphData
                  minimal.spherical.cubic minimal.vertexRotationCyclic) ∉
              orbitFaceBoundary graphData.toRotationSystem face.1) ∧
          (∀ face ∈ walk.support, ∀ port : Fin 4,
            boundaryEdge
                (baseData.rotationOrderedData graphData
                  minimal.spherical.cubic minimal.vertexRotationCyclic) port ∉
              orbitFaceBoundary graphData.toRotationSystem face.1) := by
  have hrebaseLength : rebaseCircuit.arcLength = 4 :=
    Nat.le_antisymm hshort circuit.four_le_rebase_arcLength
  rcases circuit.exists_remote_primal_separator hminimal hlength with
    ⟨walk, hcycle, hdelete, hcutCard, hcentral, hboundary⟩
  have hregular : G.IsRegularOfDegree 3 :=
    graphData.toRotationSystem_isCubic_iff.mp minimal.spherical.cubic
  have hconnected : G.Connected := by
    rw [← GoertzelV24SimpleGraphFaceDualConnectedness.rotationPrimalGraph_toRotationSystem_eq
      G graphData]
    exact minimal.primalConnected
  have hwalkLength : walk.length = 4 := by
    calc
      walk.length =
          (GoertzelV24DualCycleSeparator.dualWalkPrimalCut graphData
            (pairwiseUniqueSharedInteriorEdges graphData minimal)
              walk).ncard :=
        (GoertzelV24DualCycleSeparator.ncard_dualWalkPrimalCut_eq_length_of_isCycle
          graphData (pairwiseUniqueSharedInteriorEdges graphData minimal)
            walk hcycle).symm
      _ = rebaseCircuit.arcLength := hcutCard
      _ = 4 := hrebaseLength
  have hprofile :=
    GoertzelV24DualCycleSeparator.exists_primalCut_component_attachmentProfile_of_isCycle_of_length_eq_four
      graphData hregular hconnected hcyclic
        (pairwiseUniqueSharedInteriorEdges graphData minimal) walk hcycle
          hwalkLength hdelete
  exact ⟨hrebaseLength, walk, hcycle, hdelete,
    hcutCard.trans hrebaseLength, hprofile, hcentral, hboundary⟩

end ClosureRecoveryFaceTransferCircuit

end GoertzelV24AdjacentPairInsertion.AdjacentPairData

end

end Mettapedia.GraphTheory.FourColor
