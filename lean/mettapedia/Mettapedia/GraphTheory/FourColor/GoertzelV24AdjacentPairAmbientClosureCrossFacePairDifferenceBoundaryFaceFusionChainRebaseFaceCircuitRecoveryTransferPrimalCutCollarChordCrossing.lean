import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairAmbientClosureCrossFacePairDifferenceBoundaryFaceFusionChainRebaseFaceCircuitRecoveryTransferPrimalCutCollarChord

namespace Mettapedia.GraphTheory.FourColor

open GoertzelV24AdjacentPairBoundary
open GoertzelV24AdjacentPairInsertion
open GoertzelV24CubicSmallBoundaryCycle
open GoertzelV24DualPathTransversal
open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24FourDefectBoundary
open GoertzelV24MinimalFaceIntersections
open GoertzelV24OrbitFaceCurvatureBulk
open GoertzelV24OrbitFaceTwoSided
open GoertzelV24TwoEdgeCutMinimality
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

attribute [local instance]
  collarFiniteGraphLocallyFinite
  GoertzelV24DualCycleSeparator.graphEdgeSetDecidableEq

namespace GoertzelV24DualCycleChordCrossing

variable {F E : Type*} [Fintype F] [DecidableEq F]
  [Fintype E] [DecidableEq E]

/-- Equal primal crossings, even in two different facial-dual walks,
determine the same unordered dual edge. -/
theorem dualWalkGraphEdge_eq_of_two_walk_crossingEdge_eq
    (faceBoundary : F → Finset E) (allFaces : Finset F)
    (hall : ∀ edge,
      totalIncidenceCount faceBoundary allFaces edge ≤ 2)
    (hunique : PairwiseUniqueSharedInteriorEdges faceBoundary allFaces)
    {firstStart firstFinish secondStart secondFinish :
      AmbientFace allFaces}
    (firstWalk : (interiorDualGraph faceBoundary allFaces).Walk
      firstStart firstFinish)
    (secondWalk : (interiorDualGraph faceBoundary allFaces).Walk
      secondStart secondFinish)
    {firstStep : Fin firstWalk.length}
    {secondStep : Fin secondWalk.length}
    (hedges :
      dualWalkCrossingEdge faceBoundary allFaces hunique firstWalk
          firstStep =
        dualWalkCrossingEdge faceBoundary allFaces hunique secondWalk
          secondStep) :
    dualWalkGraphEdge faceBoundary allFaces firstWalk firstStep =
      dualWalkGraphEdge faceBoundary allFaces secondWalk secondStep := by
  let firstLeft := firstWalk.getVert firstStep.val
  let firstRight := firstWalk.getVert (firstStep.val + 1)
  let secondLeft := secondWalk.getVert secondStep.val
  let secondRight := secondWalk.getVert (secondStep.val + 1)
  have hfirstAdj := firstWalk.adj_getVert_succ firstStep.isLt
  have hsecondAdj := secondWalk.adj_getVert_succ secondStep.isLt
  have hfirstFaces : firstLeft.1 ≠ firstRight.1 := by
    intro hfaces
    exact hfirstAdj.ne (Subtype.ext hfaces)
  have hsecondFaces : secondLeft.1 ≠ secondRight.1 := by
    intro hfaces
    exact hsecondAdj.ne (Subtype.ext hfaces)
  have hfirstLeft :
      dualWalkCrossingEdge faceBoundary allFaces hunique firstWalk
          firstStep ∈ faceBoundary firstLeft.1 :=
    dualWalkCrossingEdge_mem_leftFace faceBoundary allFaces hunique
      firstWalk firstStep
  have hfirstRight :
      dualWalkCrossingEdge faceBoundary allFaces hunique firstWalk
          firstStep ∈ faceBoundary firstRight.1 :=
    dualWalkCrossingEdge_mem_rightFace faceBoundary allFaces hunique
      firstWalk firstStep
  have hsecondLeft :
      dualWalkCrossingEdge faceBoundary allFaces hunique firstWalk
          firstStep ∈ faceBoundary secondLeft.1 := by
    rw [hedges]
    exact dualWalkCrossingEdge_mem_leftFace faceBoundary allFaces hunique
      secondWalk secondStep
  have hsecondRight :
      dualWalkCrossingEdge faceBoundary allFaces hunique firstWalk
          firstStep ∈ faceBoundary secondRight.1 := by
    rw [hedges]
    exact dualWalkCrossingEdge_mem_rightFace faceBoundary allFaces hunique
      secondWalk secondStep
  have hleft :=
    eq_or_eq_of_mem_faceBoundary_of_mem_faceBoundary_of_mem_faceBoundary_of_ne_of_count_le_two
      faceBoundary allFaces hall firstLeft.2 firstRight.2 secondLeft.2
      hfirstFaces hfirstLeft hfirstRight hsecondLeft
  have hright :=
    eq_or_eq_of_mem_faceBoundary_of_mem_faceBoundary_of_mem_faceBoundary_of_ne_of_count_le_two
      faceBoundary allFaces hall firstLeft.2 firstRight.2 secondRight.2
      hfirstFaces hfirstLeft hfirstRight hsecondRight
  change s(firstLeft, firstRight) = s(secondLeft, secondRight)
  rcases hleft with hleft | hleft <;>
    rcases hright with hright | hright
  · exact False.elim (hsecondFaces (hleft.trans hright.symm))
  · apply Sym2.eq_iff.mpr
    exact Or.inl ⟨Subtype.ext hleft.symm, Subtype.ext hright.symm⟩
  · apply Sym2.eq_iff.mpr
    exact Or.inr ⟨Subtype.ext hright.symm, Subtype.ext hleft.symm⟩
  · exact False.elim (hsecondFaces (hleft.trans hright.symm))

/-- Inclusion of primal crossing sets forces inclusion of the underlying
unordered dual edges, even for walks with different endpoints. -/
theorem walk_edges_subset_of_crossingEdges_subset
    (faceBoundary : F → Finset E) (allFaces : Finset F)
    (hall : ∀ edge,
      totalIncidenceCount faceBoundary allFaces edge ≤ 2)
    (hunique : PairwiseUniqueSharedInteriorEdges faceBoundary allFaces)
    {firstStart firstFinish secondStart secondFinish :
      AmbientFace allFaces}
    (firstWalk : (interiorDualGraph faceBoundary allFaces).Walk
      firstStart firstFinish)
    (secondWalk : (interiorDualGraph faceBoundary allFaces).Walk
      secondStart secondFinish)
    (hsubset :
      dualWalkCrossingEdges faceBoundary allFaces hunique firstWalk ⊆
        dualWalkCrossingEdges faceBoundary allFaces hunique secondWalk) :
    ∀ dualEdge ∈ firstWalk.edges, dualEdge ∈ secondWalk.edges := by
  intro dualEdge hdualEdge
  rcases List.get_of_mem hdualEdge with ⟨firstEdgeStep, hfirstGet⟩
  let firstStep : Fin firstWalk.length :=
    Fin.cast firstWalk.length_edges firstEdgeStep
  have hfirstCast :
      Fin.cast firstWalk.length_edges.symm firstStep = firstEdgeStep := by
    apply Fin.ext
    rfl
  let primalEdge :=
    dualWalkCrossingEdge faceBoundary allFaces hunique firstWalk firstStep
  have hfirstCrossing : primalEdge ∈
      dualWalkCrossingEdges faceBoundary allFaces hunique firstWalk :=
    (mem_dualWalkCrossingEdges_iff faceBoundary allFaces hunique firstWalk
      primalEdge).2 ⟨firstStep, rfl⟩
  have hsecondCrossing := hsubset hfirstCrossing
  rcases (mem_dualWalkCrossingEdges_iff faceBoundary allFaces hunique
      secondWalk primalEdge).1 hsecondCrossing with
    ⟨secondStep, hsecondPrimal⟩
  have hgraphEdge :=
    dualWalkGraphEdge_eq_of_two_walk_crossingEdge_eq faceBoundary allFaces
      hall hunique firstWalk secondWalk hsecondPrimal.symm
  have hsecondGet :
      secondWalk.edges.get
          (Fin.cast secondWalk.length_edges.symm secondStep) = dualEdge := by
    calc
      secondWalk.edges.get
          (Fin.cast secondWalk.length_edges.symm secondStep) =
          dualWalkGraphEdge faceBoundary allFaces secondWalk secondStep :=
        edges_get_dualWalkGraphEdge faceBoundary allFaces secondWalk
          secondStep
      _ = dualWalkGraphEdge faceBoundary allFaces firstWalk firstStep :=
        hgraphEdge.symm
      _ = firstWalk.edges.get
          (Fin.cast firstWalk.length_edges.symm firstStep) :=
        (edges_get_dualWalkGraphEdge faceBoundary allFaces firstWalk
          firstStep).symm
      _ = firstWalk.edges.get firstEdgeStep := by rw [hfirstCast]
      _ = dualEdge := hfirstGet
  rw [← hsecondGet]
  exact List.get_mem secondWalk.edges
    (Fin.cast secondWalk.length_edges.symm secondStep)

end GoertzelV24DualCycleChordCrossing

namespace GoertzelV24DualCycleCollar

/-- If two incident faces form an edge of a facial-dual walk, their shared
primal edge occurs among that walk's crossings. -/
theorem mem_dualWalkCrossingEdges_of_shared_primal_edge_of_mem_walk_edges
    (data : Data G)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace data.toRotationSystem)))
    {start finish : AmbientFace
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    (walk : (interiorDualGraph
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace data.toRotationSystem))).Walk start finish)
    {edge : G.edgeSet}
    {leftFace rightFace : AmbientFace
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    (hfacesNe : leftFace ≠ rightFace)
    (hleftBoundary : edge ∈
      orbitFaceBoundary data.toRotationSystem leftFace.1)
    (hrightBoundary : edge ∈
      orbitFaceBoundary data.toRotationSystem rightFace.1)
    (hwalkEdge : s(leftFace, rightFace) ∈ walk.edges) :
    edge ∈ dualWalkCrossingEdges
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem)) hunique
        walk := by
  by_contra hnotCrossing
  have hchord := isChord_of_shared_primal_edge_not_mem_crossings
    data hunique walk
      (walk.fst_mem_support_of_mem_edges hwalkEdge)
      (walk.snd_mem_support_of_mem_edges hwalkEdge) hfacesNe hleftBoundary
      hrightBoundary hnotCrossing
  exact (SimpleGraph.Walk.isChord_sym2Mk.1 hchord).2.1 hwalkEdge

/-- The two chord triangles of an exact adjacent-pair collar both cross
the internal primal edge, and their full crossing sets are distinct. -/
theorem exists_internal_chord_two_triangles_with_distinct_crossings_of_adjacent_pair_boundary_eq
    (data : Data G) (hcubic : data.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic data.toRotationSystem)
    (htwoSided : OrbitFacesTwoSided data.toRotationSystem)
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
    {first second : V} (hadj : G.Adj first second)
    (hboundary :
      crossingEdgeFinset G
          (fun vertex => vertex ∈ ({first, second} : Set V)) =
        dualWalkCrossingEdges
          (orbitFaceBoundary data.toRotationSystem)
          (Finset.univ : Finset (OrbitFace data.toRotationSystem))
          hunique walk) :
    let removed := dualWalkCrossingEdges
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem)) hunique walk
    ∃ internalEdge : G.edgeSet,
      ∃ leftFace rightFace : AmbientFace
          (Finset.univ : Finset (OrbitFace data.toRotationSystem)),
        ∃ firstTriangle secondTriangle :
            (interiorDualGraph
              (orbitFaceBoundary data.toRotationSystem)
              (Finset.univ : Finset
                (OrbitFace data.toRotationSystem))).Walk leftFace leftFace,
          internalEdge.1 = s(first, second) ∧
            internalEdge ∉ removed ∧
            internalEdge ∈
              orbitFaceBoundary data.toRotationSystem leftFace.1 ∧
            internalEdge ∈
              orbitFaceBoundary data.toRotationSystem rightFace.1 ∧
            firstTriangle.IsCycle ∧ firstTriangle.length = 3 ∧
            secondTriangle.IsCycle ∧ secondTriangle.length = 3 ∧
            internalEdge ∈ dualWalkCrossingEdges
              (orbitFaceBoundary data.toRotationSystem)
              (Finset.univ : Finset
                (OrbitFace data.toRotationSystem)) hunique firstTriangle ∧
            internalEdge ∈ dualWalkCrossingEdges
              (orbitFaceBoundary data.toRotationSystem)
              (Finset.univ : Finset
                (OrbitFace data.toRotationSystem)) hunique secondTriangle ∧
            dualWalkCrossingEdges
                (orbitFaceBoundary data.toRotationSystem)
                (Finset.univ : Finset
                  (OrbitFace data.toRotationSystem)) hunique firstTriangle ≠
              dualWalkCrossingEdges
                (orbitFaceBoundary data.toRotationSystem)
                (Finset.univ : Finset
                  (OrbitFace data.toRotationSystem)) hunique
                    secondTriangle := by
  dsimp only
  rcases exists_internal_chord_two_triangles_of_adjacent_pair_boundary_eq
      data hcubic hrotation htwoSided hunique walk hcycle hlength hadj
        hboundary with
    ⟨internalEdge, leftFace, rightFace, firstTriangle, secondTriangle,
      hproperties⟩
  have hinternalValue := hproperties.1
  have hinternalNotRemoved := hproperties.2.1
  have hleftBoundary := hproperties.2.2.1
  have hrightBoundary := hproperties.2.2.2.1
  have hchord := hproperties.2.2.2.2.1
  have hfirstCycle := hproperties.2.2.2.2.2.1
  have hfirstLength := hproperties.2.2.2.2.2.2.1
  have hsecondCycle := hproperties.2.2.2.2.2.2.2.1
  have hsecondLength := hproperties.2.2.2.2.2.2.2.2.1
  have hfirstChord := hproperties.2.2.2.2.2.2.2.2.2.1
  have hsecondChord := hproperties.2.2.2.2.2.2.2.2.2.2.1
  have hfirstOnlyWitness := hproperties.2.2.2.2.2.2.2.2.2.2.2
  let firstOnly := Classical.choose hfirstOnlyWitness
  have hfirstOnly := (Classical.choose_spec hfirstOnlyWitness).1
  have hfirstOnlyNotSecond := (Classical.choose_spec hfirstOnlyWitness).2
  have hfacesNe : leftFace ≠ rightFace :=
    (SimpleGraph.Walk.isChord_sym2Mk.1 hchord).1.ne
  have hfirstInternal :=
    mem_dualWalkCrossingEdges_of_shared_primal_edge_of_mem_walk_edges
      data hunique firstTriangle hfacesNe hleftBoundary hrightBoundary
        hfirstChord
  have hsecondInternal :=
    mem_dualWalkCrossingEdges_of_shared_primal_edge_of_mem_walk_edges
      data hunique secondTriangle hfacesNe hleftBoundary hrightBoundary
        hsecondChord
  have hcrossingsNe :
      dualWalkCrossingEdges
          (orbitFaceBoundary data.toRotationSystem)
          (Finset.univ : Finset
            (OrbitFace data.toRotationSystem)) hunique firstTriangle ≠
        dualWalkCrossingEdges
          (orbitFaceBoundary data.toRotationSystem)
          (Finset.univ : Finset
            (OrbitFace data.toRotationSystem)) hunique secondTriangle := by
    intro hcrossings
    apply hfirstOnlyNotSecond
    apply
      GoertzelV24DualCycleChordCrossing.walk_edges_subset_of_crossingEdges_subset
        (orbitFaceBoundary data.toRotationSystem)
        (Finset.univ : Finset (OrbitFace data.toRotationSystem))
        (orbitFace_incidence_le_two data.toRotationSystem) hunique
          firstTriangle secondTriangle
    · rw [hcrossings]
    · exact hfirstOnly
  exact ⟨internalEdge, leftFace, rightFace, firstTriangle, secondTriangle,
    hinternalValue, hinternalNotRemoved, hleftBoundary, hrightBoundary,
    hfirstCycle, hfirstLength, hsecondCycle, hsecondLength,
    hfirstInternal, hsecondInternal, hcrossingsNe⟩

end GoertzelV24DualCycleCollar

namespace GoertzelV24DualCycleSeparator

/-- The two chord triangles of an exact adjacent-pair collar cut off the
two endpoint stars, in one of the two possible triangle orders. -/
theorem exists_chord_triangle_singleton_components_of_adjacent_pair_boundary_eq
    (data : Data G) (hregular : G.IsRegularOfDegree 3)
    (hconnected : G.Connected) (hcyclic : CyclicallyFiveEdgeConnected G)
    (hrotation : VertexRotationCyclic data.toRotationSystem)
    (htwoSided : OrbitFacesTwoSided data.toRotationSystem)
    (hdual : (interiorDualGraph
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace data.toRotationSystem))).Connected)
    (hsphere : OrbitSphericalCubicMapData data.toRotationSystem)
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
    {first second : V} (hadj : G.Adj first second)
    (hboundary :
      crossingEdgeFinset G
          (fun vertex => vertex ∈ ({first, second} : Set V)) =
        dualWalkCrossingEdges
          (orbitFaceBoundary data.toRotationSystem)
          (Finset.univ : Finset (OrbitFace data.toRotationSystem))
          hunique walk) :
    let removed := dualWalkCrossingEdges
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem)) hunique walk
    ∃ internalEdge : G.edgeSet,
      ∃ leftFace rightFace : AmbientFace
          (Finset.univ : Finset (OrbitFace data.toRotationSystem)),
        ∃ firstTriangle secondTriangle :
            (interiorDualGraph
              (orbitFaceBoundary data.toRotationSystem)
              (Finset.univ : Finset
                (OrbitFace data.toRotationSystem))).Walk leftFace leftFace,
          ∃ firstComponent :
              (G.deleteEdges
                (dualWalkPrimalCut data hunique
                  firstTriangle)).ConnectedComponent,
            ∃ secondComponent :
                (G.deleteEdges
                  (dualWalkPrimalCut data hunique
                    secondTriangle)).ConnectedComponent,
              internalEdge.1 = s(first, second) ∧
                internalEdge ∉ removed ∧
                internalEdge ∈
                  orbitFaceBoundary data.toRotationSystem leftFace.1 ∧
                internalEdge ∈
                  orbitFaceBoundary data.toRotationSystem rightFace.1 ∧
                firstTriangle.IsCycle ∧ firstTriangle.length = 3 ∧
                secondTriangle.IsCycle ∧ secondTriangle.length = 3 ∧
                crossingEdgeFinset G
                    (fun vertex => vertex ∈ firstComponent.supp) =
                  dualWalkCrossingEdges
                    (orbitFaceBoundary data.toRotationSystem)
                    (Finset.univ : Finset
                      (OrbitFace data.toRotationSystem)) hunique
                        firstTriangle ∧
                crossingEdgeFinset G
                    (fun vertex => vertex ∈ secondComponent.supp) =
                  dualWalkCrossingEdges
                    (orbitFaceBoundary data.toRotationSystem)
                    (Finset.univ : Finset
                      (OrbitFace data.toRotationSystem)) hunique
                        secondTriangle ∧
                ((firstComponent.supp = {first} ∧
                    secondComponent.supp = {second}) ∨
                  (firstComponent.supp = {second} ∧
                    secondComponent.supp = {first})) ∧
                internalEdge ∈ dualWalkCrossingEdges
                  (orbitFaceBoundary data.toRotationSystem)
                  (Finset.univ : Finset
                    (OrbitFace data.toRotationSystem)) hunique
                      firstTriangle ∧
                internalEdge ∈ dualWalkCrossingEdges
                  (orbitFaceBoundary data.toRotationSystem)
                  (Finset.univ : Finset
                    (OrbitFace data.toRotationSystem)) hunique
                      secondTriangle ∧
                dualWalkCrossingEdges
                    (orbitFaceBoundary data.toRotationSystem)
                    (Finset.univ : Finset
                      (OrbitFace data.toRotationSystem)) hunique
                        firstTriangle ≠
                  dualWalkCrossingEdges
                    (orbitFaceBoundary data.toRotationSystem)
                    (Finset.univ : Finset
                      (OrbitFace data.toRotationSystem)) hunique
                        secondTriangle := by
  dsimp only
  rcases
      GoertzelV24DualCycleCollar.exists_internal_chord_two_triangles_with_distinct_crossings_of_adjacent_pair_boundary_eq
        data (data.toRotationSystem_isCubic_iff.mpr hregular) hrotation
          htwoSided hunique walk hcycle hlength hadj hboundary with
    ⟨internalEdge, leftFace, rightFace, firstTriangle, secondTriangle,
      hinternalValue, hinternalNotRemoved, hleftBoundary,
      hrightBoundary, hfirstCycle, hfirstLength, hsecondCycle,
      hsecondLength, hfirstInternal, hsecondInternal, hcrossingsNe⟩
  have hfirstDelete :
      ¬ (G.deleteEdges
        (dualWalkPrimalCut data hunique firstTriangle)).Connected :=
    not_connected_deleteEdges_dualWalkPrimalCut_of_isCycle data htwoSided
      hdual hconnected hsphere hunique firstTriangle hfirstCycle
  have hsecondDelete :
      ¬ (G.deleteEdges
        (dualWalkPrimalCut data hunique secondTriangle)).Connected :=
    not_connected_deleteEdges_dualWalkPrimalCut_of_isCycle data htwoSided
      hdual hconnected hsphere hunique secondTriangle hsecondCycle
  rcases
      exists_primalCut_component_card_eq_one_and_boundary_eq_of_isCycle_of_length_eq_three
        data hregular hconnected hcyclic hunique firstTriangle hfirstCycle
          hfirstLength hfirstDelete with
    ⟨firstComponent, hfirstCard, hfirstBoundary⟩
  rcases
      exists_primalCut_component_card_eq_one_and_boundary_eq_of_isCycle_of_length_eq_three
        data hregular hconnected hcyclic hunique secondTriangle hsecondCycle
          hsecondLength hsecondDelete with
    ⟨secondComponent, hsecondCard, hsecondBoundary⟩
  have hfirstSuppNcard : firstComponent.supp.ncard = 1 := by
    rw [← Nat.card_coe_set_eq]
    exact hfirstCard
  have hsecondSuppNcard : secondComponent.supp.ncard = 1 := by
    rw [← Nat.card_coe_set_eq]
    exact hsecondCard
  rcases Set.ncard_eq_one.mp hfirstSuppNcard with
    ⟨firstVertex, hfirstSupp⟩
  rcases Set.ncard_eq_one.mp hsecondSuppNcard with
    ⟨secondVertex, hsecondSupp⟩
  have hfirstEndpoint : firstVertex = first ∨ firstVertex = second := by
    have hinternalBoundary : internalEdge ∈
        crossingEdgeFinset G
          (fun vertex => vertex ∈ firstComponent.supp) := by
      rw [hfirstBoundary]
      exact hfirstInternal
    rcases (mem_crossingEdgeFinset_iff
        (fun vertex => vertex ∈ firstComponent.supp) internalEdge).1
          hinternalBoundary with
      ⟨inside, _outside, hinsideEdge, _houtsideEdge, hinsideSide,
        _houtsideSide⟩
    rw [hfirstSupp] at hinsideSide
    have hinsideVertex : inside = firstVertex := by
      simpa using hinsideSide
    have hinsidePair : inside = first ∨ inside = second := by
      rw [hinternalValue] at hinsideEdge
      simpa [Sym2.mem_iff] using hinsideEdge
    rcases hinsidePair with hinsideFirst | hinsideSecond
    · exact Or.inl (hinsideVertex.symm.trans hinsideFirst)
    · exact Or.inr (hinsideVertex.symm.trans hinsideSecond)
  have hsecondEndpoint : secondVertex = first ∨ secondVertex = second := by
    have hinternalBoundary : internalEdge ∈
        crossingEdgeFinset G
          (fun vertex => vertex ∈ secondComponent.supp) := by
      rw [hsecondBoundary]
      exact hsecondInternal
    rcases (mem_crossingEdgeFinset_iff
        (fun vertex => vertex ∈ secondComponent.supp) internalEdge).1
          hinternalBoundary with
      ⟨inside, _outside, hinsideEdge, _houtsideEdge, hinsideSide,
        _houtsideSide⟩
    rw [hsecondSupp] at hinsideSide
    have hinsideVertex : inside = secondVertex := by
      simpa using hinsideSide
    have hinsidePair : inside = first ∨ inside = second := by
      rw [hinternalValue] at hinsideEdge
      simpa [Sym2.mem_iff] using hinsideEdge
    rcases hinsidePair with hinsideFirst | hinsideSecond
    · exact Or.inl (hinsideVertex.symm.trans hinsideFirst)
    · exact Or.inr (hinsideVertex.symm.trans hinsideSecond)
  have hverticesNe : firstVertex ≠ secondVertex := by
    intro hvertices
    apply hcrossingsNe
    have hsides :
        (fun vertex => vertex ∈ firstComponent.supp) =
          (fun vertex => vertex ∈ secondComponent.supp) := by
      funext vertex
      simp [hfirstSupp, hsecondSupp, hvertices]
    calc
      dualWalkCrossingEdges
          (orbitFaceBoundary data.toRotationSystem)
          (Finset.univ : Finset
            (OrbitFace data.toRotationSystem)) hunique firstTriangle =
          crossingEdgeFinset G
            (fun vertex => vertex ∈ firstComponent.supp) :=
        hfirstBoundary.symm
      _ = crossingEdgeFinset G
            (fun vertex => vertex ∈ secondComponent.supp) := by
        rw [hsides]
      _ = dualWalkCrossingEdges
          (orbitFaceBoundary data.toRotationSystem)
          (Finset.univ : Finset
            (OrbitFace data.toRotationSystem)) hunique secondTriangle :=
        hsecondBoundary
  have horientation :
      (firstComponent.supp = {first} ∧
          secondComponent.supp = {second}) ∨
        (firstComponent.supp = {second} ∧
          secondComponent.supp = {first}) := by
    rcases hfirstEndpoint with hfirstEndpoint | hfirstEndpoint
    · rcases hsecondEndpoint with hsecondEndpoint | hsecondEndpoint
      · exact False.elim
          (hverticesNe (hfirstEndpoint.trans hsecondEndpoint.symm))
      · exact Or.inl ⟨hfirstSupp.trans (by rw [hfirstEndpoint]),
          hsecondSupp.trans (by rw [hsecondEndpoint])⟩
    · rcases hsecondEndpoint with hsecondEndpoint | hsecondEndpoint
      · exact Or.inr ⟨hfirstSupp.trans (by rw [hfirstEndpoint]),
          hsecondSupp.trans (by rw [hsecondEndpoint])⟩
      · exact False.elim
          (hverticesNe (hfirstEndpoint.trans hsecondEndpoint.symm))
  exact ⟨internalEdge, leftFace, rightFace, firstTriangle, secondTriangle,
    firstComponent, secondComponent, hinternalValue,
    hinternalNotRemoved, hleftBoundary, hrightBoundary, hfirstCycle,
    hfirstLength, hsecondCycle,
    hsecondLength, hfirstBoundary, hsecondBoundary, horientation,
    hfirstInternal, hsecondInternal, hcrossingsNe⟩

end GoertzelV24DualCycleSeparator

end

end Mettapedia.GraphTheory.FourColor
