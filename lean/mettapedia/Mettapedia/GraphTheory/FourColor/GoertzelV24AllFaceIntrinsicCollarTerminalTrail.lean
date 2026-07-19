import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite
import Mettapedia.GraphTheory.FourColor.GoertzelV24AllFaceIntrinsicCollarTerminalSignature

/-! Scalar-support trails forced by the nonzero terminal signature of an
intrinsic singleton collar. -/

namespace Mettapedia.GraphTheory.FourColor

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

open GoertzelV24AdjacentPairBoundary
open GoertzelV24AdjacentPairInsertion
open GoertzelV24FourDefectBoundary
open GoertzelV24RecoveredAdjacentPairData
open GoertzelV24RecoveredAdjacentPairFusionChainNormalForm
open GoertzelV24SimpleGraphTaitBridge
open GoertzelV24TwoEdgeCutMinimality
open SimpleGraph
open SimpleGraphDartRotation

variable {W : Type*} [Fintype W] [DecidableEq W]
  {H : SimpleGraph W} [DecidableRel H.Adj]

noncomputable section

private theorem f2_eq_one_of_ne_zero (value : F2) (hvalue : value ≠ 0) :
    value = 1 := by
  fin_cases value
  · exact False.elim (hvalue rfl)
  · rfl

/-- A finite binary sum is the parity of its nonzero support. -/
theorem f2Sum_eq_supportCard {Edge : Type*} [DecidableEq Edge]
    (edges : Finset Edge) (chain : Edge → F2) :
    (∑ edge ∈ edges, chain edge) =
      (((edges.filter fun edge => chain edge ≠ 0).card : Nat) : F2) := by
  have hsupport :
      (∑ edge ∈ edges, chain edge) =
        ∑ edge ∈ edges.filter (fun edge => chain edge ≠ 0),
          chain edge := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro edge _hedge
    by_cases hzero : chain edge = 0 <;> simp [hzero]
  calc
    (∑ edge ∈ edges, chain edge) =
        ∑ edge ∈ edges.filter (fun edge => chain edge ≠ 0),
          chain edge := hsupport
    _ = ∑ _edge ∈ edges.filter (fun edge => chain edge ≠ 0),
          (1 : F2) := by
      apply Finset.sum_congr rfl
      intro edge hedge
      have hne : chain edge ≠ 0 := (Finset.mem_filter.mp hedge).2
      exact f2_eq_one_of_ne_zero (chain edge) hne
    _ = (((edges.filter fun edge => chain edge ≠ 0).card : Nat) : F2) := by
      simp

/-- A vertex is odd in the scalar support graph exactly when the binary
Kirchhoff boundary is nonzero there. -/
theorem scalarSupportGraph_degree_odd_iff
    (chain : H.edgeSet → F2) (vertex : W) :
    Odd ((scalarSupportGraph chain).degree vertex) ↔
      scalarVertexKirchhoffSum H chain vertex ≠ 0 := by
  rw [← incidentEdgeFinset_card_eq_degree,
    scalarSupportGraph_incidentEdgeFinset_card]
  rw [← ZMod.natCast_ne_zero_iff_odd]
  rw [← f2Sum_eq_supportCard
    (incidentEdgeFinset H vertex) chain]
  rfl

omit [Fintype W] [DecidableEq W] in
/-- Graph degree is independent of the chosen finite enumeration of the
same neighbor set. -/
theorem degree_eq_of_neighborFintypes (graph : SimpleGraph W) (vertex : W)
    (first second : Fintype (graph.neighborSet vertex)) :
    @SimpleGraph.degree W graph vertex first =
      @SimpleGraph.degree W graph vertex second := by
  classical
  unfold SimpleGraph.degree
  apply congrArg Finset.card
  ext neighbor
  simp [SimpleGraph.neighborFinset]

/-- A nonzero scalar boundary terminal is joined inside its scalar support
component to a distinct nonzero boundary terminal. -/
theorem exists_scalarSupportPath_to_distinct_boundary
    (chain : H.edgeSet → F2) (terminals : Finset W) (start : W)
    (hstartBoundary : scalarVertexKirchhoffSum H chain start ≠ 0)
    (hboundary : ∀ vertex : W,
      scalarVertexKirchhoffSum H chain vertex ≠ 0 →
        vertex ∈ terminals) :
    ∃ (finish : W),
      finish ∈ terminals ∧ finish ≠ start ∧
        scalarVertexKirchhoffSum H chain finish ≠ 0 ∧
        ∃ path : H.Walk start finish,
          path.IsPath ∧
            ∀ edge : H.edgeSet, (edge : Sym2 W) ∈ path.edges →
              chain edge ≠ 0 := by
  let support := scalarSupportGraph chain
  have hstartOdd : Odd (support.degree start) := by
    exact (scalarSupportGraph_degree_odd_iff chain start).2 hstartBoundary
  let component : support.ConnectedComponent :=
    support.connectedComponentMk start
  letI componentVertexFintype : Fintype component.supp :=
    Subtype.fintype _
  letI componentNeighborFintype
      (vertex : component.supp) :
      Fintype ((support.induce component.supp).neighborSet vertex) :=
    Subtype.fintype _
  have hstartComponent : start ∈ component.supp := by
    rfl
  let startInComponent : component.supp := ⟨start, hstartComponent⟩
  have hstartNeighbors : support.neighborSet start ⊆ component.supp := by
    intro vertex hadjacent
    exact component.mem_supp_of_adj_mem_supp hstartComponent hadjacent
  have hstartDegree :
      (support.induce component.supp).degree startInComponent =
        support.degree start := by
    have hinduced := SimpleGraph.degree_induce_of_neighborSet_subset
      (G := support) (s := component.supp) (v := startInComponent)
        hstartNeighbors
    exact hinduced.trans
      (degree_eq_of_neighborFintypes support start
        (Subtype.fintype _) inferInstance)
  have hstartInducedOdd :
      Odd ((support.induce component.supp).degree startInComponent) := by
    simpa [hstartDegree] using hstartOdd
  obtain ⟨finishInComponent, hfinishNe, hfinishInducedOdd⟩ :=
    (support.induce component.supp).exists_ne_odd_degree_of_exists_odd_degree
      startInComponent hstartInducedOdd
  have hfinishNeighbors :
      support.neighborSet finishInComponent.1 ⊆ component.supp := by
    intro vertex hadjacent
    exact component.mem_supp_of_adj_mem_supp
      finishInComponent.2 hadjacent
  have hfinishDegree :
      (support.induce component.supp).degree finishInComponent =
        support.degree finishInComponent.1 := by
    have hinduced := SimpleGraph.degree_induce_of_neighborSet_subset
      (G := support) (s := component.supp) (v := finishInComponent)
        hfinishNeighbors
    exact hinduced.trans
      (degree_eq_of_neighborFintypes support finishInComponent.1
        (Subtype.fintype _) inferInstance)
  have hfinishOdd : Odd (support.degree finishInComponent.1) := by
    simpa [hfinishDegree] using hfinishInducedOdd
  have hfinishBoundary :
      scalarVertexKirchhoffSum H chain finishInComponent.1 ≠ 0 := by
    exact (scalarSupportGraph_degree_odd_iff
      chain finishInComponent.1).1 hfinishOdd
  have hfinishDistinct : finishInComponent.1 ≠ start := by
    intro heq
    exact hfinishNe (Subtype.ext heq)
  have hreachable : support.Reachable start finishInComponent.1 :=
    component.reachable_of_mem_supp hstartComponent finishInComponent.2
  rcases hreachable.exists_isPath with ⟨supportPath, hsupportPath⟩
  let path : H.Walk start finishInComponent.1 :=
    supportPath.mapLe (scalarSupportGraph_le chain)
  have hpath : path.IsPath := by
    exact hsupportPath.mapLe (scalarSupportGraph_le chain)
  refine ⟨finishInComponent.1, hboundary _ hfinishBoundary,
    hfinishDistinct, hfinishBoundary, path, hpath, ?_⟩
  intro edge hedge
  have hedgePath : (edge : Sym2 W) ∈ supportPath.edges := by
    change (edge : Sym2 W) ∈
      (supportPath.mapLe (scalarSupportGraph_le chain)).edges at hedge
    rw [SimpleGraph.Walk.edges_mapLe_eq_edges] at hedge
    exact hedge
  have hedgeSupport :
      (edge : Sym2 W) ∈ (scalarSupportGraph chain).edgeSet :=
    supportPath.edges_subset_edgeSet hedgePath
  exact (ambientEdge_mem_scalarSupportGraph_edgeSet_iff chain edge).1
    hedgeSupport

namespace GoertzelV24AdjacentPairInsertion.AdjacentPairData

/-- Scalar projection commutes with the Kirchhoff boundary operator. -/
theorem scalarVertexKirchhoffSum_crossFaceCoordinate
    (chain : H.edgeSet → Color) (coordinate : Bool) (vertex : W) :
    scalarVertexKirchhoffSum H
        (fun edge => crossFaceCoordinate coordinate (chain edge)) vertex =
      crossFaceCoordinate coordinate
        (vertexKirchhoffSum H chain vertex) := by
  cases coordinate
  · exact scalarVertexKirchhoffSum_fst H chain vertex
  · exact scalarVertexKirchhoffSum_snd H chain vertex

/-- Every nonzero color has a nonzero binary coordinate. -/
theorem exists_crossFaceCoordinate_ne_zero
    (value : Color) (hvalue : value ≠ 0) :
    ∃ coordinate : Bool, crossFaceCoordinate coordinate value ≠ 0 := by
  by_cases hfirst : value.1 = 0
  · have hsecond : value.2 ≠ 0 := by
      intro hsecond
      exact hvalue (Prod.ext hfirst hsecond)
    exact ⟨true, hsecond⟩
  · exact ⟨false, hfirst⟩

open GoertzelV24AdjacentPairBoundary.AdjacentPairData

attribute [local instance]
  fusionFaceNetworkGraphEdgeSetDecidableEq
  fusionFaceNetworkRetainedVertexFintype
  fusionFaceNetworkRetainedVertexDecidableEq

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]
  {graphData : Data G}
  {minimal : GraphBackedVertexMinimalTaitCounterexample graphData}
  {baseData : AdjacentPairData G}

namespace CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle

variable {rebaseCircuit :
  CrossCentralExactFaceCertifiedRebaseCircuit graphData minimal baseData}

namespace IntrinsicShortTargetEscapeCollar

/-- Some target port based at the singleton endpoint carries nonzero
common-core discrepancy boundary. -/
theorem exists_singletonTargetPort_boundary_ne_zero
    {cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit}
    {targetEdge : G.edgeSet}
    {sourceNormal : RotationOrderedCyclicKempeFusionChainNormalForm
      graphData minimal baseData}
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge)
    (sourceEscape : sourceNormal.KempeOrbitAdjacentEscape) :
    ∃ targetPort : Fin 4,
      boundaryDeletedVertex collar.targetData targetPort ∈
          collar.singletonCutProfile.component.supp ∧
        vertexKirchhoffSum collar.commonCore
          (collar.commonDiscrepancy sourceEscape)
          (collar.targetPortInCommonCore targetPort) ≠ 0 := by
  rcases collar.singletonTargetPort_boundarySum_ne_zero sourceEscape with
      ⟨hfirstSingleton, hsum⟩ | ⟨hsecondSingleton, hsum⟩
  · have hinsideZero : boundaryDeletedVertex collar.targetData 0 ∈
        collar.singletonCutProfile.component.supp := by
      simpa [boundaryDeletedVertex] using hfirstSingleton
    have hinsideOne : boundaryDeletedVertex collar.targetData 1 ∈
        collar.singletonCutProfile.component.supp := by
      simpa [boundaryDeletedVertex] using hfirstSingleton
    by_cases hzero : vertexKirchhoffSum collar.commonCore
        (collar.commonDiscrepancy sourceEscape)
        (collar.targetPortInCommonCore 0) = 0
    · refine ⟨1, hinsideOne, ?_⟩
      intro hone
      exact hsum (by rw [hzero, hone, add_zero])
    · exact ⟨0, hinsideZero, hzero⟩
  · have hinsideTwo : boundaryDeletedVertex collar.targetData 2 ∈
        collar.singletonCutProfile.component.supp := by
      simpa [boundaryDeletedVertex] using hsecondSingleton
    have hinsideThree : boundaryDeletedVertex collar.targetData 3 ∈
        collar.singletonCutProfile.component.supp := by
      simpa [boundaryDeletedVertex] using hsecondSingleton
    by_cases htwo : vertexKirchhoffSum collar.commonCore
        (collar.commonDiscrepancy sourceEscape)
        (collar.targetPortInCommonCore 2) = 0
    · refine ⟨3, hinsideThree, ?_⟩
      intro hthree
      exact hsum (by rw [htwo, hthree, add_zero])
    · exact ⟨2, hinsideTwo, htwo⟩

/-- The nonzero singleton terminal launches an honest simple trail in one
binary discrepancy coordinate.  The trail stays inside the exact common
core, ends at a distinct named terminal, and every one of its edges changes
that coordinate between the source and target escape colorings. -/
theorem exists_singletonTerminal_coordinateSupportPath
    {cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit}
    {targetEdge : G.edgeSet}
    {sourceNormal : RotationOrderedCyclicKempeFusionChainNormalForm
      graphData minimal baseData}
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge)
    (sourceEscape : sourceNormal.KempeOrbitAdjacentEscape) :
    ∃ (coordinate : Bool) (targetPort : Fin 4)
        (finish : collar.commonPortVertexFinset)
        (path : collar.commonCore.Walk
          (collar.targetPortInCommonCore targetPort) finish.1),
      boundaryDeletedVertex collar.targetData targetPort ∈
          collar.singletonCutProfile.component.supp ∧
        finish ≠ collar.targetPortCommonTerminal targetPort ∧
        crossFaceCoordinate coordinate
            ((collar.commonDiscrepancyBoundaryState sourceEscape).1
              (collar.targetPortCommonTerminal targetPort)) ≠ 0 ∧
        crossFaceCoordinate coordinate
            ((collar.commonDiscrepancyBoundaryState sourceEscape).1
              finish) ≠ 0 ∧
        path.IsPath ∧
        ∀ edge : collar.commonCore.edgeSet,
          (edge : Sym2 collar.commonCoreVertex) ∈ path.edges →
            crossFaceCoordinate coordinate
              (collar.commonDiscrepancy sourceEscape edge) ≠ 0 := by
  rcases collar.exists_singletonTargetPort_boundary_ne_zero sourceEscape with
    ⟨targetPort, hinside, hstartColor⟩
  rcases exists_crossFaceCoordinate_ne_zero _ hstartColor with
    ⟨coordinate, hstartCoordinate⟩
  let scalarChain : collar.commonCore.edgeSet → F2 :=
    fun edge => crossFaceCoordinate coordinate
      (collar.commonDiscrepancy sourceEscape edge)
  have hstartBoundary : scalarVertexKirchhoffSum collar.commonCore
      scalarChain (collar.targetPortInCommonCore targetPort) ≠ 0 := by
    rw [scalarVertexKirchhoffSum_crossFaceCoordinate]
    exact hstartCoordinate
  have hboundary : ∀ vertex : collar.commonCoreVertex,
      scalarVertexKirchhoffSum collar.commonCore scalarChain vertex ≠ 0 →
        vertex ∈ collar.commonPortVertexFinset := by
    intro vertex hscalar
    by_contra hterminal
    apply hscalar
    rw [scalarVertexKirchhoffSum_crossFaceCoordinate,
      collar.vertexKirchhoffSum_commonDiscrepancy_eq_zero_of_not_mem_commonPortVertexFinset
        sourceEscape vertex hterminal]
    cases coordinate <;> rfl
  rcases exists_scalarSupportPath_to_distinct_boundary scalarChain
      collar.commonPortVertexFinset
      (collar.targetPortInCommonCore targetPort) hstartBoundary
      hboundary with
    ⟨finishVertex, hfinishMem, hfinishNe, hfinishBoundary,
      path, hpath, hpathSupport⟩
  let finish : collar.commonPortVertexFinset :=
    ⟨finishVertex, hfinishMem⟩
  have hfinishCoordinate : crossFaceCoordinate coordinate
      (vertexKirchhoffSum collar.commonCore
        (collar.commonDiscrepancy sourceEscape) finishVertex) ≠ 0 := by
    rw [← scalarVertexKirchhoffSum_crossFaceCoordinate]
    exact hfinishBoundary
  refine ⟨coordinate, targetPort, finish, path, hinside, ?_, ?_, ?_,
    hpath, ?_⟩
  · intro heq
    apply hfinishNe
    exact congrArg Subtype.val heq
  · simpa only [commonDiscrepancyBoundaryState_apply,
      targetPortCommonTerminal] using
      hstartCoordinate
  · simpa only [commonDiscrepancyBoundaryState_apply, finish] using
      hfinishCoordinate
  · intro edge hedge
    exact hpathSupport edge hedge

end IntrinsicShortTargetEscapeCollar

end CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle

end GoertzelV24AdjacentPairInsertion.AdjacentPairData

end

end Mettapedia.GraphTheory.FourColor
