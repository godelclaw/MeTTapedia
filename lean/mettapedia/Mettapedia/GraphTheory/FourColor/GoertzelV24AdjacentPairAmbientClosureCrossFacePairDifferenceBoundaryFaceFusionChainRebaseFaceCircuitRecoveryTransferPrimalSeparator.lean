import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairAmbientClosureCrossFacePairDifferenceBoundaryFaceFusionChainRebaseFaceCircuitRecoveryTransferPrimalCycle
import Mettapedia.GraphTheory.FourColor.GoertzelV24SharedFacesThreeEdgeSeparator

namespace Mettapedia.GraphTheory.FourColor

open GoertzelV24DualPathTransversal
open GoertzelV24FaceBoundaryLinearAlgebra
open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24OrbitFaceCurvatureBulk
open GoertzelV24OrbitFaceCycleSpaceEquality
open GoertzelV24OrbitFaceTwoSided
open GoertzelV24PrimalCycleSpace
open GoertzelV24SharedFacesTwoEdgeSeparator
open GoertzelV24WalkCycleParity
open SimpleGraph
open SimpleGraphDartRotation

variable {V E : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E]

noncomputable section

namespace GoertzelV24DualCycleSeparator

omit [Fintype V] [DecidableEq V] in
/-- Cyclic successor of a dual-cycle step reads the same vertex as the
ordinary next walk position, including the closing step. -/
private theorem getVert_succ_eq_getVert_finRotate
    {H : SimpleGraph V} {start : V}
    (walk : H.Walk start start)
    (hcycle : walk.IsCycle)
    (step : Fin walk.length) :
    walk.getVert (step.val + 1) =
      walk.getVert (finRotate walk.length step).val := by
  have hpositive : 0 < walk.length :=
    lt_of_lt_of_le (by omega) hcycle.three_le_length
  have hone : 1 < walk.length :=
    lt_of_lt_of_le (by omega) hcycle.three_le_length
  letI : NeZero walk.length := ⟨Nat.ne_of_gt hpositive⟩
  by_cases hnext : step.val + 1 < walk.length
  · have hrotate : (finRotate walk.length step).val = step.val + 1 := by
      rw [finRotate_apply, Fin.val_add, Fin.val_one',
        Nat.mod_eq_of_lt hone, Nat.mod_eq_of_lt hnext]
    rw [hrotate]
  · have hlast : step.val + 1 = walk.length := by omega
    have hrotate : (finRotate walk.length step).val = 0 := by
      rw [finRotate_apply, Fin.val_add, Fin.val_one',
        Nat.mod_eq_of_lt hone, hlast, Nat.mod_self]
    rw [hlast, hrotate, walk.getVert_length, walk.getVert_zero]

/-- A facial-boundary linear combination evaluated on one dual-cycle
crossing is the sum of its values on the two incident faces. -/
theorem orbitFaceBoundaryLinearMap_apply_dualWalkCrossingEdge
    (RS : RotationSystem V E)
    (htwoSided : OrbitFacesTwoSided RS)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS)))
    {start : AmbientFace
      (Finset.univ : Finset (OrbitFace RS))}
    (walk : (interiorDualGraph
      (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS))).Walk start start)
    (step : Fin walk.length)
    (coefficients : OrbitFace RS → F2) :
    orbitFaceBoundaryLinearMap RS coefficients
        (dualWalkCrossingEdge
          (orbitFaceBoundary RS)
          (Finset.univ : Finset (OrbitFace RS)) hunique walk step) =
      coefficients (walk.getVert step.val).1 +
        coefficients (walk.getVert (step.val + 1)).1 := by
  let left := walk.getVert step.val
  let right := walk.getVert (step.val + 1)
  let edge := dualWalkCrossingEdge
    (orbitFaceBoundary RS)
    (Finset.univ : Finset (OrbitFace RS)) hunique walk step
  have hadj := walk.adj_getVert_succ step.isLt
  have hfaces : left.1 ≠ right.1 := by
    intro hface
    exact hadj.ne (Subtype.ext hface)
  have hleft : edge ∈ orbitFaceBoundary RS left.1 :=
    dualWalkCrossingEdge_mem_leftFace
      (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS)) hunique walk step
  have hright : edge ∈ orbitFaceBoundary RS right.1 :=
    dualWalkCrossingEdge_mem_rightFace
      (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS)) hunique walk step
  have hincident := orbitFace_incidentFaces_eq_pair_of_mem
    RS htwoSided hfaces edge hleft hright
  rw [orbitFaceBoundaryLinearMap_apply]
  calc
    (∑ face : OrbitFace RS,
        if edge ∈ orbitFaceBoundary RS face then
          coefficients face else 0) =
        ∑ face ∈ (Finset.univ.filter fun face : OrbitFace RS =>
          edge ∈ orbitFaceBoundary RS face), coefficients face := by
      rw [Finset.sum_filter]
    _ = ∑ face ∈ ({left.1, right.1} : Finset (OrbitFace RS)),
        coefficients face := by rw [hincident]
    _ = coefficients left.1 + coefficients right.1 := by
      simp [hfaces]

/-- The total coordinate of all primal crossings of a simple dual cycle
vanishes in every facial-boundary linear combination. -/
theorem sum_orbitFaceBoundaryLinearMap_dualCycle_eq_zero
    (RS : RotationSystem V E)
    (htwoSided : OrbitFacesTwoSided RS)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS)))
    {start : AmbientFace
      (Finset.univ : Finset (OrbitFace RS))}
    (walk : (interiorDualGraph
      (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS))).Walk start start)
    (hcycle : walk.IsCycle)
    (coefficients : OrbitFace RS → F2) :
    (∑ step : Fin walk.length,
      orbitFaceBoundaryLinearMap RS coefficients
        (dualWalkCrossingEdge
          (orbitFaceBoundary RS)
          (Finset.univ : Finset (OrbitFace RS)) hunique walk step)) = 0 := by
  simp_rw [orbitFaceBoundaryLinearMap_apply_dualWalkCrossingEdge
    RS htwoSided hunique walk]
  rw [Finset.sum_add_distrib]
  have hshift :
      (∑ step : Fin walk.length,
        coefficients (walk.getVert (step.val + 1)).1) =
      ∑ step : Fin walk.length,
        coefficients (walk.getVert step.val).1 := by
    calc
      (∑ step : Fin walk.length,
          coefficients (walk.getVert (step.val + 1)).1) =
          ∑ step : Fin walk.length,
            coefficients
              (walk.getVert (finRotate walk.length step).val).1 := by
        apply Finset.sum_congr rfl
        intro step _hstep
        rw [getVert_succ_eq_getVert_finRotate walk hcycle step]
      _ = ∑ step : Fin walk.length,
          coefficients (walk.getVert step.val).1 :=
        Equiv.sum_comp (finRotate walk.length)
          (fun step : Fin walk.length =>
            coefficients (walk.getVert step.val).1)
  rw [hshift]
  simp

variable {G : SimpleGraph V} [DecidableRel G.Adj]

local instance graphEdgeSetDecidableEq (G : SimpleGraph V) :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

/-- Consequently every primal graph cycle meets the crossing set of a
simple facial-dual cycle with even parity. -/
theorem f2CycleSpace_sum_crossings_eq_zero_of_dualCycle
    (data : Data G)
    (htwoSided : OrbitFacesTwoSided data.toRotationSystem)
    (hdual : (interiorDualGraph
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace data.toRotationSystem))).Connected)
    (hconnected : G.Connected)
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
    (hdualCycle : walk.IsCycle)
    {cycle : G.edgeSet → F2}
    (hcycle : cycle ∈ f2CycleSpace G) :
    (∑ step : Fin walk.length,
      cycle (dualWalkCrossingEdge
        (orbitFaceBoundary data.toRotationSystem)
        (Finset.univ : Finset
          (OrbitFace data.toRotationSystem)) hunique walk step)) = 0 := by
  have hspan : cycle ∈ LinearMap.range
      (orbitFaceBoundaryLinearMap data.toRotationSystem) := by
    rw [range_orbitFaceBoundaryLinearMap_eq_f2CycleSpace
      data htwoSided hdual hconnected hsphere]
    exact hcycle
  rcases hspan with ⟨coefficients, rfl⟩
  exact sum_orbitFaceBoundaryLinearMap_dualCycle_eq_zero
    data.toRotationSystem htwoSided hunique walk hdualCycle coefficients

/-- The primal edge set crossed by a facial-dual walk, viewed in the
ambient simple graph. -/
def dualWalkPrimalCut
    (data : Data G)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace data.toRotationSystem)))
    {start : AmbientFace
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    (walk : (interiorDualGraph
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace data.toRotationSystem))).Walk start start) :
    Set (Sym2 V) :=
  {edge | ∃ step : Fin walk.length,
    (dualWalkCrossingEdge
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace data.toRotationSystem)) hunique walk step).1 = edge}

/-- The primal cut is exactly the range of the position-indexed crossing
map. -/
theorem dualWalkPrimalCut_eq_range
    (data : Data G)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace data.toRotationSystem)))
    {start : AmbientFace
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    (walk : (interiorDualGraph
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace data.toRotationSystem))).Walk start start) :
    dualWalkPrimalCut data hunique walk =
      Set.range (fun step : Fin walk.length =>
        (dualWalkCrossingEdge
          (orbitFaceBoundary data.toRotationSystem)
          (Finset.univ : Finset
            (OrbitFace data.toRotationSystem)) hunique walk step).1) := by
  ext edge
  simp [dualWalkPrimalCut]

/-- A simple dual cycle of length `n` induces a primal cut of exactly `n`
ambient graph edges. -/
theorem ncard_dualWalkPrimalCut_eq_length_of_isCycle
    (data : Data G)
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
    (hdualCycle : walk.IsCycle) :
    (dualWalkPrimalCut data hunique walk).ncard = walk.length := by
  rw [dualWalkPrimalCut_eq_range]
  rw [Set.ncard_range_of_injective]
  · simp
  · exact Subtype.val_injective.comp
      (dualWalkCrossingEdge_injective_of_isCycle
        (orbitFaceBoundary data.toRotationSystem)
        (Finset.univ : Finset
          (OrbitFace data.toRotationSystem))
        (orbitFace_incidence_le_two data.toRotationSystem)
        hunique walk hdualCycle)

/-- The primal crossings of a simple closed facial-dual walk form an edge
separator. The proof is purely algebraic: every primal cycle has even
intersection with the crossings, whereas connectivity after deleting them
would close one crossing by a return walk that uses none of the others. -/
theorem not_connected_deleteEdges_dualWalkPrimalCut_of_isCycle
    (data : Data G)
    (htwoSided : OrbitFacesTwoSided data.toRotationSystem)
    (hdual : (interiorDualGraph
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace data.toRotationSystem))).Connected)
    (hconnected : G.Connected)
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
    (hdualCycle : walk.IsCycle) :
    ¬ (G.deleteEdges (dualWalkPrimalCut data hunique walk)).Connected := by
  intro hdeleteConnected
  let firstStep : Fin walk.length :=
    ⟨0, lt_of_lt_of_le (by omega) hdualCycle.three_le_length⟩
  let firstEdge : G.edgeSet :=
    dualWalkCrossingEdge
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace data.toRotationSystem)) hunique walk firstStep
  rcases data.toRotationSystem.dartsOn_nonempty firstEdge with ⟨dart, hdart⟩
  have hdartEdge : data.toRotationSystem.edgeOf dart = firstEdge :=
    (data.toRotationSystem.mem_dartsOn).1 hdart
  have hdartEdgeValue : dart.edge = firstEdge.1 :=
    congrArg Subtype.val hdartEdge
  rcases hdeleteConnected dart.snd dart.fst with ⟨returnWalkDeleted⟩
  let returnWalk : G.Walk dart.snd dart.fst :=
    returnWalkDeleted.mapLe
      (G.deleteEdges_le (dualWalkPrimalCut data hunique walk))
  have hreturnEdges : returnWalk.edges = returnWalkDeleted.edges := by
    exact returnWalkDeleted.edges_mapLe_eq_edges
      (G.deleteEdges_le (dualWalkPrimalCut data hunique walk))
  have hcrossingCut (step : Fin walk.length) :
      (dualWalkCrossingEdge
        (orbitFaceBoundary data.toRotationSystem)
        (Finset.univ : Finset
          (OrbitFace data.toRotationSystem)) hunique walk step).1 ∈
        dualWalkPrimalCut data hunique walk := by
    exact ⟨step, rfl⟩
  have hreturnAvoid (step : Fin walk.length) :
      (dualWalkCrossingEdge
        (orbitFaceBoundary data.toRotationSystem)
        (Finset.univ : Finset
          (OrbitFace data.toRotationSystem)) hunique walk step).1 ∉
        returnWalk.edges := by
    intro hmem
    have hdeleted := returnWalkDeleted.edges_subset_edgeSet
      (by simpa [hreturnEdges] using hmem)
    rw [SimpleGraph.edgeSet_deleteEdges] at hdeleted
    exact hdeleted.2 (hcrossingCut step)
  let closedWalk : G.Walk dart.fst dart.fst :=
    SimpleGraph.Walk.cons dart.adj returnWalk
  have hcycle : walkEdgeParity closedWalk ∈ f2CycleSpace G :=
    walkEdgeParity_mem_f2CycleSpace_of_closed closedWalk
  have hcoordinates :=
    f2CycleSpace_sum_crossings_eq_zero_of_dualCycle
      data htwoSided hdual hconnected hsphere hunique walk hdualCycle hcycle
  have hinjective := dualWalkCrossingEdge_injective_of_isCycle
    (orbitFaceBoundary data.toRotationSystem)
    (Finset.univ : Finset (OrbitFace data.toRotationSystem))
    (orbitFace_incidence_le_two data.toRotationSystem)
    hunique walk hdualCycle
  have hfirstCoordinate : walkEdgeParity closedWalk firstEdge = 1 := by
    have hreturnCount : returnWalk.edges.count firstEdge.1 = 0 :=
      List.count_eq_zero.2 (hreturnAvoid firstStep)
    have hdartPairValue : s(dart.fst, dart.snd) = firstEdge.1 :=
      hdartEdgeValue
    change ((List.count firstEdge.1
      (s(dart.fst, dart.snd) :: returnWalk.edges) : Nat) : F2) = 1
    simp [hdartPairValue, hreturnCount]
  have hotherCoordinate (step : Fin walk.length) (hne : step ≠ firstStep) :
      walkEdgeParity closedWalk
        (dualWalkCrossingEdge
          (orbitFaceBoundary data.toRotationSystem)
          (Finset.univ : Finset
            (OrbitFace data.toRotationSystem)) hunique walk step) = 0 := by
    let edge := dualWalkCrossingEdge
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace data.toRotationSystem)) hunique walk step
    have hreturnCount : returnWalk.edges.count edge.1 = 0 :=
      List.count_eq_zero.2 (hreturnAvoid step)
    have hdartPairNe : s(dart.fst, dart.snd) ≠ edge.1 := by
      intro heq
      apply hne
      apply hinjective
      apply Subtype.ext
      exact (hdartEdgeValue.symm.trans heq).symm
    change ((List.count edge.1
      (s(dart.fst, dart.snd) :: returnWalk.edges) : Nat) : F2) = 0
    simp [hdartPairNe, hreturnCount]
  have hsumOne :
      (∑ step : Fin walk.length,
        walkEdgeParity closedWalk
          (dualWalkCrossingEdge
            (orbitFaceBoundary data.toRotationSystem)
            (Finset.univ : Finset
              (OrbitFace data.toRotationSystem)) hunique walk step)) = 1 := by
    rw [Finset.sum_eq_single firstStep]
    · exact hfirstCoordinate
    · intro step _hstep hne
      exact hotherCoordinate step hne
    · intro hnot
      exact False.elim (hnot (Finset.mem_univ firstStep))
  rw [hsumOne] at hcoordinates
  exact one_ne_zero hcoordinates

end GoertzelV24DualCycleSeparator

open GoertzelV24AdjacentPairBoundary
open GoertzelV24AdjacentPairInsertion
open GoertzelV24FourDefectBoundary
open GoertzelV24TwoEdgeCutMinimality

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

namespace GoertzelV24AdjacentPairInsertion.AdjacentPairData

open GoertzelV24AdjacentPairBoundary.AdjacentPairData
open GoertzelV24FourDefectBoundary.DegreeTwoBoundaryData
open GoertzelV24MinimalFaceIntersections

attribute [local instance]
  fusionFaceNetworkGraphEdgeSetDecidableEq
  fusionFaceNetworkRetainedVertexFintype
  fusionFaceNetworkRetainedVertexDecidableEq

variable {graphData : Data G}
  {minimal : GraphBackedVertexMinimalTaitCounterexample graphData}
  {baseData : AdjacentPairData G}

namespace ClosureRecoveryFaceTransferCircuit

variable {rebaseCircuit :
  CrossCentralExactFaceCertifiedRebaseCircuit graphData minimal baseData}

/-- In a graph-backed minimal counterexample, no simple facial-dual cycle
can have a connected primal complement after all of its crossing edges are
deleted. -/
theorem primalCut_not_connected_of_isCycle
    {start : AmbientFace
      (Finset.univ : Finset (OrbitFace graphData.toRotationSystem))}
    (walk : (interiorDualGraph
      (orbitFaceBoundary graphData.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace graphData.toRotationSystem))).Walk start start)
    (hcycle : walk.IsCycle) :
    ¬ (G.deleteEdges
      (GoertzelV24DualCycleSeparator.dualWalkPrimalCut graphData
        (pairwiseUniqueSharedInteriorEdges graphData minimal) walk)).Connected := by
  have hconnected : G.Connected := by
    rw [← GoertzelV24SimpleGraphFaceDualConnectedness.rotationPrimalGraph_toRotationSystem_eq
      G graphData]
    exact minimal.primalConnected
  have hdual := orbitFaceInteriorDual_connected
    graphData.toRotationSystem minimal.spherical.cubic
      minimal.primalConnected minimal.vertexRotationCyclic
  exact GoertzelV24DualCycleSeparator.not_connected_deleteEdges_dualWalkPrimalCut_of_isCycle
    graphData minimal.facesTwoSided hdual hconnected minimal.spherical
      (pairwiseUniqueSharedInteriorEdges graphData minimal) walk hcycle

/-- Saturated recovery monodromy therefore produces a remote primal edge
separator whose exact size is the rebase-circuit length. -/
theorem exists_remote_primal_separator
    (circuit : ClosureRecoveryFaceTransferCircuit rebaseCircuit)
    (hminimal : circuit.IsLengthMinimal)
    (hlength : circuit.arcLength = rebaseCircuit.arcLength) :
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
          (pairwiseUniqueSharedInteriorEdges graphData minimal) walk).ncard =
            rebaseCircuit.arcLength ∧
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
  rcases circuit.exists_remote_isCycle_with_primalCrossing_injective
      hminimal hlength with
    ⟨walk, hcycle, _hinjective, hcrossingCard, hcentral, hboundary⟩
  have hseparator := primalCut_not_connected_of_isCycle
    (graphData := graphData) (minimal := minimal) walk hcycle
  have hcutCard :=
    GoertzelV24DualCycleSeparator.ncard_dualWalkPrimalCut_eq_length_of_isCycle
      graphData (pairwiseUniqueSharedInteriorEdges graphData minimal)
        walk hcycle
  have hcrossingLength :=
    GoertzelV24DualPathTransversal.card_dualWalkCrossingEdges_eq_length_of_isCycle
      (orbitFaceBoundary graphData.toRotationSystem)
      (Finset.univ : Finset (OrbitFace graphData.toRotationSystem))
      (orbitFace_incidence_le_two graphData.toRotationSystem)
      (pairwiseUniqueSharedInteriorEdges graphData minimal) walk hcycle
  have hwalkLength : walk.length = rebaseCircuit.arcLength :=
    hcrossingLength.symm.trans hcrossingCard
  exact ⟨walk, hcycle, hseparator, hcutCard.trans hwalkLength,
    hcentral, hboundary⟩

end ClosureRecoveryFaceTransferCircuit

end GoertzelV24AdjacentPairInsertion.AdjacentPairData

end

end Mettapedia.GraphTheory.FourColor
