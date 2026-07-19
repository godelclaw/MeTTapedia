import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairAmbientClosureCrossFacePairDifferenceBoundaryFaceFusionChainRebaseFaceCircuitPortPairingReductionKempeEscape
import Mettapedia.GraphTheory.FourColor.GoertzelV24DualPathTransversal

namespace Mettapedia.GraphTheory.FourColor

open GoertzelV24AdjacentPairBoundary
open GoertzelV24AdjacentPairInsertion
open GoertzelV24FaceOrbitIncidence
open GoertzelV24FourDefectBoundary
open GoertzelV24MinimalFaceIntersections
open GoertzelV24TwoEdgeCutMinimality
open SimpleGraph
open SimpleGraphDartRotation

variable {F E : Type*} [Fintype F] [DecidableEq F]
  [Fintype E] [DecidableEq E]

noncomputable section

namespace GoertzelV24DualPathTransversal

/-- The underlying dual-graph edge traversed at a walk position. -/
def dualWalkGraphEdge
    (faceBoundary : F → Finset E) (allFaces : Finset F)
    {start finish : AmbientFace allFaces}
    (walk : (interiorDualGraph faceBoundary allFaces).Walk start finish)
    (step : Fin walk.length) : Sym2 (AmbientFace allFaces) :=
  s(walk.getVert step.val, walk.getVert (step.val + 1))

/-- If two steps cross the same primal edge, then they traverse the same
unoriented edge of the facial dual. -/
theorem dualWalkGraphEdge_eq_of_crossingEdge_eq
    (faceBoundary : F → Finset E) (allFaces : Finset F)
    (hall : ∀ edge,
      totalIncidenceCount faceBoundary allFaces edge ≤ 2)
    (hunique : PairwiseUniqueSharedInteriorEdges faceBoundary allFaces)
    {start finish : AmbientFace allFaces}
    (walk : (interiorDualGraph faceBoundary allFaces).Walk start finish)
    {first second : Fin walk.length}
    (hedges : dualWalkCrossingEdge faceBoundary allFaces hunique walk first =
      dualWalkCrossingEdge faceBoundary allFaces hunique walk second) :
    dualWalkGraphEdge faceBoundary allFaces walk first =
      dualWalkGraphEdge faceBoundary allFaces walk second := by
  let firstLeft := walk.getVert first.val
  let firstRight := walk.getVert (first.val + 1)
  let secondLeft := walk.getVert second.val
  let secondRight := walk.getVert (second.val + 1)
  have hfirstAdj := walk.adj_getVert_succ first.isLt
  have hsecondAdj := walk.adj_getVert_succ second.isLt
  have hfirstFaces : firstLeft.1 ≠ firstRight.1 := by
    intro hfaces
    exact hfirstAdj.ne (Subtype.ext hfaces)
  have hsecondFaces : secondLeft.1 ≠ secondRight.1 := by
    intro hfaces
    exact hsecondAdj.ne (Subtype.ext hfaces)
  have hfirstLeft :
      dualWalkCrossingEdge faceBoundary allFaces hunique walk first ∈
        faceBoundary firstLeft.1 :=
    dualWalkCrossingEdge_mem_leftFace faceBoundary allFaces hunique walk first
  have hfirstRight :
      dualWalkCrossingEdge faceBoundary allFaces hunique walk first ∈
        faceBoundary firstRight.1 :=
    dualWalkCrossingEdge_mem_rightFace faceBoundary allFaces hunique walk first
  have hsecondLeft :
      dualWalkCrossingEdge faceBoundary allFaces hunique walk first ∈
        faceBoundary secondLeft.1 := by
    rw [hedges]
    exact dualWalkCrossingEdge_mem_leftFace faceBoundary allFaces hunique
      walk second
  have hsecondRight :
      dualWalkCrossingEdge faceBoundary allFaces hunique walk first ∈
        faceBoundary secondRight.1 := by
    rw [hedges]
    exact dualWalkCrossingEdge_mem_rightFace faceBoundary allFaces hunique
      walk second
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

omit [Fintype F] [DecidableEq F] [Fintype E] in
/-- Positional reading of the dual graph edge agrees with positional
reading of the walk's edge list. -/
theorem edges_get_dualWalkGraphEdge
    (faceBoundary : F → Finset E) (allFaces : Finset F)
    {start finish : AmbientFace allFaces}
    (walk : (interiorDualGraph faceBoundary allFaces).Walk start finish)
    (step : Fin walk.length) :
    let edgeStep : Fin walk.edges.length :=
      Fin.cast walk.length_edges.symm step
    walk.edges.get edgeStep =
      dualWalkGraphEdge faceBoundary allFaces walk step := by
  dsimp only
  simp [dualWalkGraphEdge, SimpleGraph.Walk.edges,
    List.get_eq_getElem, SimpleGraph.Walk.darts_getElem_eq_getVert]

/-- A simple facial-dual cycle crosses distinct primal edges. -/
theorem dualWalkCrossingEdge_injective_of_isCycle
    (faceBoundary : F → Finset E) (allFaces : Finset F)
    (hall : ∀ edge,
      totalIncidenceCount faceBoundary allFaces edge ≤ 2)
    (hunique : PairwiseUniqueSharedInteriorEdges faceBoundary allFaces)
    {start : AmbientFace allFaces}
    (walk : (interiorDualGraph faceBoundary allFaces).Walk start start)
    (hcycle : walk.IsCycle) :
    Function.Injective
      (dualWalkCrossingEdge faceBoundary allFaces hunique walk) := by
  intro first second hedges
  have hgraphEdge := dualWalkGraphEdge_eq_of_crossingEdge_eq
    faceBoundary allFaces hall hunique walk hedges
  have hinjective : Function.Injective walk.edges.get :=
    List.nodup_iff_injective_get.mp hcycle.edges_nodup
  let first' : Fin walk.edges.length :=
    Fin.cast walk.length_edges.symm first
  let second' : Fin walk.edges.length :=
    Fin.cast walk.length_edges.symm second
  have hget : walk.edges.get first' = walk.edges.get second' := by
    rw [edges_get_dualWalkGraphEdge faceBoundary allFaces walk first,
      edges_get_dualWalkGraphEdge faceBoundary allFaces walk second]
    exact hgraphEdge
  exact Fin.cast_injective walk.length_edges.symm (hinjective hget)

/-- A simple dual cycle of length `n` therefore crosses exactly `n`
distinct primal edges. -/
theorem card_dualWalkCrossingEdges_eq_length_of_isCycle
    (faceBoundary : F → Finset E) (allFaces : Finset F)
    (hall : ∀ edge,
      totalIncidenceCount faceBoundary allFaces edge ≤ 2)
    (hunique : PairwiseUniqueSharedInteriorEdges faceBoundary allFaces)
    {start : AmbientFace allFaces}
    (walk : (interiorDualGraph faceBoundary allFaces).Walk start start)
    (hcycle : walk.IsCycle) :
    (dualWalkCrossingEdges faceBoundary allFaces hunique walk).card =
      walk.length := by
  rw [dualWalkCrossingEdges,
    Finset.card_image_of_injective _
      (dualWalkCrossingEdge_injective_of_isCycle faceBoundary allFaces hall
        hunique walk hcycle),
    Finset.card_univ, Fintype.card_fin]

end GoertzelV24DualPathTransversal

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

namespace GoertzelV24AdjacentPairInsertion.AdjacentPairData

open GoertzelV24AdjacentPairBoundary.AdjacentPairData
open GoertzelV24FourDefectBoundary.DegreeTwoBoundaryData

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

/-- The saturated remote dual cycle crosses an injectively indexed set of
primal edges whose cardinality is the rebase-circuit length. -/
theorem exists_remote_isCycle_with_primalCrossing_injective
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
        Function.Injective
          (GoertzelV24DualPathTransversal.dualWalkCrossingEdge
            (orbitFaceBoundary graphData.toRotationSystem)
            (Finset.univ : Finset
              (OrbitFace graphData.toRotationSystem))
            (pairwiseUniqueSharedInteriorEdges graphData minimal) walk) ∧
        (GoertzelV24DualPathTransversal.dualWalkCrossingEdges
          (orbitFaceBoundary graphData.toRotationSystem)
          (Finset.univ : Finset
            (OrbitFace graphData.toRotationSystem))
          (pairwiseUniqueSharedInteriorEdges graphData minimal) walk).card =
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
  rcases circuit.exists_isCycle_closedDualWalk_of_saturated
      hminimal hlength with ⟨walk, hcycle, hsupport⟩
  have hinjective :=
    GoertzelV24DualPathTransversal.dualWalkCrossingEdge_injective_of_isCycle
      (orbitFaceBoundary graphData.toRotationSystem)
      (Finset.univ : Finset (OrbitFace graphData.toRotationSystem))
      (orbitFace_incidence_le_two graphData.toRotationSystem)
      (pairwiseUniqueSharedInteriorEdges graphData minimal) walk hcycle
  have hcard :=
    GoertzelV24DualPathTransversal.card_dualWalkCrossingEdges_eq_length_of_isCycle
      (orbitFaceBoundary graphData.toRotationSystem)
      (Finset.univ : Finset (OrbitFace graphData.toRotationSystem))
      (orbitFace_incidence_le_two graphData.toRotationSystem)
      (pairwiseUniqueSharedInteriorEdges graphData minimal) walk hcycle
  have hwalkLength : walk.length = rebaseCircuit.arcLength := by
    have hsupportLength := walk.length_support
    rw [hsupport] at hsupportLength
    simp [CrossCentralExactFaceCertifiedRebaseCircuit.cyclicDualFaces]
      at hsupportLength
    rw [rebaseCircuit.arcLength_eq_rest_length_add_one]
    omega
  have hcentral : ∀ face ∈ walk.support,
      centralEdge
          (baseData.rotationOrderedData graphData minimal.spherical.cubic
            minimal.vertexRotationCyclic) ∉
        orbitFaceBoundary graphData.toRotationSystem face.1 := by
    intro face hface
    apply rebaseCircuit.central_not_mem_of_mem_cyclicDualFaces
    rwa [← hsupport]
  have hboundary : ∀ face ∈ walk.support, ∀ port : Fin 4,
      boundaryEdge
          (baseData.rotationOrderedData graphData minimal.spherical.cubic
            minimal.vertexRotationCyclic) port ∉
        orbitFaceBoundary graphData.toRotationSystem face.1 := by
    intro face hface port
    apply rebaseCircuit.boundary_not_mem_of_mem_cyclicDualFaces
    rwa [← hsupport]
  refine ⟨walk, hcycle, hinjective, hcard.trans hwalkLength,
    hcentral, hboundary⟩

end ClosureRecoveryFaceTransferCircuit

end GoertzelV24AdjacentPairInsertion.AdjacentPairData

end

end Mettapedia.GraphTheory.FourColor
