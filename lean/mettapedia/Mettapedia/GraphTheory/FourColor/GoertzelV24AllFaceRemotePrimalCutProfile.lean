import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairAmbientClosureCrossFacePairDifferenceBoundaryFaceFusionChainRebaseFaceCircuitRemoteDualCycleReentryOrbitKempeState

namespace Mettapedia.GraphTheory.FourColor

open GoertzelV24AdjacentPairBoundary
open GoertzelV24AdjacentPairInsertion
open GoertzelV24CubicSmallBoundaryCycle
open GoertzelV24DualPathTransversal
open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24FourDefectBoundary
open GoertzelV24MinimalFaceIntersections
open GoertzelV24OrbitFaceTwoSided
open GoertzelV24RecoveredAdjacentPairData
open GoertzelV24RecoveredAdjacentPairFusionChainNormalForm
open GoertzelV24TwoEdgeCutMinimality
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

attribute [local instance]
  collarFiniteGraphLocallyFinite
  GoertzelV24DualCycleSeparator.graphEdgeSetDecidableEq

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

namespace CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle

variable {rebaseCircuit :
  CrossCentralExactFaceCertifiedRebaseCircuit graphData minimal baseData}

/-- The finite primal crossing set carried by a remote facial-dual cycle. -/
abbrev crossingEdges
    (cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit) : Finset G.edgeSet :=
  dualWalkCrossingEdges
    (orbitFaceBoundary graphData.toRotationSystem)
    (Finset.univ : Finset (OrbitFace graphData.toRotationSystem))
    (pairwiseUniqueSharedInteriorEdges graphData minimal) cycle.walk

/-- The set-valued primal edge cut carried by a remote facial-dual cycle. -/
abbrev primalCut
    (cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit) : Set (Sym2 V) :=
  GoertzelV24DualCycleSeparator.dualWalkPrimalCut graphData
    (pairwiseUniqueSharedInteriorEdges graphData minimal) cycle.walk

/-- A large remote profile records an exact primal separator of size at
least five. -/
structure LongPrimalCutProfile
    (cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit) where
  length_ge_five : 5 ≤ cycle.walk.length
  primalCut_not_connected : ¬ (G.deleteEdges cycle.primalCut).Connected
  primalCut_ncard_eq_length : cycle.primalCut.ncard = cycle.walk.length

/-- A remote dual triangle cuts off a singleton primal component. -/
structure SingletonPrimalCutProfile
    (cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit) where
  length_eq_three : cycle.walk.length = 3
  component : (G.deleteEdges cycle.primalCut).ConnectedComponent
  component_card_eq_one :
    Nat.card {vertex : V // vertex ∈ component.supp} = 1
  component_boundary_eq :
    crossingEdgeFinset G (fun vertex => vertex ∈ component.supp) =
      cycle.crossingEdges

/-- A remote dual four-cycle cuts off an exact adjacent-pair collar.  Its
internal primal edge is an off-cycle chord between two support faces. -/
structure AdjacentPairPrimalCutProfile
    (cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit) where
  length_eq_four : cycle.walk.length = 4
  component : (G.deleteEdges cycle.primalCut).ConnectedComponent
  firstVertex : V
  secondVertex : V
  first_ne_second : firstVertex ≠ secondVertex
  component_support_eq : component.supp = {firstVertex, secondVertex}
  adjacent : G.Adj firstVertex secondVertex
  component_boundary_eq :
    crossingEdgeFinset G (fun vertex => vertex ∈ component.supp) =
      cycle.crossingEdges
  first_boundary_card_eq_two :
    (cycle.crossingEdges ∩ incidentEdgeFinset G firstVertex).card = 2
  second_boundary_card_eq_two :
    (cycle.crossingEdges ∩ incidentEdgeFinset G secondVertex).card = 2
  internalEdge : G.edgeSet
  leftFace : AmbientFace
    (Finset.univ : Finset (OrbitFace graphData.toRotationSystem))
  rightFace : AmbientFace
    (Finset.univ : Finset (OrbitFace graphData.toRotationSystem))
  internalEdge_value : internalEdge.1 = s(firstVertex, secondVertex)
  internalEdge_not_crossing : internalEdge ∉ cycle.crossingEdges
  leftFace_mem_support : leftFace ∈ cycle.walk.support
  rightFace_mem_support : rightFace ∈ cycle.walk.support
  leftFace_ne_rightFace : leftFace ≠ rightFace
  internalEdge_mem_leftFace :
    internalEdge ∈ orbitFaceBoundary graphData.toRotationSystem leftFace.1
  internalEdge_mem_rightFace :
    internalEdge ∈ orbitFaceBoundary graphData.toRotationSystem rightFace.1
  dual_adjacent :
    (interiorDualGraph
      (orbitFaceBoundary graphData.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace graphData.toRotationSystem))).Adj leftFace rightFace

/-- The exhaustive primal scope of a remote facial-dual cycle in a
vertex-minimal counterexample. -/
inductive PrimalCutScopeProfile
    (cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit) : Prop
  | long (profile : cycle.LongPrimalCutProfile)
  | singleton (profile : cycle.SingletonPrimalCutProfile)
  | adjacentPair (profile : cycle.AdjacentPairPrimalCutProfile)

/-- Every crossed primal edge is different from the restored central
edge. -/
theorem crossingEdge_ne_central
    (cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit)
    {edge : G.edgeSet} (hedge : edge ∈ cycle.crossingEdges) :
    centralEdge (RecoveredRotationOrderedData graphData minimal baseData) ≠
      edge := by
  rcases (mem_dualWalkCrossingEdges_iff
      (orbitFaceBoundary graphData.toRotationSystem)
      (Finset.univ : Finset (OrbitFace graphData.toRotationSystem))
      (pairwiseUniqueSharedInteriorEdges graphData minimal)
      cycle.walk edge).1 hedge with ⟨step, hstep⟩
  have hedgeFace : edge ∈ orbitFaceBoundary graphData.toRotationSystem
      (cycle.walk.getVert step.val).1 := by
    rw [← hstep]
    exact dualWalkCrossingEdge_mem_leftFace
      (orbitFaceBoundary graphData.toRotationSystem)
      (Finset.univ : Finset (OrbitFace graphData.toRotationSystem))
      (pairwiseUniqueSharedInteriorEdges graphData minimal)
      cycle.walk step
  have hcentralOff := cycle.central_not_mem
    (cycle.walk.getVert step.val) (cycle.walk.getVert_mem_support step.val)
  intro heq
  exact hcentralOff (heq ▸ hedgeFace)

/-- Every crossed primal edge is different from each of the four restored
boundary edges. -/
theorem crossingEdge_ne_boundary
    (cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit)
    {edge : G.edgeSet} (hedge : edge ∈ cycle.crossingEdges)
    (port : Fin 4) :
    boundaryEdge
        (baseData.rotationOrderedData graphData minimal.spherical.cubic
          minimal.vertexRotationCyclic) port ≠ edge := by
  rcases (mem_dualWalkCrossingEdges_iff
      (orbitFaceBoundary graphData.toRotationSystem)
      (Finset.univ : Finset (OrbitFace graphData.toRotationSystem))
      (pairwiseUniqueSharedInteriorEdges graphData minimal)
      cycle.walk edge).1 hedge with ⟨step, hstep⟩
  have hedgeFace : edge ∈ orbitFaceBoundary graphData.toRotationSystem
      (cycle.walk.getVert step.val).1 := by
    rw [← hstep]
    exact dualWalkCrossingEdge_mem_leftFace
      (orbitFaceBoundary graphData.toRotationSystem)
      (Finset.univ : Finset (OrbitFace graphData.toRotationSystem))
      (pairwiseUniqueSharedInteriorEdges graphData minimal)
      cycle.walk step
  have hboundaryOff := cycle.boundary_not_mem
    (cycle.walk.getVert step.val) (cycle.walk.getVert_mem_support step.val)
      port
  intro heq
  exact hboundaryOff (heq ▸ hedgeFace)

/-- The internal edge of a remote adjacent-pair collar is different from
the restored central edge. -/
theorem AdjacentPairPrimalCutProfile.internalEdge_ne_central
    {cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit}
    (profile : cycle.AdjacentPairPrimalCutProfile) :
    centralEdge (RecoveredRotationOrderedData graphData minimal baseData) ≠
      profile.internalEdge := by
  intro heq
  exact cycle.central_not_mem profile.leftFace profile.leftFace_mem_support
    (heq ▸ profile.internalEdge_mem_leftFace)

/-- The internal edge of a remote adjacent-pair collar is different from
each restored boundary edge. -/
theorem AdjacentPairPrimalCutProfile.internalEdge_ne_boundary
    {cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit}
    (profile : cycle.AdjacentPairPrimalCutProfile) (port : Fin 4) :
    boundaryEdge
        (baseData.rotationOrderedData graphData minimal.spherical.cubic
          minimal.vertexRotationCyclic) port ≠ profile.internalEdge := by
  intro heq
  exact cycle.boundary_not_mem profile.leftFace profile.leftFace_mem_support
    port (heq ▸ profile.internalEdge_mem_leftFace)

/-- Cyclic five-edge-connectivity classifies every remote simple dual
cycle as an exact separator of size at least five, a singleton star, or an
adjacent-pair collar.  No face-size restriction is used. -/
theorem primalCutScopeProfile
    (cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit) :
    cycle.PrimalCutScopeProfile := by
  have hregular : G.IsRegularOfDegree 3 :=
    graphData.toRotationSystem_isCubic_iff.mp minimal.spherical.cubic
  have hconnected : G.Connected := by
    rw [← GoertzelV24SimpleGraphFaceDualConnectedness.rotationPrimalGraph_toRotationSystem_eq
      G graphData]
    exact minimal.primalConnected
  have hcyclic : CyclicallyFiveEdgeConnected G :=
    GoertzelV24FourEdgeCutGluing.cyclicallyFiveEdgeConnected_of_vertexMinimalTaitCounterexample
      graphData minimal
  have hdelete := cycle.primalCut_not_connected
  by_cases hlong : 5 ≤ cycle.walk.length
  · exact .long {
      length_ge_five := hlong
      primalCut_not_connected := hdelete
      primalCut_ncard_eq_length := cycle.ncard_primalCut_eq_length }
  · have hthree : 3 ≤ cycle.walk.length := cycle.isCycle.three_le_length
    have hsmall : cycle.walk.length = 3 ∨ cycle.walk.length = 4 := by
      omega
    rcases hsmall with hlength | hlength
    · have hprofile :=
        GoertzelV24DualCycleSeparator.exists_primalCut_component_card_eq_one_and_boundary_eq_of_isCycle_of_length_eq_three
          graphData hregular hconnected hcyclic
            (pairwiseUniqueSharedInteriorEdges graphData minimal)
              cycle.walk cycle.isCycle hlength hdelete
      dsimp only at hprofile
      rcases hprofile with ⟨component, hcard, hboundary⟩
      exact .singleton {
        length_eq_three := hlength
        component := component
        component_card_eq_one := hcard
        component_boundary_eq := hboundary }
    · have hprofile :=
        GoertzelV24DualCycleSeparator.exists_primalCut_adjacent_pair_collar_with_internal_dual_chord_of_isCycle_of_length_eq_four
          graphData hregular hconnected hcyclic minimal.vertexRotationCyclic
            minimal.facesTwoSided
            (pairwiseUniqueSharedInteriorEdges graphData minimal)
              cycle.walk cycle.isCycle hlength hdelete
      dsimp only at hprofile
      rcases hprofile with
        ⟨component, first, second, hne, hsupp, hadj, hboundary,
          hfirstCard, hsecondCard, internalEdge, leftFace, rightFace,
          hinternalValue, hinternalNotCrossing, hleftSupport,
          hrightSupport, hfaces, hleftBoundary, hrightBoundary,
          hdualAdjacent⟩
      exact .adjacentPair {
        length_eq_four := hlength
        component := component
        firstVertex := first
        secondVertex := second
        first_ne_second := hne
        component_support_eq := hsupp
        adjacent := hadj
        component_boundary_eq := hboundary
        first_boundary_card_eq_two := hfirstCard
        second_boundary_card_eq_two := hsecondCard
        internalEdge := internalEdge
        leftFace := leftFace
        rightFace := rightFace
        internalEdge_value := hinternalValue
        internalEdge_not_crossing := hinternalNotCrossing
        leftFace_mem_support := hleftSupport
        rightFace_mem_support := hrightSupport
        leftFace_ne_rightFace := hfaces
        internalEdge_mem_leftFace := hleftBoundary
        internalEdge_mem_rightFace := hrightBoundary
        dual_adjacent := hdualAdjacent }

end CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle

namespace CrossFaceAdjacentPairReentry

/-- A cross-face restart retains the exact scope of its remote primal cut,
or the literal recovery transfer that generated it. -/
def ScopedGeometry
    {targetEdge : G.edgeSet}
    (_reentry : CrossFaceAdjacentPairReentry graphData minimal baseData
      targetEdge) : Prop :=
  (∃ circuit : CrossCentralExactFaceCertifiedRebaseCircuit graphData
        minimal baseData,
      circuit.IsLengthMinimal ∧
        ∃ cycle :
            CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
              circuit,
          targetEdge ∈ cycle.crossingEdges ∧
            cycle.PrimalCutScopeProfile) ∨
    ∃ circuit : CrossCentralExactFaceCertifiedRebaseCircuit graphData
        minimal baseData,
      circuit.IsLengthMinimal ∧
        ∃ rotated : CrossCentralExactFaceCertifiedRebaseCircuit graphData
            minimal baseData,
          rotated.arcLength = circuit.arcLength ∧
            ∃ transfer : ClosureRecoveryFaceTransfer rotated,
              targetEdge = transfer.recovery.edge

/-- Every geometrically witnessed cross-face restart has scoped geometry. -/
theorem scopedGeometry
    {targetEdge : G.edgeSet}
    (reentry : CrossFaceAdjacentPairReentry graphData minimal baseData
      targetEdge) :
    reentry.ScopedGeometry := by
  rcases reentry.geometry with hremote | hrecovery
  · rcases hremote with ⟨circuit, hminimal, cycle, htarget⟩
    exact Or.inl
      ⟨circuit, hminimal, cycle, htarget, cycle.primalCutScopeProfile⟩
  · exact Or.inr hrecovery

end CrossFaceAdjacentPairReentry

/-- The scoped state-enriched cross-face relation retains the target Kempe
orbit and classifies every remote separator without a face-size premise. -/
def RotationOrderedFusionCrossFaceDartScopedKempeOrbitReentry
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (source target : G.Dart) : Prop :=
  RotationOrderedFusionCrossFaceDartKempeOrbitReentry graphData minimal
      source target ∧
    ∃ (baseData : AdjacentPairData G) (targetEdge : G.edgeSet),
      centralDart
          (RecoveredRotationOrderedData graphData minimal
            baseData).centralAdjacent = source ∧
        ∃ reentry : CrossFaceAdjacentPairReentry graphData minimal baseData
            targetEdge,
          reentry.ScopedGeometry ∧ targetEdge.1 = target.edge

/-- Every state-enriched cross-face step refines to the scoped relation. -/
theorem RotationOrderedFusionCrossFaceDartKempeOrbitReentry.toScoped
    {source target : G.Dart}
    (reentry : RotationOrderedFusionCrossFaceDartKempeOrbitReentry
      graphData minimal source target) :
    RotationOrderedFusionCrossFaceDartScopedKempeOrbitReentry
      graphData minimal source target := by
  refine ⟨reentry, ?_⟩
  rcases reentry.1 with
    ⟨baseData, targetEdge, hsource, htarget, hedge, _htargetFusion⟩
  exact ⟨baseData, targetEdge, hsource, htarget,
    htarget.scopedGeometry, hedge⟩

/-- Starting at any dart, the all-face machine reaches a structural target
or a nonempty closed orbit carrying both target Kempe states and scoped
remote-separator geometry. -/
theorem exists_reachable_rotationOrderedFusionStructuralTarget_or_crossFaceDartScopedKempeOrbitReentryCycle
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (start : G.Dart) :
    (∃ finish : G.Dart,
        Relation.ReflTransGen
            (RotationOrderedFusionCrossFaceDartScopedKempeOrbitReentry
              graphData minimal) start finish ∧
          RotationOrderedFusionStructuralTargetAtDart graphData minimal
            finish) ∨
      ∃ cycleDart : G.Dart,
        Relation.ReflTransGen
            (RotationOrderedFusionCrossFaceDartScopedKempeOrbitReentry
              graphData minimal) start cycleDart ∧
          Relation.TransGen
            (RotationOrderedFusionCrossFaceDartScopedKempeOrbitReentry
              graphData minimal) cycleDart cycleDart := by
  let refineStep := fun source target
      (step : RotationOrderedFusionCrossFaceDartKempeOrbitReentry
        graphData minimal source target) => step.toScoped
  rcases
      exists_reachable_rotationOrderedFusionStructuralTarget_or_crossFaceDartKempeOrbitReentryCycle
        graphData minimal start with
    hterminal | hcycle
  · rcases hterminal with ⟨finish, hreach, hfinish⟩
    exact Or.inl ⟨finish, hreach.mono refineStep, hfinish⟩
  · rcases hcycle with ⟨cycleDart, hreach, hclosed⟩
    exact Or.inr ⟨cycleDart, hreach.mono refineStep,
      hclosed.mono refineStep⟩

end GoertzelV24AdjacentPairInsertion.AdjacentPairData

end

end Mettapedia.GraphTheory.FourColor
