import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairAmbientClosureCrossFacePairDifferenceBoundaryFaceFusionChainRebaseFaceCircuitRecoveryTransferFaceCycle

namespace Mettapedia.GraphTheory.FourColor

open GoertzelV24AdjacentPairBoundary
open GoertzelV24AdjacentPairInsertion
open GoertzelV24FaceOrbitIncidence
open GoertzelV24FourDefectBoundary
open GoertzelV24TwoEdgeCutMinimality
open SimpleGraph
open SimpleGraphDartRotation

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

namespace GoertzelV24AdjacentPairInsertion.AdjacentPairData

open GoertzelV24AdjacentPairBoundary.AdjacentPairData
open GoertzelV24FourDefectBoundary.DegreeTwoBoundaryData

attribute [local instance]
  fusionFaceNetworkGraphEdgeSetDecidableEq
  fusionFaceNetworkRetainedVertexFintype
  fusionFaceNetworkRetainedVertexDecidableEq

/-- The two planar endpoint pairings produced by deleting a shared edge
from complementary exact-cut trails.  Both constructors retain their
simple ambient cycle closures and strict total-length decrease. -/
inductive LocalizedStrictPortPairingDescent
    {graphData : Data G} {data : AdjacentPairData G}
    (pair : RetainedIntersectionExactFaceCutPair graphData data)
    (oldCross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet)
    (face : OrbitFace graphData.toRotationSystem) : Type (u + 1) where
  | sameSide
      (descent : LocalizedStrictlyShorterSameSidePaths pair oldCross face)
  | mixedPort
      (descent : LocalizedStrictlyShorterMixedPortCycles pair oldCross face)

namespace LocalizedStrictPortPairingDescent

/-- The square reduction whose two seam pairs are connected by the strict
paths: `01|23` for the same-side constructor and `12|30` for the mixed-port
constructor. -/
def reductionSide
    {graphData : Data G} {data : AdjacentPairData G}
    {pair : RetainedIntersectionExactFaceCutPair graphData data}
    {oldCross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    {face : OrbitFace graphData.toRotationSystem}
    (descent : LocalizedStrictPortPairingDescent pair oldCross face) :
    SquareReductionSide :=
  match descent with
  | .sameSide _ => SquareReductionSide.join01_23
  | .mixedPort _ => SquareReductionSide.join12_30

/-- The two strict paths, indexed in the ordered seam coordinates of their
associated noncrossing square reduction. -/
def seamPath
    {graphData : Data G} {data : AdjacentPairData G}
    {pair : RetainedIntersectionExactFaceCutPair graphData data}
    {oldCross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    {face : OrbitFace graphData.toRotationSystem}
    (descent : LocalizedStrictPortPairingDescent pair oldCross face)
    (step : Fin 2) :
    (DeletedAdjacentPairGraph G data.firstVertex data.secondVertex).Walk
      (data.retainedPort (descent.reductionSide.leftPort step))
      (data.retainedPort (descent.reductionSide.rightPort step)) := by
  cases descent with
  | sameSide same =>
      refine Fin.cases ?_ (fun remaining => ?_) step
      · simpa [reductionSide, SquareReductionSide.leftPort,
          SquareReductionSide.rightPort,
          SquareReductionSide.join01_23] using same.zeroToOnePath.reverse
      · refine Fin.cases ?_ (fun impossible => Fin.elim0 impossible) remaining
        simpa [reductionSide, SquareReductionSide.leftPort,
          SquareReductionSide.rightPort,
          SquareReductionSide.join01_23] using same.twoToThreePath
  | mixedPort mixed =>
      refine Fin.cases ?_ (fun remaining => ?_) step
      · simpa [reductionSide, SquareReductionSide.leftPort,
          SquareReductionSide.rightPort,
          SquareReductionSide.join01_23,
          SquareReductionSide.join12_30] using mixed.zeroToThreePath
      · refine Fin.cases ?_ (fun impossible => Fin.elim0 impossible) remaining
        simpa [reductionSide, SquareReductionSide.leftPort,
          SquareReductionSide.rightPort,
          SquareReductionSide.join01_23,
          SquareReductionSide.join12_30] using mixed.oneToTwoPath

/-- Both seam-coordinate paths are simple. -/
theorem seamPath_isPath
    {graphData : Data G} {data : AdjacentPairData G}
    {pair : RetainedIntersectionExactFaceCutPair graphData data}
    {oldCross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    {face : OrbitFace graphData.toRotationSystem}
    (descent : LocalizedStrictPortPairingDescent pair oldCross face)
    (step : Fin 2) :
    (descent.seamPath step).IsPath := by
  cases descent with
  | sameSide same =>
      fin_cases step
      · exact same.zeroToOne_isPath.reverse
      · exact same.twoToThree_isPath
  | mixedPort mixed =>
      fin_cases step
      · exact mixed.zeroToThree_isPath
      · exact mixed.oneToTwo_isPath

/-- The retained facial edge removed by either strict splice. -/
def selectedEdge
    {graphData : Data G} {data : AdjacentPairData G}
    {pair : RetainedIntersectionExactFaceCutPair graphData data}
    {oldCross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    {face : OrbitFace graphData.toRotationSystem}
    (descent : LocalizedStrictPortPairingDescent pair oldCross face) :
    (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet :=
  match descent with
  | .sameSide same => same.selectedEdge
  | .mixedPort mixed => mixed.selectedEdge

/-- The splice edge differs from the cross of the preceding exact state. -/
theorem selectedEdge_ne_oldCross
    {graphData : Data G} {data : AdjacentPairData G}
    {pair : RetainedIntersectionExactFaceCutPair graphData data}
    {oldCross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    {face : OrbitFace graphData.toRotationSystem}
    (descent : LocalizedStrictPortPairingDescent pair oldCross face) :
    descent.selectedEdge ≠ oldCross := by
  cases descent with
  | sameSide same => exact same.selectedEdge_ne_oldCross
  | mixedPort mixed => exact mixed.selectedEdge_ne_oldCross

/-- The splice edge lies on the selected ambient face. -/
theorem selectedAmbientEdge_mem_face
    {graphData : Data G} {data : AdjacentPairData G}
    {pair : RetainedIntersectionExactFaceCutPair graphData data}
    {oldCross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    {face : OrbitFace graphData.toRotationSystem}
    (descent : LocalizedStrictPortPairingDescent pair oldCross face) :
    retainedEdgeToAmbientEdge data descent.selectedEdge ∈
      orbitFaceBoundary graphData.toRotationSystem face := by
  cases descent with
  | sameSide same => exact same.selectedAmbientEdge_mem_face
  | mixedPort mixed => exact mixed.selectedAmbientEdge_mem_face

/-- The removed facial edge occurs on neither seam-coordinate path. -/
theorem selectedEdge_not_mem_seamPath
    {graphData : Data G} {data : AdjacentPairData G}
    {pair : RetainedIntersectionExactFaceCutPair graphData data}
    {oldCross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    {face : OrbitFace graphData.toRotationSystem}
    (descent : LocalizedStrictPortPairingDescent pair oldCross face)
    (step : Fin 2) :
    descent.selectedEdge.1 ∉ (descent.seamPath step).edges := by
  cases descent with
  | sameSide same =>
      fin_cases step
      · change same.selectedEdge.1 ∉ same.zeroToOnePath.reverse.edges
        simpa only [SimpleGraph.Walk.edges_reverse, List.mem_reverse] using
          same.selectedEdge_not_mem_zeroToOnePath
      · change same.selectedEdge.1 ∉ same.twoToThreePath.edges
        exact
          same.selectedEdge_not_mem_twoToThreePath
  | mixedPort mixed =>
      fin_cases step
      · change mixed.selectedEdge.1 ∉ mixed.zeroToThreePath.edges
        exact
          mixed.selectedEdge_not_mem_zeroToThreePath
      · change mixed.selectedEdge.1 ∉ mixed.oneToTwoPath.edges
        exact
          mixed.selectedEdge_not_mem_oneToTwoPath

/-- Sum of the two reduced path lengths, independent of which planar
pairing occurs. -/
def totalPathLength
    {graphData : Data G} {data : AdjacentPairData G}
    {pair : RetainedIntersectionExactFaceCutPair graphData data}
    {oldCross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    {face : OrbitFace graphData.toRotationSystem}
    (descent : LocalizedStrictPortPairingDescent pair oldCross face) : Nat :=
  match descent with
  | .sameSide same =>
      same.zeroToOnePath.length + same.twoToThreePath.length
  | .mixedPort mixed =>
      mixed.zeroToThreePath.length + mixed.oneToTwoPath.length

/-- Either planar pairing is strictly shorter than its two source trails. -/
theorem totalPathLength_lt
    {graphData : Data G} {data : AdjacentPairData G}
    {pair : RetainedIntersectionExactFaceCutPair graphData data}
    {oldCross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    {face : OrbitFace graphData.toRotationSystem}
    (descent : LocalizedStrictPortPairingDescent pair oldCross face) :
    descent.totalPathLength <
      pair.prefixTrail.length + pair.suffixTrail.length := by
  cases descent with
  | sameSide same => exact same.total_length_lt
  | mixedPort mixed => exact mixed.total_length_lt

/-- The two ordered seam paths account for exactly the unified path-length
measure. -/
theorem seamPath_length_add
    {graphData : Data G} {data : AdjacentPairData G}
    {pair : RetainedIntersectionExactFaceCutPair graphData data}
    {oldCross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    {face : OrbitFace graphData.toRotationSystem}
    (descent : LocalizedStrictPortPairingDescent pair oldCross face) :
    (descent.seamPath 0).length + (descent.seamPath 1).length =
      descent.totalPathLength := by
  cases descent with
  | sameSide same =>
      change same.zeroToOnePath.reverse.length +
        same.twoToThreePath.length = _
      simp [totalPathLength]
  | mixedPort mixed =>
      change mixed.zeroToThreePath.length + mixed.oneToTwoPath.length = _
      rfl

end LocalizedStrictPortPairingDescent

/-- The signed singleton theorem as one compositional planar-pairing
descent, rather than a disjunction of two geometric record types. -/
theorem CrossCentralExactFaceRebaseStep.target_strictPortPairingDescent
    {graphData : Data G} {data : AdjacentPairData G}
    {source : CrossCentralExactFaceCutChannelState graphData data}
    {firstRoot secondRoot : V}
    {firstFusion : G.Walk firstRoot firstRoot}
    {secondFusion : G.Walk secondRoot secondRoot}
    {successors : LocalizedFusionSuccessorResolution source.pair source.face
      firstFusion secondFusion}
    (step : CrossCentralExactFaceRebaseStep graphData data source successors) :
    let pair := step.targetRetainedIntersectionProfile
    Nonempty (LocalizedStrictPortPairingDescent pair source.cross
      source.face) := by
  rcases
      step.target_strictlyShorterSameSidePaths_or_strictlyShorterMixedPortCycles
    with hsame | hmixed
  · rcases hsame with ⟨same⟩
    exact ⟨.sameSide same⟩
  · rcases hmixed with ⟨mixed⟩
    exact ⟨.mixedPort mixed⟩

/-- Minimal-counterexample provenance is preserved by the unified descent. -/
theorem CrossCentralExactFaceCertifiedRebaseStep.target_strictPortPairingDescent
    {graphData : Data G}
    {minimal : GraphBackedVertexMinimalTaitCounterexample graphData}
    {baseData : AdjacentPairData G}
    {source : CrossCentralExactFaceCutState graphData
      (baseData.rotationOrderedData graphData minimal.spherical.cubic
        minimal.vertexRotationCyclic)}
    (step : CrossCentralExactFaceCertifiedRebaseStep graphData minimal
      baseData source) :
    Nonempty (LocalizedStrictPortPairingDescent
      step.target.retainedIntersectionProfile source.1 step.selectedFace) := by
  rcases
      step.target_strictlyShorterSameSidePaths_or_strictlyShorterMixedPortCycles
    with hsame | hmixed
  · rcases hsame with ⟨same⟩
    exact ⟨.sameSide same⟩
  · rcases hmixed with ⟨mixed⟩
    exact ⟨.mixedPort mixed⟩

/-- A fixed-face transition supplies strict planar-pairing descent at its
complete target state. -/
theorem CrossCentralExactFaceCertifiedRebaseTransitionOnFace.target_strictPortPairingDescent
    {graphData : Data G}
    {minimal : GraphBackedVertexMinimalTaitCounterexample graphData}
    {baseData : AdjacentPairData G}
    {face : OrbitFace graphData.toRotationSystem}
    {source target : CrossCentralExactFaceCutState graphData
      (baseData.rotationOrderedData graphData minimal.spherical.cubic
        minimal.vertexRotationCyclic)}
    (transition : CrossCentralExactFaceCertifiedRebaseTransitionOnFace
      graphData minimal baseData face source target) :
    Nonempty (LocalizedStrictPortPairingDescent
      target.retainedIntersectionProfile source.1 face) := by
  rcases transition with ⟨step, htarget, hface⟩
  rw [← htarget, ← hface]
  exact step.target_strictPortPairingDescent

/-- Every certified facial arc therefore ends in one strict noncrossing
port pairing. -/
theorem CrossCentralExactFaceCertifiedRebaseArc.target_strictPortPairingDescent
    {graphData : Data G}
    {minimal : GraphBackedVertexMinimalTaitCounterexample graphData}
    {baseData : AdjacentPairData G}
    (arc : CrossCentralExactFaceCertifiedRebaseArc graphData minimal
      baseData) :
    Nonempty (LocalizedStrictPortPairingDescent
      arc.target.retainedIntersectionProfile arc.source.1
        arc.selectedFace) :=
  arc.transition.target_strictPortPairingDescent

namespace CrossCentralExactFaceCertifiedRebaseInvolutionCell

variable {graphData : Data G}
  {minimal : GraphBackedVertexMinimalTaitCounterexample graphData}
  {baseData : AdjacentPairData G}

/-- Both endpoints of a constant-face involution cell carry the unified
strict port-pairing descent, oriented away from the other endpoint. -/
def EndpointStrictPortPairingDescent
    (cell : CrossCentralExactFaceCertifiedRebaseInvolutionCell graphData
      minimal baseData) : Prop :=
  Nonempty (LocalizedStrictPortPairingDescent
      cell.source.retainedIntersectionProfile cell.target.1 cell.face) ∧
    Nonempty (LocalizedStrictPortPairingDescent
      cell.target.retainedIntersectionProfile cell.source.1 cell.face)

theorem endpoint_strictPortPairingDescent
    (cell : CrossCentralExactFaceCertifiedRebaseInvolutionCell graphData
      minimal baseData) :
    cell.EndpointStrictPortPairingDescent := by
  rcases cell.endpoint_strictDescent_normalForm with
    ⟨hsource, htarget⟩
  constructor
  · rcases hsource with hsame | hmixed
    · rcases hsame with ⟨same⟩
      exact ⟨.sameSide same⟩
    · rcases hmixed with ⟨mixed⟩
      exact ⟨.mixedPort mixed⟩
  · rcases htarget with hsame | hmixed
    · rcases hsame with ⟨same⟩
      exact ⟨.sameSide same⟩
    · rcases hmixed with ⟨mixed⟩
      exact ⟨.mixedPort mixed⟩

end CrossCentralExactFaceCertifiedRebaseInvolutionCell

namespace CrossCentralExactFaceCertifiedRebaseCircuit

variable {graphData : Data G}
  {minimal : GraphBackedVertexMinimalTaitCounterexample graphData}
  {baseData : AdjacentPairData G}

/-- The shortest-circuit trichotomy with the constant-face branch reduced
to explicit strict port-pairing descent at both states of its involution
cell. -/
theorem IsLengthMinimal.exists_endpointStrictPortPairingDescent_or_remoteDualCycle_or_rotated_recoveryFaceTransfer
    {circuit : CrossCentralExactFaceCertifiedRebaseCircuit graphData
      minimal baseData}
    (hminimal : circuit.IsLengthMinimal) :
    (∃ cell : CrossCentralExactFaceCertifiedRebaseInvolutionCell graphData
        minimal baseData,
      cell.EndpointStrictPortPairingDescent) ∨
      Nonempty (RemoteDualCycle circuit) ∨
      ∃ rotated : CrossCentralExactFaceCertifiedRebaseCircuit graphData
          minimal baseData,
        rotated.arcLength = circuit.arcLength ∧
          Nonempty (ClosureRecoveryFaceTransfer rotated) := by
  rcases
      hminimal.involutionCell_or_exists_remoteDualCycle_or_rotated_recoveryFaceTransfer
    with hcell | hremote | htransfer
  · rcases hcell with ⟨cell⟩
    exact Or.inl ⟨cell, cell.endpoint_strictPortPairingDescent⟩
  · exact Or.inr (Or.inl hremote)
  · exact Or.inr (Or.inr htransfer)

end CrossCentralExactFaceCertifiedRebaseCircuit

end GoertzelV24AdjacentPairInsertion.AdjacentPairData

end

end Mettapedia.GraphTheory.FourColor
