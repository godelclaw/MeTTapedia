import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairAmbientClosureCrossFacePairDifferenceBoundaryFaceFusionChainRebaseFaceCircuitRecoverySupportBalance
import Mettapedia.GraphTheory.FourColor.GoertzelV24SharedFacesTwoEdgeSeparator

namespace Mettapedia.GraphTheory.FourColor

open GoertzelV24AdjacentPairBoundary
open GoertzelV24AdjacentPairInsertion
open GoertzelV24FaceOrbitIncidence
open GoertzelV24FourDefectBoundary
open GoertzelV24SharedFacesTwoEdgeSeparator
open GoertzelV24TwoEdgeCutMinimality
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

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

namespace ClosureRecoveryFaceCircuit

variable {rebaseCircuit :
  CrossCentralExactFaceCertifiedRebaseCircuit graphData minimal baseData}

/-- The target face at a recovery-cycle position. -/
def targetFaceAt
    (circuit : ClosureRecoveryFaceCircuit rebaseCircuit)
    (position : Fin circuit.arcLength) :
    OrbitFace graphData.toRotationSystem :=
  (circuit.dependencyAt position).targetFace

@[simp] theorem targetFaces_length
    (circuit : ClosureRecoveryFaceCircuit rebaseCircuit) :
    circuit.targetFaces.length = circuit.arcLength := by
  simp [targetFaces, arcLength]

/-- Target-face positions are injective on a shortest recovery circuit. -/
theorem IsLengthMinimal.targetFaceAt_injective
    {circuit : ClosureRecoveryFaceCircuit rebaseCircuit}
    (hminimal : circuit.IsLengthMinimal) :
    Function.Injective circuit.targetFaceAt := by
  intro first second hface
  have hinjective : Function.Injective circuit.targetFaces.get :=
    List.nodup_iff_injective_get.mp hminimal.targetFaces_nodup
  let first' : Fin circuit.targetFaces.length :=
    Fin.cast circuit.targetFaces_length.symm first
  let second' : Fin circuit.targetFaces.length :=
    Fin.cast circuit.targetFaces_length.symm second
  have hget : circuit.targetFaces.get first' =
      circuit.targetFaces.get second' := by
    change ((circuit.first :: circuit.rest).map
        ClosureRecoveryFaceArc.targetFace).get first' =
      ((circuit.first :: circuit.rest).map
        ClosureRecoveryFaceArc.targetFace).get second'
    simp only [List.get_eq_getElem, List.getElem_map]
    simpa [first', second', targetFaceAt, dependencyAt,
      List.get_eq_getElem] using hface
  exact Fin.cast_injective circuit.targetFaces_length.symm
    (hinjective hget)

/-- A recovery occurrence together with its target facial incidence. -/
abbrev EdgeFaceIncidence :=
  Σ edge : G.edgeSet,
    { face : OrbitFace graphData.toRotationSystem //
      edge ∈ orbitFaceBoundary graphData.toRotationSystem face }

/-- The edge/target-face incidence at a recovery-cycle position. -/
def edgeFaceIncidenceAt
    (circuit : ClosureRecoveryFaceCircuit rebaseCircuit)
    (position : Fin circuit.arcLength) :
    EdgeFaceIncidence (G := G) (graphData := graphData) :=
  ⟨(circuit.dependencyAt position).edge,
    ⟨circuit.targetFaceAt position,
      (circuit.dependencyAt position).edge_mem_targetFace⟩⟩

/-- Distinct positions of a shortest recovery circuit give distinct
edge/target-face incidences. -/
theorem IsLengthMinimal.edgeFaceIncidenceAt_injective
    {circuit : ClosureRecoveryFaceCircuit rebaseCircuit}
    (hminimal : circuit.IsLengthMinimal) :
    Function.Injective circuit.edgeFaceIncidenceAt := by
  intro first second hincidence
  apply hminimal.targetFaceAt_injective
  exact congrArg
    (fun occurrence : EdgeFaceIncidence (G := G) (graphData := graphData) =>
      occurrence.2.1) hincidence

/-- Direct facial incidence counting bounds a shortest recovery circuit
by twice the number of ambient edges. -/
theorem IsLengthMinimal.arcLength_le_two_mul_card_edges
    {circuit : ClosureRecoveryFaceCircuit rebaseCircuit}
    (hminimal : circuit.IsLengthMinimal) :
    circuit.arcLength ≤ 2 * Fintype.card G.edgeSet := by
  have hcard := Fintype.card_le_of_injective
    circuit.edgeFaceIncidenceAt hminimal.edgeFaceIncidenceAt_injective
  calc
    circuit.arcLength = Fintype.card (Fin circuit.arcLength) := by simp
    _ ≤ Fintype.card
        (EdgeFaceIncidence (G := G) (graphData := graphData)) := hcard
    _ = ∑ edge : G.edgeSet,
        Fintype.card { face : OrbitFace graphData.toRotationSystem //
          edge ∈ orbitFaceBoundary graphData.toRotationSystem face } :=
      Fintype.card_sigma
    _ ≤ ∑ _edge : G.edgeSet, 2 := by
      apply Finset.sum_le_sum
      intro edge hedge
      rw [Fintype.card_subtype]
      simpa [totalIncidenceCount] using
        orbitFace_totalIncidenceCount_le_two
          graphData.toRotationSystem edge
    _ = 2 * Fintype.card G.edgeSet := by simp [Nat.mul_comm]

end ClosureRecoveryFaceCircuit

namespace ClosureRecoveryCodeAlternation

variable {rebaseCircuit :
  CrossCentralExactFaceCertifiedRebaseCircuit graphData minimal baseData}
  {recoveryCircuit : ClosureRecoveryFaceCircuit rebaseCircuit}

/-- The two equal-code gains of an alternation land on different faces of
a shortest recovery circuit. -/
theorem targetFaces_ne
    (alternation : ClosureRecoveryCodeAlternation rebaseCircuit
      recoveryCircuit)
    (hrecoveryMinimal : recoveryCircuit.IsLengthMinimal) :
    (recoveryCircuit.dependencyAt alternation.earlier).targetFace ≠
      (recoveryCircuit.dependencyAt alternation.later).targetFace := by
  intro hface
  have hpositions := hrecoveryMinimal.targetFaceAt_injective hface
  exact (ne_of_lt alternation.restoring_lt)
    (congrArg recoveryCircuit.restoringPositionAt hpositions)

/-- The common support edge lies on both gain target faces. -/
theorem edge_mem_targetFaces
    (alternation : ClosureRecoveryCodeAlternation rebaseCircuit
      recoveryCircuit) :
    (recoveryCircuit.dependencyAt alternation.earlier).edge ∈
        orbitFaceBoundary graphData.toRotationSystem
          (recoveryCircuit.dependencyAt alternation.earlier).targetFace ∧
      (recoveryCircuit.dependencyAt alternation.earlier).edge ∈
        orbitFaceBoundary graphData.toRotationSystem
          (recoveryCircuit.dependencyAt alternation.later).targetFace := by
  constructor
  · exact (recoveryCircuit.dependencyAt
      alternation.earlier).edge_mem_targetFace
  · have hedge :
        (recoveryCircuit.dependencyAt alternation.earlier).edge =
          (recoveryCircuit.dependencyAt alternation.later).edge := by
      have hcode := congrArg Prod.snd alternation.code_eq
      simpa [ClosureRecoveryFaceCircuit.codeAt,
        ClosureRecoveryFaceArc.code] using hcode
    rw [hedge]
    exact (recoveryCircuit.dependencyAt
      alternation.later).edge_mem_targetFace

/-- The gain target faces are exactly the two quotient faces incident to
the repeated support edge. -/
theorem incidentFaces_eq_target_pair
    (alternation : ClosureRecoveryCodeAlternation rebaseCircuit
      recoveryCircuit)
    (hrecoveryMinimal : recoveryCircuit.IsLengthMinimal) :
    (Finset.univ.filter fun face : OrbitFace graphData.toRotationSystem =>
      (recoveryCircuit.dependencyAt alternation.earlier).edge ∈
        orbitFaceBoundary graphData.toRotationSystem face) =
      {(recoveryCircuit.dependencyAt alternation.earlier).targetFace,
        (recoveryCircuit.dependencyAt alternation.later).targetFace} := by
  exact orbitFace_incidentFaces_eq_pair_of_mem
    graphData.toRotationSystem minimal.facesTwoSided
    (alternation.targetFaces_ne hrecoveryMinimal)
    (recoveryCircuit.dependencyAt alternation.earlier).edge
    alternation.edge_mem_targetFaces.1
    alternation.edge_mem_targetFaces.2

/-- Every selected face is either off the repeated edge or is one of its
two gain target faces. -/
theorem selectedFace_off_or_eq_targetFace
    (alternation : ClosureRecoveryCodeAlternation rebaseCircuit
      recoveryCircuit)
    (hrecoveryMinimal : recoveryCircuit.IsLengthMinimal)
    (arc : CrossCentralExactFaceCertifiedRebaseArc graphData minimal
      baseData) :
    (recoveryCircuit.dependencyAt alternation.earlier).edge ∉
        orbitFaceBoundary graphData.toRotationSystem arc.selectedFace ∨
      arc.selectedFace =
          (recoveryCircuit.dependencyAt alternation.earlier).targetFace ∨
        arc.selectedFace =
          (recoveryCircuit.dependencyAt alternation.later).targetFace := by
  by_cases hoff : (recoveryCircuit.dependencyAt alternation.earlier).edge ∉
      orbitFaceBoundary graphData.toRotationSystem arc.selectedFace
  · exact Or.inl hoff
  · right
    have hon : (recoveryCircuit.dependencyAt alternation.earlier).edge ∈
        orbitFaceBoundary graphData.toRotationSystem arc.selectedFace := by
      simpa only [not_not] using hoff
    have hmem : arc.selectedFace ∈
        Finset.univ.filter fun face : OrbitFace graphData.toRotationSystem =>
          (recoveryCircuit.dependencyAt alternation.earlier).edge ∈
            orbitFaceBoundary graphData.toRotationSystem face := by
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hon⟩
    rw [alternation.incidentFaces_eq_target_pair hrecoveryMinimal] at hmem
    simpa using hmem

/-- A selected face off the repeated support edge has a concrete recovery
dependency directly to the earlier gain target. -/
def recoveryFromSelectedFaceOffEdge
    (alternation : ClosureRecoveryCodeAlternation rebaseCircuit
      recoveryCircuit)
    (arc : CrossCentralExactFaceCertifiedRebaseArc graphData minimal
      baseData)
    (hoff : (recoveryCircuit.dependencyAt alternation.earlier).edge ∉
      orbitFaceBoundary graphData.toRotationSystem arc.selectedFace) :
    ClosureRecoveryFaceArc rebaseCircuit := {
  sourceFace := arc.selectedFace
  targetFace :=
    (recoveryCircuit.dependencyAt alternation.earlier).targetFace
  channel := (recoveryCircuit.dependencyAt alternation.earlier).channel
  edge := (recoveryCircuit.dependencyAt alternation.earlier).edge
  recoveryArc :=
    (recoveryCircuit.dependencyAt alternation.earlier).recoveryArc
  recoveryArc_mem_displayed :=
    (recoveryCircuit.dependencyAt
      alternation.earlier).recoveryArc_mem_displayed
  recoveryArc_selectedFace :=
    (recoveryCircuit.dependencyAt
      alternation.earlier).recoveryArc_selectedFace
  edge_not_mem_sourceFace := hoff
  edge_not_mem_recoverySource :=
    (recoveryCircuit.dependencyAt
      alternation.earlier).edge_not_mem_recoverySource
  edge_mem_recoveryTarget :=
    (recoveryCircuit.dependencyAt
      alternation.earlier).edge_mem_recoveryTarget
  edge_mem_targetFace :=
    (recoveryCircuit.dependencyAt
      alternation.earlier).edge_mem_targetFace
  targetFace_ne_sourceFace := by
    intro heq
    apply hoff
    rw [← heq]
    exact (recoveryCircuit.dependencyAt
      alternation.earlier).edge_mem_targetFace }

@[simp] theorem recoveryFromSelectedFaceOffEdge_sourceFace
    (alternation : ClosureRecoveryCodeAlternation rebaseCircuit
      recoveryCircuit)
    (arc : CrossCentralExactFaceCertifiedRebaseArc graphData minimal
      baseData)
    (hoff : (recoveryCircuit.dependencyAt alternation.earlier).edge ∉
      orbitFaceBoundary graphData.toRotationSystem arc.selectedFace) :
    (alternation.recoveryFromSelectedFaceOffEdge arc hoff).sourceFace =
      arc.selectedFace := rfl

@[simp] theorem recoveryFromSelectedFaceOffEdge_targetFace
    (alternation : ClosureRecoveryCodeAlternation rebaseCircuit
      recoveryCircuit)
    (arc : CrossCentralExactFaceCertifiedRebaseArc graphData minimal
      baseData)
    (hoff : (recoveryCircuit.dependencyAt alternation.earlier).edge ∉
      orbitFaceBoundary graphData.toRotationSystem arc.selectedFace) :
    (alternation.recoveryFromSelectedFaceOffEdge arc hoff).targetFace =
      (recoveryCircuit.dependencyAt alternation.earlier).targetFace := rfl

/-- Thus every selected face either supplies such a concrete dependency
or is one of the two gain target faces. -/
theorem exists_recoveryFromSelectedFace_or_eq_targetFace
    (alternation : ClosureRecoveryCodeAlternation rebaseCircuit
      recoveryCircuit)
    (hrecoveryMinimal : recoveryCircuit.IsLengthMinimal)
    (arc : CrossCentralExactFaceCertifiedRebaseArc graphData minimal
      baseData) :
    (∃ recovery : ClosureRecoveryFaceArc rebaseCircuit,
      recovery.sourceFace = arc.selectedFace ∧
        recovery.targetFace =
          (recoveryCircuit.dependencyAt alternation.earlier).targetFace) ∨
      arc.selectedFace =
          (recoveryCircuit.dependencyAt alternation.earlier).targetFace ∨
        arc.selectedFace =
          (recoveryCircuit.dependencyAt alternation.later).targetFace := by
  rcases alternation.selectedFace_off_or_eq_targetFace
      hrecoveryMinimal arc with hoff | hface
  · left
    exact ⟨alternation.recoveryFromSelectedFaceOffEdge arc hoff, rfl, rfl⟩
  · exact Or.inr hface

end ClosureRecoveryCodeAlternation

end GoertzelV24AdjacentPairInsertion.AdjacentPairData

end

end Mettapedia.GraphTheory.FourColor
