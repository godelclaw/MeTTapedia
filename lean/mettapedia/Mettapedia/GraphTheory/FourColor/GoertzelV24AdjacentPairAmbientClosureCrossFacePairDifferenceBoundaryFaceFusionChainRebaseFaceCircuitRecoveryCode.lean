import Mathlib.Data.List.Cycle
import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairAmbientClosureCrossFacePairDifferenceBoundaryFaceFusionChainRebaseFaceCircuitRecoveryPosition

namespace Mettapedia.GraphTheory.FourColor

open GoertzelV24AdjacentPairBoundary
open GoertzelV24AdjacentPairInsertion
open GoertzelV24FaceOrbitIncidence
open GoertzelV24FourDefectBoundary
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

namespace ClosureRecoveryFaceArc

variable {rebaseCircuit :
  CrossCentralExactFaceCertifiedRebaseCircuit graphData minimal baseData}

/-- The finite support-transport code of a concrete recovery arc. -/
def code (arc : ClosureRecoveryFaceArc rebaseCircuit) :
    ExactClosureChannel × G.edgeSet :=
  (arc.channel, arc.edge)

/-- At a dependency junction, the incoming support edge lies on the
shared face and the outgoing support edge does not. -/
theorem Follows.incoming_mem_outgoing_not_mem
    {first second : ClosureRecoveryFaceArc rebaseCircuit}
    (follows : Follows first second) :
    first.edge ∈ orbitFaceBoundary graphData.toRotationSystem
        first.targetFace ∧
      second.edge ∉ orbitFaceBoundary graphData.toRotationSystem
        first.targetFace := by
  constructor
  · exact first.edge_mem_targetFace
  · intro hsecond
    apply second.edge_not_mem_sourceFace
    rw [← follows]
    exact hsecond

/-- Consecutive recovery dependencies use different support edges. -/
theorem Follows.edge_ne
    {first second : ClosureRecoveryFaceArc rebaseCircuit}
    (follows : Follows first second) :
    first.edge ≠ second.edge := by
  intro hedge
  rcases follows.incoming_mem_outgoing_not_mem with ⟨hfirst, hsecond⟩
  exact hsecond (hedge ▸ hfirst)

/-- Consequently consecutive finite recovery codes differ. -/
theorem Follows.code_ne
    {first second : ClosureRecoveryFaceArc rebaseCircuit}
    (follows : Follows first second) :
    first.code ≠ second.code := by
  intro hcode
  exact follows.edge_ne (congrArg Prod.snd hcode)

end ClosureRecoveryFaceArc

namespace ClosureRecoveryFaceCircuit

variable {rebaseCircuit :
  CrossCentralExactFaceCertifiedRebaseCircuit graphData minimal baseData}

/-- A concrete recovery circuit viewed intrinsically as a cyclic list. -/
def dependencyCycle
    (circuit : ClosureRecoveryFaceCircuit rebaseCircuit) :
    Cycle (ClosureRecoveryFaceArc rebaseCircuit) :=
  (circuit.first :: circuit.rest : List
    (ClosureRecoveryFaceArc rebaseCircuit))

/-- The intrinsic dependency cycle is composable across every cyclic
boundary. -/
theorem dependencyCycle_chain
    (circuit : ClosureRecoveryFaceCircuit rebaseCircuit) :
    circuit.dependencyCycle.Chain ClosureRecoveryFaceArc.Follows := by
  rw [dependencyCycle, Cycle.chain_coe_cons]
  have hcyclic : List.IsChain ClosureRecoveryFaceArc.Follows
      ((circuit.first :: circuit.rest) ++ [circuit.first]) := by
    apply circuit.consecutive.append (List.IsChain.singleton _)
    intro last hlast first hfirst
    have hfirstEq : first = circuit.first := by simpa using hfirst.symm
    subst first
    rcases List.mem_getLast?_eq_getLast hlast with ⟨hne, hlastEq⟩
    subst last
    exact circuit.closing
  simpa only [List.cons_append] using hcyclic

/-- The cyclic finite-code word carried by a recovery circuit. -/
def codeCycle
    (circuit : ClosureRecoveryFaceCircuit rebaseCircuit) :
    Cycle (ExactClosureChannel × G.edgeSet) :=
  circuit.dependencyCycle.map ClosureRecoveryFaceArc.code

/-- Adjacent entries of the cyclic code word are always different. -/
theorem codeCycle_chain_ne
    (circuit : ClosureRecoveryFaceCircuit rebaseCircuit) :
    circuit.codeCycle.Chain (· ≠ ·) := by
  rw [codeCycle, Cycle.chain_map]
  exact circuit.dependencyCycle_chain.imp
    (fun _ _ follows => follows.code_ne)

/-- The concrete dependency displayed at a recovery-cycle position. -/
def dependencyAt
    (circuit : ClosureRecoveryFaceCircuit rebaseCircuit)
    (position : Fin circuit.arcLength) :
    ClosureRecoveryFaceArc rebaseCircuit :=
  (circuit.first :: circuit.rest).get position

/-- The finite channel/edge code at a recovery-cycle position. -/
def codeAt
    (circuit : ClosureRecoveryFaceCircuit rebaseCircuit)
    (position : Fin circuit.arcLength) :
    ExactClosureChannel × G.edgeSet :=
  (circuit.dependencyAt position).code

/-- The underlying rebase position selected at a recovery-cycle
position. -/
noncomputable def restoringPositionAt
    (circuit : ClosureRecoveryFaceCircuit rebaseCircuit)
    (position : Fin circuit.arcLength) :
    Fin rebaseCircuit.arcLength :=
  (circuit.dependencyAt position).restoringPosition

/-- On a shortest recovery circuit, the positional assignment into the
underlying rebase circuit is injective. -/
theorem IsLengthMinimal.restoringPositionAt_injective
    {circuit : ClosureRecoveryFaceCircuit rebaseCircuit}
    (hminimal : circuit.IsLengthMinimal) :
    Function.Injective circuit.restoringPositionAt := by
  intro first second hposition
  have hinjective : Function.Injective circuit.restoringPositions.get :=
    List.nodup_iff_injective_get.mp hminimal.restoringPositions_nodup
  let first' : Fin circuit.restoringPositions.length :=
    Fin.cast circuit.restoringPositions_length.symm first
  let second' : Fin circuit.restoringPositions.length :=
    Fin.cast circuit.restoringPositions_length.symm second
  have hget : circuit.restoringPositions.get first' =
      circuit.restoringPositions.get second' := by
    change ((circuit.first :: circuit.rest).map
        ClosureRecoveryFaceArc.restoringPosition).get first' =
      ((circuit.first :: circuit.rest).map
        ClosureRecoveryFaceArc.restoringPosition).get second'
    simp only [List.get_eq_getElem, List.getElem_map]
    simpa [first', second', restoringPositionAt, dependencyAt,
      List.get_eq_getElem] using hposition
  exact Fin.cast_injective circuit.restoringPositions_length.symm
    (hinjective hget)

/-- Either the finite code alphabet bounds a recovery cycle, or two
distinct recovery positions carry the same channel and support edge. -/
theorem arcLength_le_twice_card_edges_or_exists_code_collision
    (circuit : ClosureRecoveryFaceCircuit rebaseCircuit) :
    circuit.arcLength ≤ 2 * Fintype.card G.edgeSet ∨
      ∃ first second : Fin circuit.arcLength,
        first ≠ second ∧ circuit.codeAt first = circuit.codeAt second := by
  classical
  by_cases hinjective : Function.Injective circuit.codeAt
  · left
    have hcard := Fintype.card_le_of_injective circuit.codeAt hinjective
    have hchannel : Fintype.card ExactClosureChannel = 2 := by decide
    simpa [hchannel] using hcard
  · right
    rcases Function.not_injective_iff.mp hinjective with
      ⟨first, second, hcode, hne⟩
    exact ⟨first, second, hne, hcode⟩

/-- In the collision branch of a shortest recovery circuit, the equal
codes occur at distinct positions of the underlying rebase circuit. -/
theorem IsLengthMinimal.exists_distinct_restoringPositions_of_code_collision
    {circuit : ClosureRecoveryFaceCircuit rebaseCircuit}
    (hminimal : circuit.IsLengthMinimal)
    (collision : ∃ first second : Fin circuit.arcLength,
      first ≠ second ∧ circuit.codeAt first = circuit.codeAt second) :
    ∃ first second : Fin circuit.arcLength,
      circuit.codeAt first = circuit.codeAt second ∧
        circuit.restoringPositionAt first ≠
          circuit.restoringPositionAt second := by
  rcases collision with ⟨first, second, hne, hcode⟩
  exact ⟨first, second, hcode,
    fun hposition => hne (hminimal.restoringPositionAt_injective hposition)⟩

end ClosureRecoveryFaceCircuit

end GoertzelV24AdjacentPairInsertion.AdjacentPairData

end

end Mettapedia.GraphTheory.FourColor
