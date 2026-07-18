import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairAmbientClosureCrossFacePairDifferenceBoundaryFaceFusionChainRebaseDynamics

namespace Mettapedia.GraphTheory.FourColor

open GoertzelV24AdjacentPairBoundary
open GoertzelV24AdjacentPairInsertion
open GoertzelV24FourDefectBoundary
open GoertzelV24TwoEdgeCutMinimality
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

/-- A total transition system on a finite type reaches a terminal state or
contains a reachable nonempty closed transition chain. -/
theorem finite_reflTransGen_terminal_or_transGen_cycle
    {State : Type*} [Finite State]
    (transition : State → State → Prop)
    (terminal : State → Prop)
    (terminal_or_step : ∀ state, terminal state ∨
      ∃ target, transition state target)
    (start : State) :
    (∃ finish, Relation.ReflTransGen transition start finish ∧
        terminal finish) ∨
      ∃ cycleState,
        Relation.ReflTransGen transition start cycleState ∧
          Relation.TransGen transition cycleState cycleState := by
  classical
  by_cases hterminal : ∃ finish,
      Relation.ReflTransGen transition start finish ∧ terminal finish
  · exact Or.inl hterminal
  · right
    by_contra hcycle
    let Reachable := {state : State //
      Relation.ReflTransGen transition start state}
    let descent : Reachable → Reachable → Prop :=
      fun next current =>
        Relation.TransGen transition current.1 next.1
    letI : IsTrans Reachable descent :=
      ⟨fun _first _second _third hfirst hsecond =>
        Relation.TransGen.trans hsecond hfirst⟩
    letI : Std.Irrefl descent :=
      ⟨fun state hclosed =>
        hcycle ⟨state.1, state.2, hclosed⟩⟩
    have hwf : WellFounded descent :=
      Finite.wellFounded_of_trans_of_irrefl descent
    let initial : Reachable := ⟨start, Relation.ReflTransGen.refl⟩
    exact hwf.induction (C := fun _ => False) initial
      (fun current smaller => by
      have hnotTerminal : ¬terminal current.1 := by
        intro hcurrent
        exact hterminal ⟨current.1, current.2, hcurrent⟩
      rcases terminal_or_step current.1 with hcurrent | ⟨target, hstep⟩
      · exact False.elim (hnotTerminal hcurrent)
      · let next : Reachable :=
          ⟨target, current.2.tail hstep⟩
        exact smaller next (Relation.TransGen.single hstep))

namespace GoertzelV24AdjacentPairInsertion.AdjacentPairData

open GoertzelV24AdjacentPairBoundary.AdjacentPairData
open GoertzelV24FourDefectBoundary.DegreeTwoBoundaryData

attribute [local instance]
  fusionFaceNetworkGraphEdgeSetDecidableEq
  fusionFaceNetworkRetainedVertexFintype
  fusionFaceNetworkRetainedVertexDecidableEq

/-- The two stopping families for exact-state rebase dynamics. -/
def CrossCentralExactFaceCutState.CertifiedStoppingOutcome
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (baseData : AdjacentPairData G)
    (state : CrossCentralExactFaceCutState graphData
      (baseData.rotationOrderedData graphData minimal.spherical.cubic
        minimal.vertexRotationCyclic)) : Prop :=
  CrossCentralSourceClosureCycleDescent state.2 ∨
    state.CertifiedTerminalOutcome graphData minimal baseData

/-- Each exact state either stops with a certified mathematical outcome or
takes one provenance-certified rebase transition. -/
theorem CrossCentralExactFaceCutState.certifiedStopping_or_transition
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (baseData : AdjacentPairData G)
    (state : CrossCentralExactFaceCutState graphData
      (baseData.rotationOrderedData graphData minimal.spherical.cubic
        minimal.vertexRotationCyclic)) :
    state.CertifiedStoppingOutcome graphData minimal baseData ∨
      ∃ target, CrossCentralExactFaceCertifiedRebaseTransition graphData
        minimal baseData state target := by
  rcases state.descent_or_certifiedTerminal_or_transition
      graphData minimal baseData with hdescent | hterminal | htransition
  · exact Or.inl (Or.inl hdescent)
  · exact Or.inl (Or.inr hterminal)
  · exact Or.inr htransition

/-- Exact finite-state pumping for the faithful rebase dynamics.  Starting
at any exact pair, one reaches a strict descent or certified terminal
normal form, unless a nonempty closed chain of provenance-certified
rebases is reachable. -/
theorem CrossCentralExactFaceCutState.exists_reachable_certifiedStopping_or_rebaseCycle
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (baseData : AdjacentPairData G)
    (start : CrossCentralExactFaceCutState graphData
      (baseData.rotationOrderedData graphData minimal.spherical.cubic
        minimal.vertexRotationCyclic)) :
    (∃ finish,
        Relation.ReflTransGen
            (CrossCentralExactFaceCertifiedRebaseTransition graphData
              minimal baseData) start finish ∧
          finish.CertifiedStoppingOutcome graphData minimal baseData) ∨
      ∃ cycleState,
        Relation.ReflTransGen
            (CrossCentralExactFaceCertifiedRebaseTransition graphData
              minimal baseData) start cycleState ∧
          Relation.TransGen
            (CrossCentralExactFaceCertifiedRebaseTransition graphData
              minimal baseData) cycleState cycleState := by
  exact finite_reflTransGen_terminal_or_transGen_cycle
    (CrossCentralExactFaceCertifiedRebaseTransition graphData minimal
      baseData)
    (CrossCentralExactFaceCutState.CertifiedStoppingOutcome graphData
      minimal baseData)
    (CrossCentralExactFaceCutState.certifiedStopping_or_transition
      graphData minimal baseData) start

/-- The finite pumping conclusion, packaged at an exact cut pair. -/
def CrossCentralExactFaceCutPair.CertifiedRebasePumpingOutcome
    {graphData : Data G}
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (baseData : AdjacentPairData G)
    {cross : (DeletedAdjacentPairGraph G baseData.firstVertex
      baseData.secondVertex).edgeSet}
    (pair : CrossCentralExactFaceCutPair graphData
      (baseData.rotationOrderedData graphData minimal.spherical.cubic
        minimal.vertexRotationCyclic) cross) : Prop :=
  let start : CrossCentralExactFaceCutState graphData
      (baseData.rotationOrderedData graphData minimal.spherical.cubic
        minimal.vertexRotationCyclic) := ⟨cross, pair⟩
  (∃ finish,
      Relation.ReflTransGen
          (CrossCentralExactFaceCertifiedRebaseTransition graphData
            minimal baseData) start finish ∧
        finish.CertifiedStoppingOutcome graphData minimal baseData) ∨
    ∃ cycleState,
      Relation.ReflTransGen
          (CrossCentralExactFaceCertifiedRebaseTransition graphData
            minimal baseData) start cycleState ∧
        Relation.TransGen
          (CrossCentralExactFaceCertifiedRebaseTransition graphData
            minimal baseData) cycleState cycleState

/-- Every exact cut pair in a minimal spherical counterexample realizes
the packaged finite pumping outcome. -/
theorem CrossCentralExactFaceCutPair.certifiedRebasePumping_outcome
    {graphData : Data G}
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (baseData : AdjacentPairData G)
    {cross : (DeletedAdjacentPairGraph G baseData.firstVertex
      baseData.secondVertex).edgeSet}
    (pair : CrossCentralExactFaceCutPair graphData
      (baseData.rotationOrderedData graphData minimal.spherical.cubic
        minimal.vertexRotationCyclic) cross) :
    pair.CertifiedRebasePumpingOutcome minimal baseData := by
  exact CrossCentralExactFaceCutState.exists_reachable_certifiedStopping_or_rebaseCycle
    graphData minimal baseData ⟨cross, pair⟩

end GoertzelV24AdjacentPairInsertion.AdjacentPairData

end

end Mettapedia.GraphTheory.FourColor
