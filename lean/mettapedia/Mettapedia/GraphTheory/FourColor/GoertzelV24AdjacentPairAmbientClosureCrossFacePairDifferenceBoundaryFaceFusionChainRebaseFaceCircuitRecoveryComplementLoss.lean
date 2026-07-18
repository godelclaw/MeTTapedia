import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairAmbientClosureCrossFacePairDifferenceBoundaryFaceFusionChainRebaseFaceCircuitRecoverySmallCycleClassification

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

/-- A loss balancing one recovery gain, displayed on the strict cyclic
complement of its restoring arc. -/
structure ClosureRecoveryComplementLoss
    (rebaseCircuit : CrossCentralExactFaceCertifiedRebaseCircuit graphData
      minimal baseData)
    (recovery : ClosureRecoveryFaceArc rebaseCircuit) where
  before : List
    (CrossCentralExactFaceCertifiedRebaseArc graphData minimal baseData)
  after : List
    (CrossCentralExactFaceCertifiedRebaseArc graphData minimal baseData)
  displayed_split : rebaseCircuit.first :: rebaseCircuit.rest =
    before ++ recovery.recoveryArc :: after
  lossArc :
    CrossCentralExactFaceCertifiedRebaseArc graphData minimal baseData
  lossArc_mem_complement : lossArc ∈ after ++ before
  lossArc_source_mem :
    recovery.edge.1 ∈ recovery.channel.edges lossArc.source
  lossArc_target_not_mem :
    recovery.edge.1 ∉ recovery.channel.edges lossArc.target

namespace ClosureRecoveryComplementLoss

variable {rebaseCircuit :
  CrossCentralExactFaceCertifiedRebaseCircuit graphData minimal baseData}
  {recovery : ClosureRecoveryFaceArc rebaseCircuit}

/-- The balancing loss remains one of the displayed rebase arcs. -/
theorem lossArc_mem_displayed
    (loss : ClosureRecoveryComplementLoss rebaseCircuit recovery) :
    loss.lossArc ∈ rebaseCircuit.first :: rebaseCircuit.rest := by
  rw [loss.displayed_split]
  rcases List.mem_append.mp loss.lossArc_mem_complement with
    hafter | hbefore
  · exact List.mem_append_right _ (List.mem_cons_of_mem _ hafter)
  · exact List.mem_append_left _ hbefore

/-- A support loss is not the restoring gain it balances. -/
theorem lossArc_ne_recoveryArc
    (loss : ClosureRecoveryComplementLoss rebaseCircuit recovery) :
    loss.lossArc ≠ recovery.recoveryArc := by
  intro harc
  apply recovery.edge_not_mem_recoverySource
  rw [← harc]
  exact loss.lossArc_source_mem

/-- The strict cyclic complement of a recovery gain is nonempty. -/
theorem complement_ne_nil
    (loss : ClosureRecoveryComplementLoss rebaseCircuit recovery) :
    loss.after ++ loss.before ≠ [] :=
  List.ne_nil_of_mem loss.lossArc_mem_complement

end ClosureRecoveryComplementLoss

namespace ClosureRecoveryFaceArc

variable {rebaseCircuit :
  CrossCentralExactFaceCertifiedRebaseCircuit graphData minimal baseData}

/-- Closing the underlying rebase trace forces every stored support gain
to be balanced by a loss on its strict cyclic complement. -/
theorem exists_complementLoss
    (recovery : ClosureRecoveryFaceArc rebaseCircuit) :
    Nonempty (ClosureRecoveryComplementLoss rebaseCircuit recovery) := by
  rcases List.mem_iff_append.mp recovery.recoveryArc_mem_displayed with
    ⟨before, after, hsplit⟩
  let rotated := rebaseCircuit.rotateAtSplit recovery.recoveryArc
    before after hsplit
  cases hcomplement : after ++ before with
  | nil =>
      have hclosing : CrossCentralExactFaceCertifiedRebaseArc.Follows
          recovery.recoveryArc recovery.recoveryArc := by
        simpa [rotated, hcomplement] using rotated.closing
      have hreturn : recovery.recoveryArc.target =
          recovery.recoveryArc.source := hclosing
      exact False.elim (recovery.edge_not_mem_recoverySource
        (hreturn ▸ recovery.edge_mem_recoveryTarget))
  | cons complementFirst complementRest =>
      have hchain : List.IsChain
          CrossCentralExactFaceCertifiedRebaseArc.Follows
          (recovery.recoveryArc :: complementFirst :: complementRest) := by
        simpa [rotated, hcomplement] using rotated.consecutive
      have hparts := List.isChain_cons_cons.mp hchain
      have hcomplementSource : recovery.edge.1 ∈
          recovery.channel.edges complementFirst.source := by
        rw [← hparts.1]
        exact recovery.edge_mem_recoveryTarget
      have hcomplementTarget : recovery.edge.1 ∉
          recovery.channel.edges
            ((complementFirst :: complementRest).getLast (by simp)).target := by
        have hclosing : CrossCentralExactFaceCertifiedRebaseArc.Follows
            ((complementFirst :: complementRest).getLast (by simp))
            recovery.recoveryArc := by
          simpa [rotated, hcomplement] using rotated.closing
        have hlast :
            ((complementFirst :: complementRest).getLast
              (by simp)).target = recovery.recoveryArc.source := by
          exact hclosing
        intro hmem
        apply recovery.edge_not_mem_recoverySource
        rw [← hlast]
        exact hmem
      rcases GoertzelV24RebaseFaceCircuit.exists_entry_loss_of_endpoint_loss
          CrossCentralExactFaceCertifiedRebaseArc.source
          CrossCentralExactFaceCertifiedRebaseArc.target
          (fun state => recovery.edge.1 ∈ recovery.channel.edges state)
          complementFirst complementRest hparts.2 hcomplementSource
          hcomplementTarget with
        ⟨lossArc, hlossMem, hlossSource, hlossTarget⟩
      exact ⟨{
        before := before
        after := after
        displayed_split := hsplit
        lossArc := lossArc
        lossArc_mem_complement := by simpa [hcomplement] using hlossMem
        lossArc_source_mem := hlossSource
        lossArc_target_not_mem := hlossTarget }⟩

end ClosureRecoveryFaceArc

end GoertzelV24AdjacentPairInsertion.AdjacentPairData

end

end Mettapedia.GraphTheory.FourColor
