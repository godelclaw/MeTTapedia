import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairAmbientClosureCrossFacePairDifferenceBoundaryFaceFusionChainRebaseFaceCircuitRecoveryLossPosition

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

/-- A directed recovery transfer retaining both the support loss on its
source face and the restoring gain on its target face. -/
structure ClosureRecoveryFaceTransfer
    (rebaseCircuit : CrossCentralExactFaceCertifiedRebaseCircuit graphData
      minimal baseData) where
  recovery : ClosureRecoveryFaceArc rebaseCircuit
  lossArc :
    CrossCentralExactFaceCertifiedRebaseArc graphData minimal baseData
  lossArc_mem_displayed :
    lossArc ∈ rebaseCircuit.first :: rebaseCircuit.rest
  lossArc_selectedFace : lossArc.selectedFace = recovery.sourceFace
  edge_mem_lossSource :
    recovery.edge.1 ∈ recovery.channel.edges lossArc.source
  edge_not_mem_lossTarget :
    recovery.edge.1 ∉ recovery.channel.edges lossArc.target

namespace ClosureRecoveryFaceTransfer

variable {rebaseCircuit :
  CrossCentralExactFaceCertifiedRebaseCircuit graphData minimal baseData}

/-- The localized loss arc and the restoring gain arc are distinct. -/
theorem lossArc_ne_recoveryArc
    (transfer : ClosureRecoveryFaceTransfer rebaseCircuit) :
    transfer.lossArc ≠ transfer.recovery.recoveryArc := by
  intro harc
  apply transfer.recovery.edge_not_mem_recoverySource
  rw [← harc]
  exact transfer.edge_mem_lossSource

/-- The first displayed position of the localized source-face loss. -/
noncomputable def lossPosition
    (transfer : ClosureRecoveryFaceTransfer rebaseCircuit) :
    Fin rebaseCircuit.arcLength := by
  classical
  exact
    ⟨(rebaseCircuit.first :: rebaseCircuit.rest).idxOf transfer.lossArc,
      by
        rw [CrossCentralExactFaceCertifiedRebaseCircuit.arcLength]
        exact List.idxOf_lt_length_iff.mpr transfer.lossArc_mem_displayed⟩

/-- Reading the rebase trace at the localized loss position recovers its
source-face loss arc. -/
@[simp] theorem get_lossPosition
    (transfer : ClosureRecoveryFaceTransfer rebaseCircuit) :
    (rebaseCircuit.first :: rebaseCircuit.rest).get
        transfer.lossPosition = transfer.lossArc := by
  classical
  apply List.idxOf_get

/-- The localized source-face loss belongs to the complete loss carrier
of the transfer's recovery code. -/
theorem lossPosition_mem_lossPositions
    (transfer : ClosureRecoveryFaceTransfer rebaseCircuit) :
    transfer.lossPosition ∈ transfer.recovery.lossPositions := by
  rw [transfer.recovery.mem_lossPositions_iff]
  rw [transfer.get_lossPosition]
  exact ⟨transfer.edge_mem_lossSource,
    transfer.edge_not_mem_lossTarget⟩

/-- The localized loss position is selected on the dependency's source
face. -/
theorem selectedFace_at_lossPosition
    (transfer : ClosureRecoveryFaceTransfer rebaseCircuit) :
    ((rebaseCircuit.first :: rebaseCircuit.rest).get
        transfer.lossPosition).selectedFace =
      transfer.recovery.sourceFace := by
  rw [transfer.get_lossPosition]
  exact transfer.lossArc_selectedFace

/-- A localized loss position differs from its restoring gain position. -/
theorem lossPosition_ne_restoringPosition
    (transfer : ClosureRecoveryFaceTransfer rebaseCircuit) :
    transfer.lossPosition ≠ transfer.recovery.restoringPosition := by
  intro hposition
  apply transfer.lossArc_ne_recoveryArc
  calc
    transfer.lossArc =
        (rebaseCircuit.first :: rebaseCircuit.rest).get
          transfer.lossPosition := transfer.get_lossPosition.symm
    _ = (rebaseCircuit.first :: rebaseCircuit.rest).get
          transfer.recovery.restoringPosition := by rw [hposition]
    _ = transfer.recovery.recoveryArc :=
      transfer.recovery.get_restoringPosition

/-- Forgetting the localized source-face loss recovers the original
directed face dependency. -/
theorem to_faceDependency
    (transfer : ClosureRecoveryFaceTransfer rebaseCircuit) :
    rebaseCircuit.ClosureRecoveryFaceDependency
      transfer.recovery.sourceFace transfer.recovery.targetFace :=
  transfer.recovery.to_dependency

end ClosureRecoveryFaceTransfer

namespace CrossCentralExactFaceCertifiedRebaseCircuit

variable {rebaseCircuit :
  CrossCentralExactFaceCertifiedRebaseCircuit graphData minimal baseData}

/-- A support loss across a displayed constant-face middle block occurs on
a concrete arc selected on that same face. -/
theorem OutsideClosureRecoveryWitness.exists_lossArc_on_middleBlock
    (rebaseCircuit : CrossCentralExactFaceCertifiedRebaseCircuit graphData
      minimal baseData)
    (middleFace : OrbitFace graphData.toRotationSystem)
    (left middleFirst right :
      CrossCentralExactFaceCertifiedRebaseArc graphData minimal baseData)
    (before middleRest after : List
      (CrossCentralExactFaceCertifiedRebaseArc graphData minimal baseData))
    (hsplit : rebaseCircuit.first :: rebaseCircuit.rest =
      before ++
        (left :: ((middleFirst :: middleRest) ++ (right :: after))))
    (hmiddleFaces : ∀ arc ∈ middleFirst :: middleRest,
      arc.selectedFace = middleFace)
    (witness : OutsideClosureRecoveryWitness middleFace
      middleFirst.source right.source
        (right :: (after ++ before ++ [left]))) :
    ∃ lossArc ∈ middleFirst :: middleRest,
      witness.edge.1 ∈ witness.channel.edges lossArc.source ∧
        witness.edge.1 ∉ witness.channel.edges lossArc.target ∧
        lossArc.selectedFace = middleFace := by
  let middleArcs := middleFirst :: middleRest
  have hfullChain : List.IsChain
      CrossCentralExactFaceCertifiedRebaseArc.Follows
        (before ++ (left :: (middleArcs ++ (right :: after)))) := by
    rw [← hsplit]
    exact rebaseCircuit.consecutive
  have htailChain : List.IsChain
      CrossCentralExactFaceCertifiedRebaseArc.Follows
        (left :: (middleArcs ++ (right :: after))) :=
    (List.isChain_append.mp hfullChain).2.1
  have hleftParts := List.isChain_cons_cons.mp htailChain
  have hmiddleAfterChain : List.IsChain
      CrossCentralExactFaceCertifiedRebaseArc.Follows
        (middleArcs ++ (right :: after)) := by
    simpa [middleArcs] using hleftParts.2
  have hmiddleParts := List.isChain_append.mp hmiddleAfterChain
  have hmiddleChain : List.IsChain
      CrossCentralExactFaceCertifiedRebaseArc.Follows middleArcs :=
    hmiddleParts.1
  have hmiddleNe : middleArcs ≠ [] := by simp [middleArcs]
  let middleLast := middleArcs.getLast hmiddleNe
  have hlastMem : middleLast ∈ middleArcs.getLast? := by
    rw [List.getLast?_eq_getLast_of_ne_nil hmiddleNe]
    simp [middleLast]
  have hlastFollows :
      CrossCentralExactFaceCertifiedRebaseArc.Follows middleLast right :=
    hmiddleParts.2.2 middleLast hlastMem right (by simp)
  have hlastTarget : witness.edge.1 ∉
      witness.channel.edges middleLast.target := by
    change middleLast.target = right.source at hlastFollows
    rw [hlastFollows]
    exact witness.edge_not_mem_target
  change List.IsChain (fun left right => left.target = right.source)
    (middleFirst :: middleRest) at hmiddleChain
  rcases GoertzelV24RebaseFaceCircuit.exists_entry_loss_of_endpoint_loss
      CrossCentralExactFaceCertifiedRebaseArc.source
      CrossCentralExactFaceCertifiedRebaseArc.target
      (fun state => witness.edge.1 ∈ witness.channel.edges state)
      middleFirst middleRest hmiddleChain
      witness.edge_mem_source hlastTarget with
    ⟨lossArc, hlossMem, hlossSource, hlossTarget⟩
  exact ⟨lossArc, hlossMem, hlossSource, hlossTarget,
    hmiddleFaces lossArc hlossMem⟩

/-- Every outside recovery witness from a displayed constant-face block
lifts to a transfer carrying a localized source-face loss. -/
theorem OutsideClosureRecoveryWitness.exists_faceTransfer
    (rebaseCircuit : CrossCentralExactFaceCertifiedRebaseCircuit graphData
      minimal baseData)
    (middleFace : OrbitFace graphData.toRotationSystem)
    (left middleFirst right :
      CrossCentralExactFaceCertifiedRebaseArc graphData minimal baseData)
    (before middleRest after : List
      (CrossCentralExactFaceCertifiedRebaseArc graphData minimal baseData))
    (hsplit : rebaseCircuit.first :: rebaseCircuit.rest =
      before ++
        (left :: ((middleFirst :: middleRest) ++ (right :: after))))
    (hmiddleFaces : ∀ arc ∈ middleFirst :: middleRest,
      arc.selectedFace = middleFace)
    (witness : OutsideClosureRecoveryWitness middleFace
      middleFirst.source right.source
        (right :: (after ++ before ++ [left]))) :
    Nonempty (ClosureRecoveryFaceTransfer rebaseCircuit) := by
  rcases witness.exists_lossArc_on_middleBlock rebaseCircuit middleFace
      left middleFirst right before middleRest after hsplit hmiddleFaces with
    ⟨lossArc, hlossMem, hlossSource, hlossTarget, hlossFace⟩
  have hlossDisplayed : lossArc ∈
      rebaseCircuit.first :: rebaseCircuit.rest := by
    rw [hsplit]
    exact List.mem_append_right before
      (List.mem_cons_of_mem left
        (List.mem_append_left (right :: after) hlossMem))
  have hrecoveryDisplayed : witness.recoveryArc ∈
      rebaseCircuit.first :: rebaseCircuit.rest :=
    rebaseCircuit.outside_subset_displayed_of_middleBlock_split
      left middleFirst right before middleRest after hsplit
      witness.recoveryArc witness.recoveryArc_mem_outside
  exact ⟨{
    recovery := {
      sourceFace := middleFace
      targetFace := witness.recoveryArc.selectedFace
      channel := witness.channel
      edge := witness.edge
      recoveryArc := witness.recoveryArc
      recoveryArc_mem_displayed := hrecoveryDisplayed
      recoveryArc_selectedFace := rfl
      edge_not_mem_sourceFace := witness.edge_not_mem_middleFace
      edge_not_mem_recoverySource := witness.edge_not_mem_recoverySource
      edge_mem_recoveryTarget := witness.edge_mem_recoveryTarget
      edge_mem_targetFace := witness.edge_mem_recoveryFace
      targetFace_ne_sourceFace := witness.recoveryFace_ne_middleFace }
    lossArc := lossArc
    lossArc_mem_displayed := hlossDisplayed
    lossArc_selectedFace := hlossFace
    edge_mem_lossSource := hlossSource
    edge_not_mem_lossTarget := hlossTarget }⟩

/-- The shortest-circuit backtrack trichotomy can retain the concrete
source-face loss instead of projecting immediately to a face relation. -/
theorem IsLengthMinimal.middleBlock_nonzeroComplementProfile_or_recoveryFaceTransfer
    {rebaseCircuit : CrossCentralExactFaceCertifiedRebaseCircuit graphData
      minimal baseData}
    (hminimal : rebaseCircuit.IsLengthMinimal)
    (firstFace secondFace : OrbitFace graphData.toRotationSystem)
    (hfaces : firstFace ≠ secondFace)
    (left middleFirst right :
      CrossCentralExactFaceCertifiedRebaseArc graphData minimal baseData)
    (before middleRest after : List
      (CrossCentralExactFaceCertifiedRebaseArc graphData minimal baseData))
    (hsplit : rebaseCircuit.first :: rebaseCircuit.rest =
      before ++
        (left :: ((middleFirst :: middleRest) ++ (right :: after))))
    (hleftFace : left.selectedFace = firstFace)
    (hmiddleFaces : ∀ arc ∈ middleFirst :: middleRest,
      arc.selectedFace = secondFace)
    (hrightFace : right.selectedFace = firstFace) :
    MiddleBlockNonzeroComplementProfile middleFirst right middleRest ∨
      Nonempty (ClosureRecoveryFaceTransfer rebaseCircuit) := by
  rcases
      hminimal.middleBlock_nonzeroComplementProfile_or_outside_prefixRecovery_or_suffixRecovery
        firstFace secondFace hfaces left middleFirst right before middleRest
          after hsplit hleftFace hmiddleFaces hrightFace with
    hnormal | hprefix | hsuffix
  · exact Or.inl hnormal
  · right
    rcases OutsideClosureRecoveryWitness.exists_of_prefix secondFace
        middleFirst.source right.source
          (right :: (after ++ before ++ [left])) hprefix with
      ⟨witness⟩
    exact witness.exists_faceTransfer rebaseCircuit secondFace left
      middleFirst right before middleRest after hsplit hmiddleFaces
  · right
    rcases OutsideClosureRecoveryWitness.exists_of_suffix secondFace
        middleFirst.source right.source
          (right :: (after ++ before ++ [left])) hsuffix with
      ⟨witness⟩
    exact witness.exists_faceTransfer rebaseCircuit secondFace left
      middleFirst right before middleRest after hsplit hmiddleFaces

/-- The provenance-retaining face relation consists of concrete transfers
whose loss is selected on the source face and whose gain is selected on the
target face. -/
def ClosureRecoveryFaceTransferDependency
    (rebaseCircuit : CrossCentralExactFaceCertifiedRebaseCircuit graphData
      minimal baseData)
    (sourceFace targetFace : OrbitFace graphData.toRotationSystem) : Prop :=
  ∃ transfer : ClosureRecoveryFaceTransfer rebaseCircuit,
    transfer.recovery.sourceFace = sourceFace ∧
      transfer.recovery.targetFace = targetFace

/-- The provenance-retaining relation refines the original recovery-face
dependency relation. -/
theorem ClosureRecoveryFaceTransferDependency.to_faceDependency
    {rebaseCircuit : CrossCentralExactFaceCertifiedRebaseCircuit graphData
      minimal baseData}
    {sourceFace targetFace : OrbitFace graphData.toRotationSystem}
    (dependency : rebaseCircuit.ClosureRecoveryFaceTransferDependency
      sourceFace targetFace) :
    rebaseCircuit.ClosureRecoveryFaceDependency sourceFace targetFace := by
  rcases dependency with ⟨transfer, hsource, htarget⟩
  simpa [hsource, htarget] using transfer.to_faceDependency

/-- A provenance-retaining transfer dependency never loops at one face. -/
theorem ClosureRecoveryFaceTransferDependency.ne
    {rebaseCircuit : CrossCentralExactFaceCertifiedRebaseCircuit graphData
      minimal baseData}
    {sourceFace targetFace : OrbitFace graphData.toRotationSystem}
    (dependency : rebaseCircuit.ClosureRecoveryFaceTransferDependency
      sourceFace targetFace) :
    targetFace ≠ sourceFace :=
  dependency.to_faceDependency.ne

/-- The target of a provenance-retaining transfer remains a selected face
of the rebase circuit. -/
theorem ClosureRecoveryFaceTransferDependency.targetFace_mem_selectedFaces
    {rebaseCircuit : CrossCentralExactFaceCertifiedRebaseCircuit graphData
      minimal baseData}
    {sourceFace targetFace : OrbitFace graphData.toRotationSystem}
    (dependency : rebaseCircuit.ClosureRecoveryFaceTransferDependency
      sourceFace targetFace) :
    targetFace ∈ rebaseCircuit.selectedFaces :=
  dependency.to_faceDependency.recoveryFace_mem_selectedFaces

end CrossCentralExactFaceCertifiedRebaseCircuit

/-- Consecutive provenance-retaining transfers meet at their dependency
face. -/
def ClosureRecoveryFaceTransfer.Follows
    {rebaseCircuit : CrossCentralExactFaceCertifiedRebaseCircuit graphData
      minimal baseData}
    (first second : ClosureRecoveryFaceTransfer rebaseCircuit) : Prop :=
  first.recovery.targetFace = second.recovery.sourceFace

/-- A nonempty cyclic list of recovery transfers retaining a localized
source-face loss at every dependency. -/
structure ClosureRecoveryFaceTransferCircuit
    (rebaseCircuit : CrossCentralExactFaceCertifiedRebaseCircuit graphData
      minimal baseData) where
  first : ClosureRecoveryFaceTransfer rebaseCircuit
  rest : List (ClosureRecoveryFaceTransfer rebaseCircuit)
  consecutive : List.IsChain ClosureRecoveryFaceTransfer.Follows
    (first :: rest)
  closing : ClosureRecoveryFaceTransfer.Follows
    ((first :: rest).getLast (by simp)) first

namespace ClosureRecoveryFaceTransferCircuit

variable {rebaseCircuit :
  CrossCentralExactFaceCertifiedRebaseCircuit graphData minimal baseData}

/-- A cyclic transfer relation lifts to a concrete cyclic list retaining
the loss and gain arcs at every step. -/
theorem exists_of_transGen_cycle
    {face : OrbitFace graphData.toRotationSystem}
    (cycle : Relation.TransGen
      rebaseCircuit.ClosureRecoveryFaceTransferDependency face face) :
    Nonempty (ClosureRecoveryFaceTransferCircuit rebaseCircuit) := by
  have existsTransferChain : ∀ {source target :
      OrbitFace graphData.toRotationSystem},
      Relation.TransGen
          rebaseCircuit.ClosureRecoveryFaceTransferDependency source target →
        ∃ (first : ClosureRecoveryFaceTransfer rebaseCircuit)
            (rest : List (ClosureRecoveryFaceTransfer rebaseCircuit)),
          List.IsChain ClosureRecoveryFaceTransfer.Follows (first :: rest) ∧
            first.recovery.sourceFace = source ∧
            ((first :: rest).getLast (by simp)).recovery.targetFace =
              target := by
    intro source target run
    induction run using Relation.TransGen.head_induction_on with
    | single dependency =>
        rcases dependency with ⟨transfer, hsource, htarget⟩
        exact ⟨transfer, [], List.IsChain.singleton _, hsource,
          by simpa using htarget⟩
    | @head source middle dependency run ih =>
        rcases dependency with ⟨transfer, hsource, htarget⟩
        rcases ih with ⟨first, rest, hchain, hfirstSource, hlastTarget⟩
        refine ⟨transfer, first :: rest, ?_, hsource, ?_⟩
        · apply List.IsChain.cons_cons
          · exact htarget.trans hfirstSource.symm
          · exact hchain
        · simpa using hlastTarget
  rcases existsTransferChain cycle with
    ⟨first, rest, hchain, hsource, htarget⟩
  exact ⟨{
    first := first
    rest := rest
    consecutive := hchain
    closing := htarget.trans hsource.symm }⟩

/-- Forgetting every localized loss turns a transfer circuit into the
corresponding concrete recovery circuit. -/
def toRecoveryFaceCircuit
    (circuit : ClosureRecoveryFaceTransferCircuit rebaseCircuit) :
    ClosureRecoveryFaceCircuit rebaseCircuit := {
  first := circuit.first.recovery
  rest := circuit.rest.map ClosureRecoveryFaceTransfer.recovery
  consecutive := by
    change List.IsChain ClosureRecoveryFaceArc.Follows
      ((circuit.first :: circuit.rest).map
        ClosureRecoveryFaceTransfer.recovery)
    rw [List.isChain_map]
    exact circuit.consecutive
  closing := by
    change (((circuit.first :: circuit.rest).map
      ClosureRecoveryFaceTransfer.recovery).getLast
        (by simp)).targetFace = circuit.first.recovery.sourceFace
    calc
      (((circuit.first :: circuit.rest).map
          ClosureRecoveryFaceTransfer.recovery).getLast
            (by simp)).targetFace =
          ((circuit.first :: circuit.rest).getLast
            (by simp)).recovery.targetFace := by
        exact congrArg
          (fun recovery : ClosureRecoveryFaceArc rebaseCircuit =>
            recovery.targetFace)
          (List.getLast_map _)
      _ = circuit.first.recovery.sourceFace := by
        simpa [ClosureRecoveryFaceTransfer.Follows] using circuit.closing }

/-- The projected recovery list is exactly the pointwise loss-forgetting
image of the transfer list. -/
@[simp] theorem toRecoveryFaceCircuit_dependencies
    (circuit : ClosureRecoveryFaceTransferCircuit rebaseCircuit) :
    circuit.toRecoveryFaceCircuit.first ::
        circuit.toRecoveryFaceCircuit.rest =
      (circuit.first :: circuit.rest).map
        ClosureRecoveryFaceTransfer.recovery := by
  simp [toRecoveryFaceCircuit]

/-- Projection preserves the number of cyclic dependencies. -/
@[simp] theorem toRecoveryFaceCircuit_arcLength
    (circuit : ClosureRecoveryFaceTransferCircuit rebaseCircuit) :
    circuit.toRecoveryFaceCircuit.arcLength =
      (circuit.first :: circuit.rest).length := by
  simp [ClosureRecoveryFaceCircuit.arcLength]

/-- Every dependency in the projected recovery circuit still has a
displayed support loss selected on its source face. -/
theorem exists_sourceFace_loss_of_mem_toRecoveryFaceCircuit
    (circuit : ClosureRecoveryFaceTransferCircuit rebaseCircuit)
    (recovery : ClosureRecoveryFaceArc rebaseCircuit)
    (hrecovery : recovery ∈
      circuit.toRecoveryFaceCircuit.first ::
        circuit.toRecoveryFaceCircuit.rest) :
    ∃ lossArc :
        CrossCentralExactFaceCertifiedRebaseArc graphData minimal baseData,
      lossArc ∈ rebaseCircuit.first :: rebaseCircuit.rest ∧
        lossArc.selectedFace = recovery.sourceFace ∧
        recovery.edge.1 ∈ recovery.channel.edges lossArc.source ∧
        recovery.edge.1 ∉ recovery.channel.edges lossArc.target := by
  rw [circuit.toRecoveryFaceCircuit_dependencies] at hrecovery
  rcases List.mem_map.mp hrecovery with
    ⟨transfer, htransferMem, htransfer⟩
  subst recovery
  exact ⟨transfer.lossArc, transfer.lossArc_mem_displayed,
    transfer.lossArc_selectedFace, transfer.edge_mem_lossSource,
    transfer.edge_not_mem_lossTarget⟩

end ClosureRecoveryFaceTransferCircuit

namespace CrossCentralExactFaceCertifiedRebaseCircuit

/-- If every selected face has an outgoing provenance-retaining transfer,
the finite selected-face relation contains a concrete transfer circuit. -/
theorem exists_recoveryFaceTransferCircuit_of_forall_outgoing
    (rebaseCircuit : CrossCentralExactFaceCertifiedRebaseCircuit graphData
      minimal baseData)
    (houtgoing : ∀ sourceFace ∈ rebaseCircuit.selectedFaces,
      ∃ targetFace,
        rebaseCircuit.ClosureRecoveryFaceTransferDependency
          sourceFace targetFace) :
    Nonempty (ClosureRecoveryFaceTransferCircuit rebaseCircuit) := by
  classical
  have htotal : ∀ face,
      face ∉ rebaseCircuit.selectedFaces ∨
        ∃ target,
          rebaseCircuit.ClosureRecoveryFaceTransferDependency
            face target := by
    intro face
    by_cases hface : face ∈ rebaseCircuit.selectedFaces
    · exact Or.inr (houtgoing face hface)
    · exact Or.inl hface
  have hreachableMem : ∀ {start target},
      start ∈ rebaseCircuit.selectedFaces →
        Relation.ReflTransGen
            rebaseCircuit.ClosureRecoveryFaceTransferDependency
            start target →
          target ∈ rebaseCircuit.selectedFaces := by
    intro start target hstart reachable
    induction reachable with
    | refl => exact hstart
    | tail _ dependency _ =>
        exact dependency.targetFace_mem_selectedFaces
  rcases rebaseCircuit.selectedFaces_nonempty with ⟨start, hstart⟩
  rcases finite_reflTransGen_terminal_or_transGen_cycle
      rebaseCircuit.ClosureRecoveryFaceTransferDependency
      (fun face => face ∉ rebaseCircuit.selectedFaces) htotal start with
    hterminal | hcycle
  · rcases hterminal with ⟨finish, hreachable, hfinish⟩
    exact False.elim
      (hfinish (hreachableMem hstart hreachable))
  · rcases hcycle with ⟨face, hreachable, hclosed⟩
    exact ClosureRecoveryFaceTransferCircuit.exists_of_transGen_cycle hclosed

end CrossCentralExactFaceCertifiedRebaseCircuit

end GoertzelV24AdjacentPairInsertion.AdjacentPairData

end

end Mettapedia.GraphTheory.FourColor
