import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairAmbientClosureCrossFacePairDifferenceBoundaryFaceFusionChainRebaseFaceCircuitRecoveryCode

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

namespace GoertzelV24RebaseFaceCircuit

/-- Along a nonempty composable arc list, an endpoint change from
presence to absence is witnessed by one arc. -/
theorem exists_entry_loss_of_endpoint_loss
    {State Entry : Type*} (source target : Entry → State)
    (property : State → Prop)
    (first : Entry) (rest : List Entry)
    (chain : List.IsChain (fun left right =>
      target left = source right) (first :: rest))
    (hsource : property (source first))
    (htarget : ¬ property
      (target ((first :: rest).getLast (by simp)))) :
    ∃ entry ∈ first :: rest,
      property (source entry) ∧ ¬ property (target entry) := by
  induction rest generalizing first with
  | nil =>
      exact ⟨first, by simp, hsource, by simpa using htarget⟩
  | cons second rest ih =>
      have hparts := List.isChain_cons_cons.mp chain
      by_cases hfirstTarget : property (target first)
      · have hsecondSource : property (source second) := by
          rw [← hparts.1]
          exact hfirstTarget
        have htailTarget : ¬ property
            (target ((second :: rest).getLast (by simp))) := by
          simpa using htarget
        rcases ih second hparts.2 hsecondSource htailTarget with
          ⟨entry, hentry, hentrySource, hentryTarget⟩
        exact ⟨entry, List.mem_cons_of_mem first hentry,
          hentrySource, hentryTarget⟩
      · exact ⟨first, by simp, hsource, hfirstTarget⟩

/-- If a composable list displays a present endpoint before a later
absent endpoint, the strict intervening list is nonempty and contains a
loss. -/
theorem exists_entry_loss_between_of_split
    {State Entry : Type*} (source target : Entry → State)
    (property : State → Prop)
    (displayed : List Entry)
    (chain : List.IsChain (fun left right =>
      target left = source right) displayed)
    (left right : Entry) (before between after : List Entry)
    (hsplit : displayed =
      before ++ (left :: (between ++ (right :: after))))
    (hleftTarget : property (target left))
    (hrightSource : ¬ property (source right)) :
    ∃ entry ∈ between,
      property (source entry) ∧ ¬ property (target entry) := by
  let leftSegment := left :: between
  have hfullChain : List.IsChain (fun left right =>
      target left = source right)
      (before ++ (leftSegment ++ (right :: after))) := by
    have hchain := chain
    rw [hsplit] at hchain
    simpa [leftSegment, List.append_assoc] using hchain
  have hsegmentAfterChain : List.IsChain (fun left right =>
      target left = source right) (leftSegment ++ (right :: after)) :=
    (List.isChain_append.mp hfullChain).2.1
  have hparts := List.isChain_append.mp hsegmentAfterChain
  have hbetweenNe : between ≠ [] := by
    intro hbetween
    have hfollow : target left = source right := by
      have hcross := hparts.2.2 left (by simp [leftSegment, hbetween])
        right (by simp)
      simpa [leftSegment, hbetween] using hcross
    exact hrightSource (hfollow ▸ hleftTarget)
  rcases between with _ | ⟨middleFirst, middleRest⟩
  · exact False.elim (hbetweenNe rfl)
  · have hleftParts := List.isChain_cons_cons.mp hparts.1
    have hmiddleTarget : ¬ property
        (target ((middleFirst :: middleRest).getLast (by simp))) := by
      have hcross := hparts.2.2
        ((middleFirst :: middleRest).getLast (by simp))
        (by
          rw [List.getLast?_eq_getLast_of_ne_nil (by simp)]
          simp [leftSegment])
        right (by simp)
      intro hmiddle
      apply hrightSource
      rw [← hcross]
      exact hmiddle
    have hmiddleSource : property (source middleFirst) := by
      rw [← hleftParts.1]
      exact hleftTarget
    exact exists_entry_loss_of_endpoint_loss source target property
      middleFirst middleRest hleftParts.2 hmiddleSource hmiddleTarget

/-- Two increasing positions split a list at their displayed entries. -/
theorem exists_split_at_two_positions
    {Entry : Type*} (displayed : List Entry)
    (first second : Fin displayed.length) (hlt : first < second) :
    ∃ before between after,
      displayed = before ++
        (displayed.get first ::
          (between ++ (displayed.get second :: after))) := by
  let tail := displayed.drop (first.1 + 1)
  let gap : Nat := second.1 - (first.1 + 1)
  have hgap : gap < tail.length := by
    simp [gap, tail]
    omega
  have htailGet : tail[gap] = displayed.get second := by
    change (displayed.drop (first.1 + 1))[gap] = displayed[second.1]
    rw [List.getElem_drop]
    congr 1
    simp [gap]
    omega
  have htail : tail = tail.take gap ++
      (displayed.get second :: tail.drop (gap + 1)) := by
    calc
      tail = tail.take gap ++ tail.drop gap :=
        (List.take_append_drop gap tail).symm
      _ = tail.take gap ++
          (tail[gap] :: tail.drop (gap + 1)) := by
            rw [List.drop_eq_getElem_cons hgap]
      _ = tail.take gap ++
          (displayed.get second :: tail.drop (gap + 1)) := by
            exact congrArg (fun entry => tail.take gap ++
              (entry :: tail.drop (gap + 1))) htailGet
  refine ⟨displayed.take first, tail.take gap, tail.drop (gap + 1), ?_⟩
  calc
    displayed = displayed.take first ++ displayed.drop first :=
      (List.take_append_drop first displayed).symm
    _ = displayed.take first ++
        (displayed.get first :: displayed.drop (first + 1)) := by
          simpa only [List.get_eq_getElem] using congrArg
            (fun rest => displayed.take first ++ rest)
            (List.drop_eq_getElem_cons first.isLt)
    _ = displayed.take first ++
        (displayed.get first :: tail) := by rfl
    _ = displayed.take first ++
        (displayed.get first ::
          (tail.take gap ++
            (displayed.get second :: tail.drop (gap + 1)))) := by
          exact congrArg
            (fun rest => displayed.take first ++
              (displayed.get first :: rest)) htail

end GoertzelV24RebaseFaceCircuit

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

namespace CrossCentralExactFaceCertifiedRebaseCircuit

/-- A shortest certified rebase circuit displays no arc twice. -/
theorem IsLengthMinimal.displayedArcs_nodup
    {circuit : CrossCentralExactFaceCertifiedRebaseCircuit graphData
      minimal baseData}
    (hminimal : circuit.IsLengthMinimal) :
    (circuit.first :: circuit.rest).Nodup := by
  rw [List.nodup_iff_pairwise_ne]
  have hsources : List.Pairwise
      (fun first second :
        CrossCentralExactFaceCertifiedRebaseArc graphData minimal baseData =>
        first.source ≠ second.source)
      (circuit.first :: circuit.rest) := by
    rw [← List.pairwise_map, ← List.nodup_iff_pairwise_ne]
    exact hminimal.sourceStates_nodup
  apply hsources.imp
  intro first second hsource harc
  exact hsource (congrArg CrossCentralExactFaceCertifiedRebaseArc.source harc)

end CrossCentralExactFaceCertifiedRebaseCircuit

namespace ClosureRecoveryFaceArc

variable {rebaseCircuit :
  CrossCentralExactFaceCertifiedRebaseCircuit graphData minimal baseData}

/-- Equal recovery codes at two displayed restoring arcs force a support
loss in the strict intervening rebase segment. -/
theorem exists_support_loss_between_of_same_code
    (left right : ClosureRecoveryFaceArc rebaseCircuit)
    (before between after : List
      (CrossCentralExactFaceCertifiedRebaseArc graphData minimal baseData))
    (hsplit : rebaseCircuit.first :: rebaseCircuit.rest =
      before ++ (left.recoveryArc ::
        (between ++ (right.recoveryArc :: after))))
    (hcode : left.code = right.code) :
    ∃ lossArc ∈ between,
      left.edge.1 ∈ left.channel.edges lossArc.source ∧
        left.edge.1 ∉ left.channel.edges lossArc.target := by
  have hchannel : left.channel = right.channel :=
    congrArg Prod.fst hcode
  have hedge : left.edge = right.edge :=
    congrArg Prod.snd hcode
  have hrightSource : left.edge.1 ∉
      left.channel.edges right.recoveryArc.source := by
    simpa [hchannel, hedge] using right.edge_not_mem_recoverySource
  exact GoertzelV24RebaseFaceCircuit.exists_entry_loss_between_of_split
    CrossCentralExactFaceCertifiedRebaseArc.source
    CrossCentralExactFaceCertifiedRebaseArc.target
    (fun state => left.edge.1 ∈ left.channel.edges state)
    (rebaseCircuit.first :: rebaseCircuit.rest)
    rebaseCircuit.consecutive left.recoveryArc right.recoveryArc
    before between after hsplit left.edge_mem_recoveryTarget hrightSource

/-- The complementary cyclic interval contains another loss for the same
channel and edge. -/
theorem exists_two_sided_support_losses_of_same_code
    (left right : ClosureRecoveryFaceArc rebaseCircuit)
    (before between after : List
      (CrossCentralExactFaceCertifiedRebaseArc graphData minimal baseData))
    (hsplit : rebaseCircuit.first :: rebaseCircuit.rest =
      before ++ (left.recoveryArc ::
        (between ++ (right.recoveryArc :: after))))
    (hcode : left.code = right.code) :
    (∃ lossArc ∈ between,
      left.edge.1 ∈ left.channel.edges lossArc.source ∧
        left.edge.1 ∉ left.channel.edges lossArc.target) ∧
      (∃ lossArc ∈ after ++ before,
        left.edge.1 ∈ left.channel.edges lossArc.source ∧
          left.edge.1 ∉ left.channel.edges lossArc.target) := by
  have hforward := left.exists_support_loss_between_of_same_code right
    before between after hsplit hcode
  have hchannel : left.channel = right.channel :=
    congrArg Prod.fst hcode
  have hedge : left.edge = right.edge :=
    congrArg Prod.snd hcode
  let rightPrefix := before ++ (left.recoveryArc :: between)
  have hsplitRight : rebaseCircuit.first :: rebaseCircuit.rest =
      rightPrefix ++ (right.recoveryArc :: after) := by
    simpa [rightPrefix, List.append_assoc] using hsplit
  let rotated := rebaseCircuit.rotateAtSplit right.recoveryArc rightPrefix after
    hsplitRight
  have hrotatedSplit : rotated.first :: rotated.rest =
      [] ++ (right.recoveryArc ::
        ((after ++ before) ++ (left.recoveryArc :: between))) := by
    simp [rotated, rightPrefix, List.append_assoc]
  have hrightTarget : left.edge.1 ∈
      left.channel.edges right.recoveryArc.target := by
    simpa [hchannel, hedge] using right.edge_mem_recoveryTarget
  have hbackward :=
    GoertzelV24RebaseFaceCircuit.exists_entry_loss_between_of_split
      CrossCentralExactFaceCertifiedRebaseArc.source
      CrossCentralExactFaceCertifiedRebaseArc.target
      (fun state => left.edge.1 ∈ left.channel.edges state)
      (rotated.first :: rotated.rest) rotated.consecutive
      right.recoveryArc left.recoveryArc [] (after ++ before) between
      hrotatedSplit hrightTarget left.edge_not_mem_recoverySource
  exact ⟨hforward, hbackward⟩

end ClosureRecoveryFaceArc

/-- Two equal recovery gains together with one balancing loss in each
complementary interval of the underlying rebase circuit. -/
structure ClosureRecoveryCodeAlternation
    (rebaseCircuit : CrossCentralExactFaceCertifiedRebaseCircuit graphData
      minimal baseData)
    (recoveryCircuit : ClosureRecoveryFaceCircuit rebaseCircuit) where
  earlier : Fin recoveryCircuit.arcLength
  later : Fin recoveryCircuit.arcLength
  restoring_lt : recoveryCircuit.restoringPositionAt earlier <
    recoveryCircuit.restoringPositionAt later
  code_eq : recoveryCircuit.codeAt earlier = recoveryCircuit.codeAt later
  before : List
    (CrossCentralExactFaceCertifiedRebaseArc graphData minimal baseData)
  between : List
    (CrossCentralExactFaceCertifiedRebaseArc graphData minimal baseData)
  after : List
    (CrossCentralExactFaceCertifiedRebaseArc graphData minimal baseData)
  displayed_split : rebaseCircuit.first :: rebaseCircuit.rest =
    before ++ ((recoveryCircuit.dependencyAt earlier).recoveryArc ::
      (between ++
        ((recoveryCircuit.dependencyAt later).recoveryArc :: after)))
  forwardLoss :
    CrossCentralExactFaceCertifiedRebaseArc graphData minimal baseData
  forwardLoss_mem : forwardLoss ∈ between
  forwardLoss_source_mem :
    (recoveryCircuit.dependencyAt earlier).edge.1 ∈
      (recoveryCircuit.dependencyAt earlier).channel.edges
        forwardLoss.source
  forwardLoss_target_not_mem :
    (recoveryCircuit.dependencyAt earlier).edge.1 ∉
      (recoveryCircuit.dependencyAt earlier).channel.edges
        forwardLoss.target
  backwardLoss :
    CrossCentralExactFaceCertifiedRebaseArc graphData minimal baseData
  backwardLoss_mem : backwardLoss ∈ after ++ before
  backwardLoss_source_mem :
    (recoveryCircuit.dependencyAt earlier).edge.1 ∈
      (recoveryCircuit.dependencyAt earlier).channel.edges
        backwardLoss.source
  backwardLoss_target_not_mem :
    (recoveryCircuit.dependencyAt earlier).edge.1 ∉
      (recoveryCircuit.dependencyAt earlier).channel.edges
        backwardLoss.target

namespace ClosureRecoveryCodeAlternation

variable {rebaseCircuit :
  CrossCentralExactFaceCertifiedRebaseCircuit graphData minimal baseData}
  {recoveryCircuit : ClosureRecoveryFaceCircuit rebaseCircuit}

theorem between_ne_nil
    (alternation : ClosureRecoveryCodeAlternation rebaseCircuit
      recoveryCircuit) :
    alternation.between ≠ [] :=
  List.ne_nil_of_mem alternation.forwardLoss_mem

theorem complement_ne_nil
    (alternation : ClosureRecoveryCodeAlternation rebaseCircuit
      recoveryCircuit) :
    alternation.after ++ alternation.before ≠ [] :=
  List.ne_nil_of_mem alternation.backwardLoss_mem

/-- On a shortest underlying rebase circuit, the balancing losses in the
two complementary intervals are different arcs. -/
theorem forwardLoss_ne_backwardLoss
    (alternation : ClosureRecoveryCodeAlternation rebaseCircuit
      recoveryCircuit)
    (hrebaseMinimal : rebaseCircuit.IsLengthMinimal) :
    alternation.forwardLoss ≠ alternation.backwardLoss := by
  have hnodup := hrebaseMinimal.displayedArcs_nodup
  rw [alternation.displayed_split] at hnodup
  have hpairwise := List.nodup_iff_pairwise_ne.mp hnodup
  rcases List.mem_append.mp alternation.backwardLoss_mem with
    hafter | hbefore
  · have hsuffix := (List.pairwise_append.mp hpairwise).2.1
    have htail := (List.pairwise_cons.mp hsuffix).2
    have hcross := (List.pairwise_append.mp htail).2.2
    exact hcross alternation.forwardLoss alternation.forwardLoss_mem
      alternation.backwardLoss
        (List.mem_cons_of_mem _ hafter)
  · have hcross := (List.pairwise_append.mp hpairwise).2.2
    have hforwardRest : alternation.forwardLoss ∈
        (recoveryCircuit.dependencyAt alternation.earlier).recoveryArc ::
          (alternation.between ++
            ((recoveryCircuit.dependencyAt alternation.later).recoveryArc ::
              alternation.after)) :=
      List.mem_cons_of_mem _
        (List.mem_append_left _ alternation.forwardLoss_mem)
    exact (hcross alternation.backwardLoss hbefore
      alternation.forwardLoss hforwardRest).symm

end ClosureRecoveryCodeAlternation

namespace ClosureRecoveryFaceCircuit

variable {rebaseCircuit :
  CrossCentralExactFaceCertifiedRebaseCircuit graphData minimal baseData}

/-- An ordered pair of equal recovery codes produces a concrete cyclic
gain/loss alternation. -/
theorem exists_codeAlternation_of_restoringPositionAt_lt
    (circuit : ClosureRecoveryFaceCircuit rebaseCircuit)
    (earlier later : Fin circuit.arcLength)
    (hlt : circuit.restoringPositionAt earlier <
      circuit.restoringPositionAt later)
    (hcode : circuit.codeAt earlier = circuit.codeAt later) :
    Nonempty (ClosureRecoveryCodeAlternation rebaseCircuit circuit) := by
  let displayed := rebaseCircuit.first :: rebaseCircuit.rest
  rcases GoertzelV24RebaseFaceCircuit.exists_split_at_two_positions
      displayed (circuit.restoringPositionAt earlier)
        (circuit.restoringPositionAt later) hlt with
    ⟨before, between, after, hsplit⟩
  dsimp only [displayed] at hsplit
  simp only [restoringPositionAt] at hsplit
  rw [(circuit.dependencyAt earlier).get_restoringPosition,
    (circuit.dependencyAt later).get_restoringPosition] at hsplit
  have hsplit' : rebaseCircuit.first :: rebaseCircuit.rest =
      before ++ ((circuit.dependencyAt earlier).recoveryArc ::
        (between ++
          ((circuit.dependencyAt later).recoveryArc :: after))) := by
    exact hsplit
  rcases
      (circuit.dependencyAt earlier).exists_two_sided_support_losses_of_same_code
        (circuit.dependencyAt later) before between after hsplit' hcode with
    ⟨⟨forwardLoss, hforwardMem, hforwardSource, hforwardTarget⟩,
      ⟨backwardLoss, hbackwardMem, hbackwardSource, hbackwardTarget⟩⟩
  exact ⟨{
    earlier := earlier
    later := later
    restoring_lt := hlt
    code_eq := hcode
    before := before
    between := between
    after := after
    displayed_split := hsplit'
    forwardLoss := forwardLoss
    forwardLoss_mem := hforwardMem
    forwardLoss_source_mem := hforwardSource
    forwardLoss_target_not_mem := hforwardTarget
    backwardLoss := backwardLoss
    backwardLoss_mem := hbackwardMem
    backwardLoss_source_mem := hbackwardSource
    backwardLoss_target_not_mem := hbackwardTarget }⟩

/-- A code collision on a shortest recovery circuit therefore supplies
a cyclic gain/loss alternation, in whichever restoring order occurs. -/
theorem IsLengthMinimal.exists_codeAlternation_of_code_collision
    {circuit : ClosureRecoveryFaceCircuit rebaseCircuit}
    (hminimal : circuit.IsLengthMinimal)
    (collision : ∃ first second : Fin circuit.arcLength,
      first ≠ second ∧ circuit.codeAt first = circuit.codeAt second) :
    Nonempty (ClosureRecoveryCodeAlternation rebaseCircuit circuit) := by
  rcases collision with ⟨first, second, hne, hcode⟩
  have hpositionNe : circuit.restoringPositionAt first ≠
      circuit.restoringPositionAt second := by
    intro hposition
    exact hne (hminimal.restoringPositionAt_injective hposition)
  rcases lt_or_gt_of_ne hpositionNe with hlt | hgt
  · exact circuit.exists_codeAlternation_of_restoringPositionAt_lt
      first second hlt hcode
  · exact circuit.exists_codeAlternation_of_restoringPositionAt_lt
      second first hgt hcode.symm

/-- The finite-code dichotomy can now expose a concrete alternating
gain/loss configuration in its collision branch. -/
theorem IsLengthMinimal.arcLength_le_twice_card_edges_or_codeAlternation
    {circuit : ClosureRecoveryFaceCircuit rebaseCircuit}
    (hminimal : circuit.IsLengthMinimal) :
    circuit.arcLength ≤ 2 * Fintype.card G.edgeSet ∨
      Nonempty (ClosureRecoveryCodeAlternation rebaseCircuit circuit) := by
  rcases circuit.arcLength_le_twice_card_edges_or_exists_code_collision with
    hbound | hcollision
  · exact Or.inl hbound
  · exact Or.inr
      (hminimal.exists_codeAlternation_of_code_collision hcollision)

end ClosureRecoveryFaceCircuit

end GoertzelV24AdjacentPairInsertion.AdjacentPairData

end

end Mettapedia.GraphTheory.FourColor
