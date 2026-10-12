import Mettapedia.GSLT.Causality.PaidProbeCampaign

/-!
# Extra funding for supplied paid probe histories

Replay retains the selected rule instances in their original order. A frame
of additional resources is carried through every actual firing; specializing
the frame to currency leaves the assay resources and their response readout
unchanged. Sequential campaign replay threads the enlarged remaining purse
through those same supplied rounds. This does not select a new schedule or
claim that arbitrary executions become more informative with more funding.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Causality.ResourceInteraction

open OccurrenceHistory

universe uRes uRule uObs

namespace System

variable {R : Type uRes} (S : System.{uRes, uRule} R) [DecidableEq R]

omit [DecidableEq R] in
theorem enables_add_frame {M : Multiset R} {site : S.Site}
    (firing : S.Instance site) (enabled : S.Enables M firing) (frame : Multiset R) :
    S.Enables (M + frame) firing :=
  enabled.trans (Multiset.le_add_right M frame)

theorem fire_add_frame {M : Multiset R} {site : S.Site}
    (firing : S.Instance site) (enabled : S.Enables M firing) (frame : Multiset R) :
    S.fire (M + frame) firing = S.fire M firing + frame := by
  have consumed : S.consume firing ≤ M :=
    (Multiset.le_add_right (S.consume firing) (S.read firing)).trans enabled
  unfold fire
  rw [← tsub_add_eq_add_tsub consumed]
  ac_rfl

/-- Every occurrence is replayed with its original site and instance. -/
def replayFrame : {M N : Multiset R} →
    OccurrencePath S.presentation M N → (frame : Multiset R) →
      OccurrencePath S.presentation (M + frame) (N + frame)
  | _, _, .refl _, _ => .refl _
  | _, _, .cons occurrence rest, frame =>
      .cons ⟨occurrence.site,
        ⟨occurrence.evidence.val,
          S.enables_add_frame occurrence.evidence.val occurrence.evidence.property.1 frame,
          (congrArg (fun resources : Multiset R => resources + frame)
            occurrence.evidence.property.2).trans
            (S.fire_add_frame occurrence.evidence.val occurrence.evidence.property.1 frame).symm⟩⟩
        (replayFrame rest frame)

theorem replayFrame_pathEntries : ∀ {M N : Multiset R}
    (path : OccurrencePath S.presentation M N) (frame : Multiset R),
    S.pathEntries (S.replayFrame path frame) = S.pathEntries path
  | _, _, .refl _, _ => rfl
  | _, _, .cons occurrence rest, frame => by
      change (⟨occurrence.site, occurrence.evidence.val⟩ : S.Entry) ::
        S.pathEntries (S.replayFrame rest frame) = _
      rw [replayFrame_pathEntries rest frame]
      rfl

theorem replayFrame_sites : ∀ {M N : Multiset R}
    (path : OccurrencePath S.presentation M N) (frame : Multiset R),
    (S.replayFrame path frame).sites = path.sites
  | _, _, .refl _, _ => rfl
  | _, _, .cons occurrence rest, frame => by
      change occurrence.site :: _ = occurrence.site :: _
      rw [replayFrame_sites rest frame]

theorem replayFrame_valuation {A : Type uObs} [AddCommMonoid A]
    (value : ∀ {site : S.Site}, S.Instance site → A) {M N : Multiset R}
    (path : OccurrencePath S.presentation M N) (frame : Multiset R) :
    (S.instanceValuation @value).onPath (S.replayFrame path frame) =
      (S.instanceValuation @value).onPath path := by
  rw [S.instanceValuation_onPath, S.instanceValuation_onPath, S.replayFrame_pathEntries]

/-- In a resource presentation the starting marking and ordered instances
 determine the complete occurrence path, including all intermediate markings. -/
theorem path_heq_of_pathEntries_eq {M N : S.theory.Term}
    (first : OccurrencePath S.presentation M N) :
    ∀ {N' : S.theory.Term} (second : OccurrencePath S.presentation M N'),
    S.pathEntries first = S.pathEntries second → HEq first second := by
  induction first with
  | refl M =>
      intro N' second same
      cases second with
      | refl => exact HEq.rfl
      | cons occurrence rest => simp only [pathEntries] at same; contradiction
  | @cons M middle N occurrence rest inductionHypothesis =>
      intro N' second same
      cases second with
      | refl => simp only [pathEntries] at same; contradiction
      | @cons _ middle' _ occurrence' rest' =>
          obtain ⟨site, ⟨firing, enabled, endpoint⟩⟩ := occurrence
          obtain ⟨site', ⟨firing', enabled', endpoint'⟩⟩ := occurrence'
          change (⟨site, firing⟩ : S.Entry) :: S.pathEntries rest =
            (⟨site', firing'⟩ : S.Entry) :: S.pathEntries rest' at same
          obtain ⟨heads, tails⟩ := List.cons.inj same
          have sites : site = site' := congrArg Sigma.fst heads
          subst site'
          have firings : firing = firing' := eq_of_heq (Sigma.mk.inj heads).2
          subst firing'
          have middles : middle = middle' := endpoint.trans endpoint'.symm
          subst middle'
          subst middle
          have targets := S.target_eq_of_pathEntries_eq rest rest' tails
          have rests := inductionHypothesis rest' tails
          subst N'
          have sameRests := eq_of_heq rests
          subst rest'
          exact HEq.rfl

/-- Endpoint equality transports the retained path, rather than reconstructing
 it from an observation. -/
def castPath {M N M' N' : Multiset R} (source : M = M') (target : N = N')
    (path : OccurrencePath S.presentation M N) : OccurrencePath S.presentation M' N' :=
  source ▸ target ▸ path

theorem castPath_heq {M N M' N' : Multiset R} (source : M = M') (target : N = N')
    (path : OccurrencePath S.presentation M N) : HEq (S.castPath source target path) path := by
  cases source
  cases target
  rfl

theorem castPath_pathEntries {M N M' N' : Multiset R}
    (source : M = M') (target : N = N') (path : OccurrencePath S.presentation M N) :
    S.pathEntries (S.castPath source target path) = S.pathEntries path := by
  cases source
  cases target
  rfl

theorem replayFrame_zero {M N : Multiset R} (path : OccurrencePath S.presentation M N) :
    HEq (S.replayFrame path 0) path := by
  have same := S.path_heq_of_pathEntries_eq
    (S.castPath (add_zero M) (add_zero N) (S.replayFrame path 0)) path
    (by rw [S.castPath_pathEntries, S.replayFrame_pathEntries])
  exact (S.castPath_heq (add_zero M) (add_zero N) (S.replayFrame path 0)).symm.trans same

theorem replayFrame_add {M N : Multiset R} (path : OccurrencePath S.presentation M N)
    (first second : Multiset R) :
    HEq (S.replayFrame (S.replayFrame path first) second)
      (S.replayFrame path (first + second)) := by
  have same := S.path_heq_of_pathEntries_eq
    (S.castPath (add_assoc M first second) (add_assoc N first second)
      (S.replayFrame (S.replayFrame path first) second))
    (S.replayFrame path (first + second))
    (by rw [S.castPath_pathEntries, S.replayFrame_pathEntries,
      S.replayFrame_pathEntries, S.replayFrame_pathEntries])
  exact (S.castPath_heq (add_assoc M first second) (add_assoc N first second)
    (S.replayFrame (S.replayFrame path first) second)).symm.trans same

end System

end Mettapedia.GSLT.Causality.ResourceInteraction

namespace Mettapedia.GSLT.Causality.ProbeCampaign

open ResourceInteraction OccurrenceHistory
open ComplementaryAssay (purse)

universe q u v w

variable {Questions : Type q} {X : Type u} {Providers : Type v} {Clients : Type w}
variable [DecidableEq X] [DecidableEq Providers] [DecidableEq Clients]

private theorem purse_add (first extra : Nat) : purse (first + extra) = purse first + purse extra :=
  Multiset.replicate_add first extra ()

private theorem leftPart_add {R T : Type*} (first second : Multiset (R ⊕ T)) :
    leftPart (first + second) = leftPart first + leftPart second :=
  Multiset.filterMap_add _ _ _

omit [DecidableEq X] [DecidableEq Providers] [DecidableEq Clients] in
theorem initial_extra_purse (request : Request Questions X Providers Clients)
    (budget extra : Nat) :
    AssayProbeDelivery.initial request.session request.provider request.client request.arrival
      (budget + extra) =
    AssayProbeDelivery.initial request.session request.provider request.client request.arrival
      budget + marking 0 (purse extra) := by
  cases request.arrival <;>
    simp only [AssayProbeDelivery.initial, AssayProbeDelivery.paidOffered, purse_add,
      marking_add, add_zero]

namespace Round

variable {protocol : Protocol Questions X} {request : Request Questions X Providers Clients}
variable {budget : Nat}

/-- Extra currency accompanies the supplied path without changing its firings. -/
def replay (round : Round protocol request budget) (extra : Nat) :
    Round protocol request (budget + extra) where
  endpoint := round.endpoint + marking 0 (purse extra)
  path := (AssayProbeDelivery.paid (protocol.test request.question)
      (protocol.deliveryCost request.question) (protocol.inspectionCost request.question)).castPath
    (initial_extra_purse request budget extra).symm rfl
    ((AssayProbeDelivery.paid (protocol.test request.question)
      (protocol.deliveryCost request.question) (protocol.inspectionCost request.question)).replayFrame
      round.path (marking 0 (purse extra)))

theorem replay_endpoint (round : Round protocol request budget) (extra : Nat) :
    (round.replay extra).endpoint = round.endpoint + marking 0 (purse extra) := rfl

theorem replay_resources (round : Round protocol request budget) (extra : Nat) :
    leftPart (round.replay extra).endpoint = leftPart round.endpoint := by
  rw [replay_endpoint, leftPart_add, leftPart_marking, add_zero]

theorem replay_responses (round : Round protocol request budget) (extra : Nat) :
    (round.replay extra).responses = round.responses := by
  rw [responses, responses, replay_resources]

theorem replay_remaining (round : Round protocol request budget) (extra : Nat) :
    (round.replay extra).remaining = round.remaining + extra := by
  rw [remaining, remaining, replay_endpoint, rightPart_add, rightPart_marking,
    Multiset.card_add, purse, Multiset.card_replicate]

theorem replay_spent (round : Round protocol request budget) (extra : Nat) :
    (round.replay extra).spent = round.spent := by
  have first := round.ledger
  have second := (round.replay extra).ledger
  rw [replay_remaining] at second
  omega

/-- The ordered provider and inspection instances are retained exactly. -/
theorem replay_pathEntries (round : Round protocol request budget) (extra : Nat) :
    (AssayProbeDelivery.paid (protocol.test request.question)
      (protocol.deliveryCost request.question) (protocol.inspectionCost request.question)).pathEntries
        (round.replay extra).path =
    (AssayProbeDelivery.paid (protocol.test request.question)
      (protocol.deliveryCost request.question) (protocol.inspectionCost request.question)).pathEntries
        round.path := by
  unfold replay
  rw [System.castPath_pathEntries, System.replayFrame_pathEntries]

/-- Reindexing funding retains the actual round and its path. -/
def castBudget {budget' : Nat} (same : budget = budget')
    (round : Round protocol request budget) : Round protocol request budget' :=
  same ▸ round

theorem castBudget_heq {budget' : Nat} (same : budget = budget')
    (round : Round protocol request budget) : HEq (round.castBudget same) round := by
  cases same
  rfl

theorem castBudget_pathEntries {budget' : Nat} (same : budget = budget')
    (round : Round protocol request budget) :
    (AssayProbeDelivery.paid (protocol.test request.question)
      (protocol.deliveryCost request.question) (protocol.inspectionCost request.question)).pathEntries
        (round.castBudget same).path =
    (AssayProbeDelivery.paid (protocol.test request.question)
      (protocol.deliveryCost request.question) (protocol.inspectionCost request.question)).pathEntries
        round.path := by
  cases same
  rfl

theorem eq_of_pathEntries_eq (first second : Round protocol request budget)
    (same : (AssayProbeDelivery.paid (protocol.test request.question)
      (protocol.deliveryCost request.question) (protocol.inspectionCost request.question)).pathEntries
        first.path =
    (AssayProbeDelivery.paid (protocol.test request.question)
      (protocol.deliveryCost request.question) (protocol.inspectionCost request.question)).pathEntries
        second.path) : first = second := by
  have endpoints := (AssayProbeDelivery.paid (protocol.test request.question)
    (protocol.deliveryCost request.question) (protocol.inspectionCost request.question)).target_eq_of_pathEntries_eq
      first.path second.path same
  have paths := (AssayProbeDelivery.paid (protocol.test request.question)
    (protocol.deliveryCost request.question) (protocol.inspectionCost request.question)).path_heq_of_pathEntries_eq
      first.path second.path same
  cases first
  cases second
  dsimp only at endpoints paths
  cases endpoints
  have pathsEq := eq_of_heq paths
  cases pathsEq
  rfl

theorem replay_zero (round : Round protocol request budget) : HEq (round.replay 0) round := by
  have same : (round.replay 0).castBudget (Nat.add_zero budget) = round :=
    eq_of_pathEntries_eq _ _ (by rw [castBudget_pathEntries, replay_pathEntries])
  exact (castBudget_heq (Nat.add_zero budget) (round.replay 0)).symm.trans (heq_of_eq same)

theorem replay_add (round : Round protocol request budget) (first second : Nat) :
    HEq ((round.replay first).replay second) (round.replay (first + second)) := by
  have same : ((round.replay first).replay second).castBudget (Nat.add_assoc budget first second) =
      round.replay (first + second) :=
    eq_of_pathEntries_eq _ _ (by rw [castBudget_pathEntries, replay_pathEntries,
      replay_pathEntries, replay_pathEntries])
  exact (castBudget_heq (Nat.add_assoc budget first second)
    ((round.replay first).replay second)).symm.trans (heq_of_eq same)

end Round

namespace Campaign

variable {protocol : Protocol Questions X}

/-- Query-indexed words retain every selected delivery and inspection
instance, including provider, client, session and the supplied value. -/
def firingWords : {budget : Nat} → {requests : List (Request Questions X Providers Clients)} →
    Campaign protocol budget requests →
      List (Σ question : Questions, List
        (AssayProbeDelivery.paid (Providers := Providers) (Clients := Clients)
          (protocol.test question) (protocol.deliveryCost question)
          (protocol.inspectionCost question)).Entry)
  | _, _, .nil _ => []
  | _, request :: _, .cons first rest =>
      ⟨request.question, (AssayProbeDelivery.paid (protocol.test request.question)
        (protocol.deliveryCost request.question) (protocol.inspectionCost request.question)).pathEntries
          first.path⟩ :: firingWords rest

/-- Funding indices may be changed by an equality without changing a run. -/
def castBudget {budget budget' : Nat} {requests : List (Request Questions X Providers Clients)}
    (same : budget = budget') (campaign : Campaign protocol budget requests) :
    Campaign protocol budget' requests := same ▸ campaign

theorem castBudget_remaining {budget budget' : Nat}
    {requests : List (Request Questions X Providers Clients)} (same : budget = budget')
    (campaign : Campaign protocol budget requests) :
    (campaign.castBudget same).remaining = campaign.remaining := by
  cases same
  rfl

theorem castBudget_spent {budget budget' : Nat}
    {requests : List (Request Questions X Providers Clients)} (same : budget = budget')
    (campaign : Campaign protocol budget requests) :
    (campaign.castBudget same).spent = campaign.spent := by
  cases same
  rfl

theorem castBudget_publicLog {budget budget' : Nat}
    {requests : List (Request Questions X Providers Clients)} (same : budget = budget')
    (campaign : Campaign protocol budget requests) :
    (campaign.castBudget same).publicLog = campaign.publicLog := by
  cases same
  rfl

theorem castBudget_firingWords {budget budget' : Nat}
    {requests : List (Request Questions X Providers Clients)} (same : budget = budget')
    (campaign : Campaign protocol budget requests) :
    (campaign.castBudget same).firingWords = campaign.firingWords := by
  cases same
  rfl

theorem castBudget_heq {budget budget' : Nat}
    {requests : List (Request Questions X Providers Clients)} (same : budget = budget')
    (campaign : Campaign protocol budget requests) : HEq (campaign.castBudget same) campaign := by
  cases same
  rfl

/-- Replay threads extra currency through the retained rounds in order. -/
def replay : {budget : Nat} → {requests : List (Request Questions X Providers Clients)} →
    (campaign : Campaign protocol budget requests) → (extra : Nat) →
    Campaign protocol (budget + extra) requests
  | _, _, .nil budget, extra => .nil (budget + extra)
  | _, _, .cons first rest, extra =>
      .cons (first.replay extra)
        (castBudget (first.replay_remaining extra).symm (replay rest extra))

theorem replay_remaining {budget : Nat} {requests : List (Request Questions X Providers Clients)}
    (campaign : Campaign protocol budget requests) (extra : Nat) :
    (campaign.replay extra).remaining = campaign.remaining + extra := by
  induction campaign with
  | nil _ => rfl
  | cons first rest inductionHypothesis =>
      simp only [replay, remaining, castBudget_remaining, inductionHypothesis]

theorem replay_spent {budget : Nat} {requests : List (Request Questions X Providers Clients)}
    (campaign : Campaign protocol budget requests) (extra : Nat) :
    (campaign.replay extra).spent = campaign.spent := by
  induction campaign with
  | nil _ => rfl
  | cons first rest inductionHypothesis =>
      simp only [replay, spent, castBudget_spent, Round.replay_spent, inductionHypothesis]

theorem replay_publicLog {budget : Nat} {requests : List (Request Questions X Providers Clients)}
    (campaign : Campaign protocol budget requests) (extra : Nat) :
    (campaign.replay extra).publicLog = campaign.publicLog := by
  induction campaign with
  | nil _ => rfl
  | cons first rest inductionHypothesis =>
      simp only [replay, publicLog, castBudget_publicLog, Round.replay_responses, inductionHypothesis]

theorem replay_firingWords {budget : Nat}
    {requests : List (Request Questions X Providers Clients)}
    (campaign : Campaign protocol budget requests) (extra : Nat) :
    (campaign.replay extra).firingWords = campaign.firingWords := by
  induction campaign with
  | nil _ => rfl
  | cons first rest inductionHypothesis =>
      simp only [replay, firingWords, castBudget_firingWords, Round.replay_pathEntries,
        inductionHypothesis]

/-- Fixed requests, initial funding and all selected firing words determine
the campaign, including its intermediate round paths and balances. -/
theorem eq_of_firingWords_eq {budget : Nat}
    {requests : List (Request Questions X Providers Clients)}
    (first : Campaign protocol budget requests) :
    ∀ second : Campaign protocol budget requests,
      first.firingWords = second.firingWords → first = second := by
  induction first with
  | nil budget =>
      intro second _
      cases second
      rfl
  | @cons budget request requests first rest inductionHypothesis =>
      intro second same
      cases second with
      | cons first' rest' =>
          change Sigma.mk request.question _ :: rest.firingWords =
            Sigma.mk request.question _ :: rest'.firingWords at same
          obtain ⟨heads, tails⟩ := List.cons.inj same
          have firsts : first = first' := Round.eq_of_pathEntries_eq _ _
            (eq_of_heq (Sigma.mk.inj heads).2)
          subst first'
          have rests := inductionHypothesis rest' tails
          subst rest'
          rfl

theorem replay_zero {budget : Nat} {requests : List (Request Questions X Providers Clients)}
    (campaign : Campaign protocol budget requests) : HEq (campaign.replay 0) campaign := by
  have same : (campaign.replay 0).castBudget (Nat.add_zero budget) = campaign :=
    eq_of_firingWords_eq _ _ (by rw [castBudget_firingWords, replay_firingWords])
  exact (castBudget_heq (Nat.add_zero budget) (campaign.replay 0)).symm.trans (heq_of_eq same)

theorem replay_add {budget : Nat} {requests : List (Request Questions X Providers Clients)}
    (campaign : Campaign protocol budget requests) (first second : Nat) :
    HEq ((campaign.replay first).replay second) (campaign.replay (first + second)) := by
  have same : ((campaign.replay first).replay second).castBudget
      (Nat.add_assoc budget first second) = campaign.replay (first + second) :=
    eq_of_firingWords_eq _ _ (by rw [castBudget_firingWords, replay_firingWords,
      replay_firingWords, replay_firingWords])
  exact (castBudget_heq (Nat.add_assoc budget first second)
    ((campaign.replay first).replay second)).symm.trans (heq_of_eq same)

end Campaign

namespace ReplayControls

open ComplementaryAssay (Verdict)

def protocol : Protocol Nat Nat where
  test := fun question value => value == question
  deliveryCost := fun _ _ => 3
  inspectionCost := fun _ _ => 4

def firstRequest : Request Nat Nat Nat Nat where
  question := 7
  session := 0
  provider := 11
  client := 22
  arrival := some 7

def secondRequest : Request Nat Nat Nat Nat where
  question := 8
  session := 1
  provider := 12
  client := 22
  arrival := some 8

def complete : Round protocol firstRequest 7 := completedRound protocol firstRequest 7

def stopped : Round protocol firstRequest 6 := completedRound protocol firstRequest 6

theorem complete_public_response :
    complete.responses = {(0, Verdict.confirm, 22, 7)} := by
  rw [complete, completedRound_responses]
  change AssayProbeDelivery.observed (fun value : Nat => value == 7)
    (fun _ => 3) (fun _ => 4) 0 (11 : Nat) (22 : Nat) (some 7) 7 = _
  rw [AssayProbeDelivery.observed_some]
  rfl

theorem complete_extra_funding :
    (complete.replay 5).responses = {(0, Verdict.confirm, 22, 7)} ∧
      (complete.replay 5).spent = 7 ∧ (complete.replay 5).remaining = 5 ∧
      ((AssayProbeDelivery.paid (protocol.test firstRequest.question)
        (protocol.deliveryCost firstRequest.question)
        (protocol.inspectionCost firstRequest.question)).pathEntries
          (complete.replay 5).path).length = 2 := by
  refine ⟨(complete.replay_responses 5).trans complete_public_response, ?_, ?_, ?_⟩
  · rw [Round.replay_spent]
    have sound := complete.response_sound (0, Verdict.confirm, 22, 7)
      (by rw [complete_public_response]; exact Multiset.mem_singleton_self _)
    obtain ⟨value, arrived, _, _, _, spent⟩ := sound
    have valueEq : value = 7 := by
      simpa only [firstRequest, Option.some.injEq] using arrived.symm
    subst value
    exact spent
  · rw [Round.replay_remaining]
    rfl
  · rw [Round.replay_pathEntries]
    rfl

/-- More funding preserves this stopped prefix; it does not insert an
inspection the supplied execution did not perform. -/
theorem extra_funding_does_not_force_completion :
    (stopped.replay 1).responses = 0 ∧ (stopped.replay 1).remaining = 4 ∧
      ((AssayProbeDelivery.paid (protocol.test firstRequest.question)
        (protocol.deliveryCost firstRequest.question)
        (protocol.inspectionCost firstRequest.question)).pathEntries
          (stopped.replay 1).path).length = 1 ∧
      (completedRound protocol firstRequest 7).responses ≠ 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [Round.replay_responses]
    rfl
  · rw [Round.replay_remaining]
    rfl
  · rw [Round.replay_pathEntries]
    rfl
  · change complete.responses ≠ 0
    rw [complete_public_response]
    exact Multiset.singleton_ne_zero _

def twoRequests : Campaign protocol 7 [firstRequest, secondRequest] :=
  executeCampaign protocol [firstRequest, secondRequest] 7

/-- Each test costs seven, but the actual seven-token campaign completes
only its first test. Funding its retained history leaves the second quiet. -/
theorem replay_retains_campaign_log :
    (twoRequests.replay 7).publicLog =
      [(7, {(0, Verdict.confirm, 22, 7)}), (8, 0)] ∧
      (twoRequests.replay 7).spent = 7 ∧ (twoRequests.replay 7).remaining = 7 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [Campaign.replay_publicLog]
    rfl
  · rw [Campaign.replay_spent]
    rfl
  · rw [Campaign.replay_remaining]
    rfl

theorem individually_affordable_is_not_a_joint_campaign :
    (completedRound protocol firstRequest 7).responses ≠ 0 ∧
      (completedRound protocol secondRequest 7).responses ≠ 0 ∧
      twoRequests.completedTests = 1 ∧
      (executeCampaign protocol [firstRequest, secondRequest] 14).completedTests = 2 := by
  refine ⟨?_, ?_, rfl, rfl⟩
  · change complete.responses ≠ 0
    rw [complete_public_response]
    exact Multiset.singleton_ne_zero _
  · rw [completedRound_responses]
    change AssayProbeDelivery.observed (fun value : Nat => value == 8)
      (fun _ => 3) (fun _ => 4) 1 (12 : Nat) (22 : Nat) (some 8) 7 ≠ 0
    rw [AssayProbeDelivery.observed_some]
    exact Multiset.singleton_ne_zero _

end ReplayControls

end Mettapedia.GSLT.Causality.ProbeCampaign
