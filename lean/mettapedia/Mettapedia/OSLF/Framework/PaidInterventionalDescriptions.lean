import Mettapedia.GSLT.Causality.PaidProbeReplay
import Mettapedia.OSLF.Framework.FiniteAssayLearner
import Mettapedia.CategoryTheory.PartialSections

/-!
# Completed paid responses as partial descriptions

The domain of a description consists of actual response occurrences in a
sequential campaign. Repeated questions retain separate positions. A
missing response supplies no Boolean answer and no negative evidence.
Full paths, their budgets, sessions and providers remain in a separate
receipt type; a partial answer is only its public readout.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Framework.PaidInterventionalDescriptions

open Mettapedia.GSLT.Causality
open Mettapedia.GSLT.Causality.ProbeCampaign
open Mettapedia.CategoryTheory.PartialSections

universe q u v w f

variable {Questions : Type q} {X : Type u} {Providers : Type v} {Clients : Type w}

/-- Read only a packet present at the actual endpoint. -/
noncomputable def packetAnswer (responses : Multiset (Response X Clients)) : Option Bool := by
  classical
  exact if present : ∃ response, response ∈ responses then
    some (Classical.choose present).2.1.bit
  else none

theorem packetAnswer_none (responses : Multiset (Response X Clients)) :
    packetAnswer responses = none ↔ responses = 0 := by
  classical
  unfold packetAnswer
  split_ifs with present
  · simp only [false_iff]
    intro empty
    obtain ⟨response, member⟩ := present
    simp [empty] at member
  · simp only [true_iff]
    apply Multiset.eq_zero_iff_forall_notMem.mpr
    exact fun response member => present ⟨response, member⟩

theorem packetAnswer_some (responses : Multiset (Response X Clients))
    (consistent : ∀ first ∈ responses, ∀ second ∈ responses,
      first.2.1.bit = second.2.1.bit) (answer : Bool) :
    packetAnswer responses = some answer ↔
      ∃ response ∈ responses, response.2.1.bit = answer := by
  classical
  unfold packetAnswer
  split_ifs with present
  · constructor
    · intro same
      exact ⟨Classical.choose present, Classical.choose_spec present,
        Option.some.inj same⟩
    · rintro ⟨response, member, readout⟩
      exact congrArg some ((consistent _ (Classical.choose_spec present) _ member).trans readout)
  · constructor
    · intro impossible
      cases impossible
    · rintro ⟨response, member, _⟩
      exact False.elim (present ⟨response, member⟩)

/-- A view exposes precisely the defined entries of an optional readout. -/
noncomputable def viewOfAnswers {Feature : Type f} (answers : Feature → Option Bool) :
    View Feature Bool where
  context := {feature | ∃ answer, answers feature = some answer}
  values feature := Classical.choose feature.property

theorem viewOfAnswers_value {Feature : Type f} (answers : Feature → Option Bool)
    (feature : Feature) (present : feature ∈ (viewOfAnswers answers).context) :
    answers feature = some ((viewOfAnswers answers).values ⟨feature, present⟩) :=
  Classical.choose_spec present

theorem viewOfAnswers_readout {Feature : Type f} (answers : Feature → Option Bool)
    (feature : Feature) (answer : Bool) (same : answers feature = some answer) :
    (viewOfAnswers answers).values ⟨feature, ⟨answer, same⟩⟩ = answer := by
  exact Option.some.inj ((viewOfAnswers_value answers feature ⟨answer, same⟩).symm.trans same)

theorem viewOfAnswers_extends {Feature : Type f} (first second : Feature → Option Bool)
    (preserves : ∀ feature answer, first feature = some answer → second feature = some answer) :
    viewOfAnswers first ≤ viewOfAnswers second := by
  refine ⟨?_, ?_⟩
  · rintro feature ⟨answer, present⟩
    exact ⟨answer, preserves feature answer present⟩
  · intro feature inFirst inSecond
    apply Option.some.inj
    exact (preserves feature _ (viewOfAnswers_value first feature inFirst)).symm.trans
      (viewOfAnswers_value second feature inSecond)

theorem viewOfAnswers_reindex {Feature Other : Type f} (select : Other → Feature)
    (answers : Feature → Option Bool) :
    viewOfAnswers (answers ∘ select) = reindexFeatures select (viewOfAnswers answers) := by
  apply View.ext
  · rfl
  · intro feature first second
    apply Option.some.inj
    exact (viewOfAnswers_value (answers ∘ select) feature first).symm.trans
      (viewOfAnswers_value answers (select feature) second)

namespace Round

variable [DecidableEq X] [DecidableEq Providers] [DecidableEq Clients]
variable {protocol : Protocol Questions X} {request : Request Questions X Providers Clients}
variable {budget : Nat}

theorem consistent (round : ProbeCampaign.Round protocol request budget) :
    ∀ first ∈ round.responses, ∀ second ∈ round.responses,
      first.2.1.bit = second.2.1.bit := by
  intro first firstMember second secondMember
  obtain ⟨_, _, _, singleton, _, _⟩ := round.response_sound first firstMember
  have same : second = first := by simpa [singleton] using secondMember
  rw [same]

noncomputable def answer (round : ProbeCampaign.Round protocol request budget) : Option Bool :=
  packetAnswer round.responses

theorem answer_some (round : ProbeCampaign.Round protocol request budget) (value : Bool) :
    answer round = some value ↔
      ∃ response ∈ round.responses, response.2.1.bit = value :=
  packetAnswer_some round.responses (consistent round) value

theorem answer_none (round : ProbeCampaign.Round protocol request budget) :
    answer round = none ↔ round.responses = 0 := packetAnswer_none _

/-- Independent observation semantics is supplied by a calibrated offered
value, and compared with an actual authenticated response. -/
theorem answer_agrees (round : ProbeCampaign.Round protocol request budget)
    (observation : Bool)
    (calibrated : ∀ value, request.arrival = some value →
      protocol.test request.question value = observation)
    (answer : Bool) (answered : Round.answer round = some answer) : answer = observation := by
  obtain ⟨response, member, readout⟩ := (answer_some round answer).mp answered
  obtain ⟨value, offered, packet, _, _, _⟩ := round.response_sound response member
  subst response
  have tested : protocol.test request.question value = answer := by simpa using readout
  exact tested.symm.trans (calibrated value offered)

theorem answer_replay (round : ProbeCampaign.Round protocol request budget) (extra : Nat) :
    answer (round.replay extra) = answer round := by
  unfold answer
  rw [ProbeCampaign.Round.replay_responses]

theorem compatible_iff_answer {Hypotheses : Type*}
    (prediction : Hypotheses → Questions → Bool) (hypothesis : Hypotheses)
    (round : ProbeCampaign.Round protocol request budget) :
    FiniteAssayLearner.Compatible prediction hypothesis request.question round.responses ↔
      ∀ bit, Round.answer round = some bit → prediction hypothesis request.question = bit := by
  constructor
  · intro compatible bit answered
    obtain ⟨response, present, same⟩ := (answer_some round bit).mp answered
    exact (compatible response present).trans same
  · intro compatible response present
    exact compatible response.2.1.bit
      ((answer_some round response.2.1.bit).mpr ⟨response, present, rfl⟩)

end Round

variable [DecidableEq X] [DecidableEq Providers] [DecidableEq Clients]

/-- A complete receipt retains the actual round and the particular packet
whose bit it exposes. The request index retains question, provider, client,
session and offered endpoint; the round retains path, expenditure and purse. -/
structure CompletedReceipt (protocol : Protocol Questions X)
    (request : Request Questions X Providers Clients) (budget : Nat) (answer : Bool) where
  round : ProbeCampaign.Round protocol request budget
  response : Response X Clients
  authenticated : response ∈ round.responses
  readout : response.2.1.bit = answer

namespace CompletedReceipt

variable {protocol : Protocol Questions X} {request : Request Questions X Providers Clients}
variable {budget : Nat} {answer : Bool}

theorem actual_answer (receipt : CompletedReceipt protocol request budget answer) :
    Round.answer receipt.round = some answer :=
  (Round.answer_some _ _).mpr ⟨receipt.response, receipt.authenticated, receipt.readout⟩

def replay (receipt : CompletedReceipt protocol request budget answer) (extra : Nat) :
    CompletedReceipt protocol request (budget + extra) answer where
  round := receipt.round.replay extra
  response := receipt.response
  authenticated := by rw [ProbeCampaign.Round.replay_responses]; exact receipt.authenticated
  readout := receipt.readout

theorem replay_balance (receipt : CompletedReceipt protocol request budget answer) (extra : Nat) :
    (receipt.replay extra).round.remaining = receipt.round.remaining + extra :=
  ProbeCampaign.Round.replay_remaining _ _

end CompletedReceipt

namespace Campaign

variable {protocol : Protocol Questions X}

noncomputable def answerAt : {budget : Nat} →
    {requests : List (Request Questions X Providers Clients)} →
    ProbeCampaign.Campaign protocol budget requests → Nat → Option Bool
  | _, _, .nil _, _ => none
  | _, _, .cons first _, 0 => Round.answer first
  | _, _, .cons _ rest, index + 1 => answerAt rest index

noncomputable def describe {budget : Nat}
    {requests : List (Request Questions X Providers Clients)}
    (campaign : ProbeCampaign.Campaign protocol budget requests) : View Nat Bool :=
  viewOfAnswers (answerAt campaign)

theorem answerAt_publicLog {budget : Nat}
    {requests : List (Request Questions X Providers Clients)}
    (campaign : ProbeCampaign.Campaign protocol budget requests) (index : Nat) :
    answerAt campaign index = (campaign.publicLog[index]?).bind
      (fun packet => packetAnswer packet.2) := by
  induction campaign generalizing index with
  | nil _ => simp [answerAt, ProbeCampaign.Campaign.publicLog]
  | cons first rest inductionHypothesis =>
      cases index with
      | zero => rfl
      | succ index => exact inductionHypothesis index

theorem answerAt_replay {budget : Nat}
    {requests : List (Request Questions X Providers Clients)}
    (campaign : ProbeCampaign.Campaign protocol budget requests) (extra index : Nat) :
    answerAt (campaign.replay extra) index = answerAt campaign index := by
  rw [answerAt_publicLog, ProbeCampaign.Campaign.replay_publicLog, ← answerAt_publicLog]

theorem describe_replay {budget : Nat}
    {requests : List (Request Questions X Providers Clients)}
    (campaign : ProbeCampaign.Campaign protocol budget requests) (extra : Nat) :
    describe (campaign.replay extra) = describe campaign := by
  apply congrArg viewOfAnswers
  funext index
  exact answerAt_replay campaign extra index

theorem answerAt_bounded {budget : Nat}
    {requests : List (Request Questions X Providers Clients)}
    (campaign : ProbeCampaign.Campaign protocol budget requests) (index : Nat)
    (answer : Bool) (answered : answerAt campaign index = some answer) : index < requests.length := by
  induction campaign generalizing index with
  | nil _ => cases answered
  | cons first rest inductionHypothesis =>
      cases index with
      | zero => simp
      | succ index => exact Nat.succ_lt_succ (inductionHypothesis index answered)

/-- The receipt fibre is tied to an actual campaign position. -/
def Receipts : {budget : Nat} → {requests : List (Request Questions X Providers Clients)} →
    ProbeCampaign.Campaign protocol budget requests → Nat → Bool → Type (max u w)
  | _, _, .nil _, _, _ => PEmpty
  | _, _, .cons first _, 0, answer =>
      {response : Response X Clients // response ∈ first.responses ∧ response.2.1.bit = answer}
  | _, _, .cons _ rest, index + 1, answer => Receipts rest index answer

theorem receipt_iff_answer {budget : Nat}
    {requests : List (Request Questions X Providers Clients)}
    (campaign : ProbeCampaign.Campaign protocol budget requests) (index : Nat) (answer : Bool) :
    Nonempty (Receipts campaign index answer) ↔ answerAt campaign index = some answer := by
  induction campaign generalizing index with
  | nil _ => simp [Receipts, answerAt]
  | cons first rest inductionHypothesis =>
      cases index with
      | zero =>
          simpa [Receipts, answerAt, nonempty_subtype] using (Round.answer_some first answer).symm
      | succ index => exact inductionHypothesis index

/-- Decode the complete actual round stored at this occurrence. The
response subtype never substitutes an invented path for its origin. -/
def completeReceipt : {budget : Nat} →
    {requests : List (Request Questions X Providers Clients)} →
    (campaign : ProbeCampaign.Campaign protocol budget requests) →
    (index : Nat) → (answer : Bool) → Receipts campaign index answer →
      Σ request : Request Questions X Providers Clients,
        Σ paidBudget : Nat, CompletedReceipt protocol request paidBudget answer
  | _, _, .nil _, _, _, impossible => PEmpty.elim impossible
  | budget, request :: _, .cons first _, 0, _, response =>
      ⟨request, budget, ⟨first, response.val, response.property.1, response.property.2⟩⟩
  | _, _, .cons _ rest, index + 1, answer, receipt => completeReceipt rest index answer receipt

theorem completeReceipt_readout {budget : Nat}
    {requests : List (Request Questions X Providers Clients)}
    (campaign : ProbeCampaign.Campaign protocol budget requests) (index : Nat) (answer : Bool)
    (receipt : Receipts campaign index answer) :
    Round.answer (completeReceipt campaign index answer receipt).2.2.round = some answer :=
  (completeReceipt campaign index answer receipt).2.2.actual_answer

/-- Append a compatible campaign using the remaining purse, rather than
funding each appended request independently. -/
def append : {budget : Nat} → {requests : List (Request Questions X Providers Clients)} →
    (first : ProbeCampaign.Campaign protocol budget requests) →
    {later : List (Request Questions X Providers Clients)} →
    ProbeCampaign.Campaign protocol first.remaining later →
      ProbeCampaign.Campaign protocol budget (requests ++ later)
  | _, _, .nil _, _, continuation => continuation
  | _, _, .cons round rest, _, continuation => .cons round (append rest continuation)

theorem append_answerAt {budget : Nat}
    {requests later : List (Request Questions X Providers Clients)}
    (first : ProbeCampaign.Campaign protocol budget requests)
    (continuation : ProbeCampaign.Campaign protocol first.remaining later)
    (index : Nat) (earlier : index < requests.length) :
    answerAt (append first continuation) index = answerAt first index := by
  induction first generalizing index with
  | nil _ => simp at earlier
  | cons round rest inductionHypothesis =>
      cases index with
      | zero => rfl
      | succ index =>
          exact inductionHypothesis continuation index (Nat.lt_of_succ_lt_succ earlier)

theorem append_preserves_description {budget : Nat}
    {requests later : List (Request Questions X Providers Clients)}
    (first : ProbeCampaign.Campaign protocol budget requests)
    (continuation : ProbeCampaign.Campaign protocol first.remaining later) :
    describe first ≤ describe (append first continuation) := by
  apply viewOfAnswers_extends
  intro index answer answered
  rw [append_answerAt first continuation index (answerAt_bounded first index answer answered)]
  exact answered

/-- Revision reads precisely the defined Boolean values in the actual
campaign, and never treats absence as refutation. -/
def ReadoutCompatible {Hypotheses : Type*}
    (prediction : Hypotheses → Questions → Bool) (hypothesis : Hypotheses) :
    {budget : Nat} → {requests : List (Request Questions X Providers Clients)} →
    ProbeCampaign.Campaign protocol budget requests → Prop
  | _, _, .nil _ => True
  | _, request :: _, .cons first rest =>
      (∀ bit, Round.answer first = some bit → prediction hypothesis request.question = bit) ∧
        ReadoutCompatible prediction hypothesis rest

theorem learn_readout {Hypotheses : Type*}
    (prediction : Hypotheses → Questions → Bool) {budget : Nat}
    {requests : List (Request Questions X Providers Clients)}
    (campaign : ProbeCampaign.Campaign protocol budget requests)
    (candidates : Finset Hypotheses) (hypothesis : Hypotheses) :
    hypothesis ∈ FiniteAssayLearner.learn prediction campaign candidates ↔
      hypothesis ∈ candidates ∧ ReadoutCompatible prediction hypothesis campaign := by
  induction campaign generalizing candidates with
  | nil _ => simp [FiniteAssayLearner.learn, ReadoutCompatible]
  | cons first rest inductionHypothesis =>
      rw [FiniteAssayLearner.learn, inductionHypothesis,
        FiniteAssayLearner.revise_mem, Round.compatible_iff_answer]
      exact and_assoc

end Campaign

end Mettapedia.OSLF.Framework.PaidInterventionalDescriptions
