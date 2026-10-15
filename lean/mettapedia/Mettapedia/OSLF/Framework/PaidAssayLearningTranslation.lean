import Mettapedia.GSLT.Causality.PaidProbeTranslationCoherence
import Mettapedia.OSLF.Framework.PaidInterventionalDescriptions

/-!
# Paid answer, description and learner transport

The operational translation maps the actual paid path and its endpoint.
Its independently read responses then determine the same optional Boolean
answer and the same description at every retained campaign position.
Complete authenticated receipts transport separately from those readouts.

A compatible translation of predictions earns the version-space comparison.
The comparison concerns corresponding campaigns; it does not assert that
an arbitrary target schedule is a translated source schedule.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Framework.PaidAssayLearningTranslation

open Mettapedia.GSLT.Causality
open Mettapedia.GSLT.Causality.ProbeCampaign
open Mettapedia.CategoryTheory.PartialSections

namespace Descriptions

open PaidInterventionalDescriptions

universe q u v w

variable {Questions Questions' : Type q} {X X' : Type u}
  {Providers Providers' : Type v} {Clients Clients' : Type w}
  {source : Protocol Questions X} {target : Protocol Questions' X'}
  [DecidableEq X] [DecidableEq Providers] [DecidableEq Clients]
  [DecidableEq X'] [DecidableEq Providers'] [DecidableEq Clients']

variable (translation : Translation (Providers := Providers) (Providers' := Providers')
  (Clients := Clients) (Clients' := Clients') source target)

theorem round_answer {request : Request Questions X Providers Clients} {budget : Nat}
    (original : ProbeCampaign.Round source request budget) :
    Round.answer (translation.round original) = Round.answer original := by
  cases answered : Round.answer original with
  | none =>
      apply (Round.answer_none _).mpr
      rw [translation.round_responses, (Round.answer_none original).mp answered, Multiset.map_zero]
  | some bit =>
      obtain ⟨packet, present, readout⟩ := (Round.answer_some original bit).mp answered
      apply (Round.answer_some _ bit).mpr
      refine ⟨translation.response packet, ?_, readout⟩
      rw [translation.round_responses]
      exact Multiset.mem_map_of_mem _ present

def receipt {request : Request Questions X Providers Clients} {budget : Nat} {bit : Bool}
    (original : CompletedReceipt source request budget bit) :
    CompletedReceipt target (translation.request request) budget bit where
  round := translation.round original.round
  response := translation.response original.response
  authenticated := by
    rw [translation.round_responses]
    exact Multiset.mem_map_of_mem _ original.authenticated
  readout := original.readout

theorem receipt_answer {request : Request Questions X Providers Clients} {budget : Nat} {bit : Bool}
    (original : CompletedReceipt source request budget bit) :
    Round.answer (receipt translation original).round = some bit :=
  (receipt translation original).actual_answer

theorem receipt_balance {request : Request Questions X Providers Clients} {budget : Nat} {bit : Bool}
    (original : CompletedReceipt source request budget bit) :
    (receipt translation original).round.remaining = original.round.remaining ∧
      (receipt translation original).round.spent = original.round.spent :=
  ⟨translation.round_remaining original.round, translation.round_spent original.round⟩

theorem answerAt_reindexBudget {before after : Nat} (same : before = after)
    {protocol : Protocol Questions X} {requests : List (Request Questions X Providers Clients)}
    (original : ProbeCampaign.Campaign protocol before requests) (index : Nat) :
    Campaign.answerAt (original.reindexBudget same) index = Campaign.answerAt original index := by
  cases same
  rfl

theorem campaign_answerAt : ∀ {budget : Nat}
    {requests : List (Request Questions X Providers Clients)}
    (original : ProbeCampaign.Campaign source budget requests) (index : Nat),
    Campaign.answerAt (translation.campaign original) index = Campaign.answerAt original index
  | _, _, .nil _, _ => rfl
  | _, _, .cons first rest, 0 => round_answer translation first
  | _, _, .cons first rest, index + 1 => by
      change Campaign.answerAt ((translation.campaign rest).reindexBudget _) index = _
      rw [answerAt_reindexBudget, campaign_answerAt rest index]
      rfl

/-- Campaign positions are the feature vocabulary. Repeated authored
questions remain different positions even when their public bits agree. -/
theorem campaign_description {budget : Nat}
    {requests : List (Request Questions X Providers Clients)}
    (original : ProbeCampaign.Campaign source budget requests) :
    Campaign.describe (translation.campaign original) = Campaign.describe original := by
  unfold Campaign.describe
  exact congrArg viewOfAnswers (funext (campaign_answerAt translation original))

theorem description_reindex {budget : Nat}
    {requests : List (Request Questions X Providers Clients)}
    (original : ProbeCampaign.Campaign source budget requests) (select : Nat → Nat) :
    viewOfAnswers (Campaign.answerAt (translation.campaign original) ∘ select) =
      reindexFeatures select (Campaign.describe original) := by
  rw [viewOfAnswers_reindex]
  exact congrArg (reindexFeatures select) (campaign_description translation original)

end Descriptions

namespace ReceiptCoherence

open PaidInterventionalDescriptions
open Descriptions

universe q u v w

variable {Questions Questions' Questions'' : Type q} {X X' X'' : Type u}
  {Providers Providers' Providers'' : Type v} {Clients Clients' Clients'' : Type w}
  [DecidableEq X] [DecidableEq Providers] [DecidableEq Clients]

def reindexRequest {protocol : Protocol Questions X}
    {request request' : Request Questions X Providers Clients} (same : request = request')
    {budget : Nat} {bit : Bool} (original : CompletedReceipt protocol request budget bit) :
    CompletedReceipt protocol request' budget bit := same ▸ original

@[simp] theorem reindex_round {protocol : Protocol Questions X}
    {request request' : Request Questions X Providers Clients} (same : request = request')
    {budget : Nat} {bit : Bool} (original : CompletedReceipt protocol request budget bit) :
    (reindexRequest same original).round = original.round.reindexRequest same := by cases same; rfl

@[simp] theorem reindex_response {protocol : Protocol Questions X}
    {request request' : Request Questions X Providers Clients} (same : request = request')
    {budget : Nat} {bit : Bool} (original : CompletedReceipt protocol request budget bit) :
    (reindexRequest same original).response = original.response := by cases same; rfl

theorem eq_of_round_response {protocol : Protocol Questions X}
    {request : Request Questions X Providers Clients} {budget : Nat} {bit : Bool}
    (first second : CompletedReceipt protocol request budget bit)
    (rounds : first.round = second.round) (responses : first.response = second.response) :
    first = second := by
  cases first
  cases second
  cases rounds
  cases responses
  rfl

theorem receipt_id {protocol : Protocol Questions X}
    {request : Request Questions X Providers Clients} {budget : Nat} {bit : Bool}
    (original : CompletedReceipt protocol request budget bit) :
    reindexRequest (Translation.request_id request) (receipt (Translation.id protocol) original) = original := by
  apply eq_of_round_response
  · exact (reindex_round _ _).trans (Translation.round_id original.round)
  · exact (reindex_response _ _).trans (Translation.response_id original.response)

variable [DecidableEq X'] [DecidableEq Providers'] [DecidableEq Clients']
  [DecidableEq X''] [DecidableEq Providers''] [DecidableEq Clients'']

theorem receipt_comp {source : Protocol Questions X} {middle : Protocol Questions' X'}
    {target : Protocol Questions'' X''}
    (first : Translation (Providers := Providers) (Providers' := Providers')
      (Clients := Clients) (Clients' := Clients') source middle)
    (second : Translation (Providers := Providers') (Providers' := Providers'')
      (Clients := Clients') (Clients' := Clients'') middle target)
    {request : Request Questions X Providers Clients} {budget : Nat} {bit : Bool}
    (original : CompletedReceipt source request budget bit) :
    reindexRequest (first.request_comp second request) (receipt (first.comp second) original) =
      receipt second (receipt first original) := by
  apply eq_of_round_response
  · exact (reindex_round _ _).trans (first.round_comp second original.round)
  · exact (reindex_response _ _).trans (first.response_comp second original.response)

end ReceiptCoherence

namespace Learning

open FiniteAssayLearner

universe h h' q u v w

variable {Hypotheses : Type h} {Hypotheses' : Type h'}
  {Questions Questions' : Type q} {X X' : Type u}
  {Providers Providers' : Type v} {Clients Clients' : Type w}
  {source : Protocol Questions X} {target : Protocol Questions' X'}

variable (translation : Translation (Providers := Providers) (Providers' := Providers')
  (Clients := Clients) (Clients' := Clients') source target)
  (hypotheses : Hypotheses ≃ Hypotheses')
  (sourcePrediction : Hypotheses → Questions → Bool)
  (targetPrediction : Hypotheses' → Questions' → Bool)
  (predicts : ∀ hypothesis query,
    targetPrediction (hypotheses hypothesis) (translation.question query) =
      sourcePrediction hypothesis query)

include predicts

theorem compatible_map (hypothesis : Hypotheses) (query : Questions)
    (responses : Multiset (Response X Clients)) :
    Compatible targetPrediction (hypotheses hypothesis) (translation.question query)
        (responses.map translation.response) ↔
      Compatible sourcePrediction hypothesis query responses := by
  constructor
  · intro compatible packet present
    have answer := compatible (translation.response packet) (Multiset.mem_map_of_mem _ present)
    exact (predicts hypothesis query).symm.trans answer
  · intro compatible packet present
    obtain ⟨original, member, rfl⟩ := Multiset.mem_map.mp present
    exact (predicts hypothesis query).trans (compatible original member)

theorem revise_map (candidates : Finset Hypotheses) (query : Questions)
    (responses : Multiset (Response X Clients)) :
    revise targetPrediction (candidates.map hypotheses.toEmbedding)
        (translation.question query) (responses.map translation.response) =
      (revise sourcePrediction candidates query responses).map hypotheses.toEmbedding := by
  classical
  ext hypothesis
  constructor
  · intro member
    obtain ⟨mappedInitial, agrees⟩ := (revise_mem _ _ _ _ _).mp member
    obtain ⟨original, initial, rfl⟩ := Finset.mem_map.mp mappedInitial
    exact Finset.mem_map.mpr ⟨original,
      (revise_mem _ _ _ _ _).mpr ⟨initial,
        (compatible_map translation hypotheses sourcePrediction targetPrediction predicts _ _ _).mp agrees⟩,
      rfl⟩
  · intro member
    obtain ⟨original, revised, rfl⟩ := Finset.mem_map.mp member
    obtain ⟨initial, agrees⟩ := (revise_mem _ _ _ _ _).mp revised
    exact (revise_mem _ _ _ _ _).mpr ⟨Finset.mem_map.mpr ⟨original, initial, rfl⟩,
      (compatible_map translation hypotheses sourcePrediction targetPrediction predicts _ _ _).mpr agrees⟩

variable [DecidableEq X] [DecidableEq Providers] [DecidableEq Clients]
  [DecidableEq X'] [DecidableEq Providers'] [DecidableEq Clients']

/-- Hypothesis revision commutes on the independently read log of each
actual translated campaign, with its own sequential paid paths retained. -/
theorem learn_map {budget : Nat} {requests : List (Request Questions X Providers Clients)}
    (original : ProbeCampaign.Campaign source budget requests) (candidates : Finset Hypotheses) :
    learn targetPrediction (translation.campaign original) (candidates.map hypotheses.toEmbedding) =
      (learn sourcePrediction original candidates).map hypotheses.toEmbedding := by
  classical
  ext hypothesis
  constructor
  · intro member
    obtain ⟨mappedInitial, agrees⟩ := (learn_mem _ _ _ _).mp member
    obtain ⟨candidate, initial, rfl⟩ := Finset.mem_map.mp mappedInitial
    apply Finset.mem_map.mpr
    refine ⟨candidate, (learn_mem _ _ _ _).mpr ⟨initial, ?_⟩, rfl⟩
    intro packet present
    apply (compatible_map translation hypotheses sourcePrediction targetPrediction predicts _ _ _).mp
    apply agrees (translation.packet packet)
    rw [translation.campaign_publicLog]
    exact List.mem_map_of_mem present
  · intro member
    obtain ⟨candidate, learned, rfl⟩ := Finset.mem_map.mp member
    obtain ⟨initial, agrees⟩ := (learn_mem _ _ _ _).mp learned
    apply (learn_mem _ _ _ _).mpr
    refine ⟨Finset.mem_map.mpr ⟨candidate, initial, rfl⟩, ?_⟩
    intro packet present
    rw [translation.campaign_publicLog] at present
    obtain ⟨originalPacket, member, rfl⟩ := List.mem_map.mp present
    exact (compatible_map translation hypotheses sourcePrediction targetPrediction predicts _ _ _).mpr
      (agrees originalPacket member)

end Learning

namespace ChargeControls

def sourceProtocol : Protocol Unit Bool where
  test := fun _ value => value
  deliveryCost := fun _ _ => 1
  inspectionCost := fun _ _ => 1

def targetProtocol : Protocol Unit Bool where
  test := fun _ value => value
  deliveryCost := fun _ _ => 1
  inspectionCost := fun _ _ => 2

def request : Request Unit Bool Unit Unit := ⟨(), 0, (), (), some true⟩

theorem test_preserved (query : Unit) (value : Bool) :
    targetProtocol.test query value = sourceProtocol.test query value := rfl

/-- The test vocabulary agrees, but the actual target controller cannot
complete a verdict using the source controller's two-token purse. -/
theorem ignoring_charge_changes_completion :
    (completedRound sourceProtocol request 2).responses =
        {(0, ComplementaryAssay.Verdict.confirm, (), true)} ∧
      (completedRound targetProtocol request 2).responses = 0 := by
  constructor <;> rw [completedRound_responses] <;>
    simp [sourceProtocol, targetProtocol, request, AssayProbeDelivery.observed_some,
      ComplementaryAssay.verdictOf]

/-- The target failure is not an unlucky choice of schedule: no supplied
finite target prefix can produce a completed answer with that purse. -/
theorem target_underfunded_is_silent (history : Round targetProtocol request 2) :
    history.responses = 0 := by
  apply Multiset.eq_zero_iff_forall_notMem.mpr
  intro packet member
  obtain ⟨payload, _, _, _, affordable, _⟩ := history.response_sound packet member
  have impossible : ¬ 1 + 2 ≤ (2 : Nat) := by decide
  exact impossible affordable

theorem exact_inspection_law_fails :
    ¬ (∀ query value, targetProtocol.inspectionCost query value =
      sourceProtocol.inspectionCost query value) := by
  intro law
  have wrong : (2 : Nat) = 1 := law () true
  cases wrong

end ChargeControls

end Mettapedia.OSLF.Framework.PaidAssayLearningTranslation
