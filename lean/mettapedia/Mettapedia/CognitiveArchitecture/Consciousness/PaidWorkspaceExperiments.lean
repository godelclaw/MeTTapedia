import Mettapedia.CognitiveArchitecture.Consciousness.PhenomenalRealization
import Mettapedia.GSLT.Causality.ContextualRealization
import Mettapedia.GSLT.Causality.ProbeCampaignCompletion
import Mettapedia.GSLT.Causality.PaidProbeTranslation
import Mettapedia.GSLT.Causality.PaidProbeReplay
import Mettapedia.OSLF.Framework.FiniteAssayLearner

/-!
# Paid component experiments on an existing workspace

The probe executes the existing architectural commands before its actual
endpoint report is offered to the existing paid delivery/inspection protocol.
Each command consumes one token; delivery and inspection consume two and
three respectively. A halted probe supplies no offer, and an incomplete
delivery/inspection supplies no answer. The receipt retains both paths and
their successive purses. The declared handoff supplies the offered endpoint
report; it does not assert an external provider's authority.

Compression uses the independently defined architectural core transition.
All finite intervention words commute, and paid command paths retain their
charges. Compression forgets the event counter, which remains in the concrete
receipt rather than being reconstructed from its public answer.
-/

set_option autoImplicit false

namespace Mettapedia.CognitiveArchitecture.Consciousness.PaidWorkspaceExperiments

open Mettapedia.GSLT
open Mettapedia.GSLT.Causality
open Mettapedia.GSLT.Causality.ProbeCampaign
open Mettapedia.CognitiveArchitecture.Consciousness.ArchitecturalIndicators
open Mettapedia.OSLF.Framework.FiniteAssayLearner

/-! ## One real paid command per transition -/

universe u v

/-- The successor and subtraction are indexed at each actual command.
The command word remains separate from the endpoint. -/
inductive PaidWord {S : Type u} {Commands : Type v} (advance : S → Commands → S) :
    S → Nat → List Commands → S → Nat → Type (max u v) where
  | nil (state : S) (budget : Nat) : PaidWord advance state budget [] state budget
  | cons {state : S} {budget : Nat} {command : Commands} {commands : List Commands}
      {target : S} {remaining : Nat} (affordable : 1 ≤ budget)
      (rest : PaidWord advance (advance state command) (budget - 1) commands target remaining) :
      PaidWord advance state budget (command :: commands) target remaining

namespace PaidWord

variable {S : Type u} {Commands : Type v} {advance : S → Commands → S}

theorem ledger {state target : S} {budget remaining : Nat} {commands : List Commands}
    (path : PaidWord advance state budget commands target remaining) :
    budget = remaining + commands.length := by
  induction path with
  | nil => simp only [List.length_nil, Nat.add_zero]
  | cons affordable rest inductionHypothesis =>
      simp only [List.length_cons]
      omega

theorem endpoint {state target : S} {budget remaining : Nat} {commands : List Commands}
    (path : PaidWord advance state budget commands target remaining) :
    target = commands.foldl advance state := by
  induction path with
  | nil => rfl
  | cons _ _ inductionHypothesis => exact inductionHypothesis

def execute (advance : S → Commands → S) (state : S) :
    (commands : List Commands) → (budget : Nat) → commands.length ≤ budget →
      PaidWord advance state budget commands (commands.foldl advance state)
        (budget - commands.length)
  | [], budget, _ => .nil state budget
  | command :: commands, budget, affordable => by
      have first : 1 ≤ budget := by simp only [List.length_cons] at affordable; omega
      have later : commands.length ≤ budget - 1 := by
        simp only [List.length_cons] at affordable
        omega
      have subtraction : (budget - 1) - commands.length =
          budget - (command :: commands).length := by
        simp only [List.length_cons]
        omega
      rw [← subtraction]
      exact .cons first (execute advance (advance state command) commands (budget - 1) later)

def map {T : Type u} (translate : S → T) (targetAdvance : T → Commands → T)
    (commutes : ∀ state command,
      translate (advance state command) = targetAdvance (translate state) command) :
    {state target : S} → {budget remaining : Nat} → {commands : List Commands} →
      PaidWord advance state budget commands target remaining →
        PaidWord targetAdvance (translate state) budget commands (translate target) remaining
  | _, _, _, _, _, .nil state budget => .nil _ budget
  | state, _, _, _, _, .cons affordable rest => by
      exact .cons affordable (commutes state _ ▸ map translate targetAdvance commutes rest)

/-- Replay every supplied paid command, rather than choosing a new schedule
because an increased purse permits more behavior. -/
def replay (extra : Nat) :
    {state target : S} → {budget remaining : Nat} → {commands : List Commands} →
      PaidWord advance state budget commands target remaining →
        PaidWord advance state (budget + extra) commands target (remaining + extra)
  | _, _, _, _, _, .nil state budget => .nil state (budget + extra)
  | _, _, budget, _, _, .cons affordable rest => by
      have more : 1 ≤ budget + extra := by omega
      have subtraction : (budget - 1) + extra = (budget + extra) - 1 := by omega
      exact .cons more (subtraction ▸ replay extra rest)

end PaidWord

/-- Forgetting purse annotations produces steps of the actual workspace
GSLT, while retaining every intermediate state. -/
def paidWordOperational : {state target : State} → {budget remaining : Nat} →
    {commands : List Input} → PaidWord step state budget commands target remaining →
      theory.RewritePath state target
  | _, _, _, _, _, .nil state _ => GSLT.RewritePath.nil (S := theory) state
  | _, _, _, _, _, .cons _ rest =>
      GSLT.RewritePath.cons (S := theory) ⟨_, rfl⟩ (paidWordOperational rest)

theorem paidWordOperational_length {state target : State} {budget remaining : Nat}
    {commands : List Input} (path : PaidWord step state budget commands target remaining) :
    (paidWordOperational path).length = commands.length := by
  induction path with
  | nil => rfl
  | cons _ _ inductionHypothesis =>
      simp only [paidWordOperational, GSLT.RewritePath.length, List.length_cons]
      omega

/-- Read only declared public fields after executing the intervention. -/
def readField (field : Field) (state : State) : Bool :=
  match field with
  | .workspace => state.context.1
  | .report => state.context.2
  | .attention => state.commitments

structure Question where
  commands : List Input
  field : Field
  deriving DecidableEq, Repr

def observation (state : State) (question : Question) : Bool :=
  readField question.field (run state question.commands)

def protocol : Protocol Question Bool where
  test _ value := value
  deliveryCost _ _ := 2
  inspectionCost _ _ := 3

theorem observation_native_iff (state : State) (question : Question) (value : Bool) :
    observation state question = value ↔
      (Mettapedia.OSLF.Framework.GSLTTypeSynthesis.gsltOSLF theory).satisfies (S := ()) state
        (probeNativeType question.commands (question.field, value)).pred := by
  change observation state question = value ↔
    modal.sat (probeFormula question.commands (question.field, value)) state
  rw [probeFormula_exact]
  cases question with
  | mk commands field => cases field <;> exact Iff.rfl

def probeCount (question : Question) (budget : Nat) : Nat :=
  min budget question.commands.length

def probeEndpoint (state : State) (question : Question) (budget : Nat) : State :=
  run state (question.commands.take budget)

def probeRemaining (question : Question) (budget : Nat) : Nat :=
  budget - probeCount question budget

/-- A partial command execution preserves its actual paid prefix. -/
def probePath (state : State) (question : Question) (budget : Nat) :
    PaidWord step state budget (question.commands.take budget)
      (probeEndpoint state question budget) (probeRemaining question budget) := by
  have affordable : (question.commands.take budget).length ≤ budget := List.length_take_le _ _
  simpa only [probeEndpoint, probeRemaining, probeCount, run, List.length_take,
    Nat.min_comm] using PaidWord.execute step state (question.commands.take budget) budget affordable

def request (state : State) (question : Question) (budget session provider client : Nat) :
    Request Question Bool Nat Nat where
  question := question
  session := session
  provider := provider
  client := client
  arrival := if question.commands.length ≤ budget then
    some (readField question.field (probeEndpoint state question budget)) else none

/-- The full concrete snapshot and path precede the supplied offer. -/
structure Experiment (state : State) (question : Question)
    (budget session provider client : Nat) where
  probe : PaidWord step state budget (question.commands.take budget)
    (probeEndpoint state question budget) (probeRemaining question budget)
  assay : Round protocol (request state question budget session provider client)
    (probeRemaining question budget)

def execute (state : State) (question : Question) (budget session provider client : Nat) :
    Experiment state question budget session provider client where
  probe := probePath state question budget
  assay := completedRound protocol (request state question budget session provider client)
    (probeRemaining question budget)

namespace Experiment

variable {state : State} {question : Question} {budget session provider client : Nat}

def responses (experiment : Experiment state question budget session provider client) :
    Multiset (Response Bool Nat) := experiment.assay.responses

def spent (experiment : Experiment state question budget session provider client) : Nat :=
  probeCount question budget + experiment.assay.spent

def remaining (experiment : Experiment state question budget session provider client) : Nat :=
  experiment.assay.remaining

theorem ledger (experiment : Experiment state question budget session provider client) :
    budget = experiment.remaining + experiment.spent := by
  have probeLedger := experiment.probe.ledger
  have assayLedger := experiment.assay.ledger
  simp only [List.length_take] at probeLedger
  change budget = experiment.assay.remaining +
    (min budget question.commands.length + experiment.assay.spent)
  omega

theorem response_sound (experiment : Experiment state question budget session provider client)
    (response : Response Bool Nat) (present : response ∈ experiment.responses) :
    question.commands.length + 2 + 3 ≤ budget ∧
      response = (session, ComplementaryAssay.verdictOf (observation state question), client,
        observation state question) ∧
      experiment.responses = {response} ∧
      experiment.spent = question.commands.length + 2 + 3 := by
  obtain ⟨value, arrives, responseEq, singleton, affordable, assaySpent⟩ :=
    experiment.assay.response_sound response present
  have completed : question.commands.length ≤ budget := by
    by_contra incomplete
    simp only [request, if_neg incomplete] at arrives
    cases arrives
  have actual : value = observation state question := by
    simp only [request, if_pos completed, probeEndpoint] at arrives
    rw [List.take_of_length_le completed] at arrives
    exact (Option.some.inj arrives).symm
  subst value
  have count : probeCount question budget = question.commands.length :=
    Nat.min_eq_right completed
  have available : probeRemaining question budget = budget - question.commands.length := by
    simp only [probeRemaining, count]
  change 2 + 3 ≤ probeRemaining question budget at affordable
  change experiment.assay.spent = 2 + 3 at assaySpent
  refine ⟨by omega, responseEq, singleton, ?_⟩
  change probeCount question budget + experiment.assay.spent = _
  omega

theorem underfunded_silent (experiment : Experiment state question budget session provider client)
    (underfunded : budget < question.commands.length + 2 + 3) : experiment.responses = 0 := by
  by_contra responds
  obtain ⟨response, present⟩ := Multiset.exists_mem_of_ne_zero responds
  have affordable := (experiment.response_sound response present).1
  omega

private theorem probeRemaining_replay (complete : question.commands.length ≤ budget) (extra : Nat) :
    probeRemaining question budget + extra = probeRemaining question (budget + extra) := by
  have more : question.commands.length ≤ budget + extra := by omega
  simp only [probeRemaining, probeCount, Nat.min_eq_right complete, Nat.min_eq_right more]
  omega

private theorem request_replay (complete : question.commands.length ≤ budget) (extra : Nat) :
    request state question budget session provider client =
      request state question (budget + extra) session provider client := by
  have more : question.commands.length ≤ budget + extra := by omega
  simp only [request, if_pos complete, if_pos more, probeEndpoint,
    List.take_of_length_le complete, List.take_of_length_le more]

private def castRound {first second : Request Question Bool Nat Nat} {before after : Nat}
    (offered : first = second) (funding : before = after)
    (round : Round protocol first before) : Round protocol second after :=
  funding ▸ offered ▸ round

private theorem castRound_responses {first second : Request Question Bool Nat Nat} {before after : Nat}
    (offered : first = second) (funding : before = after) (round : Round protocol first before) :
    (castRound offered funding round).responses = round.responses := by
  cases offered
  cases funding
  rfl

private theorem castRound_spent {first second : Request Question Bool Nat Nat} {before after : Nat}
    (offered : first = second) (funding : before = after) (round : Round protocol first before) :
    (castRound offered funding round).spent = round.spent := by
  cases offered
  cases funding
  rfl

private theorem castRound_remaining {first second : Request Question Bool Nat Nat} {before after : Nat}
    (offered : first = second) (funding : before = after) (round : Round protocol first before) :
    (castRound offered funding round).remaining = round.remaining := by
  cases offered
  cases funding
  rfl

/-- Replaying a previously completed intervention retains its given assay
prefix, even if the increased purse could enable an additional inspection. -/
def replay (experiment : Experiment state question budget session provider client)
    (complete : question.commands.length ≤ budget) (extra : Nat) :
    Experiment state question (budget + extra) session provider client where
  probe := by
    have more : question.commands.length ≤ budget + extra := by omega
    have original := experiment.probe.replay extra
    rw [probeRemaining_replay complete extra] at original
    simpa only [probeEndpoint, List.take_of_length_le complete,
      List.take_of_length_le more] using original
  assay := castRound (request_replay complete extra) (probeRemaining_replay complete extra)
    (experiment.assay.replay extra)

theorem replay_responses (experiment : Experiment state question budget session provider client)
    (complete : question.commands.length ≤ budget) (extra : Nat) :
    (experiment.replay complete extra).responses = experiment.responses := by
  change (castRound _ _ (experiment.assay.replay extra)).responses = experiment.assay.responses
  rw [castRound_responses, Round.replay_responses]

theorem replay_spent (experiment : Experiment state question budget session provider client)
    (complete : question.commands.length ≤ budget) (extra : Nat) :
    (experiment.replay complete extra).spent = experiment.spent := by
  have more : question.commands.length ≤ budget + extra := by omega
  change probeCount question (budget + extra) +
    (castRound _ _ (experiment.assay.replay extra)).spent =
      probeCount question budget + experiment.assay.spent
  rw [castRound_spent, Round.replay_spent]
  simp only [probeCount, Nat.min_eq_right complete, Nat.min_eq_right more]

theorem replay_remaining (experiment : Experiment state question budget session provider client)
    (complete : question.commands.length ≤ budget) (extra : Nat) :
    (experiment.replay complete extra).remaining = experiment.remaining + extra := by
  change (castRound _ _ (experiment.assay.replay extra)).remaining = experiment.assay.remaining + extra
  rw [castRound_remaining, Round.replay_remaining]

end Experiment

theorem execute_responses (state : State) (question : Question)
    (budget session provider client : Nat) :
    (execute state question budget session provider client).responses =
      if question.commands.length + 2 + 3 ≤ budget then
        {(session, ComplementaryAssay.verdictOf (observation state question), client,
          observation state question)} else 0 := by
  by_cases full : question.commands.length + 2 + 3 ≤ budget
  · have probeAffordable : question.commands.length ≤ budget := by omega
    have count : probeCount question budget = question.commands.length :=
      Nat.min_eq_right probeAffordable
    have affordable : 2 + 3 ≤ probeRemaining question budget := by
      simp only [probeRemaining, count]
      omega
    rw [if_pos full]
    change (completedRound protocol (request state question budget session provider client)
      (probeRemaining question budget)).responses = _
    rw [completedRound_responses]
    simp only [request, if_pos probeAffordable, probeEndpoint,
      List.take_of_length_le probeAffordable, protocol, AssayProbeDelivery.observed_some,
      if_pos affordable, observation]
  · exact (if_neg full).symm ▸
      (execute state question budget session provider client).underfunded_silent (by omega)

theorem execute_full_ledger (state : State) (question : Question)
    (budget session provider client : Nat)
    (affordable : question.commands.length + 2 + 3 ≤ budget) :
    (execute state question budget session provider client).spent =
        question.commands.length + 2 + 3 ∧
      (execute state question budget session provider client).remaining =
        budget - (question.commands.length + 2 + 3) := by
  have responses := execute_responses state question budget session provider client
  rw [if_pos affordable] at responses
  have present : (session, ComplementaryAssay.verdictOf (observation state question), client,
      observation state question) ∈ (execute state question budget session provider client).responses := by
    rw [responses]
    exact Multiset.mem_singleton_self _
  have paid := (execute state question budget session provider client).response_sound _ present
  have conserved := (execute state question budget session provider client).ledger
  exact ⟨paid.2.2.2, by omega⟩

/-! ## Operational learner on the executed answers -/

def prediction (mode : Mode) (question : Question) : Bool := observation (initial mode) question

def candidates : Finset Mode := {.connected, .shadow}

def revised (state : State) (question : Question) (budget session provider client : Nat) :
    Finset Mode := revise prediction candidates question
      (execute state question budget session provider client).responses

def separatingQuestion : Question := ⟨broadcastWord false true, .report⟩

theorem separating_price : separatingQuestion.commands.length + 2 + 3 = 7 := rfl

theorem funded_separating_ledger (mode : Mode) :
    (execute (initial mode) separatingQuestion 7 10 20 30).spent = 7 ∧
      (execute (initial mode) separatingQuestion 7 10 20 30).remaining = 0 :=
  execute_full_ledger (initial mode) separatingQuestion 7 10 20 30 (by decide)

theorem separating_execution_answers :
    observation (initial .connected) separatingQuestion = true ∧
      observation (initial .shadow) separatingQuestion = false := by
  simp [observation, separatingQuestion, run, broadcastWord, step, readField, reading, initial]

theorem connected_funded_separates :
    revised (initial .connected) separatingQuestion 7 10 20 30 = {.connected} := by
  ext mode
  cases mode <;>
    simp [revised, execute_responses, separatingQuestion, broadcastWord, observation,
      readField, run, step, reading, initial, candidates, prediction, revise, Compatible,
      ComplementaryAssay.verdictOf_bit]

theorem shadow_funded_separates :
    revised (initial .shadow) separatingQuestion 7 10 20 30 = {.shadow} := by
  ext mode
  cases mode <;>
    simp [revised, execute_responses, separatingQuestion, broadcastWord, observation,
      readField, run, step, reading, initial, candidates, prediction, revise, Compatible,
      ComplementaryAssay.verdictOf_bit]

theorem one_unit_short_has_no_verdict (mode : Mode) :
    (execute (initial mode) separatingQuestion 6 10 20 30).responses = 0 :=
  (execute (initial mode) separatingQuestion 6 10 20 30).underfunded_silent (by decide)

theorem one_unit_short_preserves_candidates (mode : Mode) :
    revised (initial mode) separatingQuestion 6 10 20 30 = candidates := by
  rw [revised, one_unit_short_has_no_verdict]
  exact silence_preserves prediction candidates separatingQuestion

/-- The one-token-short experiment really reaches the delivered packet;
only its positive-price inspection is missing. -/
theorem one_unit_short_delivery_only (mode : Mode) :
    (execute (initial mode) separatingQuestion 6 10 20 30).assay.endpoint =
      AssayProbeDelivery.paidReceived 10 20 30
        (observation (initial mode) separatingQuestion) 2 := by
  change (AssayProbeDelivery.execute (fun value : Bool => value) (fun _ => 2) (fun _ => 3)
    10 20 30 (some (observation (initial mode) separatingQuestion)) 4).1 = _
  simp only [AssayProbeDelivery.execute, dif_pos (by decide : 2 ≤ 4),
    dif_neg (by decide : ¬ 3 ≤ 4 - 2)]
  rfl

theorem correct_candidate_survives (mode : Mode) (question : Question)
    (budget session provider client : Nat) :
    mode ∈ revised (initial mode) question budget session provider client := by
  apply (revise_mem prediction candidates question _ mode).2
  refine ⟨by cases mode <;> simp [candidates], ?_⟩
  intro response present
  have sound := (execute (initial mode) question budget session provider client).response_sound response present
  rw [sound.2.1]
  exact (ComplementaryAssay.verdictOf_bit _).symm

/-- Passive word experiments have identical authenticated public packets at
the same budget, provider, client and session. -/
def passiveQuestion (commands : List PassiveInput) (field : Field) : Question :=
  ⟨commands.map Input.ordinary, field⟩

theorem passive_observation_eq (commands : List PassiveInput) (field : Field) :
    observation (initial .connected) (passiveQuestion commands field) =
      observation (initial .shadow) (passiveQuestion commands field) := by
  have same := congrFun ordinary_interactions_cannot_separate_modes commands
  have runPassive (state : State) :
      run state (commands.map Input.ordinary) = commands.foldl passiveStep state := by
    simp only [run, List.foldl_map]
    rfl
  change evaluation (commands.foldl passiveStep (initial .connected)) =
    evaluation (commands.foldl passiveStep (initial .shadow)) at same
  change readField field (run (initial .connected) (commands.map Input.ordinary)) =
    readField field (run (initial .shadow) (commands.map Input.ordinary))
  rw [runPassive, runPassive]
  cases field with
  | workspace => exact congrArg (fun value : Bool × Bool × Module => value.1) same
  | report => exact congrArg (fun value : Bool × Bool × Module => value.2.1) same
  | attention => exact congrArg (fun value : Bool × Bool × Module => value.2.2) same

theorem passive_answers_agree (commands : List PassiveInput) (field : Field)
    (budget session provider client : Nat) :
    (execute (initial .connected) (passiveQuestion commands field) budget session provider client).responses =
      (execute (initial .shadow) (passiveQuestion commands field) budget session provider client).responses := by
  rw [execute_responses, execute_responses, passive_observation_eq]

theorem passive_question_preserves_candidates (mode : Mode) (commands : List PassiveInput)
    (field : Field) (budget session provider client : Nat) :
    revised (initial mode) (passiveQuestion commands field) budget session provider client = candidates := by
  apply Finset.Subset.antisymm (revise_subset _ _ _ _)
  intro hypothesis member
  apply (revise_mem _ _ _ _ _).2
  refine ⟨member, ?_⟩
  intro response present
  have sound := (execute (initial mode) (passiveQuestion commands field)
    budget session provider client).response_sound response present
  rw [sound.2.1, ComplementaryAssay.verdictOf_bit]
  cases hypothesis <;> cases mode <;>
    simp only [prediction, passive_observation_eq]

/-- Any sequential campaign made from these actual passive experiments
preserves both candidates; the next experiment receives the previous purse. -/
def passiveLearning (mode : Mode) :
    List (List PassiveInput × Field) → Nat → Nat → Finset Mode → Finset Mode
  | [], _, _, candidates => candidates
  | query :: queries, budget, session, candidates =>
      let experiment := execute (initial mode) (passiveQuestion query.1 query.2)
        budget session 20 30
      passiveLearning mode queries experiment.remaining (session + 1)
        (revise prediction candidates (passiveQuestion query.1 query.2) experiment.responses)

theorem passive_campaign_preserves_candidates (mode : Mode)
    (queries : List (List PassiveInput × Field)) (budget session : Nat) :
    passiveLearning mode queries budget session candidates = candidates := by
  induction queries generalizing budget session with
  | nil => rfl
  | cons query queries inductionHypothesis =>
      simp only [passiveLearning]
      rw [← revised, passive_question_preserves_candidates]
      exact inductionHypothesis _ _

/-! ## The nonidentity operational compression and context square -/

def coreRun (state : CoreState) (commands : List Input) : CoreState := commands.foldl coreStep state

theorem compression_commands_commute (state : State) (commands : List Input) :
    coreView (run state commands) = coreRun (coreView state) commands := by
  induction commands generalizing state with
  | nil => rfl
  | cons command commands inductionHypothesis =>
      exact (inductionHypothesis (step state command)).trans
        (congrArg (fun state => coreRun state commands) (coreStep_commutes state command))

def coreReadField (field : Field) (state : CoreState) : Bool := readField field (restore state)

def coreObservation (state : CoreState) (question : Question) : Bool :=
  coreReadField question.field (coreRun state question.commands)

theorem compression_observation (state : State) (question : Question) :
    coreReadField question.field (coreRun (coreView state) question.commands) =
      observation state question := by
  rw [← compression_commands_commute]
  cases question with
  | mk commands field => cases field <;> rfl

def coreProtocol : Protocol Question Bool where
  test _ value := value
  deliveryCost _ _ := Nat.succ 1
  inspectionCost _ _ := Nat.succ 2

/-- The independent core command account uses chronological summation. -/
def coreCommandPrice (commands : List Input) : Nat :=
  commands.foldr (fun _ spent => 1 + spent) 0

theorem coreCommandPrice_exact (commands : List Input) :
    coreCommandPrice commands = commands.length := by
  induction commands with
  | nil => rfl
  | cons command commands inductionHypothesis =>
      change 1 + coreCommandPrice commands = commands.length + 1
      omega

def coreProbeEndpoint (state : CoreState) (question : Question) (budget : Nat) : CoreState :=
  coreRun state (question.commands.take budget)

def coreRequest (state : CoreState) (question : Question) (budget session provider client : Nat) :
    Request Question Bool Nat Nat where
  question := question
  session := session
  provider := provider
  client := client
  arrival := if question.commands.length ≤ budget then
    some (coreReadField question.field (coreProbeEndpoint state question budget)) else none

structure CoreExperiment (state : CoreState) (question : Question)
    (budget session provider client : Nat) where
  probe : PaidWord coreStep state budget (question.commands.take budget)
    (coreProbeEndpoint state question budget) (probeRemaining question budget)
  assay : Round coreProtocol (coreRequest state question budget session provider client)
    (probeRemaining question budget)

def coreExecute (state : CoreState) (question : Question) (budget session provider client : Nat) :
    CoreExperiment state question budget session provider client where
  probe := by
    have affordable : (question.commands.take budget).length ≤ budget := List.length_take_le _ _
    simpa only [coreProbeEndpoint, coreRun, probeRemaining, probeCount, List.length_take,
      Nat.min_comm] using
        PaidWord.execute coreStep state (question.commands.take budget) budget affordable
  assay := completedRound coreProtocol (coreRequest state question budget session provider client)
    (probeRemaining question budget)

theorem compression_request (state : State) (question : Question)
    (budget session provider client : Nat) :
    coreRequest (coreView state) question budget session provider client =
      request state question budget session provider client := by
  have readout : coreReadField question.field (coreProbeEndpoint (coreView state) question budget) =
      readField question.field (probeEndpoint state question budget) := by
    unfold coreProbeEndpoint probeEndpoint
    rw [← compression_commands_commute]
    cases question with
    | mk commands field => cases field <;> rfl
  simp only [coreRequest, request, readout]

/-- Independent controller paths have equal answers at the declared
compression; the concrete starting state stays in the source receipt. -/
theorem compression_responses (state : State) (question : Question)
    (budget session provider client : Nat) :
    (coreExecute (coreView state) question budget session provider client).assay.responses =
      (execute state question budget session provider client).responses := by
  change (completedRound coreProtocol (coreRequest (coreView state) question budget session provider client)
      (probeRemaining question budget)).responses =
    (completedRound protocol (request state question budget session provider client)
      (probeRemaining question budget)).responses
  rw [compression_request]
  rfl

def compressionProtocol : Translation
    (Providers := Nat) (Providers' := Nat) (Clients := Nat) (Clients' := Nat)
    protocol coreProtocol where
  question := id
  value := id
  provider := id
  client := id
  test _ _ := rfl
  delivery _ _ := rfl
  inspection _ _ := rfl

theorem compression_protocol_request (state : State) (question : Question)
    (budget session provider client : Nat) :
    compressionProtocol.request (request state question budget session provider client) =
      coreRequest (coreView state) question budget session provider client := by
  rw [compression_request]
  simp only [Translation.request, compressionProtocol, request, id_eq, Option.map_id]

/-- The actual command and resource-occurrence paths are transported.
The target receipt still refers to the original source receipt externally;
the noninjective state compression supplies no inverse origin reconstruction. -/
def compressExperiment {state : State} {question : Question}
    {budget session provider client : Nat}
    (experiment : Experiment state question budget session provider client) :
    CoreExperiment (coreView state) question budget session provider client where
  probe := by
    have mapped := experiment.probe.map coreView coreStep coreStep_commutes
    have endpoint : coreView (probeEndpoint state question budget) =
        coreProbeEndpoint (coreView state) question budget :=
      compression_commands_commute state (question.commands.take budget)
    exact endpoint ▸ mapped
  assay := compression_protocol_request state question budget session provider client ▸
    compressionProtocol.round experiment.assay

private theorem castRound_responses {first second : Request Question Bool Nat Nat}
    {budget : Nat} (same : first = second) (round : Round coreProtocol first budget) :
    (same ▸ round).responses = round.responses := by
  cases same
  rfl

private theorem castRound_remaining {first second : Request Question Bool Nat Nat}
    {budget : Nat} (same : first = second) (round : Round coreProtocol first budget) :
    (same ▸ round).remaining = round.remaining := by
  cases same
  rfl

private theorem castRound_spent {first second : Request Question Bool Nat Nat}
    {budget : Nat} (same : first = second) (round : Round coreProtocol first budget) :
    (same ▸ round).spent = round.spent := by
  cases same
  rfl

theorem compressExperiment_responses {state : State} {question : Question}
    {budget session provider client : Nat}
    (experiment : Experiment state question budget session provider client) :
    (compressExperiment experiment).assay.responses = experiment.responses := by
  change (compression_protocol_request state question budget session provider client ▸
    compressionProtocol.round experiment.assay).responses = experiment.assay.responses
  rw [castRound_responses, Translation.round_responses]
  have responseIdentity : compressionProtocol.response = id := by
    funext answer
    rcases answer with ⟨session, verdict, client, payload⟩
    rfl
  rw [responseIdentity, Multiset.map_id]

theorem compressExperiment_remaining {state : State} {question : Question}
    {budget session provider client : Nat}
    (experiment : Experiment state question budget session provider client) :
    (compressExperiment experiment).assay.remaining = experiment.remaining := by
  change (compression_protocol_request state question budget session provider client ▸
    compressionProtocol.round experiment.assay).remaining = experiment.assay.remaining
  rw [castRound_remaining]
  exact compressionProtocol.round_remaining experiment.assay

theorem compressExperiment_spent {state : State} {question : Question}
    {budget session provider client : Nat}
    (experiment : Experiment state question budget session provider client) :
    coreCommandPrice (question.commands.take budget) +
        (compressExperiment experiment).assay.spent = experiment.spent := by
  rw [coreCommandPrice_exact, List.length_take]
  change min budget question.commands.length +
    (compression_protocol_request state question budget session provider client ▸
      compressionProtocol.round experiment.assay).spent = experiment.spent
  rw [castRound_spent, Translation.round_spent]
  rfl

/-- Reducing the protocol's target prices preserves the raw answer test,
but changes affordability. This is not an admitted charge comparison. -/
def incorrectlyUnchargedCoreProtocol : Protocol Question Bool where
  test _ value := value
  deliveryCost _ _ := 1
  inspectionCost _ _ := 1

theorem discarding_charges_changes_affordability :
    (execute (initial .connected) separatingQuestion 6 10 20 30).responses = 0 ∧
      (completedRound incorrectlyUnchargedCoreProtocol
        (coreRequest (coreView (initial .connected)) separatingQuestion 6 10 20 30) 4).responses ≠ 0 := by
  refine ⟨one_unit_short_has_no_verdict _, ?_⟩
  rw [completedRound_responses, compression_request]
  change AssayProbeDelivery.observed (fun value : Bool => value) (fun _ => 1) (fun _ => 1)
    10 20 30 (some true) 4 ≠ 0
  rw [AssayProbeDelivery.observed_some, if_pos (by decide : 1 + 1 ≤ 4)]
  exact Multiset.singleton_ne_zero _

def compressPaidWord {state target : State} {budget remaining : Nat} {commands : List Input}
    (path : PaidWord step state budget commands target remaining) :
    PaidWord coreStep (coreView state) budget commands (coreView target) remaining :=
  path.map coreView coreStep coreStep_commutes

theorem compression_charge_preserved (question : Question) (value : Bool) :
    coreCommandPrice question.commands + coreProtocol.deliveryCost question value +
        coreProtocol.inspectionCost question value =
      question.commands.length + protocol.deliveryCost question value +
        protocol.inspectionCost question value := by
  rw [coreCommandPrice_exact]
  rfl

open Mettapedia.GSLT.IndexedOperational
open Mettapedia.GSLT.MinimalEnablingContext
open Mettapedia.GSLT.AdmissibleContextCongruence
open Mettapedia.GSLT.Causality.Abstraction

/-- Contexts are complete admitted command words, not term equality. -/
def wordRules : ContextualRules theory where
  Context := List Input
  identity := []
  compose outer inner := inner ++ outer
  plug := fun commands state => run state commands
  plug_identity _ := rfl
  plug_compose _ _ _ := List.foldl_append
  plug_resp := by intro _ _ _ same; cases same; rfl
  Rule := Input
  fires command state target := step state command = target
  fires_resp_left := by
    intro command state other target same advances
    cases same
    exact ⟨target, advances, rfl⟩
  fires_resp_right := by
    intro command state target other advances same
    cases same
    exact advances
  fires_step := fun {command _ _} advances => ⟨command, advances⟩

def coreWordRules : ContextualRules coreTheory where
  Context := List Input
  identity := []
  compose outer inner := inner ++ outer
  plug := fun commands state => coreRun state commands
  plug_identity _ := rfl
  plug_compose _ _ _ := List.foldl_append
  plug_resp := by intro _ _ _ same; cases same; rfl
  Rule := Input
  fires command state target := coreStep state command = target
  fires_resp_left := by
    intro command state other target same advances
    cases same
    exact ⟨target, advances, rfl⟩
  fires_resp_right := by
    intro command state target other advances same
    cases same
    exact advances
  fires_step := fun {command _ _} advances => ⟨command, advances⟩

def wordClass : AdmissibleClass wordRules := ⊤

def coreWordClass : AdmissibleClass coreWordRules := ⊤

/-- The core transition independently computes its successor; both forward
and outgoing reflection hold for every architectural command. -/
def compressionOperational : SemanticCoveredTranslation theory coreTheory where
  mapTerm := coreView
  mapEquiv := by intro _ _ same; cases same; rfl
  mapStep := by
    intro state target advances
    obtain ⟨command, rfl⟩ := advances
    exact ⟨command, (coreStep_commutes state command).symm⟩
  liftStep := by
    intro state target advances
    obtain ⟨command, advances⟩ := advances
    exact ⟨step state command, ⟨command, rfl⟩,
      (coreStep_commutes state command).trans advances⟩

def compressionInterventions : InterventionMap wordClass coreWordClass where
  map := id
  admissible _ := AdmissibleClass.top_admissible _

theorem compression_context_square (commands : List Input) (state : State) :
    coreTheory.Equiv
      (compressionOperational.mapTerm (wordRules.plug commands state))
      (coreWordRules.plug (compressionInterventions.map commands)
        (compressionOperational.mapTerm state)) :=
  compression_commands_commute state commands

def fieldObservations : ContextualRules.Observations theory where
  Atom := Field × Bool
  observes atom state := readField atom.1 state = atom.2
  observes_resp := by intro _ _ _ same; cases same; rfl

def coreFieldObservations : ContextualRules.Observations coreTheory where
  Atom := Field × Bool
  observes atom state := coreReadField atom.1 state = atom.2
  observes_resp := by intro _ _ _ same; cases same; rfl

theorem compression_field_iff (atom : Field × Bool) (state : State) :
    fieldObservations.observes atom state ↔
      coreFieldObservations.observes atom (compressionOperational.mapTerm state) := by
  rcases atom with ⟨field, value⟩
  cases field <;> exact Iff.rfl

/-- This invokes the existing contextual-realization theorem with an earned
square over all finite component interventions. -/
def compressionContextualCover : Mettapedia.GSLT.HennessyMilner.SystemCover
    (wordClass.saturated fieldObservations)
    (coreWordClass.saturated coreFieldObservations) :=
  ContextualRealization.saturatedCover compressionOperational compressionInterventions
    fieldObservations coreFieldObservations id compression_field_iff
    (fun {context} _ state => compression_context_square context state)

theorem compression_is_not_injective : ¬ Function.Injective coreView := by
  intro injective
  have same := injective different_counts_same_core
  have count := congrArg (fun state => state.evidence) same
  have impossible : (0 : Nat) = 7 := count
  omega

/-- Complete dependent experiment receipts retain the concrete snapshot
after the behavioral compression forgets its administrative event count. -/
def countedReceipt (count : Nat) :
    Σ state : State, Experiment state separatingQuestion 7 10 20 30 :=
  ⟨counted count, execute (counted count) separatingQuestion 7 10 20 30⟩

theorem counted_receipts_same_answer :
    (countedReceipt 0).2.responses = (countedReceipt 7).2.responses := by
  change (execute (counted 0) separatingQuestion 7 10 20 30).responses =
    (execute (counted 7) separatingQuestion 7 10 20 30).responses
  rw [← compression_responses, ← compression_responses, different_counts_same_core]

theorem counted_receipts_distinct : countedReceipt 0 ≠ countedReceipt 7 := by
  intro same
  have states := congrArg Sigma.fst same
  have counts := congrArg (fun state => state.evidence) states
  change (0 : Nat) = 7 at counts
  omega

/-- The independently formed full formula descriptions agree under this
noninjective operational compression, including admitted interventions. -/
theorem compression_phenomenal_description_exact
    (context : Set PhenomenalRealization.WorkspaceDescriptions.Query) (state : State) :
    PhenomenalRealization.FormulaDescriptions.describe coreModal context (coreView state) =
      PhenomenalRealization.FormulaDescriptions.describe modal context state :=
  PhenomenalRealization.WorkspaceDescriptions.compressed_description_exact context state

end Mettapedia.CognitiveArchitecture.Consciousness.PaidWorkspaceExperiments
