import Mettapedia.CogArch.Consciousness.PaidWorkspaceExperiments
import Mettapedia.OSLF.Framework.PaidInterventionalDescriptions

/-!
# Partial workspace descriptions with complete paid evidence

Descriptions read authenticated packets from supplied actual experiments.
The concrete snapshot is an external index, while features select declared
interventions and fields. Complete evidence retains that snapshot, every
command, both paths, provider/client/session and all purse projections.

A supplied experiment family is not a claim that its individually funded
members share one purse. The sequential campaign type below passes each
remaining purse to the next experiment before computing its whole ledger.

The nonidentity architectural compression maps actual command and resource
occurrences. Reindexing changes the question vocabulary only; it does not
invent source snapshots in the fibre of the noninjective compression.
-/

set_option autoImplicit false

namespace Mettapedia.CogArch.Consciousness.PaidWorkspaceDescriptions

open Mettapedia.GSLT.Causality
open Mettapedia.GSLT.Causality.ProbeCampaign
open Mettapedia.CategoryTheory.PartialSections
open Mettapedia.CogArch.Consciousness.ArchitecturalIndicators
open Mettapedia.CogArch.Consciousness.PaidWorkspaceExperiments
open Mettapedia.OSLF.Framework.PaidInterventionalDescriptions
open Mettapedia.OSLF.Framework.FiniteAssayLearner

/-- The answer erases the actual paths, but cannot expose a bit from an
empty endpoint packet. -/
noncomputable def answer {state : State} {question : Question}
    {budget session provider client : Nat}
    (experiment : Experiment state question budget session provider client) : Option Bool :=
  packetAnswer experiment.responses

theorem answer_none {state : State} {question : Question} {budget session provider client : Nat}
    (experiment : Experiment state question budget session provider client) :
    answer experiment = none ↔ experiment.responses = 0 := packetAnswer_none _

theorem answer_some {state : State} {question : Question} {budget session provider client : Nat}
    (experiment : Experiment state question budget session provider client) (value : Bool) :
    answer experiment = some value ↔
      ∃ response ∈ experiment.responses, response.2.1.bit = value :=
  packetAnswer_some _ (Round.consistent experiment.assay) value

/-- A public answer agrees with the independent operational observation,
using the actual authenticated response and paid-command completion. -/
theorem answer_agrees {state : State} {question : Question} {budget session provider client : Nat}
    (experiment : Experiment state question budget session provider client) (value : Bool)
    (answered : answer experiment = some value) : value = observation state question := by
  obtain ⟨response, member, readout⟩ := (answer_some experiment value).mp answered
  have sound := experiment.response_sound response member
  rw [sound.2.1, ComplementaryAssay.verdictOf_bit] at readout
  exact readout.symm

/-- The full dependent receipt keeps independently indexed protocol origins
instead of recovering them from the public Boolean answer. -/
structure AnsweredExperiment (state : State) (question : Question)
    (budget session provider client : Nat) (value : Bool) where
  experiment : Experiment state question budget session provider client
  response : Response Bool Nat
  authenticated : response ∈ experiment.responses
  readout : response.2.1.bit = value

namespace AnsweredExperiment

variable {state : State} {question : Question} {budget session provider client : Nat} {value : Bool}

theorem actual_answer (receipt : AnsweredExperiment state question budget session provider client value) :
    answer receipt.experiment = some value :=
  (answer_some _ _).mpr ⟨receipt.response, receipt.authenticated, receipt.readout⟩

theorem observation_agrees (receipt : AnsweredExperiment state question budget session provider client value) :
    value = observation state question := answer_agrees receipt.experiment value receipt.actual_answer

theorem authenticated_fields
    (receipt : AnsweredExperiment state question budget session provider client value) :
    receipt.response =
      (session, ComplementaryAssay.verdictOf (observation state question), client,
        observation state question) ∧
      question.commands.length + 2 + 3 ≤ budget ∧
      receipt.experiment.spent = question.commands.length + 2 + 3 := by
  have sound := receipt.experiment.response_sound receipt.response receipt.authenticated
  exact ⟨sound.2.1, sound.1, sound.2.2.2⟩

/-- The native assertion is earned from the admitted, actually executed
context and independently specified observation. -/
theorem native_certificate
    (receipt : AnsweredExperiment state question budget session provider client value) :
    (Mettapedia.OSLF.Framework.GSLTTypeSynthesis.gsltOSLF theory).satisfies (S := ()) state
      (probeNativeType question.commands (question.field, value)).pred :=
  (observation_native_iff state question value).mp receipt.observation_agrees.symm

def replay (receipt : AnsweredExperiment state question budget session provider client value)
    (extra : Nat) : AnsweredExperiment state question (budget + extra) session provider client value where
  experiment := receipt.experiment.replay (by have paid := receipt.authenticated_fields.2.1; omega) extra
  response := receipt.response
  authenticated := by rw [Experiment.replay_responses]; exact receipt.authenticated
  readout := receipt.readout

theorem replay_remaining
    (receipt : AnsweredExperiment state question budget session provider client value) (extra : Nat) :
    (receipt.replay extra).experiment.remaining = receipt.experiment.remaining + extra :=
  Experiment.replay_remaining receipt.experiment
    (by have paid := receipt.authenticated_fields.2.1; omega) extra

end AnsweredExperiment

/-- Each member stores its actual paid execution. Its budget is not a claim
of simultaneous affordability of all members. -/
structure Family (state : State) where
  budget : Question → Nat
  session : Question → Nat
  provider : Question → Nat
  client : Question → Nat
  experiment : ∀ question, Experiment state question (budget question) (session question)
    (provider question) (client question)

namespace Family

variable {state : State}

noncomputable def answers (family : Family state) (question : Question) : Option Bool :=
  answer (family.experiment question)

noncomputable def describe (family : Family state) : View Question Bool :=
  viewOfAnswers family.answers

/-- The fibre is tied to this family's exact supplied experiment. -/
def Receipts (family : Family state) (question : Question) (value : Bool) : Type :=
  {receipt : AnsweredExperiment state question (family.budget question) (family.session question)
      (family.provider question) (family.client question) value //
    receipt.experiment = family.experiment question}

theorem receipt_iff_answer (family : Family state) (question : Question) (value : Bool) :
    Nonempty (family.Receipts question value) ↔ family.answers question = some value := by
  constructor
  · rintro ⟨⟨receipt, actual⟩⟩
    change answer (family.experiment question) = some value
    rw [← actual]
    exact receipt.actual_answer
  · intro answered
    obtain ⟨response, member, readout⟩ := (answer_some _ value).mp answered
    exact ⟨⟨⟨family.experiment question, response, member, readout⟩, rfl⟩⟩

theorem answer_agrees (family : Family state) (question : Question) (value : Bool)
    (answered : family.answers question = some value) : value = observation state question :=
  PaidWorkspaceDescriptions.answer_agrees (family.experiment question) value answered

theorem description_value (family : Family state) (question : Question)
    (present : question ∈ family.describe.context) :
    family.describe.values ⟨question, present⟩ = observation state question :=
  family.answer_agrees question _ (viewOfAnswers_value family.answers question present)

/-- Feature reindexing is the existing partial-section operation, retaining
the same actual experiment in each selected coordinate. -/
noncomputable def selectedDescription {Features : Type} (select : Features → Question)
    (family : Family state) : View Features Bool := viewOfAnswers (family.answers ∘ select)

theorem selectedDescription_reindex {Features : Type} (select : Features → Question)
    (family : Family state) :
    family.selectedDescription select = reindexFeatures select family.describe :=
  viewOfAnswers_reindex select family.answers

def reviseAt (family : Family state) (question : Question) (candidates : Finset Mode) : Finset Mode :=
  revise prediction candidates question (family.experiment question).responses

/-- Revision uses every actual public packet. A partial answer is its exact
Boolean readout, and silence introduces no compatible/incompatible verdict. -/
theorem reviseAt_readout (family : Family state) (question : Question)
    (candidates : Finset Mode) (hypothesis : Mode) :
    hypothesis ∈ family.reviseAt question candidates ↔
      hypothesis ∈ candidates ∧
        ∀ value, family.answers question = some value → prediction hypothesis question = value := by
  rw [reviseAt, revise_mem]
  apply and_congr_right
  intro _
  constructor
  · intro compatible value answered
    obtain ⟨response, member, readout⟩ := (answer_some _ value).mp answered
    exact (compatible response member).trans readout
  · intro agrees response member
    exact agrees response.2.1.bit ((answer_some _ _).mpr ⟨response, member, rfl⟩)

end Family

/-! ## The actual nonidentity compressed experiment family -/

structure CoreFamily (state : CoreState) where
  budget : Question → Nat
  session : Question → Nat
  provider : Question → Nat
  client : Question → Nat
  experiment : ∀ question, CoreExperiment state question (budget question) (session question)
    (provider question) (client question)

namespace CoreFamily

variable {state : CoreState}

noncomputable def answers (family : CoreFamily state) (question : Question) : Option Bool :=
  packetAnswer (family.experiment question).assay.responses

noncomputable def describe (family : CoreFamily state) : View Question Bool := viewOfAnswers family.answers

def reviseAt (family : CoreFamily state) (question : Question) (candidates : Finset Mode) : Finset Mode :=
  revise prediction candidates question (family.experiment question).assay.responses

end CoreFamily

def Family.compress {state : State} (family : Family state) : CoreFamily (coreView state) where
  budget := family.budget
  session := family.session
  provider := family.provider
  client := family.client
  experiment question := compressExperiment (family.experiment question)

theorem Family.compress_answers {state : State} (family : Family state) (question : Question) :
    family.compress.answers question = family.answers question := by
  unfold CoreFamily.answers Family.answers Family.compress answer
  rw [compressExperiment_responses]

theorem Family.compress_describe {state : State} (family : Family state) :
    family.compress.describe = family.describe := by
  unfold CoreFamily.describe Family.describe
  congr 1
  funext question
  exact family.compress_answers question

theorem Family.compress_feature_reindex {state : State} {Features : Type}
    (family : Family state) (select : Features → Question) :
    viewOfAnswers (family.compress.answers ∘ select) =
      reindexFeatures select family.describe := by
  rw [viewOfAnswers_reindex]
  change reindexFeatures select family.compress.describe = reindexFeatures select family.describe
  rw [family.compress_describe]

theorem Family.compress_revision {state : State} (family : Family state)
    (question : Question) (candidates : Finset Mode) :
    family.compress.reviseAt question candidates = family.reviseAt question candidates := by
  unfold CoreFamily.reviseAt Family.reviseAt Family.compress
  rw [compressExperiment_responses]

/-! ## The complete paid workspace campaign -/

inductive Campaign (state : State) : Nat → List Question → Type where
  | nil (budget : Nat) : Campaign state budget []
  | cons {budget session provider client : Nat} {question : Question} {questions : List Question}
      (first : Experiment state question budget session provider client)
      (rest : Campaign state first.remaining questions) : Campaign state budget (question :: questions)

namespace Campaign

variable {state : State}

def remaining : {budget : Nat} → {questions : List Question} → Campaign state budget questions → Nat
  | _, _, .nil budget => budget
  | _, _, .cons _ rest => remaining rest

def spent : {budget : Nat} → {questions : List Question} → Campaign state budget questions → Nat
  | _, _, .nil _ => 0
  | _, _, .cons first rest => first.spent + spent rest

theorem ledger {budget : Nat} {questions : List Question} (campaign : Campaign state budget questions) :
    budget = campaign.remaining + campaign.spent := by
  induction campaign with
  | nil _ => rfl
  | cons first rest inductionHypothesis =>
      have firstLedger := first.ledger
      change _ = rest.remaining + (first.spent + rest.spent)
      omega

noncomputable def answerAt : {budget : Nat} → {questions : List Question} →
    Campaign state budget questions → Nat → Option Bool
  | _, _, .nil _, _ => none
  | _, _, .cons first _, 0 => answer first
  | _, _, .cons _ rest, index + 1 => answerAt rest index

noncomputable def describe {budget : Nat} {questions : List Question}
    (campaign : Campaign state budget questions) : View Nat Bool := viewOfAnswers campaign.answerAt

def learn : {budget : Nat} → {questions : List Question} →
    Campaign state budget questions → Finset Mode → Finset Mode
  | _, _, .nil _, candidates => candidates
  | _, question :: _, .cons first rest, candidates =>
      learn rest (revise prediction candidates question first.responses)

theorem learn_mem {budget : Nat} {questions : List Question}
    (campaign : Campaign state budget questions) (candidates : Finset Mode) (hypothesis : Mode) :
    hypothesis ∈ campaign.learn candidates ↔ hypothesis ∈ candidates ∧
      ∀ index question value, questions[index]? = some question →
        campaign.answerAt index = some value → prediction hypothesis question = value := by
  induction campaign generalizing candidates with
  | nil _ => simp [learn]
  | @cons budget session provider client question questions first rest inductionHypothesis =>
      change hypothesis ∈ rest.learn (revise prediction candidates question first.responses) ↔ _
      rw [inductionHypothesis, revise_mem]
      constructor
      · rintro ⟨⟨original, compatible⟩, restCompatible⟩
        refine ⟨original, ?_⟩
        intro index asked value found answered
        cases index with
        | zero =>
            have same : question = asked := Option.some.inj found
            subst asked
            obtain ⟨response, member, readout⟩ := (answer_some first value).mp answered
            exact (compatible response member).trans readout
        | succ index => exact restCompatible index asked value found answered
      · rintro ⟨original, compatible⟩
        refine ⟨⟨original, ?_⟩, ?_⟩
        · intro response member
          exact compatible 0 question response.2.1.bit rfl
            ((answer_some first _).mpr ⟨response, member, rfl⟩)
        · intro index asked value found answered
          exact compatible (index + 1) asked value found answered

end Campaign

abbrev coreExperimentRemaining {state : CoreState} {question : Question} {budget session provider client : Nat}
    (experiment : CoreExperiment state question budget session provider client) : Nat :=
  experiment.assay.remaining

def coreExperimentSpent {state : CoreState} {question : Question} {budget session provider client : Nat}
    (experiment : CoreExperiment state question budget session provider client) : Nat :=
  coreCommandPrice (question.commands.take budget) + experiment.assay.spent

theorem coreExperimentLedger {state : CoreState} {question : Question} {budget session provider client : Nat}
    (experiment : CoreExperiment state question budget session provider client) :
    budget = coreExperimentRemaining experiment + coreExperimentSpent experiment := by
  have probeLedger := experiment.probe.ledger
  have assayLedger := experiment.assay.ledger
  unfold coreExperimentSpent
  rw [coreCommandPrice_exact]
  change budget = experiment.assay.remaining +
    ((question.commands.take budget).length + experiment.assay.spent)
  omega

def corePrediction (mode : Mode) (question : Question) : Bool :=
  coreObservation (coreView (initial mode)) question

theorem corePrediction_agrees (mode : Mode) (question : Question) :
    corePrediction mode question = prediction mode question :=
  compression_observation (initial mode) question

inductive CoreCampaign (state : CoreState) : Nat → List Question → Type where
  | nil (budget : Nat) : CoreCampaign state budget []
  | cons {budget session provider client : Nat} {question : Question} {questions : List Question}
      (first : CoreExperiment state question budget session provider client)
      (rest : CoreCampaign state (coreExperimentRemaining first) questions) :
        CoreCampaign state budget (question :: questions)

namespace CoreCampaign

variable {state : CoreState}

def remaining : {budget : Nat} → {questions : List Question} → CoreCampaign state budget questions → Nat
  | _, _, .nil budget => budget
  | _, _, .cons _ rest => remaining rest

def spent : {budget : Nat} → {questions : List Question} → CoreCampaign state budget questions → Nat
  | _, _, .nil _ => 0
  | _, _, .cons first rest => coreExperimentSpent first + spent rest

theorem ledger {budget : Nat} {questions : List Question} (campaign : CoreCampaign state budget questions) :
    budget = campaign.remaining + campaign.spent := by
  induction campaign with
  | nil _ => rfl
  | cons first rest inductionHypothesis =>
      have firstLedger := coreExperimentLedger first
      change _ = rest.remaining + (coreExperimentSpent first + rest.spent)
      omega

noncomputable def answerAt : {budget : Nat} → {questions : List Question} →
    CoreCampaign state budget questions → Nat → Option Bool
  | _, _, .nil _, _ => none
  | _, _, .cons first _, 0 => packetAnswer first.assay.responses
  | _, _, .cons _ rest, index + 1 => answerAt rest index

noncomputable def describe {budget : Nat} {questions : List Question}
    (campaign : CoreCampaign state budget questions) : View Nat Bool := viewOfAnswers campaign.answerAt

def learn : {budget : Nat} → {questions : List Question} →
    CoreCampaign state budget questions → Finset Mode → Finset Mode
  | _, _, .nil _, candidates => candidates
  | _, question :: _, .cons first rest, candidates =>
      learn rest (revise corePrediction candidates question first.assay.responses)

def reindexBudget {first second : Nat} {questions : List Question} (same : first = second)
    (campaign : CoreCampaign state first questions) : CoreCampaign state second questions := same ▸ campaign

theorem reindexBudget_remaining {first second : Nat} {questions : List Question} (same : first = second)
    (campaign : CoreCampaign state first questions) :
    (reindexBudget same campaign).remaining = campaign.remaining := by cases same; rfl

theorem reindexBudget_spent {first second : Nat} {questions : List Question} (same : first = second)
    (campaign : CoreCampaign state first questions) :
    (reindexBudget same campaign).spent = campaign.spent := by cases same; rfl

theorem reindexBudget_answerAt {first second : Nat} {questions : List Question} (same : first = second)
    (campaign : CoreCampaign state first questions) (index : Nat) :
    (reindexBudget same campaign).answerAt index = campaign.answerAt index := by cases same; rfl

theorem reindexBudget_learn {first second : Nat} {questions : List Question} (same : first = second)
    (campaign : CoreCampaign state first questions) (candidates : Finset Mode) :
    (reindexBudget same campaign).learn candidates = campaign.learn candidates := by cases same; rfl

end CoreCampaign

namespace Campaign

variable {state : State}

def compress : {budget : Nat} → {questions : List Question} →
    Campaign state budget questions → CoreCampaign (coreView state) budget questions
  | _, _, .nil budget => .nil budget
  | _, _, .cons first rest => .cons (compressExperiment first)
      (CoreCampaign.reindexBudget (compressExperiment_remaining first).symm (compress rest))

theorem compress_remaining {budget : Nat} {questions : List Question}
    (campaign : Campaign state budget questions) : campaign.compress.remaining = campaign.remaining := by
  induction campaign with
  | nil _ => rfl
  | cons first rest inductionHypothesis =>
      change (CoreCampaign.reindexBudget _ rest.compress).remaining = rest.remaining
      rw [CoreCampaign.reindexBudget_remaining, inductionHypothesis]

theorem compress_spent {budget : Nat} {questions : List Question}
    (campaign : Campaign state budget questions) : campaign.compress.spent = campaign.spent := by
  induction campaign with
  | nil _ => rfl
  | cons first rest inductionHypothesis =>
      change coreExperimentSpent (compressExperiment first) +
        (CoreCampaign.reindexBudget _ rest.compress).spent = first.spent + rest.spent
      rw [CoreCampaign.reindexBudget_spent, inductionHypothesis]
      exact congrArg (fun spent => spent + rest.spent) (compressExperiment_spent first)

theorem compress_answerAt {budget : Nat} {questions : List Question}
    (campaign : Campaign state budget questions) (index : Nat) :
    campaign.compress.answerAt index = campaign.answerAt index := by
  induction campaign generalizing index with
  | nil _ => rfl
  | cons first rest inductionHypothesis =>
      cases index with
      | zero =>
          change packetAnswer (compressExperiment first).assay.responses = packetAnswer first.responses
          rw [compressExperiment_responses]
      | succ index =>
          change (CoreCampaign.reindexBudget _ rest.compress).answerAt index = rest.answerAt index
          rw [CoreCampaign.reindexBudget_answerAt, inductionHypothesis]

theorem compress_describe {budget : Nat} {questions : List Question}
    (campaign : Campaign state budget questions) : campaign.compress.describe = campaign.describe := by
  unfold CoreCampaign.describe describe
  congr 1
  funext index
  exact campaign.compress_answerAt index

theorem compress_revision {budget : Nat} {questions : List Question}
    (campaign : Campaign state budget questions) (candidates : Finset Mode) :
    campaign.compress.learn candidates = campaign.learn candidates := by
  have predictionLaw : corePrediction = prediction := by
    funext mode question
    exact corePrediction_agrees mode question
  induction campaign generalizing candidates with
  | nil _ => rfl
  | cons first rest inductionHypothesis =>
      change (CoreCampaign.reindexBudget _ rest.compress).learn
        (revise corePrediction candidates _ (compressExperiment first).assay.responses) = _
      rw [CoreCampaign.reindexBudget_learn, inductionHypothesis,
        compressExperiment_responses, predictionLaw]
      rfl

/-- A passive campaign is specified by the actual question list. -/
def Passive (questions : List Question) : Prop :=
  ∀ question ∈ questions, ∃ commands field, question = passiveQuestion commands field

theorem passive_candidate_survives (mode hypothesis : Mode) {budget : Nat} {questions : List Question}
    (campaign : Campaign (initial mode) budget questions) (passive : Passive questions)
    (candidates : Finset Mode) (initial : hypothesis ∈ candidates) :
    hypothesis ∈ campaign.learn candidates := by
  induction campaign generalizing candidates with
  | nil _ => exact initial
  | @cons budget session provider client question questions first rest inductionHypothesis =>
      have compatible : Compatible prediction hypothesis question first.responses := by
        intro response member
        obtain ⟨commands, field, same⟩ := passive question List.mem_cons_self
        have sound := first.response_sound response member
        rw [sound.2.1, ComplementaryAssay.verdictOf_bit]
        subst question
        cases hypothesis <;> cases mode <;>
          simp only [prediction, passive_observation_eq]
      have retained := (revise_mem prediction candidates question first.responses hypothesis).mpr
        ⟨initial, compatible⟩
      exact inductionHypothesis (fun next member => passive next (List.mem_cons_of_mem question member))
        _ retained

theorem passive_preserves_candidates (mode : Mode) {budget : Nat} {questions : List Question}
    (campaign : Campaign (initial mode) budget questions) (passive : Passive questions)
    (candidates : Finset Mode) : campaign.learn candidates = candidates := by
  apply Finset.ext
  intro hypothesis
  constructor
  · intro retained
    exact (campaign.learn_mem candidates hypothesis).mp retained |>.1
  · exact campaign.passive_candidate_survives mode hypothesis passive candidates

/-- Supplied corresponding passive campaigns can stop at different internal
paths, but equal completion domains earn equality of all public answers. -/
theorem passive_answers_agree (mode other : Mode) {budget otherBudget : Nat} {questions : List Question}
    (campaign : Campaign (initial mode) budget questions)
    (otherCampaign : Campaign (initial other) otherBudget questions)
    (passive : Passive questions)
    (sameCompletion : ∀ index, (∃ value, campaign.answerAt index = some value) ↔
      ∃ value, otherCampaign.answerAt index = some value) :
    campaign.answerAt = otherCampaign.answerAt := by
  have agrees : ∀ {state : State} {budget : Nat} {questions : List Question}
      (campaign : Campaign state budget questions) (index : Nat) (value : Bool),
      campaign.answerAt index = some value →
        ∃ question, questions[index]? = some question ∧ value = observation state question := by
    intro state budget questions campaign index value answered
    induction campaign generalizing index with
    | nil _ => cases answered
    | @cons budget session provider client question questions first rest inductionHypothesis =>
        cases index with
        | zero => exact ⟨question, rfl, PaidWorkspaceDescriptions.answer_agrees first value answered⟩
        | succ index => exact inductionHypothesis index answered
  funext index
  cases firstAnswer : campaign.answerAt index with
  | none =>
      cases secondAnswer : otherCampaign.answerAt index with
      | none => rfl
      | some value =>
          obtain ⟨first, answered⟩ := (sameCompletion index).mpr ⟨value, secondAnswer⟩
          rw [firstAnswer] at answered
          cases answered
  | some value =>
      obtain ⟨otherValue, otherAnswered⟩ := (sameCompletion index).mp ⟨value, firstAnswer⟩
      obtain ⟨question, found, firstObservation⟩ := agrees campaign index value firstAnswer
      obtain ⟨otherQuestion, otherFound, otherObservation⟩ := agrees otherCampaign index otherValue otherAnswered
      have sameQuestion := Option.some.inj (found.symm.trans otherFound)
      subst otherQuestion
      obtain ⟨commands, field, same⟩ := passive question (List.mem_of_getElem? found)
      rw [otherAnswered]
      congr 1
      rw [firstObservation, otherObservation, same]
      cases mode <;> cases other <;> simp only [passive_observation_eq]

end Campaign

/-! ## Funded and underfunded description controls -/

def executedFamily (state : State) (budget session provider client : Nat) : Family state where
  budget _ := budget
  session _ := session
  provider _ := provider
  client _ := client
  experiment question := execute state question budget session provider client

theorem funded_answer_connected :
    (executedFamily (initial .connected) 7 10 20 30).answers separatingQuestion = some true := by
  apply (answer_some _ _).mpr
  refine ⟨(10, ComplementaryAssay.verdictOf true, 30, true), ?_, ?_⟩
  · change (10, ComplementaryAssay.verdictOf true, 30, true) ∈
      (execute (initial .connected) separatingQuestion 7 10 20 30).responses
    rw [execute_responses, if_pos (by decide)]
    rw [separating_execution_answers.1]
    exact Multiset.mem_singleton_self _
  · change (ComplementaryAssay.verdictOf true).bit = true
    exact ComplementaryAssay.verdictOf_bit true

theorem funded_answer_shadow :
    (executedFamily (initial .shadow) 7 10 20 30).answers separatingQuestion = some false := by
  apply (answer_some _ _).mpr
  refine ⟨(10, ComplementaryAssay.verdictOf false, 30, false), ?_, ?_⟩
  · change (10, ComplementaryAssay.verdictOf false, 30, false) ∈
      (execute (initial .shadow) separatingQuestion 7 10 20 30).responses
    rw [execute_responses, if_pos (by decide)]
    rw [separating_execution_answers.2]
    exact Multiset.mem_singleton_self _
  · change (ComplementaryAssay.verdictOf false).bit = false
    exact ComplementaryAssay.verdictOf_bit false

theorem funded_description_separates :
    (executedFamily (initial .connected) 7 10 20 30).describe ≠
      (executedFamily (initial .shadow) 7 10 20 30).describe := by
  intro same
  have firstPresent : separatingQuestion ∈
      (executedFamily (initial .connected) 7 10 20 30).describe.context :=
    ⟨true, funded_answer_connected⟩
  have secondPresent : separatingQuestion ∈
      (executedFamily (initial .shadow) 7 10 20 30).describe.context :=
    ⟨false, funded_answer_shadow⟩
  have equalValues := (le_of_eq same).2 separatingQuestion firstPresent secondPresent
  rw [Family.description_value, Family.description_value,
    separating_execution_answers.1, separating_execution_answers.2] at equalValues
  cases equalValues

theorem short_answer_absent (mode : Mode) :
    (executedFamily (initial mode) 6 10 20 30).answers separatingQuestion = none :=
  (answer_none _).mpr (one_unit_short_has_no_verdict mode)

theorem short_description_absent (mode : Mode) :
    separatingQuestion ∉ (executedFamily (initial mode) 6 10 20 30).describe.context := by
  rintro ⟨value, present⟩
  rw [short_answer_absent] at present
  cases present

theorem short_description_preserves_candidates (mode : Mode) :
    (executedFamily (initial mode) 6 10 20 30).reviseAt separatingQuestion candidates = candidates :=
  one_unit_short_preserves_candidates mode

/-- Snapshots with the same complete observable behavior can still supply
different dependent experiment origins. -/
def countedOrigins (count : Nat) : Σ state : State, Family state :=
  ⟨counted count, executedFamily (counted count) 7 10 20 30⟩

theorem counted_origins_distinct : countedOrigins 0 ≠ countedOrigins 7 := by
  intro same
  have states := congrArg Sigma.fst same
  have counts := congrArg (fun state => state.evidence) states
  change (0 : Nat) = 7 at counts
  omega

theorem counted_origins_same_answer :
    (countedOrigins 0).2.answers separatingQuestion = (countedOrigins 7).2.answers separatingQuestion := by
  exact congrArg packetAnswer counted_receipts_same_answer

end Mettapedia.CogArch.Consciousness.PaidWorkspaceDescriptions
