import Mettapedia.OSLF.NativeTypes.GeneratedLogic.ObservedSystems
import Mettapedia.OSLF.Framework.RelationalAnswerTypeSynthesis
import Mettapedia.OSLF.Framework.RelationalCompletionTypeSynthesis

/-!
# Relational answer evaluation at the front door

A consumer that states its semantics as a relational answer source (a request evaluated from a state to a final state
and an ordered list of answers) has native types generated over the evaluation system: a request steps to each of its
completed runs, and a run steps to each of its answer occurrences. "Some run emits an observed answer" is `◇◇` of the
answer observation, and "the request completes, and every run is observed" is `◇⊤ ∧ □` of the run observation.

When the runs of a request are listed exactly (`RunsOf`, for instance by an exact evaluator of every request,
`Evaluator`), the evaluation of the request unfolds into a finite system of nodes (the request, its runs by position, their answers by position), encoded as closed patterns, with
the answer and run observations declared as relations (`unfolded`). That system is asked through the front door
(`ObservedSystems`):

- **some run emits an observed answer** is the front door's `◇◇(inRelation "answer")` at the request
  (`produces_iff`);
- **the request completes and every run is observed** is the front door's `◇⊤ ∧ □(inRelation "run")` at the request
  (`completes_iff`).
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.GeneratedLogic.RelationalAnswers

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.WellSorted (isObjectPattern isObjectPatternList)
open Mettapedia.GSLT.Dynamics.RelationalAnswerEvaluation
open Mettapedia.OSLF.Framework.RelationalAnswerTypeSynthesis
open Mettapedia.OSLF.Framework.RelationalCompletionTypeSynthesis

/-! ## Nodes of an unfolded evaluation -/

/-- A position as a closed pattern: the vector of that many marks. -/
def positionPattern (position : ℕ) : Pattern := .collection .vec (List.replicate position (.apply "mark" [])) none

/-- The position a pattern names. -/
def patternPosition? : Pattern → Option ℕ
  | .collection .vec elements none => some elements.length
  | _ => none

theorem patternPosition?_positionPattern (position : ℕ) : patternPosition? (positionPattern position) = some position := by
  simp [positionPattern, patternPosition?]

theorem isObjectPatternList_marks : ∀ count, isObjectPatternList (List.replicate count (.apply "mark" [])) = true
  | 0 => rfl
  | count + 1 => by
    simp only [List.replicate_succ, isObjectPatternList, isObjectPattern, Bool.true_and]
    exact isObjectPatternList_marks count

theorem isWellScopedListAt_marks : ∀ count,
    Pattern.isWellScopedListAt 0 (List.replicate count (.apply "mark" [])) = true
  | 0 => rfl
  | count + 1 => by
    simp only [List.replicate_succ, Pattern.isWellScopedListAt, Pattern.isWellScopedAt, Bool.true_and]
    exact isWellScopedListAt_marks count

/-- **A node of an unfolded evaluation**: the request, a run by position, or an answer of a run by position. -/
inductive Node where
  | request
  | run (index : ℕ)
  | answer (index occurrence : ℕ)

namespace Node

def encode : Node → Pattern
  | .request => .apply "request" []
  | .run index => .apply "run" [positionPattern index]
  | .answer index occurrence => .apply "answer" [positionPattern index, positionPattern occurrence]

def decode : Pattern → Option Node
  | .apply "request" [] => some .request
  | .apply "run" [index] => (patternPosition? index).map .run
  | .apply "answer" [index, occurrence] =>
    (patternPosition? index).bind fun index => (patternPosition? occurrence).map (.answer index)
  | _ => none

theorem decode_encode (node : Node) : decode (encode node) = some node := by
  cases node <;> simp [encode, decode, patternPosition?_positionPattern]

theorem state (node : Node) : IsState (encode node) := by
  cases node <;>
    simp [encode, positionPattern, IsState, IsObject, isObjectPattern, isObjectPatternList, Pattern.isWellScopedAt,
      Pattern.isWellScopedListAt, isObjectPatternList_marks, isWellScopedListAt_marks]

end Node

/-! ## The unfolded evaluation -/

universe uState uRequest uAnswer

variable {State : Type uState} {Request : Type uRequest} {Answer : Type uAnswer}
  {source : RelationalAnswerSource State Request Answer}

/-- **The runs of one request, listed exactly.** -/
structure RunsOf (source : RelationalAnswerSource State Request Answer) (initial : State) (request : Request) where
  runs : List (State × List Answer)
  exact : ∀ final answers, source.Evaluates initial request final answers ↔ (final, answers) ∈ runs

/-- **An exact evaluator**: the completed runs of every request, listed. -/
structure Evaluator (source : RelationalAnswerSource State Request Answer) where
  evaluate : State → Request → List (State × List Answer)
  exact : ∀ initial request final answers,
    source.Evaluates initial request final answers ↔ (final, answers) ∈ evaluate initial request

/-- The runs of one request, from an exact evaluator. -/
def Evaluator.runsOf (evaluator : Evaluator source) (initial : State) (request : Request) :
    RunsOf source initial request :=
  ⟨evaluator.evaluate initial request, evaluator.exact initial request⟩

variable {initial : State} {request : Request} (listed : RunsOf source initial request)
  (answerObservation : State → Request → State → Answer → Prop)
  [∀ initial request final answer, Decidable (answerObservation initial request final answer)]
  (runObservation : State → Request → State → List Answer → Prop)
  [∀ initial request final answers, Decidable (runObservation initial request final answers)]

/-- The successors of a node: the runs of the request, and the answers of a run. -/
def successors : Node → List Node
  | .request => (List.range listed.runs.length).map .run
  | .run index =>
    match listed.runs[index]? with
    | some (_, answers) => (List.range answers.length).map (.answer index)
    | none => []
  | .answer _ _ => []

/-- The declared observations: `answer` of answer occurrences, `run` of runs. -/
def observations : String → Node → Bool
  | "answer", .answer index occurrence =>
    match listed.runs[index]? with
    | some (final, answers) =>
      match answers[occurrence]? with
      | some answer => decide (answerObservation initial request final answer)
      | none => false
    | none => false
  | "run", .run index =>
    match listed.runs[index]? with
    | some (final, answers) => decide (runObservation initial request final answers)
    | none => false
  | _, _ => false

/-- **The evaluation of one request, unfolded** into a system of nodes encoded as closed patterns. -/
def unfolded : EncodedSystem Node where
  encode := Node.encode
  decode := Node.decode
  decode_encode := Node.decode_encode
  state := Node.state
  successors := successors listed
  observations := observations listed answerObservation runObservation

/-- Some run emits an observed answer. -/
def producesFormula : Formula 0 := .possibly .any (.possibly .any (.inRelation "answer"))

/-- The request completes, and every run is observed. -/
def completesFormula : Formula 0 := .and (.possibly .any .top) (.necessarily .any (.inRelation "run"))

/-- **Some run emits an observed answer** is the front door's `◇◇(inRelation "answer")` at the request. -/
theorem produces_iff :
    (unfolded listed answerObservation runObservation).observed.reading.sat Env.closed
        producesFormula (Node.encode .request) ↔
      producesAnswerSatisfying source answerObservation (.request initial request) := by
  rw [producesAnswerSatisfying_request_iff, producesFormula]
  change (unfolded listed answerObservation runObservation).observed.reading.sat Env.closed
    (.possibly .any _) ((unfolded listed answerObservation runObservation).encode .request) ↔ _
  rw [EncodedSystem.sat_possibly_encode_iff]
  constructor
  · rintro ⟨next, member, holds⟩
    simp only [unfolded, successors, List.mem_map, List.mem_range] at member
    obtain ⟨index, below, rfl⟩ := member
    rw [EncodedSystem.sat_possibly_encode_iff] at holds
    obtain ⟨next, member, observed⟩ := holds
    rw [EncodedSystem.sat_observe_encode_iff] at observed
    have found := List.getElem?_eq_getElem below
    generalize listed.runs[index] = run at found
    obtain ⟨final, answers⟩ := run
    simp only [unfolded, successors, found, List.mem_map, List.mem_range] at member
    obtain ⟨occurrence, occurrenceBelow, rfl⟩ := member
    simp only [unfolded, observations, found, List.getElem?_eq_getElem occurrenceBelow, decide_eq_true_eq]
      at observed
    exact ⟨final, answers, ⟨occurrence, occurrenceBelow⟩,
      (listed.exact _ _).mpr (List.mem_of_getElem? found), observed⟩
  · rintro ⟨final, answers, occurrence, evaluation, observed⟩
    obtain ⟨index, below, found⟩ := List.getElem_of_mem ((listed.exact _ _).mp evaluation)
    have found? := (List.getElem?_eq_getElem below).trans (congrArg some found)
    refine ⟨.run index, by simp [unfolded, successors, below], ?_⟩
    rw [EncodedSystem.sat_possibly_encode_iff]
    refine ⟨.answer index occurrence, ?_, ?_⟩
    · simp [unfolded, successors, found?]
    · rw [EncodedSystem.sat_observe_encode_iff]
      simp only [unfolded, observations, found?, List.getElem?_eq_getElem occurrence.isLt, decide_eq_true_eq]
      exact observed

/-- **The request completes and every run is observed** is the front door's `◇⊤ ∧ □(inRelation "run")` at the
request. -/
theorem completes_iff :
    (unfolded listed answerObservation runObservation).observed.reading.sat Env.closed
        completesFormula (Node.encode .request) ↔
      completesOnly source runObservation (.request initial request) := by
  rw [completesOnly_request_iff]
  change (unfolded listed answerObservation runObservation).observed.reading.sat Env.closed
      (.possibly .any .top) ((unfolded listed answerObservation runObservation).encode .request) ∧
    (unfolded listed answerObservation runObservation).observed.reading.sat Env.closed
      (.necessarily .any (.inRelation "run"))
      ((unfolded listed answerObservation runObservation).encode .request) ↔ _
  rw [EncodedSystem.sat_possibly_encode_iff, EncodedSystem.sat_necessarily_encode_iff]
  apply and_congr
  · constructor
    · rintro ⟨next, member, -⟩
      simp only [unfolded, successors, List.mem_map, List.mem_range] at member
      obtain ⟨index, below, rfl⟩ := member
      exact ⟨_, _, (listed.exact _ _).mpr (List.getElem_mem below)⟩
    · rintro ⟨final, answers, evaluation⟩
      obtain ⟨index, below, -⟩ := List.getElem_of_mem ((listed.exact _ _).mp evaluation)
      exact ⟨.run index, by simp [unfolded, successors, below], trivial⟩
  · constructor
    · intro every final answers evaluation
      obtain ⟨index, below, found⟩ := List.getElem_of_mem ((listed.exact _ _).mp evaluation)
      have found? := (List.getElem?_eq_getElem below).trans (congrArg some found)
      have observed := every (.run index) (by simp [unfolded, successors, below])
      rw [EncodedSystem.sat_observe_encode_iff] at observed
      simpa only [unfolded, observations, found?, decide_eq_true_eq] using observed
    · intro every next member
      simp only [unfolded, successors, List.mem_map, List.mem_range] at member
      obtain ⟨index, below, rfl⟩ := member
      rw [EncodedSystem.sat_observe_encode_iff]
      have found := List.getElem?_eq_getElem below
      generalize listed.runs[index] = run at found
      obtain ⟨final, answers⟩ := run
      simp only [unfolded, observations, found, decide_eq_true_eq]
      exact every final answers ((listed.exact _ _).mpr (List.mem_of_getElem? found))

end Mettapedia.OSLF.NativeTypes.GeneratedLogic.RelationalAnswers
