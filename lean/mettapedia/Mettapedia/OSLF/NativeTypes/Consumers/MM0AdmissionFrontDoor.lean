import Mettapedia.OSLF.NativeTypes.Consumers.MM0AdmissionControls
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.RelationalAnswerFrontDoor

/-!
# Supplied MM0 proofs through the front door

The supplied-witness check is the completion type of the retained MeTTa evaluation of the checker. The evaluation is
deterministic, so at a fuel where a request completes its runs are listed exactly (`listedAt`), and the request
unfolds into a finite system at the front door (`RelationalAnswers`). From a ready state every run ends ready and within
the cache frame (`observation_on_runs`), so the front door reads the answer list alone.

- **The check returns a Boolean exactly when the front door's `◇⊤ ∧ □(inRelation "run")` holds** at the request, for
  the run observation "the answers are that Boolean" (`proofCheck_iff_frontDoor`).
- **A theorem submission is published exactly when the front door's `◇⊤ ∧ □(inRelation "run")` holds** at the
  submission, for the run observation "the answer is the admitted state with the pending specification's remainder"
  (`submissionCheck_iff_frontDoor`); on actual runs the existential publication observation is that decidable one,
  since the shared service's run pins the remainder (`publication_on_runs`).
- On the controls' theory, the kernel runs the MeTTa checker and the shared service inside the front door: the
  theorem's own witness is accepted and published, and the missing-hypothesis witness is rejected and not published
  (each by a closed region of the request's evaluation).
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Consumers.MM0Admission

open Mettapedia.Languages.MM0
open Kernel
open MeTTa
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.PeTTa
open Eval Effects
open SessionInitialization (Spaces)
open AdmissionChecks (Ready)
open Mettapedia.OSLF.MeTTaIL.Syntax (Pattern)
open Mettapedia.OSLF.NativeTypes.GeneratedLogic
open Mettapedia.OSLF.NativeTypes.GeneratedLogic.RelationalAnswers

/-- The completed run of a proof request at a fuel. -/
def runsAt (spaces : Spaces) (before : State) (request : ProofRequest) (fuel : Nat) : List (State × List Atom) :=
  match run program fuel
      (SessionProof.requestConfiguration before spaces request.context request.hypotheses request.witness
        request.claim) with
  | .complete after answers [] [] => [(after, answers)]
  | _ => []

/-- **The runs of a proof request, listed exactly** at a fuel where it completes: the evaluation is deterministic, so
every completion at any fuel is this one. -/
def listedAt (spaces : Spaces) (before : State) (request : ProofRequest) (fuel : Nat)
    (completes : (runsAt spaces before request fuel).length = 1) : RunsOf (proofSource spaces) before request where
  runs := runsAt spaces before request fuel
  exact final answers := by
    unfold runsAt at completes ⊢
    split at completes
    · rename_i after answers' returned
      constructor
      · rintro ⟨actualFuel, actualRun⟩
        obtain ⟨rfl, rfl, -⟩ :=
          completed_result_unique program fuel actualFuel _ after final answers' [] [] answers [] [] returned actualRun
        exact List.mem_singleton_self _
      · intro member
        simp only [List.mem_singleton, Prod.mk.injEq] at member
        obtain ⟨rfl, rfl⟩ := member
        exact ⟨fuel, returned⟩
    · simp at completes

/-- The front door reads the answer Boolean: an answer is it, and a run answers it alone. -/
def isAnswer (answer : Bool) (_ : State) (_ : ProofRequest) (_ : State) (atom : Atom) : Prop := atom = boolean answer

def answersOnly (answer : Bool) (_ : State) (_ : ProofRequest) (_ : State) (answers : List Atom) : Prop :=
  answers = [boolean answer]

instance (answer : Bool) (before : State) (request : ProofRequest) (after : State) (atom : Atom) :
    Decidable (isAnswer answer before request after atom) := by
  unfold isAnswer
  infer_instance

instance (answer : Bool) (before : State) (request : ProofRequest) (after : State) (answers : List Atom) :
    Decidable (answersOnly answer before request after answers) := by
  unfold answersOnly
  infer_instance

/-- **On the request's actual runs the completion observation is the answer list alone**: from a ready state, every
run ends ready and within the cache frame. -/
theorem observation_on_runs (spaces : Spaces) (theory : Theory) (before : State) (ready : Ready spaces theory before)
    (request : ProofRequest) (answer : Bool) {after : State} {answers : List Atom}
    (evaluated : (proofSource spaces).Evaluates before request after answers) :
    proofObservation spaces theory answer before request after answers ↔
      answersOnly answer before request after answers := by
  obtain ⟨reference, bound, fuel, completed, readyAfter, frame⟩ :=
    SessionProof.sufficient_fuel spaces theory request.context request.hypotheses request.witness request.claim
      before ready
  have referenceRun := completed 0
  simp only [Nat.add_zero] at referenceRun
  obtain ⟨actualFuel, returned⟩ := evaluated
  obtain ⟨rfl, -, -⟩ :=
    completed_result_unique program fuel actualFuel _ reference after _ [] [] answers [] [] referenceRun returned
  exact ⟨fun observed => observed.1, fun same => ⟨same, readyAfter, bound, frame⟩⟩

/-- The proof request unfolded at the front door, along an exact listing of its runs. -/
def system (spaces : Spaces) (before : State) (request : ProofRequest) (answer : Bool)
    (listed : RunsOf (proofSource spaces) before request) : EncodedSystem Node :=
  unfolded listed (isAnswer answer) (answersOnly answer)

/-- **The supplied-witness check is the front door's native type** `◇⊤ ∧ □(inRelation "run")` at the request: it
returns the Boolean exactly when the request completes and every run answers it alone. -/
theorem proofCheck_iff_frontDoor (spaces : Spaces) (theory : Theory) (before : State)
    (ready : Ready spaces theory before) (request : ProofRequest) (answer : Bool)
    (listed : RunsOf (proofSource spaces) before request) :
    proofCheck theory request = answer ↔
      (system spaces before request answer listed).observed.reading.sat Env.closed completesFormula
        (Node.encode .request) := by
  refine (proofCheck_native_exact spaces theory before ready request answer).trans ?_
  refine Iff.trans ?_ (completes_iff listed (isAnswer answer) (answersOnly answer)).symm
  change Mettapedia.OSLF.Framework.RelationalCompletionTypeSynthesis.completesOnly (proofSource spaces)
      (proofObservation spaces theory answer) (.request before request) ↔ _
  rw [Mettapedia.OSLF.Framework.RelationalCompletionTypeSynthesis.completesOnly_request_iff,
    Mettapedia.OSLF.Framework.RelationalCompletionTypeSynthesis.completesOnly_request_iff]
  refine and_congr Iff.rfl ⟨fun every after answers evaluated => ?_, fun every after answers evaluated => ?_⟩
  · exact (observation_on_runs spaces theory before ready request answer evaluated).mp (every after answers evaluated)
  · exact (observation_on_runs spaces theory before ready request answer evaluated).mpr (every after answers evaluated)

/-! ## Theorem submissions through the shared service -/

/-- The completed run of a theorem submission at a fuel. -/
def serviceRunsAt (spaces : Spaces) (logical : SpecificationAdmission.State) (before : State)
    (submission : TheoremSubmission) (fuel : Nat) : List (State × List Atom) :=
  match run program fuel (SharedService.requestConfiguration before spaces logical submission.command) with
  | .complete after answers [] [] => [(after, answers)]
  | _ => []

/-- **The runs of a submission, listed exactly** at a fuel where it completes. -/
def serviceListedAt (spaces : Spaces) (logical : SpecificationAdmission.State) (before : State)
    (submission : TheoremSubmission) (fuel : Nat)
    (completes : (serviceRunsAt spaces logical before submission fuel).length = 1) :
    RunsOf (serviceSource spaces logical) before submission where
  runs := serviceRunsAt spaces logical before submission fuel
  exact final answers := by
    unfold serviceRunsAt at completes ⊢
    split at completes
    · rename_i after answers' returned
      constructor
      · rintro ⟨actualFuel, actualRun⟩
        obtain ⟨rfl, rfl, -⟩ :=
          completed_result_unique program fuel actualFuel _ after final answers' [] [] answers [] [] returned actualRun
        exact List.mem_singleton_self _
      · intro member
        simp only [List.mem_singleton, Prod.mk.injEq] at member
        obtain ⟨rfl, rfl⟩ := member
        exact ⟨fuel, returned⟩
    · simp at completes

/-- The front door reads publication: the answer is the admitted state with the pending specification's remainder. -/
def publishes (spaces : Spaces) (logical : SpecificationAdmission.State) (_ : State) (submission : TheoremSubmission)
    (_ : State) (answers : List Atom) : Prop :=
  match SpecificationAdmission.pending? logical.pending submission.command.proofDeclaration with
  | some remaining =>
    answers = [SpecificationStep.resultValue spaces (some (SharedService.admittedState logical submission.command remaining))]
  | none => False

instance (spaces : Spaces) (logical : SpecificationAdmission.State) (before : State) (submission : TheoremSubmission)
    (after : State) (answers : List Atom) : Decidable (publishes spaces logical before submission after answers) := by
  unfold publishes
  split <;> infer_instance

/-- An answer is the publication. -/
def publication (spaces : Spaces) (logical : SpecificationAdmission.State) (before : State)
    (submission : TheoremSubmission) (after : State) (atom : Atom) : Prop :=
  publishes spaces logical before submission after [atom]

instance (spaces : Spaces) (logical : SpecificationAdmission.State) (before : State) (submission : TheoremSubmission)
    (after : State) (atom : Atom) : Decidable (publication spaces logical before submission after atom) := by
  unfold publication
  infer_instance

/-- **On the submission's actual runs the publication observation is the decidable one.** -/
theorem publication_on_runs (spaces : Spaces) (logical : SpecificationAdmission.State) (before : State)
    (input : SharedService.Input spaces logical before) (submission : TheoremSubmission) {after : State}
    {answers : List Atom} (evaluated : (serviceSource spaces logical).Evaluates before submission after answers) :
    publicationObservation spaces logical before submission after answers ↔
      publishes spaces logical before submission after answers := by
  constructor
  · rintro ⟨remaining, rfl⟩
    obtain ⟨fuel, returned⟩ := evaluated
    have pending := ((SharedService.source_advances_iff spaces logical submission.command remaining before input).mp
      ⟨after, fuel, returned⟩).1
    simp only [publishes, pending]
  · intro published
    unfold publishes at published
    split at published
    · rename_i remaining _
      exact ⟨remaining, published⟩
    · exact published.elim

/-- The submission unfolded at the front door, along an exact listing of its runs. -/
def serviceSystem (spaces : Spaces) (logical : SpecificationAdmission.State) (before : State)
    (submission : TheoremSubmission) (listed : RunsOf (serviceSource spaces logical) before submission) :
    EncodedSystem Node :=
  unfolded listed (publication spaces logical) (publishes spaces logical)

/-- **The submission check is the front door's `◇⊤ ∧ □(inRelation "run")`** at the submission: it accepts exactly
when the submission completes and every run publishes. -/
theorem submissionCheck_iff_frontDoor (spaces : Spaces) (logical : SpecificationAdmission.State) (before : State)
    (input : SharedService.Input spaces logical before) (submission : TheoremSubmission)
    (listed : RunsOf (serviceSource spaces logical) before submission) :
    submissionCheck logical submission = true ↔
      (serviceSystem spaces logical before submission listed).observed.reading.sat Env.closed completesFormula
        (Node.encode .request) := by
  refine (submissionCheck_native_exact spaces logical before input submission).trans ?_
  refine Iff.trans ?_ (completes_iff listed (publication spaces logical) (publishes spaces logical)).symm
  change Mettapedia.OSLF.Framework.RelationalCompletionTypeSynthesis.completesOnly (serviceSource spaces logical)
      (publicationObservation spaces logical) (.request before submission) ↔ _
  rw [Mettapedia.OSLF.Framework.RelationalCompletionTypeSynthesis.completesOnly_request_iff,
    Mettapedia.OSLF.Framework.RelationalCompletionTypeSynthesis.completesOnly_request_iff]
  refine and_congr Iff.rfl ⟨fun every after answers evaluated => ?_, fun every after answers evaluated => ?_⟩
  · exact (publication_on_runs spaces logical before input submission evaluated).mp (every after answers evaluated)
  · exact (publication_on_runs spaces logical before input submission evaluated).mpr (every after answers evaluated)

namespace Controls

theorem good_completes : (runsAt spaces initial goodProof 10000).length = 1 := by decide +kernel

def goodSystem (answer : Bool) : EncodedSystem Node :=
  system spaces initial goodProof answer (listedAt spaces initial goodProof 10000 good_completes)

theorem good_answer :
    ask (goodSystem true).observed.env [] systemLanguage 2 completesFormula (Node.encode .request) none 4 =
      .proved (.closedRegion 4) := by
  decide +kernel

/-- **The theorem's witness is accepted**, decided by the front door on the MeTTa checker's own run. -/
theorem good_accepted : proofCheck declarations goodProof = true :=
  (proofCheck_iff_frontDoor spaces declarations initial input.ready goodProof true _).mpr (ask_proved good_answer)

theorem bad_completes : (runsAt spaces initial badProof 10000).length = 1 := by decide +kernel

def badSystem (answer : Bool) : EncodedSystem Node :=
  system spaces initial badProof answer (listedAt spaces initial badProof 10000 bad_completes)

theorem bad_not_true_answer :
    ask (badSystem true).observed.env [] systemLanguage 2 completesFormula (Node.encode .request) none 4 =
      .refuted (.closedRegion 4) := by
  decide +kernel

theorem bad_false_answer :
    ask (badSystem false).observed.env [] systemLanguage 2 completesFormula (Node.encode .request) none 4 =
      .proved (.closedRegion 4) := by
  decide +kernel

/-- **The missing-hypothesis witness is rejected**: its run answers `false`, and not `true`. -/
theorem bad_rejected : proofCheck declarations badProof = false :=
  (proofCheck_iff_frontDoor spaces declarations initial input.ready badProof false _).mpr (ask_proved bad_false_answer)

theorem bad_not_accepted : proofCheck declarations badProof ≠ true := fun accepted =>
  ask_refuted bad_not_true_answer
    ((proofCheck_iff_frontDoor spaces declarations initial input.ready badProof true _).mp accepted)

theorem submission_completes : (serviceRunsAt spaces logical initial submission 5000).length = 1 := by decide +kernel

def serviceAnswer (submitted : TheoremSubmission) (completes : (serviceRunsAt spaces logical initial submitted 5000).length = 1)
    : Answer :=
  ask (serviceSystem spaces logical initial submitted (serviceListedAt spaces logical initial submitted 5000 completes)).observed.env
    [] systemLanguage 2 completesFormula (Node.encode .request) none 4

theorem submission_answer : serviceAnswer submission submission_completes = .proved (.closedRegion 4) := by
  decide +kernel

/-- **The pending theorem with its witness is published**, decided by the front door on the shared service's run. -/
theorem submission_published : submissionCheck logical submission = true :=
  (submissionCheck_iff_frontDoor spaces logical initial input submission _).mpr (ask_proved submission_answer)

theorem bad_submission_completes : (serviceRunsAt spaces logical initial badSubmission 5000).length = 1 := by
  decide +kernel

theorem bad_submission_answer : serviceAnswer badSubmission bad_submission_completes = .refuted (.closedRegion 4) := by
  decide +kernel

/-- **The missing-hypothesis witness is not published.** -/
theorem bad_submission_rejected : submissionCheck logical badSubmission = false := by
  cases checked : submissionCheck logical badSubmission with
  | false => rfl
  | true =>
    exact absurd ((submissionCheck_iff_frontDoor spaces logical initial input badSubmission _).mp checked)
      (ask_refuted bad_submission_answer)

end Controls

end Mettapedia.OSLF.NativeTypes.Consumers.MM0Admission
