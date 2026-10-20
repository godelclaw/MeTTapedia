import Mettapedia.Languages.MM0.MeTTa.Session.SessionProof
import Mettapedia.Languages.MM0.MeTTa.Session.SharedService
import Mettapedia.OSLF.Framework.RelationalCompletionTypeSynthesis

/-!
# Executable native observations of submitted MM0 proofs and admissions

The existing supplied-witness checker decides a generated completion type of
the actual retained MeTTa evaluation relation. The type observes the whole
singleton answer, physical table readiness and the earned cache frame.

The service consumer checks ordinary theorem submissions through the actual
shared service with an empty saved prefix. Permission from the pending
specification, declaration formation and the submitted proof are separate
conditions. No existential replacement proof repairs a rejected submission.
The semantic adapter uses the existing operational evaluator; it does not
claim that capability-backed tables fit the finite pattern-language adapter.
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
open Mettapedia.GSLT.Dynamics.RelationalAnswerEvaluation
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis
open Mettapedia.OSLF.Framework.RelationalCompletionTypeSynthesis

structure ProofRequest where
  context : Context
  hypotheses : List Preterm
  witness : ProofWitness
  claim : Preterm

def proofCheck (theory : Theory) (request : ProofRequest) : Bool :=
  request.witness.check theory.termSignature theory.definitionSignature theory.theoremSignature
    request.context request.hypotheses request.claim

/-- The source is actual completion of the already verified MeTTa request,
retaining the full final state and ordered answer list. -/
def proofSource (spaces : Spaces) : RelationalAnswerSource State ProofRequest Atom where
  Evaluates before request after answers :=
    ∃ fuel, run program fuel
      (SessionProof.requestConfiguration before spaces request.context request.hypotheses request.witness request.claim) =
        .complete after answers [] []

def proofObservation (spaces : Spaces) (theory : Theory) (answer : Bool)
    (before : State) (_request : ProofRequest) (after : State) (answers : List Atom) : Prop :=
  answers = [boolean answer] ∧ Ready spaces theory after ∧
    ∃ bound, InferenceCache.Frame spaces.cache (TableAccess.tableValue spaces.terms) bound before after

def proofNativeType (spaces : Spaces) (theory : Theory) (answer : Bool) :
    GSLTNativeType (evaluationGSLT (proofSource spaces)) :=
  completionNativeType (proofSource spaces) (proofObservation spaces theory answer)

/-- This finite computation decides the actual completion type for this
supplied witness. Termination and frames come from the existing checker
execution bridge, not a new proof-search assumption. -/
theorem proofCheck_native_exact (spaces : Spaces) (theory : Theory) (before : State)
    (ready : Ready spaces theory before) (request : ProofRequest) (answer : Bool) :
    proofCheck theory request = answer ↔
      (gsltOSLF (evaluationGSLT (proofSource spaces))).satisfies (S := ())
        (.request before request) (proofNativeType spaces theory answer).pred := by
  change proofCheck theory request = answer ↔
    completesOnly (proofSource spaces) (proofObservation spaces theory answer) (.request before request)
  rw [completesOnly_request_iff]
  obtain ⟨reference, bound, fuel, completed, readyAfter, frame⟩ :=
    SessionProof.sufficient_fuel spaces theory request.context request.hypotheses request.witness request.claim before ready
  have referenceRun := completed 0
  simp only [Nat.add_zero] at referenceRun
  constructor
  · intro checked
    refine ⟨⟨reference, [boolean (proofCheck theory request)], fuel, referenceRun⟩, ?_⟩
    intro after answers evaluated
    obtain ⟨actualFuel, returned⟩ := evaluated
    have same := completed_result_unique program fuel actualFuel _ reference after _ [] [] answers [] []
      referenceRun returned
    rcases same with ⟨rfl, sameAnswers, _⟩
    exact ⟨sameAnswers.symm.trans (congrArg (fun result => [boolean result]) checked), readyAfter, bound, frame⟩
  · rintro ⟨_, readings⟩
    have observed := (readings reference [boolean (proofCheck theory request)] ⟨fuel, referenceRun⟩).1
    simpa [boolean] using observed

theorem rejected_witness_not_accepted (spaces : Spaces) (theory : Theory) (before : State)
    (ready : Ready spaces theory before) (request : ProofRequest)
    (rejected : proofCheck theory request = false) :
    ¬ (gsltOSLF (evaluationGSLT (proofSource spaces))).satisfies (S := ()) (.request before request)
      (proofNativeType spaces theory true).pred := by
  intro accepted
  have checked := (proofCheck_native_exact spaces theory before ready request true).mpr accepted
  rw [rejected] at checked
  cases checked

/-- Logical authority comes from the independently checked declaration history;
physical table readiness alone does not supply that history. -/
theorem proofNative_has_specified_proof (spaces : Spaces) (theory : Theory)
    (specification : List SpecificationEntry) (declarations : List ProofDeclaration)
    (checked : SpecificationAdmission.verify? specification declarations = some theory)
    (before : State) (ready : Ready spaces theory before) (request : ProofRequest)
    (member : (gsltOSLF (evaluationGSLT (proofSource spaces))).satisfies (S := ())
      (.request before request) (proofNativeType spaces theory true).pred) :
    Upstream.Lean3ProofAdmission.Reference.SpecifiedProof
      (Upstream.Lean3Typing.projectRun (declarations.map ProofDeclaration.admission))
      (Upstream.Lean3Typing.Reference.ofContext request.context)
      (Upstream.Lean3ProofAdmission.sourceHypotheses request.hypotheses)
      (Upstream.Lean3Typing.Reference.SExpr.ofKernel request.claim) := by
  apply (Upstream.Lean3ProofAdmission.checked_specification_proof_iff checked
    request.context request.hypotheses request.claim).mpr
  exact ProofWitness.check_sound
    ((proofCheck_native_exact spaces theory before ready request true).mpr member)

structure TheoremSubmission where
  isLocal : Bool
  index : Nat
  declaration : TheoremDecl
  dummies : List Nat
  witness : ProofWitness

def TheoremSubmission.command (submission : TheoremSubmission) : SharedService.Command :=
  ⟨submission.isLocal, submission.index, submission.declaration, submission.dummies, [], submission.witness⟩

/-- State authority is checked independently of witness validity. -/
def submissionCheck (logical : SpecificationAdmission.State) (submission : TheoremSubmission) : Bool :=
  (SpecificationAdmission.pending? logical.pending submission.command.proofDeclaration).isSome &&
    Admission.check logical.theory submission.command.admission

theorem submissionCheck_exact (logical : SpecificationAdmission.State) (submission : TheoremSubmission) :
    submissionCheck logical submission = true ↔
      (∃ remaining, SpecificationAdmission.pending? logical.pending submission.command.proofDeclaration = some remaining) ∧
      SharedProof.Formation logical.theory submission.index submission.declaration submission.dummies ∧
      ProofWitness.Checks logical.theory.termSignature logical.theory.definitionSignature logical.theory.theoremSignature
        (Admission.proofContext submission.declaration submission.dummies)
        submission.declaration.hypotheses submission.witness submission.declaration.conclusion := by
  rw [submissionCheck, Bool.and_eq_true, Option.isSome_iff_exists, Admission.check_iff]
  constructor
  · rintro ⟨permitted, authorized⟩
    cases authorized with
    | theoremDecl fresh statement dummySorts checked => exact ⟨permitted, ⟨fresh, statement, dummySorts⟩, checked⟩
  · rintro ⟨permitted, formed, checked⟩
    exact ⟨permitted, .theoremDecl formed.fresh formed.statement formed.dummySorts checked⟩

theorem submissionCheck_service (spaces : Spaces) (logical : SpecificationAdmission.State) (before : State)
    (ready : Ready spaces logical.theory before) (submission : TheoremSubmission) :
    submissionCheck logical submission = true ↔ SharedService.Accepted spaces logical submission.command ready :=
  (submissionCheck_exact logical submission).trans (SharedService.empty_saved_iff ready rfl).symm

def serviceSource (spaces : Spaces) (logical : SpecificationAdmission.State) :
    RelationalAnswerSource State TheoremSubmission Atom where
  Evaluates before submission after answers :=
    ∃ fuel, run program fuel (SharedService.requestConfiguration before spaces logical submission.command) =
      .complete after answers [] []

def publicationObservation (spaces : Spaces) (logical : SpecificationAdmission.State)
    (_before : State) (submission : TheoremSubmission) (_after : State) (answers : List Atom) : Prop :=
  ∃ remaining, answers = [SpecificationStep.resultValue spaces
    (some (SharedService.admittedState logical submission.command remaining))]

def publicationNativeType (spaces : Spaces) (logical : SpecificationAdmission.State) :
    GSLTNativeType (evaluationGSLT (serviceSource spaces logical)) :=
  completionNativeType (serviceSource spaces logical) (publicationObservation spaces logical)

/-- Native publication requires the precise pending declaration and supplied
proof; table lookup or another proof of the conclusion cannot substitute. -/
theorem submissionCheck_native_exact (spaces : Spaces) (logical : SpecificationAdmission.State)
    (before : State) (input : SharedService.Input spaces logical before) (submission : TheoremSubmission) :
    submissionCheck logical submission = true ↔
      (gsltOSLF (evaluationGSLT (serviceSource spaces logical))).satisfies (S := ())
        (.request before submission) (publicationNativeType spaces logical).pred := by
  rw [submissionCheck_service spaces logical before input.ready submission]
  change SharedService.Accepted spaces logical submission.command input.ready ↔
    completesOnly (serviceSource spaces logical) (publicationObservation spaces logical) (.request before submission)
  rw [completesOnly_request_iff]
  constructor
  · intro accepted
    obtain ⟨reference, remaining, fuel, returned⟩ :=
      (SharedService.accepted_iff_source_advances spaces logical submission.command before input).mp accepted
    refine ⟨⟨reference, _, fuel, returned⟩, ?_⟩
    intro after answers evaluated
    obtain ⟨actualFuel, actualRun⟩ := evaluated
    have same := completed_result_unique program fuel actualFuel _ reference after _ [] [] answers [] [] returned actualRun
    exact ⟨remaining, same.2.1.symm⟩
  · rintro ⟨⟨after, answers, fuel, returned⟩, observed⟩
    obtain ⟨remaining, same⟩ := observed after answers ⟨fuel, returned⟩
    apply (SharedService.accepted_iff_source_advances spaces logical submission.command before input).mpr
    exact ⟨after, remaining, fuel, by simpa only [same] using returned⟩

theorem publication_has_independent_history (spaces : Spaces) (logical : SpecificationAdmission.State)
    (before : State) (input : SharedService.Input spaces logical before) (submission : TheoremSubmission)
    (member : (gsltOSLF (evaluationGSLT (serviceSource spaces logical))).satisfies (S := ())
      (.request before submission) (publicationNativeType spaces logical).pred) :
    ∃ ordinary remaining, SpecificationAdmission.pending? logical.pending submission.command.proofDeclaration = some remaining ∧
      SpecificationAdmission.Step logical
        ⟨.theoremDecl submission.index submission.declaration submission.dummies ordinary, submission.isLocal⟩
        (SharedService.admittedState logical submission.command remaining) :=
  SharedService.Accepted.specification_step input.ready
    ((submissionCheck_service spaces logical before input.ready submission).mp
      ((submissionCheck_native_exact spaces logical before input submission).mpr member))

end Mettapedia.OSLF.NativeTypes.Consumers.MM0Admission
