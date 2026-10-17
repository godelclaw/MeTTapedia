import Mettapedia.OSLF.Syntax.RhoQuoteSafeCommComparison
import Mettapedia.OSLF.Syntax.RhoPayloadExecutorComparison
import Mettapedia.Languages.MeTTa.PrimeComparisons.Rho.ScopedRepresentation
import Mettapedia.GSLT.LanguageDef.SemanticServiceInvocation

/-!
# Services for the declared scoped rho profile

The declaration package, source context and source sort fix each request
interface. Admission reads actual native constructor syntax and compares its
literal context, type and re-encoding. It is a decision of this selected
source image, rather than a decision of arbitrary native type inhabitation.

The intensional face is the existing declaration-backed native judgment.
The operational face selects directed COMM/Drop steps in parallel contexts.
The extensional observations are the independently stated structural
relation and scoped source events. The existing embedding theorems compare
these faces. No ambient set foundation or global conversion policy is chosen.

Equation packets and native execution use distinct existing service faces.
This module has no external byte parser or executed resource bound.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PrimeComparisons.Rho.ScopedServices

open Mettapedia.OSLF.Binding RhoSchema
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation
open Mettapedia.GSLT.LanguageDef
open SemanticService
open SemanticEvidence KernelAuthority
open ScopedRepresentation ScopedRepresentation.DeclarationProfile
open ScopedRepresentation.Operations (NativeTerm)

/-- A request retains the actual native telescope and proposed native type. -/
structure TermRequest (n : Nat) where
  context : Tower.Ctx n
  term : NativeTerm n
  type : NativeTerm n

/-- Compare a native telescope with the complete fixed rho source context. -/
def contextMatches : (source : Mettapedia.OSLF.Binding.Ctx sig) →
    Tower.Ctx source.length → Bool
  | [], .nil => true
  | sort :: source, .snoc context type =>
      contextMatches source context && decide (type = BindingSignatureEmbedding.sortType names sort)

theorem contextMatches_exact : ∀ (source : Mettapedia.OSLF.Binding.Ctx sig)
    (context : Tower.Ctx source.length),
    contextMatches source context = true ↔ context = BindingSignatureEmbedding.context names source
  | [], .nil => by simp [contextMatches, BindingSignatureEmbedding.context]
  | sort :: source, .snoc context type => by
      change (contextMatches source context &&
        decide (type = BindingSignatureEmbedding.sortType names sort)) = true ↔ _
      simp only [Bool.and_eq_true, decide_eq_true_eq, contextMatches_exact source context,
        BindingSignatureEmbedding.context, Ctx.snoc.injEq]

def sourceRequest {context : Mettapedia.OSLF.Binding.Ctx sig} {sort : Srt}
    (term : Term sig context sort) : TermRequest context.length where
  context := BindingSignatureEmbedding.context names context
  term := Inversion.E term
  type := BindingSignatureEmbedding.sortType names sort

/-- Admission is specified by the authored grammar and literal request
metadata independently of the executable readback. -/
def Admitted (context : Mettapedia.OSLF.Binding.Ctx sig) (sort : Srt)
    (request : TermRequest context.length) : Prop :=
  request.context = BindingSignatureEmbedding.context names context ∧
  request.type = BindingSignatureEmbedding.sortType names sort ∧
  ∃ source : Term sig context sort, Inversion.E source = request.term

def admit? (context : Mettapedia.OSLF.Binding.Ctx sig) (sort : Srt)
    (request : TermRequest context.length) : Option (Term sig context sort) :=
  if contextMatches context request.context = true ∧
      request.type = BindingSignatureEmbedding.sortType names sort then
    match readback context sort request.term with
    | some source => if Inversion.E source = request.term then some source else none
    | none => none
  else none

/-- Successful admission recovers the precise literal source term and all
request metadata. The reverse direction covers every complete source term. -/
theorem admit?_exact {context : Mettapedia.OSLF.Binding.Ctx sig} {sort : Srt}
    (request : TermRequest context.length) (source : Term sig context sort) :
    admit? context sort request = some source ↔
      request.context = BindingSignatureEmbedding.context names context ∧
      request.type = BindingSignatureEmbedding.sortType names sort ∧
      Inversion.E source = request.term := by
  constructor
  · intro accepted
    unfold admit? at accepted
    split at accepted
    · rename_i metadata
      cases decoded : readback context sort request.term with
      | none => simp [decoded] at accepted
      | some recovered =>
          simp only [decoded] at accepted
          split at accepted
          · rename_i literal
            cases Option.some.inj accepted
            exact ⟨(contextMatches_exact _ _).mp metadata.1, metadata.2, literal⟩
          · cases accepted
    · cases accepted
  · rintro ⟨contextEqual, typeEqual, literal⟩
    have metadata : contextMatches context request.context = true :=
      (contextMatches_exact _ _).mpr contextEqual
    simp only [admit?, metadata, typeEqual, and_self, ↓reduceIte]
    rw [← literal, readback_encode]
    simp

def checkAdmission (context : Mettapedia.OSLF.Binding.Ctx sig) (sort : Srt)
    (request : TermRequest context.length) : Bool :=
  (admit? context sort request).isSome

theorem checkAdmission_exact {context : Mettapedia.OSLF.Binding.Ctx sig} {sort : Srt}
    (request : TermRequest context.length) :
    checkAdmission context sort request = true ↔ Admitted context sort request := by
  simp only [checkAdmission, Option.isSome_iff_exists, admit?_exact, Admitted]
  constructor
  · rintro ⟨source, contextEqual, typeEqual, literal⟩
    exact ⟨contextEqual, typeEqual, source, literal⟩
  · rintro ⟨contextEqual, typeEqual, source, literal⟩
    exact ⟨source, contextEqual, typeEqual, literal⟩

theorem sourceRequest_admitted {context : Mettapedia.OSLF.Binding.Ctx sig} {sort : Srt}
    (source : Term sig context sort) : Admitted context sort (sourceRequest source) :=
  ⟨rfl, rfl, source, rfl⟩

theorem admission_judgment {context : Mettapedia.OSLF.Binding.Ctx sig} {sort : Srt}
    (request : TermRequest context.length) (admitted : Admitted context sort request) :
    FormationSensitive.Judgment rules request.context request.term request.type := by
  obtain ⟨contextEqual, typeEqual, source, literal⟩ := admitted
  rw [contextEqual, typeEqual, ← literal]
  exact source_judgment source

def admissionTarget (context : Mettapedia.OSLF.Binding.Ctx sig) (sort : Srt) : AdmissionObject where
  Carrier := TermRequest context.length
  Meaning := Admitted context sort

def admissionKernel (context : Mettapedia.OSLF.Binding.Ctx sig) (sort : Srt) :
    Checker.DecisionKernel (TermRequest context.length) (Admitted context sort) where
  decide := checkAdmission context sort
  correct := checkAdmission_exact

def admissionService (context : Mettapedia.OSLF.Binding.Ctx sig) (sort : Srt) :
    SemanticService.Service (admissionTarget context sort) :=
  .directDecision (admissionKernel context sort)

def admissionRequest {context : Mettapedia.OSLF.Binding.Ctx sig} {sort : Srt}
    (request : TermRequest context.length) :
    SemanticServiceInvocation.Request (admissionService context sort) :=
  .directDecision request

theorem admission_invocation_exact {context : Mettapedia.OSLF.Binding.Ctx sig} {sort : Srt}
    (request : TermRequest context.length) :
    (SemanticServiceInvocation.invoke (admissionRequest (context := context) (sort := sort) request)).acceptedValue =
      some request ↔ Admitted context sort request := by
  change (if checkAdmission context sort request then some request else none) =
    some request ↔ _
  rw [← checkAdmission_exact (sort := sort) request]
  cases checkAdmission context sort request <;> simp


/-! ## Native operation selection without source decoding -/

namespace Selection
open ScopedRepresentation.Operations

/-- An address contains only parallel-child choices. The empty address
selects the root; it cannot descend beneath quotation or input. -/
abbrev Address := List Bool

/-- The independent selected-position observation refines the existing
native parallel reduction relation. -/
inductive Step {n : Nat} : Address → NativeTerm n → NativeTerm n → Prop where
  | root {first second} : Root first second → Step [] first second
  | left {path first second} (other : NativeTerm n) : Step path first second →
      Step (false :: path) (parallel first other) (parallel second other)
  | right {path first second} (other : NativeTerm n) : Step path first second →
      Step (true :: path) (parallel other first) (parallel other second)

theorem Step.parallel {n : Nat} {path : Address} {first second : NativeTerm n}
    (step : Step path first second) : ParallelStep first second := by
  induction step with
  | root step => exact .root step
  | left other _ ih => exact .left other ih
  | right other _ ih => exact .right other ih

/-- Inspect only the native constructor spine. Literal head/channel checks
are performed when the regenerated source endpoint is compared below. -/
def rootCandidate? {n : Nat} : NativeTerm n → Option (RootCode n)
  | .app (.app (.const _) (.app (.app (.const _) channel) payload))
      (.app (.app (.const _) _) (.lam body)) =>
      some (.communication channel payload body)
  | .app (.const _) (.app (.const _) payload) => some (.reflection payload)
  | _ => none

def rootEndpoints {n : Nat} (code : RootCode n) : NativeTerm n × NativeTerm n :=
  decodeStep (.root code)

theorem rootEndpoints_sound {n : Nat} (code : RootCode n) :
    Root (rootEndpoints code).1 (rootEndpoints code).2 := by
  cases code with
  | communication channel payload body => exact .communication channel payload body
  | reflection payload => exact .reflection payload

/-- COMM computes native capture-avoiding `inst0`; Drop returns its native
payload. No source term, certificate or proposed result is an input. -/
def executeRoot? {n : Nat} (term : NativeTerm n) : Option (NativeTerm n) :=
  match rootCandidate? term with
  | none => none
  | some code =>
      let endpoints := rootEndpoints code
      if endpoints.1 = term then some endpoints.2 else none

theorem executeRoot_sound {n : Nat} {first second : NativeTerm n}
    (executed : executeRoot? first = some second) : Root first second := by
  unfold executeRoot? at executed
  cases candidate : rootCandidate? first with
  | none => simp [candidate] at executed
  | some code =>
      simp only [candidate] at executed
      split at executed
      · rename_i same
        have target := Option.some.inj executed
        have root := rootEndpoints_sound code
        simpa only [same, target] using root
      · cases executed

theorem executeRoot_complete {n : Nat} {first second : NativeTerm n}
    (step : Root first second) : executeRoot? first = some second := by
  cases step with
  | communication channel payload body =>
      simp [executeRoot?, rootCandidate?, rootEndpoints, decodeStep, parallel, output, input]
  | reflection payload =>
      simp [executeRoot?, rootCandidate?, rootEndpoints, decodeStep, drop, quote]

def parallelView? {n : Nat} : NativeTerm n → Option (NativeTerm n × NativeTerm n)
  | .app (.app (.const head) first) second =>
      if head = parallelName then some (first, second) else none
  | _ => none

theorem parallelView_exact {n : Nat} (term first second : NativeTerm n) :
    parallelView? term = some (first, second) ↔ term = parallel first second := by
  cases term <;> simp [parallelView?, parallel]
  case app function argument =>
    cases function <;> simp
    case app function value =>
      cases function <;> simp
      case const head => exact and_assoc.symm

def executeAt? {n : Nat} : Address → NativeTerm n → Option (NativeTerm n)
  | [], term => executeRoot? term
  | side :: path, term =>
      match parallelView? term with
      | none => none
      | some (first, second) =>
          if side then (executeAt? path second).map (parallel first)
          else (executeAt? path first).map (fun next => parallel next second)

theorem executeAt_sound {n : Nat} (path : Address) (first second : NativeTerm n)
    (executed : executeAt? path first = some second) : Step path first second := by
  induction path generalizing first second with
  | nil => exact .root (executeRoot_sound executed)
  | cons side path ih =>
      cases view : parallelView? first with
      | none => simp [executeAt?, view] at executed
      | some endpoints =>
          obtain ⟨left, right⟩ := endpoints
          have source := (parallelView_exact first left right).mp view
          cases side with
          | false =>
              cases next : executeAt? path left with
              | none => simp [executeAt?, view, next] at executed
              | some target =>
                  simp only [executeAt?, view, Bool.false_eq_true, ↓reduceIte,
                    next, Option.map_some] at executed
                  have targetEqual := Option.some.inj executed
                  rw [← targetEqual, source]
                  exact .left right (ih left target next)
          | true =>
              cases next : executeAt? path right with
              | none => simp [executeAt?, view, next] at executed
              | some target =>
                  simp only [executeAt?, view, ↓reduceIte, next, Option.map_some] at executed
                  have targetEqual := Option.some.inj executed
                  rw [← targetEqual, source]
                  exact .right left (ih right target next)

theorem executeAt_complete {n : Nat} {path : Address} {first second : NativeTerm n}
    (step : Step path first second) : executeAt? path first = some second := by
  induction step with
  | root step => exact executeRoot_complete step
  | left other _ ih => simp [executeAt?, parallelView?, parallel, ih]
  | right other _ ih => simp [executeAt?, parallelView?, parallel, ih]

theorem executeAt_exact {n : Nat} (path : Address) (first second : NativeTerm n) :
    executeAt? path first = some second ↔ Step path first second :=
  ⟨executeAt_sound path first second, executeAt_complete⟩

/-- Every original native parallel step has a finite address. The executor
is complete over addresses without committing to a scheduling order. -/
theorem parallel_iff_execution {n : Nat} (first second : NativeTerm n) :
    ParallelStep first second ↔ ∃ path, executeAt? path first = some second := by
  constructor
  · intro step
    induction step with
    | root root => exact ⟨[], executeRoot_complete root⟩
    | left other _ ih =>
        obtain ⟨path, executed⟩ := ih
        exact ⟨false :: path, by simp [executeAt?, parallelView?, parallel, executed]⟩
    | right other _ ih =>
        obtain ⟨path, executed⟩ := ih
        exact ⟨true :: path, by simp [executeAt?, parallelView?, parallel, executed]⟩
  · rintro ⟨path, executed⟩
    exact (executeAt_sound path first second executed).parallel

end Selection


/-! ## Equation evidence retains both admitted native endpoints -/

abbrev EquationRequest (n : Nat) := TermRequest n × TermRequest n

def EquationMeaning (context : Mettapedia.OSLF.Binding.Ctx sig) (sort : Srt)
    (request : EquationRequest context.length) : Prop :=
  Admitted context sort request.1 ∧ Admitted context sort request.2 ∧
    Conversion.Structural context sort request.1.term request.2.term

def equationTarget (context : Mettapedia.OSLF.Binding.Ctx sig) (sort : Srt) : AdmissionObject where
  Carrier := EquationRequest context.length
  Meaning := EquationMeaning context sort

def checkEquation (context : Mettapedia.OSLF.Binding.Ctx sig) (sort : Srt)
    (request : EquationRequest context.length) (proof : EquationEvidence context sort) : Bool :=
  checkAdmission context sort request.1 && checkAdmission context sort request.2 &&
    checkNativeEquation proof request.1.term request.2.term

def equationChecker (context : Mettapedia.OSLF.Binding.Ctx sig) (sort : Srt) :
    Checker (EquationRequest context.length) (EquationEvidence context sort) where
  check := checkEquation context sort

theorem equationChecker_sound {context : Mettapedia.OSLF.Binding.Ctx sig} {sort : Srt}
    (request : EquationRequest context.length) (proof : EquationEvidence context sort)
    (accepted : checkEquation context sort request proof = true) : EquationMeaning context sort request := by
  simp only [checkEquation, Bool.and_eq_true] at accepted
  obtain ⟨⟨firstCheck, secondCheck⟩, equationCheck⟩ := accepted
  have firstAdmission := (checkAdmission_exact (sort := sort) request.1).mp firstCheck
  have secondAdmission := (checkAdmission_exact (sort := sort) request.2).mp secondCheck
  refine ⟨firstAdmission, secondAdmission, ?_⟩
  obtain ⟨_, _, first, firstLiteral⟩ := firstAdmission
  obtain ⟨_, _, second, secondLiteral⟩ := secondAdmission
  rw [← firstLiteral, ← secondLiteral] at equationCheck ⊢
  exact (Conversion.structural_iff_native_evidence first second).mpr ⟨proof, equationCheck⟩

theorem equationChecker_complete {context : Mettapedia.OSLF.Binding.Ctx sig} {sort : Srt}
    (request : EquationRequest context.length) (meaning : EquationMeaning context sort request) :
    ∃ proof : EquationEvidence context sort, checkEquation context sort request proof = true := by
  obtain ⟨firstAdmission, secondAdmission, equation⟩ := meaning
  have firstCheck := (checkAdmission_exact (sort := sort) request.1).mpr firstAdmission
  have secondCheck := (checkAdmission_exact (sort := sort) request.2).mpr secondAdmission
  obtain ⟨_, _, first, firstLiteral⟩ := firstAdmission
  obtain ⟨_, _, second, secondLiteral⟩ := secondAdmission
  rw [← firstLiteral, ← secondLiteral] at equation
  obtain ⟨proof, accepted⟩ := (Conversion.structural_iff_native_evidence first second).mp equation
  refine ⟨proof, ?_⟩
  simp only [checkEquation, firstCheck, secondCheck, Bool.and_self, Bool.true_and]
  rw [← firstLiteral, ← secondLiteral]
  exact accepted

theorem equationAuthority (context : Mettapedia.OSLF.Binding.Ctx sig) (sort : Srt) :
    (equationChecker context sort).Authority (EquationMeaning context sort) where
  sound := equationChecker_sound
  complete := equationChecker_complete

def equationService (context : Mettapedia.OSLF.Binding.Ctx sig) (sort : Srt) :
    SemanticService.Service (equationTarget context sort) :=
  .certificateBoundary (EquationEvidence context sort) (equationChecker context sort)
    (equationAuthority context sort)

def equationRequest {context : Mettapedia.OSLF.Binding.Ctx sig} {sort : Srt}
    (request : EquationRequest context.length) (proof : EquationEvidence context sort) :
    SemanticServiceInvocation.Request (equationService context sort) :=
  .certificateBoundary request proof

theorem equation_invocation_exact {context : Mettapedia.OSLF.Binding.Ctx sig} {sort : Srt}
    (request : EquationRequest context.length) (proof : EquationEvidence context sort) :
    (SemanticServiceInvocation.invoke (equationRequest request proof)).acceptedValue = some request ↔
      checkEquation context sort request proof = true := by
  change (if checkEquation context sort request proof then some request else none) = some request ↔ _
  cases checkEquation context sort request proof <;> simp

/-- Evidence existence agrees with the original complete scoped source
relation. A supplied packet is still checked at both literal endpoints. -/
theorem source_equation_iff_service {context : Mettapedia.OSLF.Binding.Ctx sig} {sort : Srt}
    (first second : Term sig context sort) :
    EqClosure rhoSourceE first second ↔
      ∃ proof : EquationEvidence context sort,
        (SemanticServiceInvocation.invoke
          (equationRequest (sourceRequest first, sourceRequest second) proof)).acceptedValue =
            some (sourceRequest first, sourceRequest second) := by
  rw [Conversion.source_equation_iff_structural]
  constructor
  · intro equation
    obtain ⟨proof, accepted⟩ := equationChecker_complete
      (sourceRequest first, sourceRequest second)
      ⟨sourceRequest_admitted first, sourceRequest_admitted second, equation⟩
    exact ⟨proof, (equation_invocation_exact _ _).mpr accepted⟩
  · rintro ⟨proof, accepted⟩
    exact (equationChecker_sound _ proof ((equation_invocation_exact _ _).mp accepted)).2.2

/-! ## Actual admitted native operation invocation -/

structure OperationRequest (context : Mettapedia.OSLF.Binding.Ctx sig) where
  argument : TermRequest context.length
  address : Selection.Address

def OperationAdmitted {context : Mettapedia.OSLF.Binding.Ctx sig}
    (request : OperationRequest context) : Prop :=
  Admitted context .pr request.argument ∧
    ∃ target, Selection.Step request.address request.argument.term target

def checkOperation {context : Mettapedia.OSLF.Binding.Ctx sig}
    (request : OperationRequest context) : Bool :=
  checkAdmission context .pr request.argument &&
    (Selection.executeAt? request.address request.argument.term).isSome

theorem checkOperation_exact {context : Mettapedia.OSLF.Binding.Ctx sig}
    (request : OperationRequest context) :
    checkOperation request = true ↔ OperationAdmitted request := by
  simp only [checkOperation, Bool.and_eq_true, checkAdmission_exact,
    Option.isSome_iff_exists, Selection.executeAt_exact, OperationAdmitted]

def operationSource (context : Mettapedia.OSLF.Binding.Ctx sig) : AdmissionObject where
  Carrier := OperationRequest context
  Meaning := OperationAdmitted

/-- The reply retains its entire request, including the selected address. -/
abbrev OperationReply (context : Mettapedia.OSLF.Binding.Ctx sig) :=
  OperationRequest context × Option (NativeTerm context.length)

def OperationMeaning {context : Mettapedia.OSLF.Binding.Ctx sig}
    (reply : OperationReply context) : Prop :=
  Admitted context .pr reply.1.argument ∧
    ∃ target, reply.2 = some target ∧ Selection.Step reply.1.address reply.1.argument.term target

def operationTarget (context : Mettapedia.OSLF.Binding.Ctx sig) : AdmissionObject where
  Carrier := OperationReply context
  Meaning := OperationMeaning

def runOperation {context : Mettapedia.OSLF.Binding.Ctx sig}
    (request : OperationRequest context) : OperationReply context :=
  (request, Selection.executeAt? request.address request.argument.term)

/-- Execution uses the original native term and selected address. Its
source admission is a proved property, rather than a correctness callback. -/
def operationArrow (context : Mettapedia.OSLF.Binding.Ctx sig) :
    AdmissionHom (operationSource context) (operationTarget context) where
  run := runOperation
  preserves request admitted := by
    obtain ⟨sourceAdmitted, target, step⟩ := admitted
    exact ⟨sourceAdmitted, target, Selection.executeAt_complete step, step⟩

def operationService (context : Mettapedia.OSLF.Binding.Ctx sig) :
    SemanticService.Service (operationTarget context) :=
  .nativeOperation (operationSource context) (operationArrow context)

def operationRequest {context : Mettapedia.OSLF.Binding.Ctx sig}
    (request : OperationRequest context) :
    SemanticServiceInvocation.Request (operationService context) :=
  .nativeOperation request

/-- Raw operation invocation is possible, but semantic use retains precisely
its independently defined source-admission premise. -/
theorem operation_input_admission_exact {context : Mettapedia.OSLF.Binding.Ctx sig}
    (request : OperationRequest context) :
    SemanticServiceInvocation.InputAdmission (operationRequest request) ↔ OperationAdmitted request :=
  SemanticServiceInvocation.native_operation_input_admission_iff _ _

def admitOperationRequest? {context : Mettapedia.OSLF.Binding.Ctx sig}
    (request : OperationRequest context) :
    Option (SemanticServiceInvocation.Request (operationService context)) :=
  if checkOperation request then some (operationRequest request) else none

theorem admitOperationRequest_exact {context : Mettapedia.OSLF.Binding.Ctx sig}
    (request : OperationRequest context) :
    admitOperationRequest? request = some (operationRequest request) ↔ OperationAdmitted request := by
  simp only [admitOperationRequest?]
  rw [← checkOperation_exact request]
  cases checkOperation request <;> simp

theorem admitted_operation_preserves {context : Mettapedia.OSLF.Binding.Ctx sig}
    (request : OperationRequest context) (admitted : OperationAdmitted request) :
    OperationMeaning (runOperation request) :=
  (operationArrow context).preserves request admitted

/-- Every admitted reply earns both source-event reflection and its actual
native declaration judgment in the unchanged source context and sort. -/
theorem operation_reply_reflects_source {context : Mettapedia.OSLF.Binding.Ctx sig}
    (reply : OperationReply context) (meaning : OperationMeaning reply) :
    ∃ first second : Term sig context Srt.pr,
      Inversion.E first = reply.1.argument.term ∧ reply.2 = some (Inversion.E second) ∧
      Mettapedia.Languages.ProcessCalculi.RhoCalculus.ScopedNativeServices.SourceStep first second ∧
      FormationSensitive.Judgment rules reply.1.argument.context (Inversion.E second) reply.1.argument.type := by
  obtain ⟨admitted, result, literal, selected⟩ := meaning
  obtain ⟨contextEqual, typeEqual, source, sourceLiteral⟩ := admitted
  obtain ⟨target, targetLiteral, reflected⟩ :=
    Operations.parallel_reflects source selected.parallel sourceLiteral
  refine ⟨source, target, sourceLiteral, ?_, reflected, ?_⟩
  · exact literal.trans (congrArg some targetLiteral)
  · rw [contextEqual, typeEqual]
    exact source_judgment target

/-- A proposed reply is checked against the selected computation, rather
than being trusted as the operation's result. -/
def checkProposedResult {context : Mettapedia.OSLF.Binding.Ctx sig}
    (request : OperationRequest context) (proposed : NativeTerm context.length) : Bool :=
  checkOperation request &&
    decide (Selection.executeAt? request.address request.argument.term = some proposed)

theorem proposed_result_sound {context : Mettapedia.OSLF.Binding.Ctx sig}
    (request : OperationRequest context) (proposed : NativeTerm context.length)
    (accepted : checkProposedResult request proposed = true) :
    Admitted context .pr request.argument ∧
      Operations.ParallelStep request.argument.term proposed := by
  simp only [checkProposedResult, Bool.and_eq_true] at accepted
  obtain ⟨admitted, executed⟩ := accepted
  exact ⟨((checkOperation_exact request).mp admitted).1,
    (Selection.executeAt_sound _ _ _ (of_decide_eq_true executed)).parallel⟩

theorem forged_result_refused {context : Mettapedia.OSLF.Binding.Ctx sig}
    (request : OperationRequest context) (actual forged : NativeTerm context.length)
    (executed : Selection.executeAt? request.address request.argument.term = some actual)
    (different : actual ≠ forged) : checkProposedResult request forged = false := by
  simp [checkProposedResult, executed, different]


/-! ## Whole source steps through the three concrete services -/

theorem operation_invocation_value {context : Mettapedia.OSLF.Binding.Ctx sig}
    (request : OperationRequest context) (result : NativeTerm context.length) :
    (SemanticServiceInvocation.invoke (operationRequest request)).acceptedValue =
      some (request, some result) ↔
      Selection.executeAt? request.address request.argument.term = some result := by
  change some (request, Selection.executeAt? request.address request.argument.term) =
    some (request, some result) ↔ _
  simp

/-- A full original scoped source event is exactly two endpoint-bound
structural proof invocations around one admitted direct native operation.
The intermediate source terms are witnesses, not inputs to execution. -/
theorem source_step_iff_service_invocations {context : Mettapedia.OSLF.Binding.Ctx sig}
    (first second : Term sig context Srt.pr) :
    Mettapedia.Languages.ProcessCalculi.RhoCalculus.ScopedNativeServices.SourceStep first second ↔
      ∃ (before after : Term sig context Srt.pr)
          (prior later : EquationEvidence context Srt.pr) (address : Selection.Address),
        (SemanticServiceInvocation.invoke
          (equationRequest (sourceRequest first, sourceRequest before) prior)).acceptedValue =
            some (sourceRequest first, sourceRequest before) ∧
        SemanticServiceInvocation.InputAdmission
          (operationRequest ⟨sourceRequest before, address⟩) ∧
        (SemanticServiceInvocation.invoke
          (operationRequest ⟨sourceRequest before, address⟩)).acceptedValue =
            some (⟨sourceRequest before, address⟩, some (Inversion.E after)) ∧
        (SemanticServiceInvocation.invoke
          (equationRequest (sourceRequest after, sourceRequest second) later)).acceptedValue =
            some (sourceRequest after, sourceRequest second) := by
  rw [Operations.source_step_iff_native_modulo]
  constructor
  · rintro ⟨before, after, priorEquation, execution, laterEquation⟩
    obtain ⟨prior, priorAccepted⟩ := (source_equation_iff_service first before).mp priorEquation
    obtain ⟨later, laterAccepted⟩ := (source_equation_iff_service after second).mp laterEquation
    obtain ⟨address, executed⟩ := (Selection.parallel_iff_execution _ _).mp execution
    refine ⟨before, after, prior, later, address, priorAccepted, ?_, ?_, laterAccepted⟩
    · exact (operation_input_admission_exact _).mpr
        ⟨sourceRequest_admitted before, Inversion.E after,
          (Selection.executeAt_exact _ _ _).mp executed⟩
    · exact (operation_invocation_value _ _).mpr executed
  · rintro ⟨before, after, prior, later, address, priorAccepted, _, executed, laterAccepted⟩
    refine ⟨before, after, (source_equation_iff_service first before).mpr ⟨prior, priorAccepted⟩,
      ?_, (source_equation_iff_service after second).mpr ⟨later, laterAccepted⟩⟩
    exact (Selection.parallel_iff_execution _ _).mpr
      ⟨address, (operation_invocation_value _ _).mp executed⟩

/-! ## Native explicit structural proofs and compact-proof expansion -/

namespace ExplicitEquations
open Mettapedia.GSLT.LanguageDef.SemanticEvidence
open Mettapedia.OSLF.NativeTypes.Certificates

abbrev Proof := Conversion.Explicit.Certificate

def claim {context : Mettapedia.OSLF.Binding.Ctx sig} (sort : Srt)
    (request : EquationRequest context.length) : Conversion.Explicit.Claim :=
  ⟨context, sort, request.1.term, request.2.term⟩

/-- The original finite-rule proof history is qualified by independent
admission of its literal native request fields. -/
def guest (context : Mettapedia.OSLF.Binding.Ctx sig) (sort : Srt) :
    NativeProofSystem (EquationRequest context.length) where
  ProofObject := (FiniteRuleKernel.guest Conversion.Explicit.presentation).ProofObject
  Judges proof request := Admitted context sort request.1 ∧ Admitted context sort request.2 ∧
    (FiniteRuleKernel.guest Conversion.Explicit.presentation).Judges proof (claim sort request)

def check (context : Mettapedia.OSLF.Binding.Ctx sig) (sort : Srt)
    (request : EquationRequest context.length) (proof : Proof) : Bool :=
  checkAdmission context sort request.1 && checkAdmission context sort request.2 &&
    Conversion.Explicit.check (claim sort request) proof

/-- All guards and the explicit structural proof are actually checked. -/
def kernel (context : Mettapedia.OSLF.Binding.Ctx sig) (sort : Srt) :
    NativeProofKernel (guest context sort) where
  decide request proof := check context sort request proof
  correct input proof := by
    change Proof at proof
    change check context sort input proof = true ↔
      Admitted context sort input.1 ∧ Admitted context sort input.2 ∧
        ∃ derivation : Conversion.Explicit.Derivation (claim sort input),
          Tree.erase derivation = proof
    simp only [check, Bool.and_eq_true, checkAdmission_exact,
      Conversion.Explicit.check_exact]
    exact and_assoc

theorem meaning_exact (context : Mettapedia.OSLF.Binding.Ctx sig) (sort : Srt)
    (request : EquationRequest context.length) :
    EquationMeaning context sort request ↔ Nonempty ((guest context sort).ProofFibre request) := by
  constructor
  · rintro ⟨firstAdmission, secondAdmission, equation⟩
    obtain ⟨derivation⟩ := Conversion.Explicit.derivation_complete equation
    exact ⟨⟨Tree.erase derivation, firstAdmission, secondAdmission, derivation, rfl⟩⟩
  · rintro ⟨⟨proof, firstAdmission, secondAdmission, derivation, erased⟩⟩
    exact ⟨firstAdmission, secondAdmission, Conversion.Explicit.derivation_sound derivation⟩

def service (context : Mettapedia.OSLF.Binding.Ctx sig) (sort : Srt) :
    SemanticService.Service (equationTarget context sort) :=
  .nativeProof (guest context sort) (kernel context sort) (meaning_exact context sort)

def request {context : Mettapedia.OSLF.Binding.Ctx sig} {sort : Srt}
    (input : EquationRequest context.length) (proof : Proof) :
    SemanticServiceInvocation.Request (service context sort) := .nativeProof input proof

theorem invocation_exact {context : Mettapedia.OSLF.Binding.Ctx sig} {sort : Srt}
    (input : EquationRequest context.length) (proof : Proof) :
    (SemanticServiceInvocation.invoke (request (sort := sort) input proof)).acceptedValue = some input ↔
      check context sort input proof = true := by
  change (if check context sort input proof then some input else none) = some input ↔ _
  cases check context sort input proof <;> simp

/-- The already admitted compact request computes an explicit proof at its
unchanged context, sort, metadata and native endpoint fields. -/
theorem compact_expansion_accepted
    {context : Mettapedia.OSLF.Binding.Ctx sig} {sort : Srt}
    (input : EquationRequest context.length) (proof : EquationEvidence context sort)
    (accepted : checkEquation context sort input proof = true) :
    ∃ output : Proof, Conversion.Explicit.expand? proof = some output ∧
      check context sort input output = true := by
  have qualified := (equationChecker_sound input proof accepted)
  obtain ⟨_, _, first, firstLiteral⟩ := qualified.1
  obtain ⟨_, _, second, secondLiteral⟩ := qualified.2.1
  have compactChecked : EqualityCertificates.check proof first second = true := by
    have acceptedProof := (Bool.and_eq_true_iff.mp accepted).2
    rw [← firstLiteral, ← secondLiteral, checkNativeEquation_on_source] at acceptedProof
    exact acceptedProof
  obtain ⟨output, computed, explicitChecked⟩ := Conversion.Explicit.expand_checked
    proof first second compactChecked
  refine ⟨output, computed, ?_⟩
  have before := (checkAdmission_exact input.1).mpr qualified.1
  have after := (checkAdmission_exact input.2).mpr qualified.2.1
  simp only [check, before, after, Bool.and_self, Bool.true_and]
  unfold claim
  rw [← firstLiteral, ← secondLiteral]
  exact explicitChecked

/-- Source equation derivability agrees with native explicit-proof service
acceptance, independently of the separate compact replay service. -/
theorem source_equation_iff_service {context : Mettapedia.OSLF.Binding.Ctx sig} {sort : Srt}
    (first second : Term sig context sort) :
    EqClosure rhoSourceE first second ↔
      ∃ proof : Proof,
        (SemanticServiceInvocation.invoke
          (request (sort := sort) (sourceRequest first, sourceRequest second) proof)).acceptedValue =
            some (sourceRequest first, sourceRequest second) := by
  rw [Conversion.source_equation_iff_structural]
  constructor
  · intro equation
    have native := Conversion.Explicit.derivation_complete equation
    obtain ⟨derivation⟩ := native
    refine ⟨Tree.erase derivation, (invocation_exact (sort := sort) _ _).mpr ?_⟩
    have before := (checkAdmission_exact (sourceRequest first)).mpr (sourceRequest_admitted first)
    have after := (checkAdmission_exact (sourceRequest second)).mpr (sourceRequest_admitted second)
    simp only [check, before, after, Bool.and_self, Bool.true_and]
    exact Tree.check_erase derivation
  · rintro ⟨proof, accepted⟩
    have checked := (invocation_exact (sort := sort) _ _).mp accepted
    have clauses := (Bool.and_eq_true_iff.mp checked).2
    exact Conversion.Explicit.check_sound _ proof clauses

theorem source_step_iff_service_invocations {context : Mettapedia.OSLF.Binding.Ctx sig}
    (first second : Term sig context Srt.pr) :
    Mettapedia.Languages.ProcessCalculi.RhoCalculus.ScopedNativeServices.SourceStep first second ↔
      ∃ (before after : Term sig context Srt.pr)
          (prior later : Proof) (address : Selection.Address),
        (SemanticServiceInvocation.invoke
          (request (sort := .pr) (sourceRequest first, sourceRequest before) prior)).acceptedValue =
            some (sourceRequest first, sourceRequest before) ∧
        SemanticServiceInvocation.InputAdmission
          (operationRequest ⟨sourceRequest before, address⟩) ∧
        (SemanticServiceInvocation.invoke
          (operationRequest ⟨sourceRequest before, address⟩)).acceptedValue =
            some (⟨sourceRequest before, address⟩, some (Inversion.E after)) ∧
        (SemanticServiceInvocation.invoke
          (request (sort := .pr) (sourceRequest after, sourceRequest second) later)).acceptedValue =
            some (sourceRequest after, sourceRequest second) := by
  rw [Operations.source_step_iff_native_modulo]
  constructor
  · rintro ⟨before, after, priorEquation, execution, laterEquation⟩
    obtain ⟨prior, priorAccepted⟩ := (source_equation_iff_service first before).mp priorEquation
    obtain ⟨later, laterAccepted⟩ := (source_equation_iff_service after second).mp laterEquation
    obtain ⟨address, executed⟩ := (Selection.parallel_iff_execution _ _).mp execution
    refine ⟨before, after, prior, later, address, priorAccepted, ?_, ?_, laterAccepted⟩
    · exact (operation_input_admission_exact _).mpr
        ⟨sourceRequest_admitted before, Inversion.E after,
          (Selection.executeAt_exact _ _ _).mp executed⟩
    · exact (operation_invocation_value _ _).mpr executed
  · rintro ⟨before, after, prior, later, address, priorAccepted, _, executed, laterAccepted⟩
    refine ⟨before, after, (source_equation_iff_service first before).mpr ⟨prior, priorAccepted⟩,
      ?_, (source_equation_iff_service after second).mpr ⟨later, laterAccepted⟩⟩
    exact (Selection.parallel_iff_execution _ _).mpr
      ⟨address, (operation_invocation_value _ _).mp executed⟩

end ExplicitEquations

/-! ## Required interfaces and existing typed invocation routing -/

inductive ServiceRole where
  | admission (sort : Srt)
  | equation (sort : Srt)
  | nativeEquation (sort : Srt)
  | execution
  deriving DecidableEq

/-- The required family includes both source sorts and both evidence and
execution services; it is not selected by an empty-coverage witness. -/
def requiredServices : List ServiceRole :=
  [.admission .nm, .admission .pr, .equation .nm, .equation .pr,
    .nativeEquation .nm, .nativeEquation .pr, .execution]

theorem requiredServices_complete (role : ServiceRole) : role ∈ requiredServices := by
  cases role with
  | admission sort => cases sort <;> decide
  | equation sort => cases sort <;> decide
  | nativeEquation sort => cases sort <;> decide
  | execution => decide

def serviceTarget (context : Mettapedia.OSLF.Binding.Ctx sig) : ServiceRole → AdmissionObject
  | .admission sort => admissionTarget context sort
  | .equation sort => equationTarget context sort
  | .nativeEquation sort => equationTarget context sort
  | .execution => operationTarget context

def service (context : Mettapedia.OSLF.Binding.Ctx sig) :
    (role : ServiceRole) → SemanticService.Service (serviceTarget context role)
  | .admission sort => admissionService context sort
  | .equation sort => equationService context sort
  | .nativeEquation sort => ExplicitEquations.service context sort
  | .execution => operationService context

open Mettapedia.GSLT.LanguageDef.SemanticService

def requiredInterface (context : Mettapedia.OSLF.Binding.Ctx sig) :
    (role : ServiceRole) → Interface (serviceTarget context role)
  | .admission _ => .directDecision
  | .equation sort => .certificateBoundary (EquationEvidence context sort)
  | .nativeEquation sort => .nativeProof (ExplicitEquations.guest context sort)
  | .execution => .nativeOperation (operationSource context)

/-- Registration retains the exact evidence language and operation source,
not merely the name of a service face. -/
theorem service_interface_matches (context : Mettapedia.OSLF.Binding.Ctx sig) (role : ServiceRole) :
    InterfaceMatches (RawService.erase (service context role)) (requiredInterface context role) := by
  cases role with
  | admission sort => exact .directDecision _
  | equation sort => exact .certificateBoundary _ _
  | nativeEquation sort => exact .nativeProof _ _
  | execution => exact .nativeOperation _ _

/-- The existing invocation retains its concrete target and request input
under each selected service role. -/
abbrev RoutedRequest (context : Mettapedia.OSLF.Binding.Ctx sig) :=
  (role : ServiceRole) × SemanticServiceInvocation.Request (service context role)

def invokeRouted {context : Mettapedia.OSLF.Binding.Ctx sig} (request : RoutedRequest context) :
    SemanticServiceInvocation.Response request.2 := SemanticServiceInvocation.invoke request.2

theorem routed_accepted_meaning {context : Mettapedia.OSLF.Binding.Ctx sig}
    (request : RoutedRequest context) (admitted : SemanticServiceInvocation.InputAdmission request.2)
    {value : (serviceTarget context request.1).Carrier}
    (accepted : (invokeRouted request).acceptedValue = some value) :
    (serviceTarget context request.1).Meaning value :=
  SemanticServiceInvocation.accepted_meaning request.2 admitted accepted

/-- A native-equation request selects the original explicit proof language,
while the compact equation role retains its original certificate language. -/
def nativeEquationRequest {context : Mettapedia.OSLF.Binding.Ctx sig} {sort : Srt}
    (input : EquationRequest context.length) (proof : ExplicitEquations.Proof) :
    RoutedRequest context :=
  ⟨.nativeEquation sort, ExplicitEquations.request (sort := sort) input proof⟩

theorem routed_native_equation_exact {context : Mettapedia.OSLF.Binding.Ctx sig} {sort : Srt}
    (input : EquationRequest context.length) (proof : ExplicitEquations.Proof) :
    (invokeRouted (nativeEquationRequest (sort := sort) input proof)).acceptedValue = some input ↔
      ExplicitEquations.check context sort input proof = true :=
  ExplicitEquations.invocation_exact input proof

/-- Original scoped source events pass through the registered native-proof
roles around the registered direct operation, retaining all request fields. -/
theorem source_step_iff_routed_invocations {context : Mettapedia.OSLF.Binding.Ctx sig}
    (first second : Term sig context Srt.pr) :
    Mettapedia.Languages.ProcessCalculi.RhoCalculus.ScopedNativeServices.SourceStep first second ↔
      ∃ (before after : Term sig context Srt.pr)
          (prior later : ExplicitEquations.Proof) (address : Selection.Address),
        (invokeRouted (nativeEquationRequest (sort := .pr)
          (sourceRequest first, sourceRequest before) prior)).acceptedValue =
            some (sourceRequest first, sourceRequest before) ∧
        SemanticServiceInvocation.InputAdmission
          (operationRequest ⟨sourceRequest before, address⟩) ∧
        (invokeRouted ⟨.execution,
          operationRequest ⟨sourceRequest before, address⟩⟩).acceptedValue =
            some (⟨sourceRequest before, address⟩, some (Inversion.E after)) ∧
        (invokeRouted (nativeEquationRequest (sort := .pr)
          (sourceRequest after, sourceRequest second) later)).acceptedValue =
            some (sourceRequest after, sourceRequest second) :=
  ExplicitEquations.source_step_iff_service_invocations first second

/-! ## Admission and operation refusal boundaries -/

theorem wrong_context_refused {context : Mettapedia.OSLF.Binding.Ctx sig} {sort : Srt}
    (request : TermRequest context.length)
    (different : request.context ≠ BindingSignatureEmbedding.context names context) :
    checkAdmission context sort request = false := by
  cases checked : checkAdmission context sort request with
  | false => rfl
  | true => exact False.elim (different ((checkAdmission_exact (sort := sort) request).mp checked).1)

theorem wrong_type_refused {context : Mettapedia.OSLF.Binding.Ctx sig} {sort : Srt}
    (request : TermRequest context.length)
    (different : request.type ≠ BindingSignatureEmbedding.sortType names sort) :
    checkAdmission context sort request = false := by
  cases checked : checkAdmission context sort request with
  | false => rfl
  | true => exact False.elim (different ((checkAdmission_exact (sort := sort) request).mp checked).2.1)

theorem unknown_head_refused {context : Mettapedia.OSLF.Binding.Ctx sig} {sort : Srt}
    (request : TermRequest context.length) (unknown : request.term = .const `rho.unknown) :
    checkAdmission context sort request = false := by
  cases sort <;> simp [checkAdmission, admit?, unknown, readback, zeroName]

/-- Root execution and parallel selection cannot consume a quoted redex,
regardless of the requested address. -/
theorem quoted_redex_refused {n : Nat} (address : Selection.Address) (term : NativeTerm n) :
    Selection.executeAt? address (Operations.quote term) = none := by
  cases executed : Selection.executeAt? address (Operations.quote term) with
  | none => rfl
  | some target =>
      exact False.elim (Operations.quoted_redex_cannot_step term target
        (Selection.executeAt_sound _ _ _ executed).parallel)


/-- Admit metadata and literal source syntax before invoking the original
native operation. A failed selected address returns no admitted reply. -/
def invokeOperation? {context : Mettapedia.OSLF.Binding.Ctx sig}
    (request : OperationRequest context) : Option (OperationReply context) :=
  if checkAdmission context .pr request.argument then
    match (SemanticServiceInvocation.invoke.{0, 0} (operationRequest request)).acceptedValue with
    | some reply => if reply.2.isSome then some reply else none
    | none => none
  else none

theorem invokeOperation_some_iff {context : Mettapedia.OSLF.Binding.Ctx sig}
    (request : OperationRequest context) (result : NativeTerm context.length) :
    invokeOperation? request = some (request, some result) ↔
      Admitted context .pr request.argument ∧
        Selection.Step request.address request.argument.term result := by
  change (if checkAdmission context .pr request.argument then
    if (Selection.executeAt? request.address request.argument.term).isSome then
      some (request, Selection.executeAt? request.address request.argument.term) else none
    else none) = some (request, some result) ↔ _
  rw [← checkAdmission_exact (sort := Srt.pr) request.argument,
    ← Selection.executeAt_exact]
  cases checkAdmission context .pr request.argument <;>
    cases Selection.executeAt? request.address request.argument.term <;> simp

theorem invokeOperation_sound {context : Mettapedia.OSLF.Binding.Ctx sig}
    (request : OperationRequest context) (reply : OperationReply context)
    (accepted : invokeOperation? request = some reply) :
    reply.1 = request ∧ OperationMeaning reply := by
  change (if checkAdmission context .pr request.argument then
    if (Selection.executeAt? request.address request.argument.term).isSome then
      some (request, Selection.executeAt? request.address request.argument.term) else none
    else none) = some reply at accepted
  cases admitted : checkAdmission context .pr request.argument with
  | false => simp [admitted] at accepted
  | true =>
      cases executed : Selection.executeAt? request.address request.argument.term with
      | none => simp [admitted, executed] at accepted
      | some result =>
          simp only [admitted, executed, ↓reduceIte, Option.isSome_some, Option.some.injEq] at accepted
          rw [← accepted]
          exact ⟨rfl, (checkAdmission_exact (sort := Srt.pr) request.argument).mp admitted,
            result, rfl, (Selection.executeAt_exact _ _ _).mp executed⟩

theorem invokeOperation_context_refused {context : Mettapedia.OSLF.Binding.Ctx sig}
    (request : OperationRequest context)
    (different : request.argument.context ≠ BindingSignatureEmbedding.context names context) :
    invokeOperation? request = none := by
  have refused := wrong_context_refused (sort := Srt.pr) request.argument different
  simp [invokeOperation?, refused]

theorem invokeOperation_type_refused {context : Mettapedia.OSLF.Binding.Ctx sig}
    (request : OperationRequest context)
    (different : request.argument.type ≠ BindingSignatureEmbedding.sortType names Srt.pr) :
    invokeOperation? request = none := by
  have refused := wrong_type_refused (sort := Srt.pr) request.argument different
  simp [invokeOperation?, refused]

/-- Safe invocation returns a source-event witness and the actual native
result judgment. This theorem applies to arbitrary submitted requests. -/
theorem invokeOperation_reflects_source {context : Mettapedia.OSLF.Binding.Ctx sig}
    (request : OperationRequest context) (reply : OperationReply context)
    (accepted : invokeOperation? request = some reply) :
    ∃ first second : Term sig context Srt.pr,
      Inversion.E first = request.argument.term ∧ reply.2 = some (Inversion.E second) ∧
      Mettapedia.Languages.ProcessCalculi.RhoCalculus.ScopedNativeServices.SourceStep first second ∧
      FormationSensitive.Judgment rules request.argument.context (Inversion.E second) request.argument.type := by
  obtain ⟨sameRequest, meaning⟩ := invokeOperation_sound request reply accepted
  simpa only [sameRequest] using operation_reply_reflects_source reply meaning

namespace Controls
open RhoSchema.IntrinsicEncoding

def emptyRequest : TermRequest 0 := sourceRequest (.op Op.nil .nil : Term sig [] Srt.pr)

def wrongSortRequest : TermRequest 0 :=
  { emptyRequest with type := BindingSignatureEmbedding.sortType names Srt.nm }

def unknownHeadRequest : TermRequest 0 := { emptyRequest with term := .const `rho.unknown }

def openRequest : TermRequest 1 := sourceRequest openInputDropsAmbient

def wrongContextRequest : TermRequest 1 :=
  { openRequest with context := .snoc .nil (BindingSignatureEmbedding.sortType names Srt.pr) }

theorem ordinary_source_is_admitted : checkAdmission [] .pr emptyRequest = true := by decide

theorem open_quoted_source_is_admitted : checkAdmission [Srt.nm] .pr openRequest = true := by decide

theorem wrong_sort_is_refused : checkAdmission [] .pr wrongSortRequest = false := by decide

theorem wrong_context_is_refused : checkAdmission [Srt.nm] .pr wrongContextRequest = false := by decide

theorem unknown_head_is_refused : checkAdmission [] .pr unknownHeadRequest = false := by decide

def dropRequest : OperationRequest [] where
  argument := sourceRequest (.op Op.drp (.cons (.op Op.quo (.cons (.op Op.nil .nil) .nil)) .nil))
  address := []

theorem drop_operation_admitted : checkOperation dropRequest = true := by decide

theorem drop_constructs_original_payload :
    (runOperation dropRequest).2 = some (.const zeroName) := by decide

theorem forged_result_is_refused :
    checkProposedResult dropRequest (Operations.drop (Operations.quote (.const zeroName))) = false := by decide

/-- The same request is a direct native operation; a submitted equation
packet belongs to the distinct external boundary face. -/
theorem service_faces_distinct :
    (operationService []).face = .nativeOperation ∧
    (equationService [] .pr).face = .certificateBoundary ∧
    (admissionService [] .pr).face = .directDecision := by decide

end Controls


/-! ## Guarded authored communication and the two declared observers -/

namespace AuthoredAdapter
open Mettapedia.OSLF.Binding
open RhoSchema.IntrinsicEncoding
open RhoSemanticRulePolynomial

private abbrev raw := BindingCloneAlgebra.terms sig

/-- This request constructor covers all intrinsic scopes. The closed
quote-safe comparison below is a separate admission boundary. -/
def communicationRequest {context : Mettapedia.OSLF.Binding.Ctx sig}
    (channel : Term sig context Srt.nm) (payload : Term sig context Srt.pr)
    (body : Term sig (Srt.nm :: context) Srt.pr) : OperationRequest context where
  argument := sourceRequest (commSource raw channel payload body)
  address := []

theorem communication_executes {context : Mettapedia.OSLF.Binding.Ctx sig}
    (channel : Term sig context Srt.nm) (payload : Term sig context Srt.pr)
    (body : Term sig (Srt.nm :: context) Srt.pr) :
    invokeOperation? (communicationRequest channel payload body) =
      some (communicationRequest channel payload body,
        some (Inversion.E (RhoSemanticRulePolynomial.commTarget raw payload body))) := by
  apply (invokeOperation_some_iff _ _).mpr
  refine ⟨sourceRequest_admitted _, .root ?_⟩
  change Operations.Root
    (Operations.parallel (Operations.output (Inversion.E channel) (Inversion.E payload))
      (Operations.input (Inversion.E channel) (Inversion.E body)))
    (Inversion.E (Mettapedia.OSLF.Binding.bind
      (RhoScopedInstanceReadout.receiveRaw (.op Op.quo (.cons payload .nil))) body))
  have square : inst0 (Operations.quote (Inversion.E payload)) (Inversion.E body) =
      Inversion.E (Mettapedia.OSLF.Binding.bind
        (RhoScopedInstanceReadout.receiveRaw (.op Op.quo (.cons payload .nil))) body) :=
    Operations.encode_receive (.op Op.quo (.cons payload .nil)) body
  rw [← square]
  exact Operations.Root.communication (Inversion.E channel) (Inversion.E payload) (Inversion.E body)

/-- Finite source arguments, not a new rho syntax or a correctness provider. -/
structure Arguments where
  channel : Term sig [] Srt.nm
  payload : Term sig [] Srt.pr
  body : Term sig [Srt.nm] Srt.pr

def quoteSafe (arguments : Arguments) : Bool :=
  intrinsicQuoteSafe 0 arguments.channel && intrinsicQuoteSafe 0 arguments.payload &&
    intrinsicQuoteSafe 1 arguments.body

theorem quoteSafe_exact (arguments : Arguments) : quoteSafe arguments = true ↔
    intrinsicQuoteSafe 0 arguments.channel = true ∧
    intrinsicQuoteSafe 0 arguments.payload = true ∧
    intrinsicQuoteSafe 1 arguments.body = true := by
  simp only [quoteSafe, Bool.and_eq_true, and_assoc]

def request (arguments : Arguments) : OperationRequest [] :=
  communicationRequest arguments.channel arguments.payload arguments.body

def result (arguments : Arguments) : Term sig [] Srt.pr :=
  RhoSemanticRulePolynomial.commTarget raw arguments.payload arguments.body

/-- The guard limits this adapter to the domain of the existing authored
comparison. It does not restrict the full intrinsic native service. -/
def execute? (arguments : Arguments) : Option (OperationReply []) :=
  if quoteSafe arguments then invokeOperation? (request arguments) else none

theorem execute_exact (arguments : Arguments) :
    execute? arguments = some (request arguments, some (Inversion.E (result arguments))) ↔
      quoteSafe arguments = true := by
  simp only [execute?, request, result, communication_executes]
  cases quoteSafe arguments <;> simp

open Mettapedia.Languages.ProcessCalculi.RhoCalculus
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefRewriteSystem
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedContextualStep

/-- Accepted native computation participates in the actual authored firing.
Only the source comparison is structural; the immediate result comparison
uses the explicitly larger residual observer. -/
theorem guarded_comparison (arguments : Arguments) (safe : quoteSafe arguments = true) :
    execute? arguments = some (request arguments, some (Inversion.E (result arguments))) ∧
    RhoClosedTermWellSorted Mettapedia.OSLF.Framework.ConstructorCategory.rhoProc
      (RhoAuthoredCommRuleCover.authoredInputFirst arguments.channel arguments.payload arguments.body) ∧
    RhoStep (RhoAuthoredCommRuleCover.authoredInputFirst arguments.channel arguments.payload arguments.body)
      (RhoAuthoredCommRuleCover.authoredResult arguments.payload arguments.body) ∧
    StructuralCongruence
      (encodeTerm (RhoAuthoredCommRuleCover.intrinsicSource arguments.channel arguments.payload arguments.body))
      (RhoAuthoredCommRuleCover.authoredInputFirst arguments.channel arguments.payload arguments.body) ∧
    ProcResidualEquiv (RhoAuthoredCommRuleCover.authoredResult arguments.payload arguments.body)
      (encodeTerm (result arguments)) := by
  obtain ⟨channelSafe, payloadSafe, bodySafe⟩ := (quoteSafe_exact arguments).mp safe
  exact ⟨(execute_exact arguments).mpr safe,
    RhoQuoteSafeCommComparison.authored_comm_residual_simulation
      arguments.channel arguments.payload arguments.body channelSafe payloadSafe bodySafe⟩

/-- Both compared immediate results retain their independently stated
canonical authored admission, despite their distinct representations. -/
theorem guarded_targets_admitted (arguments : Arguments) (safe : quoteSafe arguments = true) :
    RhoClosedTermWellSorted Mettapedia.OSLF.Framework.ConstructorCategory.rhoProc
      (RhoAuthoredCommRuleCover.authoredResult arguments.payload arguments.body) ∧
    RhoClosedTermWellSorted Mettapedia.OSLF.Framework.ConstructorCategory.rhoProc
      (encodeTerm (result arguments)) := by
  obtain ⟨channelSafe, payloadSafe, bodySafe⟩ := (quoteSafe_exact arguments).mp safe
  have comparison := RhoQuoteSafeCommComparison.authored_comm_both_targets_admitted
    arguments.channel arguments.payload arguments.body channelSafe payloadSafe bodySafe
  exact ⟨comparison.1, comparison.2.1⟩

/-- The exact class of observations licensed by the existing comparison is
retained. No structural-congruence invariance is substituted for it. -/
theorem residual_observation (arguments : Arguments) (safe : quoteSafe arguments = true)
    (observation : ProcPred) (respects : ProcPredRespectsResidualEquiv observation) :
    observation (RhoAuthoredCommRuleCover.authoredResult arguments.payload arguments.body) ↔
      observation (encodeTerm (result arguments)) := by
  obtain ⟨_, payloadSafe, bodySafe⟩ := (quoteSafe_exact arguments).mp safe
  exact RhoQuoteSafeCommComparison.residualObservation_agrees_of_safe observation respects
    arguments.payload arguments.body payloadSafe bodySafe

/-- A payload-sorted view is computed by the existing translation rather
than identifying the two source binding signatures. -/
def payloadReadout? (arguments : Arguments) : Option
    (Term RhoPayloadPresentation.sig [] RhoPayloadPresentation.Srt.pr ×
     Term RhoPayloadPresentation.sig [] RhoPayloadPresentation.Srt.pr) := do
  let first ← RhoPayloadPresentation.tProc (RhoPayloadPresentation.Env.empty [])
    (RhoAuthoredCommRuleCover.authoredInputFirst arguments.channel arguments.payload arguments.body)
  let second ← RhoPayloadPresentation.tProc (RhoPayloadPresentation.Env.empty [])
    (RhoAuthoredCommRuleCover.authoredResult arguments.payload arguments.body)
  return (first, second)

/-- On the guarded domain, that executable view is defined and has the
actual payload presentation's directed strict step. -/
theorem payload_readout_step (arguments : Arguments) (safe : quoteSafe arguments = true) :
    ∃ first second,
      payloadReadout? arguments = some (first, second) ∧
        RhoPayloadPresentation.Steps RhoPayloadPresentation.strictRules first second := by
  have comparison := guarded_comparison arguments safe
  have sourceAdmission := (rhoClosedTermWellSorted_process_iff _).mp comparison.2.1
  obtain ⟨first, translated⟩ := RhoPayloadPresentation.closed_admitted_translates
    (fun name => by simp [Mettapedia.OSLF.MeTTaIL.DerivedPresentationSyntax.FreeSortContext.empty])
    sourceAdmission.1 sourceAdmission.2
  obtain ⟨second, translatedResult, step⟩ :=
    RhoPayloadPresentation.rhoStep_simulation sourceAdmission.1 comparison.2.2.1 translated
  exact ⟨first, second, by simp [payloadReadout?, translated, translatedResult], step⟩

/-- This witness simultaneously has residual agreement and an accepted
native operation, while its two immediate raw targets remain structurally
distinguishable. -/
theorem unquote_keeps_observer_boundary :
    execute? ⟨RhoSchema.chan, RhoSchema.nilP, .op Op.drp (.cons (.var .zero) .nil)⟩ =
      some (request ⟨RhoSchema.chan, RhoSchema.nilP, .op Op.drp (.cons (.var .zero) .nil)⟩,
        some (Inversion.E RhoSchema.commTarget)) ∧
    ProcResidualEquiv authoredCommReduct (encodeTerm RhoSchema.commTarget) ∧
    ¬ StructuralCongruence authoredCommReduct (encodeTerm RhoSchema.commTarget) := by
  refine ⟨?_, RhoQuoteSafeCommComparison.unquote_result_residual_but_not_structural⟩
  exact (execute_exact _).mpr (by decide +kernel)

/-- Quote-unsafe intrinsic terms are still handled by the full native
profile. Only the authored adapter refuses its unsupported comparison. -/
def unsafeArguments : Arguments :=
  ⟨RhoSchema.chan, RhoSchema.nilP,
    .op Op.drp (.cons (.op Op.quo (.cons (.op Op.drp (.cons (.var .zero) .nil)) .nil)) .nil)⟩

theorem unsafe_adapter_refused : execute? unsafeArguments = none := by decide +kernel

theorem unsafe_intrinsic_still_executes :
    invokeOperation? (request unsafeArguments) =
      some (request unsafeArguments, some (Inversion.E (result unsafeArguments))) :=
  communication_executes _ _ _

/-- The existing open source-admission counterexample also executes through
actual native services. Native coverage does not imply sealed-quote closure. -/
theorem open_native_target_boundary :
    invokeOperation? (communicationRequest openCommAmbientName openCommPayload openCommContinuation) =
      some (communicationRequest openCommAmbientName openCommPayload openCommContinuation,
        some (Inversion.E openCommTarget)) ∧
    intrinsicQuoteSafe 1 openCommSource = true ∧
    intrinsicQuoteSafe 1 openCommTarget = false := by
  exact ⟨communication_executes _ _ _, openComm_not_closed_on_literal_source⟩

end AuthoredAdapter




end Mettapedia.Languages.MeTTa.PrimeComparisons.Rho.ScopedServices
