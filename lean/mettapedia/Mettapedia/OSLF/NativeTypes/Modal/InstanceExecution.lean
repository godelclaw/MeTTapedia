import Mettapedia.OSLF.NativeTypes.Decision.Machine.Interface
import Mettapedia.OSLF.NativeTypes.Decision.Machine.Meaning
import Mettapedia.OSLF.NativeTypes.Decision.Machine.State
import Mettapedia.OSLF.NativeTypes.Decision.Machine
import Mettapedia.OSLF.NativeTypes.Modal.InstanceDecision
import Mettapedia.OSLF.NativeTypes.Instances.Local.Backend
import Mettapedia.OSLF.NativeTypes.Instances.Local.CursorBackend
import Mettapedia.OSLF.NativeTypes.Instances.Local.Structural

open Mettapedia.OSLF.Framework

/-!
# Executable supplied instances of generated modal formers

The request retains the actual schema, supplied assignment, focused term,
filled program and specified contractum. Its equation-invariant leaf checks
that contractum's class together with the assignment-substituted continuation.
Source admission is checked separately from formation and assignment admission.
A completed instance does not establish universal rely-family membership.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Modal.InstanceExecution

open Mettapedia.OSLF.MeTTaIL Syntax
open Mettapedia.OSLF.NativeTypes.Generation Mettapedia.OSLF.NativeTypes.Modal.Rules
open Mettapedia.OSLF.NativeTypes.Decision.Reference.Core
open Mettapedia.OSLF.NativeTypes.Modal.InstanceDecision
open Mettapedia.OSLF.NativeTypes.Decision.Machine

variable {generated : Generated} {schema : Schema generated.plan}
variable {codes : ModalInstanceCodes generated schema}
variable {assignment : ScopedRuleMatching.Assignment} {focus : Pattern}

/-- Primitive carrier admission is computational; it supplies no operational
coverage or final native-membership answer. -/
structure SourceAdmission (admitted : Pattern → Prop) where
  accepts : Pattern → Bool
  exact : ∀ source, accepts source = true ↔ admitted source

inductive Issue where
  | request (reason : ModalInstanceIssue)
  | unsupportedSource
  deriving DecidableEq, Repr

structure AdmittedRequest (codes : ModalInstanceCodes generated schema)
    (assignment : ScopedRuleMatching.Assignment) (focus : Pattern) (admitted : Pattern → Prop) where
  request : ModalInstanceRequest codes assignment focus
  sourceAdmitted : admitted request.source

def admit? {admitted : Pattern → Prop} (admission : SourceAdmission admitted)
    (codes : ModalInstanceCodes generated schema) (decisions : ModalInstanceDecisions codes)
    (assignment : ScopedRuleMatching.Assignment) (focus : Pattern) :
    Except Issue (AdmittedRequest codes assignment focus admitted) :=
  if (generated.modalFormer? schema codes.actualInputs).isSome then
    match admitModalInstance? codes decisions assignment focus with
    | .error reason => .error (.request reason)
    | .ok request =>
      if checked : admission.accepts request.source = true then
        .ok ⟨request, (admission.exact request.source).mp checked⟩
      else .error .unsupportedSource
  else .error (.request .unavailableFormer)

theorem admission_retains_former {admitted : Pattern → Prop}
    (admission : SourceAdmission admitted) (decisions : ModalInstanceDecisions codes)
    {result : AdmittedRequest codes assignment focus admitted}
    (success : admit? admission codes decisions assignment focus = .ok result) :
    (generated.modalFormer? schema codes.actualInputs).isSome = true := by
  unfold admit? at success
  split at success
  · assumption
  · cases success

/-- The actual sorted-source checker supplies the generic local profile's
source gate. Both directions are proved by the existing independent typing
semantics. -/
def localSourceAdmission : SourceAdmission
    (Mettapedia.OSLF.NativeTypes.Instances.Local.Backend.Source generated.plan schema.bound schema.programCarrier) where
  accepts := Mettapedia.OSLF.NativeTypes.Instances.Local.Backend.sourceChecked generated.plan schema.bound schema.programCarrier
  exact _source := ⟨Mettapedia.GSLT.LanguageDef.WellSorted.checkOpenPatternWellSorted_sound,
    Mettapedia.GSLT.LanguageDef.WellSorted.checkOpenPatternWellSorted_complete⟩

/-- Only the primitive equation test and the actual continuation decision
appear in this leaf. Successors are supplied by the retained occurrence stream. -/
def leaf {admitted : Pattern → Prop}
    (equations : EquationDecision (GeneratedInstance.system schema))
    (decisions : ModalInstanceDecisions codes)
    (request : ModalInstanceRequest codes assignment focus) :
    LeafBackend (GeneratedInstance.system schema) admitted :=
  LeafBackend.ofBoolean
    (contractumPredicate (GeneratedInstance.system schema) request.target
      ((codes.inputs.2 assignment).meaning request.target))
    (fun actual => equations.equivalent actual request.target &&
      @decide ((codes.inputs.2 assignment).meaning request.target)
        (decisions.continuation assignment request.target)) (by
        intro actual
        simp only [Bool.and_eq_true]
        exact and_congr (equations.exact actual request.target)
          (@decide_eq_true_iff ((codes.inputs.2 assignment).meaning request.target)
            (decisions.continuation assignment request.target)))

def leaves {admitted : Pattern → Prop}
    (equations : EquationDecision (GeneratedInstance.system schema))
    (decisions : ModalInstanceDecisions codes)
    (request : ModalInstanceRequest codes assignment focus) :
    Unit → LeafBackend (GeneratedInstance.system schema) admitted :=
  fun _ => leaf equations decisions request

def tests {admitted : Pattern → Prop}
    (equations : EquationDecision (GeneratedInstance.system schema))
    (decisions : ModalInstanceDecisions codes)
    (request : ModalInstanceRequest codes assignment focus) :
    Unit → Test (GeneratedInstance.system schema) admitted :=
  Mettapedia.OSLF.NativeTypes.Modal.InstanceDecision.tests equations request.target
    ((codes.inputs.2 assignment).meaning request.target)
    (@decide ((codes.inputs.2 assignment).meaning request.target)
      (decisions.continuation assignment request.target))
    (@decide_eq_true_iff ((codes.inputs.2 assignment).meaning request.target)
      (decisions.continuation assignment request.target))

theorem leaf_meaning {admitted : Pattern → Prop}
    (equations : EquationDecision (GeneratedInstance.system schema))
    (decisions : ModalInstanceDecisions codes)
    (request : ModalInstanceRequest codes assignment focus) (index : Unit) :
    (leaves (admitted := admitted) equations decisions request index).predicate =
      (tests (admitted := admitted) equations decisions request index).predicate := rfl

/-- The operational question names the source's specified right-hand side and
the substituted continuation, rather than an arbitrary successor. -/
theorem native_meaning {admitted : Pattern → Prop}
    (equations : EquationDecision (GeneratedInstance.system schema))
    (decisions : ModalInstanceDecisions codes)
    (request : ModalInstanceRequest codes assignment focus)
    (spatial : Decision.Spatial.SpatialTheory (GeneratedInstance.system schema) :=
      .empty (GeneratedInstance.system schema)) :
    Mettapedia.OSLF.NativeTypes.Decision.Reference.Core.denotation (tests (admitted := admitted) equations decisions request)
      instanceFormula spatial request.source ↔
      Nonempty (Mettapedia.OSLF.NativeTypes.Modal.Rules.Outcome schema focus assignment codes.continuation) :=
  (instance_native_comparison equations request.target
    ((codes.inputs.2 assignment).meaning request.target)
    (@decide ((codes.inputs.2 assignment).meaning request.target)
      (decisions.continuation assignment request.target))
    (@decide_eq_true_iff ((codes.inputs.2 assignment).meaning request.target)
      (decisions.continuation assignment request.target)) request.source spatial).trans
        (GeneratedInstance.outcome_exact request)

theorem machine_native_meaning {admitted : Pattern → Prop}
    (equations : EquationDecision (GeneratedInstance.system schema))
    (decisions : ModalInstanceDecisions codes)
    (request : ModalInstanceRequest codes assignment focus)
    (spatial : Decision.Spatial.SpatialTheory (GeneratedInstance.system schema) :=
      .empty (GeneratedInstance.system schema)) :
    Mettapedia.OSLF.NativeTypes.Decision.Machine.denotation
        (leaves (admitted := admitted) equations decisions request) instanceFormula spatial request.source ↔
      Nonempty (Mettapedia.OSLF.NativeTypes.Modal.Rules.Outcome schema focus assignment codes.continuation) := by
  rw [Mettapedia.OSLF.NativeTypes.Decision.Machine.denotation_comparison
    (leaves (admitted := admitted) equations decisions request)
    (tests (admitted := admitted) equations decisions request)
    (leaf_meaning equations decisions request) instanceFormula spatial]
  exact native_meaning equations decisions request spatial

structure Session {admitted : Pattern → Prop}
    (backend : CursorBackend (GeneratedInstance.system schema) admitted)
    (equations : EquationDecision (GeneratedInstance.system schema))
    (decisions : ModalInstanceDecisions codes)
    (assignment : ScopedRuleMatching.Assignment) (focus : Pattern) where
  admittedRequest : AdmittedRequest codes assignment focus admitted
  state : Mettapedia.OSLF.NativeTypes.Decision.Machine.State (Mettapedia.OSLF.NativeTypes.Decision.Machine.Evidence backend)
    (Mettapedia.OSLF.NativeTypes.Decision.Machine.denotation (leaves (admitted := admitted) equations decisions admittedRequest.request)
      instanceFormula backend.spatial.theory admittedRequest.request.source)

variable {admitted : Pattern → Prop}
variable {backend : CursorBackend (GeneratedInstance.system schema) admitted}
variable {equations : EquationDecision (GeneratedInstance.system schema)}
variable {decisions : ModalInstanceDecisions codes}

def Session.result (session : Session backend equations decisions assignment focus) :
    Mettapedia.OSLF.NativeTypes.Decision.Reference.Core.Outcome
      (Nonempty (Mettapedia.OSLF.NativeTypes.Modal.Rules.Outcome schema focus assignment codes.continuation)) :=
  Mettapedia.OSLF.NativeTypes.Decision.Reference.Core.Outcome.map
    (machine_native_meaning (admitted := admitted) equations decisions session.admittedRequest.request
      backend.spatial.theory) session.state.outcome

def Session.answer (session : Session backend equations decisions assignment focus) : Option Bool :=
  session.result.answer

def Session.spent (session : Session backend equations decisions assignment focus) : Nat := session.state.spent

def Session.observations (session : Session backend equations decisions assignment focus) :
    List (Mettapedia.OSLF.NativeTypes.Decision.Machine.Observation backend) :=
  session.state.observations.filterMap Mettapedia.OSLF.NativeTypes.Decision.Machine.Evidence.operational?

def resume (budget : Nat) (session : Session backend equations decisions assignment focus) :
    Session backend equations decisions assignment focus :=
  ⟨session.admittedRequest, Mettapedia.OSLF.NativeTypes.Decision.Machine.resume budget session.state⟩

theorem exact_resume (first more : Nat) (session : Session backend equations decisions assignment focus) :
    resume (first + more) session = resume more (resume first session) := by
  cases session
  simp only [resume, Mettapedia.OSLF.NativeTypes.Decision.Machine.resume_add]

theorem resume_work_bounded (budget : Nat) (session : Session backend equations decisions assignment focus) :
    (resume budget session).spent ≤ session.spent + budget :=
  Mettapedia.OSLF.NativeTypes.Decision.Machine.resume_spent_le session.state budget

theorem resume_retains_request (budget : Nat) (session : Session backend equations decisions assignment focus) :
    (resume budget session).admittedRequest = session.admittedRequest := rfl

theorem resume_conclusive (session : Session backend equations decisions assignment focus)
    (answer : Bool) (read : session.answer = some answer) (budget : Nat) :
    resume budget session = session := by
  have settled : session.state.outcome.Decided := by
    cases result : session.state.outcome with
    | proved proof => exact ⟨true, rfl⟩
    | refuted refutation => exact ⟨false, rfl⟩
    | unknown =>
      simp only [Session.answer, Session.result, result, Mettapedia.OSLF.NativeTypes.Decision.Reference.Core.Outcome.map,
        Mettapedia.OSLF.NativeTypes.Decision.Reference.Core.Outcome.answer] at read
      cases read
  cases session
  simp only [resume, Mettapedia.OSLF.NativeTypes.Decision.Machine.resume_conclusive _ settled]

theorem positive (session : Session backend equations decisions assignment focus)
    (read : session.answer = some true) :
    Nonempty (Mettapedia.OSLF.NativeTypes.Modal.Rules.Outcome schema focus assignment codes.continuation) :=
  Mettapedia.OSLF.NativeTypes.Decision.Reference.Core.Outcome.positive session.result read

theorem negative (session : Session backend equations decisions assignment focus)
    (read : session.answer = some false) :
    ¬ Nonempty (Mettapedia.OSLF.NativeTypes.Modal.Rules.Outcome schema focus assignment codes.continuation) :=
  Mettapedia.OSLF.NativeTypes.Decision.Reference.Core.Outcome.negative session.result read

theorem observed_step (session : Session backend equations decisions assignment focus)
    (observation : Mettapedia.OSLF.NativeTypes.Decision.Machine.Observation backend)
    (_listed : observation ∈ session.observations) :
    (GeneratedInstance.system schema).Step observation.source
      (backend.target observation.source observation.receipt) := observation.step

def start (backend : CursorBackend (GeneratedInstance.system schema) admitted)
    (equations : EquationDecision (GeneratedInstance.system schema))
    (decisions : ModalInstanceDecisions codes)
    (request : AdmittedRequest codes assignment focus admitted) :
    Session backend equations decisions assignment focus :=
  ⟨request, Mettapedia.OSLF.NativeTypes.Decision.Machine.start backend (leaves equations decisions request.request)
    instanceFormula request.request.source request.sourceAdmitted⟩

def run (backend : CursorBackend (GeneratedInstance.system schema) admitted)
    (equations : EquationDecision (GeneratedInstance.system schema))
    (decisions : ModalInstanceDecisions codes)
    (request : AdmittedRequest codes assignment focus admitted) (budget : Nat) :
    Session backend equations decisions assignment focus :=
  resume budget (start backend equations decisions request)

def check (backend : CursorBackend (GeneratedInstance.system schema) admitted)
    (equations : EquationDecision (GeneratedInstance.system schema))
    (admission : SourceAdmission admitted) (codes : ModalInstanceCodes generated schema)
    (decisions : ModalInstanceDecisions codes)
    (assignment : ScopedRuleMatching.Assignment) (focus : Pattern) (budget : Nat) :
    Except Issue (Session backend equations decisions assignment focus) :=
  (admit? admission codes decisions assignment focus).map
    (fun request => run backend equations decisions request budget)

/-- Exhaustive computation is a separate request. Ordinary checking and
resuming do not calculate this bound. -/
def totalBound (backend : CursorBackend (GeneratedInstance.system schema) admitted)
    (equations : EquationDecision (GeneratedInstance.system schema))
    (decisions : ModalInstanceDecisions codes)
    (request : AdmittedRequest codes assignment focus admitted) : Nat :=
  Mettapedia.OSLF.NativeTypes.Decision.Machine.totalBound backend (leaves equations decisions request.request)
    instanceFormula request.request.source request.sourceAdmitted

theorem start_empty (request : AdmittedRequest codes assignment focus admitted) :
    (start backend equations decisions request).answer = none ∧
      (start backend equations decisions request).spent = 0 ∧
      (start backend equations decisions request).observations = [] := ⟨rfl, rfl, rfl⟩

theorem run_exact_resume (request : AdmittedRequest codes assignment focus admitted) (first more : Nat) :
    run backend equations decisions request (first + more) =
      resume more (run backend equations decisions request first) :=
  exact_resume first more (start backend equations decisions request)

theorem run_work_bounded (request : AdmittedRequest codes assignment focus admitted) (budget : Nat) :
    (run backend equations decisions request budget).spent ≤ budget :=
  Mettapedia.OSLF.NativeTypes.Decision.Machine.spent_le_budget backend (leaves equations decisions request.request)
    instanceFormula request.request.source request.sourceAdmitted budget

theorem run_complete (request : AdmittedRequest codes assignment focus admitted) (budget : Nat)
    (enough : totalBound backend equations decisions request ≤ budget) :
    (run backend equations decisions request budget).result.Decided :=
  Mettapedia.OSLF.NativeTypes.Decision.Reference.Core.Outcome.map_decided
    (machine_native_meaning (admitted := admitted) equations decisions request.request backend.spatial.theory) _
    (Mettapedia.OSLF.NativeTypes.Decision.Machine.complete_at_bound backend (leaves equations decisions request.request)
      instanceFormula request.request.source request.sourceAdmitted budget enough)

theorem conclusive_mono (request : AdmittedRequest codes assignment focus admitted)
    (small large : Nat) (ordered : small ≤ large) (answer : Bool)
    (read : (run backend equations decisions request small).answer = some answer) :
    (run backend equations decisions request large).answer = some answer := by
  rw [← Nat.add_sub_of_le ordered, run_exact_resume,
    resume_conclusive (run backend equations decisions request small) answer read]
  exact read

section AuthoredLocal

open GeneralExecutionAdmission

def localCursor (foundation : generated.plan.complete = true)
    (equationFree : generated.plan.equations = [])
    (generic : GeneralExecutionTotalAdmission.checkGeneric generated.plan = true) :
    CursorBackend (GeneratedInstance.system schema)
      (Mettapedia.OSLF.NativeTypes.Instances.Local.Backend.Source generated.plan schema.bound schema.programCarrier) :=
  Mettapedia.OSLF.NativeTypes.Instances.Local.CursorBackend.cursorBackend generated.plan schema.bound schema.programCarrier
    rfl foundation equationFree generic

def localEquations (equationFree : generated.plan.equations = []) :
    EquationDecision (GeneratedInstance.system schema) where
  equivalent (first : Pattern) (second : Pattern) := decide (first = second)
  exact (first : Pattern) (second : Pattern) := by
    rw [decide_eq_true_iff]
    change first = second ↔ Relation.EqvGen
      (GeneralOccurrenceSemantics.Equation generated.plan schema.bound schema.programCarrier) first second
    exact (Mettapedia.OSLF.NativeTypes.Instances.Local.Structural.no_equation_iff_eq
      equationFree schema.bound schema.programCarrier first second).symm

/-- The local adapter constructs its engine and primitive source/equation
checks directly from the generated plan. Its profile hypotheses are the
computed admission gates already used by the authored local generator. -/
def checkLocal (schema : Schema generated.plan) (foundation : generated.plan.complete = true)
    (equationFree : generated.plan.equations = [])
    (generic : GeneralExecutionTotalAdmission.checkGeneric generated.plan = true)
    (codes : ModalInstanceCodes generated schema) (decisions : ModalInstanceDecisions codes)
    (assignment : ScopedRuleMatching.Assignment) (focus : Pattern) (budget : Nat) :=
  check (localCursor (schema := schema) foundation equationFree generic)
    (localEquations (schema := schema) equationFree) (localSourceAdmission (schema := schema))
    codes decisions assignment focus budget

end AuthoredLocal

end Mettapedia.OSLF.NativeTypes.Modal.InstanceExecution
