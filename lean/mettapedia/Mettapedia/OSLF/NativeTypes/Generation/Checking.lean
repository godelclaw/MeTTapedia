import Mettapedia.OSLF.NativeTypes.Generation.Core
import Mettapedia.OSLF.NativeTypes.Structural.DecompositionReadout

open Mettapedia.OSLF.Framework

/-!
# Certified checking of generated operational judgments

The query keeps the executed state and its native receipts. A witness can
establish possibility before search finishes; absence needs checked coverage.
The outgoing universal readout is separate from OSLF's incoming adjoint box.
An unsupported connective is a refusal, and missing coverage is unknown.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Generation

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL
open GeneralOccurrenceFrontier
open Mettapedia.OSLF.NativeTypes.Structural (Connective)

inductive ModalQuery where
  | possibility
  | outgoingUniversal
  deriving DecidableEq, Repr

inductive CheckResult where
  | decided (answer : Bool)
  | unknown
  | refused (connective : Connective)
  | illFormed (reason : Mettapedia.OSLF.NativeTypes.Structural.Refusal)
  | refusedPossibility
  | rejectedCube
  deriving DecidableEq, Repr

/-- A conclusive answer retains the actual frontier that earned it. -/
structure QueryRun (generated : Generated) (bound : List TypeExpr)
    (expected : TypeExpr) (source : Pattern) where
  state : State (generated.request bound expected source)
  result : CheckResult

/-- A quotient-level modal query carries the earned equation invariance of
its executable predicate. Raw syntax tests cannot silently certify absence
over an entire equation class. -/
structure InvariantTest (request : Request) where
  accepts : Pattern → Bool
  invariant : ∀ first second, Relation.EqvGen
    (GeneralOccurrenceSemantics.Equation request.plan request.bound request.expected)
    first second → accepts first = accepts second

def sourceAdmission (request : Request) : Bool :=
  request.plan.complete &&
    Mettapedia.GSLT.LanguageDef.WellSorted.checkOpenPatternWellSorted
      request.plan.snapshot.language request.plan.snapshot.free request.bound request.expected request.root

theorem sourceAdmission_eq_true_iff {request : Request} :
    sourceAdmission request = true ↔
      request.plan.complete = true ∧
        Mettapedia.GSLT.LanguageDef.WellSorted.OpenPatternWellSorted
          request.plan.snapshot.language request.plan.snapshot.free
          request.bound request.expected request.root := by
  unfold sourceAdmission
  rw [Bool.and_eq_true, Mettapedia.GSLT.LanguageDef.WellSorted.checkOpenPatternWellSorted_eq_true_iff]

theorem sourceAdmission_sound {request : Request} (checked : sourceAdmission request = true)
    (compiled : request.plan = GeneralExecutionAdmission.compile request.plan.snapshot request.plan.permissions) :
    Admitted request := by
  obtain ⟨accepted, sorted⟩ := sourceAdmission_eq_true_iff.mp checked
  exact ⟨compiled, accepted, sorted⟩

theorem sourceAdmission_complete {request : Request} (admitted : Admitted request) :
    sourceAdmission request = true :=
  sourceAdmission_eq_true_iff.mpr ⟨admitted.accepted, admitted.rootSorted⟩

def modalReadout (kind : ModalQuery) (request : Request) (state : State request)
    (test : Pattern → Bool) : CheckResult :=
  match kind with
  | .possibility =>
      if (targets request state).any test then .decided true
      else if sourceAdmission request && checkCertificate request state then .decided false
      else .unknown
  | .outgoingUniversal =>
      if !(targets request state).all test then .decided false
      else if sourceAdmission request && checkCertificate request state then .decided true
      else .unknown

def Generated.checkModal (generated : Generated) (bound : List TypeExpr)
    (expected : TypeExpr) (source : Pattern) (kind : ModalQuery)
    (test : InvariantTest (generated.request bound expected source)) (budget : Nat) :
    QueryRun generated bound expected source :=
  let request := generated.request bound expected source
  let state := generated.execute bound expected source budget
  let enabled := match kind with
    | .possibility => generated.logicFragment.core.possibility
    | .outgoingUniversal => generated.logicFragment.core.modal
  {state := state, result :=
    if !enabled then match kind with
      | .possibility => .refusedPossibility
      | .outgoingUniversal => .refused .modal
    else match generated.equationAdmission with
      | some true => modalReadout kind request state test.accepts
      | some false => .rejectedCube
      | none => .unknown}

def formulaReadout (request : Request) (state : State request) (componentBudget : Nat)
    (formula : Mettapedia.OSLF.NativeTypes.Structural.Formula) : CheckResult :=
  if sourceAdmission request then
    match Mettapedia.OSLF.NativeTypes.Structural.readGeneratedFormula request state componentBudget formula with
    | some answer => .decided answer
    | none => .unknown
  else .unknown

/-- Generated structural/propositional judgments use the same executed
equation representatives and coverage certificate as modal checking. -/
def Generated.checkFormula (generated : Generated) (bound : List TypeExpr)
    (expected : TypeExpr) (source : Pattern) (formula : Mettapedia.OSLF.NativeTypes.Structural.Formula)
    (budget : Nat) : QueryRun generated bound expected source :=
  let request := generated.request bound expected source
  let state := generated.execute bound expected source budget
  {state := state, result :=
    match generated.elaborate expected formula with
    | .error reason => .illFormed reason
    | .ok _ =>
        match generated.equationAdmission with
        | some true => formulaReadout request state budget formula
        | some false => .rejectedCube
        | none => .unknown}

theorem formula_readout_sound {request : Request} {state : State request}
    {formula : Mettapedia.OSLF.NativeTypes.Structural.Formula} {answer : Bool} {componentBudget : Nat}
    (compiled : request.plan = GeneralExecutionAdmission.compile request.plan.snapshot request.plan.permissions)
    (read : formulaReadout request state componentBudget formula = .decided answer)
    (atom : TypeExpr → Nat → Pattern → Prop) :
    answer = true ↔ Mettapedia.OSLF.NativeTypes.Structural.Holds request.plan.snapshot.language request.plan.snapshot.free
      request.bound (Mettapedia.OSLF.NativeTypes.Structural.frontierEquation request) atom request.expected formula request.root := by
  unfold formulaReadout at read
  split at read
  · rename_i admission
    cases observed : Mettapedia.OSLF.NativeTypes.Structural.readGeneratedFormula request state componentBudget formula with
    | none => simp [observed] at read
    | some value =>
        simp only [observed, CheckResult.decided.injEq] at read
        subst value
        exact Mettapedia.OSLF.NativeTypes.Structural.readGeneratedFormula_sound
          (sourceAdmission_sound admission compiled) atom componentBudget formula answer observed
  · cases read

theorem generated_formula_sound {generated : Generated} {bound : List TypeExpr}
    {expected : TypeExpr} {source : Pattern} {formula : Mettapedia.OSLF.NativeTypes.Structural.Formula}
    {budget : Nat} {answer : Bool}
    (read : (generated.checkFormula bound expected source formula budget).result = .decided answer)
    (atom : TypeExpr → Nat → Pattern → Prop) :
    answer = true ↔ Mettapedia.OSLF.NativeTypes.Structural.Holds generated.snapshot.language generated.snapshot.free
      bound (Mettapedia.OSLF.NativeTypes.Structural.frontierEquation (generated.request bound expected source))
      atom expected formula source.eraseBinderMetadata := by
  unfold Generated.checkFormula at read
  cases formed : generated.elaborate expected formula with
  | error reason => simp [formed] at read
  | ok judgment =>
      simp only [formed] at read
      cases admission : generated.equationAdmission with
      | none => simp [admission] at read
      | some accepted =>
          cases accepted with
          | false => simp [admission] at read
          | true =>
              simp only [admission] at read
              exact formula_readout_sound rfl read atom

theorem possibility_witness_sound {request : Request} {state : State request}
    {test : Pattern → Bool}
    (checked : modalReadout .possibility request state test = .decided true) :
    ∃ target, (GeneralOccurrenceSemantics.gslt request.plan request.bound request.expected).Step
      request.root target ∧ test target = true := by
  simp only [modalReadout] at checked
  split at checked
  next found =>
    obtain ⟨target, member, accepts⟩ := List.any_eq_true.mp found
    obtain ⟨answer, _, same⟩ := List.mem_map.mp member
    subst target
    exact ⟨answer.val.target, emitted_step request answer, accepts⟩
  next absent => split at checked <;> cases checked

theorem possibility_refutation_sound {request : Request} {state : State request}
    {test : Pattern → Bool}
    (compiled : request.plan = GeneralExecutionAdmission.compile request.plan.snapshot request.plan.permissions)
    (invariant : ∀ first second, Relation.EqvGen
      (GeneralOccurrenceSemantics.Equation request.plan request.bound request.expected)
      first second → test first = test second)
    (checked : modalReadout .possibility request state test = .decided false) :
    ¬ ∃ target, (GeneralOccurrenceSemantics.gslt request.plan request.bound request.expected).Step
      request.root target ∧ test target = true := by
  simp only [modalReadout] at checked
  split at checked
  next found => cases checked
  next absent =>
    split at checked
    next certified =>
      simp only [Bool.and_eq_true] at certified
      have admitted := sourceAdmission_sound certified.1 compiled
      intro succeeds
      have positive := (certified_outgoing_diamond admitted certified.2 test invariant).mpr succeeds
      exact absent positive
    next unfinished => cases checked

theorem complete_possibility_iff {request : Request} {state : State request}
    (admitted : Admitted request) (certificate : checkCertificate request state = true)
    (admission : sourceAdmission request = true) (test : Pattern → Bool)
    (invariant : ∀ first second, Relation.EqvGen
      (GeneralOccurrenceSemantics.Equation request.plan request.bound request.expected)
      first second → test first = test second) :
    modalReadout .possibility request state test = .decided true ↔
      ∃ target, (GeneralOccurrenceSemantics.gslt request.plan request.bound request.expected).Step
        request.root target ∧ test target = true := by
  rw [← certified_outgoing_diamond admitted certificate test invariant]
  simp only [modalReadout, admission, certificate, Bool.true_and, if_true]
  cases observed : (targets request state).any test <;> simp

theorem complete_outgoing_universal_iff {request : Request} {state : State request}
    (admitted : Admitted request) (certificate : checkCertificate request state = true)
    (admission : sourceAdmission request = true) (test : Pattern → Bool)
    (invariant : ∀ first second, Relation.EqvGen
      (GeneralOccurrenceSemantics.Equation request.plan request.bound request.expected)
      first second → test first = test second) :
    modalReadout .outgoingUniversal request state test = .decided true ↔
      ∀ target, (GeneralOccurrenceSemantics.gslt request.plan request.bound request.expected).Step
        request.root target → test target = true := by
  rw [← certified_outgoing_universal admitted certificate test invariant]
  simp only [modalReadout, admission, certificate, Bool.true_and, if_true]
  cases observed : (targets request state).all test <;> simp

theorem unfinished_empty_is_unknown (request : Request) (state : State request)
    (empty : state.answers = []) (unfinished : complete request state = false) (test : Pattern → Bool) :
    modalReadout .possibility request state test = .unknown := by
  simp [modalReadout, targets, empty, unfinished_certificate_rejected request state unfinished]

theorem generated_resume (generated : Generated) (bound : List TypeExpr) (expected : TypeExpr)
    (source : Pattern) (first second : Nat) :
    generated.execute bound expected source (first + second) =
      run _ second (generated.execute bound expected source first) :=
  run_add _ _ _ _

end Mettapedia.OSLF.NativeTypes.Generation
