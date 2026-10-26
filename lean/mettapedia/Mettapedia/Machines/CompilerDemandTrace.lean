import Mathlib.Tactic

/-!
# Compiler refusals across result demands

The reference interprets a finite compiler script. A separate observer records
whether the compiler inspected result demand. A stable terminal refusal before
such an inspection applies to either demand. Scalar-only refusals, transient
resource failures and recovered failures do not supply that certificate.
An explicit gate may instead reject a particular demand before its continuation;
the scalar and answer attempts can therefore refuse for different reasons.

`bind` represents dependent frontend work; `recover` keeps observations made by
an unsuccessful probe while replacing its handled error. This is a protocol
model, not a model of the native compiler's AST, allocator or source revisions.
Its application requires all demand reads to be observed and the remaining
inputs and source authority to stay fixed. Revision-scoped cache validity is a
separate obligation, as in `RevisionedQueryFacts`.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.CompilerDemandTrace

inductive Demand where
  | scalar | answers
  deriving DecidableEq, Repr

inductive Refusal where
  | stable (reason : Nat)
  | resource
  deriving DecidableEq, Repr

inductive Script (Plan : Type) where
  | done (plan : Plan)
  | refuse (reason : Refusal)
  | common (next : Script Plan)
  | demand (scalar answers : Script Plan)
  | gate (forbidden : Demand) (reason : Nat) (next : Script Plan)
  | bind (first : Script Plan) (next : Plan → Script Plan)
  | recover (first alternative : Script Plan)

variable {Plan : Type}

def reference (mode : Demand) : Script Plan → Except Refusal Plan
  | .done plan => .ok plan
  | .refuse reason => .error reason
  | .common next => reference mode next
  | .demand scalar answers =>
      match mode with
      | .scalar => reference mode scalar
      | .answers => reference mode answers
  | .gate forbidden reason next =>
      if mode = forbidden then .error (.stable reason) else reference mode next
  | .bind first next =>
      match reference mode first with
      | .error reason => .error reason
      | .ok plan => reference mode (next plan)
  | .recover first alternative =>
      match reference mode first with
      | .ok plan => .ok plan
      | .error _ => reference mode alternative

structure Report (Plan : Type) where
  result : Except Refusal Plan
  demandObserved : Bool
  deriving DecidableEq, Repr

def inspect (mode : Demand) : Script Plan → Report Plan
  | .done plan => ⟨.ok plan, false⟩
  | .refuse reason => ⟨.error reason, false⟩
  | .common next => inspect mode next
  | .demand scalar answers =>
      let branch := match mode with
        | .scalar => inspect mode scalar
        | .answers => inspect mode answers
      { branch with demandObserved := true }
  | .gate forbidden reason next =>
      let branch := if mode = forbidden then ⟨.error (.stable reason), false⟩
        else inspect mode next
      { branch with demandObserved := true }
  | .bind first next =>
      let head := inspect mode first
      match head.result with
      | .error _ => head
      | .ok plan =>
          let tail := inspect mode (next plan)
          { tail with demandObserved := head.demandObserved || tail.demandObserved }
  | .recover first alternative =>
      let head := inspect mode first
      match head.result with
      | .ok _ => head
      | .error _ =>
          let tail := inspect mode alternative
          { tail with demandObserved := head.demandObserved || tail.demandObserved }

theorem inspect_refines (mode : Demand) (script : Script Plan) :
    (inspect mode script).result = reference mode script := by
  induction script with
  | done plan => rfl
  | refuse reason => rfl
  | common next ih => exact ih
  | demand scalar answers ihs iha =>
      cases mode <;> simpa [inspect, reference] using (by assumption)
  | gate forbidden reason next ih =>
      by_cases same : mode = forbidden
      · simp [inspect, reference, same]
      · simpa [inspect, reference, same] using ih
  | bind first next ihFirst ihNext =>
      cases found : reference mode first with
      | error reason =>
          have observed := ihFirst.trans found
          simp [inspect, reference, found, observed]
      | ok plan =>
          have observed := ihFirst.trans found
          simpa [inspect, reference, found, observed] using ihNext plan
  | recover first alternative ihFirst ihAlternative =>
      cases found : reference mode first with
      | error reason =>
          have observed := ihFirst.trans found
          simpa [inspect, reference, found, observed] using ihAlternative
      | ok plan =>
          have observed := ihFirst.trans found
          simp [inspect, reference, found, observed]

/-- Before the first demand read, the whole observed compiler execution is
independent of demand, including dependent work and handled probes. -/
theorem unobserved_same (script : Script Plan) (first second : Demand)
    (unobserved : (inspect first script).demandObserved = false) :
    inspect second script = inspect first script := by
  induction script with
  | done plan => rfl
  | refuse reason => rfl
  | common next ih => exact ih unobserved
  | demand scalar answers ihs iha =>
      cases first <;> simp [inspect] at unobserved
  | gate forbidden reason next ih =>
      by_cases same : first = forbidden <;> simp [inspect, same] at unobserved
  | bind probe next ihPrefix ihNext =>
      cases found : (inspect first probe).result with
      | error reason =>
          have before : (inspect first probe).demandObserved = false := by
            simpa [inspect, found] using unobserved
          simp [inspect, ihPrefix before, found]
      | ok plan =>
          have both : (inspect first probe).demandObserved = false ∧
              (inspect first (next plan)).demandObserved = false := by
            simpa [inspect, found, Bool.or_eq_false_iff] using unobserved
          simp [inspect, ihPrefix both.1, found, ihNext plan both.2]
  | recover probe alternative ihPrefix ihAlternative =>
      cases found : (inspect first probe).result with
      | ok plan =>
          have before : (inspect first probe).demandObserved = false := by
            simpa [inspect, found] using unobserved
          simp [inspect, ihPrefix before, found]
      | error reason =>
          have both : (inspect first probe).demandObserved = false ∧
              (inspect first alternative).demandObserved = false := by
            simpa [inspect, found, Bool.or_eq_false_iff] using unobserved
          simp [inspect, ihPrefix both.1, found, ihAlternative both.2]

def Report.sharedRefusal (report : Report Plan) : Option Nat :=
  if report.demandObserved then none
  else match report.result with
    | .error (.stable reason) => some reason
    | _ => none

/-- The certificate licenses the other demand's same stable refusal. It is
not a statement that any failed scalar compilation rejects answer production. -/
theorem shared_refusal_sound (script : Script Plan) (first second : Demand)
    (reason : Nat) (certified : (inspect first script).sharedRefusal = some reason) :
    reference second script = .error (.stable reason) := by
  have unobserved : (inspect first script).demandObserved = false := by
    cases h : (inspect first script).demandObserved <;>
      simp_all [Report.sharedRefusal]
  have result : (inspect first script).result = .error (.stable reason) := by
    cases h : (inspect first script).result with
    | ok plan => simp [Report.sharedRefusal, unobserved, h] at certified
    | error refusal =>
        cases refusal <;> simp_all [Report.sharedRefusal]
  rw [← inspect_refines, unobserved_same script first second unobserved, result]

/-- An explicit gate supplies a demand-specific refusal before interpreting
its continuation. A common dependent prefix may carry that fact, but an
arbitrary demand branch or handled failure cannot.

The repeated inspections here describe the mathematical protocol; this is not
a native cost claim or a requirement to rerun compiler work. -/
def forbiddenBeforeRead (mode : Demand) : Script Plan → Option (Demand × Nat)
  | .done _ | .refuse _ => none
  | .common next => forbiddenBeforeRead mode next
  | .demand _ _ => none
  | .gate forbidden reason _ => some (forbidden, reason)
  | .bind first next =>
      match forbiddenBeforeRead mode first with
      | some fact => some fact
      | none =>
          let head := inspect mode first
          if head.demandObserved then none
          else match head.result with
            | .error _ => none
            | .ok plan => forbiddenBeforeRead mode (next plan)
  | .recover first alternative =>
      let head := inspect mode first
      if head.demandObserved then none
      else match head.result with
        | .ok _ => none
        | .error _ => forbiddenBeforeRead mode alternative

theorem forbidden_before_read_sound (script : Script Plan) (mode target : Demand)
    (reason : Nat) (certified : forbiddenBeforeRead mode script = some (target, reason)) :
    reference target script = .error (.stable reason) := by
  induction script with
  | done plan => simp [forbiddenBeforeRead] at certified
  | refuse refusal => simp [forbiddenBeforeRead] at certified
  | common next ih => exact ih certified
  | demand scalar answers ihs iha => simp [forbiddenBeforeRead] at certified
  | gate forbidden why next ih =>
      have same : forbidden = target ∧ why = reason := by
        simpa [forbiddenBeforeRead] using certified
      simp [reference, same.1, same.2]
  | bind first next ihFirst ihNext =>
      cases fact : forbiddenBeforeRead mode first with
      | some known =>
          have known : forbiddenBeforeRead mode first = some (target, reason) := by
            simpa [forbiddenBeforeRead, fact] using certified
          simp [reference, ihFirst known]
      | none =>
          cases seen : (inspect mode first).demandObserved with
          | true => simp [forbiddenBeforeRead, fact, seen] at certified
          | false =>
              cases found : (inspect mode first).result with
              | error refusal => simp [forbiddenBeforeRead, fact, seen, found] at certified
              | ok plan =>
                  have prefixResult : reference target first = .ok plan := by
                    rw [← inspect_refines, unobserved_same first mode target seen, found]
                  have later : forbiddenBeforeRead mode (next plan) = some (target, reason) := by
                    simpa [forbiddenBeforeRead, fact, seen, found] using certified
                  simp [reference, prefixResult, ihNext plan later]
  | recover first alternative ihFirst ihAlternative =>
      cases seen : (inspect mode first).demandObserved with
      | true => simp [forbiddenBeforeRead, seen] at certified
      | false =>
          cases found : (inspect mode first).result with
          | ok plan => simp [forbiddenBeforeRead, seen, found] at certified
          | error refusal =>
              have prefixResult : reference target first = .error refusal := by
                rw [← inspect_refines, unobserved_same first mode target seen, found]
              have later : forbiddenBeforeRead mode alternative = some (target, reason) := by
                simpa [forbiddenBeforeRead, seen, found] using certified
              simp [reference, prefixResult, ihAlternative later]

/-- The scalar attempt may certify answer refusal through either a common
terminal refusal or an explicit answer exclusion. -/
def answerRefusal (script : Script Plan) : Option Nat :=
  match (inspect .scalar script).sharedRefusal with
  | some reason => some reason
  | none => match forbiddenBeforeRead .scalar script with
    | some (.answers, reason) => some reason
    | _ => none

theorem answer_refusal_sound (script : Script Plan) (reason : Nat)
    (certified : answerRefusal script = some reason) :
    reference .answers script = .error (.stable reason) := by
  cases commonFact : (inspect .scalar script).sharedRefusal with
  | some why =>
      have same : why = reason := by simpa [answerRefusal, commonFact] using certified
      exact shared_refusal_sound script .scalar .answers reason (same ▸ commonFact)
  | none =>
      cases gateFact : forbiddenBeforeRead .scalar script with
      | none => simp [answerRefusal, commonFact, gateFact] at certified
      | some fact =>
          rcases fact with ⟨target, why⟩
          cases target with
          | scalar => simp [answerRefusal, commonFact, gateFact] at certified
          | answers =>
              have same : why = reason := by
                simpa [answerRefusal, commonFact, gateFact] using certified
              exact forbidden_before_read_sound script .scalar .answers reason (same ▸ gateFact)

namespace Controls

def shared : Script Nat :=
  .common (.bind (.done 3) (fun value => .common (.refuse (.stable (value + 4)))))

theorem shared_frontend_refusal :
    (inspect .scalar shared).sharedRefusal = some 7 ∧
    reference .answers shared = .error (.stable 7) := by
  simp [shared, inspect, reference, Report.sharedRefusal]

def scalarOnly : Script Nat := .demand (.refuse (.stable 7)) (.done 42)

theorem scalar_refusal_does_not_poison_answers :
    (inspect .scalar scalarOnly).sharedRefusal = none ∧
    reference .scalar scalarOnly = .error (.stable 7) ∧
    reference .answers scalarOnly = .ok 42 := by decide

theorem resource_refusal_is_not_stable :
    (inspect .scalar (.common (.refuse .resource) : Script Nat)).sharedRefusal = none := by
  decide

def recovered : Script Nat :=
  .recover (.refuse (.stable 7)) (.demand (.refuse .resource) (.done 42))

theorem recovered_refusal_cannot_certify_later_failure :
    (inspect .scalar recovered).sharedRefusal = none ∧
    reference .scalar recovered = .error .resource ∧
    reference .answers recovered = .ok 42 := by decide

theorem recovered_success_is_not_a_refusal :
    (inspect .answers (.recover (.refuse (.stable 7)) (.done 42))).sharedRefusal = none := by
  decide

def singleOnly : Script Nat := .gate .answers 11 (.refuse (.stable 7))

theorem explicit_gate_does_not_recompile_the_other_demand :
    forbiddenBeforeRead .scalar singleOnly = some (.answers, 11) ∧
    answerRefusal singleOnly = some 11 ∧
    reference .scalar singleOnly = .error (.stable 7) ∧
    reference .answers singleOnly = .error (.stable 11) := by decide

theorem earlier_demand_branch_prevents_gate_export :
    let script : Script Nat := .demand (.gate .answers 11 (.done 1)) (.done 42)
    forbiddenBeforeRead .scalar script = none ∧ reference .answers script = .ok 42 := by decide

theorem handled_gate_is_not_a_global_refusal :
    let script : Script Nat := .recover (.gate .answers 11 (.done 1)) (.done 42)
    forbiddenBeforeRead .scalar script = none ∧ reference .answers script = .ok 42 := by decide

end Controls
end Mettapedia.Machines.CompilerDemandTrace

#print axioms Mettapedia.Machines.CompilerDemandTrace.inspect_refines
#print axioms Mettapedia.Machines.CompilerDemandTrace.unobserved_same
#print axioms Mettapedia.Machines.CompilerDemandTrace.shared_refusal_sound
#print axioms Mettapedia.Machines.CompilerDemandTrace.Controls.shared_frontend_refusal
#print axioms Mettapedia.Machines.CompilerDemandTrace.Controls.scalar_refusal_does_not_poison_answers
#print axioms Mettapedia.Machines.CompilerDemandTrace.Controls.resource_refusal_is_not_stable
#print axioms Mettapedia.Machines.CompilerDemandTrace.Controls.recovered_refusal_cannot_certify_later_failure
#print axioms Mettapedia.Machines.CompilerDemandTrace.Controls.recovered_success_is_not_a_refusal
#print axioms Mettapedia.Machines.CompilerDemandTrace.forbidden_before_read_sound
#print axioms Mettapedia.Machines.CompilerDemandTrace.answer_refusal_sound
#print axioms Mettapedia.Machines.CompilerDemandTrace.Controls.explicit_gate_does_not_recompile_the_other_demand
#print axioms Mettapedia.Machines.CompilerDemandTrace.Controls.earlier_demand_branch_prevents_gate_export
#print axioms Mettapedia.Machines.CompilerDemandTrace.Controls.handled_gate_is_not_a_global_refusal
