import Mettapedia.Languages.MeTTa.PeTTa.CoherentTypeQuery
import Mettapedia.Machines.ConstraintPropagation.ResidualChecks

/-!
# Conditional PeTTa type checks

A check on a logical slot is retained until its value is available. A ready
check uses the independently defined finite resolved contract. The store
simplifier preserves every completion of the partial bindings, and rejects
a completion that binds a Number-constrained slot to a string.

This is a source-level model of retained checks and their answer semantics.
It is not a correspondence theorem for SWI's freeze/2, open polymorphic
unification, native closures, mutable classifiers, or the C implementation.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.ResidualTypeChecks

open Mettapedia.Machines.ConstraintPropagation.Readiness.Bindings (Extends Refines)
open MainlineTypeQueryGSLT
open Mettapedia.Machines.ConstraintPropagation.ResidualChecks

inductive Reference where
  | value (atom : Term)
  | slot (name : String)
  deriving DecidableEq

structure Requirement where
  value : Reference
  expected : Reference
  deriving DecidableEq

abbrev PartialBindings := String → Option Term
abbrev Completion := String → Term

def Reference.resolve (bindings : PartialBindings) : Reference → Option Term
  | .value atom => some atom
  | .slot name => bindings name

def Reference.denote (completion : Completion) : Reference → Term
  | .value atom => atom
  | .slot name => completion name

theorem resolve_sound (bindings : PartialBindings) (completion : Completion)
    (extension : Extends bindings completion) (ref : Reference) (atom : Term)
    (resolved : ref.resolve bindings = some atom) : ref.denote completion = atom := by
  cases ref with
  | value value => simpa [Reference.resolve, Reference.denote] using resolved
  | slot name => exact extension name atom resolved

def Requirement.Holds (snapshot : Snapshot) (completion : Completion)
    (requirement : Requirement) : Prop :=
  CoherentTypeQuery.Check snapshot
    (requirement.value.denote completion) (requirement.expected.denote completion)

def probe (snapshot : Snapshot) (bindings : PartialBindings)
    (requirement : Requirement) : Option Bool := do
  let atom ← requirement.value.resolve bindings
  let expected ← requirement.expected.resolve bindings
  return CoherentTypeQuery.check snapshot atom expected

theorem probe_correct (snapshot : Snapshot) (bindings : PartialBindings)
    (completion : Completion) (extension : Extends bindings completion)
    (requirement : Requirement) (verdict : Bool)
    (ready : probe snapshot bindings requirement = some verdict) :
    requirement.Holds snapshot completion ↔ verdict = true := by
  unfold probe at ready
  cases hv : requirement.value.resolve bindings with
  | none => simp [hv] at ready
  | some atom =>
    cases ht : requirement.expected.resolve bindings with
    | none => simp [hv, ht] at ready
    | some expected =>
      have exactVerdict : CoherentTypeQuery.check snapshot atom expected = verdict := by
        simpa [hv, ht] using ready
      unfold Requirement.Holds
      rw [resolve_sound bindings completion extension requirement.value atom hv,
          resolve_sound bindings completion extension requirement.expected expected ht,
          ← CoherentTypeQuery.check_iff, exactVerdict]

theorem discharge_preserves_completions (snapshot : Snapshot) (bindings : PartialBindings)
    (completion : Completion) (extension : Extends bindings completion)
    (requirements : List Requirement) :
    OutcomeHolds (Requirement.Holds snapshot completion)
      (discharge (probe snapshot bindings) requirements) ↔
    Holds (Requirement.Holds snapshot completion) requirements :=
  discharge_correct _ _ (probe_correct snapshot bindings completion extension) requirements

theorem posting_commutes (snapshot : Snapshot) (completion : Completion)
    (one two : Requirement) (rest : List Requirement) :
    Holds (Requirement.Holds snapshot completion) (one :: two :: rest) ↔
    Holds (Requirement.Holds snapshot completion) (two :: one :: rest) :=
  holds_perm _ _ _ (List.Perm.swap _ _ _)

theorem resolve_refines (early late : PartialBindings) (refines : Refines early late)
    (ref : Reference) (atom : Term) (ready : ref.resolve early = some atom) :
    ref.resolve late = some atom := by
  cases ref with
  | value value => exact ready
  | slot name => exact refines name atom ready

theorem probe_refines (snapshot : Snapshot) (early late : PartialBindings)
    (refines : Refines early late) (requirement : Requirement) (verdict : Bool)
    (ready : probe snapshot early requirement = some verdict) :
    probe snapshot late requirement = some verdict := by
  unfold probe at ready ⊢
  cases hv : requirement.value.resolve early with
  | none => simp [hv] at ready
  | some atom =>
    cases ht : requirement.expected.resolve early with
    | none => simp [hv, ht] at ready
    | some expected =>
      have hv' := resolve_refines early late refines requirement.value atom hv
      have ht' := resolve_refines early late refines requirement.expected expected ht
      simpa [hv, ht, hv', ht'] using ready

theorem incremental_checking_matches_final (snapshot : Snapshot)
    (early late : PartialBindings) (refines : Refines early late)
    (requirements : List Requirement) :
    (discharge (probe snapshot early) requirements).bind
      (discharge (probe snapshot late)) = discharge (probe snapshot late) requirements :=
  discharge_compose _ _ (probe_refines snapshot early late refines) requirements

namespace Controls

def snapshot : Snapshot := {
  revision := 0
  declarations := []
  annotations := []
  registeredFunctions := []
}

def numberRequirement : Requirement := ⟨.slot "x", .value (.atom "Number")⟩
def stringRequirement : Requirement := ⟨.slot "x", .value (.atom "String")⟩

def unbound : PartialBindings := fun _ => none
def numberBound : PartialBindings := fun name => if name = "x" then some (.number "3") else none
def stringBound : PartialBindings := fun name => if name = "x" then some (.string "s") else none

theorem unbound_is_retained :
    discharge (probe snapshot unbound) [numberRequirement] = some [numberRequirement] := by
  decide

theorem numeric_binding_discharges :
    discharge (probe snapshot numberBound) [numberRequirement] = some [] := by
  decide

theorem string_binding_refutes :
    discharge (probe snapshot stringBound) [numberRequirement] = none := by
  decide

def requiresNumber : Reference × List Requirement := ⟨.slot "x", [numberRequirement]⟩
def requiresString : Reference × List Requirement := ⟨.slot "x", [stringRequirement]⟩

/-- Equal visible terms are insufficient for identifying conditional answers. -/
theorem visible_value_does_not_determine_acceptance :
    requiresNumber.1 = requiresString.1 ∧
    discharge (probe snapshot numberBound) requiresNumber.2 = some [] ∧
    discharge (probe snapshot numberBound) requiresString.2 = none := by
  decide

end Controls

#print axioms discharge_preserves_completions
#print axioms posting_commutes
#print axioms incremental_checking_matches_final
#print axioms Controls.string_binding_refutes
#print axioms Controls.visible_value_does_not_determine_acceptance

end Mettapedia.Languages.MeTTa.PeTTa.ResidualTypeChecks
