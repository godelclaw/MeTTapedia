import Mettapedia.Logic.LP.Substitution
import Mathlib.Tactic.DeriveFintype

/-!
# Instantiation entry contracts for relational calls

Modes describe the current instantiated terms, separately from value types.
An output must be a plain unconstrained variable with exactly one occurrence
in the complete call vector. Thus aliases and nested sharing are visible;
testing only the root with a variable predicate is insufficient.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.CheckedInstantiation

open Mettapedia.Logic.LP

inductive Mode where
  | input | output | any
  deriving DecidableEq, Repr

variable {σ : LPSignature} [DecidableEq σ.vars]

def occurrences (name : σ.vars) : Term σ → Nat
  | .var other => if name = other then 1 else 0
  | .const _ => 0
  | .app _ children => ∑ index, occurrences name (children index)

def vectorOccurrences (name : σ.vars) (values : List (Term σ)) : Nat :=
  (values.map (occurrences name)).sum

inductive Admitted (constraints : Finset σ.vars) (values : List (Term σ)) :
    Mode → Term σ → Prop where
  | input {value : Term σ} : value.isGround → Admitted constraints values .input value
  | output {name : σ.vars} : name ∉ constraints → vectorOccurrences name values = 1 →
      Admitted constraints values .output (.var name)
  | any (value : Term σ) : Admitted constraints values .any value

def check (constraints : Finset σ.vars) (values : List (Term σ)) : Mode → Term σ → Bool
  | .input, value => decide (value.freeVars = ∅)
  | .output, .var name => decide (name ∉ constraints ∧ vectorOccurrences name values = 1)
  | .output, _ => false
  | .any, _ => true

theorem check_exact (constraints : Finset σ.vars) (values : List (Term σ))
    (mode : Mode) (value : Term σ) :
    check constraints values mode value = true ↔ Admitted constraints values mode value := by
  cases mode with
  | input =>
      simp only [check,decide_eq_true_eq,← Term.isGround_iff_freeVars_empty]
      constructor
      · exact Admitted.input
      · intro admitted; cases admitted with | input ground => exact ground
  | output =>
      cases value with
      | var name =>
          simp only [check,decide_eq_true_eq]
          constructor
          · rintro ⟨plain,fresh⟩; exact .output plain fresh
          · intro admitted; cases admitted with | output plain fresh => exact ⟨plain,fresh⟩
      | const name =>
          constructor
          · simp [check]
          · intro impossible; cases impossible
      | app function children =>
          constructor
          · simp [check]
          · intro impossible; cases impossible
  | any =>
      constructor
      · intro _; exact .any value
      · intro _; rfl

inductive VectorAdmitted (constraints : Finset σ.vars) (whole : List (Term σ)) :
    List Mode → List (Term σ) → Prop where
  | nil : VectorAdmitted constraints whole [] []
  | cons {mode : Mode} {value : Term σ} {modes : List Mode} {values : List (Term σ)} :
      Admitted constraints whole mode value → VectorAdmitted constraints whole modes values →
      VectorAdmitted constraints whole (mode :: modes) (value :: values)

def checkVector (constraints : Finset σ.vars) (whole : List (Term σ)) :
    List Mode → List (Term σ) → Bool
  | [], [] => true
  | mode :: modes, value :: values =>
      check constraints whole mode value && checkVector constraints whole modes values
  | _, _ => false

theorem checkVector_exact (constraints : Finset σ.vars) (whole : List (Term σ))
    (modes : List Mode) (values : List (Term σ)) :
    checkVector constraints whole modes values = true ↔ VectorAdmitted constraints whole modes values := by
  induction modes generalizing values with
  | nil =>
      cases values with
      | nil => exact ⟨fun _ => .nil,fun _ => rfl⟩
      | cons value values =>
          constructor
          · simp [checkVector]
          · intro impossible; cases impossible
  | cons mode modes ih =>
      cases values with
      | nil =>
          constructor
          · simp [checkVector]
          · intro impossible; cases impossible
      | cons value values =>
          simp only [checkVector,Bool.and_eq_true,check_exact,ih]
          constructor
          · rintro ⟨head,tail⟩; exact .cons head tail
          · intro admitted; cases admitted with | cons head tail => exact ⟨head,tail⟩

omit [DecidableEq σ.vars] in
/-- Later bindings cannot change a ground input. They may still change open
outputs; output freshness is an entry property, not a permanent invariant. -/
theorem ground_input_stable (value : Term σ) (ground : value.isGround) (later : Subst σ) :
    later.applyTerm value = value := by
  induction value with
  | var name => cases ground
  | const name => rfl
  | app function children ih =>
      simp only [Subst.applyTerm]
      congr 1
      funext index
      exact ih index (ground index)

namespace Controls

abbrev sig : LPSignature where
  constants := String
  vars := Nat
  relationSymbols := Unit
  relationArity _ := 0
  functionSymbols := Nat
  functionArity := id

def x : Term sig := .var 0
def number : Term sig := .const "3"
def wrapped : Term sig := .app 1 (fun _ => x)

theorem fresh_output : check (σ := sig) ∅ [number,x] .output x = true := by decide
theorem alias_is_not_fresh : check (σ := sig) ∅ [x,x] .output x = false := by decide
theorem nested_sharing_is_not_fresh :
    check (σ := sig) ∅ [wrapped,x] .output x = false := by decide
theorem constrained_is_not_fresh : check (σ := sig) {0} [x] .output x = false := by decide
theorem any_does_not_establish_groundness :
    check (σ := sig) ∅ [x] .any x = true ∧ check (σ := sig) ∅ [x] .input x = false := by decide

end Controls

#print axioms check_exact
#print axioms checkVector_exact
#print axioms ground_input_stable

end Mettapedia.Languages.MeTTa.PeTTa.CheckedInstantiation
