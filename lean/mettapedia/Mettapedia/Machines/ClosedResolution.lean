import Mathlib.Data.List.Basic

/-!
# Captured resolution remains stable under ambient extension

This small call language isolates the dependency discipline required by a
protected inference service. Calls explicitly choose captured or ambient
resolution. Evaluation follows real callee bodies, so closing the entry point
alone is insufficient: every reachable captured body must be closed as well.

For a closed captured table, an induction on evaluation fuel proves exact
invariance under arbitrary changes to ambient bindings. The controls exercise
transitive calls and exhibit a compromised body that reaches ambient code.
The language is a resolution contract, not an HE or PeTTa evaluator, and does
not model native reflection or foreign-function memory access.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.ClosedResolution

inductive Reference where
  | captured (name : Nat)
  | ambient (name : Nat)
  deriving DecidableEq, Repr

inductive Code (Value : Type) where
  | input
  | literal (value : Value)
  | call (reference : Reference) (argument : Code Value)
  | ifEqual (left right yes no : Code Value)
  deriving Repr

namespace Code

variable {Value : Type}

def closed : Code Value → Bool
  | .input | .literal _ => true
  | .call (.captured _) argument => closed argument
  | .call (.ambient _) _ => false
  | .ifEqual left right yes no => closed left && closed right && closed yes && closed no

end Code

abbrev Table (Value : Type) := Nat → Option (Code Value)

def ClosedTable {Value : Type} (captured : Table Value) : Prop :=
  ∀ name body, captured name = some body → body.closed = true

def resolve {Value : Type} (captured ambient : Table Value) : Reference → Option (Code Value)
  | .captured name => captured name
  | .ambient name => ambient name

/-- Fuel bounds this reference execution. Exhaustion remains distinct from a
successful result; the invariance theorem concerns every fuel, not a guessed
termination bound. -/
def evaluate {Value : Type} [DecidableEq Value] :
    Nat → Table Value → Table Value → Code Value → Value → Option Value
  | 0, _, _, _, _ => none
  | _ + 1, _, _, .input, input => some input
  | _ + 1, _, _, .literal value, _ => some value
  | fuel + 1, captured, ambient, .call reference argument, input => do
      let value ← evaluate fuel captured ambient argument input
      let body ← resolve captured ambient reference
      evaluate fuel captured ambient body value
  | fuel + 1, captured, ambient, .ifEqual left right yes no, input => do
      let a ← evaluate fuel captured ambient left input
      let b ← evaluate fuel captured ambient right input
      evaluate fuel captured ambient (if a = b then yes else no) input

/-- Every helper call, branch and return is preserved, not only lookup at the
entry symbol. Ambient extension may change arbitrary bindings. -/
theorem evaluate_invariant {Value : Type} [DecidableEq Value]
    (captured : Table Value) (allClosed : ClosedTable captured)
    (ambient firstOther : Table Value) (fuel : Nat) (code : Code Value)
    (closed : code.closed = true) (input : Value) :
    evaluate fuel captured ambient code input = evaluate fuel captured firstOther code input := by
  induction fuel generalizing code input with
  | zero => rfl
  | succ fuel ih =>
      cases code with
      | input | literal => rfl
      | call reference argument =>
          cases reference with
          | ambient name => simp [Code.closed] at closed
          | captured name =>
              have argClosed : argument.closed = true := closed
              simp only [evaluate, ih argument argClosed input, resolve]
              cases value : evaluate fuel captured firstOther argument input with
              | none => rfl
              | some actual =>
                  cases body : captured name with
                  | none => rfl
                  | some next =>
                      exact ih next (allClosed name next body) actual
      | ifEqual left right yes no =>
          have parts : ((left.closed = true ∧ right.closed = true) ∧
              yes.closed = true) ∧ no.closed = true := by
            simpa only [Code.closed, Bool.and_eq_true] using closed
          obtain ⟨⟨⟨leftClosed, rightClosed⟩, yesClosed⟩, noClosed⟩ := parts
          simp only [evaluate, ih left leftClosed input, ih right rightClosed input]
          cases a : evaluate fuel captured firstOther left input with
          | none => rfl
          | some av =>
              cases b : evaluate fuel captured firstOther right input with
              | none => rfl
              | some bv =>
                  by_cases equal : av = bv
                  · simpa [equal] using ih yes yesClosed input
                  · simpa [equal] using ih no noClosed input

/-- A client may observe the result through any data-only function. This does
not assert that timing, private closures or native pointers are hidden. -/
theorem observation_invariant {Value Result : Type} [DecidableEq Value]
    (captured : Table Value) (allClosed : ClosedTable captured)
    (ambient other : Table Value) (fuel : Nat) (code : Code Value)
    (closed : code.closed = true) (input : Value) (observe : Value → Result) :
    (evaluate fuel captured ambient code input).map observe =
      (evaluate fuel captured other code input).map observe := by
  rw [evaluate_invariant captured allClosed ambient other fuel code closed input]

namespace Controls

def trusted : Table Nat
  | 0 => some (.call (.captured 1) .input)
  | 1 => some (.ifEqual .input (.literal 7) (.literal 1) (.literal 0))
  | _ => none

def ambientSafe : Table Nat := fun _ => some (.literal 0)
def ambientAttack : Table Nat := fun _ => some (.literal 1)
def entry : Code Nat := .call (.captured 0) .input

theorem trusted_closed : ClosedTable trusted := by
  intro name body found
  cases name with
  | zero => cases found; rfl
  | succ name =>
      cases name with
      | zero => cases found; rfl
      | succ name => simp [trusted] at found

theorem transitive_valid_check : evaluate 5 trusted ambientSafe entry 7 = some 1 := by decide
theorem transitive_invalid_check : evaluate 5 trusted ambientSafe entry 99 = some 0 := by decide

theorem arbitrary_extension_preserves_invalid_check (ambient : Table Nat) :
    evaluate 5 trusted ambient entry 99 = some 0 := by
  rw [evaluate_invariant trusted trusted_closed ambient ambientSafe 5 entry rfl 99]
  exact transitive_invalid_check

/-- Only the top-level reference was captured. Its helper escapes to the
ambient resolver, which can change the result used to authorize minting. -/
def compromised : Table Nat
  | 0 => some (.call (.ambient 1) .input)
  | _ => none

theorem entry_is_closed : entry.closed = true := rfl
theorem compromised_rejects_before_extension :
    evaluate 5 compromised ambientSafe entry 99 = some 0 := by decide
theorem compromised_accepts_after_extension :
    evaluate 5 compromised ambientAttack entry 99 = some 1 := by decide
theorem compromised_is_not_closed : ¬ ClosedTable compromised := by
  intro closed
  have impossible := closed 0 (.call (.ambient 1) .input) rfl
  cases impossible

end Controls

end Mettapedia.Machines.ClosedResolution
