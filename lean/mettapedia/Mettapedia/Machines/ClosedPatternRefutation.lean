import Mettapedia.Machines.CallerCursorJoin

/-!
# Conservative refutation before relational matching

A closed constructor fragment has literal leaves, pairs and binding patterns.
Matching visits the left component first and can leave a partial binding on
failure. Refutation inspects the right component first without binding. A
bounded refuter falls back to full matching whenever its allowance runs out.

The result is an observation refinement: rejected working bindings stay
private, and every successful match survives selection with the same bindings.
The C n-ary stack, list views, representation tags and native graph facts have
separate correspondence obligations.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.ClosedPatternRefutation

inductive Data (Leaf : Type) where
  | leaf (value : Leaf)
  | pair (left right : Data Leaf)
  deriving DecidableEq, Repr

inductive Pattern (Key Leaf : Type) where
  | bind (key : Key)
  | literal (value : Data Leaf)
  | pair (left right : Pattern Key Leaf)
  deriving DecidableEq, Repr

variable {Key Leaf : Type} [DecidableEq Key] [DecidableEq Leaf]

abbrev Environment (Key Leaf : Type) := CallerCursorJoin.Bindings Key (Data Leaf)

abbrev Result (Key Leaf : Type) := CallerCursorJoin.MatchResult Key (Data Leaf)

def exactMatch : Pattern Key Leaf → Data Leaf → Environment Key Leaf → Result Key Leaf
  | .bind key, value, env => CallerCursorJoin.slot key env value
  | .literal wanted, value, env => ⟨env, decide (value = wanted)⟩
  | .pair left right, .pair first second, env =>
      let firstMatch := exactMatch left first env
      if firstMatch.accepted then exactMatch right second firstMatch.bindings else firstMatch
  | .pair _ _, .leaf _, env => ⟨env, false⟩

def refutes : Nat → Pattern Key Leaf → Data Leaf → Bool
  | 0, _, _ => false
  | _ + 1, .bind _, _ => false
  | _ + 1, .literal wanted, value => !(decide (value = wanted))
  | budget + 1, .pair left right, .pair first second =>
      refutes budget right second || refutes budget left first
  | _ + 1, .pair _ _, .leaf _ => true

theorem refutation_sound (budget : Nat) (pattern : Pattern Key Leaf)
    (value : Data Leaf) (env : Environment Key Leaf)
    (rejected : refutes budget pattern value = true) :
    (exactMatch pattern value env).accepted = false := by
  induction budget generalizing pattern value env with
  | zero => simp [refutes] at rejected
  | succ budget ih =>
      cases pattern with
      | bind key => simp [refutes] at rejected
      | literal wanted => simpa [refutes, exactMatch] using rejected
      | pair left right =>
          cases value with
          | leaf value => rfl
          | pair first second =>
              cases firstMatch : exactMatch left first env with
              | mk bindings accepted =>
                  cases accepted with
                  | false => simp [exactMatch, firstMatch]
                  | true =>
                      have alternatives := Bool.or_eq_true_iff.mp rejected
                      rcases alternatives with rightRejected | leftRejected
                      · simpa [exactMatch, firstMatch] using ih right second bindings rightRejected
                      · have impossible := ih left first env leftRejected
                        simp [firstMatch] at impossible

def selected (budget : Nat) (pattern : Pattern Key Leaf) (value : Data Leaf)
    (env : Environment Key Leaf) : Result Key Leaf :=
  if refutes budget pattern value then ⟨env, false⟩ else exactMatch pattern value env

def observe (result : Result Key Leaf) : Option (Environment Key Leaf) :=
  if result.accepted then some result.bindings else none

theorem selected_refines (budget : Nat) (pattern : Pattern Key Leaf)
    (value : Data Leaf) (env : Environment Key Leaf) :
    observe (selected budget pattern value env) = observe (exactMatch pattern value env) := by
  by_cases rejected : refutes budget pattern value = true
  · simp [selected, rejected, observe, refutation_sound budget pattern value env rejected]
  · simp [selected, rejected]

theorem successful_match_is_not_refuted (budget : Nat) (pattern : Pattern Key Leaf)
    (value : Data Leaf) (env : Environment Key Leaf)
    (accepted : (exactMatch pattern value env).accepted = true) :
    refutes budget pattern value = false := by
  cases rejected : refutes budget pattern value with
  | false => rfl
  | true => have bad := refutation_sound budget pattern value env rejected
            simp [accepted] at bad

theorem zero_allowance_keeps_exact_matching (pattern : Pattern Key Leaf)
    (value : Data Leaf) (env : Environment Key Leaf) :
    selected 0 pattern value env = exactMatch pattern value env := by
  simp [selected, refutes]

inductive Realizes : Pattern Key Leaf → Data Leaf → Prop where
  | bind (key : Key) (value : Data Leaf) : Realizes (.bind key) value
  | literal (value : Data Leaf) : Realizes (.literal value) value
  | pair {left right : Pattern Key Leaf} {first second : Data Leaf}
      (leftRealizes : Realizes left first) (rightRealizes : Realizes right second) :
      Realizes (.pair left right) (.pair first second)

/-- Unknown output operands are wildcards. They need not yet be constructed. -/
def refutesShape : Nat → Pattern Key Leaf → Pattern Key Leaf → Bool
  | 0, _, _ => false
  | budget + 1, pattern, .literal value => refutes (budget + 1) pattern value
  | _ + 1, _, .bind _ => false
  | budget + 1, .pair left right, .pair first second =>
      refutesShape budget right second || refutesShape budget left first
  | _ + 1, _, .pair _ _ => false

theorem symbolic_refutation_sound (budget : Nat) (pattern shape : Pattern Key Leaf)
    (value : Data Leaf) (env : Environment Key Leaf) (realized : Realizes shape value)
    (rejected : refutesShape budget pattern shape = true) :
    (exactMatch pattern value env).accepted = false := by
  induction budget generalizing pattern shape value env with
  | zero => simp [refutesShape] at rejected
  | succ budget ih =>
      cases shape with
      | bind key => simp [refutesShape] at rejected
      | literal actual =>
          cases realized
          exact refutation_sound (budget + 1) pattern _ env rejected
      | pair firstShape secondShape =>
          cases pattern with
          | bind key => simp [refutesShape] at rejected
          | literal wanted => simp [refutesShape] at rejected
          | pair left right =>
              cases realized with
              | pair leftRealizes rightRealizes =>
                  rename_i leftValue rightValue
                  cases headMatch : exactMatch left leftValue env with
                  | mk bindings accepted =>
                      cases accepted with
                      | false => simp [exactMatch, headMatch]
                      | true =>
                          have alternatives := Bool.or_eq_true_iff.mp rejected
                          rcases alternatives with rightRejected | leftRejected
                          · simpa [exactMatch, headMatch] using
                              ih right secondShape _ bindings rightRealizes rightRejected
                          · have bad := ih left firstShape _ env leftRealizes leftRejected
                            simp [headMatch] at bad

def selectedShape (budget : Nat) (pattern shape : Pattern Key Leaf)
    (value : Data Leaf) (env : Environment Key Leaf) : Result Key Leaf :=
  if refutesShape budget pattern shape then ⟨env, false⟩ else exactMatch pattern value env

theorem symbolic_selection_refines (budget : Nat) (pattern shape : Pattern Key Leaf)
    (value : Data Leaf) (env : Environment Key Leaf) (realized : Realizes shape value) :
    observe (selectedShape budget pattern shape value env) = observe (exactMatch pattern value env) := by
  by_cases rejected : refutesShape budget pattern shape = true
  · simp [selectedShape, rejected, observe,
      symbolic_refutation_sound budget pattern shape value env realized rejected]
  · simp [selectedShape, rejected]

namespace Controls

def empty : Environment Nat Nat := fun _ => none

theorem later_literal_refutes_without_binding :
    refutes 2 (.pair (.bind 0) (.literal (.leaf 9))) (.pair (.leaf 7) (.leaf 7)) = true ∧
    (selected 2 (.pair (.bind 0) (.literal (.leaf 9)))
      (.pair (.leaf 7) (.leaf 7)) empty).bindings 0 = none := by decide +kernel

theorem binder_is_not_a_literal :
    refutes 8 (.bind 0) (.leaf 7 : Data Nat) = false ∧
    (exactMatch (.bind 0) (.leaf 7) empty).accepted = true := by decide +kernel

theorem nonlinear_failure_still_uses_matching :
    refutes 4 (.pair (.bind 0) (.bind 0)) (.pair (.leaf 7) (.leaf 9 : Data Nat)) = false ∧
    (selected 4 (.pair (.bind 0) (.bind 0))
      (.pair (.leaf 7) (.leaf 9)) empty).accepted = false ∧
    (exactMatch (.pair (.bind 0) (.bind 0))
      (.pair (.leaf 7) (.leaf 9)) empty).bindings 0 = some (.leaf 7) := by decide +kernel

theorem exhausted_refuter_cannot_drop_a_match :
    (selected 0 (.pair (.bind 0) (.bind 0))
      (.pair (.leaf 9) (.leaf 9)) empty).accepted = true := by decide +kernel

theorem unknown_output_cannot_be_refuted :
    refutesShape 8 (.literal (.leaf 9)) (.bind 1 : Pattern Nat Nat) = false := by decide +kernel

theorem fixed_output_can_be_refuted_before_construction :
    refutesShape 2 (.pair (.bind 0) (.literal (.leaf 9)))
      (.pair (.bind 1) (.literal (.leaf 7)) : Pattern Nat Nat) = true := by decide +kernel

theorem nonlinear_output_retains_exact_matching :
    refutesShape 4 (.pair (.bind 0) (.bind 0))
      (.pair (.literal (.leaf 7)) (.literal (.leaf 9)) : Pattern Nat Nat) = false := by
  decide +kernel

theorem an_unknown_output_can_realize_a_match :
    (selectedShape 8 (.literal (.leaf 9)) (.bind 1) (.leaf 9) empty).accepted = true ∧
    Realizes (.bind 1 : Pattern Nat Nat) (.leaf 9) := by
  constructor
  · decide +kernel
  · exact .bind 1 (.leaf 9)

end Controls
end Mettapedia.Machines.ClosedPatternRefutation
