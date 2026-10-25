import Mettapedia.Languages.MM0.HOLKernelTypingRules

/-!
# Maintained MM0 HOL logical and equality inference schemas

The twenty-one declarations retain their actual formal-parameter order,
ordered premises, native context conjunction and object Boolean operations.
Boolean equivalence is a separate declared abbreviation reference; converting
it to intrinsic Boolean equality requires its checked definition body.
Availability of a theorem header is separate from sequential theory admission.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MM0.HOLKernelInferenceRules

open Kernel HOLKernelSyntax HOLKernelJudgment HOLKernelTypingRules

def equality (references : Symbol → Nat) (type first second : Preterm) : Preterm :=
  applySymbol references .eqc [type, first, second]

def equivalence (reference : Nat) (first second : Preterm) : Preterm :=
  Preterm.applyArgs (.term reference) [first, second]

inductive Rule where
  | truth
  | contradiction
  | conjunctionIntroduction
  | conjunctionLeft
  | conjunctionRight
  | disjunctionLeft
  | disjunctionRight
  | disjunctionElimination
  | implicationIntroduction
  | implicationElimination
  | negationIntroduction
  | negationElimination
  | reflexivity
  | symmetry
  | transitivity
  | propositionalExtensionality
  | equalityImplicationLeft
  | equalityImplicationRight
  | applicationFunction
  | applicationArgument
  | booleanEqualityElimination
  deriving DecidableEq, Repr

def Rule.all : List Rule :=
  [.truth, .contradiction, .conjunctionIntroduction, .conjunctionLeft, .conjunctionRight, .disjunctionLeft, .disjunctionRight, .disjunctionElimination, .implicationIntroduction, .implicationElimination, .negationIntroduction, .negationElimination, .reflexivity, .symmetry, .transitivity, .propositionalExtensionality, .equalityImplicationLeft, .equalityImplicationRight, .applicationFunction, .applicationArgument, .booleanEqualityElimination]

theorem Rule.mem_all (rule : Rule) : rule ∈ Rule.all := by
  cases rule <;> simp [Rule.all]

def Rule.name : Rule → String
  | .truth => "TRUTH"
  | .contradiction => "CONTR"
  | .conjunctionIntroduction => "CONJ"
  | .conjunctionLeft => "CONJUNCT1"
  | .conjunctionRight => "CONJUNCT2"
  | .disjunctionLeft => "DISJ1"
  | .disjunctionRight => "DISJ2"
  | .disjunctionElimination => "DISJ_CASES"
  | .implicationIntroduction => "DISCH"
  | .implicationElimination => "MP"
  | .negationIntroduction => "NOT_INTRO"
  | .negationElimination => "NOT_ELIM"
  | .reflexivity => "refl"
  | .symmetry => "sym"
  | .transitivity => "trans"
  | .propositionalExtensionality => "IMP_ANTISYM"
  | .equalityImplicationLeft => "EQ_IMP1"
  | .equalityImplicationRight => "EQ_IMP2"
  | .applicationFunction => "aeq1"
  | .applicationArgument => "aeq2"
  | .booleanEqualityElimination => "eqmp"

def Rule.declaration (references : Symbol → Nat) (ids : SortIds)
    (equivalenceReference : Nat) : Rule → TheoremDecl
  | .truth =>
      ⟨[.regular ids.wff ∅],
        [],
        entails references (.var 0) (holds references (applySymbol references .truth []))⟩
  | .contradiction =>
      ⟨[.regular ids.wff ∅, .regular ids.object ∅],
        [typed references (.var 0) (.var 1) (boolType references),
          entails references (.var 0) (holds references (applySymbol references .falsity []))],
        entails references (.var 0) (holds references (.var 1))⟩
  | .conjunctionIntroduction =>
      ⟨[.regular ids.wff ∅, .regular ids.object ∅, .regular ids.object ∅],
        [entails references (.var 0) (holds references (.var 1)),
          entails references (.var 0) (holds references (.var 2))],
        entails references (.var 0) (holds references (applySymbol references .andc [.var 1, .var 2]))⟩
  | .conjunctionLeft =>
      ⟨[.regular ids.wff ∅, .regular ids.object ∅, .regular ids.object ∅],
        [entails references (.var 0) (holds references (applySymbol references .andc [.var 1, .var 2]))],
        entails references (.var 0) (holds references (.var 1))⟩
  | .conjunctionRight =>
      ⟨[.regular ids.wff ∅, .regular ids.object ∅, .regular ids.object ∅],
        [entails references (.var 0) (holds references (applySymbol references .andc [.var 1, .var 2]))],
        entails references (.var 0) (holds references (.var 2))⟩
  | .disjunctionLeft =>
      ⟨[.regular ids.wff ∅, .regular ids.object ∅, .regular ids.object ∅],
        [entails references (.var 0) (holds references (.var 1)),
          typed references (.var 0) (.var 2) (boolType references)],
        entails references (.var 0) (holds references (applySymbol references .orc [.var 1, .var 2]))⟩
  | .disjunctionRight =>
      ⟨[.regular ids.wff ∅, .regular ids.object ∅, .regular ids.object ∅],
        [typed references (.var 0) (.var 1) (boolType references),
          entails references (.var 0) (holds references (.var 2))],
        entails references (.var 0) (holds references (applySymbol references .orc [.var 1, .var 2]))⟩
  | .disjunctionElimination =>
      ⟨[.regular ids.wff ∅, .regular ids.object ∅, .regular ids.object ∅, .regular ids.object ∅],
        [entails references (.var 0) (holds references (applySymbol references .orc [.var 1, .var 2])),
          typed references (.var 0) (.var 3) (boolType references),
          entails references (conjunction references (.var 0) (holds references (.var 1))) (holds references (.var 3)),
          entails references (conjunction references (.var 0) (holds references (.var 2))) (holds references (.var 3))],
        entails references (.var 0) (holds references (.var 3))⟩
  | .implicationIntroduction =>
      ⟨[.regular ids.wff ∅, .regular ids.object ∅, .regular ids.object ∅],
        [typed references (.var 0) (.var 1) (boolType references),
          typed references (.var 0) (.var 2) (boolType references),
          entails references (conjunction references (.var 0) (holds references (.var 1))) (holds references (.var 2))],
        entails references (.var 0) (holds references (applySymbol references .impc [.var 1, .var 2]))⟩
  | .implicationElimination =>
      ⟨[.regular ids.wff ∅, .regular ids.object ∅, .regular ids.object ∅],
        [entails references (.var 0) (holds references (applySymbol references .impc [.var 1, .var 2])),
          entails references (.var 0) (holds references (.var 1))],
        entails references (.var 0) (holds references (.var 2))⟩
  | .negationIntroduction =>
      ⟨[.regular ids.wff ∅, .regular ids.object ∅],
        [entails references (.var 0) (holds references (applySymbol references .impc [.var 1, applySymbol references .falsity []]))],
        entails references (.var 0) (holds references (applySymbol references .notc [.var 1]))⟩
  | .negationElimination =>
      ⟨[.regular ids.wff ∅, .regular ids.object ∅],
        [entails references (.var 0) (holds references (applySymbol references .notc [.var 1]))],
        entails references (.var 0) (holds references (applySymbol references .impc [.var 1, applySymbol references .falsity []]))⟩
  | .reflexivity =>
      ⟨[.regular ids.wff ∅, .regular ids.type ∅, .regular ids.object ∅],
        [typed references (.var 0) (.var 2) (.var 1)],
        entails references (.var 0) (holds references (equality references (.var 1) (.var 2) (.var 2)))⟩
  | .symmetry =>
      ⟨[.regular ids.type ∅, .regular ids.wff ∅, .regular ids.object ∅, .regular ids.object ∅],
        [entails references (.var 1) (holds references (equality references (.var 0) (.var 2) (.var 3)))],
        entails references (.var 1) (holds references (equality references (.var 0) (.var 3) (.var 2)))⟩
  | .transitivity =>
      ⟨[.regular ids.wff ∅, .regular ids.type ∅, .regular ids.object ∅, .regular ids.object ∅, .regular ids.object ∅],
        [entails references (.var 0) (holds references (equality references (.var 1) (.var 2) (.var 3))),
          entails references (.var 0) (holds references (equality references (.var 1) (.var 3) (.var 4)))],
        entails references (.var 0) (holds references (equality references (.var 1) (.var 2) (.var 4)))⟩
  | .propositionalExtensionality =>
      ⟨[.regular ids.wff ∅, .regular ids.object ∅, .regular ids.object ∅],
        [entails references (.var 0) (holds references (applySymbol references .impc [.var 1, .var 2])),
          entails references (.var 0) (holds references (applySymbol references .impc [.var 2, .var 1]))],
        entails references (.var 0) (holds references (equivalence equivalenceReference (.var 1) (.var 2)))⟩
  | .equalityImplicationLeft =>
      ⟨[.regular ids.wff ∅, .regular ids.object ∅, .regular ids.object ∅],
        [entails references (.var 0) (holds references (equivalence equivalenceReference (.var 1) (.var 2)))],
        entails references (.var 0) (holds references (applySymbol references .impc [.var 1, .var 2]))⟩
  | .equalityImplicationRight =>
      ⟨[.regular ids.wff ∅, .regular ids.object ∅, .regular ids.object ∅],
        [entails references (.var 0) (holds references (equivalence equivalenceReference (.var 1) (.var 2)))],
        entails references (.var 0) (holds references (applySymbol references .impc [.var 2, .var 1]))⟩
  | .applicationFunction =>
      ⟨[.regular ids.type ∅, .regular ids.type ∅, .regular ids.wff ∅, .regular ids.object ∅, .regular ids.object ∅, .regular ids.object ∅],
        [entails references (.var 2) (holds references (equality references (functionType references (.var 0) (.var 1)) (.var 4) (.var 5))),
          typed references (.var 2) (.var 3) (.var 0)],
        entails references (.var 2) (holds references (equality references (.var 1) (applySymbol references .app [.var 4, .var 3]) (applySymbol references .app [.var 5, .var 3])))⟩
  | .applicationArgument =>
      ⟨[.regular ids.type ∅, .regular ids.type ∅, .regular ids.wff ∅, .regular ids.object ∅, .regular ids.object ∅, .regular ids.object ∅],
        [typed references (.var 2) (.var 5) (functionType references (.var 0) (.var 1)),
          entails references (.var 2) (holds references (equality references (.var 0) (.var 3) (.var 4)))],
        entails references (.var 2) (holds references (equality references (.var 1) (applySymbol references .app [.var 5, .var 3]) (applySymbol references .app [.var 5, .var 4])))⟩
  | .booleanEqualityElimination =>
      ⟨[.regular ids.wff ∅, .regular ids.object ∅, .regular ids.object ∅],
        [entails references (.var 0) (holds references (equivalence equivalenceReference (.var 1) (.var 2))),
          entails references (.var 0) (holds references (.var 1))],
        entails references (.var 0) (holds references (.var 2))⟩

structure Rules (theorems : TheoremSignature) (references : Symbol → Nat) (ids : SortIds)
    (equivalenceReference : Nat) where
  index : Rule → Nat
  declared : ∀ rule, theorems (index rule) = some (rule.declaration references ids equivalenceReference)

def Rules.read? (theorems : TheoremSignature) (references : Symbol → Nat) (ids : SortIds)
    (equivalenceReference : Nat) (indices : Rule → Nat) :
    Option (Rules theorems references ids equivalenceReference) :=
  if known : Rule.all.all (fun rule =>
      decide (theorems (indices rule) = some (rule.declaration references ids equivalenceReference))) = true then
    some {
      index := indices
      declared := by
        intro rule
        exact of_decide_eq_true ((List.all_eq_true.mp known) rule (Rule.mem_all rule)) }
  else none

#print axioms Rules.read?

end Mettapedia.Languages.MM0.HOLKernelInferenceRules
