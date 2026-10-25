import Mettapedia.Languages.MM0.HOLKernelInferenceRules

/-!
# Maintained MM0 HOL binding and substitution schemas

The declarations retain actual bound formal positions, dependency sets and
ordered premise judgments. Beta permits a context that depends on its bound
formal. Generalization keeps its preceding context independent; existential
elimination also keeps its result independent. Two-name renaming retains two
separate bound formals. The equality type-recovery schemas support the shared
binding constructions.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MM0.HOLKernelBindingRules

open Kernel HOLKernelSyntax HOLKernelJudgment
open HOLKernelTypingRules (typed boolType functionType)
open HOLKernelInferenceRules (equality equivalence)

inductive Rule where
  | universalIntroduction
  | universalElimination
  | existentialIntroduction
  | existentialElimination
  | abstractionCongruence
  | variableBeta
  | eta
  | constantAbstractionRenaming
  | abstractionRenaming
  | substitution
  | beta
  | equalityLeftTyping
  | equalityRightTyping
  deriving DecidableEq, Repr

def Rule.all : List Rule :=
  [.universalIntroduction, .universalElimination, .existentialIntroduction, .existentialElimination, .abstractionCongruence, .variableBeta, .eta, .constantAbstractionRenaming, .abstractionRenaming, .substitution, .beta, .equalityLeftTyping, .equalityRightTyping]

theorem Rule.mem_all (rule : Rule) : rule ∈ Rule.all := by
  cases rule <;> simp [Rule.all]

def Rule.name : Rule → String
  | .universalIntroduction => "GEN"
  | .universalElimination => "SPEC"
  | .existentialIntroduction => "EXISTS"
  | .existentialElimination => "CHOOSE"
  | .abstractionCongruence => "leq"
  | .variableBeta => "beta"
  | .eta => "eta"
  | .constantAbstractionRenaming => "cbvv"
  | .abstractionRenaming => "cbv"
  | .substitution => "inst"
  | .beta => "betac"
  | .equalityLeftTyping => "eqR1"
  | .equalityRightTyping => "eqR2"

def Rule.declaration (references : Symbol → Nat) (ids : SortIds)
    (equivalenceReference : Nat) : Rule → TheoremDecl
  | .universalIntroduction =>
      ⟨[.regular ids.wff ∅, .regular ids.type ∅, .bound ids.object, .regular ids.object {2}],
        [entails references (conjunction references (.var 0) (hasType references (.var 2) (.var 1))) (holds references (.var 3))],
        entails references (.var 0) (holds references (applySymbol references .allc [.var 2, .var 1, .var 3]))⟩
  | .universalElimination =>
      ⟨[.regular ids.wff ∅, .regular ids.type ∅, .bound ids.object, .regular ids.object {2}, .regular ids.object {2}, .regular ids.object {2}],
        [typed references (.var 0) (.var 3) (.var 1),
          typed references (.var 0) (.var 5) (boolType references),
          entails references (conjunction references (.var 0) (holds references (equality references (.var 1) (.var 2) (.var 3)))) (holds references (equivalence equivalenceReference (.var 4) (.var 5))),
          entails references (.var 0) (holds references (applySymbol references .allc [.var 2, .var 1, .var 4]))],
        entails references (.var 0) (holds references (.var 5))⟩
  | .existentialIntroduction =>
      ⟨[.regular ids.wff ∅, .regular ids.type ∅, .bound ids.object, .regular ids.object {2}, .regular ids.object {2}, .regular ids.object {2}],
        [typed references (conjunction references (.var 0) (hasType references (.var 2) (.var 1))) (.var 4) (boolType references),
          typed references (.var 0) (.var 3) (.var 1),
          entails references (conjunction references (.var 0) (holds references (equality references (.var 1) (.var 2) (.var 3)))) (holds references (equivalence equivalenceReference (.var 4) (.var 5))),
          entails references (.var 0) (holds references (.var 5))],
        entails references (.var 0) (holds references (applySymbol references .exc [.var 2, .var 1, .var 4]))⟩
  | .existentialElimination =>
      ⟨[.regular ids.wff ∅, .regular ids.type ∅, .bound ids.object, .regular ids.object {2}, .regular ids.object ∅],
        [typed references (.var 0) (.var 4) (boolType references),
          entails references (.var 0) (holds references (applySymbol references .exc [.var 2, .var 1, .var 3])),
          entails references (conjunction references (conjunction references (.var 0) (hasType references (.var 2) (.var 1))) (holds references (.var 3))) (holds references (.var 4))],
        entails references (.var 0) (holds references (.var 4))⟩
  | .abstractionCongruence =>
      ⟨[.regular ids.wff ∅, .regular ids.type ∅, .regular ids.type ∅, .bound ids.object, .regular ids.object {3}, .regular ids.object {3}],
        [entails references (conjunction references (.var 0) (hasType references (.var 3) (.var 1))) (holds references (equality references (.var 2) (.var 4) (.var 5)))],
        entails references (.var 0) (holds references (equality references (functionType references (.var 1) (.var 2)) (applySymbol references .lam [.var 3, .var 1, .var 4]) (applySymbol references .lam [.var 3, .var 1, .var 5])))⟩
  | .variableBeta =>
      ⟨[.regular ids.type ∅, .regular ids.type ∅, .bound ids.object, .regular ids.wff {2}, .regular ids.object {2}],
        [typed references (.var 3) (applySymbol references .app [applySymbol references .lam [.var 2, .var 0, .var 4], .var 2]) (.var 1)],
        entails references (.var 3) (holds references (equality references (.var 1) (applySymbol references .app [applySymbol references .lam [.var 2, .var 0, .var 4], .var 2]) (.var 4)))⟩
  | .eta =>
      ⟨[.regular ids.wff ∅, .regular ids.type ∅, .regular ids.type ∅, .bound ids.object, .regular ids.object {3}],
        [typed references (.var 0) (.var 4) (functionType references (.var 1) (.var 2))],
        entails references (.var 0) (holds references (equality references (functionType references (.var 1) (.var 2)) (applySymbol references .lam [.var 3, .var 1, applySymbol references .app [.var 4, .var 3]]) (.var 4)))⟩
  | .constantAbstractionRenaming =>
      ⟨[.regular ids.wff ∅, .regular ids.type ∅, .regular ids.type ∅, .bound ids.object, .bound ids.object, .regular ids.object {3, 4}],
        [typed references (.var 0) (.var 5) (.var 2)],
        entails references (.var 0) (holds references (equality references (functionType references (.var 1) (.var 2)) (applySymbol references .lam [.var 3, .var 1, .var 5]) (applySymbol references .lam [.var 4, .var 1, .var 5])))⟩
  | .abstractionRenaming =>
      ⟨[.regular ids.type ∅, .regular ids.type ∅, .regular ids.wff ∅, .bound ids.object, .bound ids.object, .regular ids.object {3, 4}, .regular ids.object {3, 4}],
        [typed references (conjunction references (.var 2) (hasType references (.var 3) (.var 0))) (.var 5) (.var 1),
          typed references (conjunction references (.var 2) (hasType references (.var 4) (.var 0))) (.var 6) (.var 1),
          entails references (conjunction references (.var 2) (holds references (equality references (.var 0) (.var 3) (.var 4)))) (holds references (equality references (.var 1) (.var 5) (.var 6)))],
        entails references (.var 2) (holds references (equality references (functionType references (.var 0) (.var 1)) (applySymbol references .lam [.var 3, .var 0, .var 5]) (applySymbol references .lam [.var 4, .var 0, .var 6])))⟩
  | .substitution =>
      ⟨[.regular ids.wff ∅, .regular ids.type ∅, .bound ids.object, .regular ids.object {2}, .regular ids.object {2}],
        [typed references (.var 0) (.var 4) (boolType references),
          typed references (.var 0) (.var 3) (.var 1),
          entails references (conjunction references (.var 0) (holds references (equality references (.var 1) (.var 2) (.var 3)))) (holds references (.var 4))],
        entails references (.var 0) (holds references (.var 4))⟩
  | .beta =>
      ⟨[.regular ids.wff ∅, .regular ids.type ∅, .regular ids.type ∅, .bound ids.object, .regular ids.object {3}, .regular ids.object {3}, .regular ids.object {3}],
        [typed references (conjunction references (.var 0) (hasType references (.var 3) (.var 1))) (.var 5) (.var 2),
          typed references (.var 0) (.var 4) (.var 1),
          typed references (.var 0) (.var 6) (.var 2),
          entails references (conjunction references (.var 0) (holds references (equality references (.var 1) (.var 3) (.var 4)))) (holds references (equality references (.var 2) (.var 5) (.var 6)))],
        entails references (.var 0) (holds references (equality references (.var 2) (applySymbol references .app [applySymbol references .lam [.var 3, .var 1, .var 5], .var 4]) (.var 6)))⟩
  | .equalityLeftTyping =>
      ⟨[.regular ids.type ∅, .regular ids.wff ∅, .regular ids.object ∅, .regular ids.object ∅],
        [entails references (.var 1) (holds references (equality references (.var 0) (.var 2) (.var 3)))],
        typed references (.var 1) (.var 2) (.var 0)⟩
  | .equalityRightTyping =>
      ⟨[.regular ids.type ∅, .regular ids.wff ∅, .regular ids.object ∅, .regular ids.object ∅],
        [entails references (.var 1) (holds references (equality references (.var 0) (.var 2) (.var 3)))],
        typed references (.var 1) (.var 3) (.var 0)⟩

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

end Mettapedia.Languages.MM0.HOLKernelBindingRules
