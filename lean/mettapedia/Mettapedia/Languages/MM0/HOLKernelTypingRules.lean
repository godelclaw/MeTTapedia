import Mettapedia.Languages.MM0.HOLKernelStructuralRules
import Mettapedia.Languages.MM0.Kernel.RegularSubstitution
import Mettapedia.Languages.MM0.Kernel.SingleBoundSubstitution

/-!
# Native proof schemas for HOL typing in the maintained MM0 theory

The eleven schemas retain the actual argument order of the maintained
typing declarations. In particular equality and quantifier typing place
their type parameter before the logical context. Binding rules retain the
one bound formal and the body's declared dependency on that formal.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MM0.HOLKernelTypingRules

open Kernel HOLKernelSyntax HOLKernelJudgment
open HOLKernelStructuralRules (CheckedProof)

inductive Rule where
  | appT | lamT | truth | falsity | andcT | orcT | impcT | notcT | eqcT | allcT | excT
  deriving DecidableEq, Repr

def Rule.all : List Rule :=
  [.appT, .lamT, .truth, .falsity, .andcT, .orcT, .impcT, .notcT, .eqcT, .allcT, .excT]

theorem Rule.mem_all (rule : Rule) : rule ∈ Rule.all := by
  cases rule <;> simp [Rule.all]

def Rule.name : Rule → String
  | .appT => "appT"
  | .lamT => "lamT"
  | .truth => "TT"
  | .falsity => "FT"
  | .andcT => "andcT"
  | .orcT => "orcT"
  | .impcT => "impcT"
  | .notcT => "notcT"
  | .eqcT => "eqcT"
  | .allcT => "allcT"
  | .excT => "excT"

def boolType (references : Symbol → Nat) : Preterm := applySymbol references .bool []

def functionType (references : Symbol → Nat) (domain result : Preterm) : Preterm :=
  applySymbol references .function [domain, result]

def typed (references : Symbol → Nat) (antecedent expression type : Preterm) : Preterm :=
  entails references antecedent (hasType references expression type)

def binaryDeclaration (references : Symbol → Nat) (ids : SortIds) (symbol : Symbol) : TheoremDecl :=
  ⟨[.regular ids.wff ∅, .regular ids.object ∅, .regular ids.object ∅],
    [typed references (.var 0) (.var 1) (boolType references),
      typed references (.var 0) (.var 2) (boolType references)],
    typed references (.var 0) (applySymbol references symbol [.var 1, .var 2]) (boolType references)⟩

def quantifierDeclaration (references : Symbol → Nat) (ids : SortIds) (symbol : Symbol) : TheoremDecl :=
  ⟨[.regular ids.type ∅, .regular ids.wff ∅, .bound ids.object, .regular ids.object {2}],
    [typed references (conjunction references (.var 1) (hasType references (.var 2) (.var 0)))
      (.var 3) (boolType references)],
    typed references (.var 1) (applySymbol references symbol [.var 2, .var 0, .var 3])
      (boolType references)⟩

def Rule.declaration (references : Symbol → Nat) (ids : SortIds) : Rule → TheoremDecl
  | .appT =>
      ⟨[.regular ids.wff ∅, .regular ids.type ∅, .regular ids.type ∅,
          .regular ids.object ∅, .regular ids.object ∅],
        [typed references (.var 0) (.var 3) (functionType references (.var 1) (.var 2)),
          typed references (.var 0) (.var 4) (.var 1)],
        typed references (.var 0) (applySymbol references .app [.var 3, .var 4]) (.var 2)⟩
  | .lamT =>
      ⟨[.regular ids.wff ∅, .regular ids.type ∅, .regular ids.type ∅,
          .bound ids.object, .regular ids.object {3}],
        [typed references (conjunction references (.var 0) (hasType references (.var 3) (.var 1)))
          (.var 4) (.var 2)],
        typed references (.var 0) (applySymbol references .lam [.var 3, .var 1, .var 4])
          (functionType references (.var 1) (.var 2))⟩
  | .truth => ⟨[.regular ids.wff ∅], [], typed references (.var 0)
      (applySymbol references .truth []) (boolType references)⟩
  | .falsity => ⟨[.regular ids.wff ∅], [], typed references (.var 0)
      (applySymbol references .falsity []) (boolType references)⟩
  | .andcT => binaryDeclaration references ids .andc
  | .orcT => binaryDeclaration references ids .orc
  | .impcT => binaryDeclaration references ids .impc
  | .notcT =>
      ⟨[.regular ids.wff ∅, .regular ids.object ∅],
        [typed references (.var 0) (.var 1) (boolType references)],
        typed references (.var 0) (applySymbol references .notc [.var 1]) (boolType references)⟩
  | .eqcT =>
      ⟨[.regular ids.type ∅, .regular ids.wff ∅, .regular ids.object ∅, .regular ids.object ∅],
        [typed references (.var 1) (.var 2) (.var 0), typed references (.var 1) (.var 3) (.var 0)],
        typed references (.var 1) (applySymbol references .eqc [.var 0, .var 2, .var 3])
          (boolType references)⟩
  | .allcT => quantifierDeclaration references ids .allc
  | .excT => quantifierDeclaration references ids .exc

structure Rules (theorems : TheoremSignature) (references : Symbol → Nat) (ids : SortIds) where
  index : Rule → Nat
  declared : ∀ rule, theorems (index rule) = some (rule.declaration references ids)

def Rules.read? (theorems : TheoremSignature) (references : Symbol → Nat) (ids : SortIds)
    (indices : Rule → Nat) : Option (Rules theorems references ids) :=
  if known : Rule.all.all (fun rule =>
      decide (theorems (indices rule) = some (rule.declaration references ids))) = true then
    some {
      index := indices
      declared := by
        intro rule
        exact of_decide_eq_true ((List.all_eq_true.mp known) rule (Rule.mem_all rule)) }
  else none

#print axioms Rules.read?

end Mettapedia.Languages.MM0.HOLKernelTypingRules
