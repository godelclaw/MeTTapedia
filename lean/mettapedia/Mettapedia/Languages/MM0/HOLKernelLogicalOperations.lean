import Mettapedia.Languages.MM0.HOLKernelSignature

/-!
# Declared logical function constants of maintained MM0 HOL

Seven function constants supply the application presentations of the logical
constructors. The profile retains their actual names, term declarations,
typing theorem headers and stored constructor-definition bodies. These are
precise native table lookups. Body equality here is structural data equality;
semantic equivalence alone grants no authority to unfold a definition.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MM0.HOLKernelLogicalOperations

open Kernel HOLKernelSyntax

inductive Operator where
  | equality
  | conjunction
  | disjunction
  | implication
  | negation
  | universal
  | existential
  deriving DecidableEq, Repr

def Operator.all : List Operator :=
  [.equality, .conjunction, .disjunction, .implication, .negation, .universal, .existential]

theorem Operator.mem_all (operator : Operator) : operator ∈ Operator.all := by
  cases operator <;> simp [Operator.all]

def Operator.name : Operator → String
  | .equality => "eq"
  | .conjunction => "and"
  | .disjunction => "or"
  | .implication => "imp"
  | .negation => "not"
  | .universal => "all"
  | .existential => "ex"

def Operator.constructor : Operator → Symbol
  | .equality => .eqc
  | .conjunction => .andc
  | .disjunction => .orc
  | .implication => .impc
  | .negation => .notc
  | .universal => .allc
  | .existential => .exc

def Operator.declaration (ids : SortIds) : Operator → TermDecl
  | .equality => ⟨[.regular ids.type ∅], ids.object, ∅⟩
  | .conjunction => ⟨[], ids.object, ∅⟩
  | .disjunction => ⟨[], ids.object, ∅⟩
  | .implication => ⟨[], ids.object, ∅⟩
  | .negation => ⟨[], ids.object, ∅⟩
  | .universal => ⟨[.regular ids.type ∅], ids.object, ∅⟩
  | .existential => ⟨[.regular ids.type ∅], ids.object, ∅⟩

def Operator.typingName : Operator → String
  | .equality => "eqT"
  | .conjunction => "andT"
  | .disjunction => "orT"
  | .implication => "impT"
  | .negation => "notT"
  | .universal => "allT"
  | .existential => "exT"

def Operator.typingDeclaration (references : Symbol → Nat) (operators : Operator → Nat)
    (ids : SortIds) : Operator → TheoremDecl
  | .equality =>
      ⟨[.regular ids.wff ∅, .regular ids.type ∅], [],
        applySymbol references .im [(.var 0), (applySymbol references .ty [(Preterm.applyArgs (.term (operators .equality)) [(.var 1)]), (applySymbol references .function [(.var 1), (applySymbol references .function [(.var 1), (applySymbol references .bool [])])])])]⟩
  | .conjunction =>
      ⟨[.regular ids.wff ∅], [],
        applySymbol references .im [(.var 0), (applySymbol references .ty [(.term (operators .conjunction)), (applySymbol references .function [(applySymbol references .bool []), (applySymbol references .function [(applySymbol references .bool []), (applySymbol references .bool [])])])])]⟩
  | .disjunction =>
      ⟨[.regular ids.wff ∅], [],
        applySymbol references .im [(.var 0), (applySymbol references .ty [(.term (operators .disjunction)), (applySymbol references .function [(applySymbol references .bool []), (applySymbol references .function [(applySymbol references .bool []), (applySymbol references .bool [])])])])]⟩
  | .implication =>
      ⟨[.regular ids.wff ∅], [],
        applySymbol references .im [(.var 0), (applySymbol references .ty [(.term (operators .implication)), (applySymbol references .function [(applySymbol references .bool []), (applySymbol references .function [(applySymbol references .bool []), (applySymbol references .bool [])])])])]⟩
  | .negation =>
      ⟨[.regular ids.wff ∅], [],
        applySymbol references .im [(.var 0), (applySymbol references .ty [(.term (operators .negation)), (applySymbol references .function [(applySymbol references .bool []), (applySymbol references .bool [])])])]⟩
  | .universal =>
      ⟨[.regular ids.wff ∅, .regular ids.type ∅], [],
        applySymbol references .im [(.var 0), (applySymbol references .ty [(Preterm.applyArgs (.term (operators .universal)) [(.var 1)]), (applySymbol references .function [(applySymbol references .function [(.var 1), (applySymbol references .bool [])]), (applySymbol references .bool [])])])]⟩
  | .existential =>
      ⟨[.regular ids.wff ∅, .regular ids.type ∅], [],
        applySymbol references .im [(.var 0), (applySymbol references .ty [(Preterm.applyArgs (.term (operators .existential)) [(.var 1)]), (applySymbol references .function [(applySymbol references .function [(.var 1), (applySymbol references .bool [])]), (applySymbol references .bool [])])])]⟩

def Operator.body (references : Symbol → Nat) (operators : Operator → Nat) : Operator → Definition.Body
  | .equality => ⟨[], applySymbol references .app [(applySymbol references .app [(Preterm.applyArgs (.term (operators .equality)) [(.var 0)]), (.var 1)]), (.var 2)]⟩
  | .conjunction => ⟨[], applySymbol references .app [(applySymbol references .app [(.term (operators .conjunction)), (.var 0)]), (.var 1)]⟩
  | .disjunction => ⟨[], applySymbol references .app [(applySymbol references .app [(.term (operators .disjunction)), (.var 0)]), (.var 1)]⟩
  | .implication => ⟨[], applySymbol references .app [(applySymbol references .app [(.term (operators .implication)), (.var 0)]), (.var 1)]⟩
  | .negation => ⟨[], applySymbol references .app [(.term (operators .negation)), (.var 0)]⟩
  | .universal => ⟨[], applySymbol references .app [(Preterm.applyArgs (.term (operators .universal)) [(.var 1)]), (applySymbol references .lam [(.var 0), (.var 1), (.var 2)])]⟩
  | .existential => ⟨[], applySymbol references .app [(Preterm.applyArgs (.term (operators .existential)) [(.var 1)]), (applySymbol references .lam [(.var 0), (.var 1), (.var 2)])]⟩

structure Profile (sorts : SortSignature) (terms : TermSignature) (definitions : Definition.Signature)
    (theorems : TheoremSignature) (signature : Signature sorts terms) where
  reference : Operator → Nat
  named : ∀ operator, signature.names (reference operator) = some operator.name
  declared : ∀ operator, terms (reference operator) = some (operator.declaration signature.ids)
  typingReference : Operator → Nat
  typingDeclared : ∀ operator, theorems (typingReference operator) =
    some (operator.typingDeclaration signature.symbol reference signature.ids)
  defined : ∀ (operator : Operator), definitions (signature.symbol operator.constructor) =
    some (operator.body signature.symbol reference)

section ReferenceNames
variable {sorts : SortSignature} {terms : TermSignature} {definitions : Definition.Signature}
variable {theorems : TheoremSignature} {signature : Signature sorts terms}

theorem Operator.name_injective : Function.Injective Operator.name := by
  intro first second same
  cases first <;> cases second <;> simp_all [Operator.name]

theorem Profile.reference_injective (profile : Profile sorts terms definitions theorems signature) :
    Function.Injective profile.reference := by
  intro first second same
  apply Operator.name_injective
  have equal := congrArg signature.names same
  rw [profile.named, profile.named] at equal
  exact Option.some.inj equal

theorem Profile.reference_ne_symbol (profile : Profile sorts terms definitions theorems signature)
    (operator : Operator) (constructor : Symbol) : profile.reference operator ≠ signature.symbol constructor := by
  intro same
  have equal := congrArg signature.names same
  rw [profile.named, signature.named] at equal
  have names := Option.some.inj equal
  cases operator <;> cases constructor <;> simp [Operator.name, Symbol.name] at names

end ReferenceNames

def Profile.read? {sorts : SortSignature} {terms : TermSignature} {definitions : Definition.Signature}
    {theorems : TheoremSignature} (signature : Signature sorts terms)
    (references typings : Operator → Nat) :
    Option (Profile sorts terms definitions theorems signature) :=
  if names : Operator.all.all (fun operator =>
      decide (signature.names (references operator) = some operator.name)) = true then
  if declarations : Operator.all.all (fun operator =>
      decide (terms (references operator) = some (operator.declaration signature.ids))) = true then
  if typing : Operator.all.all (fun operator =>
      decide (theorems (typings operator) =
        some (operator.typingDeclaration signature.symbol references signature.ids))) = true then
  if bodies : Operator.all.all (fun operator =>
      decide (definitions (signature.symbol operator.constructor) =
        some (operator.body signature.symbol references))) = true then
    some {
      reference := references
      named := fun operator => of_decide_eq_true
        ((List.all_eq_true.mp names) operator (Operator.mem_all operator))
      declared := fun operator => of_decide_eq_true
        ((List.all_eq_true.mp declarations) operator (Operator.mem_all operator))
      typingReference := typings
      typingDeclared := fun operator => of_decide_eq_true
        ((List.all_eq_true.mp typing) operator (Operator.mem_all operator))
      defined := fun operator => of_decide_eq_true
        ((List.all_eq_true.mp bodies) operator (Operator.mem_all operator)) }
  else none else none else none else none

#print axioms Profile.read?

end Mettapedia.Languages.MM0.HOLKernelLogicalOperations
