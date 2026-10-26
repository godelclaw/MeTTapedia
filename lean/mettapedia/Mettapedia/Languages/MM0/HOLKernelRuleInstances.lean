import Mettapedia.Languages.MM0.HOLKernelJudgmentReadback
import Mettapedia.Languages.MM0.HOLKernelInferenceRules

/-!
# Typed arguments and sequents of the maintained HOL rules

Each native structural, logical or equality schema has typed source operands
and an exact ordered premise list and conclusion. These data contain no
source proofs. Decoding the raw arguments is separate from constructing a
proof of the resulting rule instance and from native theorem licensing.
-/

set_option autoImplicit false
namespace Mettapedia.Languages.MM0.HOLKernelRuleInstances
open Mettapedia.Logic Mettapedia.Logic.HOL
open Kernel HOLKernelSyntax HOLKernelTermReadback HOLKernelJudgmentReadback
universe u
variable {Const : Ty Unit → Type u} {gamma : Ctx Unit}

inductive InferenceArguments (Const : Ty Unit → Type u) (gamma : Ctx Unit) : HOLKernelInferenceRules.Rule → Type u where
  | truth (g : Formula Const gamma) : InferenceArguments Const gamma .truth
  | contradiction (g p : Formula Const gamma) : InferenceArguments Const gamma .contradiction
  | conjunctionIntroduction (g p q : Formula Const gamma) : InferenceArguments Const gamma .conjunctionIntroduction
  | conjunctionLeft (g p q : Formula Const gamma) : InferenceArguments Const gamma .conjunctionLeft
  | conjunctionRight (g p q : Formula Const gamma) : InferenceArguments Const gamma .conjunctionRight
  | disjunctionLeft (g p q : Formula Const gamma) : InferenceArguments Const gamma .disjunctionLeft
  | disjunctionRight (g p q : Formula Const gamma) : InferenceArguments Const gamma .disjunctionRight
  | disjunctionElimination (g p q r : Formula Const gamma) : InferenceArguments Const gamma .disjunctionElimination
  | implicationIntroduction (g p q : Formula Const gamma) : InferenceArguments Const gamma .implicationIntroduction
  | implicationElimination (g p q : Formula Const gamma) : InferenceArguments Const gamma .implicationElimination
  | negationIntroduction (g p : Formula Const gamma) : InferenceArguments Const gamma .negationIntroduction
  | negationElimination (g p : Formula Const gamma) : InferenceArguments Const gamma .negationElimination
  | reflexivity {type : Ty Unit} (g : Formula Const gamma) (t : Term Const gamma type) : InferenceArguments Const gamma .reflexivity
  | symmetry {type : Ty Unit} (g : Formula Const gamma) (t s : Term Const gamma type) : InferenceArguments Const gamma .symmetry
  | transitivity {type : Ty Unit} (g : Formula Const gamma) (t s v : Term Const gamma type) : InferenceArguments Const gamma .transitivity
  | propositionalExtensionality (g p q : Formula Const gamma) : InferenceArguments Const gamma .propositionalExtensionality
  | equalityImplicationLeft (g p q : Formula Const gamma) : InferenceArguments Const gamma .equalityImplicationLeft
  | equalityImplicationRight (g p q : Formula Const gamma) : InferenceArguments Const gamma .equalityImplicationRight
  | applicationFunction {domain codomain : Ty Unit} (g : Formula Const gamma) (t : Term Const gamma domain) (f h : Term Const gamma (domain ⇒ codomain)) : InferenceArguments Const gamma .applicationFunction
  | applicationArgument {domain codomain : Ty Unit} (g : Formula Const gamma) (t s : Term Const gamma domain) (f : Term Const gamma (domain ⇒ codomain)) : InferenceArguments Const gamma .applicationArgument
  | booleanEqualityElimination (g p q : Formula Const gamma) : InferenceArguments Const gamma .booleanEqualityElimination

def InferenceArguments.premises {rule : HOLKernelInferenceRules.Rule} : InferenceArguments Const gamma rule → List (Formula Const gamma)
  | .truth _ => []
  | .contradiction g _ => [.imp g .top, .imp g .bot]
  | .conjunctionIntroduction g p q => [.imp g p, .imp g q]
  | .conjunctionLeft g p q => [.imp g (.and p q)]
  | .conjunctionRight g p q => [.imp g (.and p q)]
  | .disjunctionLeft g p _ => [.imp g p, .imp g .top]
  | .disjunctionRight g _ q => [.imp g .top, .imp g q]
  | .disjunctionElimination g p q r => [.imp g (.or p q), .imp g .top,
          .imp (.and g p) r, .imp (.and g q) r]
  | .implicationIntroduction g p q => [.imp g .top, .imp g .top, .imp (.and g p) q]
  | .implicationElimination g p q => [.imp g (.imp p q), .imp g p]
  | .negationIntroduction g p => [.imp g (.imp p .bot)]
  | .negationElimination g p => [.imp g (.not p)]
  | .reflexivity g _ => [.imp g .top]
  | .symmetry g t s => [.imp g (.eq t s)]
  | .transitivity g t s v => [.imp g (.eq t s), .imp g (.eq s v)]
  | .propositionalExtensionality g p q => [.imp g (.imp p q), .imp g (.imp q p)]
  | .equalityImplicationLeft g p q => [.imp g (.eq p q)]
  | .equalityImplicationRight g p q => [.imp g (.eq p q)]
  | .applicationFunction g _ f h => [.imp g (.eq f h), .imp g .top]
  | .applicationArgument g t s _ => [.imp g .top, .imp g (.eq t s)]
  | .booleanEqualityElimination g p q => [.imp g (.eq p q), .imp g p]

def InferenceArguments.conclusion {rule : HOLKernelInferenceRules.Rule} : InferenceArguments Const gamma rule → Formula Const gamma
  | .truth g => .imp g .top
  | .contradiction g p => .imp g p
  | .conjunctionIntroduction g p q => .imp g (.and p q)
  | .conjunctionLeft g p _ => .imp g p
  | .conjunctionRight g _ q => .imp g q
  | .disjunctionLeft g p q => .imp g (.or p q)
  | .disjunctionRight g p q => .imp g (.or p q)
  | .disjunctionElimination g _ _ r => .imp g r
  | .implicationIntroduction g p q => .imp g (.imp p q)
  | .implicationElimination g _ q => .imp g q
  | .negationIntroduction g p => .imp g (.not p)
  | .negationElimination g p => .imp g (.imp p .bot)
  | .reflexivity g t => .imp g (.eq t t)
  | .symmetry g t s => .imp g (.eq s t)
  | .transitivity g t _ v => .imp g (.eq t v)
  | .propositionalExtensionality g p q => .imp g (.eq p q)
  | .equalityImplicationLeft g p q => .imp g (.imp p q)
  | .equalityImplicationRight g p q => .imp g (.imp q p)
  | .applicationFunction g t f h => .imp g (.eq (.app f t) (.app h t))
  | .applicationArgument g t s f => .imp g (.eq (.app f t) (.app f s))
  | .booleanEqualityElimination g _ q => .imp g q

def readInferenceArguments (reader : TermReader Const) (references : HOLKernelSyntax.Symbol → Nat)
    (names : Names gamma) (rule : HOLKernelInferenceRules.Rule)
    (arguments : List Preterm) : Option (InferenceArguments Const gamma rule) :=
  let context := fun native =>
    (readJudgmentWith reader references names native).map Judgment.formula
  let formula := fun native => (reader names native).bind (expect .prop)
  let object := readObjectWith reader names
  match rule, arguments with
  | .truth, [antecedent] => do
      let g ← context antecedent
      pure (.truth g)
  | .contradiction, [antecedent, conclusion] => do
      let g ← context antecedent
      let p ← formula conclusion
      pure (.contradiction g p)
  | .conjunctionIntroduction, [antecedent, first, second] => do
      let g ← context antecedent
      let p ← formula first
      let q ← formula second
      pure (.conjunctionIntroduction g p q)
  | .conjunctionLeft, [antecedent, first, second] => do
      let g ← context antecedent
      let p ← formula first
      let q ← formula second
      pure (.conjunctionLeft g p q)
  | .conjunctionRight, [antecedent, first, second] => do
      let g ← context antecedent
      let p ← formula first
      let q ← formula second
      pure (.conjunctionRight g p q)
  | .disjunctionLeft, [antecedent, first, second] => do
      let g ← context antecedent
      let p ← formula first
      let q ← formula second
      pure (.disjunctionLeft g p q)
  | .disjunctionRight, [antecedent, first, second] => do
      let g ← context antecedent
      let p ← formula first
      let q ← formula second
      pure (.disjunctionRight g p q)
  | .disjunctionElimination, [antecedent, first, second, conclusion] => do
      let g ← context antecedent
      let p ← formula first
      let q ← formula second
      let r ← formula conclusion
      pure (.disjunctionElimination g p q r)
  | .implicationIntroduction, [antecedent, first, second] => do
      let g ← context antecedent
      let p ← formula first
      let q ← formula second
      pure (.implicationIntroduction g p q)
  | .implicationElimination, [antecedent, first, second] => do
      let g ← context antecedent
      let p ← formula first
      let q ← formula second
      pure (.implicationElimination g p q)
  | .negationIntroduction, [antecedent, body] => do
      let g ← context antecedent
      let p ← formula body
      pure (.negationIntroduction g p)
  | .negationElimination, [antecedent, body] => do
      let g ← context antecedent
      let p ← formula body
      pure (.negationElimination g p)
  | .reflexivity, [antecedent, typeCode, term] => do
      let g ← context antecedent
      match readType references typeCode with
      | none => none
      | some type => do
          let t ← object type term
          pure (.reflexivity g t)
  | .symmetry, [typeCode, antecedent, first, second] => do
      let g ← context antecedent
      match readType references typeCode with
      | none => none
      | some type => do
          let t ← object type first
          let s ← object type second
          pure (.symmetry g t s)
  | .transitivity, [antecedent, typeCode, first, middle, last] => do
      let g ← context antecedent
      match readType references typeCode with
      | none => none
      | some type => do
          let t ← object type first
          let s ← object type middle
          let v ← object type last
          pure (.transitivity g t s v)
  | .propositionalExtensionality, [antecedent, first, second] => do
      let g ← context antecedent
      let p ← formula first
      let q ← formula second
      pure (.propositionalExtensionality g p q)
  | .equalityImplicationLeft, [antecedent, first, second] => do
      let g ← context antecedent
      let p ← formula first
      let q ← formula second
      pure (.equalityImplicationLeft g p q)
  | .equalityImplicationRight, [antecedent, first, second] => do
      let g ← context antecedent
      let p ← formula first
      let q ← formula second
      pure (.equalityImplicationRight g p q)
  | .applicationFunction, [domainCode, codomainCode, antecedent, argument, first, second] => do
      let g ← context antecedent
      match readType references domainCode, readType references codomainCode with
      | some domain, some codomain => do
          let t ← object domain argument
          let f ← object (.arr domain codomain) first
          let h ← object (.arr domain codomain) second
          pure (.applicationFunction g t f h)
      | _, _ => none
  | .applicationArgument, [domainCode, codomainCode, antecedent, first, second, function] => do
      let g ← context antecedent
      match readType references domainCode, readType references codomainCode with
      | some domain, some codomain => do
          let t ← object domain first
          let s ← object domain second
          let f ← object (.arr domain codomain) function
          pure (.applicationArgument g t s f)
      | _, _ => none
  | .booleanEqualityElimination, [antecedent, first, second] => do
      let g ← context antecedent
      let p ← formula first
      let q ← formula second
      pure (.booleanEqualityElimination g p q)
  | _, _ => none


inductive StructuralArguments (Const : Ty Unit → Type u) (gamma : Ctx Unit) : HOLKernelStructuralRules.Rule → Type u where
  | id (p : Formula Const gamma) : StructuralArguments Const gamma .id
  | syl (p q r : Formula Const gamma) : StructuralArguments Const gamma .syl
  | ian (g p q : Formula Const gamma) : StructuralArguments Const gamma .ian
  | anl (p q : Formula Const gamma) : StructuralArguments Const gamma .anl
  | anr (p q : Formula Const gamma) : StructuralArguments Const gamma .anr

def StructuralArguments.premises {rule : HOLKernelStructuralRules.Rule} : StructuralArguments Const gamma rule → List (Formula Const gamma)
  | .id _ => []
  | .syl p q r => [.imp p q, .imp q r]
  | .ian g p q => [.imp g p, .imp g q]
  | .anl _ _ => []
  | .anr _ _ => []

def StructuralArguments.conclusion {rule : HOLKernelStructuralRules.Rule} : StructuralArguments Const gamma rule → Formula Const gamma
  | .id p => .imp p p
  | .syl p _ r => .imp p r
  | .ian g p q => .imp g (.and p q)
  | .anl p q => .imp (.and p q) p
  | .anr p q => .imp (.and p q) q

def readStructuralArguments (reader : TermReader Const) (references : HOLKernelSyntax.Symbol → Nat)
    (names : Names gamma) (rule : HOLKernelStructuralRules.Rule)
    (arguments : List Preterm) : Option (StructuralArguments Const gamma rule) :=
  let context := fun native =>
    (readJudgmentWith reader references names native).map Judgment.formula
  match rule, arguments with
  | .id, [proposition] => do
      let p ← context proposition
      pure (.id p)
  | .syl, [first, middle, last] => do
      let p ← context first
      let q ← context middle
      let r ← context last
      pure (.syl p q r)
  | .ian, [antecedent, first, second] => do
      let g ← context antecedent
      let p ← context first
      let q ← context second
      pure (.ian g p q)
  | .anl, [first, second] => do
      let p ← context first
      let q ← context second
      pure (.anl p q)
  | .anr, [first, second] => do
      let p ← context first
      let q ← context second
      pure (.anr p q)
  | _, _ => none


/-- Renaming source operands preserves the selected native schema. -/
def InferenceArguments.rename {delta : Ctx Unit} {rule : HOLKernelInferenceRules.Rule}
    (rho : Rename Unit gamma delta) :
    InferenceArguments Const gamma rule → InferenceArguments Const delta rule
  | .truth g => .truth (HOL.rename rho g)
  | .contradiction g p => .contradiction (HOL.rename rho g) (HOL.rename rho p)
  | .conjunctionIntroduction g p q => .conjunctionIntroduction (HOL.rename rho g) (HOL.rename rho p) (HOL.rename rho q)
  | .conjunctionLeft g p q => .conjunctionLeft (HOL.rename rho g) (HOL.rename rho p) (HOL.rename rho q)
  | .conjunctionRight g p q => .conjunctionRight (HOL.rename rho g) (HOL.rename rho p) (HOL.rename rho q)
  | .disjunctionLeft g p q => .disjunctionLeft (HOL.rename rho g) (HOL.rename rho p) (HOL.rename rho q)
  | .disjunctionRight g p q => .disjunctionRight (HOL.rename rho g) (HOL.rename rho p) (HOL.rename rho q)
  | .disjunctionElimination g p q r => .disjunctionElimination (HOL.rename rho g) (HOL.rename rho p) (HOL.rename rho q) (HOL.rename rho r)
  | .implicationIntroduction g p q => .implicationIntroduction (HOL.rename rho g) (HOL.rename rho p) (HOL.rename rho q)
  | .implicationElimination g p q => .implicationElimination (HOL.rename rho g) (HOL.rename rho p) (HOL.rename rho q)
  | .negationIntroduction g p => .negationIntroduction (HOL.rename rho g) (HOL.rename rho p)
  | .negationElimination g p => .negationElimination (HOL.rename rho g) (HOL.rename rho p)
  | .reflexivity g t => .reflexivity (HOL.rename rho g) (HOL.rename rho t)
  | .symmetry g t s => .symmetry (HOL.rename rho g) (HOL.rename rho t) (HOL.rename rho s)
  | .transitivity g t s v => .transitivity (HOL.rename rho g) (HOL.rename rho t) (HOL.rename rho s) (HOL.rename rho v)
  | .propositionalExtensionality g p q => .propositionalExtensionality (HOL.rename rho g) (HOL.rename rho p) (HOL.rename rho q)
  | .equalityImplicationLeft g p q => .equalityImplicationLeft (HOL.rename rho g) (HOL.rename rho p) (HOL.rename rho q)
  | .equalityImplicationRight g p q => .equalityImplicationRight (HOL.rename rho g) (HOL.rename rho p) (HOL.rename rho q)
  | .applicationFunction g t f h => .applicationFunction (HOL.rename rho g) (HOL.rename rho t) (HOL.rename rho f) (HOL.rename rho h)
  | .applicationArgument g t s f => .applicationArgument (HOL.rename rho g) (HOL.rename rho t) (HOL.rename rho s) (HOL.rename rho f)
  | .booleanEqualityElimination g p q => .booleanEqualityElimination (HOL.rename rho g) (HOL.rename rho p) (HOL.rename rho q)

theorem InferenceArguments.rename_premises {delta : Ctx Unit} {rule : HOLKernelInferenceRules.Rule}
    (rho : Rename Unit gamma delta) (arguments : InferenceArguments Const gamma rule) :
    (arguments.rename rho).premises = arguments.premises.map (HOL.rename rho) := by
  cases arguments <;> rfl

theorem InferenceArguments.rename_conclusion {delta : Ctx Unit} {rule : HOLKernelInferenceRules.Rule}
    (rho : Rename Unit gamma delta) (arguments : InferenceArguments Const gamma rule) :
    (arguments.rename rho).conclusion = HOL.rename rho arguments.conclusion := by
  cases arguments <;> rfl

/-- The structural rule and ordered premise positions are unchanged by renaming. -/
def StructuralArguments.rename {delta : Ctx Unit} {rule : HOLKernelStructuralRules.Rule}
    (rho : Rename Unit gamma delta) :
    StructuralArguments Const gamma rule → StructuralArguments Const delta rule
  | .id p => .id (HOL.rename rho p)
  | .syl p q r => .syl (HOL.rename rho p) (HOL.rename rho q) (HOL.rename rho r)
  | .ian g p q => .ian (HOL.rename rho g) (HOL.rename rho p) (HOL.rename rho q)
  | .anl p q => .anl (HOL.rename rho p) (HOL.rename rho q)
  | .anr p q => .anr (HOL.rename rho p) (HOL.rename rho q)

theorem StructuralArguments.rename_premises {delta : Ctx Unit} {rule : HOLKernelStructuralRules.Rule}
    (rho : Rename Unit gamma delta) (arguments : StructuralArguments Const gamma rule) :
    (arguments.rename rho).premises = arguments.premises.map (HOL.rename rho) := by
  cases arguments <;> rfl

theorem StructuralArguments.rename_conclusion {delta : Ctx Unit} {rule : HOLKernelStructuralRules.Rule}
    (rho : Rename Unit gamma delta) (arguments : StructuralArguments Const gamma rule) :
    (arguments.rename rho).conclusion = HOL.rename rho arguments.conclusion := by
  cases arguments <;> rfl

end Mettapedia.Languages.MM0.HOLKernelRuleInstances
