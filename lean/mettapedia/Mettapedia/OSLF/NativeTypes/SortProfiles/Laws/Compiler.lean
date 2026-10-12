import Mettapedia.OSLF.NativeTypes.SortProfiles.EquationalCenter
import Mettapedia.OSLF.Framework.RedexPosition

open Mettapedia.OSLF.Framework

/-!
# The finite display algebra compiled from an authored language

Constructor operations come from actual declarations. Binder, substitution,
bound-index and collection headers remain explicit structural symbols in
the algebra of authored templates. This is a display algebra; its unary
binder symbols do not establish any theorem about scoped substitution.

Equation systems and directed-rule law systems are compiled separately.
Conditional premises are explicit unresolved diagnostics, never omitted
equations or unrestricted laws. Complete operation tables, rather than a
supplied admissibility predicate, feed the equational-center checker.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.SortProfiles.Laws.Compiler

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.UniversalAlgebra
open Mettapedia.OSLF.Framework.ModalHypercube (HSort)

inductive Key where
  | constructor (name : String) (arguments : Nat)
  | bound (index : Nat)
  | binder (name : Option String)
  | multiBinder (arity : Nat) (names : List String)
  | substitution
  | collection (kind : CollType) (elements : Nat) (hasRest : Bool)
  deriving DecidableEq, Repr

def Key.arity : Key → Nat
  | .constructor _ arguments => arguments
  | .bound _ => 0
  | .binder _ => 1
  | .multiBinder _ _ => 1
  | .substitution => 2
  | .collection _ elements hasRest => elements + if hasRest then 1 else 0

mutual

def patternKeys : Pattern → List Key
  | .bvar index => [.bound index]
  | .fvar _ => []
  | .apply constructor arguments =>
      .constructor constructor arguments.length :: patternKeysList arguments
  | .lambda binder body => .binder binder :: patternKeys body
  | .multiLambda arity binders body => .multiBinder arity binders :: patternKeys body
  | .subst body replacement => .substitution :: (patternKeys body ++ patternKeys replacement)
  | .collection kind elements rest =>
      .collection kind elements.length rest.isSome :: patternKeysList elements

def patternKeysList : List Pattern → List Key
  | [] => []
  | pattern :: patterns => patternKeys pattern ++ patternKeysList patterns

end

def operationKeys (language : LanguageDef) : Finset Key :=
  (language.terms.map (fun declaration =>
    Key.constructor declaration.label declaration.params.length) ++
    language.equations.flatMap (fun equation => patternKeys equation.left ++ patternKeys equation.right) ++
    language.rewrites.flatMap (fun rule => patternKeys rule.left ++ patternKeys rule.right)).toFinset

def signature (language : LanguageDef) : Signature where
  Operation := {key : Key // key ∈ operationKeys language}
  arity key := key.val.arity

instance (language : LanguageDef) : Fintype (signature language).Operation :=
  inferInstanceAs (Fintype {key : Key // key ∈ operationKeys language})

instance (language : LanguageDef) : DecidableEq (signature language).Operation :=
  inferInstanceAs (DecidableEq {key : Key // key ∈ operationKeys language})

def constructorDeclared (language : LanguageDef) (name : String) (arity : Nat) : Bool :=
  language.terms.any fun declaration =>
    declaration.label == name && declaration.params.length == arity

def keyAdmitted (language : LanguageDef) : Key → Bool
  | .constructor name arity => constructorDeclared language name arity
  | _ => true

def operation? (language : LanguageDef) (key : Key) : Option (signature language).Operation :=
  if occurs : key ∈ operationKeys language then
    if keyAdmitted language key then some ⟨key, occurs⟩ else none
  else none

def variableIndex? (names : List String) (name : String) : Option Nat :=
  if name ∈ names then some (names.idxOf name) else none

def assemble? (language : LanguageDef) (key : Key)
    (arguments : List (Term (signature language))) : Option (Term (signature language)) := do
  let operation ← operation? language key
  if length : arguments.length = (signature language).arity operation then
    some (.op operation fun index => arguments[index.val]'(by rw [length]; exact index.isLt))
  else none

mutual

def encode (language : LanguageDef) (names : List String) :
    Pattern → Option (Term (signature language))
  | .bvar index => assemble? language (.bound index) []
  | .fvar name => (variableIndex? names name).map Term.var
  | .apply constructor arguments =>
      (encodeList language names arguments).bind
        (assemble? language (.constructor constructor arguments.length))
  | .lambda binder body =>
      (encode language names body).bind fun encoded =>
        assemble? language (.binder binder) [encoded]
  | .multiLambda arity binders body =>
      (encode language names body).bind fun encoded =>
        assemble? language (.multiBinder arity binders) [encoded]
  | .subst body replacement =>
      (encode language names body).bind fun left =>
        (encode language names replacement).bind fun right =>
          assemble? language .substitution [left, right]
  | .collection kind elements rest =>
      (encodeList language names elements).bind fun encoded =>
        match rest with
        | none => assemble? language (.collection kind elements.length false) encoded
        | some name => (variableIndex? names name).bind fun index =>
            assemble? language (.collection kind elements.length true) (encoded ++ [.var index])

def encodeList (language : LanguageDef) (names : List String) :
    List Pattern → Option (List (Term (signature language)))
  | [] => some []
  | pattern :: patterns => (encode language names pattern).bind fun first =>
      (encodeList language names patterns).map (List.cons first)

end

inductive Kind where
  | equation
  | rewrite
  deriving DecidableEq, Repr

structure Law where
  kind : Kind
  declaration : Nat
  name : String
  context : List (String × TypeExpr)
  premises : List Premise
  bindings : Option RuleBindingSpec
  left : Pattern
  right : Pattern
  deriving Repr

def equationLaws (language : LanguageDef) : List Law :=
  language.equations.zipIdx.map fun (equation, index) =>
    ⟨.equation, index, equation.name, equation.typeContext, equation.premises,
      equation.bindings, equation.left, equation.right⟩

def rewriteLaws (language : LanguageDef) : List Law :=
  language.rewrites.zipIdx.map fun (rule, index) =>
    ⟨.rewrite, index, rule.name, rule.typeContext, rule.premises,
      rule.bindings, rule.left, rule.right⟩

inductive Diagnostic where
  | conditionalPremises (kind : Kind) (declaration : Nat) (premises : List Premise)
  | duplicateVariables (kind : Kind) (declaration : Nat)
  | scopedDependencies (kind : Kind) (declaration : Nat) (bindings : RuleBindingSpec)
  | unencodedLeft (kind : Kind) (declaration : Nat)
  | unencodedRight (kind : Kind) (declaration : Nat)
  deriving DecidableEq, Repr

def unresolved (language : LanguageDef) (law : Law) : List Diagnostic :=
  (if law.premises = [] then []
    else [.conditionalPremises law.kind law.declaration law.premises]) ++
  (if (law.context.map Prod.fst).Nodup then []
    else [.duplicateVariables law.kind law.declaration]) ++
  (match law.bindings with
    | none => []
    | some bindings =>
        if bindings.dependencies.all (fun dependency => dependency.2.isEmpty) &&
            bindings.occurrences.isEmpty then []
        else [.scopedDependencies law.kind law.declaration bindings]) ++
  (if (encode language (law.context.map Prod.fst) law.left).isSome then []
    else [.unencodedLeft law.kind law.declaration]) ++
  (if (encode language (law.context.map Prod.fst) law.right).isSome then []
    else [.unencodedRight law.kind law.declaration])

def encodeLaw (language : LanguageDef) (law : Law) :
    Option (Mettapedia.UniversalAlgebra.Equation (signature language)) :=
  if unresolved language law = [] then do
    let left ← encode language (law.context.map Prod.fst) law.left
    let right ← encode language (law.context.map Prod.fst) law.right
    some (left, right)
  else none

structure Compilation (language : LanguageDef) where
  laws : List Law
  system : EquationSystem (signature language)
  diagnostics : List Diagnostic

def compileLaws (language : LanguageDef) (laws : List Law) : Compilation language where
  laws := laws
  system := ⟨laws.filterMap (encodeLaw language)⟩
  diagnostics := laws.flatMap (unresolved language)

def equations (language : LanguageDef) : Compilation language := compileLaws language (equationLaws language)

def rewrites (language : LanguageDef) : Compilation language := compileLaws language (rewriteLaws language)

/-- The three-valued result preserves unresolved source laws. -/
def Compilation.check? {language : LanguageDef} (compiled : Compilation language)
    (vertex : Mettapedia.OSLF.NativeTypes.SortProfiles.EquationalCenter.Vertex (signature language)) : Option Bool :=
  if compiled.diagnostics = [] then some (Mettapedia.OSLF.NativeTypes.SortProfiles.EquationalCenter.check compiled.system vertex)
  else none

theorem Compilation.check?_some_iff {language : LanguageDef} (compiled : Compilation language)
    (vertex : Mettapedia.OSLF.NativeTypes.SortProfiles.EquationalCenter.Vertex (signature language)) (answer : Bool) :
    compiled.check? vertex = some answer ↔
      compiled.diagnostics = [] ∧ Mettapedia.OSLF.NativeTypes.SortProfiles.EquationalCenter.check compiled.system vertex = answer := by
  by_cases complete : compiled.diagnostics = []
  · simp [Compilation.check?, complete]
  · simp [Compilation.check?, complete]

theorem Compilation.check?_true_iff {language : LanguageDef} (compiled : Compilation language)
    (vertex : Mettapedia.OSLF.NativeTypes.SortProfiles.EquationalCenter.Vertex (signature language)) :
    compiled.check? vertex = some true ↔
      compiled.diagnostics = [] ∧ Mettapedia.OSLF.NativeTypes.SortProfiles.EquationalCenter.Stable compiled.system vertex := by
  rw [Compilation.check?_some_iff, Mettapedia.OSLF.NativeTypes.SortProfiles.EquationalCenter.check_iff_stable]

theorem compiled_equation_member (language : LanguageDef) (laws : List Law)
    (equation : Mettapedia.UniversalAlgebra.Equation (signature language)) :
    equation ∈ (compileLaws language laws).system.equations ↔
      ∃ law ∈ laws, encodeLaw language law = some equation := by
  exact List.mem_filterMap

theorem conditional_is_unresolved (language : LanguageDef) (law : Law)
    (conditional : law.premises ≠ []) :
    Diagnostic.conditionalPremises law.kind law.declaration law.premises ∈ unresolved language law := by
  simp [unresolved, conditional]

theorem conditional_cannot_encode (language : LanguageDef) (law : Law)
    (conditional : law.premises ≠ []) : encodeLaw language law = none := by
  have member := conditional_is_unresolved language law conditional
  have notEmpty : unresolved language law ≠ [] := by
    intro empty
    rw [empty] at member
    cases member
  simp [encodeLaw, notEmpty]

end Mettapedia.OSLF.NativeTypes.SortProfiles.Laws.Compiler
