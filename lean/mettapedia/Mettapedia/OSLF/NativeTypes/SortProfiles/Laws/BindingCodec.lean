import Mettapedia.GSLT.LanguageDef.ScopedBindingElaboration
import Mettapedia.OSLF.NativeTypes.SortProfiles.Laws.FiniteBinding
import Mettapedia.OSLF.NativeTypes.SortProfiles.Laws.Compiler

open Mettapedia.OSLF.Framework

/-!
# Source-derived binding-law terms with semantic substitution

The codec reuses the existing declaration and scoped occurrence compiler.
Lambda and explicit-substitution wrappers have a separate semantic route:
substitution is the actual intrinsic binding operator, not a unary display
symbol. Every success proves source typing and exact readback and retains
the source occurrence evidence. Its finite intermediate-type candidates are
derived from authored declarations and contexts; failed classification is
unresolved and does not refute the source law.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.SortProfiles.Laws.BindingCodec

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.RuleBinding
open Mettapedia.OSLF.Binding
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.LanguageDef.BindingSyntax
open Mettapedia.GSLT.LanguageDef.BindingSyntax.ScopedElaboration
open Mettapedia.GSLT.LanguageDef.BindingSyntax.ScopedElaboration.SchemaElaboration

def typeParts : TypeExpr → List TypeExpr
  | type@(.base _) => [type]
  | type@(.arrow domain codomain) => type :: (typeParts domain ++ typeParts codomain)
  | type@(.multiBinder domain) => type :: typeParts domain
  | type@(.collection _ element) => type :: typeParts element

def typeCandidates (language : LanguageDef) (rule : RewriteRule)
    (locals : List TypeExpr) (expected : TypeExpr) : List TypeExpr :=
  ((language.types.map fun declaration => TypeExpr.base declaration.name) ++
    (rule.typeContext.map Prod.snd).flatMap typeParts ++ locals.flatMap typeParts ++
    language.terms.flatMap (fun declaration => declaration.params.flatMap fun parameter =>
      (parameterType? parameter).toList.flatMap typeParts) ++ typeParts expected).eraseDups

structure Compiled (language : LanguageDef) (rule : RewriteRule) (spec : RuleBindingSpec)
    (locals : List TypeExpr) (source : Pattern) (type : TypeExpr) where
  term : Term (SchemaSignature language rule spec) (locals ++ []) type
  source_readback : readback term = source
  source_typed : HasType language (FreeTypeContext.ofList rule.typeContext) locals source type
  inputOccurrences : List (InputEvidence language rule spec)
  constructorOccurrences : List (List Nat × Fin language.terms.length)

def Compiled.lambda {language : LanguageDef} {rule : RewriteRule} {spec : RuleBindingSpec}
    {locals : List TypeExpr} {source : Pattern} {domain codomain : TypeExpr}
    (body : Compiled language rule spec (domain :: locals) source codomain) :
    Compiled language rule spec locals (.lambda none source) (.arrow domain codomain) where
  term := .op (.inl (.lambda domain codomain)) (.cons body.term .nil)
  source_readback := by change Pattern.lambda none (readback body.term) = _; rw [body.source_readback]
  source_typed := .lambda body.source_typed
  inputOccurrences := body.inputOccurrences
  constructorOccurrences := body.constructorOccurrences

def Compiled.substitution {language : LanguageDef} {rule : RewriteRule} {spec : RuleBindingSpec}
    {locals : List TypeExpr} {body replacement : Pattern} {domain codomain : TypeExpr}
    (first : Compiled language rule spec (domain :: locals) body codomain)
    (second : Compiled language rule spec locals replacement domain) :
    Compiled language rule spec locals (.subst body replacement) codomain where
  term := .op (.inl (.subst domain codomain)) (.cons first.term (.cons second.term .nil))
  source_readback := by
    change Pattern.subst (readback first.term) (readback second.term) = _
    rw [first.source_readback, second.source_readback]
  source_typed := .subst first.source_typed second.source_typed
  inputOccurrences := first.inputOccurrences ++ second.inputOccurrences
  constructorOccurrences := first.constructorOccurrences ++ second.constructorOccurrences

def compileWithFuel? (language : LanguageDef) (rule : RewriteRule) (spec : RuleBindingSpec)
    (site : RulePatternSite) : Nat → (locals : List TypeExpr) → (path : List Nat) →
      (source : Pattern) → (type : TypeExpr) → Option (Compiled language rule spec locals source type)
  | 0, _, _, _, _ => none
  | fuel + 1, locals, path, source, type =>
      match compileSchemaWithFuel? language rule spec site (fuel + 1) locals path source type with
      | some original =>
          if typed : checkHasType language (FreeTypeContext.ofList rule.typeContext) locals source type = true then
            some {
              term := original.term
              source_readback := original.source_readback
              source_typed := checkHasType_sound typed
              inputOccurrences := original.inputOccurrences
              constructorOccurrences := original.constructorOccurrences}
          else none
      | none =>
          match source, type with
          | .lambda none body, .arrow domain codomain =>
              (compileWithFuel? language rule spec site fuel (domain :: locals) (path ++ [0]) body codomain).map
                Compiled.lambda
          | .subst body replacement, codomain =>
              (typeCandidates language rule locals codomain).findSome? fun domain => do
                let first ← compileWithFuel? language rule spec site fuel (domain :: locals) (path ++ [0]) body codomain
                let second ← compileWithFuel? language rule spec site fuel locals (path ++ [1]) replacement domain
                pure (Compiled.substitution first second)
          | _, _ => none

def lawRule (law : Mettapedia.OSLF.NativeTypes.SortProfiles.Laws.Compiler.Law) : RewriteRule :=
  {name := law.name, typeContext := law.context, premises := law.premises,
    left := law.left, right := law.right, bindings := law.bindings}

structure CompiledLaw (language : LanguageDef) (law : Mettapedia.OSLF.NativeTypes.SortProfiles.Laws.Compiler.Law) (type : TypeExpr) where
  spec : RuleBindingSpec
  attached : (lawRule law).bindings = some spec
  admitted : admittedFor (lawRule law) spec = true
  dependencySorts : dependencySortsDeclared language spec = true
  left : Compiled language (lawRule law) spec [] law.left type
  right : Compiled language (lawRule law) spec [] law.right type

def compileLaw? (language : LanguageDef) (law : Mettapedia.OSLF.NativeTypes.SortProfiles.Laws.Compiler.Law) (type : TypeExpr) :
    Option (CompiledLaw language law type) := do
  let spec ← (lawRule law).bindings
  if attached : (lawRule law).bindings = some spec then
    if admitted : admittedFor (lawRule law) spec = true then
      if declared : dependencySortsDeclared language spec = true then
        let left ← compileWithFuel? language (lawRule law) spec .left (sourceHeight law.left) [] [] law.left type
        let right ← compileWithFuel? language (lawRule law) spec .right (sourceHeight law.right) [] [] law.right type
        pure ⟨spec, attached, admitted, declared, left, right⟩
      else none
    else none
  else none

theorem compilation_retains_original_source {language : LanguageDef} {law : Mettapedia.OSLF.NativeTypes.SortProfiles.Laws.Compiler.Law}
    {type : TypeExpr} {compiled : CompiledLaw language law type}
    (_computed : compileLaw? language law type = some compiled) :
    HasType language (FreeTypeContext.ofList (lawRule law).typeContext) [] law.left type ∧
      HasType language (FreeTypeContext.ofList (lawRule law).typeContext) [] law.right type := by
  exact ⟨compiled.left.source_typed, compiled.right.source_typed⟩

theorem compilation_exact_readback {language : LanguageDef} {law : Mettapedia.OSLF.NativeTypes.SortProfiles.Laws.Compiler.Law}
    {type : TypeExpr} {compiled : CompiledLaw language law type}
    (_computed : compileLaw? language law type = some compiled) :
    readback compiled.left.term = law.left ∧ readback compiled.right.term = law.right :=
  ⟨compiled.left.source_readback, compiled.right.source_readback⟩

def CompiledLaw.check? {language : LanguageDef} {law : Mettapedia.OSLF.NativeTypes.SortProfiles.Laws.Compiler.Law} {type : TypeExpr}
    (compiled : CompiledLaw language law type) (constructors : Mettapedia.OSLF.NativeTypes.SortProfiles.Laws.FiniteBinding.Constructors language) :
    Option Bool :=
  if finiteMetas : Mettapedia.OSLF.NativeTypes.SortProfiles.Laws.FiniteBinding.finiteMetaContext (metaArities (language := language) (lawRule law) compiled.spec) = true then
    if finiteResult : Mettapedia.OSLF.NativeTypes.SortProfiles.Laws.FiniteBinding.finiteType type = true then
      some (Mettapedia.OSLF.NativeTypes.SortProfiles.Laws.FiniteBinding.check language constructors (metaArities (language := language) (lawRule law) compiled.spec)
        compiled.left.term compiled.right.term finiteMetas rfl finiteResult)
    else none
  else none

theorem compiled_semantic_check_exact {language : LanguageDef} {law : Mettapedia.OSLF.NativeTypes.SortProfiles.Laws.Compiler.Law}
    {type : TypeExpr} (compiled : CompiledLaw language law type)
    (constructors : Mettapedia.OSLF.NativeTypes.SortProfiles.Laws.FiniteBinding.Constructors language) :
    compiled.check? constructors = some true ↔
      Mettapedia.OSLF.NativeTypes.SortProfiles.Laws.FiniteBinding.finiteMetaContext (metaArities (language := language) (lawRule law) compiled.spec) = true ∧
        Mettapedia.OSLF.NativeTypes.SortProfiles.Laws.FiniteBinding.finiteType type = true ∧
          Mettapedia.OSLF.NativeTypes.SortProfiles.Laws.FiniteBinding.Satisfies language constructors
            (metaArities (language := language) (lawRule law) compiled.spec) compiled.left.term compiled.right.term := by
  unfold CompiledLaw.check?
  split
  · rename_i metaFinite
    split
    · rename_i resultFinite
      simp only [Option.some.injEq, resultFinite, true_and]
      rw [Mettapedia.OSLF.NativeTypes.SortProfiles.Laws.FiniteBinding.check_iff language constructors
        (metaArities (language := language) (lawRule law) compiled.spec)
        compiled.left.term compiled.right.term metaFinite rfl resultFinite]
      exact ⟨fun satisfied => ⟨metaFinite, satisfied⟩, fun admitted => admitted.2⟩
    · rename_i resultNotFinite
      simp [resultNotFinite]
  · rename_i metaNotFinite
    simp [metaNotFinite]

end Mettapedia.OSLF.NativeTypes.SortProfiles.Laws.BindingCodec
