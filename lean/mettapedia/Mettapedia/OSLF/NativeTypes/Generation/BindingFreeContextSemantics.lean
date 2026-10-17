import Mettapedia.OSLF.NativeTypes.Generation.BindingCarrierSemantics
import Mettapedia.GSLT.LanguageDef.WellSortedClosing
import Mettapedia.OSLF.MeTTaIL.ClosingRepresentation
import Mettapedia.OSLF.MeTTaIL.NameSubstitutionLaws
import Mettapedia.GSLT.LanguageDef.NamedFreeContext

/-!
# Finite declared free names in the authored binder interpretation

An ordered finite base-sort assignment is closed outside the existing bound
context, without moving its bound indices or changing binder metadata. The
inverse opens those same positions in reverse order. Both operations act on
the original pattern. Every independently typed source body is represented
by an intrinsic term and reconstructs its exact source, including free names.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Generation.BindingCarrierSemantics

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Substitution
open Mettapedia.OSLF.MeTTaIL.ClosingRepresentation
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.Poly.BindingLanguage
open Mettapedia.OSLF.Binding

abbrev FreeDeclarations := List (String × String)

def freeContext : FreeDeclarations → FreeTypeContext
  | [] => FreeTypeContext.empty
  | (name, sort) :: rest => fun actual =>
      if actual = name then some (.base sort) else freeContext rest actual

/-- The base-sort profile specializes the shared finite context action. -/
def closeFree (depth : Nat) (declarations : FreeDeclarations) (pattern : Pattern) : Pattern :=
  Mettapedia.GSLT.LanguageDef.NamedFreeContext.closeNames depth
    (declarations.map Prod.fst) pattern

def openFree (depth : Nat) (declarations : FreeDeclarations) (pattern : Pattern) : Pattern :=
  Mettapedia.GSLT.LanguageDef.NamedFreeContext.openNames depth
    (declarations.map Prod.fst) pattern

/-- The legacy base-sort context is the same first-match source assignment. -/
theorem freeContext_eq_ofList (declarations : FreeDeclarations) :
    freeContext declarations = FreeTypeContext.ofList
      (declarations.map (fun entry => (entry.1, TypeExpr.base entry.2))) := by
  funext actual
  induction declarations with
  | nil => rfl
  | cons entry rest ih =>
      rcases entry with ⟨name, sort⟩
      by_cases same : actual = name
      · simp [freeContext, FreeTypeContext.ofList, same]
      · simp only [freeContext, List.map_cons, FreeTypeContext.ofList,
          if_neg same, if_neg (Ne.symm same), ih]

mutual
  theorem object_free_names (pattern : Pattern) (object : isObjectPattern pattern = true) :
      pattern.freeFvarNames = freeVars pattern := by
    cases pattern with
    | bvar => simp only [Pattern.freeFvarNames, freeVars]
    | fvar => simp only [Pattern.freeFvarNames, freeVars]
    | apply constructor arguments =>
        simpa only [Pattern.freeFvarNames, freeVars] using object_free_names_list arguments object
    | lambda binder body => simpa only [Pattern.freeFvarNames, freeVars] using object_free_names body object
    | multiLambda arity binders body => simpa only [Pattern.freeFvarNames, freeVars] using object_free_names body object
    | subst => simp [isObjectPattern] at object
    | collection kind elements rest =>
        have absent : rest = none := by
          cases rest <;> simp [isObjectPattern] at object ⊢
        subst rest
        simpa only [Pattern.freeFvarNames, freeVars, Option.toList_none,
          List.append_nil] using object_free_names_list elements object
  termination_by sizeOf pattern

  theorem object_free_names_list (patterns : List Pattern)
      (objects : isObjectPatternList patterns = true) :
      patterns.flatMap Pattern.freeFvarNames = patterns.flatMap freeVars := by
    cases patterns with
    | nil => rfl
    | cons pattern patterns =>
        simp only [isObjectPatternList, Bool.and_eq_true] at objects
        simp only [List.flatMap_cons, object_free_names pattern objects.1,
          object_free_names_list patterns objects.2]
  termination_by sizeOf patterns
end

theorem close_name_absent (pattern : Pattern) (object : isObjectPattern pattern = true)
    (depth : Nat) (name : String) :
    name ∉ (closeFVar depth name pattern).freeFvarNames := by
  rw [object_free_names _ (by rw [isObjectPattern_closeFVar]; exact object)]
  intro member
  exact ((freeVars_closeFVar_iff pattern depth name name).mp member).1 rfl

theorem closeFree_object (depth : Nat) (declarations : FreeDeclarations) (pattern : Pattern) :
    isObjectPattern (closeFree depth declarations pattern) = isObjectPattern pattern :=
  Mettapedia.GSLT.LanguageDef.NamedFreeContext.closeNames_object depth
    (declarations.map Prod.fst) pattern

/-- Closing consumes the selected free lookup and preserves every other
lookup. The old object-profile argument is retained by this specialization. -/
theorem close_one_typed {language : LanguageDef} {bound : List TypeExpr}
    {pattern : Pattern} {type : TypeExpr} (name sort : String)
    (rest : FreeDeclarations)
    (typed : HasType language (freeContext ((name, sort) :: rest)) bound pattern type)
    (_object : isObjectPattern pattern = true) :
    HasType language (freeContext rest) (bound ++ [.base sort])
      (closeFVar bound.length name pattern) type :=
  typed.closeFVarInto name (.base sort) (by simp [freeContext])
    (by
      intro actual actualType distinct present
      simpa only [freeContext, if_neg distinct] using present)

/-- The base-sort interpretation reuses the full-TypeExpr closing theorem. -/
theorem closeFree_typed {language : LanguageDef} (declarations : FreeDeclarations)
    {bound : List TypeExpr} {pattern : Pattern} {type : TypeExpr}
    (typed : HasType language (freeContext declarations) bound pattern type)
    (_object : isObjectPattern pattern = true) :
    HasType language FreeTypeContext.empty
      (bound ++ declarations.map (fun entry => .base entry.2))
      (closeFree bound.length declarations pattern) type := by
  have closed := Mettapedia.GSLT.LanguageDef.NamedFreeContext.closeContext_typed
    (declarations.map (fun entry => (entry.1, TypeExpr.base entry.2)))
    (by rwa [← freeContext_eq_ofList])
  simpa only [Mettapedia.GSLT.LanguageDef.NamedFreeContext.closeContext,
    Mettapedia.GSLT.LanguageDef.NamedFreeContext.contextSorts, List.map_map,
    Function.comp_def, closeFree] using closed

/-- Opening reconstructs the same original source through the shared inverse. -/
theorem openFree_closeFree {language : LanguageDef} (declarations : FreeDeclarations)
    {bound : List TypeExpr} {pattern : Pattern} {type : TypeExpr}
    (typed : HasType language (freeContext declarations) bound pattern type)
    (_object : isObjectPattern pattern = true) :
    openFree bound.length declarations (closeFree bound.length declarations pattern) = pattern :=
  Mettapedia.GSLT.LanguageDef.NamedFreeContext.openNames_closeNames bound.length
    (declarations.map Prod.fst) pattern
    (by rw [← isWellScopedAt_eq_lc_at]; exact typed.isWellScopedAt)

abbrev FreeTypedObject (language : LanguageDef) (declarations : FreeDeclarations)
    (context : List String) (sort : String) :=
  {pattern : Pattern // HasType language (freeContext declarations) (typeContext context)
    pattern (.base sort) ∧ isObjectPattern pattern = true}

/-- Each original finite free-context source body is encoded by the actual
intrinsic binding syntax after its free variables are closed at known slots. -/
noncomputable def encodeFree {language : LanguageDef}
    (fragment : ∀ declaration ∈ language.terms, BinderRule declaration)
    (labels : (language.terms.map (·.label)).Nodup)
    (declarations : FreeDeclarations) (context : List String) (sort : String)
    (source : FreeTypedObject language declarations context sort) :
    Term (signature language) (context ++ declarations.map Prod.snd) sort :=
  (sourceEquiv fragment labels _ _).symm
    ⟨closeFree context.length declarations source.val,
      by simpa only [typeContext, List.map_append, List.map_map, List.length_map, Function.comp_def]
        using closeFree_typed declarations source.2.1 source.2.2,
      by rw [closeFree_object]; exact source.2.2⟩

theorem encodeFree_readback {language : LanguageDef}
    (fragment : ∀ declaration ∈ language.terms, BinderRule declaration)
    (labels : (language.terms.map (·.label)).Nodup)
    (declarations : FreeDeclarations) (context : List String) (sort : String)
    (source : FreeTypedObject language declarations context sort) :
    openFree context.length declarations (toPattern (encodeFree fragment labels declarations context sort source)) =
      source.val := by
  have printed := congrArg Subtype.val ((sourceEquiv fragment labels
    (context ++ declarations.map Prod.snd) sort).apply_symm_apply
      ⟨closeFree context.length declarations source.val,
        by simpa only [typeContext, List.map_append, List.map_map, List.length_map, Function.comp_def]
          using closeFree_typed declarations source.2.1 source.2.2,
        by rw [closeFree_object]; exact source.2.2⟩)
  change toPattern (encodeFree fragment labels declarations context sort source) =
    closeFree context.length declarations source.val at printed
  rw [printed]
  simpa only [typeContext, List.length_map] using
    openFree_closeFree declarations source.2.1 source.2.2

theorem encodeFree_injective {language : LanguageDef}
    (fragment : ∀ declaration ∈ language.terms, BinderRule declaration)
    (labels : (language.terms.map (·.label)).Nodup)
    (declarations : FreeDeclarations) (context : List String) (sort : String) :
    Function.Injective (encodeFree (language := language) fragment labels declarations context sort) := by
  intro left right same
  apply Subtype.ext
  rw [← encodeFree_readback fragment labels declarations context sort left,
    ← encodeFree_readback fragment labels declarations context sort right, same]

end Mettapedia.OSLF.NativeTypes.Generation.BindingCarrierSemantics
