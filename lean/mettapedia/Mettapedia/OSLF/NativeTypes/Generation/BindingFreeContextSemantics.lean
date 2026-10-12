import Mettapedia.OSLF.NativeTypes.Generation.BindingCarrierSemantics
import Mettapedia.GSLT.LanguageDef.WellSortedClosing
import Mettapedia.OSLF.MeTTaIL.ClosingRepresentation
import Mettapedia.OSLF.MeTTaIL.NameSubstitutionLaws

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

def closeFree (depth : Nat) : FreeDeclarations → Pattern → Pattern
  | [], pattern => pattern
  | (name, _) :: rest, pattern => closeFree (depth + 1) rest (closeFVar depth name pattern)

def openFree (depth : Nat) : FreeDeclarations → Pattern → Pattern
  | [], pattern => pattern
  | (name, _) :: rest, pattern => openBVar depth (.fvar name) (openFree (depth + 1) rest pattern)

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
    isObjectPattern (closeFree depth declarations pattern) = isObjectPattern pattern := by
  induction declarations generalizing depth pattern with
  | nil => rfl
  | cons entry rest ih =>
      simp only [closeFree, ih, isObjectPattern_closeFVar]

/-- Closing consumes the free lookup only after its actual occurrences have
been replaced. Other declarations retain their original meanings. -/
theorem close_one_typed {language : LanguageDef} {bound : List TypeExpr}
    {pattern : Pattern} {type : TypeExpr} (name sort : String)
    (rest : FreeDeclarations)
    (typed : HasType language (freeContext ((name, sort) :: rest)) bound pattern type)
    (object : isObjectPattern pattern = true) :
    HasType language (freeContext rest) (bound ++ [.base sort])
      (closeFVar bound.length name pattern) type := by
  have closed := typed.closeFVar name (.base sort) (by simp [freeContext])
  apply closed.recontextualizeFree
  intro actual actualType member lookup
  have distinct : actual ≠ name := by
    intro same
    subst actual
    exact close_name_absent pattern object bound.length name member
  simpa only [freeContext, if_neg distinct] using lookup

/-- The independent authored typing judgment certifies every closed body
at its computed combined bound context, for every finite declaration list. -/
theorem closeFree_typed {language : LanguageDef} (declarations : FreeDeclarations)
    {bound : List TypeExpr} {pattern : Pattern} {type : TypeExpr}
    (typed : HasType language (freeContext declarations) bound pattern type)
    (object : isObjectPattern pattern = true) :
    HasType language FreeTypeContext.empty
      (bound ++ declarations.map (fun entry => .base entry.2))
      (closeFree bound.length declarations pattern) type := by
  induction declarations generalizing bound pattern with
  | nil => simpa only [List.map_nil, List.append_nil, closeFree, freeContext] using typed
  | cons entry rest ih =>
      obtain ⟨name, sort⟩ := entry
      have closed := close_one_typed name sort rest typed object
      have closedObject : isObjectPattern (closeFVar bound.length name pattern) = true := by
        rw [isObjectPattern_closeFVar]; exact object
      simpa only [List.map_cons, List.length_append, List.length_singleton,
        List.append_assoc, List.singleton_append, closeFree] using ih closed closedObject

/-- Actual opening reconstructs the original independently typed pattern,
including its named free occurrences and original binder display metadata. -/
theorem openFree_closeFree {language : LanguageDef} (declarations : FreeDeclarations)
    {bound : List TypeExpr} {pattern : Pattern} {type : TypeExpr}
    (typed : HasType language (freeContext declarations) bound pattern type)
    (object : isObjectPattern pattern = true) :
    openFree bound.length declarations (closeFree bound.length declarations pattern) = pattern := by
  induction declarations generalizing bound pattern with
  | nil => rfl
  | cons entry rest ih =>
      obtain ⟨name, sort⟩ := entry
      have closed := close_one_typed name sort rest typed object
      have closedObject : isObjectPattern (closeFVar bound.length name pattern) = true := by
        rw [isObjectPattern_closeFVar]; exact object
      have recovered := ih closed closedObject
      simp only [List.length_append, List.length_singleton] at recovered
      simp only [openFree, closeFree, recovered]
      exact open_close_id _ _ _
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
