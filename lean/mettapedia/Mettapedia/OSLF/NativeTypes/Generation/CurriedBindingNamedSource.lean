import Mettapedia.OSLF.NativeTypes.Generation.CurriedNativeAdequacy
import Mettapedia.GSLT.LanguageDef.WellSortedOpening

/-!
# Named finite contexts in the computed curried binding interpretation

Closing and reopening the actual finite declarations produces an independent
source comparison. Surviving bound indices and authored declaration origins
are unchanged. A distinct-name premise is used for the two-sided comparison;
the source receipt retains original display metadata outside alpha erasure.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Generation.CurriedBindingLanguage

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Substitution
open Mettapedia.OSLF.MeTTaIL.ClosingRepresentation
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.Binding
open BindingSemanticAdmission
open BindingCarrierSemantics (FreeDeclarations freeContext closeFree openFree)

variable {language : LanguageDef}

mutual
  theorem openFVar_shape (pattern : Pattern) (depth : Nat) (name : String) :
      isObjectPattern (openBVar depth (.fvar name) pattern) = isObjectPattern pattern ∧
      (openBVar depth (.fvar name) pattern).hasCanonicalBinderMetadata = pattern.hasCanonicalBinderMetadata := by
    cases pattern with
    | bvar index => simp only [openBVar]; split_ifs <;> exact ⟨rfl, rfl⟩
    | fvar => simp [openBVar, isObjectPattern, Pattern.hasCanonicalBinderMetadata]
    | apply constructor arguments =>
        simpa only [openBVar, isObjectPattern, Pattern.hasCanonicalBinderMetadata] using
          openFVar_list_shape arguments depth name
    | lambda binder body =>
        obtain ⟨object, canonical⟩ := openFVar_shape body (depth + 1) name
        simp only [openBVar, isObjectPattern, Pattern.hasCanonicalBinderMetadata, object, canonical]
        trivial
    | multiLambda arity binders body =>
        obtain ⟨object, canonical⟩ := openFVar_shape body (depth + arity) name
        simp only [openBVar, isObjectPattern, Pattern.hasCanonicalBinderMetadata, object, canonical]
        trivial
    | subst body replacement =>
        obtain ⟨_, bodyCanonical⟩ := openFVar_shape body (depth + 1) name
        obtain ⟨_, replacementCanonical⟩ := openFVar_shape replacement depth name
        simp only [openBVar, isObjectPattern, Pattern.hasCanonicalBinderMetadata,
          bodyCanonical, replacementCanonical]
        trivial
    | collection kind elements rest =>
        obtain ⟨object, canonical⟩ := openFVar_list_shape elements depth name
        simp only [openBVar, isObjectPattern, Pattern.hasCanonicalBinderMetadata, object, canonical]
        trivial
  termination_by sizeOf pattern

  theorem openFVar_list_shape (patterns : List Pattern) (depth : Nat) (name : String) :
      isObjectPatternList (patterns.map (openBVar depth (.fvar name))) = isObjectPatternList patterns ∧
      Pattern.hasCanonicalBinderMetadataList (patterns.map (openBVar depth (.fvar name))) =
        Pattern.hasCanonicalBinderMetadataList patterns := by
    cases patterns with
    | nil => exact ⟨rfl, rfl⟩
    | cons pattern patterns =>
        obtain ⟨object, canonical⟩ := openFVar_shape pattern depth name
        obtain ⟨objects, canonicals⟩ := openFVar_list_shape patterns depth name
        simp only [List.map_cons, isObjectPatternList, Pattern.hasCanonicalBinderMetadataList,
          object, canonical, objects, canonicals]
        trivial
  termination_by sizeOf patterns
end

theorem openFree_shape (declarations : FreeDeclarations) (depth : Nat) (pattern : Pattern) :
    isObjectPattern (openFree depth declarations pattern) = isObjectPattern pattern ∧
    (openFree depth declarations pattern).hasCanonicalBinderMetadata = pattern.hasCanonicalBinderMetadata := by
  induction declarations generalizing depth with
  | nil => exact ⟨rfl, rfl⟩
  | cons entry rest ih =>
      obtain ⟨object, canonical⟩ := openFVar_shape (openFree (depth + 1) rest pattern) depth entry.1
      obtain ⟨objects, canonicals⟩ := ih (depth + 1)
      exact ⟨object.trans objects, canonical.trans canonicals⟩

theorem freeContext_lookup (declarations : FreeDeclarations)
    (distinct : (declarations.map Prod.fst).Nodup) {entry : String × String}
    (member : entry ∈ declarations) : freeContext declarations entry.1 = some (.base entry.2) := by
  induction declarations with
  | nil => cases member
  | cons first rest ih =>
      simp only [List.map_cons, List.nodup_cons] at distinct
      rcases List.mem_cons.mp member with same | tail
      · subst entry; simp [freeContext]
      · have different : entry.1 ≠ first.1 := by
          intro equality
          exact distinct.1 (equality ▸ List.mem_map.mpr ⟨entry, tail, rfl⟩)
        simpa only [freeContext, if_neg different] using ih distinct.2 tail

theorem openFree_typed (declarations : FreeDeclarations) {free : FreeTypeContext}
    (lookups : ∀ entry ∈ declarations, free entry.1 = some (.base entry.2))
    {bound : List TypeExpr} {pattern : Pattern} {type : TypeExpr}
    (typed : HasType language free (bound ++ declarations.map (fun entry => .base entry.2)) pattern type) :
    HasType language free bound (openFree bound.length declarations pattern) type := by
  have opened := Mettapedia.GSLT.LanguageDef.NamedFreeContext.openContext_typed
    (declarations.map (fun entry => (entry.1, TypeExpr.base entry.2)))
    (by
      intro entry member
      obtain ⟨original, present, rfl⟩ := List.mem_map.mp member
      exact lookups original present)
    (by simpa only [Mettapedia.GSLT.LanguageDef.NamedFreeContext.contextSorts,
      List.map_map, Function.comp_def] using typed)
  simpa only [Mettapedia.GSLT.LanguageDef.NamedFreeContext.openContext,
    List.map_map, Function.comp_def, openFree] using opened

mutual
  theorem freeVars_openFVar_subset (pattern : Pattern) (depth : Nat) (name actual : String)
      (member : actual ∈ freeVars (openBVar depth (.fvar name) pattern)) :
      actual = name ∨ actual ∈ freeVars pattern := by
    cases pattern with
    | bvar index =>
        simp only [openBVar] at member
        split_ifs at member
        · exact .inl (by simpa only [freeVars, List.mem_singleton] using member)
        · simp only [freeVars, List.not_mem_nil] at member
    | fvar => exact .inr (by simpa only [openBVar] using member)
    | apply constructor arguments =>
        simpa only [freeVars] using freeVars_openFVar_list_subset arguments depth name actual
          (by simpa only [openBVar, freeVars] using member)
    | lambda binder body =>
        simpa only [freeVars] using freeVars_openFVar_subset body (depth + 1) name actual
          (by simpa only [openBVar, freeVars] using member)
    | multiLambda arity binders body =>
        simpa only [freeVars] using freeVars_openFVar_subset body (depth + arity) name actual
          (by simpa only [openBVar, freeVars] using member)
    | subst body replacement =>
        simp only [openBVar, freeVars] at member ⊢
        rcases List.mem_append.mp member with bodyMember | replacementMember
        · rcases freeVars_openFVar_subset body (depth + 1) name actual bodyMember with same | original
          · exact .inl same
          · exact .inr (List.mem_append_left _ original)
        · rcases freeVars_openFVar_subset replacement depth name actual replacementMember with same | original
          · exact .inl same
          · exact .inr (List.mem_append_right _ original)
    | collection kind elements rest =>
        simpa only [freeVars] using freeVars_openFVar_list_subset elements depth name actual
          (by simpa only [openBVar, freeVars] using member)
  termination_by sizeOf pattern

  theorem freeVars_openFVar_list_subset (patterns : List Pattern) (depth : Nat) (name actual : String)
      (member : actual ∈ (patterns.map (openBVar depth (.fvar name))).flatMap freeVars) :
      actual = name ∨ actual ∈ patterns.flatMap freeVars := by
    obtain ⟨opened, present, member⟩ := List.mem_flatMap.mp member
    obtain ⟨pattern, sourceMember, rfl⟩ := List.mem_map.mp present
    rcases freeVars_openFVar_subset pattern depth name actual member with same | original
    · exact .inl same
    · exact .inr (List.mem_flatMap.mpr ⟨pattern, sourceMember, original⟩)
  termination_by sizeOf patterns
end

theorem freeVars_openFree_subset (declarations : FreeDeclarations) (depth : Nat) (pattern : Pattern)
    (actual : String) (member : actual ∈ freeVars (openFree depth declarations pattern)) :
    actual ∈ declarations.map Prod.fst ∨ actual ∈ freeVars pattern := by
  induction declarations generalizing depth with
  | nil => exact .inr member
  | cons entry rest ih =>
      rcases freeVars_openFVar_subset (openFree (depth + 1) rest pattern) depth entry.1 actual member with same | previous
      · exact .inl (List.mem_cons.mpr (.inl same))
      · rcases ih (depth + 1) previous with declared | original
        · exact .inl (List.mem_cons.mpr (.inr declared))
        · exact .inr original

theorem closeFree_openFree (declarations : FreeDeclarations)
    (distinct : (declarations.map Prod.fst).Nodup) (depth : Nat) (pattern : Pattern)
    (fresh : ∀ name ∈ declarations.map Prod.fst, name ∉ freeVars pattern) :
    closeFree depth declarations (openFree depth declarations pattern) = pattern := by
  induction declarations generalizing depth with
  | nil => rfl
  | cons entry rest ih =>
      simp only [List.map_cons, List.nodup_cons] at distinct
      have absent : entry.1 ∉ freeVars (openFree (depth + 1) rest pattern) := by
        intro member
        rcases freeVars_openFree_subset rest (depth + 1) pattern entry.1 member with declared | original
        · exact distinct.1 declared
        · exact fresh entry.1 List.mem_cons_self original
      have closeOpen : closeFVar depth entry.1
          (openBVar depth (.fvar entry.1)
            (Mettapedia.GSLT.LanguageDef.NamedFreeContext.openNames (depth + 1)
              (rest.map Prod.fst) pattern)) =
          Mettapedia.GSLT.LanguageDef.NamedFreeContext.openNames (depth + 1)
            (rest.map Prod.fst) pattern := close_open_id depth entry.1 _ absent
      simp only [openFree, closeFree, List.map_cons,
        Mettapedia.GSLT.LanguageDef.NamedFreeContext.openNames,
        Mettapedia.GSLT.LanguageDef.NamedFreeContext.closeNames]
      rw [closeOpen]
      simpa only [openFree, closeFree] using
        ih distinct.2 (depth + 1) (fun name member => fresh name (List.mem_cons_of_mem _ member))

abbrev NamedSource (language : LanguageDef) (declarations : FreeDeclarations)
    (context : List String) (sort : String) :=
  {pattern : Pattern // HasType language (freeContext declarations)
      (Mettapedia.GSLT.Poly.BindingLanguage.typeContext context) pattern (.base sort) ∧
    isObjectPattern pattern = true ∧ pattern.hasCanonicalBinderMetadata = true}

theorem closeFree_canonical (declarations : FreeDeclarations) (depth : Nat) (pattern : Pattern) :
    (closeFree depth declarations pattern).hasCanonicalBinderMetadata = pattern.hasCanonicalBinderMetadata := by
  induction declarations generalizing depth pattern with
  | nil => rfl
  | cons entry rest ih =>
      exact (ih (depth + 1) (closeFVar depth entry.1 pattern)).trans
        (hasCanonicalBinderMetadata_closeFVar pattern depth entry.1)

noncomputable def encodeNamed (admitted : Admitted language)
    (labels : (language.terms.map (·.label)).Nodup) (declarations : FreeDeclarations)
    (context : List String) (sort : String) (source : NamedSource language declarations context sort) :
    Term (signature language) (context ++ declarations.map Prod.snd) sort :=
  (sourceEquiv admitted labels _ _).symm
    ⟨closeFree context.length declarations source.val,
      by simpa only [Mettapedia.GSLT.Poly.BindingLanguage.typeContext, List.map_append,
        List.map_map, List.length_map, Function.comp_def] using
          BindingCarrierSemantics.closeFree_typed declarations source.2.1 source.2.2.1,
      (BindingCarrierSemantics.closeFree_object _ _ _).trans source.2.2.1,
      (closeFree_canonical _ _ _).trans source.2.2.2⟩

theorem encodeNamed_readback (admitted : Admitted language)
    (labels : (language.terms.map (·.label)).Nodup) (declarations : FreeDeclarations)
    (context : List String) (sort : String) (source : NamedSource language declarations context sort) :
    openFree context.length declarations (toPattern (encodeNamed admitted labels declarations context sort source)) =
      source.val := by
  have printed := congrArg Subtype.val ((sourceEquiv admitted labels
    (context ++ declarations.map Prod.snd) sort).apply_symm_apply
      ⟨closeFree context.length declarations source.val,
        by simpa only [Mettapedia.GSLT.Poly.BindingLanguage.typeContext, List.map_append,
          List.map_map, List.length_map, Function.comp_def] using
            BindingCarrierSemantics.closeFree_typed declarations source.2.1 source.2.2.1,
        (BindingCarrierSemantics.closeFree_object _ _ _).trans source.2.2.1,
        (closeFree_canonical _ _ _).trans source.2.2.2⟩)
  change toPattern (encodeNamed admitted labels declarations context sort source) =
    closeFree context.length declarations source.val at printed
  rw [printed]
  simpa only [Mettapedia.GSLT.Poly.BindingLanguage.typeContext, List.length_map] using
    BindingCarrierSemantics.openFree_closeFree declarations source.2.1 source.2.2.1

noncomputable def decodeNamed (declarations : FreeDeclarations)
    (distinct : (declarations.map Prod.fst).Nodup) (context : List String) (sort : String)
    (term : Term (signature language) (context ++ declarations.map Prod.snd) sort) :
    NamedSource language declarations context sort :=
  ⟨openFree context.length declarations (toPattern term), by
      have original := (toPattern_typed term).recontextualizeFree
        (target := freeContext declarations)
        (fun _ present => by simp [FreeTypeContext.empty] at present)
      have typed : HasType language (freeContext declarations)
          (Mettapedia.GSLT.Poly.BindingLanguage.typeContext context ++
            declarations.map (fun entry => .base entry.2)) (toPattern term) (.base sort) := by
        simpa only [Mettapedia.GSLT.Poly.BindingLanguage.typeContext, List.map_append,
          List.map_map, Function.comp_def] using original
      simpa only [Mettapedia.GSLT.Poly.BindingLanguage.typeContext, List.length_map] using
        openFree_typed declarations (fun entry member => freeContext_lookup declarations distinct member) typed,
    (openFree_shape _ _ _).1.trans (toPattern_object term),
    (openFree_shape _ _ _).2.trans (toPattern_canonical term)⟩

theorem printed_no_free {context : List String} {sort : String}
    (term : Term (signature language) context sort) (name : String) : name ∉ freeVars (toPattern term) := by
  intro member
  have named : name ∈ (toPattern term).freeFvarNames := by
    rw [BindingCarrierSemantics.object_free_names _ (toPattern_object term)]
    exact member
  obtain ⟨type, lookup⟩ := (toPattern_typed term).freeType_of_mem_freeFvarNames_of_isObjectPattern
    (toPattern_object term) named
  simp [FreeTypeContext.empty] at lookup

theorem encodeNamed_decodeNamed (admitted : Admitted language)
    (labels : (language.terms.map (·.label)).Nodup) (declarations : FreeDeclarations)
    (distinct : (declarations.map Prod.fst).Nodup) (context : List String) (sort : String)
    (term : Term (signature language) (context ++ declarations.map Prod.snd) sort) :
    encodeNamed admitted labels declarations context sort
      (decodeNamed declarations distinct context sort term) = term := by
  apply toPattern_injective labels
  have printed := congrArg Subtype.val ((sourceEquiv admitted labels
    (context ++ declarations.map Prod.snd) sort).apply_symm_apply
      ⟨closeFree context.length declarations (decodeNamed declarations distinct context sort term).val,
        by simpa only [Mettapedia.GSLT.Poly.BindingLanguage.typeContext, List.map_append,
          List.map_map, List.length_map, Function.comp_def] using
            BindingCarrierSemantics.closeFree_typed declarations
              (decodeNamed declarations distinct context sort term).2.1
              (decodeNamed declarations distinct context sort term).2.2.1,
        (BindingCarrierSemantics.closeFree_object _ _ _).trans
          (decodeNamed declarations distinct context sort term).2.2.1,
        (closeFree_canonical _ _ _).trans (decodeNamed declarations distinct context sort term).2.2.2⟩)
  exact printed.trans (closeFree_openFree declarations distinct context.length (toPattern term)
    (fun name _ => printed_no_free term name))

/-- Every original finite distinct-name context is compared in both
directions, with exact named readback and no ambient closedness restriction. -/
noncomputable def namedSourceEquiv (admitted : Admitted language)
    (labels : (language.terms.map (·.label)).Nodup) (declarations : FreeDeclarations)
    (distinct : (declarations.map Prod.fst).Nodup) (context : List String) (sort : String) :
    Term (signature language) (context ++ declarations.map Prod.snd) sort ≃
      NamedSource language declarations context sort where
  toFun := decodeNamed declarations distinct context sort
  invFun := encodeNamed admitted labels declarations context sort
  left_inv := encodeNamed_decodeNamed admitted labels declarations distinct context sort
  right_inv source := Subtype.ext (encodeNamed_readback admitted labels declarations context sort source)

end Mettapedia.OSLF.NativeTypes.Generation.CurriedBindingLanguage
