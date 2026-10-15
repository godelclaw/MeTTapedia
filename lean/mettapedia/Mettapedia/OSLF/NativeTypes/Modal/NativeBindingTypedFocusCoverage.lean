import Mettapedia.OSLF.NativeTypes.Modal.NativeBindingInstantiationArguments
import Mettapedia.OSLF.NativeTypes.Modal.NativeBindingMatchInstantiation
import Mettapedia.OSLF.NativeTypes.Modal.NativeFocusSubstitution

/-!
# Universal typed focus coverage through authored source instantiation

The generated typing descent is compared with independently typed actual
source inhabitants. Unique constructor labels recover the same authored
parameter at each context frame. No assignment-typing oracle or hand-written
site inventory supplies the local focus type.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Modal.NativeBindingTypedFocusCoverage

open Mettapedia.OSLF.MeTTaIL Syntax RuleBinding ScopedRuleMatching GeneralTypedSites
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.LanguageDef.GeneralTypedOccurrence (objectList_member)
open Mettapedia.OSLF.NativeTypes.Generation.TypedOccurrences
open NativeBindingInstantiationArguments NativeBindingMatchInstantiation Instantiation

theorem treeSchemas_member {patterns : List Pattern} {pattern : Pattern}
    (shape : treeSchemas patterns = true) (member : pattern ∈ patterns) :
    treeSchema pattern = true := by
  induction patterns with
  | nil => cases member
  | cons first rest ih =>
      simp only [treeSchemas, Bool.and_eq_true] at shape
      rcases List.mem_cons.mp member with same | later
      · exact same ▸ shape.1
      · exact ih shape.2 later

theorem instantiated_focus {language : LanguageDef} {schemaFree actualFree : FreeTypeContext}
    {permissions : OperationalPermissions} {bound : List TypeExpr} {expected : TypeExpr}
    {pattern : Pattern} {selected : SiteData}
    (licensed : Licensed language schemaFree permissions bound expected pattern selected)
    (labels : (language.terms.map (·.label)).Nodup)
    {operation : Pattern → Pattern → Pattern} {rule : RewriteRule} {spec : RuleBindingSpec}
    {ambient : Nat} {site : RulePatternSite} {path : List Nat} {depth : Nat}
    {assignment : Assignment} {source : Pattern} {extension : List TypeExpr}
    (instantiated : instantiateWith? operation rule spec ambient site path depth assignment pattern = some source)
    (shape : treeSchema pattern = true)
    (typed : HasType language actualFree (bound ++ extension) source.eraseBinderMetadata expected)
    (object : isObjectPattern source.eraseBinderMetadata = true) :
    ∃ focus,
      FocusInstance operation rule spec ambient site assignment path depth pattern selected.address focus ∧
      HasType language actualFree (selected.focusBound ++ extension) focus.eraseBinderMetadata selected.focusType ∧
      isObjectPattern focus.eraseBinderMetadata = true ∧
      NativeFocusSubstitution.depthAt? pattern selected.address bound.length = some selected.focusBound.length := by
  induction licensed generalizing path depth source with
  | here _ _ _ =>
      exact ⟨source, .here instantiated, typed, object, rfl⟩
  | @application bound grammar declaration index arguments argument parameter parameterType inner
      declared _ _ _ argumentAt parameterAt parameterTyped _ inside ih =>
      simp only [instantiateWith?] at instantiated
      obtain ⟨results, argumentsInstantiated, same⟩ := Option.bind_eq_some_iff.mp instantiated
      cases Option.some.inj same
      obtain ⟨actualArgument, actualAt, argumentInstantiated⟩ :=
        instantiated_argument argumentsInstantiated argumentAt
      simp only [Pattern.eraseBinderMetadata] at typed
      simp only [Pattern.eraseBinderMetadata, isObjectPattern] at object
      have erasedAt : (results.map Pattern.eraseBinderMetadata)[index]? =
          some actualArgument.eraseBinderMetadata := by
        rw [List.getElem?_map, actualAt]
        rfl
      have localTyped : HasType language actualFree (bound ++ extension)
          actualArgument.eraseBinderMetadata parameterType := by
        obtain ⟨actualGrammar, actualDeclared, actualLabel, _, _, actualArguments⟩ :=
          hasType_apply_inversion typed
        have sameGrammar : actualGrammar = grammar := grammar_equal labels actualDeclared
          (List.fst_mem_of_mem_zipIdx declared) actualLabel.symm
        subst actualGrammar
        exact typed_argument actualArguments erasedAt parameterAt parameterTyped
      have localObject : isObjectPattern actualArgument.eraseBinderMetadata = true :=
        objectList_member object (List.mem_of_getElem? erasedAt)
      have argumentShape := treeSchemas_member shape (List.mem_of_getElem? argumentAt)
      obtain ⟨focus, focusSelected, focusTyped, focusObject, focusDepth⟩ :=
        ih argumentInstantiated argumentShape localTyped localObject
      refine ⟨focus, ?_, focusTyped, focusObject, ?_⟩
      · exact .application argumentAt (by simpa only [Nat.zero_add] using focusSelected)
      · simpa only [SiteData.wrapApplication, NativeFocusSubstitution.depthAt?, argumentAt,
          Option.bind_some] using focusDepth
  | @lambda bound binder body domain codomain inner _ inside ih =>
      simp only [instantiateWith?] at instantiated
      obtain ⟨actualBody, bodyInstantiated, same⟩ := Option.bind_eq_some_iff.mp instantiated
      cases Option.some.inj same
      simp only [Pattern.eraseBinderMetadata] at typed
      simp only [Pattern.eraseBinderMetadata, isObjectPattern] at object
      have localTyped : HasType language actualFree ((domain :: bound) ++ extension)
          actualBody.eraseBinderMetadata codomain := by
        cases typed with
        | lambda bodyTyped => exact bodyTyped
      obtain ⟨focus, focused, focusTyped, focusObject, focusDepth⟩ :=
        ih bodyInstantiated shape localTyped object
      refine ⟨focus, .lambda focused, focusTyped, focusObject, ?_⟩
      simpa only [SiteData.wrapLambda, NativeFocusSubstitution.depthAt?, List.length_cons,
        Nat.add_comm 1 bound.length] using focusDepth
  | @multiLambda bound arity binders body domain codomain inner _ inside ih =>
      simp only [instantiateWith?] at instantiated
      obtain ⟨actualBody, bodyInstantiated, same⟩ := Option.bind_eq_some_iff.mp instantiated
      cases Option.some.inj same
      simp only [Pattern.eraseBinderMetadata] at typed
      simp only [Pattern.eraseBinderMetadata, isObjectPattern] at object
      have localTyped : HasType language actualFree
          ((List.replicate arity domain ++ bound) ++ extension)
          actualBody.eraseBinderMetadata codomain := by
        cases typed with
        | multiLambda bodyTyped => simpa only [List.append_assoc] using bodyTyped
      obtain ⟨focus, focused, focusTyped, focusObject, focusDepth⟩ :=
        ih bodyInstantiated shape localTyped object
      refine ⟨focus, .multiLambda focused, focusTyped, focusObject, ?_⟩
      simpa only [SiteData.wrapMultiLambda, NativeFocusSubstitution.depthAt?, List.length_append,
        List.length_replicate, Nat.add_comm arity bound.length] using focusDepth
  | directCollection | authoredCollection => cases shape

end Mettapedia.OSLF.NativeTypes.Modal.NativeBindingTypedFocusCoverage
