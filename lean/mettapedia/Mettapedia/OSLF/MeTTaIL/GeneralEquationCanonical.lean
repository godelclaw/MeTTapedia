import Mettapedia.OSLF.MeTTaIL.GeneralEquationSupport

/-!
# Canonical alpha admission for generic scoped execution

Canonicalization changes only source display metadata. De Bruijn indices,
constructor labels, free names and multi-binder arities remain intact. Scoped
matching runs on that canonical representative; it is not claimed that the
literal repeated-capture comparison is invariant on noncanonical raw inputs.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.GeneralEquationCanonical

open Syntax RuleBinding ScopedRuleMatching GeneralScopedMatch GeneralEquationMeasures
open GeneralEquationSupport
open Mettapedia.OSLF.Framework.GeneralFiniteTermUniverse
open Mettapedia.GSLT.LanguageDef.WellSorted

theorem erase_support (pattern : Pattern) :
    constructors pattern.eraseBinderMetadata = constructors pattern ∧
      pattern.eraseBinderMetadata.freeFvarNames = pattern.freeFvarNames ∧
      arities pattern.eraseBinderMetadata = arities pattern := by
  induction pattern using Pattern.inductionOn with
  | hbvar index => simp [Pattern.eraseBinderMetadata, constructors, Pattern.freeFvarNames, arities]
  | hfvar name => simp [Pattern.eraseBinderMetadata, constructors, Pattern.freeFvarNames, arities]
  | happly label arguments ih =>
      simp only [Pattern.eraseBinderMetadata, constructors, Pattern.freeFvarNames, arities]
      rw [flatMap_map_eq _ constructors arguments (by intro pattern member; exact (ih pattern member).1),
        flatMap_map_eq _ Pattern.freeFvarNames arguments (by intro pattern member; exact (ih pattern member).2.1),
        flatMap_map_eq _ arities arguments (by intro pattern member; exact (ih pattern member).2.2)]
      simp
  | hlambda display body ih => simpa only [Pattern.eraseBinderMetadata, constructors, Pattern.freeFvarNames, arities] using ih
  | hmultiLambda arity display body ih =>
      simp only [Pattern.eraseBinderMetadata, constructors, Pattern.freeFvarNames, arities, ih.1, ih.2.1, ih.2.2]
      simp
  | hsubst body replacement bodyIH replacementIH =>
      simp only [Pattern.eraseBinderMetadata, constructors, Pattern.freeFvarNames, arities,
        bodyIH.1, bodyIH.2.1, bodyIH.2.2, replacementIH.1, replacementIH.2.1, replacementIH.2.2]
      simp
  | hcollection kind elements rest ih =>
      simp only [Pattern.eraseBinderMetadata, constructors, Pattern.freeFvarNames, arities]
      rw [flatMap_map_eq _ constructors elements (by intro pattern member; exact (ih pattern member).1),
        flatMap_map_eq _ Pattern.freeFvarNames elements (by intro pattern member; exact (ih pattern member).2.1),
        flatMap_map_eq _ arities elements (by intro pattern member; exact (ih pattern member).2.2)]
      simp

theorem supported_erase {alphabet : Alphabet} {pattern : Pattern} (support : Supported alphabet pattern) :
    Supported alphabet pattern.eraseBinderMetadata := by
  have same := erase_support pattern
  simpa only [Supported, same.1, same.2.1, same.2.2] using support

theorem representation_erase {parameter : TermParam} {argument : Pattern}
    (represented : MatchesParameterRepresentation parameter argument) :
    MatchesParameterRepresentation parameter argument.eraseBinderMetadata := by
  cases parameter <;> cases argument <;> simp_all [MatchesParameterRepresentation, Pattern.eraseBinderMetadata]

mutual
  theorem typed_erase {language : LanguageDef} {free : FreeTypeContext} {bound : List TypeExpr}
      {pattern : Pattern} {type : TypeExpr} (typed : HasType language free bound pattern type) :
      HasType language free bound pattern.eraseBinderMetadata type := by
    cases typed with
    | bvar found => simpa only [Pattern.eraseBinderMetadata] using HasType.bvar found
    | fvar found => simpa only [Pattern.eraseBinderMetadata] using HasType.fvar found
    | constructor authored ordinary arguments =>
        simpa only [Pattern.eraseBinderMetadata] using HasType.constructor authored ordinary (arguments_typed_erase arguments)
    | lambda body => simpa only [Pattern.eraseBinderMetadata] using HasType.lambda (binder := none) (typed_erase body)
    | multiLambda body => simpa only [Pattern.eraseBinderMetadata] using HasType.multiLambda (binders := []) (typed_erase body)
    | subst body replacement => simpa only [Pattern.eraseBinderMetadata] using HasType.subst (typed_erase body) (typed_erase replacement)
    | @collection bound kind elements rest type typedElements =>
        simpa only [Pattern.eraseBinderMetadata] using HasType.collection (rest := rest) (elements_typed_erase typedElements)
    | @collectionConstructor bound rule parameter kind elements rest type authored shape typedElements =>
        simpa only [Pattern.eraseBinderMetadata] using HasType.collectionConstructor (rest := rest) authored shape (elements_typed_erase typedElements)

  theorem arguments_typed_erase {language : LanguageDef} {free : FreeTypeContext} {bound : List TypeExpr}
      {arguments : List Pattern} {parameters : List TermParam}
      (typed : ArgumentsHaveTypes language free bound arguments parameters) :
      ArgumentsHaveTypes language free bound (arguments.map Pattern.eraseBinderMetadata) parameters := by
    cases typed with
    | nil => exact .nil
    | cons represented expected head tail =>
        exact .cons (representation_erase represented) expected (typed_erase head) (arguments_typed_erase tail)

  theorem elements_typed_erase {language : LanguageDef} {free : FreeTypeContext} {bound : List TypeExpr}
      {elements : List Pattern} {type : TypeExpr}
      (typed : ElementsHaveType language free bound elements type) :
      ElementsHaveType language free bound (elements.map Pattern.eraseBinderMetadata) type := by
    cases typed with
    | nil => exact .nil _ _
    | cons head tail => exact .cons (typed_erase head) (elements_typed_erase tail)
end

mutual
  theorem scoped_erase (pattern : Pattern) (depth : Nat) :
      pattern.eraseBinderMetadata.isWellScopedAt depth = pattern.isWellScopedAt depth := by
    cases pattern with
    | bvar index => simp only [Pattern.eraseBinderMetadata]
    | fvar name => simp only [Pattern.eraseBinderMetadata]
    | apply label arguments => simpa only [Pattern.eraseBinderMetadata, Pattern.isWellScopedAt] using scopedList_erase arguments depth
    | lambda display body => simpa only [Pattern.eraseBinderMetadata, Pattern.isWellScopedAt] using scoped_erase body (depth + 1)
    | multiLambda arity display body => simpa only [Pattern.eraseBinderMetadata, Pattern.isWellScopedAt] using scoped_erase body (depth + arity)
    | subst body replacement =>
        simp only [Pattern.eraseBinderMetadata, Pattern.isWellScopedAt,
          scoped_erase body (depth + 1), scoped_erase replacement depth]
    | collection kind elements rest => simpa only [Pattern.eraseBinderMetadata, Pattern.isWellScopedAt] using scopedList_erase elements depth
  termination_by sizeOf pattern

  theorem scopedList_erase (patterns : List Pattern) (depth : Nat) :
      Pattern.isWellScopedListAt depth (patterns.map Pattern.eraseBinderMetadata) =
        Pattern.isWellScopedListAt depth patterns := by
    cases patterns with
    | nil => rfl
    | cons pattern rest =>
        simp only [List.map_cons, Pattern.isWellScopedListAt, scoped_erase pattern depth, scopedList_erase rest depth]
  termination_by sizeOf patterns
end

mutual
  theorem object_erase (pattern : Pattern) :
      isObjectPattern pattern.eraseBinderMetadata = isObjectPattern pattern := by
    cases pattern with
    | bvar index => simp only [Pattern.eraseBinderMetadata]
    | fvar name => simp only [Pattern.eraseBinderMetadata]
    | apply label arguments => simpa only [Pattern.eraseBinderMetadata, isObjectPattern] using objectList_erase arguments
    | lambda display body => simpa only [Pattern.eraseBinderMetadata, isObjectPattern] using object_erase body
    | multiLambda arity display body => simpa only [Pattern.eraseBinderMetadata, isObjectPattern] using object_erase body
    | subst body replacement => simp only [Pattern.eraseBinderMetadata, isObjectPattern]
    | collection kind elements rest =>
        simp only [Pattern.eraseBinderMetadata, isObjectPattern, objectList_erase elements]
  termination_by sizeOf pattern

  theorem objectList_erase (patterns : List Pattern) :
      isObjectPatternList (patterns.map Pattern.eraseBinderMetadata) = isObjectPatternList patterns := by
    cases patterns with
    | nil => rfl
    | cons pattern rest => simp only [List.map_cons, isObjectPatternList, object_erase pattern, objectList_erase rest]
  termination_by sizeOf patterns
end

theorem open_typed_erase {language : LanguageDef} {free : FreeTypeContext} {bound : List TypeExpr}
    {pattern : Pattern} {type : TypeExpr}
    (typed : HasType language free bound pattern type) (object : isObjectPattern pattern = true)
    (scope : pattern.isWellScopedAt bound.length = true) :
    OpenPatternWellSorted language free bound type pattern.eraseBinderMetadata := by
  exact ⟨typed_erase typed, Pattern.eraseBinderMetadata_hasCanonicalBinderMetadata pattern,
    (object_erase pattern).trans object, (scoped_erase pattern bound.length).trans scope⟩

/-- The actual ordinary matcher runs after selecting the alpha representative. -/
def canonicalMatchRule (rule : RewriteRule) (spec : RuleBindingSpec) (ambient : Nat)
    (source : Pattern) : List ScopedRuleMatching.Assignment :=
  matchRuleAt rule spec ambient source.eraseBinderMetadata

/-- Independent matching on a canonical representative of the supplied source.
The representative is characterized by alpha equivalence, not enumeration. -/
def CanonicalRuleMatch (rule : RewriteRule) (spec : RuleBindingSpec) (ambient : Nat)
    (source : Pattern) (assignment : ScopedRuleMatching.Assignment) : Prop :=
  ∃ representative, representative.hasCanonicalBinderMetadata = true ∧
    Pattern.AlphaEquiv source representative ∧
    Matches rule spec ambient .left [] 0 [] rule.left representative assignment

theorem canonicalMatchRule_iff (rule : RewriteRule) (spec : RuleBindingSpec) (ambient : Nat)
    (source : Pattern) (assignment : ScopedRuleMatching.Assignment) :
    assignment ∈ canonicalMatchRule rule spec ambient source ↔
      CanonicalRuleMatch rule spec ambient source assignment := by
  constructor
  · intro member
    exact ⟨source.eraseBinderMetadata, Pattern.eraseBinderMetadata_hasCanonicalBinderMetadata source,
      (Pattern.eraseBinderMetadata_idempotent source).symm, matchRuleAt_iff.mp member⟩
  · rintro ⟨representative, canonical, equivalent, matched⟩
    have same : source.eraseBinderMetadata = representative := by
      simpa only [Pattern.AlphaEquiv, Pattern.eraseBinderMetadata_eq_self_of_canonical canonical] using equivalent
    change assignment ∈ matchRuleAt rule spec ambient source.eraseBinderMetadata
    rw [same]
    exact matchRuleAt_iff.mpr matched

theorem canonicalMatchRule_alpha (rule : RewriteRule) (spec : RuleBindingSpec) (ambient : Nat)
    {source renamed : Pattern} (equivalent : Pattern.AlphaEquiv source renamed) :
    canonicalMatchRule rule spec ambient source = canonicalMatchRule rule spec ambient renamed :=
  congrArg (matchRuleAt rule spec ambient) equivalent

theorem canonicalMatchRule_canonical (rule : RewriteRule) (spec : RuleBindingSpec) (ambient : Nat)
    {source : Pattern} (canonical : source.hasCanonicalBinderMetadata = true) :
    canonicalMatchRule rule spec ambient source = matchRuleAt rule spec ambient source := by
  rw [canonicalMatchRule, Pattern.eraseBinderMetadata_eq_self_of_canonical canonical]

/-- Target canonicalization retains the separately available authored receipt. -/
def canonicalTargets (targets : List Pattern) : List Pattern := targets.map Pattern.eraseBinderMetadata

theorem canonicalTargets_spec (targets : List Pattern) (target : Pattern) :
    target ∈ canonicalTargets targets ↔
      ∃ raw ∈ targets, Pattern.AlphaEquiv raw target ∧ target.hasCanonicalBinderMetadata = true := by
  simp only [canonicalTargets, List.mem_map]
  constructor
  · rintro ⟨raw, member, rfl⟩
    exact ⟨raw, member, (Pattern.eraseBinderMetadata_idempotent raw).symm,
      Pattern.eraseBinderMetadata_hasCanonicalBinderMetadata raw⟩
  · rintro ⟨raw, member, equivalent, canonical⟩
    exact ⟨raw, member, by simpa only [Pattern.AlphaEquiv,
      Pattern.eraseBinderMetadata_eq_self_of_canonical canonical] using equivalent⟩

theorem universe_contains_alpha_representative {language : LanguageDef} {free : FreeTypeContext}
    {bound : List TypeExpr} {type : TypeExpr} {source : Pattern} (providerTerms : List Pattern)
    (typed : HasType language free bound source type) (object : isObjectPattern source = true)
    (scope : source.isWellScopedAt bound.length = true) :
    source.eraseBinderMetadata ∈ sourceUniverse language free bound type source providerTerms := by
  have normalized := open_typed_erase typed object scope
  have support := supported_erase (source_supported language source providerTerms)
  have small : PatternTreeSize.nodes source.eraseBinderMetadata ≤ PatternTreeSize.nodes source := by
    rw [eraseBinderMetadata_nodes]
  apply typedUniverse_complete _ _ _ language free bound type _ normalized small support
  exact scoped_indices _ _ bound.length (PatternTreeSize.nodes source) small normalized.2.2.2
    (fun arity member => arity_le_maximum _ arity (support.2.2 arity member))

end Mettapedia.OSLF.MeTTaIL.GeneralEquationCanonical
