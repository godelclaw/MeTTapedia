import Mettapedia.OSLF.MeTTaIL.ReferenceStepEquations
import Mettapedia.GSLT.LanguageDef.BagNormalFormSection
import Mathlib.Logic.Relation
import Mathlib.Data.List.Permutation
import Mettapedia.OSLF.MeTTaIL.Complete.Coherence

/-!
# Deciding the declared equations of a bag presentation

For admissible open terms, equality of the computed normal forms is equivalent
to the generated equation relation. Both implications use the actual declared
bag laws: generator invariance and the normalization path.

The final namespace also treats retained authored equations whose matching
and substitutions preserve that normal form. Its exact source agreement is
on the admissible fibre. A separate invariant covers all raw intermediates
and establishes agreement with the unrestricted raw source relation at
admissible endpoints. The actual source rows remain retained throughout.
-/

set_option autoImplicit false
namespace Mettapedia.GSLT.LanguageDef.BagNormalForm
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.LanguageDef.EquationSemantics

variable {language : LanguageDef} {bag : GrammarRule} {unit : Option String}

/-- Two or more surviving components retain their bag wrapper. -/
theorem collapse_eq_bag_of_length (unit : String) (elements : List Pattern)
    (many : 2 ≤ elements.length) :
    collapse unit elements = .collection .hashBag elements none := by
  cases elements with
  | nil => simp at many
  | cons first rest =>
      cases rest with
      | nil => simp at many
      | cons second tail => rfl

/-- Bag shape depends on multiplicity, without evaluating the sorting order. -/
theorem normalizeBag_isBagNode_of_length (unit : String) (elements : List Pattern)
    (many : 2 ≤ (bagContents unit elements).length) :
    IsBagNode (normalizeBag (some unit) elements) := by
  refine ⟨Mettapedia.OSLF.MeTTaIL.PatternCode.sortPatterns (bagContents unit elements), ?_⟩
  exact collapse_eq_bag_of_length unit _ (by simpa using many)

/-- The constructive normalization path is an equation derivation. -/
theorem equationEquiv_normalForm (laws : BareBagTheory language bag unit)
    (base : BasePremiseEvaluator) {free : FreeTypeContext} {bound : List TypeExpr}
    {type : TypeExpr} {pattern : Pattern}
    (admissible : Admissible language free bound type pattern)
    (collectionless : collectionFree type = true) :
    EquationEquiv base language pattern (normalForm unit pattern) := by
  exact Relation.EqvGen.reflTransGen_le_eqvGen _ _ _
    (path_normalForm laws base pattern admissible collectionless)

/-- Exact equation adequacy of normalization, including open binding contexts. -/
theorem equationEquiv_iff_normalForm_eq (laws : BareBagTheory language bag unit)
    (base : BasePremiseEvaluator) {free : FreeTypeContext} {bound : List TypeExpr}
    {type : TypeExpr} {left right : Pattern}
    (leftAdmissible : Admissible language free bound type left)
    (rightAdmissible : Admissible language free bound type right)
    (collectionless : collectionFree type = true) :
    EquationEquiv base language left right ↔ normalForm unit left = normalForm unit right := by
  constructor
  · exact normalForm_eq_of_equationEquiv laws.toBagTheory
  · intro equal
    exact .trans _ _ _ (equationEquiv_normalForm laws base leftAdmissible collectionless)
      (equal ▸ (equationEquiv_normalForm laws base rightAdmissible collectionless).symm)

/-- A decision procedure for the authored equation theory on its admissible terms. -/
def decideEquationEquiv (laws : BareBagTheory language bag unit)
    (base : BasePremiseEvaluator) {free : FreeTypeContext} {bound : List TypeExpr}
    {type : TypeExpr} {left right : Pattern}
    (leftAdmissible : Admissible language free bound type left)
    (rightAdmissible : Admissible language free bound type right)
    (collectionless : collectionFree type = true) : Decidable (EquationEquiv base language left right) :=
  decidable_of_iff (normalForm unit left = normalForm unit right)
    (equationEquiv_iff_normalForm_eq laws base leftAdmissible rightAdmissible collectionless).symm

end Mettapedia.GSLT.LanguageDef.BagNormalForm

namespace Mettapedia.GSLT.LanguageDef.BagNormalForm.WithAuthoredEquations
open Mettapedia.OSLF.MeTTaIL.Syntax Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.GSLT.LanguageDef.WellSorted Mettapedia.GSLT.LanguageDef.EquationSemantics

mutual
  private theorem grammar_hasType {source target : LanguageDef}
      (same : target.terms = source.terms) {free : FreeTypeContext} {bound : List TypeExpr}
      {pattern : Pattern} {type : TypeExpr} (typed : HasType source free bound pattern type) :
      HasType target free bound pattern type := by
    cases typed with
    | bvar lookup => exact .bvar lookup
    | fvar lookup => exact .fvar lookup
    | constructor member ordinary arguments =>
        exact .constructor (same ▸ member) ordinary (grammar_arguments same arguments)
    | lambda body => exact .lambda (grammar_hasType same body)
    | multiLambda body => exact .multiLambda (grammar_hasType same body)
    | subst body replacement => exact .subst (grammar_hasType same body) (grammar_hasType same replacement)
    | collection elements => exact .collection (grammar_elements same elements)
    | collectionConstructor member shape elements =>
        exact .collectionConstructor (same ▸ member) shape (grammar_elements same elements)

  private theorem grammar_arguments {source target : LanguageDef}
      (same : target.terms = source.terms) {free : FreeTypeContext} {bound : List TypeExpr}
      {patterns : List Pattern} {parameters : List TermParam}
      (typed : ArgumentsHaveTypes source free bound patterns parameters) :
      ArgumentsHaveTypes target free bound patterns parameters := by
    cases typed with
    | nil => exact .nil
    | cons represented type first rest =>
        exact .cons represented type (grammar_hasType same first) (grammar_arguments same rest)

  private theorem grammar_elements {source target : LanguageDef}
      (same : target.terms = source.terms) {free : FreeTypeContext} {bound : List TypeExpr}
      {patterns : List Pattern} {type : TypeExpr}
      (typed : ElementsHaveType source free bound patterns type) :
      ElementsHaveType target free bound patterns type := by
    cases typed with
    | nil bound type => exact .nil bound type
    | cons first rest => exact .cons (grammar_hasType same first) (grammar_elements same rest)
end

private theorem grammar_admissible {source target : LanguageDef}
    (same : target.terms = source.terms) {free : FreeTypeContext} {bound : List TypeExpr}
    {type : TypeExpr} {pattern : Pattern} (good : Admissible source free bound type pattern) :
    Admissible target free bound type pattern :=
  ⟨grammar_hasType same good.typed,good.canonical,good.object⟩

private theorem grammar_carrier {source target : LanguageDef}
    (same : target.terms = source.terms) {rule : GrammarRule} {kind : CollType}
    (declaration : CollectionCarrierRule source rule kind) :
    CollectionCarrierRule target rule kind :=
  ⟨same ▸ declaration.authored,declaration.selfSorted⟩

private theorem grammar_algebra {source target : LanguageDef}
    (same : target.terms = source.terms) {rule : GrammarRule} {kind : CollType}
    {algebra : CollectionAlgebra} (declaration : AlgebraRule source rule kind algebra) :
    AlgebraRule target rule kind algebra := by
  refine ⟨same ▸ declaration.authored,declaration.declared,declaration.selfSorted,?_⟩
  intro unit present
  obtain ⟨unitRule,member,label,category,parameters⟩ := declaration.unitAuthored unit present
  exact ⟨unitRule,same ▸ member,label,category,parameters⟩

private theorem grammar_sorted {source target : LanguageDef}
    (same : target.terms = source.terms) {pattern : Pattern} {sort : String}
    (typed : SortedAt source pattern sort) : SortedAt target pattern sort := by
  obtain ⟨free,bound,typed⟩ := typed
  exact ⟨free,bound,grammar_hasType same typed⟩

private theorem grammar_collectionTyped {source target : LanguageDef}
    (same : target.terms = source.terms) {rule : GrammarRule} {kind : CollType}
    {elements : List Pattern}
    (typed : Mettapedia.GSLT.LanguageDef.WellSorted.CollectionTypedAt source rule kind elements) :
    Mettapedia.GSLT.LanguageDef.WellSorted.CollectionTypedAt target rule kind elements := by
  obtain ⟨parameter,member,elementType,occurs,free,bound,body⟩ := typed
  exact ⟨parameter,member,elementType,occurs,free,bound,grammar_hasType same body⟩

private theorem grammar_derived {source target : LanguageDef}
    (same : target.terms = source.terms) {first second : Pattern}
    (step : DerivedInstance source first second) : DerivedInstance target first second := by
  cases step with
  | bagPerm declaration sorted permutation =>
      exact .bagPerm (same ▸ declaration) (grammar_collectionTyped same sorted) permutation
  | setPerm declaration sorted permutation =>
      exact .setPerm (same ▸ declaration) (grammar_collectionTyped same sorted) permutation
  | setDedup declaration sorted =>
      exact .setDedup (same ▸ declaration) (grammar_collectionTyped same sorted)
  | flatten declaration flat sorted =>
      exact .flatten (grammar_algebra same declaration) flat (grammar_sorted same sorted)
  | singleton declaration flat sorted =>
      exact .singleton (grammar_algebra same declaration) flat (grammar_sorted same sorted)
  | unitElim declaration unit sorted =>
      exact .unitElim (grammar_algebra same declaration) unit (grammar_sorted same sorted)
  | emptyUnit declaration unit sorted =>
      exact .emptyUnit (grammar_algebra same declaration) unit (grammar_sorted same sorted)

private theorem comparison_step {language : LanguageDef} {base : BasePremiseEvaluator}
    {left right : Pattern}
    (step : EquationContextStep base {language with equations := []} left right) :
    EquationContextStep base language left right := by
  cases step with
  | inContext context generator =>
      rcases generator with authoredInstance | derived
      · exact False.elim (no_equationInstance_of_equations_eq_nil rfl _ _ authoredInstance)
      · exact .inContext context (.inr (grammar_derived (source := {language with equations := []}) (target := language) rfl derived))

private theorem comparison_path {language : LanguageDef} {base : BasePremiseEvaluator}
    {left right : Pattern}
    (path : Path base {language with equations := []} left right) :
    Path base language left right := by
  induction path with
  | refl => exact .refl
  | tail _ step earlier => exact earlier.tail (comparison_step step)

/-- An admissible source term reaches the normal form by the actual source's
own derived laws, with every retained authored row still present. -/
theorem source_equiv_normalForm {language : LanguageDef} {bag : GrammarRule} {unit : Option String}
    (laws : BareBagTheory {language with equations := []} bag unit)
    (base : BasePremiseEvaluator) {free : FreeTypeContext} {bound : List TypeExpr}
    {type : TypeExpr} {pattern : Pattern} (good : Admissible language free bound type pattern)
    (collectionless : collectionFree type = true) :
    EquationEquiv base language pattern (normalForm unit pattern) := by
  exact Relation.EqvGen.reflTransGen_le_eqvGen _ _ _
    (comparison_path (path_normalForm laws base pattern (grammar_admissible (source := language) (target := {language with equations := []}) rfl good) collectionless))



open Mettapedia.OSLF.MeTTaIL.Match Mettapedia.OSLF.MeTTaIL.MatchSpec

/-- Ordinary bag matching reconstructs the selected elements up to the
existing list permutation relation. Ambient consistent bindings are retained. -/
theorem matchBag_reconstruct {patterns terms : List Pattern} {bindings extended : Bindings}
    (matched : MatchBagRel patterns none .hashBag terms bindings)
    (correct : ∀ pattern ∈ patterns, Pattern.isMatchCorrect pattern = true)
    (extension : BindingsExtends bindings extended) :
    (patterns.map (applyBindings extended)).Perm terms := by
  induction patterns generalizing terms bindings with
  | nil => cases matched; exact .refl _
  | cons pattern patterns recurse =>
      cases matched with
      | cons index within head tail merged =>
        have headExtended : BindingsExtends _ extended :=
          fun key value found => extension key value (mergeBindings_subsumed_left merged found)
        have tailExtended : BindingsExtends _ extended :=
          fun key value found => extension key value (mergeBindings_subsumed_right merged found)
        have reconstructed := matchRel_correct_of_extends head (correct pattern (by simp)) headExtended
        have later := recurse tail (fun next member => correct next (by simp [member])) tailExtended
        simp only [List.map_cons,reconstructed]
        exact (List.Perm.cons _ later).trans (List.getElem_cons_eraseIdx_perm within)

/-- A first-order value pattern, or a closed bag of such patterns, is enough
for the actual unit rows. This is a row proof condition, not admission authority. -/
def RowPattern (pattern : Pattern) : Prop :=
  Pattern.isMatchCorrect pattern = true ∨
    ∃ elements, pattern = .collection .hashBag elements none ∧
      ∀ element ∈ elements, Pattern.isMatchCorrect element = true

/-- On object sources, actual ordinary matching reconstructs the normal form.
The object premise is essential: raw matching ignores the target tail field. -/
theorem match_normalForm {unit : Option String} {pattern subject : Pattern} {bindings : Bindings}
    (row : RowPattern pattern) (matched : bindings ∈ matchPattern pattern subject)
    (object : isObjectPattern subject = true) :
    normalForm unit subject = normalForm unit (applyBindings bindings pattern) := by
  rcases row with exactPattern | ⟨elements,rfl,correct⟩
  · rw [matchPattern_correct matched exactPattern]
  · have relational := matchPattern_sound matched
    cases relational with
    | collection _ bagMatch =>
      simp only [isObjectPattern, Bool.and_eq_true, Option.isNone_iff_eq_none] at object
      obtain ⟨rfl,_⟩ := object
      have permutation := matchBag_reconstruct bagMatch correct (fun _ _ found => found)
      simp only [applyBindings, normalForm_bag, List.append_nil]
      exact (normalizeBag_perm unit (permutation.map (normalForm unit))).symm

/-- Concrete premise-free rows are checked both for matching reconstruction
and for their substitution-level normal-form equation. -/
theorem equationInstance_normalForm {language : LanguageDef} {unit : Option String}
    (rows : ∀ row ∈ language.equations,
      row.premises = [] ∧ RowPattern row.left ∧ RowPattern row.right ∧
        ∀ bindings, normalForm unit (applyBindings bindings row.left) =
          normalForm unit (applyBindings bindings row.right))
    {base : BasePremiseEvaluator} {source target : Pattern}
    (object : isObjectPattern source = true) (step : EquationInstance base language source target) :
    normalForm unit source = normalForm unit target := by
  obtain ⟨fuel,step⟩ := step
  cases step with
  | forward member matched premises applied =>
    obtain ⟨empty,leftRow,_,invariant⟩ := rows _ member
    rw [empty] at premises
    cases premises
    rw [← applied]
    exact (match_normalForm leftRow matched object).trans (invariant _)
  | reverse member matched premises applied =>
    obtain ⟨empty,_,rightRow,invariant⟩ := rows _ member
    rw [empty] at premises
    cases premises
    rw [← applied]
    exact (match_normalForm rightRow matched object).trans (invariant _).symm



private theorem object_of_fill (context : Mettapedia.OSLF.MeTTaIL.DerivedContexts.OneHoleContext)
    (pattern : Pattern) (object : isObjectPattern (context.fill pattern) = true) :
    isObjectPattern pattern = true := by
  induction context with
  | hole => exact object
  | apply label before inner after recurse =>
    simp only [Mettapedia.OSLF.MeTTaIL.DerivedContexts.OneHoleContext.fill,
      isObjectPattern,isObjectPatternList_iff] at object
    exact recurse (object _ (by simp))
  | lambda binder inner recurse =>
    exact recurse (by simpa only [Mettapedia.OSLF.MeTTaIL.DerivedContexts.OneHoleContext.fill,isObjectPattern] using object)
  | multiLambda arity binders inner recurse =>
    exact recurse (by simpa only [Mettapedia.OSLF.MeTTaIL.DerivedContexts.OneHoleContext.fill,isObjectPattern] using object)
  | substBody inner replacement recurse =>
    simp [Mettapedia.OSLF.MeTTaIL.DerivedContexts.OneHoleContext.fill,isObjectPattern] at object
  | substReplacement body inner recurse =>
    simp [Mettapedia.OSLF.MeTTaIL.DerivedContexts.OneHoleContext.fill,isObjectPattern] at object
  | collection kind before inner after rest recurse =>
    simp only [Mettapedia.OSLF.MeTTaIL.DerivedContexts.OneHoleContext.fill,
      isObjectPattern,Bool.and_eq_true,isObjectPatternList_iff] at object
    exact recurse (object.2 _ (by simp))

/-- The actual contextual source generator preserves normal forms on object
sources. No reconstruction property is asserted for raw open-tail subjects. -/
theorem source_step_normalForm {language : LanguageDef} {bag : GrammarRule} {unit : Option String}
    (laws : BareBagTheory {language with equations := []} bag unit)
    (rows : ∀ row ∈ language.equations,
      row.premises = [] ∧ RowPattern row.left ∧ RowPattern row.right ∧
        ∀ bindings, normalForm unit (applyBindings bindings row.left) =
          normalForm unit (applyBindings bindings row.right))
    {base : BasePremiseEvaluator} {left right : Pattern}
    (step : EquationContextStep base language left right) (object : isObjectPattern left = true) :
    normalForm unit left = normalForm unit right := by
  cases step with
  | inContext context generator =>
    apply normalForm_fill_congr unit context
    rcases generator with authoredInstance | derived
    · exact equationInstance_normalForm rows (object_of_fill context _ object) authoredInstance
    · exact normalForm_derived laws.toBagTheory
        (grammar_derived (source := language) (target := {language with equations := []}) rfl derived)

/-- The existing normalization path transports the complete typing derivation
back to the source grammar; actual source rows remain untouched. -/
theorem normalized_admissible {language : LanguageDef} {bag : GrammarRule} {unit : Option String}
    (laws : BareBagTheory {language with equations := []} bag unit)
    (base : BasePremiseEvaluator) {free : FreeTypeContext} {bound : List TypeExpr}
    {type : TypeExpr} {pattern : Pattern} (good : Admissible language free bound type pattern)
    (collectionless : collectionFree type = true) :
    Admissible language free bound type (normalForm unit pattern) := by
  have comparisonGood := grammar_admissible (source := language)
    (target := {language with equations := []}) rfl good
  have path := path_normalForm laws base pattern comparisonGood collectionless
  exact grammar_admissible (source := {language with equations := []}) (target := language) rfl
    (path_admissible laws path comparisonGood collectionless)

/-- Normalization on the genuine admissible source fibre uses the existing
bag normal form, including empty and singleton collapse. -/
def normalizeSource {language : LanguageDef} {bag : GrammarRule} {unit : Option String}
    (laws : BareBagTheory {language with equations := []} bag unit)
    (base : BasePremiseEvaluator) (free : FreeTypeContext) (bound : List TypeExpr)
    (type : TypeExpr) (collectionless : collectionFree type = true)
    (term : {pattern // Admissible language free bound type pattern}) :
    {pattern // Admissible language free bound type pattern} :=
  ⟨normalForm unit term.1,normalized_admissible laws base term.2 collectionless⟩

private theorem fibre_path {language : LanguageDef} {bag : GrammarRule} {unit : Option String}
    (laws : BareBagTheory {language with equations := []} bag unit)
    {base : BasePremiseEvaluator} {free : FreeTypeContext} {bound : List TypeExpr}
    {type : TypeExpr} (collectionless : collectionFree type = true) {left right : Pattern}
    (path : Path base {language with equations := []} left right)
    (firstGood : Admissible language free bound type left)
    (lastGood : Admissible language free bound type right) :
    Relation.ReflTransGen
      (fun (first second : {pattern // Admissible language free bound type pattern}) =>
        EquationContextStep base language first.1 second.1)
      ⟨left,firstGood⟩ ⟨right,lastGood⟩ := by
  revert lastGood
  induction path with
  | refl => intro lastGood; exact .refl
  | @tail middle last previous step earlier =>
    intro lastGood
    have middleGood := grammar_admissible
      (source := {language with equations := []}) (target := language) rfl
      (path_admissible laws previous
        (grammar_admissible (source := language) (target := {language with equations := []}) rfl firstGood)
        collectionless)
    exact (earlier middleGood).tail (comparison_step step)

/-- A source-equational realization of the existing coherence interface on
its actual admissible fibre. The relation is the source's own contextual
step, restricted to that fibre; no raw/fibre equivalence is asserted. -/
theorem sourceNormalizer {language : LanguageDef} {bag : GrammarRule} {unit : Option String}
    (laws : BareBagTheory {language with equations := []} bag unit)
    (rows : ∀ row ∈ language.equations,
      row.premises = [] ∧ RowPattern row.left ∧ RowPattern row.right ∧
        ∀ bindings, normalForm unit (applyBindings bindings row.left) =
          normalForm unit (applyBindings bindings row.right))
    (base : BasePremiseEvaluator) (free : FreeTypeContext) (bound : List TypeExpr)
    (type : TypeExpr) (collectionless : collectionFree type = true) :
    Mettapedia.OSLF.MeTTaIL.Complete.Coherence.Normalizer
      (fun (first second : {pattern // Admissible language free bound type pattern}) =>
        EquationContextStep base language first.1 second.1)
      (normalizeSource laws base free bound type collectionless) where
  sound term := by
    have comparisonGood := grammar_admissible (source := language)
      (target := {language with equations := []}) rfl term.2
    exact Relation.EqvGen.reflTransGen_le_eqvGen _ _ _
      (fibre_path laws collectionless (path_normalForm laws base term.1 comparisonGood collectionless)
        term.2 (normalized_admissible laws base term.2 collectionless))
  canonical first second step :=
    Subtype.ext (source_step_normalForm laws rows step first.2.object)

/-- Normal-form equality exactly decides the equivalence generated by actual
source steps within the admissible fibre. -/
theorem source_fibre_equiv_iff_normalForm_eq {language : LanguageDef} {bag : GrammarRule}
    {unit : Option String} (laws : BareBagTheory {language with equations := []} bag unit)
    (rows : ∀ row ∈ language.equations,
      row.premises = [] ∧ RowPattern row.left ∧ RowPattern row.right ∧
        ∀ bindings, normalForm unit (applyBindings bindings row.left) =
          normalForm unit (applyBindings bindings row.right))
    (base : BasePremiseEvaluator) (free : FreeTypeContext) (bound : List TypeExpr)
    (type : TypeExpr) (collectionless : collectionFree type = true)
    (left right : {pattern // Admissible language free bound type pattern}) :
    Relation.EqvGen
      (fun (first second : {pattern // Admissible language free bound type pattern}) =>
        EquationContextStep base language first.1 second.1) left right ↔
      normalForm unit left.1 = normalForm unit right.1 := by
  let certified := sourceNormalizer laws rows base free bound type collectionless
  constructor
  · intro related
    exact congrArg Subtype.val (certified.eqvGen_eq related)
  · intro same
    have sameNormal : normalizeSource laws base free bound type collectionless left =
        normalizeSource laws base free bound type collectionless right := Subtype.ext same
    exact .trans _ _ _ (certified.sound left) (sameNormal ▸ (certified.sound right).symm)

/-- Singleton collapse is the same existing bag normal form on arbitrary
components; no typing or interpretation hypothesis is used here. -/
theorem normalForm_singleton (unit : String) (pattern : Pattern) :
    normalForm (some unit) (.collection .hashBag [pattern] none) =
      normalForm (some unit) pattern := by
  rw [normalForm_bag]
  simp only [List.map_cons,List.map_nil,normalizeBag]
  have normal := rootNormal_normalForm unit pattern
  generalize normalForm (some unit) pattern = image at normal ⊢
  by_cases isUnit : image = .apply unit []
  · subst isUnit
    simp [bagContents,splice,collapse]
  · by_cases isBag : IsBagNode image
    · obtain ⟨components,rfl⟩ := isBag
      obtain ⟨sorted,long,plain⟩ := normal components rfl
      have contents : bagContents unit [.collection .hashBag components none] = components := by
        simp only [bagContents,List.flatMap_cons,List.flatMap_nil,List.append_nil,splice_bag]
        apply List.filter_eq_self.mpr
        intro component member
        simpa using (plain component member).1
      rw [contents,sorted]
      match components,long with
      | first :: second :: rest,_ => rfl
    · have contents : bagContents unit [image] = [image] := by
        simp [bagContents,splice_of_not_bag isBag,isUnit]
      rw [contents,sortPatterns_singleton]
      rfl

/-- The two actual retained wrapper-unit rows are invariant under every
binding substitution, including substitutions containing arbitrary terms. -/
theorem normalForm_insert_unit (unit : String) (before after : List Pattern) :
    normalForm (some unit) (.collection .hashBag (before ++ .apply unit [] :: after) none) =
      normalForm (some unit) (.collection .hashBag (before ++ after) none) := by
  rw [normalForm_bag,normalForm_bag]
  apply normalizeBag_contents_perm
  simp only [List.map_append,List.map_cons,bagContents_append]
  rw [bagContents_cons unit (normalForm (some unit) (.apply unit []))]
  have noUnit : bagContents unit [normalForm (some unit) (.apply unit [])] = [] := by
    simp [normalForm,normalFormList,bagContents,splice]
  rw [noUnit,List.nil_append]

#print axioms normalForm_singleton
#print axioms normalForm_insert_unit

#print axioms source_equiv_normalForm
#print axioms matchBag_reconstruct
#print axioms match_normalForm
#print axioms equationInstance_normalForm
#print axioms source_step_normalForm
#print axioms normalized_admissible
#print axioms sourceNormalizer
#print axioms source_fibre_equiv_iff_normalForm_eq
end Mettapedia.GSLT.LanguageDef.BagNormalForm.WithAuthoredEquations

namespace Mettapedia.GSLT.LanguageDef.BagNormalForm.WithAuthoredEquations
open Mettapedia.OSLF.MeTTaIL.Syntax Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.MeTTaIL.DerivedContexts Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.GSLT.LanguageDef.WellSorted Mettapedia.GSLT.LanguageDef.EquationSemantics

/- The projection below is an internal observer for the raw equation
relation. It is not installed as a source or execution normalization pass. -/
mutual
  private def eraseTails : Pattern → Pattern
    | .bvar index => .bvar index
    | .fvar metavariable => .fvar metavariable
    | .apply label arguments => .apply label (eraseTailsList arguments)
    | .lambda binder body => .lambda binder (eraseTails body)
    | .multiLambda arity binders body => .multiLambda arity binders (eraseTails body)
    | .subst body replacement => .subst (eraseTails body) (eraseTails replacement)
    | .collection kind elements _ => .collection kind (eraseTailsList elements) none
  private def eraseTailsList : List Pattern → List Pattern
    | [] => []
    | pattern :: patterns => eraseTails pattern :: eraseTailsList patterns
end

@[simp] private theorem eraseTailsList_map (patterns : List Pattern) :
    eraseTailsList patterns = patterns.map eraseTails := by
  induction patterns with
  | nil => rfl
  | cons pattern patterns recurse => simp only [eraseTailsList,List.map_cons,recurse]

private theorem eraseTails_object {pattern : Pattern}
    (object : isObjectPattern pattern = true) : eraseTails pattern = pattern := by
  induction pattern using Pattern.inductionOn with
  | hbvar index => rfl
  | hfvar metavariable => rfl
  | happly label arguments recurse =>
      simp only [isObjectPattern,isObjectPatternList_iff] at object
      simp only [eraseTails,eraseTailsList_map]
      congr 1
      have fixed : arguments.map eraseTails = arguments.map id :=
        List.map_congr_left (fun pattern member => recurse pattern member (object pattern member))
      simpa only [List.map_id] using fixed
  | hlambda binder body recurse =>
      exact congrArg (Pattern.lambda binder) (recurse object)
  | hmultiLambda arity binders body recurse =>
      exact congrArg (Pattern.multiLambda arity binders) (recurse object)
  | hsubst body replacement bodyIH replacementIH => simp [isObjectPattern] at object
  | hcollection kind elements rest recurse =>
      simp only [isObjectPattern,Bool.and_eq_true,Option.isNone_iff_eq_none,isObjectPatternList_iff] at object
      rcases object with ⟨rfl,objects⟩
      simp only [eraseTails,eraseTailsList_map]
      congr 1
      have fixed : elements.map eraseTails = elements.map id :=
        List.map_congr_left (fun pattern member => recurse pattern member (objects pattern member))
      simpa only [List.map_id] using fixed

private theorem representation_eraseTails {parameter : TermParam} {argument : Pattern}
    (represented : MatchesParameterRepresentation parameter argument) :
    MatchesParameterRepresentation parameter (eraseTails argument) := by
  cases parameter with
  | simple bodyName type => trivial
  | abstractionNamed binderName bodyName type =>
      obtain ⟨body,rfl⟩ := (matchesParameterRepresentation_abstractionNamed_iff _ _ _ _).mp represented
      simp only [eraseTails,MatchesParameterRepresentation]
  | multiAbstractionNamed binderNames bodyName type =>
      obtain ⟨arity,body,rfl⟩ := (matchesParameterRepresentation_multiAbstractionNamed_iff _ _ _ _).mp represented
      simp only [eraseTails,MatchesParameterRepresentation]

mutual
  private theorem typed_eraseTails {language : LanguageDef} {free : FreeTypeContext}
      {bound : List TypeExpr} {pattern : Pattern} {type : TypeExpr}
      (typed : HasType language free bound pattern type) :
      HasType language free bound (eraseTails pattern) type := by
    cases typed with
    | bvar found => exact .bvar found
    | fvar found => exact .fvar found
    | constructor authored ordinary arguments =>
        simpa only [eraseTails,eraseTailsList_map] using
          HasType.constructor authored ordinary (arguments_eraseTails arguments)
    | lambda body =>
        simpa only [eraseTails] using HasType.lambda (typed_eraseTails body)
    | multiLambda body =>
        simpa only [eraseTails] using HasType.multiLambda (typed_eraseTails body)
    | subst body replacement =>
        simpa only [eraseTails] using HasType.subst (typed_eraseTails body) (typed_eraseTails replacement)
    | collection elements =>
        simpa only [eraseTails,eraseTailsList_map] using
          HasType.collection (rest := none) (elements_eraseTails elements)
    | collectionConstructor authored shape elements =>
        simpa only [eraseTails,eraseTailsList_map] using
          HasType.collectionConstructor (rest := none) authored shape (elements_eraseTails elements)
  private theorem arguments_eraseTails {language : LanguageDef} {free : FreeTypeContext}
      {bound : List TypeExpr} {arguments : List Pattern} {parameters : List TermParam}
      (typed : ArgumentsHaveTypes language free bound arguments parameters) :
      ArgumentsHaveTypes language free bound (arguments.map eraseTails) parameters := by
    cases typed with
    | nil => exact .nil
    | cons represented expected head tail =>
        exact .cons (representation_eraseTails represented) expected (typed_eraseTails head)
          (arguments_eraseTails tail)
  private theorem elements_eraseTails {language : LanguageDef} {free : FreeTypeContext}
      {bound : List TypeExpr} {elements : List Pattern} {type : TypeExpr}
      (typed : ElementsHaveType language free bound elements type) :
      ElementsHaveType language free bound (elements.map eraseTails) type := by
    cases typed with
    | nil bound type => exact .nil bound type
    | cons head tail => exact .cons (typed_eraseTails head) (elements_eraseTails tail)
end

private theorem sorted_eraseTails {language : LanguageDef} {pattern : Pattern} {sort : String}
    (sorted : SortedAt language pattern sort) : SortedAt language (eraseTails pattern) sort := by
  obtain ⟨free,bound,typed⟩ := sorted
  exact ⟨free,bound,typed_eraseTails typed⟩

private theorem collectionTyped_eraseTails {language : LanguageDef} {rule : GrammarRule}
    {kind : CollType} {elements : List Pattern}
    (typed : Mettapedia.GSLT.LanguageDef.WellSorted.CollectionTypedAt language rule kind elements) :
    Mettapedia.GSLT.LanguageDef.WellSorted.CollectionTypedAt language rule kind (elements.map eraseTails) := by
  obtain ⟨parameter,member,elementType,occurs,free,bound,body⟩ := typed
  refine ⟨parameter,member,elementType,occurs,free,bound,?_⟩
  simpa only [eraseTails,eraseTailsList_map] using typed_eraseTails body

private theorem derived_eraseTails {language : LanguageDef} {source target : Pattern}
    (step : DerivedInstance language source target) :
    DerivedInstance language (eraseTails source) (eraseTails target) := by
  cases step with
  | bagPerm declaration sorted permutation =>
      have mapped := collectionTyped_eraseTails sorted
      simp only [eraseTails,eraseTailsList_map] at mapped ⊢
      exact .bagPerm declaration mapped (permutation.map eraseTails)
  | setPerm declaration sorted permutation =>
      have mapped := collectionTyped_eraseTails sorted
      simp only [eraseTails,eraseTailsList_map] at mapped ⊢
      exact .setPerm declaration mapped (permutation.map eraseTails)
  | setDedup declaration sorted =>
      have mapped := collectionTyped_eraseTails sorted
      simp only [eraseTails,eraseTailsList_map,List.map_cons] at mapped ⊢
      exact .setDedup declaration mapped
  | flatten declaration flat sorted =>
      have mapped := sorted_eraseTails sorted
      simp only [eraseTails,eraseTailsList_map,List.map_append,List.map_cons] at mapped ⊢
      exact .flatten declaration flat mapped
  | singleton declaration flat sorted =>
      have mapped := sorted_eraseTails sorted
      simp only [eraseTails,eraseTailsList_map,List.map_cons,List.map_nil] at mapped ⊢
      exact .singleton declaration flat mapped
  | unitElim declaration unit sorted =>
      have mapped := sorted_eraseTails sorted
      simp only [eraseTails,eraseTailsList_map,List.map_append,List.map_cons,List.map_nil] at mapped ⊢
      exact .unitElim declaration unit mapped
  | emptyUnit declaration unit sorted =>
      have mapped := sorted_eraseTails sorted
      simp only [eraseTails,eraseTailsList_map,List.map_nil] at mapped ⊢
      exact .emptyUnit declaration unit mapped

private def eraseTailsContext : OneHoleContext → OneHoleContext
  | .hole => .hole
  | .apply label before inner after =>
      .apply label (before.map eraseTails) (eraseTailsContext inner) (after.map eraseTails)
  | .lambda binder inner => .lambda binder (eraseTailsContext inner)
  | .multiLambda arity binders inner => .multiLambda arity binders (eraseTailsContext inner)
  | .substBody inner replacement => .substBody (eraseTailsContext inner) (eraseTails replacement)
  | .substReplacement body inner => .substReplacement (eraseTails body) (eraseTailsContext inner)
  | .collection kind before inner after _ =>
      .collection kind (before.map eraseTails) (eraseTailsContext inner) (after.map eraseTails) none

private theorem eraseTails_fill (context : OneHoleContext) (pattern : Pattern) :
    eraseTails (context.fill pattern) = (eraseTailsContext context).fill (eraseTails pattern) := by
  induction context with
  | hole => rfl
  | apply label before inner after recurse =>
      simp only [OneHoleContext.fill,eraseTails,eraseTailsList_map,eraseTailsContext,
        List.map_append,List.map_cons,recurse]
  | lambda binder inner recurse => simp only [OneHoleContext.fill,eraseTails,eraseTailsContext,recurse]
  | multiLambda arity binders inner recurse => simp only [OneHoleContext.fill,eraseTails,eraseTailsContext,recurse]
  | substBody inner replacement recurse => simp only [OneHoleContext.fill,eraseTails,eraseTailsContext,recurse]
  | substReplacement body inner recurse => simp only [OneHoleContext.fill,eraseTails,eraseTailsContext,recurse]
  | collection kind before inner after rest recurse =>
      simp only [OneHoleContext.fill,eraseTails,eraseTailsList_map,eraseTailsContext,
        List.map_append,List.map_cons,recurse]

open Mettapedia.OSLF.MeTTaIL.MatchSpec

private def eraseBindings (bindings : Bindings) : Bindings :=
  bindings.map fun entry => (entry.1,eraseTails entry.2)

private theorem eraseBindings_find (bindings : Bindings) (metavariable : String) :
    (eraseBindings bindings).find? (·.1 == metavariable) =
      (bindings.find? (·.1 == metavariable)).map (fun entry => (entry.1,eraseTails entry.2)) := by
  simp only [eraseBindings,List.find?_map,Function.comp_def]

private theorem erase_applyBindings_fvar (bindings : Bindings) (metavariable : String) :
    eraseTails (applyBindings bindings (.fvar metavariable)) =
      applyBindings (eraseBindings bindings) (.fvar metavariable) := by
  simp only [applyBindings,eraseBindings_find]
  cases found : bindings.find? (·.1 == metavariable) with
  | none => simp only [Option.map_none,eraseTails]
  | some entry => cases entry; simp only [Option.map_some]

private theorem correctList_members (patterns : List Pattern) :
    isMatchCorrectListAux patterns = true ↔
      ∀ pattern ∈ patterns, Pattern.isMatchCorrect pattern = true := by
  induction patterns with
  | nil => simp [isMatchCorrectListAux]
  | cons pattern patterns recurse =>
      simp only [isMatchCorrectListAux,Bool.and_eq_true,Pattern.isMatchCorrect,
        List.forall_mem_cons] at recurse ⊢
      exact and_congr_right (fun _ => recurse)

private theorem erase_applyBindings_correct (bindings : Bindings) {pattern : Pattern}
    (correct : Pattern.isMatchCorrect pattern = true) :
    eraseTails (applyBindings bindings pattern) = applyBindings (eraseBindings bindings) pattern := by
  induction pattern using Pattern.inductionOn with
  | hbvar index => simp only [applyBindings,eraseTails]
  | hfvar metavariable => exact erase_applyBindings_fvar bindings metavariable
  | happly label arguments recurse =>
      have each := (correctList_members arguments).mp correct
      simp only [applyBindings,eraseTails,eraseTailsList_map,List.map_map]
      congr 1
      exact List.map_congr_left (fun pattern member => recurse pattern member (each pattern member))
  | hlambda binder body recurse => simp [Pattern.isMatchCorrect,isMatchCorrectAux] at correct
  | hmultiLambda arity binders body recurse => simp [Pattern.isMatchCorrect,isMatchCorrectAux] at correct
  | hsubst body replacement bodyIH replacementIH => simp [Pattern.isMatchCorrect,isMatchCorrectAux] at correct
  | hcollection kind elements rest recurse => simp [Pattern.isMatchCorrect,isMatchCorrectAux] at correct

private theorem erase_applyBindings_row (bindings : Bindings) {pattern : Pattern}
    (row : RowPattern pattern) :
    eraseTails (applyBindings bindings pattern) = applyBindings (eraseBindings bindings) pattern := by
  rcases row with correct | ⟨elements,rfl,correct⟩
  · exact erase_applyBindings_correct bindings correct
  · simp only [applyBindings,eraseTails,eraseTailsList_map,List.append_nil,List.map_map]
    congr 1
    exact List.map_congr_left (fun pattern member => erase_applyBindings_correct bindings (correct pattern member))

/-- The actual matcher preserves the internal observer even on raw subjects
whose tail annotation is ignored by ordinary bag matching. -/
private theorem match_tailInvariant {unit : Option String} {pattern subject : Pattern} {bindings : Bindings}
    (row : RowPattern pattern) (matched : bindings ∈ matchPattern pattern subject) :
    normalForm unit (eraseTails subject) =
      normalForm unit (eraseTails (applyBindings bindings pattern)) := by
  rcases row with correct | ⟨elements,rfl,correct⟩
  · rw [matchPattern_correct matched correct]
  · have relational := matchPattern_sound matched
    cases relational with
    | collection _ bagMatch =>
      have permutation := matchBag_reconstruct bagMatch correct (fun _ _ found => found)
      simp only [eraseTails,eraseTailsList_map,applyBindings,List.append_nil,normalForm_bag,List.map_map]
      simpa only [List.map_map,Function.comp_def] using
        (normalizeBag_perm unit (permutation.map (fun pattern => normalForm unit (eraseTails pattern)))).symm

private theorem equationInstance_tailInvariant {language : LanguageDef} {unit : Option String}
    (rows : ∀ row ∈ language.equations,
      row.premises = [] ∧ RowPattern row.left ∧ RowPattern row.right ∧
        ∀ bindings, normalForm unit (applyBindings bindings row.left) =
          normalForm unit (applyBindings bindings row.right))
    {base : BasePremiseEvaluator} {source target : Pattern}
    (step : EquationInstance base language source target) :
    normalForm unit (eraseTails source) = normalForm unit (eraseTails target) := by
  obtain ⟨fuel,step⟩ := step
  cases step with
  | forward member matched premises applied =>
      obtain ⟨empty,leftRow,rightRow,invariant⟩ := rows _ member
      rw [empty] at premises
      cases premises
      rw [← applied]
      apply (match_tailInvariant leftRow matched).trans
      rw [erase_applyBindings_row _ leftRow,erase_applyBindings_row _ rightRow]
      exact invariant _
  | reverse member matched premises applied =>
      obtain ⟨empty,leftRow,rightRow,invariant⟩ := rows _ member
      rw [empty] at premises
      cases premises
      rw [← applied]
      apply (match_tailInvariant rightRow matched).trans
      rw [erase_applyBindings_row _ rightRow,erase_applyBindings_row _ leftRow]
      exact (invariant _).symm

/-- Actual raw equation equivalence preserves the existing normal form at
object endpoints. The proof uses an internal invariant on all intermediates;
it does not alter the matcher or install tail erasure operationally. -/
theorem source_normalForm_eq_of_equationEquiv {language : LanguageDef} {bag : GrammarRule}
    {unit : Option String} (laws : BagTheory {language with equations := []} bag unit)
    (rows : ∀ row ∈ language.equations,
      row.premises = [] ∧ RowPattern row.left ∧ RowPattern row.right ∧
        ∀ bindings, normalForm unit (applyBindings bindings row.left) =
          normalForm unit (applyBindings bindings row.right))
    {base : BasePremiseEvaluator} {left right : Pattern}
    (leftObject : isObjectPattern left = true) (rightObject : isObjectPattern right = true)
    (related : EquationEquiv base language left right) :
    normalForm unit left = normalForm unit right := by
  have invariant := equationEquiv_invariant (fun pattern => normalForm unit (eraseTails pattern))
    (fun context first second same => by
      rw [eraseTails_fill,eraseTails_fill]
      exact normalForm_fill_congr unit (eraseTailsContext context) same)
    (fun source target generator => by
      rcases generator with authored | derived
      · exact equationInstance_tailInvariant rows authored
      · exact normalForm_derived laws
          (grammar_derived (source := language) (target := {language with equations := []}) rfl
            (derived_eraseTails derived))) related
  simpa only [eraseTails_object leftObject,eraseTails_object rightObject] using invariant

/-- Soundness and reflection against the actual unrestricted raw source
relation, for admissible endpoints of a collection-free result type. -/
theorem source_equationEquiv_iff_normalForm_eq {language : LanguageDef} {bag : GrammarRule}
    {unit : Option String} (laws : BareBagTheory {language with equations := []} bag unit)
    (rows : ∀ row ∈ language.equations,
      row.premises = [] ∧ RowPattern row.left ∧ RowPattern row.right ∧
        ∀ bindings, normalForm unit (applyBindings bindings row.left) =
          normalForm unit (applyBindings bindings row.right))
    (base : BasePremiseEvaluator) {free : FreeTypeContext} {bound : List TypeExpr}
    {type : TypeExpr} {left right : Pattern}
    (leftGood : Admissible language free bound type left)
    (rightGood : Admissible language free bound type right)
    (collectionless : collectionFree type = true) :
    EquationEquiv base language left right ↔ normalForm unit left = normalForm unit right := by
  constructor
  · exact source_normalForm_eq_of_equationEquiv laws.toBagTheory rows leftGood.object rightGood.object
  · intro same
    exact .trans _ _ _ (source_equiv_normalForm laws base leftGood collectionless)
      (same ▸ (source_equiv_normalForm laws base rightGood collectionless).symm)

#print axioms erase_applyBindings_row
#print axioms match_tailInvariant
#print axioms equationInstance_tailInvariant
#print axioms source_normalForm_eq_of_equationEquiv
#print axioms source_equationEquiv_iff_normalForm_eq

#print axioms eraseTails_object
#print axioms typed_eraseTails
#print axioms derived_eraseTails
#print axioms eraseTails_fill
end Mettapedia.GSLT.LanguageDef.BagNormalForm.WithAuthoredEquations

namespace Mettapedia.GSLT.LanguageDef.BagNormalForm.WithAuthoredEquations.AlgebraFocus

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.MeTTaIL.DerivedContexts
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.LanguageDef.EquationSemantics
open Mettapedia.OSLF.MeTTaIL.Match Mettapedia.OSLF.MeTTaIL.MatchSpec

/-- A proof view at the homogeneous algebra's base-sort focus. Empty and
singleton views retain a carrier for matching; this is not data normalization. -/
def view (unitLabel : String) (focus : Pattern) : Pattern :=
  .collection .hashBag (bagContents unitLabel [focus]) none

/-- Reading a root-normal algebra value into components and rebuilding by the
existing algebra collapse returns that value, including the declared unit. -/
theorem collapse_contents {unitLabel : String} {focus : Pattern}
    (normal : RootNormal unitLabel focus) :
    collapse unitLabel (bagContents unitLabel [focus]) = focus := by
  by_cases bagNode : IsBagNode focus
  · obtain ⟨elements, rfl⟩ := bagNode
    obtain ⟨_, many, plain⟩ := normal elements rfl
    have contents : bagContents unitLabel [.collection .hashBag elements none] = elements := by
      simp only [bagContents, List.flatMap_cons, List.flatMap_nil, List.append_nil, splice_bag]
      apply List.filter_eq_self.mpr
      intro element member
      simpa using (plain element member).1
    rw [contents, collapse_eq_bag_of_length unitLabel elements many]
  · by_cases isUnit : focus = .apply unitLabel []
    · subst focus
      simp [bagContents, splice, collapse]
    · simp [bagContents, splice_of_not_bag bagNode, isUnit, collapse]

/-- Each selected component has the same complete local typing and metadata
as the homogeneous focus. The residual's outer carrier is not collapsed. -/
theorem component_admissible {language : LanguageDef} {bag : GrammarRule} {unitLabel : String}
    (laws : BareBagTheory {language with equations := []} bag (some unitLabel))
    {free : FreeTypeContext} {bound : List TypeExpr} {focus component : Pattern}
    (good : Admissible language free bound (.base bag.category) focus)
    (member : component ∈ bagContents unitLabel [focus]) :
    Admissible language free bound (.base bag.category) component := by
  have selected : component ∈ splice focus := by
    exact (List.mem_filter.mp (by simpa only [bagContents, List.flatMap_cons,
      List.flatMap_nil, List.append_nil] using member)).1
  by_cases bagNode : IsBagNode focus
  · obtain ⟨elements, rfl⟩ := bagNode
    have inElements : component ∈ elements := by simpa using selected
    have comparisonGood := grammar_admissible (source := language)
      (target := {language with equations := []}) rfl good
    obtain ⟨_, _, typed⟩ := bag_typing laws comparisonGood.typed rfl
    refine ⟨grammar_hasType (source := {language with equations := []}) (target := language) rfl
      (elementsHaveType_iff.mp typed component inElements), ?_, ?_⟩
    · have all : Pattern.hasCanonicalBinderMetadataList elements = true := by
        simpa [Pattern.hasCanonicalBinderMetadata] using good.canonical
      exact hasCanonicalBinderMetadataList_iff.mp all component inElements
    · have all : isObjectPatternList elements = true := by
        simpa [isObjectPattern] using good.object
      exact isObjectPatternList_iff.mp all component inElements
  · rw [splice_of_not_bag bagNode] at selected
    exact List.mem_singleton.mp selected ▸ good

/-- Reading the full normal form of a bag as components returns its existing
sorted flattened contents; no outer data carrier is normalized here. -/
theorem normalForm_bag_contents (unitLabel : String) (elements : List Pattern) :
    bagContents unitLabel [normalForm (some unitLabel) (.collection .hashBag elements none)] =
      Mettapedia.OSLF.MeTTaIL.PatternCode.sortPatterns
        (bagContents unitLabel (elements.map (normalForm (some unitLabel)))) := by
  rw [normalForm_bag]
  simp only [normalizeBag]
  apply bagContents_collapse
  intro component member
  apply bagContents_spec (elements := elements.map (normalForm (some unitLabel)))
  · intro element inElements
    obtain ⟨original, _, rfl⟩ := List.mem_map.mp inElements
    exact rootNormal_normalForm unitLabel original
  · exact mem_sortPatterns.mp member

private theorem source_bag_element {language : LanguageDef} {bag : GrammarRule} {unitLabel : String}
    (laws : BareBagTheory {language with equations := []} bag (some unitLabel))
    {free : FreeTypeContext} {bound : List TypeExpr} {elements : List Pattern} {element : Pattern}
    (good : Admissible language free bound (.base bag.category) (.collection .hashBag elements none))
    (member : element ∈ elements) :
    Admissible language free bound (.base bag.category) element := by
  have comparisonGood := grammar_admissible (source := language)
    (target := {language with equations := []}) rfl good
  obtain ⟨_, _, typed⟩ := bag_typing laws comparisonGood.typed rfl
  refine ⟨grammar_hasType (source := {language with equations := []}) (target := language) rfl
    (elementsHaveType_iff.mp typed element member), ?_, ?_⟩
  · exact hasCanonicalBinderMetadataList_iff.mp
      (by simpa [Pattern.hasCanonicalBinderMetadata] using good.canonical) element member
  · exact isObjectPatternList_iff.mp (by simpa [isObjectPattern] using good.object) element member

/-- Each flattened component is read from an actual original subterm, not
from an invented canonical child index. Its source zipper crosses only bag
carriers; local scopes, constructor boundaries and complete typing remain. -/
theorem component_source_origin {language : LanguageDef} {bag : GrammarRule} {unitLabel : String}
    (laws : BareBagTheory {language with equations := []} bag (some unitLabel))
    {free : FreeTypeContext} {bound : List TypeExpr} :
    ∀ (source : Pattern) {component : Pattern},
      Admissible language free bound (.base bag.category) source →
      component ∈ bagContents unitLabel [normalForm (some unitLabel) source] →
      ∃ (original : Pattern) (context : OneHoleContext), Admissible language free bound (.base bag.category) original ∧
        context.fill original = source ∧ normalForm (some unitLabel) original = component ∧
        ∀ replacement, HasType language free bound replacement (.base bag.category) →
          HasType language free bound (context.fill replacement) (.base bag.category)
  | source, component, good, member => by
    by_cases isBag : IsBagNode source
    · obtain ⟨elements, rfl⟩ := isBag
      rw [normalForm_bag_contents] at member
      have contentMember := mem_sortPatterns.mp member
      simp only [bagContents, List.mem_filter, List.mem_flatMap, List.mem_map,
        decide_eq_true_eq] at contentMember
      obtain ⟨⟨_, ⟨element, elementMember, rfl⟩, spliced⟩, notUnit⟩ := contentMember
      have inside : component ∈ bagContents unitLabel [normalForm (some unitLabel) element] := by
        simp only [bagContents, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_filter,
          decide_eq_true_eq]
        exact ⟨spliced, notUnit⟩
      obtain ⟨original, inner, originalGood, innerFill, image, rebuild⟩ :=
        component_source_origin laws element (source_bag_element laws good elementMember) inside
      obtain ⟨index, selected⟩ := List.mem_iff_getElem?.mp elementMember
      have within := (List.getElem?_eq_some_iff.mp selected).1
      have split : elements.take index ++ element :: elements.drop (index + 1) = elements := by
        rw [← (List.getElem?_eq_some_iff.mp selected).2, List.getElem_cons_drop within]
        exact List.take_append_drop index elements
      refine ⟨original, .collection .hashBag (elements.take index) inner (elements.drop (index + 1)) none,
        originalGood, ?_, image, ?_⟩
      · simp only [OneHoleContext.fill, innerFill, split]
      · intro replacement replacementTyped
        apply grammar_hasType (source := {language with equations := []}) (target := language) rfl
        apply bag_hasType laws
        apply grammar_elements (source := language) (target := {language with equations := []}) rfl
        apply elementsHaveType_iff.mpr
        intro item itemMember
        simp only [List.mem_append, List.mem_cons] at itemMember
        rcases itemMember with earlier | replaced | later
        · exact (source_bag_element laws good (List.mem_of_mem_take earlier)).typed
        · subst item
          exact rebuild replacement replacementTyped
        · exact (source_bag_element laws good (List.mem_of_mem_drop later)).typed
    · have normalizedNotBag : ¬ IsBagNode (normalForm (some unitLabel) source) := by
        cases source with
        | collection kind elements rest =>
          cases kind <;> cases rest <;>
            simp_all [IsBagNode, normalForm]
        | _ => simp_all [IsBagNode, normalForm]
      have selected : component ∈ splice (normalForm (some unitLabel) source) := by
        exact (List.mem_filter.mp (by simpa only [bagContents, List.flatMap_cons,
          List.flatMap_nil, List.append_nil] using member)).1
      rw [splice_of_not_bag normalizedNotBag] at selected
      have same := List.mem_singleton.mp selected
      exact ⟨source, .hole, good, rfl, same.symm, fun _ typed => typed⟩
termination_by source => sizeOf source

/-- The view is admissible as the declared algebra's base-sort value. -/
theorem view_admissible {language : LanguageDef} {bag : GrammarRule} {unitLabel : String}
    (laws : BareBagTheory {language with equations := []} bag (some unitLabel))
    {free : FreeTypeContext} {bound : List TypeExpr} {focus : Pattern}
    (good : Admissible language free bound (.base bag.category) focus) :
    Admissible language free bound (.base bag.category) (view unitLabel focus) := by
  have typed : ElementsHaveType language free bound (bagContents unitLabel [focus])
      (.base bag.category) := elementsHaveType_iff.mpr
    (fun component member => (component_admissible laws good member).typed)
  refine ⟨grammar_hasType (source := {language with equations := []}) (target := language) rfl
    (bag_hasType laws (grammar_elements (source := language)
      (target := {language with equations := []}) rfl typed)), ?_, ?_⟩
  · change Pattern.hasCanonicalBinderMetadataList _ = true
    exact hasCanonicalBinderMetadataList_iff.mpr
      (fun component member => (component_admissible laws good member).canonical)
  · change (true && isObjectPatternList _) = true
    simp only [Bool.true_and]
    exact isObjectPatternList_iff.mpr
      (fun component member => (component_admissible laws good member).object)

/-- Deleting a selected occurrence leaves collection data, even when no
component or only one component remains. -/
theorem residual_admissible {language : LanguageDef} {bag : GrammarRule} {unitLabel : String}
    (laws : BareBagTheory {language with equations := []} bag (some unitLabel))
    {free : FreeTypeContext} {bound : List TypeExpr} {focus : Pattern}
    (good : Admissible language free bound (.base bag.category) focus) (index : Nat) :
    Admissible language free bound (.collection .hashBag (.base bag.category))
      (.collection .hashBag ((bagContents unitLabel [focus]).eraseIdx index) none) := by
  have each : ∀ component ∈ (bagContents unitLabel [focus]).eraseIdx index,
      Admissible language free bound (.base bag.category) component :=
    fun component member => component_admissible laws good (List.mem_of_mem_eraseIdx member)
  refine ⟨.collection (elementsHaveType_iff.mpr fun component member => (each component member).typed), ?_, ?_⟩
  · change Pattern.hasCanonicalBinderMetadataList _ = true
    exact hasCanonicalBinderMetadataList_iff.mpr fun component member => (each component member).canonical
  · change (true && isObjectPatternList _) = true
    simp only [Bool.true_and]
    exact isObjectPatternList_iff.mpr fun component member => (each component member).object

/-- The virtual carrier is a representative obtained by the source's own
empty/singleton laws. This statement requires the actual base-sort role. -/
theorem view_equivalent {language : LanguageDef} {bag : GrammarRule} {unitLabel : String}
    (laws : BareBagTheory {language with equations := []} bag (some unitLabel))
    (base : BasePremiseEvaluator) {free : FreeTypeContext} {bound : List TypeExpr} {focus : Pattern}
    (good : Admissible language free bound (.base bag.category) focus)
    (normal : RootNormal unitLabel focus) :
    EquationEquiv base language focus (view unitLabel focus) := by
  have viewGood := view_admissible laws good
  have comparisonGood := grammar_admissible (source := language)
    (target := {language with equations := []}) rfl viewGood
  have path := path_collapse (base := base) laws rfl comparisonGood
  have sourcePath := comparison_path (language := language) path
  rw [collapse_contents normal] at sourcePath
  exact (Relation.EqvGen.reflTransGen_le_eqvGen _ _ _ sourcePath).symm

/-- Every admissible source focus has a typed matching representative, with
all retained equation rows still present. -/
theorem normalized_view_equivalent {language : LanguageDef} {bag : GrammarRule} {unitLabel : String}
    (laws : BareBagTheory {language with equations := []} bag (some unitLabel))
    (base : BasePremiseEvaluator) {free : FreeTypeContext} {bound : List TypeExpr} {source : Pattern}
    (good : Admissible language free bound (.base bag.category) source) :
    EquationEquiv base language source (view unitLabel (normalForm (some unitLabel) source)) := by
  exact .trans _ _ _ (source_equiv_normalForm laws base good rfl)
    (view_equivalent laws base (normalized_admissible laws base good rfl)
      (rootNormal_normalForm unitLabel source))

/-- A component position of the virtual carrier is a real occurrence of the
root-normal source focus. The unit has none; a scalar component is at the
root, not at a fabricated collection child. -/
theorem component_origin {unitLabel : String} {focus component : Pattern} {index : Nat}
    (normal : RootNormal unitLabel focus)
    (selected : (bagContents unitLabel [focus])[index]? = some component) :
    ∃ context : OneHoleContext, context.fill component = focus ∧
      ((context = .hole ∧ component = focus ∧ index = 0) ∨
        ∃ elements, focus = .collection .hashBag elements none ∧
          elements[index]? = some component ∧
          context = .collection .hashBag (elements.take index) .hole (elements.drop (index + 1)) none) := by
  by_cases bagNode : IsBagNode focus
  · obtain ⟨elements, rfl⟩ := bagNode
    obtain ⟨_, _, plain⟩ := normal elements rfl
    have contents : bagContents unitLabel [.collection .hashBag elements none] = elements := by
      simp only [bagContents, List.flatMap_cons, List.flatMap_nil, List.append_nil, splice_bag]
      apply List.filter_eq_self.mpr
      intro element member
      simpa using (plain element member).1
    rw [contents] at selected
    refine ⟨.collection .hashBag (elements.take index) .hole (elements.drop (index + 1)) none, ?_,
      .inr ⟨elements, rfl, selected, rfl⟩⟩
    simp only [OneHoleContext.fill]
    exact congrArg (fun values => Pattern.collection .hashBag values none)
      (by rw [← (List.getElem?_eq_some_iff.mp selected).2,
        List.getElem_cons_drop (List.getElem?_eq_some_iff.mp selected).1]
          exact List.take_append_drop index elements)
  · by_cases isUnit : focus = .apply unitLabel []
    · subst focus
      simp [bagContents, splice] at selected
    · have contents : bagContents unitLabel [focus] = [focus] := by
        simp [bagContents, splice_of_not_bag bagNode, isUnit]
      rw [contents] at selected
      have within := (List.getElem?_eq_some_iff.mp selected).1
      have atZero : index = 0 := by simp at within; omega
      subst index
      simp only [List.getElem?_cons_zero, Option.some.injEq] at selected
      subst component
      exact ⟨.hole, rfl, .inl ⟨rfl, rfl, rfl⟩⟩

/-- Matching one component and the exact residual uses the existing ordinary
bag relation. It does not collapse the rest capture into its sole element. -/
theorem match_view_single_rest {unitLabel : String} {focus schema : Pattern} {index : Nat}
    {restName : String} {headBindings bindings : Bindings}
    (within : index < (bagContents unitLabel [focus]).length)
    (head : MatchRel schema (bagContents unitLabel [focus])[index] headBindings)
    (merged : mergeBindings headBindings [(restName,
      .collection .hashBag ((bagContents unitLabel [focus]).eraseIdx index) none)] = some bindings) :
    MatchRel (.collection .hashBag [schema] (some restName)) (view unitLabel focus) bindings := by
  exact .collection (by decide) (.cons index within head .nilRest merged)

/-- Recover an ordinary collection match as an actual typed source
representative. The input is the existing independent bag-matching judgment,
not a certificate asserting source completeness or firing coherence. -/
theorem recover_representative {language : LanguageDef} {bag : GrammarRule} {unitLabel : String}
    (laws : BareBagTheory {language with equations := []} bag (some unitLabel))
    (base : BasePremiseEvaluator) {free : FreeTypeContext} {bound : List TypeExpr} {source : Pattern}
    (good : Admissible language free bound (.base bag.category) source)
    {schemas : List Pattern} {rest : Option String} {bindings : Bindings}
    (matched : MatchBagRel schemas rest .hashBag
      (bagContents unitLabel [normalForm (some unitLabel) source]) bindings) :
    ∃ representative, EquationEquiv base language source representative ∧
      Admissible language free bound (.base bag.category) representative ∧
      MatchRel (.collection .hashBag schemas rest) representative bindings := by
  refine ⟨view unitLabel (normalForm (some unitLabel) source),
    normalized_view_equivalent laws base good,
    view_admissible laws (normalized_admissible laws base good rfl), ?_⟩
  exact .collection (by decide) matched

/-- A step performed at the recovered typed carrier is a step modulo the
actual source equations. No converse firing-normalization premise is assumed. -/
theorem stepModulo_of_view_step {language : LanguageDef} {bag : GrammarRule} {unitLabel : String}
    (laws : BareBagTheory {language with equations := []} bag (some unitLabel))
    (base : BasePremiseEvaluator) {free : FreeTypeContext} {bound : List TypeExpr}
    {source target : Pattern} (good : Admissible language free bound (.base bag.category) source)
    (step : Step base language (view unitLabel (normalForm (some unitLabel) source)) target) :
    StepModuloEquations base language source target :=
  ⟨_, target, normalized_view_equivalent laws base good, step, .refl _⟩

/-- Origin transport composes with the existing structural zipper. All outer
constructor and binder frames remain exactly those supplied by that context. -/
theorem component_origin_in_context {unitLabel : String} {focus component : Pattern} {index : Nat}
    (normal : RootNormal unitLabel focus)
    (selected : (bagContents unitLabel [focus])[index]? = some component)
    (outer : OneHoleContext) :
    ∃ context : OneHoleContext,
      (outer.comp context).fill component = outer.fill focus ∧
      Selects component (outer.comp context) (outer.fill focus) := by
  obtain ⟨context, fills, _⟩ := component_origin normal selected
  refine ⟨context, by rw [OneHoleContext.fill_comp, fills], ?_⟩
  rw [← fills, ← OneHoleContext.fill_comp]
  exact Selects.of_fill _ _

#print axioms collapse_contents
#print axioms component_admissible
#print axioms normalForm_bag_contents
#print axioms source_bag_element
#print axioms component_source_origin
#print axioms view_admissible
#print axioms residual_admissible
#print axioms view_equivalent
#print axioms normalized_view_equivalent
#print axioms component_origin
#print axioms match_view_single_rest
#print axioms recover_representative
#print axioms stepModulo_of_view_step
#print axioms component_origin_in_context

end Mettapedia.GSLT.LanguageDef.BagNormalForm.WithAuthoredEquations.AlgebraFocus

namespace Mettapedia.GSLT.LanguageDef.BagNormalForm.WithAuthoredEquations.AlgebraFocus

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.MeTTaIL.DerivedContexts
open Mettapedia.OSLF.MeTTaIL.GeneralTypedSites
open Mettapedia.OSLF.MeTTaIL.PatternCode
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.LanguageDef.EquationSemantics

/-- A physical source occurrence, with its actual syntax and zipper retained
beside the value read by the existing normalizer. Equal values do not identify
these records or their source addresses. -/
structure SourceOccurrence where
  original : Pattern
  address : List Nat
  context : OneHoleContext
  value : Pattern
  deriving DecidableEq, Repr

namespace SourceOccurrence

def leaf (unitLabel : String) (source : Pattern) : SourceOccurrence :=
  ⟨source, [], .hole, normalForm (some unitLabel) source⟩

def wrap (elements : List Pattern) (index : Nat) (inner : SourceOccurrence) : SourceOccurrence :=
  { inner with
    address := index :: inner.address
    context := .collection .hashBag (elements.take index) inner.context (elements.drop (index + 1)) none }

end SourceOccurrence

/-- Enumerate physical algebra components in source order. Only closed bag
carriers are traversed; constructors, binders and data boundaries stay intact.
Actual unit leaves remain here and are accounted for separately below. -/
def sourceOccurrences (unitLabel : String) : Pattern → List SourceOccurrence
  | .collection .hashBag elements none =>
      elements.attach.zipIdx.flatMap fun pair =>
        (sourceOccurrences unitLabel pair.1.val).map (SourceOccurrence.wrap elements pair.2)
  | source => [SourceOccurrence.leaf unitLabel source]
termination_by source => sizeOf source
decreasing_by
  have smaller := List.sizeOf_lt_of_mem pair.1.property
  simp_wf
  omega

private theorem zipIdx_mapValues {α β : Type} (f : α → β) :
    ∀ (items : List α) (start : Nat),
      (items.map f).zipIdx start = (items.zipIdx start).map (fun pair => (f pair.1,pair.2))
  | [], _ => rfl
  | head :: tail, start => by
      simp only [List.map_cons, List.zipIdx_cons, List.map_cons, zipIdx_mapValues f tail (start + 1)]

private theorem attach_zipIdx_flatMap {α β : Type} (items : List α) (f : α → Nat → List β) :
    items.attach.zipIdx.flatMap (fun pair => f pair.1.val pair.2) =
      items.zipIdx.flatMap (fun pair => f pair.1 pair.2) := by
  have mapped : items.attach.map (fun entry => entry.val) = items := by
    exact List.attach_map_subtype_val items
  conv_rhs => rw [← mapped, zipIdx_mapValues]
  simp only [List.flatMap_map]

/-- The source traversal's child indices are the actual original list
indices, independent of the termination proof's attached membership data. -/
theorem sourceOccurrences_bag (unitLabel : String) (elements : List Pattern) :
    sourceOccurrences unitLabel (.collection .hashBag elements none) =
      elements.zipIdx.flatMap (fun pair =>
        (sourceOccurrences unitLabel pair.1).map (SourceOccurrence.wrap elements pair.2)) := by
  rw [sourceOccurrences]
  exact attach_zipIdx_flatMap elements (fun element index =>
    (sourceOccurrences unitLabel element).map (SourceOccurrence.wrap elements index))

theorem sourceOccurrences_nonbag {unitLabel : String} {source : Pattern}
    (notBag : ¬ IsBagNode source) :
    sourceOccurrences unitLabel source = [SourceOccurrence.leaf unitLabel source] := by
  cases source with
  | collection kind elements rest => cases kind <;> cases rest <;> simp_all [sourceOccurrences, IsBagNode]
  | _ => simp only [sourceOccurrences]


/-- Traversal distinguishes physical addresses before any value sorting or
unit filtering, even when several source leaves have the same value. -/
theorem sourceOccurrences_distinct (unitLabel : String) :
    ∀ source, (sourceOccurrences unitLabel source).Pairwise
      (fun first second => first.address ≠ second.address)
  | source => by
    by_cases isBag : IsBagNode source
    · obtain ⟨elements, rfl⟩ := isBag
      rw [sourceOccurrences_bag, List.pairwise_flatMap]
      constructor
      · intro pair selected
        apply List.pairwise_map.mpr
        have inside := List.mem_of_getElem? (List.mk_mem_zipIdx_iff_getElem?.mp selected)
        exact (sourceOccurrences_distinct unitLabel pair.1).imp
          (fun {_ _} different same => different (List.cons.inj same).2)
      · have distinct : (elements.zipIdx).Pairwise
            (fun first second => first.2 ≠ second.2) := by
          apply List.pairwise_map.mp
          change (elements.zipIdx.map Prod.snd).Nodup
          rw [List.zipIdx_map_snd]
          exact List.nodup_range'
        apply distinct.imp
        intro first second different left leftMember right rightMember same
        obtain ⟨firstTag, _, rfl⟩ := List.mem_map.mp leftMember
        obtain ⟨secondTag, _, rfl⟩ := List.mem_map.mp rightMember
        exact different (List.cons.inj same).1
    · rw [sourceOccurrences_nonbag isBag]
      simp
termination_by source => sizeOf source

/-- Every enumerated record carries its real original typed subterm and
source zipper, with no change to the local free or bound typing context. -/
theorem sourceOccurrences_sound {language : LanguageDef} {bag : GrammarRule} {unitLabel : String}
    (laws : BareBagTheory {language with equations := []} bag (some unitLabel))
    {free : FreeTypeContext} {bound : List TypeExpr} :
    ∀ (source : Pattern), Admissible language free bound (.base bag.category) source →
      ∀ occurrence ∈ sourceOccurrences unitLabel source,
        Admissible language free bound (.base bag.category) occurrence.original ∧
          occurrence.context.fill occurrence.original = source ∧
          occurrence.value = normalForm (some unitLabel) occurrence.original ∧
          contextAddress occurrence.context = occurrence.address ∧
          ∀ replacement, HasType language free bound replacement (.base bag.category) →
            HasType language free bound (occurrence.context.fill replacement) (.base bag.category)
  | source, good, occurrence, member => by
    by_cases isBag : IsBagNode source
    · obtain ⟨elements, rfl⟩ := isBag
      rw [sourceOccurrences_bag] at member
      obtain ⟨⟨element, index⟩, selected, mapped⟩ := List.mem_flatMap.mp member
      obtain ⟨inner, inInner, rfl⟩ := List.mem_map.mp mapped
      have atIndex := List.mk_mem_zipIdx_iff_getElem?.mp selected
      have within := (List.getElem?_eq_some_iff.mp atIndex).1
      have elementGood := source_bag_element laws good (List.mem_of_getElem? atIndex)
      obtain ⟨originalGood, fills, image, address, rebuild⟩ :=
        sourceOccurrences_sound laws element elementGood inner inInner
      have split : elements.take index ++ element :: elements.drop (index + 1) = elements := by
        rw [← (List.getElem?_eq_some_iff.mp atIndex).2, List.getElem_cons_drop within]
        exact List.take_append_drop index elements
      refine ⟨originalGood, ?_, image, ?_, ?_⟩
      · simp only [SourceOccurrence.wrap, OneHoleContext.fill, fills, split]
      · simp only [SourceOccurrence.wrap, contextAddress, address, List.length_take,
          Nat.min_eq_left (Nat.le_of_lt within)]
      · intro replacement replacementTyped
        apply grammar_hasType (source := {language with equations := []}) (target := language) rfl
        apply bag_hasType laws
        apply grammar_elements (source := language) (target := {language with equations := []}) rfl
        apply elementsHaveType_iff.mpr
        intro item itemMember
        simp only [List.mem_append, List.mem_cons] at itemMember
        rcases itemMember with earlier | replaced | later
        · exact (source_bag_element laws good (List.mem_of_mem_take earlier)).typed
        · subst item
          exact rebuild replacement replacementTyped
        · exact (source_bag_element laws good (List.mem_of_mem_drop later)).typed
    · rw [sourceOccurrences_nonbag isBag] at member
      obtain rfl := List.mem_singleton.mp member
      exact ⟨good, rfl, rfl, rfl, fun _ typed => typed⟩
termination_by source => sizeOf source
decreasing_by
  all_goals
    subst_vars
    have smaller := List.sizeOf_lt_of_mem (List.mem_of_getElem? atIndex)
    simp_all
    omega

/-- Physical components omit actual unit leaves, while preserving their
source records in the separate administrative account. -/
def componentOccurrences (unitLabel : String) (source : Pattern) : List SourceOccurrence :=
  (sourceOccurrences unitLabel source).filter fun occurrence => decide (occurrence.value ≠ .apply unitLabel [])

def unitOccurrences (unitLabel : String) (source : Pattern) : List SourceOccurrence :=
  (sourceOccurrences unitLabel source).filter fun occurrence => decide (occurrence.value = .apply unitLabel [])

/-- Sorting transports complete source records, not their values alone. -/
def sortOccurrences (occurrences : List SourceOccurrence) : List SourceOccurrence :=
  occurrences.mergeSort fun first second => decide (patternCode first.value ≤ patternCode second.value)

def normalizedOccurrences (unitLabel : String) (source : Pattern) : List SourceOccurrence :=
  sortOccurrences (componentOccurrences unitLabel source)

theorem sortOccurrences_perm (occurrences : List SourceOccurrence) :
    (sortOccurrences occurrences).Perm occurrences := List.mergeSort_perm _ _

/-- Erasing the sorted tags gives exactly the existing value sorter. -/
theorem sortOccurrences_values (occurrences : List SourceOccurrence) :
    (sortOccurrences occurrences).map SourceOccurrence.value =
      sortPatterns (occurrences.map SourceOccurrence.value) := by
  have ordered : (sortOccurrences occurrences).Pairwise
      (fun first second => patternCode first.value ≤ patternCode second.value) := by
    have sorted := List.pairwise_mergeSort
      (le := fun first second : SourceOccurrence => decide (patternCode first.value ≤ patternCode second.value))
      (fun first second third earlier later => by
        simp only [decide_eq_true_eq] at earlier later ⊢
        exact Nat.le_trans earlier later)
      (fun first second => by simp only [Bool.or_eq_true, decide_eq_true_eq]; exact Nat.le_total _ _) occurrences
    simpa [sortOccurrences] using sorted
  have imageOrdered : ((sortOccurrences occurrences).map SourceOccurrence.value).Pairwise
      (fun first second => patternCode first ≤ patternCode second) := List.pairwise_map.mpr ordered
  calc
    _ = sortPatterns ((sortOccurrences occurrences).map SourceOccurrence.value) :=
      (sortPatterns_of_sorted imageOrdered).symm
    _ = _ := sortPatterns_eq_of_perm ((sortOccurrences_perm occurrences).map SourceOccurrence.value)

/-- Sorting preserves every source tag and address, including duplicates in
value. This theorem does not identify operational receipt keys. -/
theorem sortOccurrences_addresses (occurrences : List SourceOccurrence) :
    ((sortOccurrences occurrences).map SourceOccurrence.address).Perm
      (occurrences.map SourceOccurrence.address) :=
  (sortOccurrences_perm occurrences).map SourceOccurrence.address


/-- Removing source units commutes with the physical child traversal, and
wrapping a source zipper leaves its value unchanged. -/
theorem componentOccurrences_bag (unitLabel : String) (elements : List Pattern) :
    componentOccurrences unitLabel (.collection .hashBag elements none) =
      elements.zipIdx.flatMap (fun pair =>
        (componentOccurrences unitLabel pair.1).map (SourceOccurrence.wrap elements pair.2)) := by
  rw [componentOccurrences, sourceOccurrences_bag, List.filter_flatMap]
  apply List.flatMap_congr
  intro pair _
  rw [List.filter_map]
  rfl

private theorem flatMap_zipIdx_fst {α β : Type} (items : List α) (f : α → List β) :
    items.zipIdx.flatMap (fun pair => f pair.1) = items.flatMap f := by
  rw [← List.flatMap_map (f := Prod.fst) (g := f), List.zipIdx_map_fst]

private theorem bagContents_flatMap (unitLabel : String) (elements : List Pattern) :
    elements.flatMap (fun element => bagContents unitLabel [normalForm (some unitLabel) element]) =
      bagContents unitLabel (elements.map (normalForm (some unitLabel))) := by
  simp only [bagContents, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    List.flatMap_map, List.filter_flatMap]

private theorem normalForm_nonbag {unitLabel : String} {source : Pattern}
    (notBag : ¬ IsBagNode source) : ¬ IsBagNode (normalForm (some unitLabel) source) := by
  cases source with
  | collection kind elements rest => cases kind <;> cases rest <;> simp_all [IsBagNode, normalForm]
  | _ => simp_all [IsBagNode, normalForm]

/-- Erasing source tags recovers exactly the multiset of existing normalized
components. Flattening is not allowed to erase duplicate source occurrences. -/
theorem componentOccurrences_values (unitLabel : String) :
    ∀ source, ((componentOccurrences unitLabel source).map SourceOccurrence.value).Perm
      (bagContents unitLabel [normalForm (some unitLabel) source])
  | source => by
    by_cases isBag : IsBagNode source
    · obtain ⟨elements, rfl⟩ := isBag
      rw [componentOccurrences_bag, List.map_flatMap, normalForm_bag_contents]
      have transformed := List.Perm.flatMap_left elements.zipIdx
        (f := fun pair => ((componentOccurrences unitLabel pair.1).map
          (SourceOccurrence.wrap elements pair.2)).map SourceOccurrence.value)
        (g := fun pair => bagContents unitLabel [normalForm (some unitLabel) pair.1])
        (fun pair selected => by
          have inside := List.mem_of_getElem? (List.mk_mem_zipIdx_iff_getElem?.mp selected)
          simpa only [List.map_map, SourceOccurrence.wrap, Function.comp_def] using
            componentOccurrences_values unitLabel pair.1)
      apply transformed.trans
      rw [flatMap_zipIdx_fst elements (fun element =>
        bagContents unitLabel [normalForm (some unitLabel) element]), bagContents_flatMap]
      exact (sortPatterns_perm _).symm
    · have normalizedNotBag := normalForm_nonbag (unitLabel := unitLabel) isBag
      rw [componentOccurrences, sourceOccurrences_nonbag isBag]
      rw [bagContents]
      simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
      rw [splice_of_not_bag normalizedNotBag]
      simp only [SourceOccurrence.leaf, List.filter_cons, List.filter_nil]
      split <;> simp_all
termination_by source => sizeOf source

private theorem rootContents_sorted {unitLabel : String} {focus : Pattern}
    (normal : RootNormal unitLabel focus) :
    sortPatterns (bagContents unitLabel [focus]) = bagContents unitLabel [focus] := by
  by_cases isBag : IsBagNode focus
  · obtain ⟨elements, rfl⟩ := isBag
    obtain ⟨sorted, _, plain⟩ := normal elements rfl
    have contents : bagContents unitLabel [.collection .hashBag elements none] = elements := by
      simp only [bagContents, List.flatMap_cons, List.flatMap_nil, List.append_nil, splice_bag]
      apply List.filter_eq_self.mpr
      intro component member
      simpa using (plain component member).1
    rw [contents, sorted]
  · by_cases isUnit : focus = .apply unitLabel []
    · subst focus
      simp [bagContents, splice]
    · simp [bagContents, splice_of_not_bag isBag, isUnit]

/-- Sorting complete tags yields the exact existing canonical component
list, with multiplicity; it is not a second value normalizer. -/
theorem normalizedOccurrences_values (unitLabel : String) (source : Pattern) :
    (normalizedOccurrences unitLabel source).map SourceOccurrence.value =
      bagContents unitLabel [normalForm (some unitLabel) source] := by
  rw [normalizedOccurrences, sortOccurrences_values,
    sortPatterns_eq_of_perm (componentOccurrences_values unitLabel source),
    rootContents_sorted (rootNormal_normalForm unitLabel source)]

/-- Every sorted component still has a different physical source address. -/
theorem normalizedOccurrences_distinct (unitLabel : String) (source : Pattern) :
    ((normalizedOccurrences unitLabel source).map SourceOccurrence.address).Nodup := by
  apply (sortOccurrences_addresses (componentOccurrences unitLabel source)).nodup_iff.mpr
  apply List.pairwise_map.mpr
  exact (sourceOccurrences_distinct unitLabel source).filter _

/-- The sorted physical components and actual source-unit administration
partition the original occurrence account without adding a source leaf. -/
theorem occurrence_account (unitLabel : String) (source : Pattern) :
    (normalizedOccurrences unitLabel source ++ unitOccurrences unitLabel source).Perm
      (sourceOccurrences unitLabel source) := by
  apply ((sortOccurrences_perm (componentOccurrences unitLabel source)).append_right
    (unitOccurrences unitLabel source)).trans
  have complement : (fun occurrence : SourceOccurrence => !decide (occurrence.value ≠ .apply unitLabel [])) =
      (fun occurrence => decide (occurrence.value = .apply unitLabel [])) := by
    funext occurrence
    by_cases same : occurrence.value = .apply unitLabel [] <;> simp [same]
  simpa only [componentOccurrences, unitOccurrences, complement] using
    List.filter_append_perm (fun occurrence : SourceOccurrence =>
      decide (occurrence.value ≠ .apply unitLabel [])) (sourceOccurrences unitLabel source)


/-- Every emitted component index has its own source address. Two equal
values at different indices cannot reuse one physical source occurrence. -/
theorem normalizedOccurrences_index_injective (unitLabel : String) (source : Pattern)
    {firstIndex secondIndex : Nat}
    (firstWithin : firstIndex < (normalizedOccurrences unitLabel source).length)
    (secondWithin : secondIndex < (normalizedOccurrences unitLabel source).length) :
    (normalizedOccurrences unitLabel source)[firstIndex].address =
      (normalizedOccurrences unitLabel source)[secondIndex].address ↔ firstIndex = secondIndex := by
  constructor
  · intro same
    have sameAt : ((normalizedOccurrences unitLabel source).map SourceOccurrence.address)[firstIndex]'(by simpa) =
        ((normalizedOccurrences unitLabel source).map SourceOccurrence.address)[secondIndex]'(by simpa) := by
      simpa only [List.getElem_map] using same
    exact (normalizedOccurrences_distinct unitLabel source).getElem_inj_iff.mp sameAt
  · intro same
    subst secondIndex
    rfl

/-- The component count and every value multiplicity are those of the
existing normal-form component list, with no identification of equal tags. -/
theorem normalizedOccurrences_counts (unitLabel : String) (source : Pattern) :
    (normalizedOccurrences unitLabel source).length =
      (bagContents unitLabel [normalForm (some unitLabel) source]).length ∧
      ∀ component, ((normalizedOccurrences unitLabel source).map SourceOccurrence.value).count component =
        (bagContents unitLabel [normalForm (some unitLabel) source]).count component := by
  have values := normalizedOccurrences_values unitLabel source
  exact ⟨by simpa only [List.length_map] using congrArg List.length values,
    fun component => congrArg (List.count component) values⟩

/-- Actual source units remain in the administrative account. They do not
appear as physical components just because matching can insert a unit view. -/
theorem unitOccurrences_value {unitLabel : String} {source : Pattern} {occurrence : SourceOccurrence}
    (member : occurrence ∈ unitOccurrences unitLabel source) : occurrence.value = .apply unitLabel [] :=
  of_decide_eq_true (List.mem_filter.mp member).2

theorem normalizedOccurrences_nonunit {unitLabel : String} {source : Pattern} {occurrence : SourceOccurrence}
    (member : occurrence ∈ normalizedOccurrences unitLabel source) : occurrence.value ≠ .apply unitLabel [] := by
  have before := (sortOccurrences_perm (componentOccurrences unitLabel source)).mem_iff.mp member
  exact of_decide_eq_true (List.mem_filter.mp before).2

/-- Sorted source records retain original and normalized typing, exact
zipper readback and unchanged local scope. This is not a firing certificate. -/
theorem normalizedOccurrences_sound {language : LanguageDef} {bag : GrammarRule} {unitLabel : String}
    (laws : BareBagTheory {language with equations := []} bag (some unitLabel))
    {free : FreeTypeContext} {bound : List TypeExpr} {source : Pattern}
    (good : Admissible language free bound (.base bag.category) source)
    {occurrence : SourceOccurrence} (member : occurrence ∈ normalizedOccurrences unitLabel source) :
    Admissible language free bound (.base bag.category) occurrence.original ∧
      Admissible language free bound (.base bag.category) occurrence.value ∧
      occurrence.context.fill occurrence.original = source ∧
      occurrence.value = normalForm (some unitLabel) occurrence.original ∧
      contextAddress occurrence.context = occurrence.address ∧
      ∀ replacement, HasType language free bound replacement (.base bag.category) →
        HasType language free bound (occurrence.context.fill replacement) (.base bag.category) := by
  have before := (sortOccurrences_perm (componentOccurrences unitLabel source)).mem_iff.mp member
  obtain ⟨originalGood, fills, image, address, rebuild⟩ :=
    sourceOccurrences_sound laws source good occurrence (List.mem_filter.mp before).1
  have valueGood := normalized_admissible laws defaultBasePremises originalGood rfl
  rw [← image] at valueGood
  exact ⟨originalGood, valueGood, fills, image, address, rebuild⟩

/-- Source occurrences are conserved exactly when source-unit administration
is included. No derivation identity is selected by this accounting theorem. -/
theorem occurrence_account_length (unitLabel : String) (source : Pattern) :
    (normalizedOccurrences unitLabel source).length + (unitOccurrences unitLabel source).length =
      (sourceOccurrences unitLabel source).length := by
  simpa only [List.length_append] using (occurrence_account unitLabel source).length_eq



/-- Source records stop at physical non-bag leaves. Their stored value is
read from that original syntax by the existing normalizer. -/
theorem sourceOccurrences_leaf_value (unitLabel : String) :
    ∀ source occurrence, occurrence ∈ sourceOccurrences unitLabel source →
      ¬ IsBagNode occurrence.original ∧ occurrence.value = normalForm (some unitLabel) occurrence.original
  | source, occurrence, member => by
    by_cases isBag : IsBagNode source
    · obtain ⟨elements, rfl⟩ := isBag
      rw [sourceOccurrences_bag] at member
      obtain ⟨⟨element,index⟩, selected, mapped⟩ := List.mem_flatMap.mp member
      obtain ⟨inner, inside, rfl⟩ := List.mem_map.mp mapped
      have elementMember := List.mem_of_getElem? (List.mk_mem_zipIdx_iff_getElem?.mp selected)
      exact sourceOccurrences_leaf_value unitLabel element inner inside
    · rw [sourceOccurrences_nonbag isBag] at member
      obtain rfl := List.mem_singleton.mp member
      exact ⟨isBag,rfl⟩
termination_by source => sizeOf source

private theorem original_unit_of_nonbag {unitLabel : String} {source : Pattern}
    (notBag : ¬ IsBagNode source)
    (image : normalForm (some unitLabel) source = .apply unitLabel []) : source = .apply unitLabel [] := by
  cases source with
  | apply constructor arguments => cases arguments <;> simp_all [normalForm, normalFormList]
  | collection kind elements rest => cases kind <;> cases rest <;> simp_all [normalForm, IsBagNode]
  | _ => simp_all [normalForm]

/-- The source-unit administration consists of actual original unit leaves,
not source occurrences created to justify a virtual matching representative. -/
theorem unitOccurrences_original {unitLabel : String} {source : Pattern} {occurrence : SourceOccurrence}
    (member : occurrence ∈ unitOccurrences unitLabel source) : occurrence.original = .apply unitLabel [] := by
  obtain ⟨leaf, image⟩ := sourceOccurrences_leaf_value unitLabel source occurrence (List.mem_filter.mp member).1
  apply original_unit_of_nonbag leaf
  exact image.symm.trans (unitOccurrences_value member)

/-- Equal values preserve their two physical source addresses after sorting. -/
theorem duplicate_occurrence_control :
    let source := Pattern.collection .hashBag [.fvar "a",.fvar "a"] none
    (normalizedOccurrences "unit" source).map SourceOccurrence.value = [.fvar "a",.fvar "a"] ∧
      (normalizedOccurrences "unit" source).map SourceOccurrence.address = [[0],[1]] := by cbv

/-- A sorting permutation moves the source tags together with their values. -/
theorem reordered_occurrence_control :
    let source := Pattern.collection .hashBag [.fvar "b",.fvar "a"] none
    (normalizedOccurrences "unit" source).map SourceOccurrence.value = [.fvar "a",.fvar "b"] ∧
      (normalizedOccurrences "unit" source).map SourceOccurrence.address = [[1],[0]] := by cbv

/-- Flattening nested equal values keeps their original paths; the actual
source unit is present only in the separate administrative account. -/
theorem nested_duplicate_unit_control :
    let source := Pattern.collection .hashBag
      [.apply "unit" [], .collection .hashBag [.fvar "a",.fvar "a"] none] none
    (normalizedOccurrences "unit" source).map SourceOccurrence.address = [[1,0],[1,1]] ∧
      (unitOccurrences "unit" source).map SourceOccurrence.address = [[0]] ∧
      (sourceOccurrences "unit" source).length = 3 := by cbv

/-- Empty and unit presentations have equal values but different physical
source accounts. Normalization cannot fabricate a source leaf for the empty
presentation's virtual unit. -/
theorem empty_unit_origin_separator :
    normalForm (some "unit") (.collection .hashBag [] none) = .apply "unit" [] ∧
      sourceOccurrences "unit" (.collection .hashBag [] none) = [] ∧
      normalizedOccurrences "unit" (.apply "unit" []) = [] ∧
      (unitOccurrences "unit" (.apply "unit" [])).length = 1 := by cbv

/-- The physical account does not descend through a constructor boundary. -/
theorem constructor_occurrence_boundary (unitLabel constructorLabel : String) (arguments : List Pattern) :
    sourceOccurrences unitLabel (.apply constructorLabel arguments) =
      [SourceOccurrence.leaf unitLabel (.apply constructorLabel arguments)] :=
  sourceOccurrences_nonbag (by simp [IsBagNode])

#print axioms sourceOccurrences_distinct
#print axioms sourceOccurrences_sound
#print axioms sourceOccurrences_bag
#print axioms sourceOccurrences_nonbag
#print axioms sortOccurrences_perm
#print axioms sortOccurrences_values
#print axioms sortOccurrences_addresses
#print axioms componentOccurrences_bag
#print axioms componentOccurrences_values
#print axioms normalizedOccurrences_values
#print axioms normalizedOccurrences_distinct
#print axioms occurrence_account
#print axioms normalizedOccurrences_index_injective
#print axioms normalizedOccurrences_counts
#print axioms unitOccurrences_value
#print axioms normalizedOccurrences_nonunit
#print axioms normalizedOccurrences_sound
#print axioms occurrence_account_length
#print axioms duplicate_occurrence_control
#print axioms reordered_occurrence_control
#print axioms nested_duplicate_unit_control
#print axioms empty_unit_origin_separator
#print axioms constructor_occurrence_boundary
#print axioms sourceOccurrences_leaf_value
#print axioms unitOccurrences_original

end Mettapedia.GSLT.LanguageDef.BagNormalForm.WithAuthoredEquations.AlgebraFocus

namespace Mettapedia.GSLT.LanguageDef.BagNormalForm.WithAuthoredEquations

open Mettapedia.OSLF.MeTTaIL Syntax ContextualStep Match
open Mettapedia.GSLT.LanguageDef.WellSorted EquationSemantics

/-- The existing source-derived normalizer is a normalizer for the original
reference-equation hub on the same admissible fibre. Directed rule premises
need no additional restriction when equation rows are unconditional. -/
theorem reference_sourceNormalizer {language : LanguageDef} {bag : GrammarRule} {unit : Option String}
    (laws : BareBagTheory {language with equations := []} bag unit)
    (rows : ∀ row ∈ language.equations,
      row.premises = [] ∧ RowPattern row.left ∧ RowPattern row.right ∧
        ∀ bindings, normalForm unit (applyBindings bindings row.left) =
          normalForm unit (applyBindings bindings row.right))
    (aligned : ReferenceStep.EquationsAligned language) (relEnv : Engine.RelationEnv)
    (free : FreeTypeContext) (bound : List TypeExpr) (type : TypeExpr)
    (collectionless : collectionFree type = true) :
    Complete.Coherence.Normalizer
      (fun (first second : {pattern // Admissible language free bound type pattern}) =>
        ReferenceStep.EquationStep relEnv language first.1 second.1)
      (normalizeSource laws (engineBasePremises relEnv) free bound type collectionless) := by
  have unconditional : ReferenceStep.UnconditionalEquations language := fun row member => (rows row member).1
  have original := sourceNormalizer laws rows (engineBasePremises relEnv) free bound type collectionless
  refine ⟨?_,?_⟩
  · intro subject
    exact Relation.EqvGen.mono
      (fun _ _ step => (ReferenceStep.equationStep_iff_unconditional unconditional aligned).mp step)
      _ _ (original.sound subject)
  · intro first second step
    exact original.canonical first second
      ((ReferenceStep.equationStep_iff_unconditional unconditional aligned).mpr step)

/-- Soundness and reflection for the actual unrestricted reference
Equivalence at admissible endpoints, retaining the authored equation rows. -/
theorem reference_equivalent_iff_normalForm_eq {language : LanguageDef} {bag : GrammarRule} {unit : Option String}
    (laws : BareBagTheory {language with equations := []} bag unit)
    (rows : ∀ row ∈ language.equations,
      row.premises = [] ∧ RowPattern row.left ∧ RowPattern row.right ∧
        ∀ bindings, normalForm unit (applyBindings bindings row.left) =
          normalForm unit (applyBindings bindings row.right))
    (aligned : ReferenceStep.EquationsAligned language) (relEnv : Engine.RelationEnv)
    {free : FreeTypeContext} {bound : List TypeExpr} {type : TypeExpr} {left right : Pattern}
    (leftGood : Admissible language free bound type left) (rightGood : Admissible language free bound type right)
    (collectionless : collectionFree type = true) :
    ReferenceStep.Equivalent relEnv language left right ↔ normalForm unit left = normalForm unit right :=
  (ReferenceStep.equivalent_iff_unconditional (fun row member => (rows row member).1) aligned).symm.trans
    (source_equationEquiv_iff_normalForm_eq laws rows (engineBasePremises relEnv)
      leftGood rightGood collectionless)

#print axioms reference_sourceNormalizer
#print axioms reference_equivalent_iff_normalForm_eq

end Mettapedia.GSLT.LanguageDef.BagNormalForm.WithAuthoredEquations

namespace Mettapedia.GSLT.LanguageDef.BagNormalForm.WithAuthoredEquations.AlgebraFocus

open Mettapedia.OSLF.MeTTaIL Syntax ContextualStep Match DerivedContexts GeneralTypedSites
open Mettapedia.GSLT.LanguageDef.WellSorted EquationSemantics

/-- The existing independent bag match recovers an actual reference-source
presentation. This is sound recovery, not completeness of a component view
for unit-sensitive schemas. -/
theorem recover_reference_presentation {language : LanguageDef} {bag : GrammarRule} {unitLabel : String}
    (laws : BareBagTheory {language with equations := []} bag (some unitLabel))
    (unconditional : ReferenceStep.UnconditionalEquations language)
    (aligned : ReferenceStep.EquationsAligned language) (relEnv : Engine.RelationEnv)
    {free : FreeTypeContext} {bound : List TypeExpr} {source : Pattern}
    (good : Admissible language free bound (.base bag.category) source)
    {schemas : List Pattern} {rest : Option String} {bindings : Bindings}
    (matched : MatchSpec.MatchBagRel schemas rest .hashBag
      (bagContents unitLabel [normalForm (some unitLabel) source]) bindings) :
    ∃ representative,ReferenceStep.Equivalent relEnv language source representative ∧
      Admissible language free bound (.base bag.category) representative ∧
      bindings ∈ matchPattern (.collection .hashBag schemas rest) representative := by
  obtain ⟨representative,converted,typed,ordinary⟩ :=
    recover_representative laws (engineBasePremises relEnv) good matched
  exact ⟨representative,(ReferenceStep.equivalent_iff_unconditional unconditional aligned).mp converted,
    typed,MatchSpec.matchRel_complete ordinary⟩

/-- A normalized component keeps its actual typed source leaf and zipper.
Its value is related to that leaf by original reference equations, rather
than by a fresh semantic relation or an invented occurrence. -/
theorem normalizedOccurrence_reference_source {language : LanguageDef} {bag : GrammarRule} {unitLabel : String}
    (laws : BareBagTheory {language with equations := []} bag (some unitLabel))
    (unconditional : ReferenceStep.UnconditionalEquations language)
    (aligned : ReferenceStep.EquationsAligned language) (relEnv : Engine.RelationEnv)
    {free : FreeTypeContext} {bound : List TypeExpr} {source : Pattern}
    (good : Admissible language free bound (.base bag.category) source)
    {occurrence : SourceOccurrence} (member : occurrence ∈ normalizedOccurrences unitLabel source) :
    Admissible language free bound (.base bag.category) occurrence.original ∧
      Admissible language free bound (.base bag.category) occurrence.value ∧
      occurrence.context.fill occurrence.original = source ∧
      ReferenceStep.Equivalent relEnv language occurrence.original occurrence.value ∧
      contextAddress occurrence.context = occurrence.address ∧
      ∀ replacement,HasType language free bound replacement (.base bag.category) →
        HasType language free bound (occurrence.context.fill replacement) (.base bag.category) := by
  obtain ⟨originalGood,valueGood,fills,image,address,rebuild⟩ := normalizedOccurrences_sound laws good member
  have converted := source_equiv_normalForm laws (engineBasePremises relEnv) originalGood rfl
  rw [← image] at converted
  exact ⟨originalGood,valueGood,fills,
    (ReferenceStep.equivalent_iff_unconditional unconditional aligned).mp converted,address,rebuild⟩

/-- Selecting a tagged component and its exact residual earns both ordinary
source matching at an equivalent representative and the selected physical
source occurrence. Equal component values keep their separate tagged indices. -/
theorem tagged_reference_presentation {language : LanguageDef} {bag : GrammarRule} {unitLabel : String}
    (laws : BareBagTheory {language with equations := []} bag (some unitLabel))
    (unconditional : ReferenceStep.UnconditionalEquations language)
    (aligned : ReferenceStep.EquationsAligned language) (relEnv : Engine.RelationEnv)
    {free : FreeTypeContext} {bound : List TypeExpr} {source schema : Pattern}
    (good : Admissible language free bound (.base bag.category) source)
    {index : Nat} {occurrence : SourceOccurrence} {restName : String} {headBindings bindings : Bindings}
    (selected : (normalizedOccurrences unitLabel source)[index]? = some occurrence)
    (head : MatchSpec.MatchRel schema occurrence.value headBindings)
    (merged : mergeBindings headBindings [(restName,.collection .hashBag
      ((bagContents unitLabel [normalForm (some unitLabel) source]).eraseIdx index) none)] = some bindings) :
    ReferenceStep.PresentedMatch (ReferenceStep.equivalentSetoid relEnv language)
        (.collection .hashBag [schema] (some restName)) source bindings ∧
      Admissible language free bound (.base bag.category) occurrence.original ∧
      occurrence.context.fill occurrence.original = source ∧
      ReferenceStep.Equivalent relEnv language occurrence.original occurrence.value ∧
      contextAddress occurrence.context = occurrence.address := by
  have selectedValue : (bagContents unitLabel [normalForm (some unitLabel) source])[index]? =
      some occurrence.value := by
    rw [← normalizedOccurrences_values,List.getElem?_map,selected]
    rfl
  obtain ⟨within,atPosition⟩ := List.getElem?_eq_some_iff.mp selectedValue
  have headAt : MatchSpec.MatchRel schema (bagContents unitLabel [normalForm (some unitLabel) source])[index]
      headBindings := by rw [atPosition]; exact head
  have matched : MatchSpec.MatchBagRel [schema] (some restName) .hashBag
      (bagContents unitLabel [normalForm (some unitLabel) source]) bindings :=
    .cons index within headAt .nilRest merged
  obtain ⟨representative,converted,_,ordinary⟩ :=
    recover_reference_presentation laws unconditional aligned relEnv good matched
  obtain ⟨originalGood,_,fills,originalEquivalent,address,_⟩ :=
    normalizedOccurrence_reference_source laws unconditional aligned relEnv good (List.mem_of_getElem? selected)
  exact ⟨⟨representative,converted,ordinary⟩,originalGood,fills,originalEquivalent,address⟩

/-- A genuine rule witness at the existing algebra view transports to a
source step modulo the actual equations, retaining its original rule index,
initial bindings and complete premise witness list. -/
theorem stepModulo_of_reference_view_rule {language : LanguageDef} {bag : GrammarRule} {unitLabel : String}
    (laws : BareBagTheory {language with equations := []} bag (some unitLabel))
    (unconditional : ReferenceStep.UnconditionalEquations language)
    (aligned : ReferenceStep.EquationsAligned language) (relEnv : Engine.RelationEnv)
    {free : FreeTypeContext} {bound : List TypeExpr} {source target : Pattern}
    (good : Admissible language free bound (.base bag.category) source)
    {index : Nat} {initial : Bindings} {witnesses : List ReferenceStep.Witness}
    (fired : ReferenceStep.StepValid relEnv language (view unitLabel (normalForm (some unitLabel) source))
      (.rule index initial witnesses) target) :
    ReferenceStep.StepModulo relEnv language source target ∧
      ∃ representative,ReferenceStep.Equivalent relEnv language source representative ∧
        ReferenceStep.StepValid relEnv language representative (.rule index initial witnesses) target := by
  have converted := (ReferenceStep.equivalent_iff_unconditional unconditional aligned).mp
    (normalized_view_equivalent laws (engineBasePremises relEnv) good)
  exact ⟨⟨_,target,converted,⟨.rule index initial witnesses,fired⟩,.refl _⟩,
    _,converted,fired⟩

#print axioms recover_reference_presentation
#print axioms normalizedOccurrence_reference_source
#print axioms tagged_reference_presentation
#print axioms stepModulo_of_reference_view_rule

end Mettapedia.GSLT.LanguageDef.BagNormalForm.WithAuthoredEquations.AlgebraFocus

namespace Mettapedia.GSLT.LanguageDef.BagNormalForm.WithAuthoredEquations.AlgebraFocus

open Mettapedia.OSLF.MeTTaIL Syntax ContextualStep Match MatchSpec
open Mettapedia.GSLT.LanguageDef.WellSorted EquationSemantics

/-- One actual unit-law expansion of the algebra view. Its leading unit is
administrative; it does not name or consume a physical source component. -/
def unitExpansion (unitLabel : String) (focus : Pattern) : Pattern :=
  .collection .hashBag (.apply unitLabel [] :: bagContents unitLabel [focus]) none

/-- The selected law supplies a genuine nullary unit of the homogeneous
base sort; no new source typing declaration is postulated. -/
theorem declared_unit_admissible {language : LanguageDef} {bag : GrammarRule} {unitLabel : String}
    (laws : BareBagTheory {language with equations := []} bag (some unitLabel))
    (base : BasePremiseEvaluator) (free : FreeTypeContext) (bound : List TypeExpr) :
    Admissible language free bound (.base bag.category) (.apply unitLabel []) := by
  have emptyTyped : HasType {language with equations := []} free bound
      (.collection .hashBag [] none) (.base bag.category) := bag_hasType laws (.nil _ _)
  have emptyGood : Admissible language free bound (.base bag.category) (.collection .hashBag [] none) :=
    ⟨grammar_hasType (source := {language with equations := []}) (target := language) rfl emptyTyped,rfl,rfl⟩
  simpa [normalForm,normalizeBag,bagContents,PatternCode.sortPatterns,collapse] using
    normalized_admissible laws base emptyGood rfl

/-- The entire component row is collection data. A zero-component selection
keeps this outer carrier even when the row is empty or a singleton. -/
theorem contents_data_admissible {language : LanguageDef} {bag : GrammarRule} {unitLabel : String}
    (laws : BareBagTheory {language with equations := []} bag (some unitLabel))
    {free : FreeTypeContext} {bound : List TypeExpr} {focus : Pattern}
    (good : Admissible language free bound (.base bag.category) focus) :
    Admissible language free bound (.collection .hashBag (.base bag.category)) (view unitLabel focus) := by
  have viewGood := view_admissible laws good
  have comparisonGood := grammar_admissible (source := language)
    (target := {language with equations := []}) rfl viewGood
  obtain ⟨_,_,elementsTyped⟩ := bag_typing laws comparisonGood.typed rfl
  exact ⟨.collection (grammar_elements (source := {language with equations := []})
    (target := language) rfl elementsTyped),viewGood.canonical,viewGood.object⟩

theorem unitExpansion_admissible {language : LanguageDef} {bag : GrammarRule} {unitLabel : String}
    (laws : BareBagTheory {language with equations := []} bag (some unitLabel))
    (base : BasePremiseEvaluator) {free : FreeTypeContext} {bound : List TypeExpr} {focus : Pattern}
    (good : Admissible language free bound (.base bag.category) focus) :
    Admissible language free bound (.base bag.category) (unitExpansion unitLabel focus) := by
  have unitGood := declared_unit_admissible laws base free bound
  have viewGood := view_admissible laws good
  have comparisonGood := grammar_admissible (source := language)
    (target := {language with equations := []}) rfl viewGood
  obtain ⟨_,_,elementsTyped⟩ := bag_typing laws comparisonGood.typed rfl
  refine ⟨grammar_hasType (source := {language with equations := []}) (target := language) rfl
    (bag_hasType laws (.cons (grammar_hasType (source := language)
      (target := {language with equations := []}) rfl unitGood.typed) elementsTyped)),?_,?_⟩
  · simpa only [unitExpansion,view,Pattern.hasCanonicalBinderMetadata,
      Pattern.hasCanonicalBinderMetadataList,Bool.true_and] using viewGood.canonical
  · simpa only [unitExpansion,view,isObjectPattern,isObjectPatternList,Bool.true_and] using viewGood.object

/-- A virtual-unit match is supported by the actual declared unit equation.
The source path retains all authored rows; no alternative equivalence or
normalization-only firing assumption is introduced. -/
theorem unitExpansion_equivalent {language : LanguageDef} {bag : GrammarRule} {unitLabel : String}
    (laws : BareBagTheory {language with equations := []} bag (some unitLabel))
    (base : BasePremiseEvaluator) {free : FreeTypeContext} {bound : List TypeExpr} {source : Pattern}
    (good : Admissible language free bound (.base bag.category) source) :
    EquationEquiv base language source (unitExpansion unitLabel (normalForm (some unitLabel) source)) := by
  have normalizedGood := normalized_admissible laws base good rfl
  have expandedGood := grammar_admissible (source := language)
    (target := {language with equations := []}) rfl (unitExpansion_admissible laws base normalizedGood)
  have removed : DerivedInstance {language with equations := []}
      (unitExpansion unitLabel (normalForm (some unitLabel) source))
      (view unitLabel (normalForm (some unitLabel) source)) := by
    change DerivedInstance {language with equations := []}
      (.collection .hashBag ([] ++ .apply unitLabel [] :: bagContents unitLabel [normalForm (some unitLabel) source]) none)
      (.collection .hashBag ([] ++ bagContents unitLabel [normalForm (some unitLabel) source]) none)
    exact .unitElim laws.bagAlgebraRule rfl (sortedAt_of_admissible laws expandedGood rfl)
  have comparisonPath := path_of_derived (base := base) removed
  have sourcePath := comparison_path (language := language) comparisonPath
  exact .trans _ _ _ (normalized_view_equivalent laws base good)
    (Relation.EqvGen.symm _ _ (Relation.EqvGen.reflTransGen_le_eqvGen _ _ _ sourcePath))

/-- Selecting the virtual unit uses the ordinary matcher at an equivalent
source presentation. The residual contains every live source component in
its existing tagged order and retains its collection-data type. -/
theorem zero_component_reference_presentation {language : LanguageDef} {bag : GrammarRule} {unitLabel : String}
    (laws : BareBagTheory {language with equations := []} bag (some unitLabel))
    (unconditional : ReferenceStep.UnconditionalEquations language)
    (aligned : ReferenceStep.EquationsAligned language) (relEnv : Engine.RelationEnv)
    {free : FreeTypeContext} {bound : List TypeExpr} {source schema : Pattern}
    (good : Admissible language free bound (.base bag.category) source)
    {restName : String} {headBindings bindings : Bindings}
    (head : MatchRel schema (.apply unitLabel []) headBindings)
    (merged : mergeBindings headBindings [(restName,view unitLabel (normalForm (some unitLabel) source))] =
      some bindings) :
    ReferenceStep.PresentedMatch (ReferenceStep.equivalentSetoid relEnv language)
        (.collection .hashBag [schema] (some restName)) source bindings ∧
      Admissible language free bound (.collection .hashBag (.base bag.category))
        (view unitLabel (normalForm (some unitLabel) source)) ∧
      bagContents unitLabel [normalForm (some unitLabel) source] =
        (normalizedOccurrences unitLabel source).map SourceOccurrence.value := by
  have sourceEquivalent := (ReferenceStep.equivalent_iff_unconditional unconditional aligned).mp
    (unitExpansion_equivalent laws (engineBasePremises relEnv) good)
  have ordinary : MatchRel (.collection .hashBag [schema] (some restName))
      (unitExpansion unitLabel (normalForm (some unitLabel) source)) bindings :=
    .collection (by decide) (.cons 0 (by simp) head .nilRest merged)
  exact ⟨⟨_,sourceEquivalent,matchRel_complete ordinary⟩,
    contents_data_admissible laws (normalized_admissible laws (engineBasePremises relEnv) good rfl),
    (normalizedOccurrences_values unitLabel source).symm⟩

#print axioms declared_unit_admissible
#print axioms contents_data_admissible
#print axioms unitExpansion_admissible
#print axioms unitExpansion_equivalent
#print axioms zero_component_reference_presentation

end Mettapedia.GSLT.LanguageDef.BagNormalForm.WithAuthoredEquations.AlgebraFocus

namespace Mettapedia.GSLT.LanguageDef.BagNormalForm.WithAuthoredEquations.AlgebraFocus

open Mettapedia.OSLF.MeTTaIL Syntax ContextualStep Match MatchSpec PatternTreeSize GeneralTypedSites
open Mettapedia.GSLT.LanguageDef.WellSorted EquationSemantics


/-- Finite ordered splits retain the source records themselves. The empty
selection is included; its algebra value is an administrative unit. -/
def occurrenceSplits {α : Type} (occurrences : List α) : List (List α × List α) :=
  occurrences.permutations.flatMap fun reordered =>
    (List.range (occurrences.length + 1)).map fun cut =>
      (reordered.take cut,reordered.drop cut)

/-- Every split is included exactly at the level of permutation and
multiplicity. Equal-valued source occurrences remain distinct records. -/
theorem mem_occurrenceSplits {α : Type} {occurrences selected residual : List α} :
    (selected,residual) ∈ occurrenceSplits occurrences ↔
      (selected ++ residual).Perm occurrences := by
  constructor
  · intro member
    obtain ⟨reordered,inPermutations,inside⟩ := List.mem_flatMap.mp member
    obtain ⟨cut,_,equal⟩ := List.mem_map.mp inside
    obtain ⟨rfl,rfl⟩ := Prod.mk.inj equal
    simpa only [List.take_append_drop] using List.mem_permutations.mp inPermutations
  · intro permutation
    apply List.mem_flatMap.mpr
    refine ⟨selected ++ residual,List.mem_permutations.mpr permutation,?_⟩
    apply List.mem_map.mpr
    refine ⟨selected.length,List.mem_range.mpr ?_,?_⟩
    · have lengths := permutation.length_eq
      simp only [List.length_append] at lengths
      omega
    · simp

/-- Allocate a fixed number of groups and a residual. Empty groups are
represented without a physical source occurrence. -/
def groupedOccurrences {α : Type} : Nat → List α → List (List (List α) × List α)
  | 0,occurrences => occurrences.permutations.map fun reordered => ([],reordered)
  | count + 1,occurrences =>
      (occurrenceSplits occurrences).flatMap fun split =>
        (groupedOccurrences count split.2).map fun remaining =>
          (split.1 :: remaining.1,remaining.2)

/-- Group enumeration covers all finite allocations and conserves the
entire flattened physical occurrence account. -/
theorem mem_groupedOccurrences {α : Type} (count : Nat)
    {occurrences : List α} {groups : List (List α)} {residual : List α} :
    (groups,residual) ∈ groupedOccurrences count occurrences ↔
      groups.length = count ∧ (groups.flatten ++ residual).Perm occurrences := by
  induction count generalizing occurrences groups residual with
  | zero =>
    cases groups with
    | nil => simp [groupedOccurrences,List.mem_permutations]
    | cons head tail => simp [groupedOccurrences]
  | succ count recurse =>
    constructor
    · intro member
      obtain ⟨⟨selected,remaining⟩,splitMember,inside⟩ := List.mem_flatMap.mp member
      obtain ⟨⟨later,last⟩,laterMember,equal⟩ := List.mem_map.mp inside
      obtain ⟨rfl,rfl⟩ := Prod.mk.inj equal
      obtain ⟨lengths,account⟩ := recurse.mp laterMember
      refine ⟨by simpa using lengths,?_⟩
      have laterAccount : ((selected :: later).flatten ++ last).Perm (selected ++ remaining) := by
        simpa only [List.flatten_cons,List.append_assoc] using account.append_left selected
      exact laterAccount.trans (mem_occurrenceSplits.mp splitMember)
    · rintro ⟨lengths,account⟩
      cases groups with
      | nil => simp at lengths
      | cons selected later =>
        apply List.mem_flatMap.mpr
        refine ⟨(selected,later.flatten ++ residual),?_,?_⟩
        · apply mem_occurrenceSplits.mpr
          simpa only [List.flatten_cons,List.append_assoc] using account
        · apply List.mem_map.mpr
          refine ⟨(later,residual),recurse.mpr ⟨by simpa using lengths,.refl _⟩,rfl⟩

/-- A permutation of erased values can be lifted to the original records.
This does not pick one equal-valued source occurrence twice. -/
theorem split_occurrences_of_values {α β : Type} (value : α → β)
    {occurrences : List α} {selected residual : List β}
    (account : (selected ++ residual).Perm (occurrences.map value)) :
    ∃ selectedTags residualTags,
      (selectedTags,residualTags) ∈ occurrenceSplits occurrences ∧
      selectedTags.map value = selected ∧ residualTags.map value = residual := by
  have lifted : ∃ reordered : List α, selected ++ residual = reordered.map value ∧
      reordered.Perm occurrences := by
    change (Relation.Comp (fun (row : List β) (tags : List α) => row = tags.map value)
      List.Perm) (selected ++ residual) occurrences
    rw [List.eq_map_comp_perm]
    exact account
  obtain ⟨reordered,values,permutation⟩ := lifted
  obtain ⟨selectedTags,residualTags,split,first,last⟩ := List.append_eq_map_iff.mp values
  exact ⟨selectedTags,residualTags,mem_occurrenceSplits.mpr (split ▸ permutation),first,last⟩

/-- A well-typed homogeneous component row is both an algebra value and
collection data. This statement does not normalize a data boundary. -/
theorem component_row_admissible {language : LanguageDef} {bag : GrammarRule} {unitLabel : String}
    (laws : BareBagTheory {language with equations := []} bag (some unitLabel))
    {free : FreeTypeContext} {bound : List TypeExpr} {components : List Pattern}
    (each : ∀ component ∈ components,
      Admissible language free bound (.base bag.category) component) :
    Admissible language free bound (.base bag.category) (.collection .hashBag components none) ∧
    Admissible language free bound (.collection .hashBag (.base bag.category))
      (.collection .hashBag components none) := by
  have elementsTyped := elementsHaveType_iff.mpr fun component member => (each component member).typed
  have canonical : Pattern.hasCanonicalBinderMetadataList components = true :=
    hasCanonicalBinderMetadataList_iff.mpr fun component member => (each component member).canonical
  have objects : isObjectPatternList components = true :=
    isObjectPatternList_iff.mpr fun component member => (each component member).object
  exact ⟨⟨grammar_hasType (source := {language with equations := []}) (target := language) rfl
      (bag_hasType laws (grammar_elements (source := language)
        (target := {language with equations := []}) rfl elementsTyped)),canonical,by simpa [isObjectPattern] using objects⟩,
    ⟨.collection elementsTyped,canonical,by simpa [isObjectPattern] using objects⟩⟩

/-- A selected group is the existing algebra collapse of its assigned
components. In particular an empty group is the declared unit, not a token. -/
theorem collapsed_row_admissible {language : LanguageDef} {bag : GrammarRule} {unitLabel : String}
    (laws : BareBagTheory {language with equations := []} bag (some unitLabel))
    (base : BasePremiseEvaluator) {free : FreeTypeContext} {bound : List TypeExpr}
    {components : List Pattern}
    (each : ∀ component ∈ components,
      Admissible language free bound (.base bag.category) component) :
    Admissible language free bound (.base bag.category) (collapse unitLabel components) := by
  cases components with
  | nil => exact declared_unit_admissible laws base free bound
  | cons first rest =>
    cases rest with
    | nil => exact each first (by simp)
    | cons second later => exact (component_row_admissible laws each).1

/-- Components assigned to any group retain the actual source typing,
normal value, and original zipper. -/
theorem grouped_occurrence_origins {language : LanguageDef} {bag : GrammarRule} {unitLabel : String}
    (laws : BareBagTheory {language with equations := []} bag (some unitLabel))
    {free : FreeTypeContext} {bound : List TypeExpr} {source : Pattern}
    (good : Admissible language free bound (.base bag.category) source)
    {count : Nat} {groups : List (List SourceOccurrence)} {residual : List SourceOccurrence}
    (allocation : (groups,residual) ∈ groupedOccurrences count (normalizedOccurrences unitLabel source)) :
    (groups.flatten ++ residual).Pairwise (fun first second => first.address ≠ second.address) ∧
      ∀ occurrence ∈ groups.flatten ++ residual,
        Admissible language free bound (.base bag.category) occurrence.original ∧
        Admissible language free bound (.base bag.category) occurrence.value ∧
        occurrence.context.fill occurrence.original = source ∧
        normalForm (some unitLabel) occurrence.original = occurrence.value ∧
        contextAddress occurrence.context = occurrence.address := by
  have account := (mem_groupedOccurrences count).mp allocation |>.2
  constructor
  · apply List.pairwise_map.mp
    exact (account.map SourceOccurrence.address).nodup_iff.mpr
      (normalizedOccurrences_distinct unitLabel source)
  · intro occurrence member
    have original := normalizedOccurrences_sound laws good (account.mem_iff.mp member)
    exact ⟨original.1,original.2.1,original.2.2.1,original.2.2.2.1.symm,original.2.2.2.2.1⟩

#print axioms mem_occurrenceSplits
#print axioms mem_groupedOccurrences
#print axioms split_occurrences_of_values
#print axioms component_row_admissible
#print axioms collapsed_row_admissible
#print axioms grouped_occurrence_origins




/-- Group boundaries are source presentations, not collection-data
normalizations. The residual retains its ordinary outer bag carrier. -/
def groupedView (unitLabel : String) (groups : List (List SourceOccurrence))
    (residual : List SourceOccurrence) : Pattern :=
  .collection .hashBag
    (groups.map (fun group => collapse unitLabel (group.map SourceOccurrence.value)) ++
      residual.map SourceOccurrence.value) none

/-- A physical component has neither a bag boundary nor the declared unit
at its normalized root. -/
theorem normalizedOccurrence_plain {unitLabel : String} {source : Pattern}
    {occurrence : SourceOccurrence} (member : occurrence ∈ normalizedOccurrences unitLabel source) :
    occurrence.value ≠ .apply unitLabel [] ∧ ¬ IsBagNode occurrence.value := by
  have valueMember : occurrence.value ∈ bagContents unitLabel [normalForm (some unitLabel) source] := by
    rw [← normalizedOccurrences_values]
    exact List.mem_map.mpr ⟨occurrence,member,rfl⟩
  exact bagContents_spec (fun element member =>
    (List.mem_singleton.mp member) ▸ rootNormal_normalForm unitLabel source) valueMember

private theorem bagContents_plain {unitLabel : String} {components : List Pattern}
    (plain : ∀ component ∈ components, component ≠ .apply unitLabel [] ∧ ¬ IsBagNode component) :
    bagContents unitLabel components = components := by
  induction components with
  | nil => rfl
  | cons head tail recurse =>
    have first := plain head (by simp)
    rw [bagContents_cons,bagContents, List.flatMap_cons,List.flatMap_nil,List.append_nil,
      splice_of_not_bag first.2]
    simp only [List.filter_cons,decide_eq_true first.1,if_true,List.filter_nil]
    change head :: bagContents unitLabel tail = head :: tail
    rw [recurse (fun component member => plain component (by simp [member]))]

private theorem bagContents_grouped {unitLabel : String} {groups : List (List Pattern)}
    {residual : List Pattern}
    (plain : ∀ component ∈ groups.flatten ++ residual,
      component ≠ .apply unitLabel [] ∧ ¬ IsBagNode component) :
    bagContents unitLabel (groups.map (collapse unitLabel) ++ residual) = groups.flatten ++ residual := by
  induction groups with
  | nil => simpa using bagContents_plain plain
  | cons group groups recurse =>
    have firstPlain : ∀ component ∈ group,
        component ≠ .apply unitLabel [] ∧ ¬ IsBagNode component := by
      intro component member
      exact plain component (by simp [member])
    have laterPlain : ∀ component ∈ groups.flatten ++ residual,
        component ≠ .apply unitLabel [] ∧ ¬ IsBagNode component := by
      intro component member
      apply plain component
      simpa only [List.flatten_cons,List.append_assoc,List.mem_append] using Or.inr member
    rw [List.map_cons,List.cons_append,bagContents_cons,bagContents_collapse firstPlain,
      recurse laterPlain,List.flatten_cons,List.append_assoc]

/-- Group and residual values exhaust exactly the existing physical
components; group boundaries and empty groups add no component. -/
theorem groupedView_contents {unitLabel : String} {source : Pattern} {count : Nat}
    {groups : List (List SourceOccurrence)} {residual : List SourceOccurrence}
    (allocation : (groups,residual) ∈ groupedOccurrences count (normalizedOccurrences unitLabel source)) :
    bagContents unitLabel
      (groups.map (fun group => collapse unitLabel (group.map SourceOccurrence.value)) ++
        residual.map SourceOccurrence.value) = (groups.flatten ++ residual).map SourceOccurrence.value := by
  have account := (mem_groupedOccurrences count).mp allocation |>.2
  have mapped : (groups.map (List.map SourceOccurrence.value)).flatten =
      groups.flatten.map SourceOccurrence.value := List.map_flatten.symm
  rw [List.map_append,← mapped]
  simpa only [List.map_map,Function.comp_def] using
    bagContents_grouped (groups := groups.map (List.map SourceOccurrence.value))
    (residual := residual.map SourceOccurrence.value) (by
      intro component member
      rw [mapped,← List.map_append] at member
      obtain ⟨occurrence,inside,rfl⟩ := List.mem_map.mp member
      exact normalizedOccurrence_plain (account.mem_iff.mp inside))

/-- Every constructed group has the homogeneous base sort; the residual
also keeps its separate collection-data typing. -/
theorem groupedView_admissible {language : LanguageDef} {bag : GrammarRule} {unitLabel : String}
    (laws : BareBagTheory {language with equations := []} bag (some unitLabel))
    (base : BasePremiseEvaluator) {free : FreeTypeContext} {bound : List TypeExpr} {source : Pattern}
    (good : Admissible language free bound (.base bag.category) source)
    {count : Nat} {groups : List (List SourceOccurrence)} {residual : List SourceOccurrence}
    (allocation : (groups,residual) ∈ groupedOccurrences count (normalizedOccurrences unitLabel source)) :
    Admissible language free bound (.base bag.category) (groupedView unitLabel groups residual) ∧
      Admissible language free bound (.collection .hashBag (.base bag.category))
        (.collection .hashBag (residual.map SourceOccurrence.value) none) := by
  have account := (mem_groupedOccurrences count).mp allocation |>.2
  have each : ∀ occurrence ∈ groups.flatten ++ residual,
      Admissible language free bound (.base bag.category) occurrence.value :=
    fun occurrence member => (normalizedOccurrences_sound laws good (account.mem_iff.mp member)).2.1
  constructor
  · apply (component_row_admissible laws ?_).1
    intro component member
    rcases List.mem_append.mp member with grouped | retained
    · obtain ⟨group,inGroups,rfl⟩ := List.mem_map.mp grouped
      apply collapsed_row_admissible laws base
      intro value valueMember
      obtain ⟨occurrence,inGroup,rfl⟩ := List.mem_map.mp valueMember
      exact each occurrence (List.mem_append_left _ (List.mem_flatten.mpr ⟨group,inGroups,inGroup⟩))
    · obtain ⟨occurrence,inResidual,rfl⟩ := List.mem_map.mp retained
      exact each occurrence (List.mem_append_right _ inResidual)
  · apply (component_row_admissible laws ?_).2
    intro value member
    obtain ⟨occurrence,inResidual,rfl⟩ := List.mem_map.mp member
    exact each occurrence (List.mem_append_right _ inResidual)

/-- Finite grouping is justified by the actual typed flattening and unit
laws. All authored equation rows remain in the source language. -/
theorem groupedView_equivalent {language : LanguageDef} {bag : GrammarRule} {unitLabel : String}
    (laws : BareBagTheory {language with equations := []} bag (some unitLabel))
    (base : BasePremiseEvaluator) {free : FreeTypeContext} {bound : List TypeExpr} {source : Pattern}
    (good : Admissible language free bound (.base bag.category) source)
    {count : Nat} {groups : List (List SourceOccurrence)} {residual : List SourceOccurrence}
    (allocation : (groups,residual) ∈ groupedOccurrences count (normalizedOccurrences unitLabel source)) :
    EquationEquiv base language source (groupedView unitLabel groups residual) := by
  have account := (mem_groupedOccurrences count).mp allocation |>.2
  have groupedGood := (groupedView_admissible laws base good allocation).1
  have comparisonGood := grammar_admissible (source := language)
    (target := {language with equations := []}) rfl groupedGood
  let terms := groups.map (fun group => collapse unitLabel (group.map SourceOccurrence.value)) ++
    residual.map SourceOccurrence.value
  have spliced := path_splice (base := base) laws (type := .base bag.category) rfl terms [] comparisonGood
  simp only [List.nil_append] at spliced
  have afterSplice := path_admissible laws spliced comparisonGood rfl
  have dropped := path_dropUnits (base := base) laws rfl (terms.flatMap splice) [] afterSplice
  simp only [List.nil_append] at dropped
  have flattened : Path base {language with equations := []} (groupedView unitLabel groups residual)
      (.collection .hashBag ((groups.flatten ++ residual).map SourceOccurrence.value) none) := by
    have combined := spliced.trans dropped
    change Path base {language with equations := []} (.collection .hashBag terms none)
      (.collection .hashBag (bagContents unitLabel terms) none) at combined
    simpa only [terms,groupedView,groupedView_contents allocation] using combined
  have groupedPath := comparison_path (language := language) flattened
  have normalizedGood := normalized_admissible laws base good rfl
  have normalViewGood := grammar_admissible (source := language)
    (target := {language with equations := []}) rfl (view_admissible laws normalizedGood)
  have permuted : ((groups.flatten ++ residual).map SourceOccurrence.value).Perm
      (bagContents unitLabel [normalForm (some unitLabel) source]) := by
    rw [← normalizedOccurrences_values]
    exact account.map SourceOccurrence.value
  have permutation := path_of_derived (base := base)
    (DerivedInstance.bagPerm_of_sorted (sortedAt_of_admissible laws normalViewGood rfl) permuted.symm)
  have permutationPath := comparison_path (language := language) permutation
  exact .trans _ _ _ (normalized_view_equivalent laws base good)
    (.trans _ _ _ (Relation.EqvGen.reflTransGen_le_eqvGen _ _ _ permutationPath)
      (Relation.EqvGen.reflTransGen_le_eqvGen _ _ _ groupedPath).symm)

/-- Any ordinary match of a listed grouped presentation is an actual
reference match at an equivalent representative, including empty groups. -/
theorem grouped_reference_presentation {language : LanguageDef} {bag : GrammarRule} {unitLabel : String}
    (laws : BareBagTheory {language with equations := []} bag (some unitLabel))
    (unconditional : ReferenceStep.UnconditionalEquations language)
    (aligned : ReferenceStep.EquationsAligned language) (relEnv : Engine.RelationEnv)
    {free : FreeTypeContext} {bound : List TypeExpr} {source schema : Pattern}
    (good : Admissible language free bound (.base bag.category) source)
    {count : Nat} {groups : List (List SourceOccurrence)} {residual : List SourceOccurrence}
    (allocation : (groups,residual) ∈ groupedOccurrences count (normalizedOccurrences unitLabel source))
    {bindings : Bindings}
    (matched : MatchRel schema (groupedView unitLabel groups residual) bindings) :
    ReferenceStep.PresentedMatch (ReferenceStep.equivalentSetoid relEnv language) schema source bindings := by
  exact ⟨_,(ReferenceStep.equivalent_iff_unconditional unconditional aligned).mp
    (groupedView_equivalent laws (engineBasePremises relEnv) good allocation),matchRel_complete matched⟩

/-- Flattening group tags together with the residual and physical source
units gives exactly the original source occurrence account. -/
theorem grouped_occurrence_account {unitLabel : String} {source : Pattern} {count : Nat}
    {groups : List (List SourceOccurrence)} {residual : List SourceOccurrence}
    (allocation : (groups,residual) ∈ groupedOccurrences count (normalizedOccurrences unitLabel source)) :
    ((groups.flatten ++ residual) ++ unitOccurrences unitLabel source).Perm
      (sourceOccurrences unitLabel source) :=
  (((mem_groupedOccurrences count).mp allocation).2.append_right _).trans
    (occurrence_account unitLabel source)

#print axioms groupedView_contents
#print axioms groupedView_admissible
#print axioms groupedView_equivalent
#print axioms grouped_reference_presentation
#print axioms grouped_occurrence_account




private theorem listNodes_map_sum (components : List Pattern) :
    listNodes components = (components.map nodes).sum := by
  induction components with
  | nil => rfl
  | cons first rest recurse => simp only [listNodes,List.map_cons,List.sum_cons,recurse]

private theorem listNodes_append (first second : List Pattern) :
    listNodes (first ++ second) = listNodes first + listNodes second := by
  simp only [listNodes_map_sum,List.map_append,List.sum_append]

private theorem listNodes_perm {first second : List Pattern} (permutation : first.Perm second) :
    listNodes first = listNodes second := by
  simp only [listNodes_map_sum]
  exact (permutation.map nodes).sum_eq

private theorem listNodes_positive {components : List Pattern} (nonempty : components ≠ []) :
    0 < listNodes components := by
  cases components with
  | nil => exact (nonempty rfl).elim
  | cons first rest => have positive := nodes_positive first; simp only [listNodes]; omega

/-- A group can contain every source component, or no component. Its
collapsed algebra value has a non-strict source-node bound. -/
theorem collapse_nodes_le (unitLabel : String) {selected residual whole : List Pattern}
    (account : (selected ++ residual).Perm whole) :
    nodes (collapse unitLabel selected) ≤ nodes (collapse unitLabel whole) := by
  have lengths := account.length_eq
  simp only [List.length_append] at lengths
  have sizes := listNodes_perm account
  rw [listNodes_append] at sizes
  cases selected with
  | nil =>
    change 1 ≤ nodes (collapse unitLabel whole)
    have positive := nodes_positive (collapse unitLabel whole)
    omega
  | cons first selected =>
    cases whole with
    | nil => simp only [List.length_cons,List.length_nil] at lengths; omega
    | cons head whole =>
      cases selected with
      | nil =>
        cases whole with
        | nil => simp only [collapse,listNodes] at *; omega
        | cons second later => simp only [collapse,nodes,listNodes] at *; omega
      | cons second later =>
        cases whole with
        | nil => simp only [List.length_cons,List.length_nil] at lengths; omega
        | cons next remaining => simp only [collapse,nodes,listNodes] at *; omega

/-- Genuine positive consumption with a nonempty residual gives strict
source descent. Unit padding and whole-group selection are deliberately
outside this stronger statement. -/
theorem collapse_nodes_lt (unitLabel : String) {selected residual whole : List Pattern}
    (account : (selected ++ residual).Perm whole)
    (selectedNonempty : selected ≠ []) (residualNonempty : residual ≠ []) :
    nodes (collapse unitLabel selected) < nodes (collapse unitLabel whole) := by
  have lengths := account.length_eq
  have selectedLength : 0 < selected.length := List.length_pos_iff.mpr selectedNonempty
  have residualLength : 0 < residual.length := List.length_pos_iff.mpr residualNonempty
  simp only [List.length_append] at lengths
  have sizes := listNodes_perm account
  rw [listNodes_append] at sizes
  have positive := listNodes_positive residualNonempty
  cases whole with
  | nil => simp only [List.length_nil] at lengths; omega
  | cons head whole =>
    cases whole with
    | nil => simp only [List.length_cons,List.length_nil] at lengths; omega
    | cons next remaining =>
      cases selected with
      | nil => exact (selectedNonempty rfl).elim
      | cons first selected =>
        cases selected <;> simp only [collapse,nodes,listNodes] at * <;> omega

/-- Every finite physical group has a bounded algebra value, including the
whole-source and zero-component cases. The measure is the existing source
normal form's tree size, not an arbitrary presentation size. -/
theorem split_group_nodes_le {unitLabel : String} {source : Pattern}
    {selected residual : List SourceOccurrence}
    (allocation : (selected,residual) ∈ occurrenceSplits (normalizedOccurrences unitLabel source)) :
    nodes (collapse unitLabel (selected.map SourceOccurrence.value)) ≤
      nodes (normalForm (some unitLabel) source) := by
  have account := (mem_occurrenceSplits.mp allocation).map SourceOccurrence.value
  rw [List.map_append,normalizedOccurrences_values] at account
  have bounded := collapse_nodes_le unitLabel account
  rw [collapse_contents (rootNormal_normalForm unitLabel source)] at bounded
  exact bounded

/-- The strict bound has an explicit physical progress condition. Neither
an administrative unit nor a group equal to the whole source earns it. -/
theorem split_group_nodes_lt {unitLabel : String} {source : Pattern}
    {selected residual : List SourceOccurrence}
    (allocation : (selected,residual) ∈ occurrenceSplits (normalizedOccurrences unitLabel source))
    (selectedNonempty : selected ≠ []) (residualNonempty : residual ≠ []) :
    nodes (collapse unitLabel (selected.map SourceOccurrence.value)) <
      nodes (normalForm (some unitLabel) source) := by
  have account := (mem_occurrenceSplits.mp allocation).map SourceOccurrence.value
  rw [List.map_append,normalizedOccurrences_values] at account
  have bounded := collapse_nodes_lt unitLabel account
    (by simpa using selectedNonempty) (by simpa using residualNonempty)
  rw [collapse_contents (rootNormal_normalForm unitLabel source)] at bounded
  exact bounded

/-- Every actual selected member of an admissible source presentation
allocates a finite group of the original source's tagged components. The
converse uses the existing source equation normalizer, not a matching oracle. -/
theorem source_selection_covered {language : LanguageDef} {bag : GrammarRule} {unitLabel : String}
    (laws : BareBagTheory {language with equations := []} bag (some unitLabel))
    (rows : ∀ row ∈ language.equations,
      row.premises = [] ∧ RowPattern row.left ∧ RowPattern row.right ∧
        ∀ bindings,normalForm (some unitLabel) (applyBindings bindings row.left) =
          normalForm (some unitLabel) (applyBindings bindings row.right))
    (aligned : ReferenceStep.EquationsAligned language) (relEnv : Engine.RelationEnv)
    {free : FreeTypeContext} {bound : List TypeExpr} {source : Pattern} {elements : List Pattern}
    (sourceGood : Admissible language free bound (.base bag.category) source)
    (representativeGood : Admissible language free bound (.base bag.category)
      (.collection .hashBag elements none))
    (equivalent : ReferenceStep.Equivalent relEnv language source (.collection .hashBag elements none))
    (index : Nat) (within : index < elements.length) :
    ∃ selected residual,
      (selected,residual) ∈ occurrenceSplits (normalizedOccurrences unitLabel source) ∧
      selected.map SourceOccurrence.value = bagContents unitLabel [normalForm (some unitLabel) elements[index]] ∧
      residual.map SourceOccurrence.value =
        bagContents unitLabel ((elements.eraseIdx index).map (normalForm (some unitLabel))) ∧
      collapse unitLabel (selected.map SourceOccurrence.value) = normalForm (some unitLabel) elements[index] ∧
      nodes (normalForm (some unitLabel) elements[index]) ≤ nodes (normalForm (some unitLabel) source) := by
  have normalEqual := (reference_equivalent_iff_normalForm_eq laws rows aligned relEnv
    sourceGood representativeGood rfl).mp equivalent
  have reordered := (List.getElem_cons_eraseIdx_perm within).map (normalForm (some unitLabel))
  have components := (reordered.flatMap_right splice).filter
    (fun pattern => decide (pattern ≠ .apply unitLabel []))
  change (bagContents unitLabel (normalForm (some unitLabel) elements[index] ::
    (elements.eraseIdx index).map (normalForm (some unitLabel)))).Perm
      (bagContents unitLabel (elements.map (normalForm (some unitLabel)))) at components
  rw [bagContents_cons] at components
  have sortedAccount : (bagContents unitLabel (elements.map (normalForm (some unitLabel)))).Perm
      (bagContents unitLabel [normalForm (some unitLabel) source]) := by
    rw [normalEqual,normalForm_bag_contents]
    exact (sortPatterns_perm _).symm
  have fullAccount := components.trans sortedAccount
  rw [← normalizedOccurrences_values unitLabel source] at fullAccount
  obtain ⟨selected,residual,allocation,first,last⟩ :=
    split_occurrences_of_values SourceOccurrence.value fullAccount
  have selectedValue : collapse unitLabel (selected.map SourceOccurrence.value) =
      normalForm (some unitLabel) elements[index] := by
    rw [first,collapse_contents (rootNormal_normalForm unitLabel elements[index])]
  exact ⟨selected,residual,allocation,first,last,selectedValue,
    selectedValue ▸ split_group_nodes_le allocation⟩

#print axioms collapse_nodes_le
#print axioms collapse_nodes_lt
#print axioms split_group_nodes_le
#print axioms split_group_nodes_lt
#print axioms source_selection_covered




/-- The ordinary matcher realizes every finite one-group allocation. The
selected algebra value and residual collection data occupy distinct roles. -/
theorem single_group_capture_match (unitLabel selectedName restName : String)
    (different : selectedName ≠ restName) (selected residual : List SourceOccurrence) :
    MatchRel (.collection .hashBag [.fvar selectedName] (some restName))
      (groupedView unitLabel [selected] residual)
      [(restName,.collection .hashBag (residual.map SourceOccurrence.value) none),
       (selectedName,collapse unitLabel (selected.map SourceOccurrence.value))] := by
  apply MatchRel.collection (by decide)
  apply MatchBagRel.cons 0 (by simp) MatchRel.fvar MatchBagRel.nilRest
  simp [mergeBindings,different]

private theorem source_row_contents_equivalent {language : LanguageDef} {bag : GrammarRule} {unitLabel : String}
    (laws : BareBagTheory {language with equations := []} bag (some unitLabel))
    (base : BasePremiseEvaluator) {free : FreeTypeContext} {bound : List TypeExpr} {elements : List Pattern}
    (good : Admissible language free bound (.base bag.category) (.collection .hashBag elements none)) :
    EquationEquiv base language (.collection .hashBag elements none)
      (.collection .hashBag (bagContents unitLabel (elements.map (normalForm (some unitLabel)))) none) := by
  have viewGood := view_admissible laws (normalized_admissible laws base good rfl)
  have comparisonGood := grammar_admissible (source := language)
    (target := {language with equations := []}) rfl viewGood
  have permuted : (bagContents unitLabel [normalForm (some unitLabel)
      (.collection .hashBag elements none)]).Perm
      (bagContents unitLabel (elements.map (normalForm (some unitLabel)))) := by
    rw [normalForm_bag_contents]
    exact sortPatterns_perm _
  have permutation := path_of_derived (base := base)
    (DerivedInstance.bagPerm_of_sorted (sortedAt_of_admissible laws comparisonGood rfl) permuted)
  exact .trans _ _ _ (normalized_view_equivalent laws base good)
    (Relation.EqvGen.reflTransGen_le_eqvGen _ _ _ (comparison_path (language := language) permutation))

/-- Every actual one-variable/rest source match at an admissible equivalent
presentation is recovered by a finite physical grouping, with actual source
equivalence for both captures and a typed residual data boundary. This does
not transport arbitrary literal provider predicates or rule conclusions. -/
theorem source_capture_covered {language : LanguageDef} {bag : GrammarRule} {unitLabel : String}
    (laws : BareBagTheory {language with equations := []} bag (some unitLabel))
    (rows : ∀ row ∈ language.equations,
      row.premises = [] ∧ RowPattern row.left ∧ RowPattern row.right ∧
        ∀ bindings,normalForm (some unitLabel) (applyBindings bindings row.left) =
          normalForm (some unitLabel) (applyBindings bindings row.right))
    (aligned : ReferenceStep.EquationsAligned language) (relEnv : Engine.RelationEnv)
    {free : FreeTypeContext} {bound : List TypeExpr} {source : Pattern} {elements : List Pattern}
    (sourceGood : Admissible language free bound (.base bag.category) source)
    (representativeGood : Admissible language free bound (.base bag.category)
      (.collection .hashBag elements none))
    (equivalent : ReferenceStep.Equivalent relEnv language source (.collection .hashBag elements none))
    {selectedName restName : String} (different : selectedName ≠ restName) {bindings : Bindings}
    (matched : MatchBagRel [.fvar selectedName] (some restName) .hashBag elements bindings) :
    ∃ selected residual originalSelected originalResidual,
      (selected,residual) ∈ occurrenceSplits (normalizedOccurrences unitLabel source) ∧
      bindings.lookup selectedName = some originalSelected ∧
      bindings.lookup restName = some originalResidual ∧
      ReferenceStep.Equivalent relEnv language originalSelected
        (collapse unitLabel (selected.map SourceOccurrence.value)) ∧
      ReferenceStep.Equivalent relEnv language originalResidual
        (.collection .hashBag (residual.map SourceOccurrence.value) none) ∧
      ReferenceStep.PresentedMatch (ReferenceStep.equivalentSetoid relEnv language)
        (.collection .hashBag [.fvar selectedName] (some restName)) source
        [(restName,.collection .hashBag (residual.map SourceOccurrence.value) none),
         (selectedName,collapse unitLabel (selected.map SourceOccurrence.value))] ∧
      Admissible language free bound (.collection .hashBag (.base bag.category))
        (.collection .hashBag (residual.map SourceOccurrence.value) none) ∧
      nodes (collapse unitLabel (selected.map SourceOccurrence.value)) ≤
        nodes (normalForm (some unitLabel) source) := by
  have inversion : ∃ (index : Nat) (within : index < elements.length),
      bindings = [(restName,.collection .hashBag (elements.eraseIdx index) none),
        (selectedName,elements[index])] := by
    cases matched with
    | cons index within head later merged =>
      cases head
      cases later
      exact ⟨index,within,by simpa [mergeBindings,different] using merged.symm⟩
  obtain ⟨index,within,rfl⟩ := inversion
  obtain ⟨selected,residual,allocation,_,last,selectedValue,_⟩ :=
    source_selection_covered laws rows aligned relEnv sourceGood representativeGood equivalent index within
  have grouped : ([selected],residual) ∈ groupedOccurrences 1 (normalizedOccurrences unitLabel source) :=
    (mem_groupedOccurrences 1).mpr ⟨rfl,by simpa using mem_occurrenceSplits.mp allocation⟩
  have selectedGood := source_bag_element laws representativeGood (List.getElem_mem within)
  have residualGood : Admissible language free bound (.base bag.category)
      (.collection .hashBag (elements.eraseIdx index) none) :=
    (component_row_admissible laws (fun component member =>
      source_bag_element laws representativeGood (List.mem_of_mem_eraseIdx member))).1
  have selectedEquivalent : ReferenceStep.Equivalent relEnv language elements[index]
      (collapse unitLabel (selected.map SourceOccurrence.value)) := by
    rw [selectedValue]
    exact (ReferenceStep.equivalent_iff_unconditional (fun row member => (rows row member).1) aligned).mp
      (source_equiv_normalForm laws (engineBasePremises relEnv) selectedGood rfl)
  have residualEquivalent : ReferenceStep.Equivalent relEnv language
      (.collection .hashBag (elements.eraseIdx index) none)
      (.collection .hashBag (residual.map SourceOccurrence.value) none) := by
    rw [last]
    exact (ReferenceStep.equivalent_iff_unconditional (fun row member => (rows row member).1) aligned).mp
      (source_row_contents_equivalent laws (engineBasePremises relEnv) residualGood)
  refine ⟨selected,residual,elements[index],.collection .hashBag (elements.eraseIdx index) none,
    allocation,?_,?_,selectedEquivalent,residualEquivalent,?_,?_,split_group_nodes_le allocation⟩
  · simp [Bindings.lookup,different.symm]
  · simp [Bindings.lookup]
  · exact grouped_reference_presentation laws (fun row member => (rows row member).1) aligned relEnv
      sourceGood grouped (single_group_capture_match unitLabel selectedName restName different selected residual)
  · exact (groupedView_admissible laws (engineBasePremises relEnv) sourceGood grouped).2

#print axioms single_group_capture_match
#print axioms source_capture_covered




/-- A rule firing at a finite grouped presentation is an actual original
source step modulo the declared equations. Group administration changes
neither the rule index nor its bindings or premise witness history. -/
theorem stepModulo_of_grouped_rule {language : LanguageDef} {bag : GrammarRule} {unitLabel : String}
    (laws : BareBagTheory {language with equations := []} bag (some unitLabel))
    (unconditional : ReferenceStep.UnconditionalEquations language)
    (aligned : ReferenceStep.EquationsAligned language) (relEnv : Engine.RelationEnv)
    {free : FreeTypeContext} {bound : List TypeExpr} {source target : Pattern}
    (good : Admissible language free bound (.base bag.category) source)
    {count : Nat} {groups : List (List SourceOccurrence)} {residual : List SourceOccurrence}
    (allocation : (groups,residual) ∈ groupedOccurrences count (normalizedOccurrences unitLabel source))
    {index : Nat} {initial : Bindings} {witnesses : List ReferenceStep.Witness}
    (fired : ReferenceStep.StepValid relEnv language (groupedView unitLabel groups residual)
      (.rule index initial witnesses) target) :
    ReferenceStep.StepModulo relEnv language source target ∧
      Admissible language free bound (.base bag.category) (groupedView unitLabel groups residual) ∧
      ReferenceStep.Equivalent relEnv language source (groupedView unitLabel groups residual) ∧
      ReferenceStep.StepValid relEnv language (groupedView unitLabel groups residual)
        (.rule index initial witnesses) target ∧
      ((groups.flatten ++ residual) ++ unitOccurrences unitLabel source).Perm
        (sourceOccurrences unitLabel source) := by
  have converted := (ReferenceStep.equivalent_iff_unconditional unconditional aligned).mp
    (groupedView_equivalent laws (engineBasePremises relEnv) good allocation)
  exact ⟨⟨_,target,converted,⟨.rule index initial witnesses,fired⟩,.refl _⟩,
    (groupedView_admissible laws (engineBasePremises relEnv) good allocation).1,
    converted,fired,grouped_occurrence_account allocation⟩

#print axioms stepModulo_of_grouped_rule


end Mettapedia.GSLT.LanguageDef.BagNormalForm.WithAuthoredEquations.AlgebraFocus

namespace Mettapedia.GSLT.LanguageDef.BagNormalForm.WithAuthoredEquations.AlgebraFocus

open Mettapedia.OSLF.MeTTaIL Syntax ContextualStep DerivedContexts Match MatchSpec GeneralTypedSites
open Mettapedia.GSLT.LanguageDef.WellSorted EquationSemantics

private theorem contextAddress_comp (outer inner : OneHoleContext) :
    contextAddress (outer.comp inner) = contextAddress outer ++ contextAddress inner := by
  induction outer <;> simp_all only [OneHoleContext.comp,contextAddress,List.nil_append,List.cons_append]

/-- Rebase a real physical source record along the existing outer zipper.
Its original and normalized values are retained unchanged. -/
def SourceOccurrence.underContext (outer : OneHoleContext) (occurrence : SourceOccurrence) : SourceOccurrence :=
  { occurrence with
    address := contextAddress outer ++ occurrence.address
    context := outer.comp occurrence.context }

/-- Rebasing maps a whole physical account; it does not select or duplicate
individual equal-valued occurrences. -/
theorem underContext_account (outer : OneHoleContext) {first second : List SourceOccurrence}
    (account : first.Perm second) :
    (first.map (SourceOccurrence.underContext outer)).Perm
      (second.map (SourceOccurrence.underContext outer)) := account.map _

theorem underContext_distinct (outer : OneHoleContext) {occurrences : List SourceOccurrence}
    (distinct : (occurrences.map SourceOccurrence.address).Nodup) :
    ((occurrences.map (SourceOccurrence.underContext outer)).map SourceOccurrence.address).Nodup := by
  apply List.pairwise_map.mpr
  apply List.pairwise_map.mpr
  apply (List.pairwise_map.mp distinct).imp
  intro first second different same
  exact different ((List.append_right_inj _).mp same)

/-- Every physical algebra leaf carries actual typed descent from its
original source, with the exact local context and declaring carrier. -/
theorem sourceOccurrences_typedAt {language : LanguageDef} {bag : GrammarRule} {unitLabel : String}
    (laws : BareBagTheory {language with equations := []} bag (some unitLabel))
    {free : FreeTypeContext} {bound : List TypeExpr} :
    ∀ source,Admissible language free bound (.base bag.category) source →
      ∀ occurrence,occurrence ∈ sourceOccurrences unitLabel source →
      TypedAt language free occurrence.original occurrence.context bound (.base bag.category)
        bound (.base bag.category)
  | source,good,occurrence,member => by
    by_cases isBag : IsBagNode source
    · obtain ⟨elements,rfl⟩ := isBag
      rw [sourceOccurrences_bag] at member
      obtain ⟨⟨element,index⟩,indexed,mapped⟩ := List.mem_flatMap.mp member
      obtain ⟨inside,inChild,rfl⟩ := List.mem_map.mp mapped
      have selected := List.mk_mem_zipIdx_iff_getElem?.mp indexed
      have within := (List.getElem?_eq_some_iff.mp selected).1
      have elementMember := List.mem_of_getElem? selected
      have elementGood := source_bag_element laws good elementMember
      have childTyped := sourceOccurrences_typedAt laws element elementGood inside inChild
      have childFilled := (sourceOccurrences_sound laws element elementGood inside inChild).2.1
      have split : elements.take index ++ element :: elements.drop (index + 1) = elements := by
        rw [← (List.getElem?_eq_some_iff.mp selected).2,List.getElem_cons_drop within]
        exact List.take_append_drop index elements
      have comparisonGood := grammar_admissible (source := language)
        (target := {language with equations := []}) rfl good
      have elementsTyped := (bag_typing laws comparisonGood.typed rfl).2.2
      obtain ⟨parameterName,shape⟩ := laws.bareShape
      apply TypedAt.collectionConstructor (language := language) laws.bagAuthored shape ?_ childTyped
      rw [childFilled,split]
      exact grammar_elements (source := {language with equations := []}) (target := language) rfl elementsTyped
    · rw [sourceOccurrences_nonbag isBag] at member
      obtain rfl := List.mem_singleton.mp member
      exact .here good.typed
termination_by source => sizeOf source

/-- Sorting and unit filtering preserve the real typed occurrence, not only
its endpoint type. -/
theorem normalizedOccurrences_typedAt {language : LanguageDef} {bag : GrammarRule} {unitLabel : String}
    (laws : BareBagTheory {language with equations := []} bag (some unitLabel))
    {free : FreeTypeContext} {bound : List TypeExpr} {source : Pattern}
    (good : Admissible language free bound (.base bag.category) source)
    {occurrence : SourceOccurrence} (member : occurrence ∈ normalizedOccurrences unitLabel source) :
    TypedAt language free occurrence.original occurrence.context bound (.base bag.category)
      bound (.base bag.category) := by
  have filtered := (sortOccurrences_perm (componentOccurrences unitLabel source)).mem_iff.mp member
  exact sourceOccurrences_typedAt laws source good occurrence (List.mem_filter.mp filtered).1

/-- A full original typed occurrence transports every tagged component
through its real constructor/binder zipper. No new operational context
permission is inferred from this typing descent. -/
theorem normalizedOccurrence_under_typed_context {language : LanguageDef} {bag : GrammarRule} {unitLabel : String}
    (laws : BareBagTheory {language with equations := []} bag (some unitLabel))
    {free : FreeTypeContext} {bound rootBound : List TypeExpr} {rootType : TypeExpr}
    {source : Pattern} {outer : OneHoleContext}
    (good : Admissible language free bound (.base bag.category) source)
    (selected : TypedAt language free source outer rootBound rootType bound (.base bag.category))
    {occurrence : SourceOccurrence} (member : occurrence ∈ normalizedOccurrences unitLabel source) :
    TypedAt language free occurrence.original (SourceOccurrence.underContext outer occurrence).context
        rootBound rootType bound (.base bag.category) ∧
      (SourceOccurrence.underContext outer occurrence).context.fill occurrence.original = outer.fill source ∧
      contextAddress (SourceOccurrence.underContext outer occurrence).context =
        (SourceOccurrence.underContext outer occurrence).address := by
  have inside := normalizedOccurrences_typedAt laws good member
  have sourceAccount := normalizedOccurrences_sound laws good member
  have outerTyped : TypedAt language free (occurrence.context.fill occurrence.original) outer
      rootBound rootType bound (.base bag.category) := sourceAccount.2.2.1 ▸ selected
  refine ⟨TypedAt.comp outerTyped inside,?_,?_⟩
  · rw [SourceOccurrence.underContext,OneHoleContext.fill_comp,sourceAccount.2.2.1]
  · simp only [SourceOccurrence.underContext,contextAddress_comp,sourceAccount.2.2.2.2.1]

/-- At most one physical component supports a scalar head. The unit has an
explicit virtual case, with no manufactured source occurrence. -/
inductive SourceHead where
  | unit
  | physical (occurrence : SourceOccurrence)
  deriving Repr,DecidableEq

def sourceHead? : List SourceOccurrence → Option SourceHead
  | [] => some .unit
  | [occurrence] => some (.physical occurrence)
  | _ => none

def SourceHead.original (unitLabel : String) : SourceHead → Pattern
  | .unit => .apply unitLabel []
  | .physical occurrence => occurrence.original

/-- Scalar and constructor spines retain their actual local type. A bag
node can occur at a collection-free type only at the homogeneous base sort. -/
theorem normalizedOccurrences_sound_at {language : LanguageDef} {bag : GrammarRule} {unitLabel : String}
    (laws : BareBagTheory {language with equations := []} bag (some unitLabel))
    (base : BasePremiseEvaluator) {free : FreeTypeContext} {bound : List TypeExpr}
    {expected : TypeExpr} {source : Pattern}
    (good : Admissible language free bound expected source) (collectionless : collectionFree expected = true)
    {occurrence : SourceOccurrence} (member : occurrence ∈ normalizedOccurrences unitLabel source) :
    Admissible language free bound expected occurrence.original ∧
      Admissible language free bound expected occurrence.value ∧
      occurrence.context.fill occurrence.original = source ∧
      occurrence.value = normalForm (some unitLabel) occurrence.original ∧
      contextAddress occurrence.context = occurrence.address ∧
      ∀ replacement,HasType language free bound replacement expected →
        HasType language free bound (occurrence.context.fill replacement) expected := by
  by_cases isBag : IsBagNode source
  · obtain ⟨elements,rfl⟩ := isBag
    have compared := grammar_admissible (source := language)
      (target := {language with equations := []}) rfl good
    have same := (bag_typing laws compared.typed collectionless).2.1
    subst expected
    exact normalizedOccurrences_sound laws good member
  · have filtered := (sortOccurrences_perm (componentOccurrences unitLabel source)).mem_iff.mp member
    have original := (List.mem_filter.mp filtered).1
    rw [sourceOccurrences_nonbag isBag] at original
    obtain rfl := List.mem_singleton.mp original
    exact ⟨good,normalized_admissible laws base good collectionless,rfl,rfl,rfl,fun _ typed => typed⟩

/-- A source scalar head is an actual original leaf or an explicit unit
presentation. It has the exact original source normal value. -/
theorem sourceHead_readback {language : LanguageDef} {bag : GrammarRule} {unitLabel : String}
    (laws : BareBagTheory {language with equations := []} bag (some unitLabel))
    (base : BasePremiseEvaluator) {free : FreeTypeContext} {bound : List TypeExpr} {expected : TypeExpr} {source : Pattern}
    (good : Admissible language free bound expected source) (collectionless : collectionFree expected = true)
    {head : SourceHead} (found : sourceHead? (normalizedOccurrences unitLabel source) = some head) :
    Admissible language free bound expected (head.original unitLabel) ∧
      normalForm (some unitLabel) (head.original unitLabel) = normalForm (some unitLabel) source ∧
      EquationEquiv base language source (head.original unitLabel) := by
  have shape : ∀ (occurrences : List SourceOccurrence),sourceHead? occurrences = some head →
      (head = .unit ∧ occurrences = []) ∨ ∃ occurrence,head = .physical occurrence ∧ occurrences = [occurrence] := by
    intro occurrences selected
    cases occurrences with
    | nil => exact .inl ⟨Option.some.inj selected.symm,rfl⟩
    | cons first rest =>
      cases rest with
      | nil => exact .inr ⟨first,Option.some.inj selected.symm,rfl⟩
      | cons next later => cases selected
  rcases shape _ found with ⟨rfl,empty⟩ | ⟨occurrence,rfl,singleton⟩
  · have unitGood := declared_unit_admissible laws base free bound
    have contents : bagContents unitLabel [normalForm (some unitLabel) source] = [] := by
      rw [← normalizedOccurrences_values,empty]
      rfl
    have image : normalForm (some unitLabel) source = .apply unitLabel [] := by
      rw [← collapse_contents (rootNormal_normalForm unitLabel source),contents]
      rfl
    have unitGood : Admissible language free bound expected (.apply unitLabel []) := by
      simpa only [image] using normalized_admissible laws base good collectionless
    refine ⟨unitGood,?_,?_⟩
    · simpa only [SourceHead.original,image,List.map_nil] using normalForm_apply (some unitLabel) unitLabel []
    · simpa only [SourceHead.original,image] using source_equiv_normalForm laws base good collectionless
  · have member : occurrence ∈ normalizedOccurrences unitLabel source := by rw [singleton]; exact .head _
    have original := normalizedOccurrences_sound_at laws base good collectionless member
    have contents : bagContents unitLabel [normalForm (some unitLabel) source] = [occurrence.value] := by
      rw [← normalizedOccurrences_values,singleton]
      rfl
    have image : normalForm (some unitLabel) occurrence.original = normalForm (some unitLabel) source := by
      rw [← original.2.2.2.1,← collapse_contents (rootNormal_normalForm unitLabel source),contents]
      rfl
    refine ⟨original.1,image,?_⟩
    exact .trans _ _ _ (source_equiv_normalForm laws base good collectionless)
      (image ▸ (source_equiv_normalForm laws base original.1 collectionless).symm)

#print axioms underContext_account
#print axioms underContext_distinct
#print axioms sourceOccurrences_typedAt
#print axioms normalizedOccurrences_typedAt
#print axioms normalizedOccurrence_under_typed_context
#print axioms normalizedOccurrences_sound_at
#print axioms sourceHead_readback

end Mettapedia.GSLT.LanguageDef.BagNormalForm.WithAuthoredEquations.AlgebraFocus

namespace Mettapedia.GSLT.LanguageDef.BagNormalForm.WithAuthoredEquations.AlgebraFocus

open Mettapedia.OSLF.MeTTaIL Syntax ContextualStep DerivedContexts Match MatchSpec GeneralTypedSites
open Mettapedia.GSLT.LanguageDef.WellSorted EquationSemantics

/-- A scalar normal value has a finite head readback. The empty component
row is the virtual unit case rather than a missing physical token. -/
theorem sourceHead_isSome_of_scalar {unitLabel : String} {source : Pattern}
    (scalar : ¬ IsBagNode (normalForm (some unitLabel) source)) :
    (sourceHead? (normalizedOccurrences unitLabel source)).isSome = true := by
  have length : (normalizedOccurrences unitLabel source).length ≤ 1 := by
    rw [← List.length_map (f := SourceOccurrence.value),normalizedOccurrences_values]
    by_cases unit : normalForm (some unitLabel) source = .apply unitLabel []
    · simp [unit,bagContents,splice]
    · simp [bagContents,splice_of_not_bag scalar,unit]
  cases found : normalizedOccurrences unitLabel source with
  | nil => rfl
  | cons occurrence rest =>
    cases rest with
    | nil => rfl
    | cons next later => simp only [found,List.length_cons] at length; omega

/-- Scalar readback never introduces a bag node as an original physical
leaf; such nodes belong to the exact grouped allocation account. -/
theorem sourceHead_nonbag {unitLabel : String} {source : Pattern} {head : SourceHead}
    (found : sourceHead? (normalizedOccurrences unitLabel source) = some head) :
    ¬ IsBagNode (head.original unitLabel) := by
  cases occurrences : normalizedOccurrences unitLabel source with
  | nil =>
    rw [occurrences,sourceHead?] at found
    cases Option.some.inj found
    simp [SourceHead.original,IsBagNode]
  | cons occurrence rest =>
    cases rest with
    | nil =>
      rw [occurrences,sourceHead?] at found
      cases Option.some.inj found
      have member : occurrence ∈ normalizedOccurrences unitLabel source := by rw [occurrences]; exact .head _
      have filtered := (sortOccurrences_perm (componentOccurrences unitLabel source)).mem_iff.mp member
      exact (sourceOccurrences_leaf_value unitLabel source occurrence (List.mem_filter.mp filtered).1).1
    | cons next later => simp [occurrences,sourceHead?] at found

private theorem normalForm_apply_inverse {unitLabel label : String} {source : Pattern} {targets : List Pattern}
    (nonbag : ¬ IsBagNode source)
    (image : normalForm (some unitLabel) source = .apply label targets) :
    ∃ arguments,source = .apply label arguments ∧ arguments.map (normalForm (some unitLabel)) = targets := by
  cases source with
  | apply actual arguments =>
    rw [normalForm_apply] at image
    obtain ⟨rfl,values⟩ := Pattern.apply.inj image
    exact ⟨arguments,rfl,values⟩
  | collection kind elements rest =>
    cases kind <;> cases rest <;> simp_all [normalForm,IsBagNode]
  | _ => simp only [normalForm] at image; cases image

private theorem normalForm_lambda_inverse {unitLabel : String} {source target : Pattern} {binder : Option String}
    (nonbag : ¬ IsBagNode source)
    (image : normalForm (some unitLabel) source = .lambda binder target) :
    ∃ body,source = .lambda binder body ∧ normalForm (some unitLabel) body = target := by
  cases source with
  | lambda actual body =>
    simp only [normalForm,Pattern.lambda.injEq] at image
    obtain ⟨rfl,bodyImage⟩ := image
    exact ⟨body,rfl,bodyImage⟩
  | collection kind elements rest =>
    cases kind <;> cases rest <;> simp_all [normalForm,IsBagNode]
  | _ => simp only [normalForm] at image; cases image

private theorem normalForm_multiLambda_inverse {unitLabel : String} {source target : Pattern}
    {arity : Nat} {binders : List String}
    (nonbag : ¬ IsBagNode source)
    (image : normalForm (some unitLabel) source = .multiLambda arity binders target) :
    ∃ body,source = .multiLambda arity binders body ∧ normalForm (some unitLabel) body = target := by
  cases source with
  | multiLambda actual actualNames body =>
    simp only [normalForm,Pattern.multiLambda.injEq] at image
    obtain ⟨rfl,rfl,bodyImage⟩ := image
    exact ⟨body,rfl,bodyImage⟩
  | collection kind elements rest =>
    cases kind <;> cases rest <;> simp_all [normalForm,IsBagNode]
  | _ => simp only [normalForm] at image; cases image

/-- Constructor descent recovers the actual original argument spine and
its authored declaration index. Temporary normalized children are not
mistaken for physical source occurrences. -/
theorem sourceHead_constructor {language : LanguageDef} {bag : GrammarRule} {unitLabel : String}
    (laws : BareBagTheory {language with equations := []} bag (some unitLabel))
    (base : BasePremiseEvaluator) {free : FreeTypeContext} {bound : List TypeExpr} {expected : TypeExpr} {source : Pattern}
    (good : Admissible language free bound expected source) (collectionless : collectionFree expected = true)
    {head : SourceHead} (found : sourceHead? (normalizedOccurrences unitLabel source) = some head)
    {label : String} {targets : List Pattern}
    (image : normalForm (some unitLabel) source = .apply label targets) :
    ∃ (arguments : List Pattern) (declarationIndex : Nat) (rule : GrammarRule),
      head.original unitLabel = .apply label arguments ∧
      arguments.map (normalForm (some unitLabel)) = targets ∧
      language.terms[declarationIndex]? = some rule ∧ rule.label = label ∧
      (.base rule.category : TypeExpr) = expected ∧ ¬ UsesBareCollection rule ∧
      ArgumentsHaveTypes language free bound arguments rule.params := by
  obtain ⟨originalGood,normalEq,_⟩ := sourceHead_readback laws base good collectionless found
  obtain ⟨arguments,spine,values⟩ := normalForm_apply_inverse (sourceHead_nonbag found) (normalEq.trans image)
  have typed := originalGood.typed
  rw [spine] at typed
  cases typed with
  | constructor member ordinary argumentsTyped =>
    obtain ⟨index,selected⟩ := List.mem_iff_getElem?.mp member
    exact ⟨arguments,index,_,spine,values,selected,rfl,rfl,ordinary,argumentsTyped⟩

/-- Binder descent keeps a genuine function role, its original body and
the complete extended local context. -/
theorem sourceHead_lambda {language : LanguageDef} {bag : GrammarRule} {unitLabel : String}
    (laws : BareBagTheory {language with equations := []} bag (some unitLabel))
    (base : BasePremiseEvaluator) {free : FreeTypeContext} {bound : List TypeExpr}
    {expected : TypeExpr} {source : Pattern}
    (good : Admissible language free bound expected source) (collectionless : collectionFree expected = true)
    {head : SourceHead} (found : sourceHead? (normalizedOccurrences unitLabel source) = some head)
    {binder : Option String} {target : Pattern}
    (image : normalForm (some unitLabel) source = .lambda binder target) :
    ∃ domain codomain body,expected = .arrow domain codomain ∧
      head.original unitLabel = .lambda binder body ∧ normalForm (some unitLabel) body = target ∧
      Admissible language free (domain :: bound) codomain body := by
  obtain ⟨originalGood,normalEq,_⟩ := sourceHead_readback laws base good collectionless found
  obtain ⟨body,spine,values⟩ := normalForm_lambda_inverse (sourceHead_nonbag found) (normalEq.trans image)
  have typed := originalGood.typed
  rw [spine] at typed
  cases typed with
  | lambda bodyTyped =>
    refine ⟨_,_,body,rfl,spine,values,bodyTyped,?_,?_⟩
    · have canonical := originalGood.canonical
      rw [spine] at canonical
      simp only [Pattern.hasCanonicalBinderMetadata,Bool.and_eq_true] at canonical
      exact canonical.2
    · have object := originalGood.object
      rw [spine] at object
      simpa only [isObjectPattern] using object

/-- Multi-binder readback retains the authored arity, original body and
actual repeated domain prefix. -/
theorem sourceHead_multiLambda {language : LanguageDef} {bag : GrammarRule} {unitLabel : String}
    (laws : BareBagTheory {language with equations := []} bag (some unitLabel))
    (base : BasePremiseEvaluator) {free : FreeTypeContext} {bound : List TypeExpr}
    {expected : TypeExpr} {source : Pattern}
    (good : Admissible language free bound expected source) (collectionless : collectionFree expected = true)
    {head : SourceHead} (found : sourceHead? (normalizedOccurrences unitLabel source) = some head)
    {arity : Nat} {binders : List String} {target : Pattern}
    (image : normalForm (some unitLabel) source = .multiLambda arity binders target) :
    ∃ domain codomain body,expected = .arrow (.multiBinder domain) codomain ∧
      head.original unitLabel = .multiLambda arity binders body ∧
      normalForm (some unitLabel) body = target ∧
      Admissible language free (List.replicate arity domain ++ bound) codomain body := by
  obtain ⟨originalGood,normalEq,_⟩ := sourceHead_readback laws base good collectionless found
  obtain ⟨body,spine,values⟩ := normalForm_multiLambda_inverse (sourceHead_nonbag found) (normalEq.trans image)
  have typed := originalGood.typed
  rw [spine] at typed
  cases typed with
  | multiLambda bodyTyped =>
    refine ⟨_,_,body,rfl,spine,values,bodyTyped,?_,?_⟩
    · have canonical := originalGood.canonical
      rw [spine] at canonical
      simp only [Pattern.hasCanonicalBinderMetadata,Bool.and_eq_true] at canonical
      exact canonical.2
    · have object := originalGood.object
      rw [spine] at object
      simpa only [isObjectPattern] using object

#print axioms sourceHead_isSome_of_scalar
#print axioms sourceHead_nonbag
#print axioms sourceHead_constructor
#print axioms sourceHead_lambda
#print axioms sourceHead_multiLambda

end Mettapedia.GSLT.LanguageDef.BagNormalForm.WithAuthoredEquations.AlgebraFocus

namespace Mettapedia.GSLT.LanguageDef.BagNormalForm.WithAuthoredEquations.AlgebraFocus

open Mettapedia.OSLF.MeTTaIL Syntax ContextualStep DerivedContexts Match MatchSpec GeneralTypedSites
open Mettapedia.GSLT.LanguageDef.WellSorted EquationSemantics

/-- Lift all schema slots together, conserving the original physical
records globally. Empty slot groups require no physical source occurrence. -/
theorem grouped_occurrences_of_values {α β : Type} (value : α → β)
    {occurrences : List α} :
    ∀ (groups : List (List β)) (residual : List β),
      (groups.flatten ++ residual).Perm (occurrences.map value) →
      ∃ physicalGroups physicalResidual,
        (physicalGroups,physicalResidual) ∈ groupedOccurrences groups.length occurrences ∧
        physicalGroups.map (List.map value) = groups ∧ physicalResidual.map value = residual
  | [],residual,account => by
    obtain ⟨selected,remaining,allocation,empty,last⟩ :=
      split_occurrences_of_values value (selected := []) (residual := residual) (by simpa using account)
    have selectedEmpty : selected = [] := List.map_eq_nil_iff.mp empty
    subst selected
    exact ⟨[],remaining,(mem_groupedOccurrences 0).mpr ⟨rfl,by simpa using mem_occurrenceSplits.mp allocation⟩,rfl,last⟩
  | group :: groups,residual,account => by
    obtain ⟨first,remaining,allocation,firstValues,remainingValues⟩ :=
      split_occurrences_of_values value (selected := group) (residual := groups.flatten ++ residual)
        (by simpa only [List.flatten_cons,List.append_assoc] using account)
    obtain ⟨later,last,laterAllocation,laterValues,lastValues⟩ :=
      grouped_occurrences_of_values value (occurrences := remaining) groups residual
        (by rw [remainingValues])
    have remainingAccount := (mem_groupedOccurrences groups.length).mp laterAllocation
    refine ⟨first :: later,last,(mem_groupedOccurrences (group :: groups).length).mpr ⟨?_,?_⟩,?_,lastValues⟩
    · simp only [List.length_cons,remainingAccount.1]
    · have combined := (remainingAccount.2.append_left first).trans (mem_occurrenceSplits.mp allocation)
      simpa only [List.flatten_cons,List.append_assoc] using combined
    · simp only [List.map_cons,firstValues,laterValues]

/-- The existing independent bag relation selects one row per schema slot
and leaves an exact residual. This inversion does not define a second
matching relation or change binding merge order. -/
theorem bag_selected_values {schemas targets : List Pattern} {rest : Option String}
    {kind : CollType} {bindings : Bindings}
    (matched : MatchBagRel schemas rest kind targets bindings) :
    ∃ selected residual,
      (selected ++ residual).Perm targets ∧
      List.Forall₂ (fun schema target => ∃ captured,MatchRel schema target captured) schemas selected ∧
      (rest = none → residual = []) ∧
      ∀ name,rest = some name → bindings.find? (fun entry => entry.1 == name) = some (name,.collection kind residual none) := by
  induction schemas generalizing targets bindings with
  | nil =>
    cases matched with
    | nilNoRest =>
      refine ⟨[],[],.refl _,.nil,fun _ => rfl,?_⟩
      intro name impossible
      cases impossible
    | nilRest =>
      refine ⟨[],_,.refl _,.nil,?_,?_⟩
      · intro impossible
        cases impossible
      · intro name equal
        cases Option.some.inj equal
        simp
  | cons schema schemas recurse =>
    cases matched with
    | cons index within head tail merged =>
      obtain ⟨selected,residual,account,rows,noRest,restRead⟩ := recurse tail
      refine ⟨_ :: selected,residual,?_,.cons ⟨_,head⟩ rows,noRest,?_⟩
      · exact (account.cons _).trans (List.getElem_cons_eraseIdx_perm within)
      · intro name restEq
        exact mergeBindings_subsumed_right merged (restRead name restEq)

#print axioms grouped_occurrences_of_values
#print axioms bag_selected_values

end Mettapedia.GSLT.LanguageDef.BagNormalForm.WithAuthoredEquations.AlgebraFocus

namespace Mettapedia.GSLT.LanguageDef.BagNormalForm.WithAuthoredEquations.AlgebraFocus

open Mettapedia.OSLF.MeTTaIL Syntax ContextualStep DerivedContexts Match MatchSpec GeneralTypedSites
open Mettapedia.GSLT.LanguageDef.WellSorted EquationSemantics

/-- Every finite ordinary bag match, at any schema arity, recovers one
physical group per selected source member and the exact source residual.
Nested member schemas retain their independent ordinary matching witnesses. -/
theorem source_groups_covered {language : LanguageDef} {bag : GrammarRule} {unitLabel : String}
    (laws : BareBagTheory {language with equations := []} bag (some unitLabel))
    (rows : ∀ row ∈ language.equations,
      row.premises = [] ∧ RowPattern row.left ∧ RowPattern row.right ∧
        ∀ bindings,normalForm (some unitLabel) (applyBindings bindings row.left) =
          normalForm (some unitLabel) (applyBindings bindings row.right))
    (aligned : ReferenceStep.EquationsAligned language) (relEnv : Engine.RelationEnv)
    {free : FreeTypeContext} {bound : List TypeExpr} {source : Pattern} {elements schemas : List Pattern}
    (sourceGood : Admissible language free bound (.base bag.category) source)
    (representativeGood : Admissible language free bound (.base bag.category)
      (.collection .hashBag elements none))
    (equivalent : ReferenceStep.Equivalent relEnv language source (.collection .hashBag elements none))
    {rest : Option String} {bindings : Bindings}
    (matched : MatchBagRel schemas rest .hashBag elements bindings) :
    ∃ groups residual selected originalResidual,
      (groups,residual) ∈ groupedOccurrences schemas.length (normalizedOccurrences unitLabel source) ∧
      List.Forall₂ (fun schema target => ∃ captured,MatchRel schema target captured) schemas selected ∧
      groups.map (fun group => collapse unitLabel (group.map SourceOccurrence.value)) =
        selected.map (normalForm (some unitLabel)) ∧
      residual.map SourceOccurrence.value =
        bagContents unitLabel (originalResidual.map (normalForm (some unitLabel))) ∧
      (rest = none → originalResidual = []) ∧
      (∀ name,rest = some name → bindings.find? (fun entry => entry.1 == name) =
        some (name,.collection .hashBag originalResidual none)) ∧
      ((groups.flatten ++ residual) ++ unitOccurrences unitLabel source).Perm
        (sourceOccurrences unitLabel source) := by
  obtain ⟨selected,originalResidual,selectedAccount,selectedMatches,noRest,restRead⟩ := bag_selected_values matched
  have normalEqual := (reference_equivalent_iff_normalForm_eq laws rows aligned relEnv
    sourceGood representativeGood rfl).mp equivalent
  let valueGroups := selected.map (fun element => bagContents unitLabel [normalForm (some unitLabel) element])
  have groupContents : valueGroups.flatten = bagContents unitLabel (selected.map (normalForm (some unitLabel))) := by
    simpa only [valueGroups,List.flatMap] using bagContents_flatMap unitLabel selected
  have components := ((selectedAccount.map (normalForm (some unitLabel))).flatMap_right splice).filter
    (fun pattern => decide (pattern ≠ .apply unitLabel []))
  change (bagContents unitLabel ((selected ++ originalResidual).map (normalForm (some unitLabel)))).Perm
    (bagContents unitLabel (elements.map (normalForm (some unitLabel)))) at components
  rw [List.map_append,bagContents_append] at components
  have sortedAccount : (bagContents unitLabel (elements.map (normalForm (some unitLabel)))).Perm
      ((normalizedOccurrences unitLabel source).map SourceOccurrence.value) := by
    rw [normalizedOccurrences_values,normalEqual,normalForm_bag_contents]
    exact (sortPatterns_perm _).symm
  have account := components.trans sortedAccount
  rw [← groupContents] at account
  obtain ⟨groups,residual,allocation,groupValues,residualValues⟩ :=
    grouped_occurrences_of_values SourceOccurrence.value valueGroups
      (bagContents unitLabel (originalResidual.map (normalForm (some unitLabel)))) account
  have realAllocation : (groups,residual) ∈ groupedOccurrences schemas.length (normalizedOccurrences unitLabel source) := by
    have lengths : valueGroups.length = schemas.length := by simpa only [valueGroups,List.length_map] using selectedMatches.length_eq.symm
    simpa only [lengths] using allocation
  have values : groups.map (fun group => collapse unitLabel (group.map SourceOccurrence.value)) =
      selected.map (normalForm (some unitLabel)) := by
    have collapsed := congrArg (List.map (collapse unitLabel)) groupValues
    simp only [valueGroups,List.map_map,Function.comp_def] at collapsed
    refine collapsed.trans ?_
    exact List.map_congr_left (fun element _ => collapse_contents (rootNormal_normalForm unitLabel element))
  exact ⟨groups,residual,selected,originalResidual,realAllocation,selectedMatches,values,residualValues,
    noRest,restRead,grouped_occurrence_account realAllocation⟩

#print axioms source_groups_covered

end Mettapedia.GSLT.LanguageDef.BagNormalForm.WithAuthoredEquations.AlgebraFocus
