import Mettapedia.OSLF.MeTTaIL.QuoteDropInstantiation
import Mettapedia.OSLF.MeTTaIL.CanonicalSites

/-!
# Quote-drop normal forms keep typing

A language types its reflective presentation when every quote constructor takes one process to a
name, every drop constructor takes one name to a process, and the quote constructor is the only
constructor of the name sort (`QuoteDropTyped`). Then one use of `@(*n) = n`, left to right, keeps
every type: a typed `@(*n)` is a name whose inner `n` is a name. Normal forms of well-sorted open
patterns are well-sorted, the normal captures of a typed assignment are typed, and every drop in a
typed object term is applied to a name.

- `QuoteDropStep.hasType`, `QuoteDropStep.openPatternWellSorted`: one step keeps typing;
- `openPatternWellSorted_normal`: normal forms keep well-sortedness;
- `typedAssignment_normal`: normal captures keep the declared sorts;
- `dropsNamed_of_typed`: typed object terms apply drops to names.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.QuoteDrop

open Syntax Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open ReflectiveSubstitution CanonicalBags

/-- The language types its reflective presentation: quote takes one process to a name, drop takes
one name to a process, and quote is the only constructor of the name sort. -/
structure QuoteDropTyped (language : LanguageDef) (declaration : ReflectivePresentationDecl) : Prop where
  quote : ∀ rule ∈ language.terms, rule.label = declaration.quoteConstructor →
    rule.category = declaration.nameSort ∧
      ∃ parameter, rule.params = [.simple parameter (.base declaration.processSort)]
  drop : ∀ rule ∈ language.terms, rule.label = declaration.dropConstructor →
    rule.category = declaration.processSort ∧
      ∃ parameter, rule.params = [.simple parameter (.base declaration.nameSort)]
  names : ∀ rule ∈ language.terms, rule.category = declaration.nameSort → rule.label = declaration.quoteConstructor

variable {language : LanguageDef} {free : FreeTypeContext} {declaration : ReflectivePresentationDecl}

/-! ## One step -/

theorem hasType_apply_inv {bound : List TypeExpr} {label : String} {arguments : List Pattern} {type : TypeExpr}
    (typed : HasType language free bound (.apply label arguments) type) :
    ∃ rule ∈ language.terms, rule.label = label ∧ type = .base rule.category ∧
      ArgumentsHaveTypes language free bound arguments rule.params := by
  cases typed with
  | constructor declared _ arguments => exact ⟨_, declared, rfl, rfl, arguments⟩

/-- **A typed `@(*n)` has the type of `n`.** -/
theorem hasType_collapse (typedPresentation : QuoteDropTyped language declaration) {bound : List TypeExpr}
    {name : Pattern} {type : TypeExpr}
    (typed : HasType language free bound
      (.apply declaration.quoteConstructor [.apply declaration.dropConstructor [name]]) type) :
    HasType language free bound name type := by
  obtain ⟨quote, quoteDeclared, quoteLabel, rfl, quoteArguments⟩ := hasType_apply_inv typed
  obtain ⟨quoteCategory, _, quoteParameters⟩ := typedPresentation.quote quote quoteDeclared quoteLabel
  rw [quoteParameters] at quoteArguments
  obtain ⟨drop, dropDeclared, dropLabel, _, dropArguments⟩ := hasType_apply_inv quoteArguments.simple_cons_inv.1
  obtain ⟨_, _, dropParameters⟩ := typedPresentation.drop drop dropDeclared dropLabel
  rw [dropParameters] at dropArguments
  rw [quoteCategory]
  exact dropArguments.simple_cons_inv.1

theorem matchesParameterRepresentation_step {parameter : TermParam} {left right : Pattern}
    (step : QuoteDropStep declaration left right) (matched : MatchesParameterRepresentation parameter left) :
    MatchesParameterRepresentation parameter right := by
  cases parameter with
  | simple => trivial
  | abstractionNamed binder name type =>
    obtain ⟨body, rfl⟩ := (matchesParameterRepresentation_abstractionNamed_iff _ _ _ _).mp matched
    cases step with
    | lambda _ => exact (matchesParameterRepresentation_abstractionNamed_iff _ _ _ _).mpr ⟨_, rfl⟩
  | multiAbstractionNamed binders name type =>
    cases step with
    | multiLambda _ =>
      rename_i binders' _ _ _
      cases binders' with
      | nil => trivial
      | cons => simp [MatchesParameterRepresentation] at matched
    | _ => simp [MatchesParameterRepresentation] at matched

private theorem argumentsHaveTypes_middle {bound : List TypeExpr} {argument changed : Pattern}
    (stepped : QuoteDropStep declaration argument changed)
    (typed : ∀ {type : TypeExpr}, HasType language free bound argument type → HasType language free bound changed type) :
    ∀ {before after : List Pattern} {parameters : List TermParam},
      ArgumentsHaveTypes language free bound (before ++ argument :: after) parameters →
      ArgumentsHaveTypes language free bound (before ++ changed :: after) parameters
  | [], after, parameters, arguments => by
    cases arguments with
    | cons representation parameterType head tail =>
      exact .cons (matchesParameterRepresentation_step stepped representation) parameterType (typed head) tail
  | item :: before, after, parameters, arguments => by
    cases arguments with
    | cons representation parameterType head tail =>
      exact .cons representation parameterType head (argumentsHaveTypes_middle stepped typed tail)

/-- **One quote-drop step keeps typing.** -/
theorem QuoteDropStep.hasType (typedPresentation : QuoteDropTyped language declaration) {left right : Pattern}
    (step : QuoteDropStep declaration left right) :
    ∀ {bound : List TypeExpr} {type : TypeExpr}, HasType language free bound left type →
      HasType language free bound right type := by
  induction step with
  | collapse name =>
    intro bound type typed
    exact hasType_collapse typedPresentation typed
  | apply inner ih =>
    intro bound type typed
    cases typed with
    | constructor declared notBare arguments =>
      exact .constructor declared notBare (argumentsHaveTypes_middle inner ih arguments)
  | lambda _ ih =>
    intro bound type typed
    cases typed with
    | lambda body => exact .lambda (ih body)
  | multiLambda _ ih =>
    intro bound type typed
    cases typed with
    | multiLambda body => exact .multiLambda (ih body)
  | substBody _ ih =>
    intro bound type typed
    cases typed with
    | subst body replacement => exact .subst (ih body) replacement
  | substReplacement _ ih =>
    intro bound type typed
    cases typed with
    | subst body replacement => exact .subst body (ih replacement)
  | @element kind before after element changed rest _ ih =>
    intro bound type typed
    have pointwise : ∀ {elementType : TypeExpr},
        ElementsHaveType language free bound (before ++ element :: after) elementType →
        ElementsHaveType language free bound (before ++ changed :: after) elementType := fun elements =>
      elementsHaveType_iff.mpr fun item member => by
        simp only [List.mem_append, List.mem_cons] at member
        rcases member with inBefore | rfl | inAfter
        · exact elementsHaveType_iff.mp elements item (by simp [inBefore])
        · exact ih (elementsHaveType_iff.mp elements _ (by simp))
        · exact elementsHaveType_iff.mp elements item (by simp [inAfter])
    cases typed with
    | collection elements => exact .collection (pointwise elements)
    | collectionConstructor declared parameters elements =>
      exact .collectionConstructor declared parameters (pointwise elements)

private theorem listAll_middle {f : Pattern → Bool} {before after : List Pattern} {x y : Pattern} (same : f x = f y) :
    (before ++ x :: after).all f = (before ++ y :: after).all f := by
  simp [List.all_append, same]

theorem QuoteDropStep.binderMetadata_eq {left right : Pattern} (step : QuoteDropStep declaration left right) :
    left.hasCanonicalBinderMetadata = right.hasCanonicalBinderMetadata := by
  have listForm : ∀ items : List Pattern,
      Pattern.hasCanonicalBinderMetadataList items = items.all Pattern.hasCanonicalBinderMetadata := by
    intro items
    induction items with
    | nil => rfl
    | cons item rest ih => simp [Pattern.hasCanonicalBinderMetadataList, ih]
  induction step with
  | collapse name => simp [Pattern.hasCanonicalBinderMetadata, listForm]
  | apply _ ih => simp only [Pattern.hasCanonicalBinderMetadata, listForm]; exact listAll_middle ih
  | lambda _ ih => simp only [Pattern.hasCanonicalBinderMetadata, ih]
  | multiLambda _ ih => simp only [Pattern.hasCanonicalBinderMetadata, ih]
  | substBody _ ih => simp only [Pattern.hasCanonicalBinderMetadata, ih]
  | substReplacement _ ih => simp only [Pattern.hasCanonicalBinderMetadata, ih]
  | element _ ih => simp only [Pattern.hasCanonicalBinderMetadata, listForm]; exact listAll_middle ih

theorem QuoteDropStep.objectPattern_eq {left right : Pattern} (step : QuoteDropStep declaration left right) :
    isObjectPattern left = isObjectPattern right := by
  induction step with
  | collapse name => simp [isObjectPattern, isObjectPatternList_eq_all]
  | apply _ ih => simp only [isObjectPattern, isObjectPatternList_eq_all]; exact listAll_middle ih
  | lambda _ ih => simp only [isObjectPattern, ih]
  | multiLambda _ ih => simp only [isObjectPattern, ih]
  | substBody _ ih => simp only [isObjectPattern]
  | substReplacement _ ih => simp only [isObjectPattern]
  | element _ ih => simp only [isObjectPattern, isObjectPatternList_eq_all]; rw [listAll_middle ih]

/-- **One quote-drop step keeps well-sortedness.** -/
theorem QuoteDropStep.openPatternWellSorted (typedPresentation : QuoteDropTyped language declaration)
    {left right : Pattern} (step : QuoteDropStep declaration left right)
    {bound : List TypeExpr} {type : TypeExpr} (sorted : OpenPatternWellSorted language free bound type left) :
    OpenPatternWellSorted language free bound type right := by
  obtain ⟨typed, metadata, object, scope⟩ := sorted
  exact ⟨step.hasType typedPresentation typed, step.binderMetadata_eq ▸ metadata, step.objectPattern_eq ▸ object,
    by unfold ScopeSafeAt at scope ⊢; rw [← step.wellScoped]; exact scope⟩

/-! ## Forward chains and normal forms -/

theorem QuoteDropForward.openPatternWellSorted (typedPresentation : QuoteDropTyped language declaration)
    {left right : Pattern} (forward : QuoteDropForward declaration left right)
    {bound : List TypeExpr} {type : TypeExpr} (sorted : OpenPatternWellSorted language free bound type left) :
    OpenPatternWellSorted language free bound type right := by
  induction forward with
  | refl => exact sorted
  | tail _ step ih => exact step.openPatternWellSorted typedPresentation ih

theorem QuoteDropForward.hasType (typedPresentation : QuoteDropTyped language declaration)
    {left right : Pattern} (forward : QuoteDropForward declaration left right)
    {bound : List TypeExpr} {type : TypeExpr} (typed : HasType language free bound left type) :
    HasType language free bound right type := by
  induction forward with
  | refl => exact typed
  | tail _ step ih => exact step.hasType typedPresentation ih

theorem QuoteDropForward.objectPattern_eq {left right : Pattern} (forward : QuoteDropForward declaration left right) :
    isObjectPattern left = isObjectPattern right := by
  induction forward with
  | refl => rfl
  | tail _ step ih => rw [ih, step.objectPattern_eq]

/-- **Quote-drop normal forms keep well-sortedness.** -/
theorem openPatternWellSorted_normal (typedPresentation : QuoteDropTyped language declaration) {pattern : Pattern}
    {bound : List TypeExpr} {type : TypeExpr} (sorted : OpenPatternWellSorted language free bound type pattern) :
    OpenPatternWellSorted language free bound type (normal declaration pattern) :=
  (quoteDrop_forward pattern).openPatternWellSorted typedPresentation sorted

theorem hasType_normal (typedPresentation : QuoteDropTyped language declaration) {pattern : Pattern}
    {bound : List TypeExpr} {type : TypeExpr} (typed : HasType language free bound pattern type) :
    HasType language free bound (normal declaration pattern) type :=
  (quoteDrop_forward pattern).hasType typedPresentation typed

theorem isObjectPattern_normal (pattern : Pattern) :
    isObjectPattern (normal declaration pattern) = isObjectPattern pattern :=
  (quoteDrop_forward pattern).objectPattern_eq.symm

/-- **Normal captures keep the declared sorts.** -/
theorem typedAssignment_normal {environment : GeneralPremise.Environment} {context : GeneralPremise.Context}
    (typedPresentation : QuoteDropTyped environment.language declaration)
    {assignment : ScopedRuleMatching.Assignment} (typed : GeneralPremise.TypedAssignment environment context assignment) :
    GeneralPremise.TypedAssignment environment context (normalAssignment declaration assignment) := by
  obtain ⟨sorts, objects⟩ := typed
  refine ⟨fun name value member => ?_, fun name value member => ?_⟩
  · obtain ⟨⟨name₀, value₀⟩, inOriginal, same⟩ := List.mem_map.mp member
    simp only [Prod.mk.injEq] at same
    obtain ⟨rfl, rfl⟩ := same
    obtain ⟨dependencies, expected, declared, sort, sameDependencies, sameAmbient, bodyTyped⟩ :=
      sorts name₀ value₀ inOriginal
    exact ⟨dependencies, expected, declared, sort, sameDependencies, sameAmbient,
      hasType_normal typedPresentation bodyTyped⟩
  · obtain ⟨⟨name₀, value₀⟩, inOriginal, same⟩ := List.mem_map.mp member
    simp only [Prod.mk.injEq] at same
    obtain ⟨rfl, rfl⟩ := same
    simp only [normalValue, isObjectPattern_normal]
    exact objects name₀ value₀ inOriginal

/-! ## Drops apply to names -/

/-- **A typed object name is a variable or a quotation.** -/
theorem isName_of_typed (typedPresentation : QuoteDropTyped language declaration) {bound : List TypeExpr}
    {pattern : Pattern} {type : TypeExpr} (typed : HasType language free bound pattern type)
    (nameType : type = .base declaration.nameSort) (object : isObjectPattern pattern = true) :
    isName declaration pattern = true := by
  cases typed with
  | bvar _ => simp [isName]
  | fvar _ => simp [isName]
  | @constructor _ rule arguments declared _ typedArguments =>
    simp only [TypeExpr.base.injEq] at nameType
    have isQuote := typedPresentation.names rule declared nameType
    obtain ⟨_, _, parameters⟩ := typedPresentation.quote rule declared isQuote
    rw [parameters] at typedArguments
    cases typedArguments with
    | cons _ _ _ rest =>
      cases rest
      simp [isName, isQuote]
  | lambda _ => cases nameType
  | multiLambda _ => cases nameType
  | subst _ _ => simp [isObjectPattern] at object
  | collection _ => cases nameType
  | @collectionConstructor _ rule _ _ _ _ _ declared parameters _ =>
    simp only [TypeExpr.base.injEq] at nameType
    obtain ⟨_, _, quoteParameters⟩ := typedPresentation.quote rule declared (typedPresentation.names rule declared nameType)
    have parameters := ((GrammarRule.bareParams_cons_iff _ _ _).mp parameters).2
    rw [quoteParameters] at parameters
    simp at parameters

theorem argumentsHaveTypes_mem {bound : List TypeExpr} :
    ∀ {arguments : List Pattern} {parameters : List TermParam},
      ArgumentsHaveTypes language free bound arguments parameters →
      ∀ argument ∈ arguments, ∃ type, HasType language free bound argument type
  | [], _, _, _, member => absurd member List.not_mem_nil
  | _ :: _, _, typed, argument, member => by
    cases typed with
    | cons _ _ head tail =>
      rcases List.mem_cons.mp member with rfl | inRest
      · exact ⟨_, head⟩
      · exact argumentsHaveTypes_mem tail argument inRest

/-- **Every drop in a typed object term is applied to a name.** -/
theorem dropsNamed_of_typed (typedPresentation : QuoteDropTyped language declaration) (pattern : Pattern) :
    ∀ {bound : List TypeExpr} {type : TypeExpr}, HasType language free bound pattern type →
      isObjectPattern pattern = true → dropsNamed declaration pattern = true := by
  induction pattern using Pattern.inductionOn with
  | hbvar index => intro _ _ _ _; rw [dropsNamed]
  | hfvar name => intro _ _ _ _; rw [dropsNamed]
  | happly label arguments ih =>
    intro bound type typed object
    obtain ⟨rule, declared, rfl, _, typedArguments⟩ := hasType_apply_inv typed
    have objects : ∀ argument ∈ arguments, isObjectPattern argument = true := by
      simp only [isObjectPattern, isObjectPatternList_eq_all, List.all_eq_true] at object
      exact object
    apply dropsNamed_of_apply
    · intro argument member
      obtain ⟨_, argumentTyped⟩ := argumentsHaveTypes_mem typedArguments argument member
      exact ih argument member argumentTyped (objects argument member)
    · intro isDrop argument single
      subst single
      obtain ⟨_, _, parameters⟩ := typedPresentation.drop rule declared isDrop
      rw [parameters] at typedArguments
      exact isName_of_typed typedPresentation typedArguments.simple_cons_inv.1 rfl (objects argument (by simp))
  | hlambda binder body ih =>
    intro bound type typed object
    cases typed with
    | lambda typedBody =>
      rw [dropsNamed]
      exact ih typedBody (by simpa [isObjectPattern] using object)
  | hmultiLambda arity binders body ih =>
    intro bound type typed object
    cases typed with
    | multiLambda typedBody =>
      rw [dropsNamed]
      exact ih typedBody (by simpa [isObjectPattern] using object)
  | hsubst body replacement _ _ =>
    intro _ _ _ object
    simp [isObjectPattern] at object
  | hcollection kind elements rest ih =>
    intro bound type typed object
    have objects : ∀ element ∈ elements, isObjectPattern element = true := by
      simp only [isObjectPattern, isObjectPatternList_eq_all, Bool.and_eq_true, List.all_eq_true] at object
      exact object.2
    have typedElements : ∀ element ∈ elements, ∃ elementType, HasType language free bound element elementType := by
      cases typed with
      | collection elementsTyped => exact fun element member => ⟨_, elementsHaveType_iff.mp elementsTyped element member⟩
      | collectionConstructor _ _ elementsTyped =>
        exact fun element member => ⟨_, elementsHaveType_iff.mp elementsTyped element member⟩
    rw [dropsNamed]
    simp only [List.all_eq_true, List.mem_attach, true_implies, Subtype.forall]
    intro element member
    obtain ⟨_, elementTyped⟩ := typedElements element member
    exact ih element member elementTyped (objects element member)

end Mettapedia.OSLF.MeTTaIL.QuoteDrop
