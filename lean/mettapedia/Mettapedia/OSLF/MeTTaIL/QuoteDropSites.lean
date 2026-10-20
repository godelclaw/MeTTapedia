import Mettapedia.OSLF.MeTTaIL.QuoteDropTyping

/-!
# Licensed sites at quote-drop normal forms

When no reduction site passes under a quote (`QuoteOpaque`), every licensed occurrence of a term
has a licensed counterpart in the term's quote-drop normal form at the same address, with the same
typing frames, the normal form of the focus and the normal forms of the context's fixed parts
(`licensed_normal`). The normal form never removes a node on the path to such a site: it removes
only a quote together with the drop below it.

- `fill_forward`: a context and its normal form, filled with forward-related terms, give
  forward-related terms;
- `replacementRepresentations?_forward`: the replacement check survives forward chains;
- `licensed_normal`: every licensed site has a licensed counterpart at the normal form.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.QuoteDrop

open Syntax DerivedContexts GeneralTypedSites ReflectiveSubstitution CanonicalBags
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.LanguageDef.GeneralTypedOccurrence

variable {declaration : ReflectivePresentationDecl}

variable (declaration) in
/-- The context with every fixed part in normal form. -/
def normalContext : OneHoleContext → OneHoleContext
  | .hole => .hole
  | .apply label before inner after =>
      .apply label (before.map (normal declaration)) (normalContext inner) (after.map (normal declaration))
  | .lambda binder inner => .lambda binder (normalContext inner)
  | .multiLambda arity binders inner => .multiLambda arity binders (normalContext inner)
  | .substBody inner replacement => .substBody (normalContext inner) (normal declaration replacement)
  | .substReplacement body inner => .substReplacement (normal declaration body) (normalContext inner)
  | .collection kind before inner after rest =>
      .collection kind (before.map (normal declaration)) (normalContext inner) (after.map (normal declaration)) rest

variable (declaration) in
/-- The site with its context and focus in normal form. -/
def normalSite (site : SiteData) : SiteData :=
  { site with context := normalContext declaration site.context, focus := normal declaration site.focus }

theorem forall₂_normal (items : List Pattern) :
    List.Forall₂ (QuoteDropForward declaration) items (items.map (normal declaration)) :=
  List.forall₂_map_right_iff.mpr (List.forall₂_same.mpr fun item _ => quoteDrop_forward item)

/-- **A context and its normal form, filled with forward-related terms, give forward-related
terms.** -/
theorem fill_forward : ∀ (context : OneHoleContext) {hole hole' : Pattern},
    QuoteDropForward declaration hole hole' →
      QuoteDropForward declaration (context.fill hole) ((normalContext declaration context).fill hole')
  | .hole, _, _, forward => forward
  | .apply label before inner after, _, _, forward => by
    simp only [OneHoleContext.fill, normalContext]
    exact quoteDropForward_apply_congr _
      (List.rel_append (forall₂_normal before) (.cons (fill_forward inner forward) (forall₂_normal after)))
  | .lambda binder inner, _, _, forward => by
    simp only [OneHoleContext.fill, normalContext]
    exact quoteDropForward_lambda_congr _ (fill_forward inner forward)
  | .multiLambda arity binders inner, _, _, forward => by
    simp only [OneHoleContext.fill, normalContext]
    exact quoteDropForward_multiLambda_congr _ _ (fill_forward inner forward)
  | .substBody inner replacement, _, _, forward => by
    simp only [OneHoleContext.fill, normalContext]
    exact quoteDropForward_subst_congr (fill_forward inner forward) (quoteDrop_forward replacement)
  | .substReplacement body inner, _, _, forward => by
    simp only [OneHoleContext.fill, normalContext]
    exact quoteDropForward_subst_congr (quoteDrop_forward body) (fill_forward inner forward)
  | .collection kind before inner after rest, _, _, forward => by
    simp only [OneHoleContext.fill, normalContext]
    exact quoteDropForward_collection_congr _ _
      (List.rel_append (forall₂_normal before) (.cons (fill_forward inner forward) (forall₂_normal after)))

/-! ## Parameter representations -/

theorem matchesParameterRepresentation_forward {parameter : TermParam} {left right : Pattern}
    (forward : QuoteDropForward declaration left right) (matched : MatchesParameterRepresentation parameter left) :
    MatchesParameterRepresentation parameter right := by
  induction forward with
  | refl => exact matched
  | tail _ step ih => exact matchesParameterRepresentation_step step ih

theorem matchesParameterRepresentation?_forward {parameter : TermParam} {left right : Pattern}
    (forward : QuoteDropForward declaration left right) (matched : matchesParameterRepresentation? parameter left = true) :
    matchesParameterRepresentation? parameter right = true := by
  rw [matchesParameterRepresentation?_eq_true_iff] at matched ⊢
  exact matchesParameterRepresentation_forward forward matched

/-- **The replacement check survives forward chains** of the target and the normal form of the
context. -/
theorem replacementRepresentations?_forward {language : LanguageDef} :
    ∀ (context : OneHoleContext) (frames : List TypingFrame) {target target' : Pattern},
      QuoteDropForward declaration target target' →
      replacementRepresentations? language context frames target = true →
      replacementRepresentations? language (normalContext declaration context) frames target' = true
  | .hole, frames, _, _, _, accepted => by cases frames <;> simp_all [replacementRepresentations?, normalContext]
  | .apply label before inner after, frames, target, target', forward, accepted => by
    cases frames with
    | nil => simp [replacementRepresentations?] at accepted
    | cons frame frames =>
      cases frame with
      | application declarationIndex index =>
        simp only [replacementRepresentations?, normalContext] at accepted ⊢
        split at accepted
        · rename_i parameter _
          simp only [Bool.and_eq_true] at accepted ⊢
          exact ⟨matchesParameterRepresentation?_forward (fill_forward inner forward) accepted.1,
            replacementRepresentations?_forward inner frames forward accepted.2⟩
        · cases accepted
      | _ => simp [replacementRepresentations?] at accepted
  | .lambda binder inner, frames, _, _, forward, accepted => by
    cases frames with
    | nil => simp [replacementRepresentations?] at accepted
    | cons frame frames =>
      cases frame with
      | lambda =>
        simp only [replacementRepresentations?, normalContext] at accepted ⊢
        exact replacementRepresentations?_forward inner frames forward accepted
      | _ => simp [replacementRepresentations?] at accepted
  | .multiLambda arity binders inner, frames, _, _, forward, accepted => by
    cases frames with
    | nil => simp [replacementRepresentations?] at accepted
    | cons frame frames =>
      cases frame with
      | multiLambda =>
        simp only [replacementRepresentations?, normalContext] at accepted ⊢
        exact replacementRepresentations?_forward inner frames forward accepted
      | _ => simp [replacementRepresentations?] at accepted
  | .substBody _ _, frames, _, _, _, accepted => by
    cases frames with
    | nil => simp [replacementRepresentations?] at accepted
    | cons frame frames => cases frame <;> simp [replacementRepresentations?] at accepted
  | .substReplacement _ _, frames, _, _, _, accepted => by
    cases frames with
    | nil => simp [replacementRepresentations?] at accepted
    | cons frame frames => cases frame <;> simp [replacementRepresentations?] at accepted
  | .collection kind before inner after rest, frames, _, _, forward, accepted => by
    cases frames with
    | nil => simp [replacementRepresentations?] at accepted
    | cons frame frames =>
      cases frame with
      | directCollection =>
        simp only [replacementRepresentations?, normalContext] at accepted ⊢
        exact replacementRepresentations?_forward inner frames forward accepted
      | authoredCollection =>
        simp only [replacementRepresentations?, normalContext] at accepted ⊢
        exact replacementRepresentations?_forward inner frames forward accepted
      | _ => simp [replacementRepresentations?] at accepted

/-! ## Typing of normal lists -/

variable {language : LanguageDef} {free : FreeTypeContext}

theorem argumentsHaveTypes_normal (typedPresentation : QuoteDropTyped language declaration) {bound : List TypeExpr} :
    ∀ {arguments : List Pattern} {parameters : List TermParam},
      ArgumentsHaveTypes language free bound arguments parameters →
      ArgumentsHaveTypes language free bound (arguments.map (normal declaration)) parameters
  | [], _, typed => by cases typed; exact .nil
  | _ :: _, _, typed => by
    cases typed with
    | cons representation parameterType head tail =>
      exact .cons (matchesParameterRepresentation_forward (quoteDrop_forward _) representation) parameterType
        (hasType_normal typedPresentation head) (argumentsHaveTypes_normal typedPresentation tail)

theorem elementsHaveType_normal (typedPresentation : QuoteDropTyped language declaration) {bound : List TypeExpr}
    {elements : List Pattern} {elementType : TypeExpr} (typed : ElementsHaveType language free bound elements elementType) :
    ElementsHaveType language free bound (elements.map (normal declaration)) elementType :=
  elementsHaveType_iff.mpr fun item member => by
    obtain ⟨original, inOriginal, rfl⟩ := List.mem_map.mp member
    exact hasType_normal typedPresentation (elementsHaveType_iff.mp typed original inOriginal)

theorem isObjectPatternList_normal {items : List Pattern} (objects : isObjectPatternList items = true) :
    isObjectPatternList (items.map (normal declaration)) = true := by
  rw [isObjectPatternList_eq_all] at objects ⊢
  simpa [Function.comp_def, isObjectPattern_normal] using objects

/-! ## Licensed sites -/

/-- No reduction site passes under a quote. -/
def QuoteOpaque (permissions : OperationalPermissions) (declaration : ReflectivePresentationDecl) : Prop :=
  permissions.allConstructorArguments = false ∧
    ∀ index, (declaration.quoteConstructor, index) ∉ permissions.constructorArguments

/-- **Every licensed site has a licensed counterpart at the quote-drop normal form**: the same
address, typing frames and focus typing, the normal focus and the normal context. -/
theorem licensed_normal {permissions : OperationalPermissions}
    (typedPresentation : QuoteDropTyped language declaration) (quoteOpaque : QuoteOpaque permissions declaration)
    {bound : List TypeExpr} {expected : TypeExpr} {source : Pattern} {site : SiteData}
    (licensed : Licensed language free permissions bound expected source site) :
    Licensed language free permissions bound expected (normal declaration source) (normalSite declaration site) := by
  induction licensed with
  | @here bound expected source enabled object typed =>
    exact .here enabled (by rw [isObjectPattern_normal]; exact object) (hasType_normal typedPresentation typed)
  | @application bound rule declarationIndex index arguments argument parameter parameterType inner
      declared ordinary typed objects selected parameterSelected parameterTyped permitted _ ih =>
    have notQuote : rule.label ≠ declaration.quoteConstructor := by
      intro same
      rcases permitted with all | listed
      · rw [quoteOpaque.1] at all; cases all
      · exact quoteOpaque.2 index (same ▸ listed)
    have siteShape : normalSite declaration (inner.wrapApplication declarationIndex rule.label arguments index) =
        (normalSite declaration inner).wrapApplication declarationIndex rule.label
          (arguments.map (normal declaration)) index := by
      simp [normalSite, SiteData.wrapApplication, normalContext, List.map_take, List.map_drop]
    rw [normal_apply, finish_not_quote notQuote, siteShape]
    exact .application declared ordinary (argumentsHaveTypes_normal typedPresentation typed)
      (isObjectPatternList_normal objects) (by simp [List.getElem?_map, selected]) parameterSelected parameterTyped
      permitted ih
  | @lambda bound binder body domain codomain inner enabled _ ih =>
    have siteShape : normalSite declaration (inner.wrapLambda binder domain) =
        (normalSite declaration inner).wrapLambda binder domain := by
      simp [normalSite, SiteData.wrapLambda, normalContext]
    rw [normal_lambda, siteShape]
    exact .lambda enabled ih
  | @multiLambda bound arity binders body domain codomain inner enabled _ ih =>
    have siteShape : normalSite declaration (inner.wrapMultiLambda arity binders domain) =
        (normalSite declaration inner).wrapMultiLambda arity binders domain := by
      simp [normalSite, SiteData.wrapMultiLambda, normalContext]
    rw [normal_multiLambda, siteShape]
    exact .multiLambda enabled ih
  | @directCollection bound kind elements index element elementType inner permitted typed objects selected _ ih =>
    have siteShape : normalSite declaration (inner.wrapCollection (.directCollection kind) kind elements index) =
        (normalSite declaration inner).wrapCollection (.directCollection kind) kind
          (elements.map (normal declaration)) index := by
      simp [normalSite, SiteData.wrapCollection, normalContext, List.map_take, List.map_drop]
    rw [normal_collection, siteShape]
    exact .directCollection permitted (elementsHaveType_normal typedPresentation typed)
      (isObjectPatternList_normal objects) (by simp [List.getElem?_map, selected]) ih
  | @authoredCollection bound rule declarationIndex parameterName kind elements index element elementType inner
      declared shape permitted typed objects selected _ ih =>
    have siteShape : normalSite declaration
        (inner.wrapCollection (.authoredCollection declarationIndex) kind elements index) =
        (normalSite declaration inner).wrapCollection (.authoredCollection declarationIndex) kind
          (elements.map (normal declaration)) index := by
      simp [normalSite, SiteData.wrapCollection, normalContext, List.map_take, List.map_drop]
    rw [normal_collection, siteShape]
    exact .authoredCollection declared shape permitted (elementsHaveType_normal typedPresentation typed)
      (isObjectPatternList_normal objects) (by simp [List.getElem?_map, selected]) ih

end Mettapedia.OSLF.MeTTaIL.QuoteDrop
