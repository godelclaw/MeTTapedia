import Mettapedia.GSLT.LanguageDef.GeneralTypedOccurrence

/-!
# Representation-aware replacement at generated typed occurrences

The check follows the actual enclosing declaration alternatives retained by a
site. An arrow type alone does not authorize replacing a binding argument by
an ordinary variable. Conversely, constraints in unrelated constructors do
not restrict a replacement at this occurrence.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.GeneralTypedOccurrence

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.DerivedContexts
open Mettapedia.OSLF.MeTTaIL.GeneralTypedSites
open WellSorted

def replacementRepresentations? (language : LanguageDef) :
    OneHoleContext → List TypingFrame → Pattern → Bool
  | .hole, [], _ => true
  | .apply _ _ inner _, .application declaration index :: frames, target =>
    match language.terms[declaration]?.bind (fun rule => rule.params[index]?) with
    | some parameter =>
      matchesParameterRepresentation? parameter (inner.fill target) &&
        replacementRepresentations? language inner frames target
    | none => false
  | .lambda _ inner, .lambda _ :: frames, target =>
    replacementRepresentations? language inner frames target
  | .multiLambda _ _ inner, .multiLambda _ _ :: frames, target =>
    replacementRepresentations? language inner frames target
  | .collection _ _ inner _ _, .directCollection _ :: frames, target =>
    replacementRepresentations? language inner frames target
  | .collection _ _ inner _ _, .authoredCollection _ :: frames, target =>
    replacementRepresentations? language inner frames target
  | _, _, _ => false

def _root_.Mettapedia.OSLF.MeTTaIL.GeneralTypedSites.SiteData.acceptsReplacementRepresentation
    (language : LanguageDef)
    (site : SiteData) (target : Pattern) : Bool :=
  replacementRepresentations? language site.context site.typingFrames target

theorem replace_argument {language : LanguageDef} {free : FreeTypeContext}
    {bound : List TypeExpr} {arguments : List Pattern} {parameters : List TermParam}
    (typed : ArgumentsHaveTypes language free bound arguments parameters)
    {index : Nat} {parameter : TermParam} {expected : TypeExpr} {target : Pattern}
    (selected : parameters[index]? = some parameter)
    (parameterTyped : parameterType? parameter = some expected)
    (represented : MatchesParameterRepresentation parameter target)
    (replacement : HasType language free bound target expected) :
    ArgumentsHaveTypes language free bound
      (arguments.take index ++ target :: arguments.drop (index + 1)) parameters := by
  cases typed with
  | nil => simp at selected
  | @cons bound argument arguments parameterHead parameters typeHead representationHead
      parameterTypeHead argumentTyped tailTyped =>
    cases index with
    | zero =>
      have same : parameterHead = parameter := by simpa using selected
      subst parameterHead
      have sameType : typeHead = expected := Option.some.inj (parameterTypeHead.symm.trans parameterTyped)
      subst typeHead
      simpa using ArgumentsHaveTypes.cons represented parameterTyped replacement tailTyped
    | succ index =>
      have selectedTail : parameters[index]? = some parameter := by simpa using selected
      simpa using ArgumentsHaveTypes.cons representationHead parameterTypeHead argumentTyped
        (replace_argument tailTyped selectedTail parameterTyped represented replacement)
termination_by sizeOf arguments

theorem replace_element {language : LanguageDef} {free : FreeTypeContext}
    {bound : List TypeExpr} {elements : List Pattern} {expected : TypeExpr}
    (typed : ElementsHaveType language free bound elements expected)
    {index : Nat} {element target : Pattern}
    (selected : elements[index]? = some element)
    (replacement : HasType language free bound target expected) :
    ElementsHaveType language free bound
      (elements.take index ++ target :: elements.drop (index + 1)) expected := by
  cases typed with
  | nil => simp at selected
  | @cons bound elementHead elements expected headTyped tailTyped =>
    cases index with
    | zero => simpa using ElementsHaveType.cons replacement tailTyped
    | succ index =>
      have selectedTail : elements[index]? = some element := by simpa using selected
      simpa using ElementsHaveType.cons headTyped (replace_element tailTyped selectedTail replacement)
termination_by sizeOf elements

namespace Licensed

theorem replace_checked {language : LanguageDef} {free : FreeTypeContext}
    {permissions : OperationalPermissions} {bound : List TypeExpr} {expected : TypeExpr}
    {source : Pattern} {site : SiteData}
    (licensed : Licensed language free permissions bound expected source site)
    (target : Pattern)
    (represented : site.acceptsReplacementRepresentation language target = true)
    (replacement : HasType language free site.focusBound target site.focusType) :
    HasType language free bound (site.context.fill target) expected := by
  induction licensed with
  | here _ _ _ => exact replacement
  | @application bound rule declaration index arguments argument parameter parameterType inner
      declared ordinary argumentsTyped _ selected parameterSelected parameterTyped _ innerLicensed ih =>
    have declarationAt := List.mk_mem_zipIdx_iff_getElem?.mp declared
    simp only [SiteData.acceptsReplacementRepresentation, SiteData.wrapApplication,
      replacementRepresentations?, declarationAt, Option.bind_some, parameterSelected,
      Bool.and_eq_true] at represented
    have representedArgument := (matchesParameterRepresentation?_eq_true_iff _ _).mp represented.1
    have argumentReplacement := ih represented.2 replacement
    exact HasType.constructor (List.fst_mem_of_mem_zipIdx declared) ordinary
      (replace_argument argumentsTyped parameterSelected parameterTyped
        representedArgument argumentReplacement)
  | lambda _ _ ih => exact .lambda (ih represented replacement)
  | multiLambda _ _ ih => exact .multiLambda (ih represented replacement)
  | directCollection _ elementsTyped _ selected _ ih =>
    exact .collection (replace_element elementsTyped selected (ih represented replacement))
  | authoredCollection declared shape _ elementsTyped _ selected _ ih =>
    exact .collectionConstructor (List.fst_mem_of_mem_zipIdx declared) shape
      (replace_element elementsTyped selected (ih represented replacement))

theorem replace_checked_openPatternWellSorted {language : LanguageDef} {free : FreeTypeContext}
    {permissions : OperationalPermissions} {bound : List TypeExpr} {expected : TypeExpr}
    {source : Pattern} {site : SiteData}
    (licensed : Licensed language free permissions bound expected source site)
    (admitted : OpenPatternWellSorted language free bound expected source)
    (target : Pattern)
    (represented : site.acceptsReplacementRepresentation language target = true)
    (profile : AdmissionProfileEquivalent site.focus target)
    (replacement : HasType language free site.focusBound target site.focusType) :
    OpenPatternWellSorted language free bound expected (site.context.fill target) := by
  obtain ⟨_, canonical, object, scopeProof⟩ := admitted
  rw [← licensed.source_eq] at canonical object scopeProof
  obtain ⟨canonicalEq, objectEq, scopeEq⟩ :=
    OneHoleContext.admissionProfileEquivalent_fill site.context profile
  refine ⟨licensed.replace_checked target represented replacement,
    canonicalEq.symm ▸ canonical, objectEq.symm ▸ object, ?_⟩
  unfold ScopeSafeAt at scopeProof ⊢
  rw [← scopeEq bound.length]
  exact scopeProof

end Licensed

end Mettapedia.GSLT.LanguageDef.GeneralTypedOccurrence
