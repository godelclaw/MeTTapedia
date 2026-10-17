import Mettapedia.GSLT.LanguageDef.GeneralTypedOccurrenceReplacement
import Mettapedia.OSLF.MeTTaIL.ClosingRepresentation

/-!
# Local open admission under licensed occurrence replacement

A locally admitted replacement preserves the complete open-pattern carrier
at its licensed occurrence, provided the original enclosing term is admitted
and the actual authored parameter representations accept the replacement.
Canonical metadata and object form pass through the unchanged zipper. The
existing typed replacement theorem supplies the whole target's scope.

The replacement may change its scope behavior at other binder depths. No
equality of all-depth admission profiles or additional whole-target scan is
required. These are preservation theorems for the original typing and
representation checks; they introduce no new evaluator or source judgment.
-/

set_option autoImplicit false
namespace Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.DerivedContexts
open Mettapedia.OSLF.MeTTaIL.ClosingRepresentation
open Pattern

/-- The unchanged context retains its source-side metadata and object-form
checks when a locally canonical object is inserted. Scope equality at other
depths is not a premise. -/
theorem OneHoleContext.admissionCore_fill (context : OneHoleContext) {source target : Pattern}
    (targetCanonical : target.hasCanonicalBinderMetadata = true)
    (targetObject : isObjectPattern target = true) :
    (context.fill source).hasCanonicalBinderMetadata = true →
    isObjectPattern (context.fill source) = true →
    (context.fill target).hasCanonicalBinderMetadata = true ∧
      isObjectPattern (context.fill target) = true := by
  induction context with
  | hole => intro _ _; exact ⟨targetCanonical, targetObject⟩
  | apply label before inner after ih =>
      intro oldCanonical oldObject
      simp only [OneHoleContext.fill, hasCanonicalBinderMetadata,
        hasCanonicalBinderMetadataList_append, hasCanonicalBinderMetadataList,
        Bool.and_eq_true] at oldCanonical
      simp only [OneHoleContext.fill, isObjectPattern,
        isObjectPatternList_append, isObjectPatternList, Bool.and_eq_true] at oldObject
      obtain ⟨newCanonical,newObject⟩ := ih oldCanonical.2.1 oldObject.2.1
      simp only [OneHoleContext.fill, hasCanonicalBinderMetadata,
        hasCanonicalBinderMetadataList_append, hasCanonicalBinderMetadataList,
        isObjectPattern, isObjectPatternList_append, isObjectPatternList, Bool.and_eq_true]
      exact ⟨⟨oldCanonical.1,newCanonical,oldCanonical.2.2⟩,
        oldObject.1,newObject,oldObject.2.2⟩
  | lambda binder inner ih =>
      intro oldCanonical oldObject
      simp only [OneHoleContext.fill, hasCanonicalBinderMetadata, Bool.and_eq_true] at oldCanonical
      obtain ⟨newCanonical,newObject⟩ := ih oldCanonical.2 oldObject
      exact ⟨by simpa only [OneHoleContext.fill, hasCanonicalBinderMetadata, Bool.and_eq_true]
        using And.intro oldCanonical.1 newCanonical, newObject⟩
  | multiLambda arity binders inner ih =>
      intro oldCanonical oldObject
      simp only [OneHoleContext.fill, hasCanonicalBinderMetadata, Bool.and_eq_true] at oldCanonical
      obtain ⟨newCanonical,newObject⟩ := ih oldCanonical.2 oldObject
      exact ⟨by simpa only [OneHoleContext.fill, hasCanonicalBinderMetadata, Bool.and_eq_true]
        using And.intro oldCanonical.1 newCanonical, newObject⟩
  | substBody inner replacement ih => intro _ impossible; cases impossible
  | substReplacement body inner ih => intro _ impossible; cases impossible
  | collection kind before inner after rest ih =>
      intro oldCanonical oldObject
      simp only [OneHoleContext.fill, hasCanonicalBinderMetadata,
        hasCanonicalBinderMetadataList_append, hasCanonicalBinderMetadataList,
        Bool.and_eq_true] at oldCanonical
      simp only [OneHoleContext.fill, isObjectPattern,
        isObjectPatternList_append, isObjectPatternList, Bool.and_eq_true] at oldObject
      obtain ⟨newCanonical,newObject⟩ := ih oldCanonical.2.1 oldObject.2.2.1
      simp only [OneHoleContext.fill, hasCanonicalBinderMetadata,
        hasCanonicalBinderMetadataList_append, hasCanonicalBinderMetadataList,
        isObjectPattern, isObjectPatternList_append, isObjectPatternList, Bool.and_eq_true]
      exact ⟨⟨oldCanonical.1,newCanonical,oldCanonical.2.2⟩,
        oldObject.1,oldObject.2.1,newObject,oldObject.2.2.2⟩

end Mettapedia.GSLT.LanguageDef.WellSorted

namespace Mettapedia.GSLT.LanguageDef.GeneralTypedOccurrence.Licensed
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.GeneralTypedSites
open Mettapedia.OSLF.MeTTaIL.DerivedContexts
open Mettapedia.GSLT.LanguageDef.WellSorted

/-- Local open admission at the actual licensed binding context suffices.
Typing transports scope at the resulting ambient depth, while the unchanged
zipper preserves the remaining source-side admission checks. -/
theorem replace_locally_openPatternWellSorted {language : LanguageDef} {free : FreeTypeContext}
    {permissions : OperationalPermissions} {bound : List TypeExpr} {expected : TypeExpr}
    {source : Pattern} {site : SiteData}
    (licensed : Licensed language free permissions bound expected source site)
    (admitted : OpenPatternWellSorted language free bound expected source)
    (target : Pattern)
    (represented : site.acceptsReplacementRepresentation language target = true)
    (replacement : OpenPatternWellSorted language free site.focusBound site.focusType target) :
    OpenPatternWellSorted language free bound expected (site.context.fill target) := by
  have typed := licensed.replace_checked target represented replacement.1
  have canonical := admitted.2.1
  have object := admitted.2.2.1
  rw [← licensed.source_eq] at canonical object
  obtain ⟨newCanonical,newObject⟩ :=
    OneHoleContext.admissionCore_fill site.context replacement.2.1 replacement.2.2.1 canonical object
  exact ⟨typed,newCanonical,newObject,typed.isWellScopedAt⟩

/-- The local executable admission check already earns the filled target's
open admission; an additional whole-target scan is logically redundant. -/
theorem checkOpenPatternWellSorted_fill_true {language : LanguageDef} {free : FreeTypeContext}
    {permissions : OperationalPermissions} {bound : List TypeExpr} {expected : TypeExpr}
    {source : Pattern} {site : SiteData}
    (licensed : Licensed language free permissions bound expected source site)
    (sourceChecked : checkOpenPatternWellSorted language free bound expected source = true)
    (target : Pattern)
    (represented : site.acceptsReplacementRepresentation language target = true)
    (targetChecked : checkOpenPatternWellSorted language free site.focusBound site.focusType target = true) :
    checkOpenPatternWellSorted language free bound expected (site.context.fill target) = true :=
  checkOpenPatternWellSorted_complete (licensed.replace_locally_openPatternWellSorted
    (checkOpenPatternWellSorted_sound sourceChecked) target represented
    (checkOpenPatternWellSorted_sound targetChecked))

end Mettapedia.GSLT.LanguageDef.GeneralTypedOccurrence.Licensed
