import Mettapedia.OSLF.MeTTaIL.GeneralPremiseProvider
import Mettapedia.OSLF.MeTTaIL.ScopedPattern

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.GeneralPremise

open Syntax
open Mettapedia.GSLT.LanguageDef.WellSorted

mutual
theorem typed_append_bound {language : LanguageDef} {free : FreeTypeContext}
    {bound : List TypeExpr} {pattern : Pattern} {type : TypeExpr}
    (typed : HasType language free bound pattern type) (outer : List TypeExpr) :
    HasType language free (bound ++ outer) pattern type :=
  match typed with
  | .bvar found => .bvar (by
      rw [List.getElem?_append_left]
      · exact found
      · exact List.getElem?_eq_some_iff.mp found |>.1)
  | .fvar found => .fvar found
  | .constructor declared ordinary arguments =>
      .constructor declared ordinary (arguments_append_bound arguments outer)
  | .lambda body => .lambda (typed_append_bound body outer)
  | .multiLambda body => .multiLambda (by
      simpa only [List.append_assoc] using typed_append_bound body outer)
  | .subst body replacement =>
      .subst (typed_append_bound body outer) (typed_append_bound replacement outer)
  | .collection elements => .collection (elements_append_bound elements outer)
  | .collectionConstructor declared representation elements =>
      .collectionConstructor declared representation (elements_append_bound elements outer)

theorem arguments_append_bound {language : LanguageDef} {free : FreeTypeContext}
    {bound : List TypeExpr} {patterns : List Pattern} {parameters : List TermParam}
    (typed : ArgumentsHaveTypes language free bound patterns parameters) (outer : List TypeExpr) :
    ArgumentsHaveTypes language free (bound ++ outer) patterns parameters :=
  match typed with
  | .nil => .nil
  | .cons represented expected head tail =>
      .cons represented expected (typed_append_bound head outer)
        (arguments_append_bound tail outer)

theorem elements_append_bound {language : LanguageDef} {free : FreeTypeContext}
    {bound : List TypeExpr} {patterns : List Pattern} {type : TypeExpr}
    (typed : ElementsHaveType language free bound patterns type) (outer : List TypeExpr) :
    ElementsHaveType language free (bound ++ outer) patterns type :=
  match typed with
  | .nil _ _ => .nil _ _
  | .cons head tail =>
      .cons (typed_append_bound head outer) (elements_append_bound tail outer)
end

theorem closed_wellSorted_in_bound {language : LanguageDef} {free : FreeTypeContext}
    {pattern : Pattern} {type : TypeExpr}
    (typed : OpenPatternWellSorted language free [] type pattern) (bound : List TypeExpr) :
    OpenPatternWellSorted language free bound type pattern := by
  refine ⟨by simpa using typed_append_bound typed.1 bound,
    typed.2.1, typed.2.2.1, ?_⟩
  change pattern.isWellScopedAt bound.length = true
  exact ScopedPattern.isWellScopedAt_mono typed.2.2.2 (Nat.zero_le _)

theorem closed_values_in_bound {language : LanguageDef} {free : FreeTypeContext}
    {values : List Pattern} {types : List TypeExpr}
    (typed : ValuesTyped language free [] values types) (bound : List TypeExpr) :
    ValuesTyped language free bound values types := by
  induction typed with
  | nil => exact .nil
  | cons head _ inductionHypothesis =>
      exact .cons (closed_wellSorted_in_bound head bound) inductionHypothesis

theorem closed_row_in_bound {language : LanguageDef} {free : FreeTypeContext}
    {signature : Signature} {row : ProviderRow}
    (typed : RowTyped language free [] signature row) (bound : List TypeExpr) :
    RowTyped language free bound signature row :=
  ⟨typed.1, closed_values_in_bound typed.2 bound⟩

theorem closed_row_checked_in_bound {language : LanguageDef} {free : FreeTypeContext}
    {signature : Signature} {row : ProviderRow}
    (checked : checkRow language free [] signature row = true) (bound : List TypeExpr) :
    checkRow language free bound signature row = true :=
  checkRow_complete (closed_row_in_bound (checkRow_sound checked) bound)

end Mettapedia.OSLF.MeTTaIL.GeneralPremise
