import Mettapedia.GSLT.LanguageDef.WellSortedOccurrence

/-!
# Free-context extension preserves retained typing descent

An extension preserves every defined lookup of the source context. Typing
transport retains the original constructor choices, binder contexts and
selected occurrence rather than reconstructing a potentially different
typing derivation.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.WellSorted

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.DerivedContexts

theorem TypedAt.extendFree {language : LanguageDef}
    {source target : FreeTypeContext} {focus : Pattern}
    {context : OneHoleContext} {bound focusBound : List TypeExpr}
    {type result : TypeExpr}
    (selected : TypedAt language source focus context bound type focusBound result)
    (preserves : ∀ {name freeType},
      source name = some freeType → target name = some freeType) :
    TypedAt language target focus context bound type focusBound result := by
  induction selected with
  | here typed =>
      exact .here (typed.recontextualizeFree fun _ lookup => preserves lookup)
  | application membership ordinary arguments shape length expected _ inductionHypothesis =>
      exact .application membership ordinary
        (arguments.recontextualizeFree fun _ lookup => preserves lookup)
        shape length expected inductionHypothesis
  | lambda _ inductionHypothesis => exact .lambda inductionHypothesis
  | multiLambda _ inductionHypothesis => exact .multiLambda inductionHypothesis
  | substBody replacement _ inductionHypothesis =>
      exact .substBody
        (replacement.recontextualizeFree fun _ lookup => preserves lookup)
        inductionHypothesis
  | substReplacement body _ inductionHypothesis =>
      exact .substReplacement
        (body.recontextualizeFree fun _ lookup => preserves lookup)
        inductionHypothesis
  | collection elements _ inductionHypothesis =>
      exact .collection
        (elements.recontextualizeFree fun _ lookup => preserves lookup)
        inductionHypothesis
  | collectionConstructor membership shape elements _ inductionHypothesis =>
      exact .collectionConstructor membership shape
        (elements.recontextualizeFree fun _ lookup => preserves lookup)
        inductionHypothesis

end Mettapedia.GSLT.LanguageDef.WellSorted
