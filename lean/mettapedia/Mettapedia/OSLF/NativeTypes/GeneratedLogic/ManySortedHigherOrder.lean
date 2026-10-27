import Mettapedia.OSLF.NativeTypes.GeneratedLogic.ManySorted
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.HigherOrder

/-!
# Many-sorted native types as higher-order logic

A closed many-sorted formula at a sort is translated to higher-order logic through its guarded translation
(`translateSorted`): the predicate on the sum carrier that holds at an element exactly when the element has the sort
and the formula holds there (`denote_translateSorted`). The translation uses only the basis of higher-order logic,
variables, constants, application, abstraction and equality (`basisOnly_translateSorted`), with the sort guards as
type relations of the one-sorted signature.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.GeneratedLogic.ManySorted

open Mettapedia.Logic.HOL hiding Formula
open Mettapedia.OSLF.Framework.NativeBasis (nowhere BasisOnly)
open Mettapedia.OSLF.MeTTaIL.Syntax (TypeExpr)

variable {Srt : Type} [DecidableEq Srt] {Carrier : Type} (T : NativeStructure Carrier) (toType : Srt → TypeExpr)

/-- **The higher-order translation of a closed many-sorted formula at a sort.** -/
def translateSorted (formula : SFormula Srt []) (sort : Srt) :
    Term HigherOrder.Constant (HigherOrder.context 0) HigherOrder.predicate :=
  HigherOrder.translate (guard toType formula sort)

/-- **The translation is exact**: in the standard model, it holds at an element exactly when the element has the sort
and the formula holds there. -/
theorem denote_translateSorted (formula : SFormula Srt []) (sort : Srt) (point : Carrier) :
    ((HigherOrder.standardModel T).denote (translateSorted toType formula sort)
      (nowhere (HigherOrder.presentation T)) (ULift.up point)).down ↔
      ∃ typed : T.typed point (toType sort), (restrict T toType).ssat Env.closed formula (lift sort point typed) :=
  (HigherOrder.denote_translate_closed (guard toType formula sort) point).trans (guard_iff_closed formula sort point)

/-- **The translation is built from the basis.** -/
theorem basisOnly_translateSorted (formula : SFormula Srt []) (sort : Srt) :
    BasisOnly (translateSorted toType formula sort) = true :=
  HigherOrder.basisOnly_translate _

end Mettapedia.OSLF.NativeTypes.GeneratedLogic.ManySorted
