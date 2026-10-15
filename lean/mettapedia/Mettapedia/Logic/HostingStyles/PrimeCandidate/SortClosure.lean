import Mettapedia.Logic.HostingStyles.PrimeCandidate.LambdaPiUnion
import Mettapedia.Logic.HostingStyles.ContextReadings.PresentedReadings

/-!
# Two ways to say that some sorts of a language are closed

`ContextReadings.sortsClosed lang sorts` says that every constructor of a
listed sort takes plain arguments of listed sorts.  `SortsFrom lang smaller
sorts` says that the constructors of the listed sorts are constructors of a
smaller language and take arguments whose types end at listed sorts; binders
are allowed.  This module relates them.

* Sorts closed with plain arguments are sorts whose constructors are those of
  the language itself (`sortsFrom_self_of_sortsClosed`).
* The converse fails where a constructor binds: the sorts of the λΠ-calculus
  modulo in `dkLanguage` (`dkLanguage_lfSorts_from_self`,
  `dkLanguage_lfSorts_not_sortsClosed`).
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HostingStyles.PrimeCandidate

open Mettapedia.GSLT
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.Dedukti.Language
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.Logic.HostingStyles.ContextReadings (sortsClosed takesOnly)

/-- **Sorts closed with plain arguments are sorts whose constructors are those
of the language itself.** -/
theorem sortsFrom_self_of_sortsClosed {lang : LanguageDef} {sorts : List String}
    (closed : sortsClosed lang sorts = true) : SortsFrom lang lang sorts := by
  intro rule member category
  refine ⟨member, fun parameter inParams expected expectedType => ?_⟩
  have test := List.all_eq_true.mp closed rule member
  have listed : sorts.contains rule.category = true := List.contains_iff_mem.mpr category
  simp only [listed, Bool.not_true, Bool.false_or] at test
  have plain := List.all_eq_true.mp test parameter inParams
  cases parameter with
  | simple name type =>
      cases type with
      | base sort =>
          obtain rfl : TypeExpr.base sort = expected := Option.some.inj expectedType
          exact plain
      | arrow _ _ => cases plain
      | multiBinder _ => cases plain
      | collection _ _ => cases plain
  | abstractionNamed _ _ _ => cases plain
  | multiAbstractionNamed _ _ _ => cases plain

/-- **Positive**: the sorts of the calculus in its own language, where two
constructors bind. -/
theorem dkLanguage_lfSorts_from_self (names : List String) (rules : List Dedukti.RewriteRule) :
    SortsFrom (dkLanguage names rules) (dkLanguage names rules) lfSorts :=
  (dkLanguage_carries names rules).sorts

/-- **Negative**: they are not closed with plain arguments. -/
theorem dkLanguage_lfSorts_not_sortsClosed :
    sortsClosed (dkLanguage [] []) lfSorts = false := by
  decide

#print axioms sortsFrom_self_of_sortsClosed
#print axioms dkLanguage_lfSorts_not_sortsClosed

end Mettapedia.Logic.HostingStyles.PrimeCandidate
