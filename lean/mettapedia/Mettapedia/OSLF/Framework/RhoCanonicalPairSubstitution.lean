import Mettapedia.OSLF.Syntax.RhoCanonicalNamePairs
import Mettapedia.OSLF.Framework.RhoGeneratedScopeSubstitution

/-!
# Unordered rho pair construction commutes with full substitution

Both child names are transported by the actual binding-clone substitution.
The constructor comparison holds for arbitrary quotient-valued environments
between contexts. Passing to unordered pairs uses the independently defined
`Sym2.map`, rather than a chosen order of representatives.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.OSLF.Framework.RhoCanonicalPairSubstitution

open Mettapedia.OSLF.Binding
open RhoSchema RhoCanonicalNamePairs RhoQuotationClassFibres
open RhoEquationConstructorControls
open BindingSubstitutionAlgebra FreeBindingTerms RhoGeneratedScopeSubstitution

theorem combine_substitute {source target : Ctx sig}
    (env : Environment sig (TermQ rhoSourceE) source target)
    (first second : Name source) :
    model.substitution.substitute env (combine first second) =
      combine (model.substitution.substitute env first) (model.substitution.substitute env second) := by
  unfold combine
  rw [substitute_quote, substitute_join, substitute_drop, substitute_drop]

theorem pairConstructor_substitute {source target : Ctx sig}
    (env : Environment sig (TermQ rhoSourceE) source target) (pair : Sym2 (Name source)) :
    model.substitution.substitute env (pairConstructor pair) =
      pairConstructor (Sym2.map (model.substitution.substitute env) pair) := by
  refine Sym2.inductionOn pair ?_
  intro first second
  exact combine_substitute env first second

end Mettapedia.OSLF.Framework.RhoCanonicalPairSubstitution
