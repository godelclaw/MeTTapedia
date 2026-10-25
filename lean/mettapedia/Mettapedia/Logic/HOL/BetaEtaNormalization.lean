import Mettapedia.Logic.HOL.EtaPostponement

/-!
# Strong normalization of typed beta/eta reduction

Strong eta postponement retains genuine beta progress. Combined with the
existing beta strong-normalization theorem and eta's decreasing constructor
measure, the shared relation theorem establishes termination of every
interleaving on intrinsically typed HOL terms.

The relation leaves named constants opaque. Definition unfolding and prefix
type-level computation need separate hypotheses and comparisons.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HOL.BetaEtaNormalization

open EtaConversion

universe u v
variable {Base : Type u} {Const : Ty Base → Type v}
variable {gamma : Ctx Base} {type : Ty Base}

theorem stronglyNormalizing (term : Term Const gamma type) :
    Acc (fun later earlier => BetaEtaStep earlier later) term :=
  Mettapedia.Logic.Relation.stronglyNormalizing_union_of_postponement
    BetaNormalization.stronglyNormalizing EtaNormalization.stronglyNormalizing
    (fun eta beta => EtaPostponement.eta_beta_trans eta beta) term

#print axioms stronglyNormalizing

end Mettapedia.Logic.HOL.BetaEtaNormalization
