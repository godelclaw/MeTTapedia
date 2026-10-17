import Mettapedia.UniversalAI.UniversalHyperprior.DyadicApproximation
import Mettapedia.UniversalAI.UniversalHyperprior.DyadicArithmetic

/-!
# Unresolved posterior-mean approximation obligation

The completed realization, arithmetic error bounds, and accuracy-controlled
limits now live in `DyadicApproximation`, which does not import unfinished
posterior algorithms. This legacy module retains only the unresolved
`dyadicPosteriorMean_approx` obligation against `DyadicArithmetic`; it is not
part of the completed approximation theory.

The former precision-free posterior convergence claim is false: constant exact
inputs can have a non-dyadic posterior mean, whereas any fixed output remains
a single dyadic value. `DyadicApproximationControls` proves that obstruction
and the contrasting convergence of accuracy-parameterized division.
-/

namespace Mettapedia.UniversalAI.UniversalHyperprior.Dyadic

open Mettapedia.UniversalAI.UniversalHyperprior
open Mettapedia.PLN.Bridges.ProbabilityTheory.EvidenceNormalGamma

theorem dyadicPosteriorMean_approx (ctx : DyadicContext) (ev : DyadicEvidence)
    (ctx_real : NormalNormalContext) (ev_real : NormalGammaEvidence)
    (h_ctx : ctx.toReal = ctx_real)
    (h_ev : ev.toReal = ev_real)
    (h_n : ev.n ≠ 0) :
    |(dyadicPosteriorMean ctx ev).toReal -
     posteriorMean ctx_real ev_real| ≤
    2 ^ (-(min ctx.μ₀_denom_pow ev.mean_denom_pow : ℤ)) := by
  sorry  -- TODO: Prove using error propagation through weighted average

end Mettapedia.UniversalAI.UniversalHyperprior.Dyadic
