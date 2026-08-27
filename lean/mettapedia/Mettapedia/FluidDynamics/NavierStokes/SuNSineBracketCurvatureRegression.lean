import Mettapedia.FluidDynamics.NavierStokes.SuNSineBracketCurvature

/-!
# Regression checks for bi-invariant su(N) trace-metric curvature rows
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

namespace Regression
namespace SuNComputedCurvature

open NavierStokes.FiniteGalerkin.SuNComputedCurvature

theorem kN_table_exact_regression :
    kNTable =
      [ (2, 3, 1, 0)
      , (3, 8, (3 : ℝ) / 2, 0)
      , (4, 15, 2, 0)
      , (5, 24, (5 : ℝ) / 2, 0)
      , (6, 35, 3, 0) ] :=
  kNTable_exact

theorem metric_scope_regression :
    metricScope =
      "bi-invariant su(N) trace/Killing curvature sanity check only" :=
  metricScope_exact

theorem rho_eq_matrixN_over_two_regression (r : Row) :
    rho r = (matrixN r : ℝ) / 2 :=
  rho_eq_matrixN_over_two r

theorem rho_uniform_lower_bound_regression (r : Row) :
    (1 : ℝ) ≤ rho r :=
  rho_uniform_lower_bound r

theorem computed_finite_jet_gamma2_lower_bound_regression
    (r : Row) (H : (Mode r × Mode r) → ℝ) (u : Mode r → ℝ) :
    -(cdK r) * FiniteGalerkin.finiteJetGamma 1 u ≤
      FiniteGalerkin.finiteJetGamma2 1 (ricci r) (hessianSquare r) H u :=
  computedFiniteJetGamma2_lowerBound r H u

def bochner_data_to_finite_realization_regression
    {G : BakryEmeryGronwallFramework} {r : Row}
    (D : BochnerData G r) :
    FiniteGalerkin.FiniteGalerkinBochnerRealization G :=
  D.toFiniteGalerkinBochnerRealization

theorem bochner_data_curvature_dimension_regression
    {G : BakryEmeryGronwallFramework} {r : Row}
    (D : BochnerData G r) :
    G.base.CDMinusInfinity (cdK r) :=
  D.curvatureDimension

theorem bochner_data_gradient_estimate_regression
    {G : BakryEmeryGronwallFramework} {r : Row}
    (D : BochnerData G r)
    {t : ℝ} (ht : 0 ≤ t)
    (f : G.base.Func) (x : G.base.Point) :
    G.base.eval x (G.base.gammaSelf (G.base.P t f)) ≤
      Real.exp (2 * cdK r * t) *
        G.base.eval x (G.base.P t (G.base.gammaSelf f)) :=
  D.gradientEstimate ht f x

end SuNComputedCurvature
end Regression

end NavierStokes
end FluidDynamics
end Mettapedia
