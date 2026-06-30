import Mettapedia.FluidDynamics.NavierStokes.BakryEmeryConditionalReduction

/-!
# Regression checks for the abstract Bakry-Emery conditional reduction
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

namespace Regression

theorem bakry_emery_gamma2_bochner_identity_regression
    (M : CarreDuChampSemigroup) (f : M.Func) :
    M.gamma2 f =
      (1 / 2 : ℝ) •
        (M.L (M.gammaSelf f) - (2 : ℝ) • M.Gamma f (M.L f)) :=
  M.gamma2_bochner_identity f

theorem bakry_emery_interpolation_derivative_identity_func_regression
    (M : CarreDuChampSemigroup) (t s : ℝ) (f : M.Func) :
    M.timeDeriv (fun r => M.beInterpolation t r f) s =
      (2 : ℝ) • M.P s (M.gamma2 (M.P (t - s) f)) :=
  M.interpolationDerivativeIdentity_func t s f

theorem bakry_emery_interpolation_derivative_identity_regression
    (M : CarreDuChampSemigroup) (t : ℝ) (f : M.Func) (x : M.Point) :
    M.InterpolationDerivativeIdentity t f x :=
  M.interpolationDerivativeIdentity t f x

theorem bakry_emery_interpolation_lower_bound_from_cd_regression
    (M : CarreDuChampSemigroup) {K t : ℝ} {f : M.Func} {x : M.Point}
    (hCD : M.CDMinusInfinity K) :
    M.InterpolationDerivativeLowerBound K t f x :=
  M.interpolationDerivativeLowerBound_of_CD hCD

theorem bakry_emery_variable_cd_lower_bound_regression
    (M : CarreDuChampSemigroup) {rho : M.Point → ℝ} {rhoMin : ℝ}
    (hCD : M.CDVariableInfinity rho)
    (hmin : ∀ x : M.Point, rhoMin ≤ rho x) :
    M.CDMinusInfinity (-rhoMin) :=
  M.cdMinusInfinity_of_cdVariable_lowerBound hCD hmin

theorem bakry_emery_weighted_interpolation_mono_regression
    (M : CarreDuChampSemigroup) {K t : ℝ} {f : M.Func} {x : M.Point}
    (hK : 0 ≤ K) (ht : 0 ≤ t)
    (hIdentity : M.InterpolationDerivativeIdentity t f x)
    (hLower : M.InterpolationDerivativeLowerBound K t f x) :
    MonotoneOn (M.weightedBEInterpolation K t f x) (Set.Icc 0 t) :=
  M.weightedBEInterpolation_monoOn hK ht hIdentity hLower

theorem bakry_emery_gronwall_from_interpolation_regression
    (M : CarreDuChampSemigroup) {K t : ℝ} {f : M.Func} {x : M.Point}
    (hK : 0 ≤ K) (ht : 0 ≤ t)
    (hIdentity : M.InterpolationDerivativeIdentity t f x)
    (hLower : M.InterpolationDerivativeLowerBound K t f x) :
    M.eval x (M.gammaSelf (M.P t f)) ≤
      Real.exp (2 * K * t) *
        M.eval x (M.P t (M.gammaSelf f)) :=
  M.gronwallFromInterpolation hK ht hIdentity hLower

theorem bakry_emery_gradient_estimate_regression
    (G : BakryEmeryGronwallFramework) {K t : ℝ}
    (hK : 0 ≤ K) (ht : 0 ≤ t)
    (hCD : G.base.CDMinusInfinity K)
    (f : G.base.Func) (x : G.base.Point) :
    G.base.eval x (G.base.gammaSelf (G.base.P t f)) ≤
      Real.exp (2 * K * t) *
        G.base.eval x (G.base.P t (G.base.gammaSelf f)) :=
  bakryEmeryGradientEstimate G hK ht hCD f x

theorem bakry_emery_variable_lower_bound_gradient_regression
    (G : BakryEmeryGronwallFramework) {rho : G.base.Point → ℝ}
    {rhoMin t : ℝ}
    (hrhoMin_nonpos : rhoMin ≤ 0) (ht : 0 ≤ t)
    (hCD : G.base.CDVariableInfinity rho)
    (hmin : ∀ x : G.base.Point, rhoMin ≤ rho x)
    (f : G.base.Func) (x : G.base.Point) :
    G.base.eval x (G.base.gammaSelf (G.base.P t f)) ≤
      Real.exp (2 * (-rhoMin) * t) *
        G.base.eval x (G.base.P t (G.base.gammaSelf f)) :=
  bakryEmeryGradientEstimate_variableLowerBound G
    hrhoMin_nonpos ht hCD hmin f x

theorem two_point_chain_cd_zero_regression :
    TwoPointChain.semigroup.CDMinusInfinity 0 :=
  TwoPointChain.cdZero

theorem two_point_chain_unit_slope_nonconstant_regression :
    TwoPointChain.unitSlope 0 ≠ TwoPointChain.unitSlope 1 :=
  TwoPointChain.unitSlope_nonconstant

theorem two_point_chain_gradient_estimate_fires_regression :
    TwoPointChain.semigroup.eval (0 : TwoPointChain.State)
        (TwoPointChain.semigroup.gammaSelf
          (TwoPointChain.semigroup.P 1 TwoPointChain.unitSlope)) ≤
      Real.exp (2 * (0 : ℝ) * 1) *
        TwoPointChain.semigroup.eval (0 : TwoPointChain.State)
          (TwoPointChain.semigroup.P 1
            (TwoPointChain.semigroup.gammaSelf TwoPointChain.unitSlope)) :=
  TwoPointChain.unitSlope_bakryEmeryEstimate_fires

theorem two_point_chain_gradient_estimate_strict_regression :
    TwoPointChain.semigroup.eval (0 : TwoPointChain.State)
        (TwoPointChain.semigroup.gammaSelf
          (TwoPointChain.semigroup.P 1 TwoPointChain.unitSlope)) <
      TwoPointChain.semigroup.eval (0 : TwoPointChain.State)
        (TwoPointChain.semigroup.P 1
          (TwoPointChain.semigroup.gammaSelf TwoPointChain.unitSlope)) :=
  TwoPointChain.unitSlope_bakryEmeryEstimate_strict

theorem local_sg_variable_curvature_constant_cd_regression
    {G : BakryEmeryGronwallFramework}
    (H : LocalSGVariableCurvatureIntegratedOpenInput G) :
    G.base.CDMinusInfinity (-H.rhoMin) :=
  H.constantCurvatureDimension

theorem local_sg_variable_curvature_gradient_regression
    {G : BakryEmeryGronwallFramework}
    (H : LocalSGVariableCurvatureIntegratedOpenInput G)
    {t : ℝ} (ht : 0 ≤ t)
    (f : G.base.Func) (x : G.base.Point) :
    G.base.eval x (G.base.gammaSelf (G.base.P t f)) ≤
      Real.exp (2 * (-H.rhoMin) * t) *
        G.base.eval x (G.base.P t (G.base.gammaSelf f)) :=
  H.gradientEstimate ht f x

theorem ns_bakry_emery_conditional_gradient_regression
    {G : BakryEmeryGronwallFramework}
    (D : NSBakryEmeryConditionalReduction G) :
    ∀ t : ℝ, 0 ≤ t → t ≤ D.T →
      G.base.eval D.id (G.base.gammaSelf (G.base.P t D.phi)) ≤
        Real.exp (2 * D.K * t) * D.Cphi ^ 2 :=
  D.identityGradientBound

theorem ns_bakry_emery_conditional_bkm_gate_regression
    {G : BakryEmeryGronwallFramework}
    (D : NSBakryEmeryConditionalReduction G) :
    D.gate.bkmGate :=
  D.abstractBKMGate

theorem ns_bakry_emery_exact_open_input_regression
    {G : BakryEmeryGronwallFramework}
    (D : NSBakryEmeryConditionalReduction G) :
    LocalSGCurvatureDimensionOpenInput G D.K :=
  D.exactOpenInput

theorem ns_bakry_emery_conditional_packet_regression
    {G : BakryEmeryGronwallFramework}
    (D : NSBakryEmeryConditionalReduction G) :
    (∀ t : ℝ, 0 ≤ t → t ≤ D.T →
      G.base.eval D.id (G.base.gammaSelf (G.base.P t D.phi)) ≤
        Real.exp (2 * D.K * t) * D.Cphi ^ 2) ∧
      D.gate.logHeatEnergyBound ∧
        D.gate.vorticityBound ∧
          D.gate.bkmIntegralFinite ∧
            D.gate.bkmGate ∧
              LocalSGCurvatureDimensionOpenInput G D.K :=
  D.reductionPacket

end Regression

end NavierStokes
end FluidDynamics
end Mettapedia
