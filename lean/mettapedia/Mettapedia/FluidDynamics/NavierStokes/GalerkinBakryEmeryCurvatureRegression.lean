import Mettapedia.FluidDynamics.NavierStokes.GalerkinBakryEmeryCurvature

/-!
# Regression checks for finite Galerkin Bakry-Emery curvature certificates
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

open scoped BigOperators

namespace Regression
namespace FiniteGalerkin

theorem finite_jet_energy_nonnegative_regression
    {Mode : Type*} [Fintype Mode] (u : Mode → ℝ) :
    0 ≤ NavierStokes.FiniteGalerkin.finiteJetEnergy u :=
  NavierStokes.FiniteGalerkin.finiteJetEnergy_nonneg u

theorem finite_jet_gamma2_lower_bound_regression
    {Mode : Type*} [Fintype Mode]
    {viscosity rho K : ℝ}
    {ricci : Mode → Mode → ℝ}
    {hessianSquare : ((Mode × Mode) → ℝ) → ℝ}
    (hvisc : 0 ≤ viscosity)
    (hK : -K ≤ viscosity * rho)
    (hHess : ∀ H : (Mode × Mode) → ℝ, 0 ≤ hessianSquare H)
    (hRicci :
      ∀ u : Mode → ℝ,
        rho * NavierStokes.FiniteGalerkin.finiteJetEnergy u ≤
          NavierStokes.FiniteGalerkin.finiteJetRicciQuadratic ricci u)
    (H : (Mode × Mode) → ℝ) (u : Mode → ℝ) :
    -K * NavierStokes.FiniteGalerkin.finiteJetGamma viscosity u ≤
      NavierStokes.FiniteGalerkin.finiteJetGamma2
        viscosity ricci hessianSquare H u :=
  NavierStokes.FiniteGalerkin.finiteJetGamma2_lowerBound
    hvisc hK hHess hRicci H u

theorem abelian_translation_jet_gamma2_zero_regression
    (H :
      (NavierStokes.FiniteGalerkin.AbelianTranslationJet.Mode ×
        NavierStokes.FiniteGalerkin.AbelianTranslationJet.Mode) → ℝ)
    (u : NavierStokes.FiniteGalerkin.AbelianTranslationJet.Mode → ℝ) :
    -(0 : ℝ) *
        NavierStokes.FiniteGalerkin.finiteJetGamma 1 u ≤
      NavierStokes.FiniteGalerkin.finiteJetGamma2 1
        NavierStokes.FiniteGalerkin.AbelianTranslationJet.ricci
        NavierStokes.FiniteGalerkin.AbelianTranslationJet.hessianSquare H u :=
  NavierStokes.FiniteGalerkin.AbelianTranslationJet.gamma2_lowerBound_zero H u

theorem finite_galerkin_realization_cd_regression
    {G : BakryEmeryGronwallFramework}
    (R : NavierStokes.FiniteGalerkin.FiniteGalerkinBochnerRealization G) :
    G.base.CDMinusInfinity R.K :=
  R.curvatureDimension

theorem finite_galerkin_realization_local_input_regression
    {G : BakryEmeryGronwallFramework}
    (R : NavierStokes.FiniteGalerkin.FiniteGalerkinBochnerRealization G) :
    LocalSGCurvatureDimensionOpenInput G R.K :=
  R.localCurvatureInput

theorem finite_galerkin_realization_gradient_regression
    {G : BakryEmeryGronwallFramework}
    (R : NavierStokes.FiniteGalerkin.FiniteGalerkinBochnerRealization G)
    {t : ℝ} (ht : 0 ≤ t)
    (f : G.base.Func) (x : G.base.Point) :
    G.base.eval x (G.base.gammaSelf (G.base.P t f)) ≤
      Real.exp (2 * R.K * t) *
        G.base.eval x (G.base.P t (G.base.gammaSelf f)) :=
  R.gradientEstimate ht f x

theorem finite_galerkin_ns_identity_gradient_regression
    {G : BakryEmeryGronwallFramework}
    (D : NavierStokes.FiniteGalerkin.FiniteGalerkinNSBakryEmeryReduction G) :
    ∀ t : ℝ, 0 ≤ t → t ≤ D.T →
      G.base.eval D.id (G.base.gammaSelf (G.base.P t D.phi)) ≤
        Real.exp (2 * D.realization.K * t) * D.Cphi ^ 2 :=
  D.identityGradientBound

theorem finite_galerkin_ns_bkm_gate_regression
    {G : BakryEmeryGronwallFramework}
    (D : NavierStokes.FiniteGalerkin.FiniteGalerkinNSBakryEmeryReduction G) :
    D.gate.bkmGate :=
  D.abstractBKMGate

theorem finite_galerkin_ns_packet_regression
    {G : BakryEmeryGronwallFramework}
    (D : NavierStokes.FiniteGalerkin.FiniteGalerkinNSBakryEmeryReduction G) :
    (∀ t : ℝ, 0 ≤ t → t ≤ D.T →
      G.base.eval D.id (G.base.gammaSelf (G.base.P t D.phi)) ≤
        Real.exp (2 * D.realization.K * t) * D.Cphi ^ 2) ∧
      D.gate.logHeatEnergyBound ∧
        D.gate.vorticityBound ∧
          D.gate.bkmIntegralFinite ∧
            D.gate.bkmGate ∧
              LocalSGCurvatureDimensionOpenInput G D.realization.K :=
  D.reductionPacket

end FiniteGalerkin
end Regression

end NavierStokes
end FluidDynamics
end Mettapedia
