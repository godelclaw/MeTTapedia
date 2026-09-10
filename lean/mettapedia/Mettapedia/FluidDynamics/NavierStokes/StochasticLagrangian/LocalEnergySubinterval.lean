import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalKineticEnergy

/-! # Initial-energy payments on interior time intervals -/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.LocalEnergySubinterval

open MeasureTheory
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeCurlOutputTail
open PancakeLocalInfiniteVelocity InfiniteConvectionEnergy LocalKineticEnergy
open PancakeGalerkinKineticEnergy

/-- Restricting the time interval does not increase the nonnegative
energy-enstrophy payment. The dominated cost may have either sign. -/
theorem integral_le_of_energy_enstrophy_majorant {nu T B : ℝ} {u₀ : FourierVelocity}
    (s : LocalInfiniteVelocitySolution nu u₀ T B) (hnu : 0 < nu)
    (g : Wavevector → ℝ) (hg : ∀ q, 0 ≤ g q) (hSum : Summable g)
    (hu : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ q, fourierMoment 2 (s.coefficients t) q ≤ g q)
    (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ T)
    (f : ℝ → ℝ) (C : ℝ) (hC : 0 ≤ C) (hf : IntervalIntegrable f volume a b)
    (hdom : ∀ᵐ τ ∂volume.restrict (Set.Ioo a b), f τ ≤ C *
      (kineticEnergy (s.coefficients τ) * kineticEnergy (fourierCurl (s.coefficients τ)))) :
    (∫ τ in a..b, f τ) ≤ C * kineticEnergy u₀ ^ 2 / (4 * nu) := by
  have hE := (continuousOn_energy s g hg hSum hu).mul
    (continuousOn_enstrophy s g hg hSum hu)
  have hi : IntervalIntegrable (fun τ ↦ kineticEnergy (s.coefficients τ) *
      kineticEnergy (fourierCurl (s.coefficients τ))) volume 0 b :=
    ContinuousOn.intervalIntegrable_of_Icc (ha.trans hab)
      (hE.mono (fun _ hτ ↦ ⟨hτ.1, hτ.2.trans hb⟩))
  have hiab : IntervalIntegrable (fun τ ↦ kineticEnergy (s.coefficients τ) *
      kineticEnergy (fourierCurl (s.coefficients τ))) volume a b :=
    ContinuousOn.intervalIntegrable_of_Icc hab
      (hE.mono (fun _ hτ ↦ ⟨ha.trans hτ.1, hτ.2.trans hb⟩))
  rw [restrict_Ioo_eq_restrict_Icc] at hdom
  have hle := intervalIntegral.integral_mono_ae_restrict hab hf (hiab.const_mul C) hdom
  rw [intervalIntegral.integral_const_mul] at hle
  have hsub := intervalIntegral.integral_mono_interval ha hab (le_refl b)
    (Filter.Eventually.of_forall (fun τ ↦ mul_nonneg
      (kineticEnergy_nonneg _) (kineticEnergy_nonneg _))) hi
  apply hle.trans ((mul_le_mul_of_nonneg_left hsub hC).trans ?_)
  apply (le_div_iff₀ (by positivity : 0 < 4 * nu)).mpr
  have hpay := mul_le_mul_of_nonneg_left
    (energy_enstrophy_integral_le_initial s g hg hSum hu b ⟨ha.trans hab, hb⟩) hC
  nlinarith

end Mettapedia.FluidDynamics.NavierStokes.LocalEnergySubinterval
