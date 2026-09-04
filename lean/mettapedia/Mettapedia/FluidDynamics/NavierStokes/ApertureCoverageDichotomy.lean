import Mettapedia.FluidDynamics.NavierStokes.FrozenStrainModel
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# The aperture-coverage dichotomy and the scale-local strain budget

The frequency-localized angular analysis of a vorticity-stretching gate rests
on two mechanisms, each covering a range of angular apertures `θ` around the
compressive strain direction at dyadic frequency `λ`:

* **anisotropic Bernstein** (narrow cones): a cone of aperture
  `θ ≤ λ^{−1/2}` has Fourier-support volume `θ²λ³ ≤ λ²`, so the
  `L² → L^∞` Bernstein factor improves from `λ^{3/2}` to `λ`, and the sector
  is enstrophy-controlled;
* **stretch–diffusion covariance** (wide angles): a wave vector at aperture
  `θ` retains a non-compressed component of size `θλ`, giving diffusive decay
  at rate `ν(θλ)²`, which dominates a local strain `γ` only when
  `ν(θλ)² ≥ γ`, i.e. `θ ≥ √(γ/ν)/λ`.

This file machine-checks the coverage arithmetic of that dichotomy against
the frozen-strain model of `FrozenStrainModel.lean`:

* `pancakeApertureCovered_iff_strain_le`: the two mechanisms tile the whole
  aperture range **iff** the local strain obeys the scale-local budget
  `γ ≤ ν λ`.  (The uncovered band is `anisotropic_coverage_gap`.)
* `gapAperture_diffusionRate_lt_strain`: below the stretch–diffusion
  threshold the diffusive rate `ν(θλ)²` is strictly beaten by the strain, so
  the covariance mechanism's damping premise fails there.
* `gapAperture_bernstein_volume_exceeds_planar_budget`: above the Bernstein
  threshold the cone's support volume exceeds the planar budget `λ²`, so the
  improved Bernstein constant is not available there.
* `frozenStrain_integratedStrain_peakWindow` and
  `frozenStrainAmplification_peak_ge_exp_integratedStrain_sub_one`: over the
  coherent window the frozen-strain pancake packet consumes an integrated
  strain budget of exactly `log g` while amplifying by at least
  `e^{log g − 1}` — the model saturates Grönwall.  A strain hypothesis
  bounding only time-integrated quantities therefore bounds amplification
  only exponentially in itself; a budget usable in a dyadic relaxation
  estimate must be pointwise-in-time composable.

Together these results adjudicate the "narrow ⟹ enstrophy-controlled,
else ⟹ angularly coercive" dichotomy claimed in the 2026-07-03 repair
analysis for the stochastic-Lagrangian route: in the model, that dichotomy
is *equivalent* to the scale-local strain-budget bound `γ ≤ νλ` for the
self-consistent strain, which is exactly the bound the same analysis names
as its remaining burden.  The dichotomy therefore cannot be used to prove
the budget; see `ScaleLocalPancakeStrainBudget` in
`StochasticLagrangian/DyadicPancakeClosure.lean` for the resulting named
open input.

The statements are inequalities between real parameters (apertures,
frequencies, rates); no claim about actual Navier–Stokes solutions is made
in this file.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

section ApertureCoverage

/-- **The aperture dichotomy is equivalent to the scale-local strain
budget.**  Every angular aperture `θ` is covered by one of the two
mechanisms — `θ ≤ λ^{−1/2}` (anisotropic Bernstein) or `θ ≥ √(γ/ν)/λ`
(stretch–diffusion) — **iff** the local strain obeys `γ ≤ ν λ`.

The forward direction is the contrapositive of the uncovered band
`anisotropic_coverage_gap`; the backward direction is that under the budget
the two thresholds meet or cross, so the ranges tile. -/
theorem pancakeApertureCovered_iff_strain_le {γ ν lam : ℝ} (hν : 0 < ν)
    (hlam : 0 < lam) :
    (∀ θ : ℝ, θ ≤ (Real.sqrt lam)⁻¹ ∨ Real.sqrt (γ / ν) / lam ≤ θ) ↔
      γ ≤ ν * lam := by
  constructor
  · intro hcov
    by_contra hstrain
    have hgap : (Real.sqrt lam)⁻¹ < Real.sqrt (γ / ν) / lam :=
      (anisotropic_coverage_gap hν hlam).mpr (not_le.mp hstrain)
    obtain ⟨θ, hθlow, hθhigh⟩ := exists_between hgap
    rcases hcov θ with h | h
    · exact absurd h (not_le.mpr hθlow)
    · exact absurd h (not_le.mpr hθhigh)
  · intro hstrain θ
    have hthresh : Real.sqrt (γ / ν) / lam ≤ (Real.sqrt lam)⁻¹ := by
      by_contra hcon
      exact absurd ((anisotropic_coverage_gap hν hlam).mp (not_le.mp hcon))
        (not_lt.mpr hstrain)
    rcases le_total θ ((Real.sqrt lam)⁻¹) with h | h
    · exact Or.inl h
    · exact Or.inr (le_trans hthresh h)

/-- **In the uncovered band the stretch–diffusion mechanism fails
quantitatively:** at any aperture `θ` below the threshold `√(γ/ν)/λ`, the
diffusive rate `ν(θλ)²` supplied by the retained wave-vector component is
strictly smaller than the strain `γ`, so covariance damping loses to
stretching there. -/
theorem gapAperture_diffusionRate_lt_strain {γ ν lam θ : ℝ} (hν : 0 < ν)
    (hlam : 0 < lam) (hθ : 0 ≤ θ)
    (hupper : θ < Real.sqrt (γ / ν) / lam) :
    ν * (θ * lam) ^ 2 < γ := by
  have hmul : θ * lam < Real.sqrt (γ / ν) := (lt_div_iff₀ hlam).mp hupper
  have hsqrt_pos : 0 < Real.sqrt (γ / ν) :=
    lt_of_le_of_lt (mul_nonneg hθ hlam.le) hmul
  have hratio_pos : 0 < γ / ν := by
    by_contra hcon
    have : Real.sqrt (γ / ν) = 0 :=
      Real.sqrt_eq_zero_of_nonpos (not_lt.mp hcon)
    rw [this] at hsqrt_pos
    exact lt_irrefl 0 hsqrt_pos
  have hsq : (θ * lam) ^ 2 < γ / ν := by
    have h := pow_lt_pow_left₀ hmul (mul_nonneg hθ hlam.le) two_ne_zero
    rwa [Real.sq_sqrt hratio_pos.le] at h
  calc ν * (θ * lam) ^ 2 < ν * (γ / ν) :=
        mul_lt_mul_of_pos_left hsq hν
    _ = γ := by field_simp

/-- **In the uncovered band the anisotropic Bernstein mechanism fails
quantitatively:** at any aperture `θ` above the threshold `λ^{−1/2}`, the
cone's Fourier-support volume `θ²λ³` strictly exceeds the planar budget
`λ²` that yields the improved `L² → L^∞` constant `λ`. -/
theorem gapAperture_bernstein_volume_exceeds_planar_budget {lam θ : ℝ}
    (hlam : 0 < lam) (hlow : (Real.sqrt lam)⁻¹ < θ) :
    lam ^ 2 < θ ^ 2 * lam ^ 3 := by
  have hsqrt_pos : 0 < Real.sqrt lam := Real.sqrt_pos.mpr hlam
  have hinv_nonneg : 0 ≤ (Real.sqrt lam)⁻¹ := inv_nonneg.mpr hsqrt_pos.le
  have hsq : ((Real.sqrt lam)⁻¹) ^ 2 < θ ^ 2 :=
    pow_lt_pow_left₀ hlow hinv_nonneg two_ne_zero
  have hinv_sq : ((Real.sqrt lam)⁻¹) ^ 2 = lam⁻¹ := by
    rw [inv_pow, Real.sq_sqrt hlam.le]
  rw [hinv_sq] at hsq
  have hlam3 : (0 : ℝ) < lam ^ 3 := by positivity
  have h := mul_lt_mul_of_pos_right hsq hlam3
  have hval : lam⁻¹ * lam ^ 3 = lam ^ 2 := by
    field_simp
  rwa [hval] at h

end ApertureCoverage

section IntegratedBudget

/-- Over the coherent window `[0, t*]` with `t* = log g / (2γ)`, the
frozen-strain packet consumes an integrated strain budget of exactly
`∫₀^{t*} 2γ dt = log g`. -/
theorem frozenStrain_integratedStrain_peakWindow {γ g : ℝ} (hγ : 2 * γ ≠ 0) :
    (∫ _ in (0 : ℝ)..(Real.log g / (2 * γ)), (2 * γ)) = Real.log g := by
  rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero,
    div_mul_cancel₀ _ hγ]

/-- **The frozen-strain model saturates Grönwall:** at the peak time the
amplification is at least `e^{B − 1}` where `B = ∫₀^{t*} 2γ dt` is the
integrated strain budget consumed over the window.  Consequently a strain
hypothesis that bounds only time-integrated quantities bounds the
amplification only exponentially in itself — it cannot cap the peak — so a
strain budget usable in a dyadic relaxation estimate must be
pointwise-in-time composable. -/
theorem frozenStrainAmplification_peak_ge_exp_integratedStrain_sub_one
    {ν k₀ γ g : ℝ} (hν : 0 < ν) (hk₀ : 0 < k₀) (hg : 1 < g)
    (hγ : 2 * γ = ν * k₀ ^ 2 * g) :
    Real.exp ((∫ _ in (0 : ℝ)..(Real.log g / (2 * γ)), (2 * γ)) - 1) ≤
      frozenStrainAmplification ν k₀ γ (Real.log g / (2 * γ)) := by
  have hgpos : 0 < g := lt_trans one_pos hg
  have h2γ : (2 * γ) ≠ 0 := by
    rw [hγ]
    positivity
  rw [frozenStrain_integratedStrain_peakWindow h2γ,
    frozenStrainAmplification_peak hν hk₀ hg hγ]
  have hg_exp : g = Real.exp (Real.log g) := (Real.exp_log hgpos).symm
  calc Real.exp (Real.log g - 1) ≤ Real.exp (Real.log g + (1 / g - 1)) := by
        apply Real.exp_le_exp.mpr
        have : 0 ≤ 1 / g := by positivity
        linarith
    _ = g * Real.exp (1 / g - 1) := by
        rw [Real.exp_add, ← hg_exp]

end IntegratedBudget

end NavierStokes
end FluidDynamics
end Mettapedia
