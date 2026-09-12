import Mettapedia.Analysis.RadialRieszTensor
import Mettapedia.Analysis.SignedRadialStretchEvolution

/-! # Material derivative of the constructed radial Riesz coefficient

The coefficient is differentiated from its actual scalar potential. This
is a local identity at nonzero separation, not a bound uniform in cutoff
or a justification for differentiating a periodic image series.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.Analysis.RadialRieszRegularization

open Filter
open scoped Topology ContDiff RealInnerProductSpace
variable {d : ℕ}
local notation "Rd" => EuclideanSpace ℝ (Fin d)

theorem contDiff_tensor (N : ℕ) : ContDiff ℝ ∞ (tensor (d := d) N) := by
  unfold tensor
  apply ContDiff.sum
  intro i _
  apply ContDiff.sum
  intro j _
  exact (Complex.reCLM.contDiff.comp ((kernel N i j).smooth ⊤)).smul contDiff_const

def radialCoefficientSlope (N : ℕ) (e x : Rd) : ℝ :=
  -((2 * Real.pi) ^ 2)⁻¹ *
    (8 * deriv (deriv (deriv (RadialHessian.profile (realPotential N) e))) (‖x‖ ^ 2))

theorem hasDerivAt_radialCoefficient (N : ℕ) (e : Rd) {h : ℝ → Rd} {dh : Rd} {t : ℝ}
    (hh : HasDerivAt h dh t) (ht : h t ≠ 0) :
    HasDerivAt (fun τ ↦ radialCoefficient N e (h τ))
      (radialCoefficientSlope N e (h t) * ⟪h t, dh⟫) t := by
  have hg := RadialHessian.contDiffAt_profile ((realPotential (d := d) N).smooth ⊤) e
    (pow_ne_zero 2 (norm_ne_zero_iff.mpr ht))
  have hd := (hg.derivWithin (m := ∞) (by simp)).derivWithin (m := ∞) (by simp)
  have hr := ((hd.differentiableAt (by simp)).hasDerivAt.comp t hh.norm_sq).const_mul 4
  have hk := hr.const_mul (-((2 * Real.pi) ^ 2)⁻¹)
  apply hk.congr_deriv
  simp only [radialCoefficientSlope]
  ring

theorem hasDerivAt_signedDensity (N n : ℕ) (e : EuclideanSpace ℝ (Fin 3))
    {a b h : ℝ → EuclideanSpace ℝ (Fin 3)} {da db dh : EuclideanSpace ℝ (Fin 3)} {t : ℝ}
    (ha : HasDerivAt a da t) (hb : HasDerivAt b db t) (hh : HasDerivAt h dh t) (ht : h t ≠ 0) :
    HasDerivAt (fun τ ↦ SignedRadialStretch.density (2 * (n + 1))
      (radialCoefficient N e (h τ)) (a τ) (b τ) (h τ))
      (SignedRadialStretch.rate n (radialCoefficient N e (h t))
        (radialCoefficientSlope N e (h t) * ⟪h t, dh⟫) (a t) (b t) (h t) da db dh) t :=
  SignedRadialStretch.hasDerivAt_density n ha hb hh (hasDerivAt_radialCoefficient N e hh ht)

theorem hasDerivAt_pairedStretch_tensor (N n : ℕ) (e : EuclideanSpace ℝ (Fin 3)) (he : ‖e‖ = 1)
    {a b h : ℝ → EuclideanSpace ℝ (Fin 3)} {da db dh : EuclideanSpace ℝ (Fin 3)} {t : ℝ}
    (ha : HasDerivAt a da t) (hb : HasDerivAt b db t) (hh : HasDerivAt h dh t) (ht : h t ≠ 0) :
    HasDerivAt (fun τ ↦ SignedCrossKernel.pairedStretch (2 * (n + 1)) (tensor N (h τ)) (a τ) (b τ))
      (SignedRadialStretch.rate n (radialCoefficient N e (h t))
        (radialCoefficientSlope N e (h t) * ⟪h t, dh⟫) (a t) (b t) (h t) da db dh) t := by
  apply (hasDerivAt_signedDensity N n e ha hb hh ht).congr_of_eventuallyEq
  filter_upwards [hh.continuousAt.eventually (eventually_ne_nhds ht)] with τ hτ
  exact pairedStretch_tensor N (2 * (n + 1)) e he hτ (a τ) (b τ)

end Mettapedia.Analysis.RadialRieszRegularization
