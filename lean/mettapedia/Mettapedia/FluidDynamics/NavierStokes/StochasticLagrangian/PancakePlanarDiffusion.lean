import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakePlanarSpectralDefect

/-!
# Signed diffusion production for the planar spectral defect

The square root in the actual spectral defect contributes nonnegative
curvature. The product with squared vorticity also contributes a mixed
gradient term, whose sign is not fixed. The exact second-derivative
formula below keeps both terms. Completing the square gives an explicit
gradient cost, not a free dissipativity assertion.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PancakePlanarDiffusion

open scoped Topology
open Filter PancakePlanarSpectralDefect

def planarDefectRate (a b w da db dw : ℝ) : ℝ :=
  (a * da + b * db) / Real.sqrt (a ^ 2 + b ^ 2) * w ^ 2 +
    2 * Real.sqrt (a ^ 2 + b ^ 2) * w * dw

theorem hasDerivAt_planarDefect (a b w : ℝ → ℝ) (da db dw t : ℝ)
    (ha : HasDerivAt a da t) (hb : HasDerivAt b db t) (hw : HasDerivAt w dw t)
    (hne : a t ^ 2 + b t ^ 2 ≠ 0) :
    HasDerivAt (fun s ↦ planarDefect (a s) (b s) (w s))
      (planarDefectRate (a t) (b t) (w t) da db dw) t := by
  have h := (((ha.pow 2).add (hb.pow 2)).sqrt hne).mul (hw.pow 2)
  apply h.congr_deriv
  simp only [planarDefectRate, Pi.add_apply, Pi.pow_apply]
  ring

/-- A normalized second jet of the actual planar defect. The formula
contains the mixed term `4 * da * dw`, which need not be nonnegative. -/
theorem hasDerivAt_deriv_planarDefect_at_normalized
    (a b w da db dw : ℝ → ℝ) (dda ddb ddw t : ℝ)
    (ha : ∀ s, HasDerivAt a (da s) s)
    (hb : ∀ s, HasDerivAt b (db s) s)
    (hw : ∀ s, HasDerivAt w (dw s) s)
    (hda : HasDerivAt da dda t) (hdb : HasDerivAt db ddb t)
    (hdw : HasDerivAt dw ddw t)
    (hat : a t = 1) (hbt : b t = 0) (hwt : w t = 1) :
    HasDerivAt (deriv (fun s ↦ planarDefect (a s) (b s) (w s)))
      (dda + db t ^ 2 + 4 * da t * dw t + 2 * dw t ^ 2 + 2 * ddw) t := by
  have hne : a t ^ 2 + b t ^ 2 ≠ 0 := by simp [hat, hbt]
  have hsqrt := ((ha t).pow 2 |>.add ((hb t).pow 2)).sqrt hne
  have hsqrtval : Real.sqrt (a t ^ 2 + b t ^ 2) = 1 := by simp [hat, hbt]
  have hdroot : HasDerivAt (fun s ↦ Real.sqrt (a s ^ 2 + b s ^ 2)) (da t) t := by
    simpa [hat, hbt] using hsqrt
  have hn := ((ha t).mul hda).add ((hb t).mul hdb)
  have hquot := hn.div hdroot (by rw [hsqrtval]; norm_num)
  have hrate := (hquot.mul ((hw t).pow 2)).add
    (((hdroot.const_mul 2).mul (hw t)).mul hdw)
  have hrate' : HasDerivAt
      (fun s ↦ planarDefectRate (a s) (b s) (w s) (da s) (db s) (dw s))
      (dda + db t ^ 2 + 4 * da t * dw t + 2 * dw t ^ 2 + 2 * ddw) t := by
    apply hrate.congr_deriv
    simp only [Pi.add_apply, Pi.mul_apply, Pi.div_apply, Pi.pow_apply, hat, hbt, hwt]
    norm_num
    ring
  apply hrate'.congr_of_eventuallyEq
  have hcont : ContinuousAt (fun s ↦ a s ^ 2 + b s ^ 2) t :=
    ((ha t).continuousAt.pow 2).add ((hb t).continuousAt.pow 2)
  filter_upwards [hcont.eventually_ne hne] with s hs
  exact (hasDerivAt_planarDefect a b w (da s) (db s) (dw s) s
    (ha s) (hb s) (hw s) hs).deriv

/-- The contribution in one spatial direction, when the planar strain
has `b = 0` and positive eigenvalue `a`. This is minus the Hessian term
in the heat chain rule. -/
def directionalDiffusionProduction (a w da db dw : ℝ) : ℝ :=
  -(w ^ 2 * db ^ 2 / a) - 4 * w * da * dw - 2 * a * dw ^ 2

theorem directionalDiffusionProduction_complete_square (a w da db dw : ℝ)
    (ha : a ≠ 0) :
    directionalDiffusionProduction a w da db dw =
      2 * w ^ 2 * da ^ 2 / a - w ^ 2 * db ^ 2 / a -
        2 * a * (dw + w * da / a) ^ 2 := by
  unfold directionalDiffusionProduction
  field_simp [ha]
  ring

/-- Diffusion has a paid gradient bound, not an unconditional good sign. -/
theorem directionalDiffusionProduction_le (a w da db dw : ℝ) (ha : 0 < a) :
    directionalDiffusionProduction a w da db dw ≤
      2 * w ^ 2 * da ^ 2 / a - w ^ 2 * db ^ 2 / a := by
  rw [directionalDiffusionProduction_complete_square a w da db dw ha.ne']
  nlinarith [sq_nonneg (dw + w * da / a)]

/-- Compatibility of the first jets for a planar divergence-free velocity:
`wx = 2 (bx - ay)` and `wy = -2 (ax + by)`. Even these physical
constraints do not restore a nonpositive heat-chain-rule production. -/
theorem compatible_diffusionProduction_positive (k : ℝ) :
    directionalDiffusionProduction 1 1 (9 * k) (-4 * k) (-8 * k) +
      directionalDiffusionProduction 1 1 0 (-8 * k) (-2 * k) = 72 * k ^ 2 := by
  unfold directionalDiffusionProduction
  ring

theorem compatible_jet_identities (k : ℝ) :
    -8 * k = 2 * (-4 * k - 0) ∧ -2 * k = -2 * (9 * k + -8 * k) := by
  constructor <;> ring

end Mettapedia.FluidDynamics.NavierStokes.PancakePlanarDiffusion
