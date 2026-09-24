import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakePlanarSpectralDefect

/-!
# Exact two-shear diffusion algebra

For `u = (U(y), V(x), 0)`, write `U' = 2 f` and `V' = -2 g`.
The strain has off-diagonal entry `f-g`, and the normal vorticity is
`-2(f+g)`. Its actual spectral defect is `4 |f-g| (f+g)^2`.

Pairing opposite signs of the fast shear reduces this defect to a
piecewise cubic. Its fast-amplitude derivative has a negative leading
term. This is the algebra behind a possible *increase* of the integrated
defect when heat removes a small fast shear. No spatial integral or
unconditional Navier--Stokes estimate is asserted in this module.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PancakeTwoShearDiffusion

open PancakePlanarSpectralDefect PancakeSpectralDefectEvolution
open scoped Topology
open Filter

def shearDefect (f g : ℝ) : ℝ := 4 * |f - g| * (f + g) ^ 2

theorem topSpectralDefect_twoShear (f g : ℝ) :
    topSpectralDefect (planarStrain 0 (f - g)) (normalVorticity (-2 * (f + g))) =
      shearDefect f g := by
  rw [topSpectralDefect, spectralDefect, topEigenvalue_offDiagonal,
    normalVorticity_norm_sq]
  change _ - inner ℝ (normalVorticity (-2 * (f + g)))
    (planarOperator 0 (f - g) (normalVorticity (-2 * (f + g)))) = _
  rw [planarOperator_normalVorticity, inner_zero_right, sub_zero]
  unfold shearDefect
  ring

def pairedDefect (f g : ℝ) : ℝ := (shearDefect f g + shearDefect (-f) g) / 2

theorem pairedDefect_small (f g : ℝ) (hf : 0 ≤ f) (hfg : f ≤ g) :
    pairedDefect f g = 4 * g * (g ^ 2 - f ^ 2) := by
  have hg : 0 ≤ g := hf.trans hfg
  rw [pairedDefect, shearDefect, shearDefect,
    abs_of_nonpos (sub_nonpos.mpr hfg), abs_of_nonpos (by linarith : -f - g ≤ 0)]
  ring

theorem pairedDefect_large (f g : ℝ) (hg : 0 ≤ g) (hgf : g ≤ f) :
    pairedDefect f g = 4 * f * (f ^ 2 - g ^ 2) := by
  have hf : 0 ≤ f := hg.trans hgf
  rw [pairedDefect, shearDefect, shearDefect,
    abs_of_nonneg (sub_nonneg.mpr hgf), abs_of_nonpos (by linarith : -f - g ≤ 0)]
  ring

theorem pairedDefect_nonneg (f g : ℝ) : 0 ≤ pairedDefect f g := by
  unfold pairedDefect shearDefect
  positivity

theorem pairedDefect_le_four (f g : ℝ) (hf : 0 ≤ f) (hg : 0 ≤ g)
    (hf1 : f ≤ 1) (hg1 : g ≤ 1) : pairedDefect f g ≤ 4 := by
  rcases le_total f g with h | h
  · rw [pairedDefect_small f g hf h]
    have hg3 : g ^ 3 ≤ 1 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hg1) (by positivity : 0 ≤ 1 + g + g ^ 2)]
    nlinarith [mul_nonneg hg (sq_nonneg f)]
  · rw [pairedDefect_large f g hg h]
    have hf3 : f ^ 3 ≤ 1 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hf1) (by positivity : 0 ≤ 1 + f + f ^ 2)]
    nlinarith [mul_nonneg hf (sq_nonneg g)]

/-- Fast-amplitude logarithmic derivative, with value zero assigned at
the cusp. Differentiability at the cusp is not claimed. -/
def pairedAmplitudeRate (f g : ℝ) : ℝ :=
  if f < g then -8 * g * f ^ 2
  else if g < f then 12 * f ^ 3 - 4 * f * g ^ 2 else 0

/-- A polynomial upper bound valid also on the cusp. Its negative term
is important: suppressing a small fast shear can increase this defect. -/
theorem pairedAmplitudeRate_le (f g : ℝ) (hf : 0 ≤ f) (hg : 0 ≤ g) :
    pairedAmplitudeRate f g ≤ -8 * g * f ^ 2 + 16 * f ^ 3 := by
  unfold pairedAmplitudeRate
  split_ifs with hfg hgf
  · nlinarith [pow_nonneg hf 3]
  · nlinarith [mul_nonneg hf (sq_nonneg (f - g))]
  · have h : f = g := le_antisymm (le_of_not_gt hgf) (le_of_not_gt hfg)
    subst g
    nlinarith [pow_nonneg hf 3]

theorem pairedAmplitudeRate_le_bounded (f g eps : ℝ)
    (hf : 0 ≤ f) (hg : 0 ≤ g) (hfe : f ≤ eps) :
    pairedAmplitudeRate f g ≤ (-8 * g + 16 * eps) * f ^ 2 := by
  apply (pairedAmplitudeRate_le f g hf hg).trans
  nlinarith [mul_nonneg (sub_nonneg.mpr hfe) (sq_nonneg f)]

def pairedHeatRate (nu multiplier f g : ℝ) : ℝ :=
  -nu * (3 * pairedDefect f g + (multiplier - 1) * pairedAmplitudeRate f g)

/-- The paired rate is derived from the two actual heat decay rates.
The crossing of equal amplitudes is excluded only for this pointwise
derivative statement, not for the algebraic bounds. -/
theorem hasDerivAt_pairedDefect_heat (f g : ℝ → ℝ) (nu multiplier t : ℝ)
    (hf : HasDerivAt f (-nu * multiplier * f t) t)
    (hg : HasDerivAt g (-nu * g t) t)
    (hfpos : 0 < f t) (hgpos : 0 < g t) (hne : f t ≠ g t) :
    HasDerivAt (fun s ↦ pairedDefect (f s) (g s))
      (pairedHeatRate nu multiplier (f t) (g t)) t := by
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have h := (hg.mul ((hg.pow 2).sub (hf.pow 2))).const_mul 4
    have h' : HasDerivAt (fun s ↦ 4 * (g s * (g s ^ 2 - f s ^ 2)))
        (pairedHeatRate nu multiplier (f t) (g t)) t := by
      apply h.congr_deriv
      simp only [Pi.sub_apply, Pi.pow_apply, pairedHeatRate]
      rw [pairedDefect_small _ _ hfpos.le hlt.le]
      simp only [pairedAmplitudeRate, if_pos hlt]
      ring
    apply h'.congr_of_eventuallyEq
    have hpos := hf.continuousAt.eventually (lt_mem_nhds hfpos)
    have horder := (hg.continuousAt.sub hf.continuousAt).eventually
      (lt_mem_nhds (sub_pos.mpr hlt))
    filter_upwards [hpos, horder] with s hs ho
    rw [pairedDefect_small _ _ hs.le (by linarith)]
    ring
  · have h := (hf.mul ((hf.pow 2).sub (hg.pow 2))).const_mul 4
    have h' : HasDerivAt (fun s ↦ 4 * (f s * (f s ^ 2 - g s ^ 2)))
        (pairedHeatRate nu multiplier (f t) (g t)) t := by
      apply h.congr_deriv
      simp only [Pi.sub_apply, Pi.pow_apply, pairedHeatRate]
      rw [pairedDefect_large _ _ hgpos.le hgt.le]
      simp only [pairedAmplitudeRate, if_neg (not_lt.mpr hgt.le), if_pos hgt]
      ring
    apply h'.congr_of_eventuallyEq
    have hpos := hg.continuousAt.eventually (lt_mem_nhds hgpos)
    have horder := (hf.continuousAt.sub hg.continuousAt).eventually
      (lt_mem_nhds (sub_pos.mpr hgt))
    filter_upwards [hpos, horder] with s hs ho
    rw [pairedDefect_large _ _ hs.le (by linarith)]
    ring

theorem pairedHeatRate_lower_bound (nu multiplier f g eps : ℝ)
    (hnu : 0 ≤ nu) (hm : 1 ≤ multiplier)
    (hf : 0 ≤ f) (hg : 0 ≤ g) (hfe : f ≤ eps) (he : eps ≤ 1) (hg1 : g ≤ 1) :
    nu * ((multiplier - 1) * (8 * g - 16 * eps) * f ^ 2 - 12) ≤
      pairedHeatRate nu multiplier f g := by
  have hD := pairedDefect_le_four f g hf hg (hfe.trans he) hg1
  have hA := pairedAmplitudeRate_le_bounded f g eps hf hg hfe
  have hmA := mul_le_mul_of_nonneg_left hA (sub_nonneg.mpr hm)
  unfold pairedHeatRate
  nlinarith [mul_nonneg hnu (by linarith :
    0 ≤ 12 + (multiplier - 1) * ((-8 * g + 16 * eps) * f ^ 2) -
      (3 * pairedDefect f g + (multiplier - 1) * pairedAmplitudeRate f g))]

end Mettapedia.FluidDynamics.NavierStokes.PancakeTwoShearDiffusion
