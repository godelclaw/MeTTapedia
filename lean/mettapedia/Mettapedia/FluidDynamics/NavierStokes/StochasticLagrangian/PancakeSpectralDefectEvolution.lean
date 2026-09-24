import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeTopEigenvalueDerivative
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeLocalizedQuadraticEnergy

/-!
# Gap-weighted misalignment and its material energy identity

The Rayleigh defect `lambda_max * ‖w‖² - <w,S w>` measures stretching
lost through misalignment. Under `w' = S w + f` and `S' = -S² + R`, its
derivative is a negative squared spectral residual plus explicit forcing.
Unlike an eigenframe angular-rate bound, this identity has no inverse gap.

The remainder `R` is not assumed small: for the full strain equation it
contains spin squared, pressure Hessian and viscous terms. Filtered or
truncated equations also carry their actual commutator/subgrid terms.
No estimate of those terms from arbitrary initial data is asserted here.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PancakeSpectralDefectEvolution

open scoped RealInnerProductSpace
open PancakeStrainSpectralFrame PancakeTopEigenvalueDerivative
open PancakeSpectralProjectorRegularity
open PancakeSpectralProjectorRegularity.SymmetricStrain

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

def spectralResidual (S : H →L[ℝ] H) (lambda : ℝ) (w : H) : H :=
  lambda • w - S w

def spectralDefect (S : H →L[ℝ] H) (lambda : ℝ) (w : H) : ℝ :=
  lambda * ‖w‖ ^ 2 - ⟪w, S w⟫

def remainderAnisotropy (R : H →L[ℝ] H) (e w : H) : ℝ :=
  ⟪e, R e⟫ * ‖w‖ ^ 2 - ⟪w, R w⟫

theorem spectralDefect_eq_inner (S : H →L[ℝ] H) (lambda : ℝ) (w : H) :
    spectralDefect S lambda w = ⟪w, spectralResidual S lambda w⟫ := by
  simp [spectralDefect, spectralResidual, inner_sub_right, real_inner_smul_right]

theorem norm_spectralResidual_sq (S : H →L[ℝ] H) (lambda : ℝ) (w : H) :
    ‖spectralResidual S lambda w‖ ^ 2 =
      lambda ^ 2 * ‖w‖ ^ 2 - 2 * lambda * ⟪w, S w⟫ + ‖S w‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq]
  simp only [spectralResidual, inner_sub_left, inner_sub_right,
    real_inner_smul_left, real_inner_smul_right, real_inner_self_eq_norm_sq,
    real_inner_comm (S w) w, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  ring

theorem abs_spectralDefect_le (S : H →L[ℝ] H) (lambda : ℝ) (w : H) :
    |spectralDefect S lambda w| ≤ ‖w‖ * ‖spectralResidual S lambda w‖ := by
  rw [spectralDefect_eq_inner]
  exact abs_real_inner_le_norm _ _

theorem remainderAnisotropy_add (R T : H →L[ℝ] H) (e w : H) :
    remainderAnisotropy (R + T) e w =
      remainderAnisotropy R e w + remainderAnisotropy T e w := by
  simp only [remainderAnisotropy, add_apply, inner_add_right]
  ring

/-- Isotropic pressure has exactly zero contribution to this energy. -/
theorem remainderAnisotropy_isotropic (alpha : ℝ) (e w : H) (he : ‖e‖ = 1) :
    remainderAnisotropy (alpha • (1 : H →L[ℝ] H)) e w = 0 := by
  simp [remainderAnisotropy, real_inner_smul_right, he]

theorem remainderAnisotropy_add_isotropic (R : H →L[ℝ] H) (alpha : ℝ)
    (e w : H) (he : ‖e‖ = 1) :
    remainderAnisotropy (R + alpha • (1 : H →L[ℝ] H)) e w =
      remainderAnisotropy R e w := by
  rw [remainderAnisotropy_add, remainderAnisotropy_isotropic alpha e w he, add_zero]

theorem abs_quadratic_le_opNorm (R : H →L[ℝ] H) (w : H) :
    |⟪w, R w⟫| ≤ ‖R‖ * ‖w‖ ^ 2 := by
  calc
    _ ≤ ‖w‖ * ‖R w‖ := abs_real_inner_le_norm _ _
    _ ≤ ‖w‖ * (‖R‖ * ‖w‖) := by gcongr; exact R.le_opNorm w
    _ = _ := by ring

/-- A gap-free bound, but the anisotropic operator norm still requires its
own dynamical estimate. -/
theorem abs_remainderAnisotropy_le (R : H →L[ℝ] H) (e w : H) (he : ‖e‖ = 1) :
    |remainderAnisotropy R e w| ≤ 2 * ‖R‖ * ‖w‖ ^ 2 := by
  have heR := abs_quadratic_le_opNorm R e
  rw [he] at heR
  norm_num at heR
  calc
    _ ≤ |⟪e, R e⟫ * ‖w‖ ^ 2| + |⟪w, R w⟫| := abs_sub _ _
    _ = |⟪e, R e⟫| * ‖w‖ ^ 2 + |⟪w, R w⟫| := by
      rw [abs_mul, abs_of_nonneg (sq_nonneg ‖w‖)]
    _ ≤ ‖R‖ * ‖w‖ ^ 2 + ‖R‖ * ‖w‖ ^ 2 :=
      add_le_add (mul_le_mul_of_nonneg_right heR (sq_nonneg _))
        (abs_quadratic_le_opNorm R w)
    _ = _ := by ring

/-- The exact contribution of the antisymmetric velocity gradient. -/
theorem remainderAnisotropy_negative_skew_square (W : H →L[ℝ] H) (e w : H)
    (hW : ∀ x y, ⟪W x, y⟫ = -⟪x, W y⟫) :
    remainderAnisotropy (-W * W) e w =
      ‖W e‖ ^ 2 * ‖w‖ ^ 2 - ‖W w‖ ^ 2 := by
  have hh : ∀ x : H, ⟪x, (-W * W) x⟫ = ‖W x‖ ^ 2 := by
    intro x
    have h := hW x (W x)
    rw [real_inner_self_eq_norm_sq] at h
    simpa only [mul_apply_eq_comp, neg_apply, inner_neg_right] using h.symm
  simp only [remainderAnisotropy, hh]

/-- For actual vorticity, spin annihilates `w`. Its contribution is then
nonnegative, not a damping term that may be discarded. -/
theorem remainderAnisotropy_spin_and_forcing (W R : H →L[ℝ] H) (e w : H)
    (hW : ∀ x y, ⟪W x, y⟫ = -⟪x, W y⟫) (hw : W w = 0) :
    remainderAnisotropy (-W * W + R) e w =
      ‖W e‖ ^ 2 * ‖w‖ ^ 2 + remainderAnisotropy R e w := by
  rw [remainderAnisotropy_add, remainderAnisotropy_negative_skew_square W e w hW,
    hw, norm_zero, zero_pow (by decide : 2 ≠ 0), sub_zero]

theorem spectralDefect_forcing_young (z f : H) (theta : ℝ) (htheta : 0 < theta) :
    2 * ⟪z, f⟫ ≤ theta * ‖z‖ ^ 2 + ‖f‖ ^ 2 / theta := by
  have hinner := (le_abs_self ⟪z, f⟫).trans (abs_real_inner_le_norm z f)
  apply (show 2 * ⟪z, f⟫ ≤ 2 * (‖z‖ * ‖f‖) by linarith).trans
  calc
    _ ≤ (theta ^ 2 * ‖z‖ ^ 2 + ‖f‖ ^ 2) / theta := by
      apply (le_div_iff₀ htheta).mpr
      nlinarith [sq_nonneg (theta * ‖z‖ - ‖f‖)]
    _ = _ := by field_simp

/-- Eigenvalue rate after separating strain self-interaction from forcing. -/
theorem eigenvalueRate_strainSquare (S R : H →L[ℝ] H) (e : H) (lambda : ℝ)
    (he : ‖e‖ = 1) (hpair : S e = lambda • e) :
    ⟪e, (-S * S + R) e⟫ = -lambda ^ 2 + ⟪e, R e⟫ := by
  simp only [add_apply, mul_apply_eq_comp, neg_apply,
    inner_add_right, inner_neg_right, hpair, map_smul, real_inner_smul_right,
    real_inner_self_eq_norm_sq, he]
  ring

/-- The self-interaction/stretching cancellation is a negative square. -/
theorem spectralDefect_rate_identity (S R : H →L[ℝ] H)
    (e w f : H) (lambda : ℝ)
    (hs : ∀ x y, ⟪x, S y⟫ = ⟪S x, y⟫) :
    (-lambda ^ 2 + ⟪e, R e⟫) * ‖w‖ ^ 2 +
      2 * lambda * ⟪w, S w + f⟫ -
      (⟪w, (-S * S + R) w⟫ + 2 * ⟪S w, S w + f⟫) =
    -‖spectralResidual S lambda w‖ ^ 2 + remainderAnisotropy R e w +
      2 * ⟪spectralResidual S lambda w, f⟫ := by
  rw [norm_spectralResidual_sq]
  simp only [add_apply, mul_apply_eq_comp, neg_apply,
    inner_add_right, inner_neg_right, hs w (S w), real_inner_self_eq_norm_sq,
    remainderAnisotropy, spectralResidual, inner_sub_left, real_inner_smul_left]
  ring

variable [CompleteSpace H]

/-- Exact material defect derivative. The top eigenvalue derivative is
specialized to the constructed spectral value below. -/
theorem hasDerivAt_spectralDefect
    (S : ℝ → H →L[ℝ] H) (lambda : ℝ → ℝ) (w : ℝ → H)
    (R : H →L[ℝ] H) (e f : H) (t : ℝ)
    (hS : HasDerivAt S (-S t * S t + R) t)
    (hlambda : HasDerivAt lambda (-lambda t ^ 2 + ⟪e, R e⟫) t)
    (hw : HasDerivAt w (S t (w t) + f) t) (hs : IsSelfAdjoint (S t)) :
    HasDerivAt (fun tau ↦ spectralDefect (S tau) (lambda tau) (w tau))
      (-‖spectralResidual (S t) (lambda t) (w t)‖ ^ 2 +
        remainderAnisotropy R e (w t) +
        2 * ⟪spectralResidual (S t) (lambda t) (w t), f⟫) t := by
  have hn := hw.inner ℝ hw
  have hq := PancakeLocalizedQuadraticEnergy.hasDerivAt_localizedEnergy
    S (-S t * S t + R) w (S t (w t) + f) t hS hw hs
  have h := (hlambda.mul hn).sub hq
  have hs' : ∀ x y, ⟪x, S t y⟫ = ⟪S t x, y⟫ :=
    fun x y ↦ (hs.isSymmetric x y).symm
  have hr := spectralDefect_rate_identity (S t) R e (w t) f (lambda t) hs'
  simp only [real_inner_self_eq_norm_sq,
    real_inner_comm (w t) (S t (w t) + f)] at h
  apply h.congr_deriv
  calc
    _ = (-lambda t ^ 2 + ⟪e, R e⟫) * ‖w t‖ ^ 2 +
        2 * lambda t * ⟪w t, S t (w t) + f⟫ -
        (⟪w t, (-S t * S t + R) (w t)⟫ + 2 * ⟪S t (w t), S t (w t) + f⟫) := by ring
    _ = _ := hr

local notation "R3" => EuclideanSpace ℝ (Fin 3)

def topSpectralDefect (S : SymmetricStrain) (w : R3) : ℝ :=
  spectralDefect S.1 (topEigenvalue S) w

theorem topSpectralDefect_nonneg (S : SymmetricStrain) (w : R3) :
    0 ≤ topSpectralDefect S w := by
  exact sub_nonneg.mpr
    (PancakeSpectralClusterDichotomy.rayleigh_le_topEigenvalue_mul_norm_sq S.1 S.2 w)

/-- The defect is exactly the spectral-gap-weighted transverse energy. -/
theorem topSpectralDefect_coordinates (S : SymmetricStrain) (w : R3) :
    let F := orderedEigenframe S.1 S.2
    topSpectralDefect S w =
      (F.eigenvalue 0 - F.eigenvalue 1) * ⟪w, F.eigenbasis 1⟫ ^ 2 +
      (F.eigenvalue 0 - F.eigenvalue 2) * ⟪w, F.eigenbasis 2⟫ ^ 2 := by
  dsimp only
  have hp := PancakeTransverseEnergyCoercivity.parseval_three_norm_sq
    (orderedEigenframe S.1 S.2).eigenbasis w
  have hr := rayleigh_three S.1 S.2 (orderedEigenframe S.1 S.2).eigenvalue
    (orderedEigenframe S.1 S.2).eigenbasis (orderedEigenframe S.1 S.2).apply_eigenbasis w
  unfold topSpectralDefect spectralDefect topEigenvalue
  rw [hr, ← hp]
  ring

/-- The damping square is transverse energy weighted by squared gaps.
It does not uniformly dominate unweighted line misalignment at collisions. -/
theorem norm_topSpectralResidual_sq_coordinates (S : SymmetricStrain) (w : R3) :
    let F := orderedEigenframe S.1 S.2
    ‖spectralResidual S.1 (topEigenvalue S) w‖ ^ 2 =
      (F.eigenvalue 0 - F.eigenvalue 1) ^ 2 * ⟪w, F.eigenbasis 1⟫ ^ 2 +
      (F.eigenvalue 0 - F.eigenvalue 2) ^ 2 * ⟪w, F.eigenbasis 2⟫ ^ 2 := by
  let F := orderedEigenframe S.1 S.2
  have hc (i : Fin 3) : ⟪spectralResidual S.1 (topEigenvalue S) w, F.eigenbasis i⟫ =
      (F.eigenvalue 0 - F.eigenvalue i) * ⟪w, F.eigenbasis i⟫ := by
    simp only [spectralResidual, inner_sub_left, real_inner_smul_left,
      ← S.2 w (F.eigenbasis i), F.apply_eigenbasis, real_inner_smul_right]
    change _ = (topEigenvalue S - F.eigenvalue i) * _
    ring
  have hp := PancakeTransverseEnergyCoercivity.parseval_three_norm_sq F.eigenbasis
    (spectralResidual S.1 (topEigenvalue S) w)
  rw [hc 0, hc 1, hc 2] at hp
  simpa only [sub_self, zero_mul, zero_pow (by decide : 2 ≠ 0), zero_add, mul_pow]
    using hp.symm

/-- Unlike an individual eigenline, the defect is stable through eigenvalue
collisions, with no lower bound on either spectral gap. -/
theorem abs_topSpectralDefect_sub_le (A B : SymmetricStrain) (w : R3) :
    |topSpectralDefect A w - topSpectralDefect B w| ≤
      2 * ‖A.1 - B.1‖ * ‖w‖ ^ 2 := by
  have he := PancakeTransverseEnergyFreezing.abs_constructedTopEigenvalue_sub_le
    A.1 B.1 A.2 B.2
  change |topEigenvalue A - topEigenvalue B| ≤ ‖A.1 - B.1‖ at he
  have hid : topSpectralDefect A w - topSpectralDefect B w =
      (topEigenvalue A - topEigenvalue B) * ‖w‖ ^ 2 - ⟪w, (A.1 - B.1) w⟫ := by
    simp only [topSpectralDefect, spectralDefect, sub_apply, inner_sub_right]
    ring
  rw [hid]
  calc
    _ ≤ |(topEigenvalue A - topEigenvalue B) * ‖w‖ ^ 2| +
        |⟪w, (A.1 - B.1) w⟫| := abs_sub _ _
    _ = |topEigenvalue A - topEigenvalue B| * ‖w‖ ^ 2 +
        |⟪w, (A.1 - B.1) w⟫| := by rw [abs_mul, abs_of_nonneg (sq_nonneg ‖w‖)]
    _ ≤ ‖A.1 - B.1‖ * ‖w‖ ^ 2 + ‖A.1 - B.1‖ * ‖w‖ ^ 2 :=
      add_le_add (mul_le_mul_of_nonneg_right he (sq_nonneg _))
        (abs_quadratic_le_opNorm _ w)
    _ = _ := by ring

/-- Route-facing identity with the top eigenvalue constructed from the strain
path. Only the top gap at this time must be positive; no frame derivative or
lower bound for that gap occurs in the conclusion. -/
theorem hasDerivAt_topSpectralDefect
    (S : ℝ → SymmetricStrain) (w : ℝ → R3)
    (R : R3 →L[ℝ] R3) (f : R3) (t : ℝ)
    (hS : HasDerivAt (fun tau ↦ (S tau).1) (-(S t).1 * (S t).1 + R) t)
    (hw : HasDerivAt w ((S t).1 (w t) + f) t)
    (hgap : 0 < topGap (S t)) :
    let e := (orderedEigenframe (S t).1 (S t).2).eigenbasis 0
    HasDerivAt (fun tau ↦ topSpectralDefect (S tau) (w tau))
      (-‖spectralResidual (S t).1 (topEigenvalue (S t)) (w t)‖ ^ 2 +
        remainderAnisotropy R e (w t) +
        2 * ⟪spectralResidual (S t).1 (topEigenvalue (S t)) (w t), f⟫) t := by
  dsimp only
  apply hasDerivAt_spectralDefect (fun tau ↦ (S tau).1)
    (fun tau ↦ topEigenvalue (S tau)) w R _ f t hS
  · have hl := hasDerivAt_topEigenvalue S _ t hS hgap
    rw [eigenvalueRate_strainSquare (S t).1 R _ _
      ((orderedEigenframe (S t).1 (S t).2).eigenbasis.norm_eq_one 0)
      ((orderedEigenframe (S t).1 (S t).2).apply_eigenbasis 0)] at hl
    exact hl
  · exact hw
  · exact ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
      (fun x y ↦ ((S t).2 x y).symm)

/-- Collision-compatible form: differentiability of the largest eigenvalue
replaces spectral separation. It holds almost everywhere on smooth compact
time intervals, as the budget module proves. -/
theorem hasDerivAt_topSpectralDefect_of_differentiableAt
    (S : ℝ → SymmetricStrain) (w : ℝ → R3)
    (R : R3 →L[ℝ] R3) (f : R3) (t : ℝ)
    (hS : HasDerivAt (fun tau ↦ (S tau).1) (-(S t).1 * (S t).1 + R) t)
    (hw : HasDerivAt w ((S t).1 (w t) + f) t)
    (hlambda : DifferentiableAt ℝ (fun tau ↦ topEigenvalue (S tau)) t) :
    let e := (orderedEigenframe (S t).1 (S t).2).eigenbasis 0
    HasDerivAt (fun tau ↦ topSpectralDefect (S tau) (w tau))
      (-‖spectralResidual (S t).1 (topEigenvalue (S t)) (w t)‖ ^ 2 +
        remainderAnisotropy R e (w t) +
        2 * ⟪spectralResidual (S t).1 (topEigenvalue (S t)) (w t), f⟫) t := by
  dsimp only
  apply hasDerivAt_spectralDefect (fun tau ↦ (S tau).1)
    (fun tau ↦ topEigenvalue (S tau)) w R _ f t hS
  · have hl := hasDerivAt_topEigenvalue_of_differentiableAt S _ t hS hlambda
    rw [eigenvalueRate_strainSquare (S t).1 R _ _
      ((orderedEigenframe (S t).1 (S t).2).eigenbasis.norm_eq_one 0)
      ((orderedEigenframe (S t).1 (S t).2).apply_eigenbasis 0)] at hl
    exact hl
  · exact hw
  · exact ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
      (fun x y ↦ ((S t).2 x y).symm)

end Mettapedia.FluidDynamics.NavierStokes.PancakeSpectralDefectEvolution
