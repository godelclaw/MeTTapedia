import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeTwoShearSpatialMean
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakePeriodicDiffusionWitness
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# A physical periodic heat evolution whose integrated defect increases

The velocity, its strain and curl, and its heat evolution are explicit.
The normalized spatial integral of the actual top spectral defect has
a strictly positive finite-time increase. The proof uses exact inequalities
and remains valid across spectral crossings. This is a counterexample to
free viscous monotonicity of this defect, not a nonlinear NS solution or
a refutation of regularity.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PancakeTwoShearHeatWitness

open Real PancakePeriodicMean PancakeTwoShearSpatialMean PancakeTwoShearDiffusion
open PancakePlanarSpectralDefect PancakeSpectralDefectEvolution
open PancakePeriodicDiffusionWitness (planarLaplacian)

def heatShear (nu k amplitude t z : ℝ) : ℝ :=
  amplitude * exp (-nu * k ^ 2 * t) * sin (k * z)

theorem hasDerivAt_heatShear_space (nu k amplitude t z : ℝ) :
    HasDerivAt (heatShear nu k amplitude t)
      (amplitude * exp (-nu * k ^ 2 * t) * k * cos (k * z)) z := by
  have h := (((hasDerivAt_id z).const_mul k).sin).const_mul
    (amplitude * exp (-nu * k ^ 2 * t))
  simp only [id_eq, mul_one] at h
  exact h.congr_deriv (by ring)

theorem deriv2_heatShear (nu k amplitude t z : ℝ) :
    deriv (deriv (heatShear nu k amplitude t)) z = -k ^ 2 * heatShear nu k amplitude t z := by
  have heq : deriv (heatShear nu k amplitude t) =
      (fun z ↦ amplitude * exp (-nu * k ^ 2 * t) * k * cos (k * z)) :=
    funext (fun z ↦ (hasDerivAt_heatShear_space nu k amplitude t z).deriv)
  rw [heq]
  have h := (((hasDerivAt_id z).const_mul k).cos).const_mul
    (amplitude * exp (-nu * k ^ 2 * t) * k)
  simp only [id_eq, mul_one] at h
  rw [h.deriv]
  unfold heatShear
  ring

theorem hasDerivAt_heatShear_time (nu k amplitude t z : ℝ) :
    HasDerivAt (fun s ↦ heatShear nu k amplitude s z)
      (-nu * k ^ 2 * heatShear nu k amplitude t z) t := by
  have h := ((((hasDerivAt_id t).const_mul (-nu * k ^ 2)).exp).const_mul amplitude).mul_const
    (sin (k * z))
  simp only [id_eq, mul_one] at h
  apply h.congr_deriv
  unfold heatShear
  ring

theorem heatShear_equation (nu k amplitude t z : ℝ) :
    deriv (fun s ↦ heatShear nu k amplitude s z) t =
      nu * deriv (deriv (heatShear nu k amplitude t)) z := by
  rw [(hasDerivAt_heatShear_time nu k amplitude t z).deriv, deriv2_heatShear]
  ring

def velocityX (nu : ℝ) (N : ℕ) (eps t _x y : ℝ) : ℝ :=
  heatShear nu N (2 * eps / N) t y

def velocityY (nu : ℝ) (_N : ℕ) (_eps t x _y : ℝ) : ℝ := heatShear nu 1 (-2) t x

def fastAmplitude (nu : ℝ) (N : ℕ) (eps t y : ℝ) : ℝ :=
  eps * exp (-nu * (N : ℝ) ^ 2 * t) * cos ((N : ℝ) * y)

def slowAmplitude (nu t x : ℝ) : ℝ := exp (-nu * t) * cos x

theorem velocity_gradient (nu : ℝ) (N : ℕ) (eps t x y : ℝ) (hN : N ≠ 0) :
    deriv (fun s ↦ velocityX nu N eps t s y) x = 0 ∧
    deriv (fun s ↦ velocityY nu N eps t x s) y = 0 ∧
    deriv (fun s ↦ velocityX nu N eps t x s) y = 2 * fastAmplitude nu N eps t y ∧
    deriv (fun s ↦ velocityY nu N eps t s y) x = -2 * slowAmplitude nu t x := by
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast hN
  simp only [velocityX, velocityY, deriv_const]
  refine ⟨trivial, trivial, ?_, ?_⟩
  · rw [(hasDerivAt_heatShear_space nu N (2 * eps / N) t y).deriv]
    unfold fastAmplitude
    field_simp
  · rw [(hasDerivAt_heatShear_space nu 1 (-2) t x).deriv]
    simp [slowAmplitude]
    ring

theorem velocity_divergence_zero (nu : ℝ) (N : ℕ) (eps t x y : ℝ) :
    deriv (fun s ↦ velocityX nu N eps t s y) x +
      deriv (fun s ↦ velocityY nu N eps t x s) y = 0 := by
  simp [velocityX, velocityY]

theorem deriv2_const (c z : ℝ) : deriv (deriv (fun _ : ℝ ↦ c)) z = 0 := by
  have heq : deriv (fun _ : ℝ ↦ c) = fun _ : ℝ ↦ 0 :=
    funext (fun x ↦ deriv_const x c)
  rw [heq]
  exact deriv_const z 0

theorem velocity_heat_equation (nu : ℝ) (N : ℕ) (eps t x y : ℝ) :
    deriv (fun s ↦ velocityX nu N eps s x y) t =
      nu * planarLaplacian (velocityX nu N eps t) x y ∧
    deriv (fun s ↦ velocityY nu N eps s x y) t =
      nu * planarLaplacian (velocityY nu N eps t) x y := by
  constructor
  · simpa only [velocityX, planarLaplacian, deriv2_const, zero_add] using
      heatShear_equation nu N (2 * eps / N) t y
  · simpa only [velocityY, planarLaplacian, deriv2_const, add_zero] using
      heatShear_equation nu 1 (-2) t x

theorem velocity_periodic (nu : ℝ) (N : ℕ) (eps t x y : ℝ) :
    velocityX nu N eps t (x + 2 * π) y = velocityX nu N eps t x y ∧
    velocityX nu N eps t x (y + 2 * π) = velocityX nu N eps t x y ∧
    velocityY nu N eps t (x + 2 * π) y = velocityY nu N eps t x y ∧
    velocityY nu N eps t x (y + 2 * π) = velocityY nu N eps t x y := by
  simp [velocityX, velocityY, heatShear, mul_add, sin_add_nat_mul_two_pi, sin_add_two_pi]

def physicalStrain (nu : ℝ) (N : ℕ) (eps t x y : ℝ) :=
  planarStrain (deriv (fun s ↦ velocityX nu N eps t s y) x)
    ((deriv (fun s ↦ velocityX nu N eps t x s) y +
      deriv (fun s ↦ velocityY nu N eps t s y) x) / 2)

def physicalVorticity (nu : ℝ) (N : ℕ) (eps t x y : ℝ) :=
  normalVorticity (deriv (fun s ↦ velocityY nu N eps t s y) x -
    deriv (fun s ↦ velocityX nu N eps t x s) y)

theorem physicalStrain_eq (nu : ℝ) (N : ℕ) (eps t x y : ℝ) (hN : N ≠ 0) :
    physicalStrain nu N eps t x y =
      planarStrain 0 (fastAmplitude nu N eps t y - slowAmplitude nu t x) := by
  obtain ⟨h0, _, hf, hg⟩ := velocity_gradient nu N eps t x y hN
  rw [physicalStrain, h0, hf, hg]
  congr 1
  ring

theorem physicalVorticity_eq (nu : ℝ) (N : ℕ) (eps t x y : ℝ) (hN : N ≠ 0) :
    physicalVorticity nu N eps t x y =
      normalVorticity (-2 * (fastAmplitude nu N eps t y + slowAmplitude nu t x)) := by
  obtain ⟨_, _, hf, hg⟩ := velocity_gradient nu N eps t x y hN
  rw [physicalVorticity, hf, hg]
  congr 1
  ring

def physicalDefect (nu : ℝ) (N : ℕ) (eps t x y : ℝ) : ℝ :=
  topSpectralDefect (physicalStrain nu N eps t x y) (physicalVorticity nu N eps t x y)

theorem physicalDefect_eq (nu : ℝ) (N : ℕ) (eps t x y : ℝ) (hN : N ≠ 0) :
    physicalDefect nu N eps t x y =
      shearDefect (fastAmplitude nu N eps t y) (slowAmplitude nu t x) := by
  rw [physicalDefect, physicalStrain_eq _ _ _ _ _ _ hN, physicalVorticity_eq _ _ _ _ _ _ hN,
    topSpectralDefect_twoShear]

def physicalDefectMean (nu : ℝ) (N : ℕ) (eps t : ℝ) : ℝ :=
  spatialMean (physicalDefect nu N eps t)

theorem physicalDefectMean_eq (nu : ℝ) (N : ℕ) (eps t : ℝ)
    (hN : N ≠ 0) (he : 0 ≤ eps) :
    physicalDefectMean nu N eps t =
      pairedMean (eps * exp (-nu * (N : ℝ) ^ 2 * t)) (exp (-nu * t)) := by
  rw [← rawMean_eq_pairedMean N _ _ hN (by positivity) (by positivity)]
  apply spatialMean_congr
  intro x y
  exact physicalDefect_eq nu N eps t x y hN

/-- Exact finite-time increase of the actual spatial spectral defect
under a constructed divergence-free periodic heat evolution. -/
theorem physicalDefectMean_increases :
    (24567 : ℝ) / 33554432 ≤
      physicalDefectMean 1 128 (1 / 16) (1 / 16384) - physicalDefectMean 1 128 (1 / 16) 0 := by
  let alpha : ℝ := exp (-(16383 : ℝ) / 16384)
  let beta : ℝ := exp (-(1 : ℝ) / 16384)
  have ha : 0 ≤ alpha := (exp_pos _).le
  have hb : 0 ≤ beta := (exp_pos _).le
  have ha2 : alpha ^ 2 ≤ 1 / 2 := by
    have he : 2 ≤ exp ((32766 : ℝ) / 16384) := by
      linarith [add_one_le_exp ((32766 : ℝ) / 16384)]
    calc
      alpha ^ 2 = exp (-((32766 : ℝ) / 16384)) := by
        dsimp [alpha]
        rw [← exp_nat_mul]
        congr 1
        norm_num
      _ = 1 / exp ((32766 : ℝ) / 16384) := by rw [exp_neg, one_div]
      _ ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) he
  have hb3 : (16381 : ℝ) / 16384 ≤ beta ^ 3 := by
    have heq : beta ^ 3 = exp (-(3 : ℝ) / 16384) := by
      dsimp [beta]
      rw [← exp_nat_mul]
      congr 1
      norm_num
    rw [heq]
    linarith [add_one_le_exp (-(3 : ℝ) / 16384)]
  have hab : beta * alpha = exp (-1) := by
    dsimp [alpha, beta]
    rw [← exp_add]
    congr 1
    norm_num
  have h := pairedMean_concrete_growth alpha beta ha ha2 hb hb3
  rw [hab] at h
  rw [physicalDefectMean_eq _ _ _ _ (by decide) (by norm_num),
    physicalDefectMean_eq _ _ _ _ (by decide) (by norm_num)]
  norm_num at h ⊢
  simpa only [mul_comm (exp (-1)) ((1 : ℝ) / 16), beta, neg_div] using h

theorem physicalDefectMean_strictly_increases :
    physicalDefectMean 1 128 (1 / 16) 0 < physicalDefectMean 1 128 (1 / 16) (1 / 16384) := by
  linarith [physicalDefectMean_increases]

end Mettapedia.FluidDynamics.NavierStokes.PancakeTwoShearHeatWitness
