import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic

/-!
# A reduced spectral certificate for two-shear viscous production

The profiles are `a(z)=(1+cos z)^3` and `b(z)=(1-cos z)^3`, in angle
coordinates. For `u=(sin y*a(z),sin x*b(z),0)`, the first component of
`(omega dot grad)((omega dot grad)u)` separates into three scalar profiles.
This file checks the profile algebra, its heat-direction variation, the
finite cosine expansions, and the resulting positive rational spectral sum.

This is a reduced certificate. Identification of its spectral sum with
the existing `TensorL2` projected-flux work is a separate obligation;
no theorem here asserts that that analytic bridge has been completed.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.TwoShearViscousCertificate

abbrev Jet := Fin 3 → ℝ

def sourceA (a b : Jet) : ℝ := a 1 * b 0 * b 1 + a 2 * b 0 ^ 2 / 2
def sourceB (a b : Jet) : ℝ := a 2 * b 0 ^ 2 / 2
def sourceC (a b : Jet) : ℝ :=
  (b 0 * (a 1 ^ 2 - a 0 * a 2) - a 0 * a 1 * b 1) / 2

def variationA (a b h k : Jet) : ℝ :=
  h 1 * b 0 * b 1 + a 1 * k 0 * b 1 + a 1 * b 0 * k 1 +
    (h 2 * b 0 ^ 2 + 2 * a 2 * b 0 * k 0) / 2
def variationB (a b h k : Jet) : ℝ :=
  (h 2 * b 0 ^ 2 + 2 * a 2 * b 0 * k 0) / 2
def variationC (a b h k : Jet) : ℝ :=
  (k 0 * (a 1 ^ 2 - a 0 * a 2) +
    b 0 * (2 * a 1 * h 1 - h 0 * a 2 - a 0 * h 2) -
    h 0 * a 1 * b 1 - a 0 * h 1 * b 1 - a 0 * a 1 * k 1) / 2

theorem hasDerivAt_sourceA (a b : ℝ → Jet) (h k : Jet) (t : ℝ)
    (ha : ∀ j, HasDerivAt (fun s ↦ a s j) (h j) t)
    (hb : ∀ j, HasDerivAt (fun s ↦ b s j) (k j) t) :
    HasDerivAt (fun s ↦ sourceA (a s) (b s)) (variationA (a t) (b t) h k) t := by
  convert! (((ha 1).mul (hb 0)).mul (hb 1)).add
    (((ha 2).mul ((hb 0).pow 2)).div_const 2) using 1
  simp only [variationA, Pi.mul_apply, Pi.pow_apply]
  ring

theorem hasDerivAt_sourceB (a b : ℝ → Jet) (h k : Jet) (t : ℝ)
    (ha : ∀ j, HasDerivAt (fun s ↦ a s j) (h j) t)
    (hb : ∀ j, HasDerivAt (fun s ↦ b s j) (k j) t) :
    HasDerivAt (fun s ↦ sourceB (a s) (b s)) (variationB (a t) (b t) h k) t := by
  convert! (((ha 2).mul ((hb 0).pow 2)).div_const 2) using 1
  simp only [variationB, Pi.pow_apply]
  ring

theorem hasDerivAt_sourceC (a b : ℝ → Jet) (h k : Jet) (t : ℝ)
    (ha : ∀ j, HasDerivAt (fun s ↦ a s j) (h j) t)
    (hb : ∀ j, HasDerivAt (fun s ↦ b s j) (k j) t) :
    HasDerivAt (fun s ↦ sourceC (a s) (b s)) (variationC (a t) (b t) h k) t := by
  convert! (((hb 0).mul (((ha 1).pow 2).sub ((ha 0).mul (ha 2)))).sub
    (((ha 0).mul (ha 1)).mul (hb 1))).div_const 2 using 1
  simp only [variationC, Pi.sub_apply, Pi.mul_apply, Pi.pow_apply]
  ring

/-- The first component, before changing `cos² x` to `(1+cos 2x)/2`.
Only the trigonometric identity for the x-coordinate is needed here. -/
theorem first_source_separation (f fp g gp : ℝ) (a b : Jet)
    (hg : g ^ 2 + gp ^ 2 = 1) :
    (-g * b 1) * (-f * g * a 1 * b 0) +
        (f * a 1) * (fp * gp * a 1 * b 0) +
        (gp * b 0 - fp * a 0) * (f * gp * (a 2 * b 0 + a 1 * b 1)) =
      f * sourceA a b + f * (2 * gp ^ 2 - 1) * sourceB a b +
        2 * f * fp * gp * sourceC a b := by
  dsimp [sourceA, sourceB, sourceC]
  linear_combination (f * a 1 * b 0 * b 1) * hg

def profileJet (c s : ℝ) : Jet :=
  ![(1 + c) ^ 3, -3 * s * (1 + c) ^ 2, 3 * (1 + c) * (2 - c - 3 * c ^ 2)]

/-- The jet of `(d²/dz² - 1) a`; the `-1` is the transverse sine eigenvalue. -/
def heatJet (c s : ℝ) : Jet :=
  ![profileJet c s 2 - profileJet c s 0,
    -3 * s * (1 - 8 * c - 9 * c ^ 2) - profileJet c s 1,
    -24 - 57 * c + 48 * c ^ 2 + 81 * c ^ 3 - profileJet c s 2]

theorem hasDerivAt_profile_value (z : ℝ) :
    HasDerivAt (fun x ↦ profileJet (Real.cos x) (Real.sin x) 0)
      (profileJet (Real.cos z) (Real.sin z) 1) z := by
  change HasDerivAt (fun x ↦ (1 + Real.cos x) ^ 3)
    (-3 * Real.sin z * (1 + Real.cos z) ^ 2) z
  convert! ((Real.hasDerivAt_cos z).const_add 1).pow 3 using 1
  ring

theorem hasDerivAt_profile_first (z : ℝ) :
    HasDerivAt (fun x ↦ profileJet (Real.cos x) (Real.sin x) 1)
      (profileJet (Real.cos z) (Real.sin z) 2) z := by
  have hs : Real.sin z ^ 2 = 1 - Real.cos z ^ 2 := by
    nlinarith [Real.sin_sq_add_cos_sq z]
  convert! ((Real.hasDerivAt_sin z).const_mul (-3)).mul
    (((Real.hasDerivAt_cos z).const_add 1).pow 2) using 1
  dsimp [profileJet]
  ring_nf
  simp only [hs]
  ring

theorem hasDerivAt_profile_second (z : ℝ) :
    HasDerivAt (fun x ↦ profileJet (Real.cos x) (Real.sin x) 2)
      (-3 * Real.sin z * (1 - 8 * Real.cos z - 9 * Real.cos z ^ 2)) z := by
  convert! (((Real.hasDerivAt_cos z).const_add 1).const_mul 3).mul
    (((Real.hasDerivAt_cos z).const_sub 2).sub
      (((Real.hasDerivAt_cos z).pow 2).const_mul 3)) using 1
  dsimp
  ring

theorem hasDerivAt_profile_third (z : ℝ) :
    HasDerivAt (fun x ↦ -3 * Real.sin x * (1 - 8 * Real.cos x - 9 * Real.cos x ^ 2))
      (-24 - 57 * Real.cos z + 48 * Real.cos z ^ 2 + 81 * Real.cos z ^ 3) z := by
  have hs : Real.sin z ^ 2 = 1 - Real.cos z ^ 2 := by
    nlinarith [Real.sin_sq_add_cos_sq z]
  convert! ((Real.hasDerivAt_sin z).const_mul (-3)).mul
    ((((Real.hasDerivAt_cos z).const_mul 8).const_sub 1).sub
      (((Real.hasDerivAt_cos z).pow 2).const_mul 9)) using 1
  dsimp
  ring_nf
  simp only [hs]
  ring

theorem hasDerivAt_heat_value (z : ℝ) :
    HasDerivAt (fun x ↦ heatJet (Real.cos x) (Real.sin x) 0)
      (heatJet (Real.cos z) (Real.sin z) 1) z := by
  exact (hasDerivAt_profile_second z).sub (hasDerivAt_profile_value z)

theorem hasDerivAt_heat_first (z : ℝ) :
    HasDerivAt (fun x ↦ heatJet (Real.cos x) (Real.sin x) 1)
      (heatJet (Real.cos z) (Real.sin z) 2) z := by
  exact (hasDerivAt_profile_third z).sub (hasDerivAt_profile_first z)

def polynomialA (c : ℝ) : ℝ := -3 * (c - 1) ^ 6 * (c + 1) ^ 2 * (9 * c + 4) / 2
def polynomialB (c : ℝ) : ℝ := -3 * (c - 1) ^ 6 * (c + 1) ^ 2 * (3 * c - 2) / 2
def polynomialC (c : ℝ) : ℝ := -3 * (c - 1) ^ 3 * (c + 1) ^ 5 * (3 * c + 4) / 2
def polynomialARate (c : ℝ) : ℝ :=
  15 * (c - 1) ^ 5 * (c + 1) * (27 * c ^ 3 + 28 * c ^ 2 + 9 * c + 2)
def polynomialBRate (c : ℝ) : ℝ :=
  15 * (c - 1) ^ 5 * (c + 1) * (9 * c ^ 3 + c ^ 2 - 3 * c - 1)
def polynomialCRate (c : ℝ) : ℝ :=
  15 * (c - 1) ^ 2 * (c + 1) ^ 4 * (9 * c ^ 3 + 7 * c ^ 2 - 3 * c + 2)

theorem source_profiles (c s : ℝ) (hs : s ^ 2 = 1 - c ^ 2) :
    sourceA (profileJet c s) (profileJet (-c) (-s)) = polynomialA c ∧
    sourceB (profileJet c s) (profileJet (-c) (-s)) = polynomialB c ∧
    sourceC (profileJet c s) (profileJet (-c) (-s)) = polynomialC c := by
  constructor
  · dsimp [sourceA, profileJet, polynomialA]
    ring_nf
    simp only [hs]
    ring
  constructor
  · dsimp [sourceB, profileJet, polynomialB]
    ring
  · dsimp [sourceC, profileJet, polynomialC]
    ring_nf
    simp only [hs]
    ring

theorem source_rate_profiles (c s : ℝ) (hs : s ^ 2 = 1 - c ^ 2) :
    variationA (profileJet c s) (profileJet (-c) (-s))
      (heatJet c s) (heatJet (-c) (-s)) = polynomialARate c ∧
    variationB (profileJet c s) (profileJet (-c) (-s))
      (heatJet c s) (heatJet (-c) (-s)) = polynomialBRate c ∧
    variationC (profileJet c s) (profileJet (-c) (-s))
      (heatJet c s) (heatJet (-c) (-s)) = polynomialCRate c := by
  constructor
  · dsimp [variationA, heatJet, profileJet, polynomialARate]
    ring_nf
    simp only [hs]
    ring
  constructor
  · dsimp [variationB, heatJet, profileJet, polynomialBRate]
    ring
  · dsimp [variationC, heatJet, profileJet, polynomialCRate]
    ring_nf
    simp only [hs]
    ring

/-- Coefficients at frequencies `k≥0`; negative frequencies have the same coefficient. -/
def coefficientsA : Fin 10 → ℚ :=
  ![0, -429/512, 39/32, 117/256, -27/16, 225/256, 9/32, -483/1024, 3/16, -27/1024]
def coefficientsB : Fin 10 → ℚ :=
  ![495/128, -1023/512, -21/16, 639/256, -81/64, -45/256, 9/16, -321/1024, 21/256, -9/1024]
def coefficientsC : Fin 10 → ℚ :=
  ![315/128, 357/512, -105/64, -315/256, 21/64, 165/256, 9/64, -105/1024, -15/256, -9/1024]
def coefficientsARate : Fin 10 → ℚ :=
  ![0, -2805/256, 645/32, -1215/128, -45/16, 1125/128, -405/32, 5565/512, -75/16, 405/512]
def coefficientsBRate : Fin 10 → ℚ :=
  ![4185/128, -6315/256, 285/32, 405/128, -675/64, 1845/128, -405/32, 3495/512, -525/256, 135/512]
def coefficientsCRate : Fin 10 → ℚ :=
  ![2925/128, 2445/256, -525/64, -1215/128, -345/64, -375/128, 45/64, 1335/512, 375/256, 135/512]

def cosinePolynomial : ℕ → ℝ → ℝ
  | 0, _ => 1
  | 1, c => c
  | n + 2, c => 2 * c * cosinePolynomial (n + 1) c - cosinePolynomial n c

theorem cosinePolynomial_eq_chebyshev (n : ℕ) (c : ℝ) :
    cosinePolynomial n c = (Polynomial.Chebyshev.T ℝ (n : ℤ)).eval c := by
  induction n using Nat.twoStepInduction with
  | zero => simp [cosinePolynomial]
  | one => simp [cosinePolynomial]
  | more n hn hn1 =>
    rw [cosinePolynomial, hn, hn1]
    push_cast
    rw [Polynomial.Chebyshev.T_add_two]
    simp

theorem cosinePolynomial_cos (n : ℕ) (z : ℝ) :
    cosinePolynomial n (Real.cos z) = Real.cos (n * z) := by
  rw [cosinePolynomial_eq_chebyshev, Polynomial.Chebyshev.T_real_cos]
  norm_cast

def multiplicity (k : Fin 10) : ℚ := if k = 0 then 1 else 2
def cosineSum (a : Fin 10 → ℚ) (c : ℝ) : ℝ :=
  ∑ k, ((multiplicity k * a k : ℚ) : ℝ) * cosinePolynomial k.val c

theorem cosineSum_cos (a : Fin 10 → ℚ) (z : ℝ) :
    cosineSum a (Real.cos z) =
      ∑ k, ((multiplicity k * a k : ℚ) : ℝ) * Real.cos (k.val * z) := by
  simp only [cosineSum, cosinePolynomial_cos]

theorem cosine_expansions (c : ℝ) :
    polynomialA c = cosineSum coefficientsA c ∧
    polynomialB c = cosineSum coefficientsB c ∧
    polynomialC c = cosineSum coefficientsC c ∧
    polynomialARate c = cosineSum coefficientsARate c ∧
    polynomialBRate c = cosineSum coefficientsBRate c ∧
    polynomialCRate c = cosineSum coefficientsCRate c := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    norm_num [cosineSum, Fin.sum_univ_succ, multiplicity, coefficientsA, coefficientsB,
    coefficientsC, coefficientsARate, coefficientsBRate, coefficientsCRate, cosinePolynomial,
    polynomialA, polynomialB, polynomialC, polynomialARate, polynomialBRate, polynomialCRate] <;> ring

/-- The separated inverse-Laplacian pairing. The `1` and `5` are the
transverse squared frequencies; all ±z multiplicities are included. -/
def spectralWork : ℚ :=
  ∑ k : Fin 10, multiplicity k *
    (coefficientsA k * coefficientsARate k / (1 + (k.val : ℚ) ^ 2) +
      (coefficientsB k * coefficientsBRate k + coefficientsC k * coefficientsCRate k) /
        (2 * (5 + (k.val : ℚ) ^ 2)))

theorem spectralWork_eq : spectralWork = 16932543012172819 / 351018510581760 := by
  norm_num [spectralWork, Fin.sum_univ_succ, multiplicity, coefficientsA, coefficientsB,
    coefficientsC, coefficientsARate, coefficientsBRate, coefficientsCRate]

theorem spectralWork_pos : 0 < spectralWork := by
  rw [spectralWork_eq]
  norm_num

/-- The corresponding squared-gradient spectral sum, without inverse-Laplacian weights. -/
def spectralDissipation : ℚ :=
  ∑ k : Fin 10, multiplicity k *
    (coefficientsA k ^ 2 + (coefficientsB k ^ 2 + coefficientsC k ^ 2) / 2)

theorem spectralDissipation_eq : spectralDissipation = 5565537 / 131072 := by
  norm_num [spectralDissipation, Fin.sum_univ_succ, multiplicity,
    coefficientsA, coefficientsB, coefficientsC]

theorem spectralDissipation_pos : 0 < spectralDissipation := by
  rw [spectralDissipation_eq]
  norm_num

theorem spectralDissipation_lt_work : spectralDissipation < spectralWork := by
  rw [spectralDissipation_eq, spectralWork_eq]
  norm_num

end Mettapedia.FluidDynamics.NavierStokes.TwoShearViscousCertificate
