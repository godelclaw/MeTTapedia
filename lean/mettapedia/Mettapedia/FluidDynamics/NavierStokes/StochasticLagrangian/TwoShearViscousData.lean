import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.StretchingFluxFiniteCoefficients
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.StretchingFluxSpectralEvolution

/-!
# Admissible Fourier data for the complementary two-shear test

The seven longitudinal coefficients are those of `(1 + cos z)^3`.
Reflection multiplies the odd longitudinal frequencies by minus one.
The transverse sine factors give real, mean-zero, divergence-free data
with finite support. No finite-mode invariant NS evolution is assumed.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.TwoShearViscousData

open scoped ComplexConjugate
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeBlockReality
open PancakeCurlOutputTail PancakeInfiniteSpatialLaplacian
open StretchingFluxFiniteCoefficients StretchingFluxSpectralEvolution

/-- Complex-exponential coefficients, not cosine-series amplitudes. -/
def profile (k : ℤ) : ℚ :=
  match k.natAbs with
  | 0 => 5 / 2
  | 1 => 15 / 8
  | 2 => 3 / 4
  | 3 => 1 / 8
  | _ => 0

def reflectedProfile (k : ℤ) : ℚ := (-1) ^ k.natAbs * profile k

@[simp] theorem profile_neg (k : ℤ) : profile (-k) = profile k := by simp [profile]

@[simp] theorem reflectedProfile_neg (k : ℤ) : reflectedProfile (-k) = reflectedProfile k := by
  simp [reflectedProfile]

theorem profile_eq_zero (k : ℤ) (hk : ¬ (-3 ≤ k ∧ k ≤ 3)) : profile k = 0 := by
  have h : 3 < k.natAbs := by omega
  unfold profile
  split <;> first | rfl | omega

theorem profile_cosine_expansion (z : ℝ) :
    (profile 0 : ℝ) + 2 * ((profile 1 : ℝ) * Real.cos z +
      (profile 2 : ℝ) * Real.cos (2 * z) + (profile 3 : ℝ) * Real.cos (3 * z)) =
        (1 + Real.cos z) ^ 3 := by
  norm_num [profile, Real.cos_two_mul, Real.cos_three_mul]
  ring

theorem reflectedProfile_cosine_expansion (z : ℝ) :
    (reflectedProfile 0 : ℝ) + 2 * ((reflectedProfile 1 : ℝ) * Real.cos z +
      (reflectedProfile 2 : ℝ) * Real.cos (2 * z) +
        (reflectedProfile 3 : ℝ) * Real.cos (3 * z)) = (1 - Real.cos z) ^ 3 := by
  norm_num [reflectedProfile, profile, Real.cos_two_mul, Real.cos_three_mul]
  ring

def firstHorizontal (q : Wavevector) : Prop := q 0 = 0 ∧ (q 1 = 1 ∨ q 1 = -1)
def secondHorizontal (q : Wavevector) : Prop := q 1 = 0 ∧ (q 0 = 1 ∨ q 0 = -1)

instance instDecidableFirstHorizontal (q : Wavevector) : Decidable (firstHorizontal q) :=
  inferInstanceAs (Decidable (q 0 = 0 ∧ (q 1 = 1 ∨ q 1 = -1)))
instance instDecidableSecondHorizontal (q : Wavevector) : Decidable (secondHorizontal q) :=
  inferInstanceAs (Decidable (q 1 = 0 ∧ (q 0 = 1 ∨ q 0 = -1)))

def velocity (q : Wavevector) : VelocityCoefficient :=
  ![if firstHorizontal q then -Complex.I * (q 1 : ℂ) * (profile (q 2) : ℂ) / 2 else 0,
    if secondHorizontal q then -Complex.I * (q 0 : ℂ) * (reflectedProfile (q 2) : ℂ) / 2 else 0,
    0]

def horizontalModes : Finset (ℤ × ℤ) := {(0, 1), (0, -1), (1, 0), (-1, 0)}

def modes : Finset Wavevector :=
  (horizontalModes ×ˢ Finset.Icc (-3 : ℤ) 3).image (fun p ↦ ![p.1.1, p.1.2, p.2])

theorem mem_modes (q : Wavevector) :
    q ∈ modes ↔ (firstHorizontal q ∨ secondHorizontal q) ∧ -3 ≤ q 2 ∧ q 2 ≤ 3 := by
  classical
  constructor
  · intro h
    obtain ⟨⟨⟨a, b⟩, k⟩, hp, rfl⟩ := Finset.mem_image.mp h
    rcases Finset.mem_product.mp hp with ⟨hab, hk⟩
    have hk' := Finset.mem_Icc.mp hk
    simp only [horizontalModes, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at hab
    rcases hab with h | h | h | h <;> rcases h with ⟨rfl, rfl⟩ <;>
      simpa [firstHorizontal, secondHorizontal] using hk'
  · rintro ⟨hh, hz⟩
    refine Finset.mem_image.mpr ⟨((q 0, q 1), q 2), ?_, ?_⟩
    · apply Finset.mem_product.mpr
      refine ⟨?_, Finset.mem_Icc.mpr hz⟩
      rcases hh with ⟨h0, h1 | h1⟩ | ⟨h1, h0 | h0⟩ <;>
        simp [horizontalModes, h0, h1]
    · ext i
      fin_cases i <;> rfl

theorem supported (q : Wavevector) (hq : q ∉ modes) : velocity q = 0 := by
  have hn := mt (mem_modes q).mpr hq
  by_cases hz : -3 ≤ q 2 ∧ q 2 ≤ 3
  · have hh : ¬ (firstHorizontal q ∨ secondHorizontal q) := fun h ↦ hn ⟨h, hz⟩
    simp only [not_or] at hh
    ext i
    fin_cases i <;> simp [velocity, hh.1, hh.2]
  · have hp := profile_eq_zero (q 2) hz
    ext i
    fin_cases i <;> simp [velocity, reflectedProfile, hp]

theorem transverse (q : Wavevector) : modeDot q (velocity q) = 0 := by
  have h0 : (q 0 : ℂ) *
      (if firstHorizontal q then -Complex.I * (q 1 : ℂ) * (profile (q 2) : ℂ) / 2 else 0) = 0 := by
    by_cases h : firstHorizontal q <;> simp [h, show firstHorizontal q → q 0 = 0 from And.left]
  have h1 : (q 1 : ℂ) *
      (if secondHorizontal q then -Complex.I * (q 0 : ℂ) * (reflectedProfile (q 2) : ℂ) / 2 else 0) = 0 := by
    by_cases h : secondHorizontal q <;> simp [h, show secondHorizontal q → q 1 = 0 from And.left]
  simpa [modeDot, velocity, Fin.sum_univ_three] using congrArg₂ (· + ·) h0 h1

theorem firstHorizontal_neg (q : Wavevector) : firstHorizontal (-q) ↔ firstHorizontal q := by
  simp only [firstHorizontal, Pi.neg_apply]
  omega

theorem secondHorizontal_neg (q : Wavevector) : secondHorizontal (-q) ↔ secondHorizontal q := by
  simp only [secondHorizontal, Pi.neg_apply]
  omega

theorem reality (q : Wavevector) : velocity (-q) = coefficientConjugate (velocity q) := by
  ext i
  fin_cases i <;> simp [velocity, coefficientConjugate, firstHorizontal_neg, secondHorizontal_neg]
    <;> split_ifs <;> simp [map_div₀, map_mul, map_ofNat]

theorem velocity_zero : velocity 0 = 0 := by
  ext i
  fin_cases i <;> simp [velocity, firstHorizontal, secondHorizontal]

theorem all_moments (m : ℕ) : Summable (fourierMoment m velocity) :=
  FourierFiniteSupport.summable_fourierMoment modes velocity supported m

theorem heat_supported (q : Wavevector) (hq : q ∉ modes) : laplacianCoeff velocity q = 0 := by
  simp [laplacianCoeff, supported q hq]

theorem heat_all_moments (m : ℕ) : Summable (fourierMoment m (laplacianCoeff velocity)) :=
  FourierFiniteSupport.summable_fourierMoment modes _ heat_supported m

theorem heat_reality (q : Wavevector) :
    laplacianCoeff velocity (-q) = coefficientConjugate (laplacianCoeff velocity q) :=
  laplacianCoeff_reality velocity reality q

theorem flux_coefficient_eq_double_sum (j : Fin 3) (q : Wavevector) :
    StretchingFluxCoefficients.coefficients velocity j q =
      ∑ k ∈ modes, ∑ l ∈ modes,
        StretchingFluxCoefficients.interaction velocity j (k, (l, q - k - l)) :=
  coefficients_eq_double_sum velocity modes supported j q

end Mettapedia.FluidDynamics.NavierStokes.TwoShearViscousData
