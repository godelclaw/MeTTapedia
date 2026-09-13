import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.ParallelHeatCorrelation

/-!
# Explicit finite horizontal sine data for the correlation test

The complementary profile uses eleven sine modes. This file certifies its
horizontal support, reality, zero mean, and exact infinite-equation heat
evolution. It does not certify the sign of its octic correlation derivative.
The rational diagnostic uses a `2π`-periodic torus; the coefficients here use
the unit-torus convention, so spatial derivatives carry an extra `2π`.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.ParallelHeatFlow

open scoped ComplexConjugate
open PeriodicFourierTriad PancakeLocalInfiniteVelocity

/-- Fourier coefficients of `c sin(2π k·x)`, including the zero-frequency case. -/
def sineCoefficients (k : Wavevector) (c : ℝ) : Wavevector →₀ ℂ :=
  Finsupp.single k (-Complex.I * (c : ℂ) / 2) +
    Finsupp.single (-k) (Complex.I * (c : ℂ) / 2)

theorem sineCoefficients_horizontal (k : Wavevector) (hk : k 2 = 0) (c : ℝ) :
    IsHorizontal (sineCoefficients k c) := by
  intro q hq
  have hqk : q ≠ k := by intro h; exact hq (h ▸ hk)
  have hqn : q ≠ -k := by intro h; apply hq; simpa [h] using congrArg Neg.neg hk
  simp [sineCoefficients, Finsupp.single_eq_of_ne hqk, Finsupp.single_eq_of_ne hqn]

theorem sineCoefficients_reality (k q : Wavevector) (c : ℝ) :
    sineCoefficients k c (-q) = conj (sineCoefficients k c q) := by
  simp only [sineCoefficients, Finsupp.add_apply, Finsupp.single_apply, map_add,
    apply_ite, map_div₀, map_neg, map_mul, Complex.conj_I, Complex.conj_ofReal,
    map_ofNat, map_zero, neg_eq_iff_eq_neg, neg_neg]
  split_ifs <;> ring

theorem sineCoefficients_zero (k : Wavevector) (c : ℝ) :
    sineCoefficients k c 0 = 0 := by
  by_cases hk : k = 0
  · simp [sineCoefficients, hk]
    ring
  · have hn : -k ≠ 0 := neg_ne_zero.mpr hk
    simp [sineCoefficients, Finsupp.single_eq_of_ne' hk, Finsupp.single_eq_of_ne' hn]

/-- A finite list of horizontal wavevectors and real amplitudes. -/
def sineData (modes : List (ℤ × ℤ × ℚ)) : Wavevector →₀ ℂ :=
  (modes.map fun p ↦ sineCoefficients ![p.1, p.2.1, 0] (p.2.2 : ℝ)).sum

theorem sineData_horizontal (modes : List (ℤ × ℤ × ℚ)) : IsHorizontal (sineData modes) := by
  induction modes with
  | nil => intro q _; simp [sineData]
  | cons p ps ih =>
    intro q hq
    have hp := sineCoefficients_horizontal ![p.1, p.2.1, 0] (by simp) (p.2.2 : ℝ) q hq
    simpa [sineData] using congrArg₂ (· + ·) hp (ih q hq)

theorem sineData_reality (modes : List (ℤ × ℤ × ℚ)) (q : Wavevector) :
    sineData modes (-q) = conj (sineData modes q) := by
  induction modes with
  | nil => simp [sineData]
  | cons p ps ih =>
    simpa [sineData, map_add] using congrArg₂ (· + ·)
      (sineCoefficients_reality ![p.1, p.2.1, 0] q (p.2.2 : ℝ)) ih

theorem sineData_zero (modes : List (ℤ × ℤ × ℚ)) : sineData modes 0 = 0 := by
  induction modes with
  | nil => simp [sineData]
  | cons p ps ih => simpa [sineData, sineCoefficients_zero] using ih

/-- Frequencies and rational amplitudes of the complementary profile used in
`ns_octic_parallel_shear_sanity.py`. The rapid frequency is explicit, not a cutoff. -/
def complementaryModes (k : ℤ) (δ : ℚ) : List (ℤ × ℤ × ℚ) :=
  [(0, 1, 35/64), (0, 3, 7/64), (0, 5, 7/320), (0, 7, 1/448),
   (k, 0, δ / (k : ℚ) * (10/32)),
   (k, 2, δ / (k : ℚ) * (-15/64)), (k, -2, δ / (k : ℚ) * (-15/64)),
   (k, 4, δ / (k : ℚ) * (6/64)), (k, -4, δ / (k : ℚ) * (6/64)),
   (k, 6, δ / (k : ℚ) * (-1/64)), (k, -6, δ / (k : ℚ) * (-1/64))]

def complementaryData : Wavevector →₀ ℂ := sineData (complementaryModes 65536 (1/8))

/-- The diagnostic profile has an actual infinite-equation solution on every
finite forward interval. No correlation sign is part of this construction. -/
def complementarySolution {ν : ℝ} (hν : 0 ≤ ν) (T : ℝ) :
    LocalInfiniteVelocitySolution ν (fun q ↦ vertical (complementaryData q)) T
      (initialSobolevEnergy complementaryData) :=
  solution hν complementaryData (sineData_horizontal _) (sineData_reality _)
    (sineData_zero _) T

end Mettapedia.FluidDynamics.NavierStokes.ParallelHeatFlow
