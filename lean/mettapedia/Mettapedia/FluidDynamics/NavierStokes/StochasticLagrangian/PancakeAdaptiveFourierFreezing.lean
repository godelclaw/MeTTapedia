import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeQuadraticFourierSupport

/-!
# Freezing estimates after adaptive Fourier replacement

The adaptive partition has exact cell subordination, while its quadratic
Fourier replacement has small global tails.  This file quantifies the cost of
that replacement in the strain-freezing estimate.  The loss is explicit in
the uniform weight error, the finite cell count, and a global bound for the
operator oscillation; no exact support is assumed.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes
namespace PancakeAdaptiveFourierFreezing

open scoped BigOperators
open PancakeFrameCovariance
open PancakeAdaptiveStrainCover
open PancakeQuadraticFourierSupport
open PancakeAdaptiveFourierPartition
open PancakeFiniteFourierLocalization
open PancakeBufferedAnnularMultiplier
open PancakeFrameCovariance
open PancakeAnnularSectorProjector

local notation "R3" => EuclideanSpace ℝ (Fin 3)

/-- Replacing subordinate partition weights by uniformly close weights costs
at most `card · eta · M`, where `M` bounds every freezing error globally.
This is the elementary tail-aggregation estimate needed when exact spatial
support is replaced by Fourier leakage. -/
theorem sum_approxWeight_mul_freezingError_le
    {X E ι : Type*} [TopologicalSpace X] [NormedAddCommGroup E]
    [Fintype ι]
    (weight : PartitionOfUnity ι X) (approxWeight : ι → X → ℝ)
    (A : X → E) (center : ι → X)
    (epsilon eta M : ℝ) (heta : 0 ≤ eta)
    (hactive : ∀ i x, weight i x ≠ 0 →
      ‖A x - A (center i)‖ ≤ epsilon)
    (happrox : ∀ i x, |approxWeight i x - weight i x| ≤ eta)
    (hglobal : ∀ i x, ‖A x - A (center i)‖ ≤ M)
    (x : X) :
    ∑ i : ι, approxWeight i x * ‖A x - A (center i)‖ ≤
      epsilon + (Fintype.card ι : ℝ) * eta * M := by
  have hpartition := sum_weight_mul_freezingError_le
    weight A center epsilon hactive x
  calc
    ∑ i : ι, approxWeight i x * ‖A x - A (center i)‖ ≤
        ∑ i : ι, (weight i x * ‖A x - A (center i)‖ + eta * M) := by
      apply Finset.sum_le_sum
      intro i hi
      calc
        approxWeight i x * ‖A x - A (center i)‖ =
            weight i x * ‖A x - A (center i)‖ +
              (approxWeight i x - weight i x) *
                ‖A x - A (center i)‖ := by ring
        _ ≤ weight i x * ‖A x - A (center i)‖ +
              |approxWeight i x - weight i x| *
                ‖A x - A (center i)‖ := by
            gcongr
            exact le_abs_self _
        _ ≤ weight i x * ‖A x - A (center i)‖ + eta * M := by
            exact add_le_add (le_refl _)
              (mul_le_mul (happrox i x) (hglobal i x)
                (norm_nonneg _) heta)
    _ = (∑ i : ι, weight i x * ‖A x - A (center i)‖) +
          (Fintype.card ι : ℝ) * eta * M := by
      rw [Finset.sum_add_distrib]
      simp
      ring
    _ ≤ epsilon + (Fintype.card ι : ℝ) * eta * M := by
      gcongr

/-- Specialization to the nonnegative quadratic Fourier weights produced by
the adaptive partition construction. -/
theorem sum_quadraticFourierWeight_mul_freezingError_le
    {E ι : Type*} [NormedAddCommGroup E]
    [Fintype ι]
    (weight : PartitionOfUnity ι (UnitAddTorus (Fin 3)))
    (coeff : ι → FourierCoeff (Fin 3))
    (A : UnitAddTorus (Fin 3) → E)
    (center : ι → UnitAddTorus (Fin 3))
    (epsilon delta M : ℝ) (hdelta : 0 ≤ delta)
    (hactive : ∀ i x, weight i x ≠ 0 →
      ‖A x - A (center i)‖ ≤ epsilon)
    (happrox : ∀ i x,
      |Complex.normSq (fourierPolynomial (coeff i) x) - weight i x| ≤
        delta * (delta + 2))
    (hglobal : ∀ i x, ‖A x - A (center i)‖ ≤ M)
    (x : UnitAddTorus (Fin 3)) :
    ∑ i : ι, Complex.normSq (fourierPolynomial (coeff i) x) *
        ‖A x - A (center i)‖ ≤
      epsilon + (Fintype.card ι : ℝ) *
        (delta * (delta + 2)) * M := by
  apply sum_approxWeight_mul_freezingError_le
    weight (fun i x ↦ Complex.normSq (fourierPolynomial (coeff i) x))
      A center epsilon (delta * (delta + 2)) M
  · positivity
  · exact hactive
  · exact happrox
  · exact hglobal

/-- Applying the Fourier-weighted strain error to a vector retains the same
tail loss, multiplied only by the vector norm. -/
theorem sum_quadraticFourierWeight_mul_norm_strainError_apply_le
    {ι : Type*} [Fintype ι]
    (weight : PartitionOfUnity ι (UnitAddTorus (Fin 3)))
    (coeff : ι → FourierCoeff (Fin 3))
    (strain : UnitAddTorus (Fin 3) → (R3 →L[ℝ] R3))
    (center : ι → UnitAddTorus (Fin 3))
    (epsilon delta M : ℝ) (hdelta : 0 ≤ delta)
    (hactive : ∀ i x, weight i x ≠ 0 →
      ‖strain x - strain (center i)‖ ≤ epsilon)
    (happrox : ∀ i x,
      |Complex.normSq (fourierPolynomial (coeff i) x) - weight i x| ≤
        delta * (delta + 2))
    (hglobal : ∀ i x, ‖strain x - strain (center i)‖ ≤ M)
    (x : UnitAddTorus (Fin 3)) (v : R3) :
    ∑ i : ι, Complex.normSq (fourierPolynomial (coeff i) x) *
        ‖(strain x - strain (center i)) v‖ ≤
      (epsilon + (Fintype.card ι : ℝ) *
        (delta * (delta + 2)) * M) * ‖v‖ := by
  have hfreeze := sum_quadraticFourierWeight_mul_freezingError_le
    weight coeff strain center epsilon delta M hdelta hactive
      happrox hglobal x
  calc
    ∑ i : ι, Complex.normSq (fourierPolynomial (coeff i) x) *
        ‖(strain x - strain (center i)) v‖ ≤
        ∑ i : ι, Complex.normSq (fourierPolynomial (coeff i) x) *
          (‖strain x - strain (center i)‖ * ‖v‖) := by
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul_of_nonneg_left
        (ContinuousLinearMap.le_opNorm _ _)
        (Complex.normSq_nonneg _)
    _ = (∑ i : ι, Complex.normSq (fourierPolynomial (coeff i) x) *
          ‖strain x - strain (center i)‖) * ‖v‖ := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ ≤ (epsilon + (Fintype.card ι : ℝ) *
          (delta * (delta + 2)) * M) * ‖v‖ :=
      mul_le_mul_of_nonneg_right hfreeze (norm_nonneg v)

/-- The complete spatial freezing package: one quadratic Fourier family
simultaneously has nondegenerate coverage, quantified off-cell leakage,
common buffered-frequency margins, and the explicit perturbed strain-freezing
bound. -/
theorem exists_adaptiveQuadraticFourierFreezingPackage
    {ι : Type*} [Fintype ι]
    (weight : PartitionOfUnity ι (UnitAddTorus (Fin 3)))
    (strain : UnitAddTorus (Fin 3) → (R3 →L[ℝ] R3))
    (center : ι → UnitAddTorus (Fin 3))
    (epsilon M : ℝ) {delta : ℝ} (hdelta : 0 < delta)
    (hsmall :
      (Fintype.card ι : ℝ) * (delta * (delta + 2)) ≤ 1 / 2)
    (hactive : ∀ i x, weight i x ≠ 0 →
      ‖strain x - strain (center i)‖ ≤ epsilon)
    (hglobal : ∀ i x, ‖strain x - strain (center i)‖ ≤ M) :
    ∃ (coeff : ι → FourierCoeff (Fin 3)) (N₀ : ℕ),
      2 ≤ N₀ ∧
      (∀ x,
        1 / 2 ≤ ∑ i : ι,
          Complex.normSq (fourierPolynomial (coeff i) x) ∧
        (∑ i : ι,
          Complex.normSq (fourierPolynomial (coeff i) x)) ≤ 3 / 2) ∧
      (∀ i x, weight i x = 0 →
        Complex.normSq (fourierPolynomial (coeff i) x) < delta ^ 2) ∧
      (∀ (i : ι) (F : OrientedFrameEquiv) (N : ℕ), N₀ ≤ N →
        ∀ p ∈ (quadraticFourierCoeff (coeff i)).support,
          InNormalizedPancakeShift
            localizationTransverseMargin localizationAxialMargin
            (orientedFrameSquareDyadicNormalizedMode F N p)) ∧
      (∀ x v,
        ∑ i : ι, Complex.normSq (fourierPolynomial (coeff i) x) *
            ‖(strain x - strain (center i)) v‖ ≤
          (epsilon + (Fintype.card ι : ℝ) *
            (delta * (delta + 2)) * M) * ‖v‖) := by
  obtain ⟨coeff, N₀, hpkg⟩ :=
    exists_adaptiveQuadraticFourierPackage weight hdelta hsmall
  have hN₀ := hpkg.1
  have happrox := hpkg.2.1
  have hcover := hpkg.2.2.1
  have hleak := hpkg.2.2.2.1
  have hmargin := hpkg.2.2.2.2
  refine ⟨coeff, N₀, hN₀, hcover, hleak, hmargin, ?_⟩
  intro x v
  exact sum_quadraticFourierWeight_mul_norm_strainError_apply_le
    weight coeff strain center epsilon delta M hdelta.le hactive
      happrox hglobal x v

end PancakeAdaptiveFourierFreezing
end NavierStokes
end FluidDynamics
end Mettapedia
