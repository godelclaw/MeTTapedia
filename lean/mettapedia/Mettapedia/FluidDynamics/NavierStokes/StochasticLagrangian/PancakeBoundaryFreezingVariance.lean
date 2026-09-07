import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakePhysicalBoundaryDepletion

/-!
# Quantified quadratic freezing variance after Fourier approximation

The subordinate partition pays the local squared oscillation. Each Fourier
weight approximation pays its own error times a global squared oscillation
bound. These costs are retained explicitly; no uniform frequency margin or
time budget is inferred from spatial approximation alone.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PancakeBoundaryFreezingVariance

open MeasureTheory
open PeriodicFourierTriad PancakeDyadicDirectionEvolution PancakeQuadraticFourierSupport
open PancakeQuadraticProjectionLocalization PancakeAdaptiveStrainCover
open PancakePhysicalBoundaryDepletion PancakePhysicalSpectralDefect
open PancakeFourierMaterialPaths PancakeFilteredStrainDynamics PancakeMaterialDiffusionBudget
open PancakeSpectralDefectEvolution PancakeSpectralProjectorRegularity.SymmetricStrain

local notation "T3" => UnitAddTorus (Fin 3)

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

theorem sum_approxWeight_sq_freezingError_le
    {X E ι : Type*} [TopologicalSpace X] [NormedAddCommGroup E] [Fintype ι]
    (weight : PartitionOfUnity ι X) (rho : ι → X → ℝ) (A : X → E) (center : ι → X)
    (epsilon : ℝ) (eta L : ι → ℝ) (hepsilon : 0 ≤ epsilon) (heta : ∀ i, 0 ≤ eta i)
    (hL : ∀ i, 0 ≤ L i)
    (hactive : ∀ i x, weight i x ≠ 0 → ‖A x - A (center i)‖ ≤ epsilon)
    (happrox : ∀ i x, |rho i x - weight i x| ≤ eta i)
    (hglobal : ∀ i x, ‖A x - A (center i)‖ ≤ L i) (x : X) :
    (∑ i : ι, rho i x * ‖A x - A (center i)‖ ^ 2) ≤
      epsilon ^ 2 + ∑ i : ι, eta i * L i ^ 2 := by
  have hp := sum_weight_mul_sq_freezingError_le weight A center epsilon hepsilon hactive x
  calc
    _ ≤ ∑ i : ι, (weight i x * ‖A x - A (center i)‖ ^ 2 + eta i * L i ^ 2) := by
      apply Finset.sum_le_sum
      intro i _
      have hd := (abs_le.mp (happrox i x)).2
      have hg : ‖A x - A (center i)‖ ^ 2 ≤ L i ^ 2 := by
        nlinarith [hglobal i x, hL i, norm_nonneg (A x - A (center i))]
      have h1 := mul_nonneg (sub_nonneg.mpr hd) (sq_nonneg ‖A x - A (center i)‖)
      have h2 := mul_nonneg (heta i) (sub_nonneg.mpr hg)
      nlinarith
    _ = (∑ i : ι, weight i x * ‖A x - A (center i)‖ ^ 2) +
        ∑ i : ι, eta i * L i ^ 2 := Finset.sum_add_distrib
    _ ≤ _ := add_le_add hp (le_refl _)

theorem sum_quadraticWeight_sq_freezingError_le
    {E ι : Type*} [NormedAddCommGroup E] [Fintype ι]
    (weight : PartitionOfUnity ι T3) (c : ι → FourierCoeff (Fin 3)) (A : T3 → E) (center : ι → T3)
    (epsilon eta L : ℝ) (hepsilon : 0 ≤ epsilon) (heta : 0 ≤ eta) (hL : 0 ≤ L)
    (hactive : ∀ i x, weight i x ≠ 0 → ‖A x - A (center i)‖ ≤ epsilon)
    (happrox : ∀ i x, |quadraticWeight (c i) x - weight i x| ≤ eta)
    (hglobal : ∀ i x, ‖A x - A (center i)‖ ≤ L) (x : T3) :
    (∑ i : ι, quadraticWeight (c i) x * ‖A x - A (center i)‖ ^ 2) ≤
      epsilon ^ 2 + (Fintype.card ι : ℝ) * eta * L ^ 2 := by
  have h := sum_approxWeight_sq_freezingError_le weight (fun i ↦ quadraticWeight (c i)) A center
    epsilon (fun _ ↦ eta) (fun _ ↦ L) hepsilon (fun _ ↦ heta) (fun _ ↦ hL) hactive happrox hglobal x
  simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_assoc] using h

theorem integral_physicalBoundary_energy_le_variance {ι : Type*} [Fintype ι]
    (c : ι → FourierCoeff (Fin 3)) (center : ι → T3) (chi : Wavevector → ℂ)
    (modes : Finset Wavevector) (u : FourierVelocity) (C V : ℝ)
    (hs : ∀ q, -q ∈ modes ↔ q ∈ modes)
    (hC : ∀ x : T3, ∑ i : ι, quadraticWeight (c i) x ≤ C)
    (hV : ∀ x : T3, (∑ i : ι, quadraticWeight (c i) x *
      ‖(spatialStrain modes (filteredVelocity chi u) (center i)).1 -
        (spatialStrain modes (filteredVelocity chi u) x).1‖ ^ 2) ≤ V) :
    (∫ x : T3, ‖physicalBoundaryField c center chi modes u x‖ ^ 2) ≤
      2 * C ^ 2 * (∫ x : T3, ‖spectralResidual (spatialStrain modes (filteredVelocity chi u) x).1
        (topEigenvalue (spatialStrain modes (filteredVelocity chi u) x)) (spatialVorticity modes u x)‖ ^ 2) +
      8 * C * V * ∫ x : T3, ‖spatialVorticity modes u x‖ ^ 2 := by
  let S := spatialStrain modes (filteredVelocity chi u)
  have hS := continuous_strain modes (filteredVelocity chi u)
  have hw := continuous_vorticity modes u
  have hC0 : 0 ≤ C := (Finset.sum_nonneg (fun i _ ↦
    (show 0 ≤ quadraticWeight (c i) (0 : T3) from Complex.normSq_nonneg _))).trans (hC 0)
  have he : Continuous (fun x : T3 ↦ ∑ i : ι, quadraticWeight (c i) x *
      ‖(S (center i)).1 - (S x).1‖ ^ 2 * ‖spatialVorticity modes u x‖ ^ 2) :=
    continuous_finsetSum _ (fun i _ ↦ ((continuous_quadraticWeight (c i)).mul
      ((continuous_const.sub (continuous_subtype_val.comp hS)).norm.pow 2)).mul (hw.norm.pow 2))
  have hInt : (∫ x : T3, ∑ i : ι, quadraticWeight (c i) x *
      ‖(S (center i)).1 - (S x).1‖ ^ 2 * ‖spatialVorticity modes u x‖ ^ 2) ≤
      V * ∫ x : T3, ‖spatialVorticity modes u x‖ ^ 2 := by
    rw [← integral_const_mul]
    apply integral_mono
      (he.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
      (((hw.norm.pow 2).const_mul V).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
    intro x
    dsimp only
    rw [← Finset.sum_mul]
    exact mul_le_mul_of_nonneg_right (hV x) (sq_nonneg _)
  apply (integral_physicalBoundary_energy_unfrozen c center chi modes u C hs hC).trans
  simpa only [mul_assoc] using add_le_add (le_refl _)
    (mul_le_mul_of_nonneg_left hInt (show 0 ≤ 8 * C by positivity))

/-- The same constructed Fourier family has coverage, off-cell leakage,
and the actual strain-weighted boundary estimate. The partition is supplied;
its adaptive construction is in `PancakeAdaptiveStrainCover`. -/
theorem exists_quadratic_physicalBoundary_energy_package {ι : Type*} [Fintype ι]
    (weight : PartitionOfUnity ι T3) (center : ι → T3) (chi : Wavevector → ℂ)
    (modes : Finset Wavevector) (u : FourierVelocity) (epsilon L delta : ℝ)
    (hepsilon : 0 ≤ epsilon) (hL : 0 ≤ L) (hdelta : 0 < delta)
    (hs : ∀ q, -q ∈ modes ↔ q ∈ modes)
    (hsmall : (Fintype.card ι : ℝ) * (delta * (delta + 2)) ≤ 1 / 2)
    (hactive : ∀ i x, weight i x ≠ 0 →
      ‖(spatialStrain modes (filteredVelocity chi u) x).1 -
        (spatialStrain modes (filteredVelocity chi u) (center i)).1‖ ≤ epsilon)
    (hglobal : ∀ i x, ‖(spatialStrain modes (filteredVelocity chi u) x).1 -
      (spatialStrain modes (filteredVelocity chi u) (center i)).1‖ ≤ L) :
    ∃ c : ι → FourierCoeff (Fin 3),
      (∀ x : T3, 1 / 2 ≤ ∑ i : ι, quadraticWeight (c i) x ∧
        (∑ i : ι, quadraticWeight (c i) x) ≤ 3 / 2) ∧
      (∀ i x, weight i x = 0 → quadraticWeight (c i) x < delta ^ 2) ∧
      (∫ x : T3, ‖physicalBoundaryField c center chi modes u x‖ ^ 2) ≤
        (9 / 2) * (∫ x : T3, ‖spectralResidual (spatialStrain modes (filteredVelocity chi u) x).1
          (topEigenvalue (spatialStrain modes (filteredVelocity chi u) x)) (spatialVorticity modes u x)‖ ^ 2) +
        12 * (epsilon ^ 2 + (Fintype.card ι : ℝ) * (delta * (delta + 2)) * L ^ 2) *
          ∫ x : T3, ‖spatialVorticity modes u x‖ ^ 2 := by
  obtain ⟨c, _, _, happrox, hcov, hleak, _⟩ := exists_adaptiveQuadraticFourierPackage weight hdelta hsmall
  refine ⟨c, hcov, hleak, ?_⟩
  have hV (x : T3) : (∑ i : ι, quadraticWeight (c i) x *
      ‖(spatialStrain modes (filteredVelocity chi u) (center i)).1 -
        (spatialStrain modes (filteredVelocity chi u) x).1‖ ^ 2) ≤
      epsilon ^ 2 + (Fintype.card ι : ℝ) * (delta * (delta + 2)) * L ^ 2 := by
    simp_rw [norm_sub_rev]
    exact sum_quadraticWeight_sq_freezingError_le weight c
      (fun y ↦ (spatialStrain modes (filteredVelocity chi u) y).1) center epsilon (delta * (delta + 2)) L
      hepsilon (by positivity) hL hactive happrox hglobal x
  have h := integral_physicalBoundary_energy_le_variance c center chi modes u (3 / 2)
    (epsilon ^ 2 + (Fintype.card ι : ℝ) * (delta * (delta + 2)) * L ^ 2) hs (fun x ↦ (hcov x).2) hV
  norm_num only [show 2 * (3 / 2 : ℝ) ^ 2 = 9 / 2 by norm_num,
    show 8 * (3 / 2 : ℝ) = 12 by norm_num] at h
  exact h

end Mettapedia.FluidDynamics.NavierStokes.PancakeBoundaryFreezingVariance
