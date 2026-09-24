import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.FiniteVorticityTensor

/-!
# Coercivity of a frequency-normalized projection correction

Finite Fourier support bounds the actual weighted palinstrophy by the
eighth moment. The proof passes through the polynomial quartic tensor,
so it has no Fourier-cardinality or pointwise-gradient loss. This is a
fixed-snapshot estimate, not a bound for the filtered evolution's sources.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.FiniteBandProjectionEnergy

open scoped RealInnerProductSpace
open MeasureTheory Mettapedia.Analysis PeriodicRadialRiesz QuarticTensorEnergy
open PeriodicFourierTriad PancakeCurlOutputTail PancakeFrequencyProjectorCommutator
open PancakeGalerkinKineticEnergy LocalLowDiffusionBudget LocalSpatialVorticityJets
open LocalVorticityEighthMoment GaussianRootWeightedIncrement
open LocalWeightedProjectionEvolution FourierFiniteSupport
open FiniteVorticityTensor FourierPolynomialDifferential
local notation "T3" => UnitAddTorus (Fin 3)
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

def tensorEnergy (u : FourierVelocity) : ℝ :=
  ∫ x : T3, ∑ i : Fin 3, ∑ j : Fin 3, quarticTensorEntry (fullVorticity u x) i j ^ 2

def tensorGradientEnergy (u : FourierVelocity) : ℝ :=
  ∫ x : T3, ∑ k : Fin 3, ∑ i : Fin 3, ∑ j : Fin 3,
    quarticTensorRate (fullVorticity u x) (fullCurlGradient u k x) i j ^ 2

theorem tensorEnergy_eq (u : FourierVelocity) : tensorEnergy u = meanEnergy u := by
  simp only [tensorEnergy, sum_quarticTensorEntry_sq, meanEnergy, energy_eq_norm_pow]

theorem tensorGradientEnergy_eq (u : FourierVelocity) (hu : Summable (fourierMoment 3 u)) :
    tensorGradientEnergy u = 2 * weightedPalinstrophy u + 14 * radialDissipation u := by
  have hiG : Integrable (weightedPalinstrophyDensity u) :=
    (continuous_weightedPalinstrophyDensity u hu).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hiR : Integrable (radialGradientDensity u) :=
    (continuous_radialGradientDensity u hu).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have he (x : T3) : (∑ k : Fin 3, ∑ i : Fin 3, ∑ j : Fin 3,
      quarticTensorRate (fullVorticity u x) (fullCurlGradient u k x) i j ^ 2) =
      2 * weightedPalinstrophyDensity u x + 14 * radialGradientDensity u x := by
    simp only [sum_quarticTensorRate_sq, weightedPalinstrophyDensity, radialGradientDensity,
      Finset.sum_add_distrib, Finset.mul_sum]
    congr 1 <;> apply Finset.sum_congr rfl <;> intro k _ <;> ring
  simp_rw [tensorGradientEnergy, he]
  rw [integral_add (hiG.const_mul 2) (hiR.const_mul 14), integral_const_mul, integral_const_mul]
  rfl

theorem tensorGradientEnergy_le (P : Finset Wavevector) (u : FourierVelocity)
    (hs : ∀ q, q ∉ P → u q = 0) (R : ℝ) (hP : ∀ q ∈ P, ‖frequencyVec q‖ ≤ R) :
    tensorGradientEnergy u ≤ (8 * Real.pi * R) ^ 2 * meanEnergy u := by
  have hu := summable_fourierMoment P u hs 3
  have ha := continuous_fullVorticity u
    (PancakeHigherDerivativeMoments.summable_fourierMoment_of_le _ (by omega : 1 ≤ 3) hu)
  have hi (k i j : Fin 3) : Integrable (fun x : T3 ↦
      quarticTensorRate (fullVorticity u x) (fullCurlGradient u k x) i j ^ 2) :=
    ((continuous_quarticTensorRate _ _ ha (LocalSquaredGapGradient.continuous_fullCurlGradient u k)
      i j).pow 2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hiE (i j : Fin 3) : Integrable (fun x : T3 ↦ quarticTensorEntry (fullVorticity u x) i j ^ 2) :=
    ((continuous_quarticTensorEntry _ ha i j).pow 2).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hbound (i j : Fin 3) :
      (∑ k : Fin 3, ∫ x : T3, quarticTensorRate (fullVorticity u x) (fullCurlGradient u k x) i j ^ 2) ≤
        (8 * Real.pi * R) ^ 2 * ∫ x : T3, quarticTensorEntry (fullVorticity u x) i j ^ 2 := by
    have h := integral_gradient_sq_le (tensorCoeff P u i j) (4 * R) (hasRadius_tensorCoeff P u R hP i j)
    simp_rw [fourierPolynomial_tensorDerivative P u hs, fourierPolynomial_tensorCoeff P u hs,
      Complex.norm_real, Real.norm_eq_abs, sq_abs] at h
    convert h using 1
    ring
  have heE : (∑ i : Fin 3, ∑ j : Fin 3, ∫ x : T3, quarticTensorEntry (fullVorticity u x) i j ^ 2) =
      meanEnergy u := by
    rw [← tensorEnergy_eq]
    unfold tensorEnergy
    rw [integral_finsetSum _ (fun i _ ↦ integrable_finsetSum _ (fun j _ ↦ hiE i j))]
    exact Finset.sum_congr rfl (fun i _ ↦ (integral_finsetSum _ (fun j _ ↦ hiE i j)).symm)
  have heG : tensorGradientEnergy u =
      ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3,
        ∫ x : T3, quarticTensorRate (fullVorticity u x) (fullCurlGradient u k x) i j ^ 2 := by
    unfold tensorGradientEnergy
    rw [integral_finsetSum _ (fun k _ ↦ integrable_finsetSum _ (fun i _ ↦
      integrable_finsetSum _ (fun j _ ↦ hi k i j)))]
    have he (k : Fin 3) :
        (∫ x : T3, ∑ i : Fin 3, ∑ j : Fin 3,
          quarticTensorRate (fullVorticity u x) (fullCurlGradient u k x) i j ^ 2) =
        ∑ i : Fin 3, ∑ j : Fin 3, ∫ x : T3,
          quarticTensorRate (fullVorticity u x) (fullCurlGradient u k x) i j ^ 2 := by
      rw [integral_finsetSum _ (fun i _ ↦ integrable_finsetSum _ (fun j _ ↦ hi k i j))]
      exact Finset.sum_congr rfl (fun i _ ↦ integral_finsetSum _ (fun j _ ↦ hi k i j))
    simp_rw [he]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun i _ ↦ Finset.sum_comm)
  rw [heG]
  calc
    _ ≤ ∑ i : Fin 3, ∑ j : Fin 3, (8 * Real.pi * R) ^ 2 *
        ∫ x : T3, quarticTensorEntry (fullVorticity u x) i j ^ 2 :=
      Finset.sum_le_sum (fun i _ ↦ Finset.sum_le_sum (fun j _ ↦ hbound i j))
    _ = _ := by simp_rw [← Finset.mul_sum]; rw [heE]

theorem weightedProjectionEnergy_le_meanEnergy (P : Finset Wavevector) (u : FourierVelocity)
    (hs : ∀ q, q ∉ P → u q = 0) (R : ℝ) (hP : ∀ q ∈ P, ‖frequencyVec q‖ ≤ R)
    (δ : ℝ) (hδ : 0 < δ) :
    weightedProjectionEnergy δ u ≤ (8 * Real.pi * R) ^ 2 * meanEnergy u := by
  have hu := summable_fourierMoment P u hs 3
  have hK := weightedProjectionEnergy_le δ hδ u hu
  have hT := tensorGradientEnergy_le P u hs R hP
  rw [tensorGradientEnergy_eq u hu] at hT
  have hR := radialDissipation_nonneg u
  linarith only [hK, hT, hR]

/-- The lower bound pays explicitly for the radius. It does not control
the spectral defect at this choice of `kappa`, nor a time-varying cutoff. -/
theorem correctedEnergy_ge (P : Finset Wavevector) (u : FourierVelocity)
    (hs : ∀ q, q ∉ P → u q = 0) (R : ℝ) (hP : ∀ q ∈ P, ‖frequencyVec q‖ ≤ R)
    (δ : ℝ) (hδ : 0 < δ) (κ : ℝ) (hκ : 0 < κ)
    (hscale : 48 * (8 * Real.pi * R) ^ 2 ≤ κ) :
    meanEnergy u / 16 ≤ meanEnergy u / 8 - 3 / κ * weightedProjectionEnergy δ u := by
  have hK := weightedProjectionEnergy_le_meanEnergy P u hs R hP δ hδ
  have hE := meanEnergy_nonneg u
  have hp := mul_le_mul_of_nonneg_right hscale hE
  have h1 := mul_le_mul_of_nonneg_left hK (show 0 ≤ (48 : ℝ) by positivity)
  apply (le_of_mul_le_mul_right (a := κ) ?_ hκ)
  field_simp
  nlinarith only [hp, h1]

def normalization (R : ℝ) : ℝ := 48 * (8 * Real.pi * R) ^ 2 + 1

theorem normalization_pos (R : ℝ) : 0 < normalization R := by unfold normalization; positivity

/-- The regularization is tied to the same parameter as in the existing
signed eighth-moment payment. -/
def correctedEnergy (ν R : ℝ) (u : FourierVelocity) : ℝ :=
  meanEnergy u / 8 - 3 / normalization R *
    weightedProjectionEnergy (ν ^ 2 * normalization R ^ 2 / 3) u

theorem correctedEnergy_bounds (P : Finset Wavevector) (u : FourierVelocity)
    (hs : ∀ q, q ∉ P → u q = 0) (R : ℝ) (hP : ∀ q ∈ P, ‖frequencyVec q‖ ≤ R)
    (ν : ℝ) (hν : 0 < ν) :
    meanEnergy u / 16 ≤ correctedEnergy ν R u ∧ correctedEnergy ν R u ≤ meanEnergy u / 8 := by
  have hκ := normalization_pos R
  have hδ : 0 < ν ^ 2 * normalization R ^ 2 / 3 := by positivity
  constructor
  · exact correctedEnergy_ge P u hs R hP _ hδ _ hκ (by unfold normalization; linarith)
  · have hK : 0 ≤ weightedProjectionEnergy (ν ^ 2 * normalization R ^ 2 / 3) u :=
      integral_nonneg (weightedProjectionDensity_nonneg _ hδ.le u)
    exact sub_le_self _ (mul_nonneg (by positivity) hK)

/-- Every finitely supported filter of an arbitrary field has the stated
size bounds. No closed unforced equation for that filtered field is assumed. -/
theorem correctedEnergy_filtered_bounds (P : Finset Wavevector) (u : FourierVelocity)
    (χ : Wavevector → ℂ) (hχ : ∀ q, q ∉ P → χ q = 0)
    (R : ℝ) (hP : ∀ q ∈ P, ‖frequencyVec q‖ ≤ R) (ν : ℝ) (hν : 0 < ν) :
    meanEnergy (PancakeFilteredStrainDynamics.filteredVelocity χ u) / 16 ≤
      correctedEnergy ν R (PancakeFilteredStrainDynamics.filteredVelocity χ u) ∧
    correctedEnergy ν R (PancakeFilteredStrainDynamics.filteredVelocity χ u) ≤
      meanEnergy (PancakeFilteredStrainDynamics.filteredVelocity χ u) / 8 := by
  apply correctedEnergy_bounds P _ _ R hP ν hν
  intro q hq
  simp [PancakeFilteredStrainDynamics.filteredVelocity, hχ q hq]

end Mettapedia.FluidDynamics.NavierStokes.FiniteBandProjectionEnergy
