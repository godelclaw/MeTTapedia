import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.InfiniteFourierParseval
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PeriodicProjectedTensorJet

/-!
# Signed Parseval identities for the actual projected tensor field

The real spatial inner product is identified with an absolutely convergent
coefficient pairing. The gradient projection then reduces this pairing to
the frequency contractions divided by the squared output frequency.
No absolute values, diagonal approximation, or finite cutoff are inserted.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PeriodicTensorParseval

open scoped RealInnerProductSpace ComplexConjugate
open MeasureTheory Mettapedia.Analysis UnitTorusGradientProjection
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakePeriodicComplexStretch
open PancakePeriodicVorticityEquation
open PancakeInfiniteFourierDerivative PancakeInfiniteSpatialPressure PancakeInfiniteRealCurl
open PancakeBlockReality PancakeDyadicDirectionEvolution PancakeTransverseEnergyFreezing
open LongitudinalVorticityTime InfiniteFourierParseval PeriodicGradientFluxSymbol
open PeriodicProjectedTensorJet

local notation "T3" => UnitAddTorus (Fin 3)
local notation "R3" => EuclideanSpace ℝ (Fin 3)
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

theorem hasSum_scalar_hermitian (a b : Wavevector → ℂ)
    (ha : Summable (fun q ↦ ‖a q‖)) (hb : Summable (fun q ↦ ‖b q‖)) :
    HasSum (fun q ↦ conj (a q) * b q)
      (∫ x : T3, conj (fullFourierField id a x) * fullFourierField id b x) := by
  let f := fullFourierField id a
  let g := fullFourierField id b
  have h := UnitAddTorus.hasSum_prod_mFourierCoeff
    (f.toLp 2 volume ℂ) (g.toLp 2 volume ℂ)
  simp only [UnitAddTorus.mFourierCoeff_toLp, f, g,
    mFourierCoeff_scalarFullFourierField a ha, mFourierCoeff_scalarFullFourierField b hb] at h
  convert h using 1
  apply integral_congr_ae
  filter_upwards [f.coeFn_toAEEqFun volume, g.coeFn_toAEEqFun volume] with x hx hy
  change conj (f x) * g x = conj (f.toAEEqFun volume x) * g.toAEEqFun volume x
  rw [hx, hy]

theorem hasSum_realField_inner (a b : FourierVelocity)
    (ha : Summable (fun q ↦ ‖a q‖)) (hb : Summable (fun q ↦ ‖b q‖))
    (hra : ∀ q, a (-q) = coefficientConjugate (a q)) :
    HasSum (fun q ↦ (coefficientHermitian (a q) (b q)).re)
      (∫ x : T3, ⟪realField a x, realField b x⟫) := by
  have hs (i : Fin 3) : HasSum (fun q ↦ (conj (a q i) * b q i).re)
      (∫ x : T3, (fullFourierField id a x i).re * (fullFourierField id b x i).re) := by
    have ha' := ha.of_nonneg_of_le (fun _ ↦ norm_nonneg _)
      (fun q ↦ norm_le_pi_norm (a q) i)
    have hb' := hb.of_nonneg_of_le (fun _ ↦ norm_nonneg _)
      (fun q ↦ norm_le_pi_norm (b q) i)
    have h := Complex.reCLM.hasSum (hasSum_scalar_hermitian _ _ ha' hb')
    have hi : Integrable (fun x : T3 ↦
        conj (fullFourierField id (fun q ↦ a q i) x) *
          fullFourierField id (fun q ↦ b q i) x) :=
      (by fun_prop : Continuous (fun x : T3 ↦
        conj (fullFourierField id (fun q ↦ a q i) x) *
          fullFourierField id (fun q ↦ b q i) x)).integrable_of_hasCompactSupport
            (HasCompactSupport.of_compactSpace _)
    rw [← Complex.reCLM.integral_comp_comm hi] at h
    convert! h using 1
    apply integral_congr_ae
    filter_upwards [] with x
    rw [← fullFourierField_component_eq a ha i, ← fullFourierField_component_eq b hb i]
    change (fullFourierField id a x i).re * (fullFourierField id b x i).re =
      (conj (fullFourierField id a x i) * fullFourierField id b x i).re
    simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im,
      fullFourierField_im_zero a ha hra, neg_zero, zero_mul, sub_zero]
  have hi (i : Fin 3) : Integrable (fun x : T3 ↦
      (fullFourierField id a x i).re * (fullFourierField id b x i).re) :=
    (by fun_prop : Continuous (fun x : T3 ↦
      (fullFourierField id a x i).re * (fullFourierField id b x i).re)).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
  have he (x : T3) : ⟪realField a x, realField b x⟫ =
      ∑ i : Fin 3, (fullFourierField id a x i).re * (fullFourierField id b x i).re := by
    change (∑ i : Fin 3, (fullFourierField id b x i).re * (fullFourierField id a x i).re) = _
    simp only [mul_comm]
  have hi01 : Integrable (fun x : T3 ↦
      (fullFourierField id a x 0).re * (fullFourierField id b x 0).re +
        (fullFourierField id a x 1).re * (fullFourierField id b x 1).re) := (hi 0).add (hi 1)
  simp only [he, coefficientHermitian, Fin.sum_univ_three, Complex.add_re]
  rw [integral_add hi01 (hi 2), integral_add (hi 0) (hi 1)]
  exact ((hs 0).add (hs 1)).add (hs 2)

theorem hasSum_tensor_inner (J K : Fin 3 → FourierVelocity)
    (hJ : ∀ j, Summable (fun q ↦ ‖J j q‖))
    (hK : ∀ j, Summable (fun q ↦ ‖K j q‖))
    (hr : ∀ j q, J j (-q) = coefficientConjugate (J j q)) :
    HasSum (fun q ↦ ∑ j, (coefficientHermitian (J j q) (K j q)).re)
      ⟪toTensorL2 (fun j ↦ realField (J j)), toTensorL2 (fun j ↦ realField (K j))⟫ := by
  have hs (j : Fin 3) := hasSum_realField_inner (J j) (K j) (hJ j) (hK j) (hr j)
  have hi (j : Fin 3) : Integrable (fun x : T3 ↦ ⟪realField (J j) x, realField (K j) x⟫) :=
    ((realField (J j)).continuous.inner (realField (K j)).continuous).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  rw [inner_toTensorL2]
  have hi01 : Integrable (fun x : T3 ↦
      ⟪realField (J 0) x, realField (K 0) x⟫ +
        ⟪realField (J 1) x, realField (K 1) x⟫) := (hi 0).add (hi 1)
  simp only [Fin.sum_univ_three]
  rw [integral_add hi01 (hi 2), integral_add (hi 0) (hi 1)]
  exact ((hs 0).add (hs 1)).add (hs 2)

theorem projectedCoeff_reality (n : Wavevector) (J : Fin 3 → VelocityCoefficient) (j : Fin 3) :
    projectedCoeff (-n) (fun l ↦ coefficientConjugate (J l)) j =
      coefficientConjugate (projectedCoeff n J j) := by
  ext i
  simp [projectedCoeff, contraction, coefficientConjugate, modeSquare,
    Fin.sum_univ_three, map_div₀, map_mul]
  ring

theorem hasSum_projected_inner (J K : Fin 3 → FourierVelocity)
    (hJ : ∀ j, Summable (fun q ↦ ‖J j q‖))
    (hK : ∀ j, Summable (fun q ↦ ‖K j q‖))
    (hr : ∀ j q, J j (-q) = coefficientConjugate (J j q)) :
    HasSum (fun q ↦ ∑ j, (coefficientHermitian
      (projectedCoeff q (fun l ↦ J l q) j) (K j q)).re)
      ⟪gradientProjection (toTensorL2 (fun j ↦ realField (J j))),
        toTensorL2 (fun j ↦ realField (K j))⟫ := by
  have hproj := gradientProjection_eq_field id J hJ
  change gradientProjection (toTensorL2 (fun j ↦ realField (J j))) =
    toTensorL2 (fun j ↦ realField (projectedFamily id J j)) at hproj
  rw [hproj]
  apply hasSum_tensor_inner _ K (summable_norm_projectedFamily id J hJ) hK
  intro j q
  simpa only [projectedFamily, id_eq, hr] using
    projectedCoeff_reality q (fun l ↦ J l q) j

theorem sum_hermitian_projectedCoeff (n : Wavevector) (J K : Fin 3 → VelocityCoefficient) :
    (∑ j, coefficientHermitian (projectedCoeff n J j) (K j)) =
      coefficientHermitian (contraction n J) (contraction n K) / modeSquare n := by
  simp [coefficientHermitian, projectedCoeff, contraction, modeSquare,
    Fin.sum_univ_three, map_div₀, map_mul]
  ring

theorem hasSum_projected_contraction (J K : Fin 3 → FourierVelocity)
    (hJ : ∀ j, Summable (fun q ↦ ‖J j q‖))
    (hK : ∀ j, Summable (fun q ↦ ‖K j q‖))
    (hr : ∀ j q, J j (-q) = coefficientConjugate (J j q)) :
    HasSum (fun q ↦ (coefficientHermitian
      (contraction q (fun j ↦ J j q)) (contraction q (fun j ↦ K j q)) / modeSquare q).re)
      ⟪gradientProjection (toTensorL2 (fun j ↦ realField (J j))),
        toTensorL2 (fun j ↦ realField (K j))⟫ := by
  have h := hasSum_projected_inner J K hJ hK hr
  simpa only [← Complex.re_sum, sum_hermitian_projectedCoeff] using h

theorem inner_projected_eq_tsum_contraction (J K : Fin 3 → FourierVelocity)
    (hJ : ∀ j, Summable (fun q ↦ ‖J j q‖))
    (hK : ∀ j, Summable (fun q ↦ ‖K j q‖))
    (hr : ∀ j q, J j (-q) = coefficientConjugate (J j q)) :
    ⟪gradientProjection (toTensorL2 (fun j ↦ realField (J j))),
        toTensorL2 (fun j ↦ realField (K j))⟫ =
      ∑' q, (coefficientHermitian (contraction q (fun j ↦ J j q))
        (contraction q (fun j ↦ K j q)) / modeSquare q).re :=
  (hasSum_projected_contraction J K hJ hK hr).tsum_eq.symm

/-- The physical unit-torus divergence coefficient includes the factor `2πi`. -/
def divergenceCoeff (n : Wavevector) (J : Fin 3 → VelocityCoefficient) : VelocityCoefficient :=
  unitTorusDerivativePhase • contraction n J

theorem divergenceCoeff_eq_sum (n : Wavevector) (J : Fin 3 → FourierVelocity) :
    divergenceCoeff n (fun j ↦ J j n) =
      ∑ j, indexedDerivativeCoeff id j (J j) n := by
  simp only [divergenceCoeff, contraction, Finset.smul_sum, smul_smul,
    indexedDerivativeCoeff, id_eq]

theorem hermitian_divergenceCoeff (n : Wavevector) (J K : Fin 3 → VelocityCoefficient) :
    coefficientHermitian (divergenceCoeff n J) (divergenceCoeff n K) =
      ((2 * Real.pi : ℝ) : ℂ) ^ 2 * coefficientHermitian (contraction n J) (contraction n K) := by
  simp only [divergenceCoeff, coefficientHermitian, Pi.smul_apply, smul_eq_mul,
    map_mul, unitTorusDerivativePhase, map_ofNat, Complex.conj_ofReal, Complex.conj_I,
    Fin.sum_univ_three]
  push_cast
  ring_nf
  simp only [Complex.I_sq]
  ring

theorem normalized_divergence_pair (n : Wavevector) (J K : Fin 3 → VelocityCoefficient) :
    coefficientHermitian (divergenceCoeff n J) (divergenceCoeff n K) /
        (((2 * Real.pi : ℝ) : ℂ) ^ 2 * modeSquare n) =
      coefficientHermitian (contraction n J) (contraction n K) / modeSquare n := by
  rw [hermitian_divergenceCoeff]
  have hc : ((2 * Real.pi : ℝ) : ℂ) ^ 2 ≠ 0 := by
    exact pow_ne_zero _ (Complex.ofReal_ne_zero.mpr (by positivity))
  exact mul_div_mul_left _ _ hc

theorem inner_projected_eq_tsum_divergence (J K : Fin 3 → FourierVelocity)
    (hJ : ∀ j, Summable (fun q ↦ ‖J j q‖))
    (hK : ∀ j, Summable (fun q ↦ ‖K j q‖))
    (hr : ∀ j q, J j (-q) = coefficientConjugate (J j q)) :
    ⟪gradientProjection (toTensorL2 (fun j ↦ realField (J j))),
        toTensorL2 (fun j ↦ realField (K j))⟫ =
      ∑' q, (coefficientHermitian (divergenceCoeff q (fun j ↦ J j q))
        (divergenceCoeff q (fun j ↦ K j q)) /
          (((2 * Real.pi : ℝ) : ℂ) ^ 2 * modeSquare q)).re := by
  simp only [normalized_divergence_pair]
  exact inner_projected_eq_tsum_contraction J K hJ hK hr

end Mettapedia.FluidDynamics.NavierStokes.PeriodicTensorParseval
