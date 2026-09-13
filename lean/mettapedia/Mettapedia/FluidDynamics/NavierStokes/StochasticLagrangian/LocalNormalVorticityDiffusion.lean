import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalVorticityEighthSpatialBalance
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalPairedDiffusion
import Mettapedia.Analysis.NormalVorticityEnergy
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalNormalVorticity

/-!
# Signed dissipation of fixed normal vorticity

A common spatial translation of a pair keeps its image separation fixed.
For any fixed linear projection, periodic integration by parts turns the
projected vorticity Laplacian into minus the projected gradient energy.
In particular, the normalized normal component has genuine dissipation.
Relative-separation transport is not removed by this identity.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.LocalNormalVorticity

open MeasureTheory PeriodicFourierTriad PancakeCurlOutputTail PancakeHigherDerivativeMoments
open PancakeFourierMaterialPaths PancakeHaarTransportRate PancakeFourierTranslationCurve
open LocalLowDiffusionBudget LocalSpatialVorticityJets LocalJointDiffusionBudget
open PancakePeriodicWeakDerivative Mettapedia.Analysis
open LocalAlignmentForcing LocalMeanAlignmentBalance
open PancakeLocalInfiniteVelocity PancakeLocalMaterialTrajectories LocalRadialImageEvolution

local notation "T3" => UnitAddTorus (Fin 3)
local notation "R3" => EuclideanSpace ℝ (Fin 3)
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

theorem integral_projection_mul_second_eq (P : R3 →L[ℝ] ℝ) (u : FourierVelocity)
    (hu : Summable (fourierMoment 3 u)) (j : Fin 3) :
    (∫ x : T3, P (fullVorticity u x) * P (fullCurlSecond u j x)) =
      -(∫ x : T3, P (fullCurlGradient u j x) ^ 2) := by
  let f : T3 → ℝ := fun x ↦ P (fullCurlGradient u j x)
  let g : T3 → ℝ := fun x ↦ P (fullVorticity u x)
  have hf := P.continuous.comp (LocalSquaredGapGradient.continuous_fullCurlGradient u j)
  have hg := P.continuous.comp
    (continuous_fullVorticity u (summable_fourierMoment_of_le u (by omega : 1 ≤ 3) hu))
  have hfL := P.lipschitz.locallyLipschitz.comp
    (LocalVorticityEighthMoment.locallyLipschitz_fullCurlGradient_lift u hu j)
  have hgL := P.lipschitz.locallyLipschitz.comp
    (LocalAlignmentTransport.locallyLipschitz_fullVorticity u
      (summable_fourierMoment_of_le u (by omega : 2 ≤ 3) hu))
  have hdf (x : T3) : shiftRate f (coordinateShift j) x = P (fullCurlSecond u j x) := by
    have hd := P.hasFDerivAt.comp_hasDerivAt 0 (hasDerivAt_fullCurlGradient_shift u hu j x 0)
    simpa only [shiftRate, f, Function.comp_def, coordinateShift_zero, add_zero] using hd.deriv
  have hdg (x : T3) : shiftRate g (coordinateShift j) x = P (fullCurlGradient u j x) := by
    have hd := P.hasFDerivAt.comp_hasDerivAt 0 (hasDerivAt_fullVorticity_shift u hu j x 0)
    simpa only [shiftRate, g, Function.comp_def, coordinateShift_zero, add_zero] using hd.deriv
  have he := integral_coordinateRate_mul f g j hf hg hfL hgL
  simpa only [hdf, hdg, f, g, pow_two, mul_comm] using he

theorem integral_projection_mul_laplacian_eq (P : R3 →L[ℝ] ℝ) (u : FourierVelocity)
    (hu : Summable (fourierMoment 3 u)) :
    (∫ x : T3, P (fullVorticity u x) * P (fullVorticityLaplacian u x)) =
      -(∫ x : T3, ∑ j : Fin 3, P (fullCurlGradient u j x) ^ 2) := by
  have hw := P.continuous.comp
    (continuous_fullVorticity u (summable_fourierMoment_of_le u (by omega : 1 ≤ 3) hu))
  have hs (j : Fin 3) : Integrable (fun x : T3 ↦ P (fullVorticity u x) * P (fullCurlSecond u j x)) :=
    (hw.mul (P.continuous.comp (LocalPairedDiffusion.continuous_fullCurlSecond u j))).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hg (j : Fin 3) : Integrable (fun x : T3 ↦ P (fullCurlGradient u j x) ^ 2) :=
    ((P.continuous.comp (LocalSquaredGapGradient.continuous_fullCurlGradient u j)).pow 2).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have he (x : T3) : P (fullVorticity u x) * P (fullVorticityLaplacian u x) =
      ∑ j : Fin 3, P (fullVorticity u x) * P (fullCurlSecond u j x) := by
    rw [← sum_fullCurlSecond u hu x, map_sum, Finset.mul_sum]
  simp_rw [he]
  rw [integral_finsetSum _ (fun j _ ↦ hs j), integral_finsetSum _ (fun j _ ↦ hg j)]
  simp only [integral_projection_mul_second_eq P u hu, Finset.sum_neg_distrib]

theorem integral_normal_mul_laplacian_eq (h : R3) (u : FourierVelocity)
    (hu : Summable (fourierMoment 3 u)) :
    (∫ x : T3, NormalVorticityEnergy.component (fullVorticity u x) h *
      NormalVorticityEnergy.component (fullVorticityLaplacian u x) h) =
      -(∫ x : T3, ∑ j : Fin 3, NormalVorticityEnergy.component (fullCurlGradient u j x) h ^ 2) := by
  simpa only [NormalVorticityEnergy.component, smul_apply, innerSL_apply_apply,
    smul_eq_mul, div_eq_mul_inv, mul_comm] using
      integral_projection_mul_laplacian_eq (‖h‖⁻¹ • innerSL ℝ h) u hu

theorem integral_normal_mul_laplacian_nonpos (h : R3) (u : FourierVelocity)
    (hu : Summable (fourierMoment 3 u)) :
    (∫ x : T3, NormalVorticityEnergy.component (fullVorticity u x) h *
      NormalVorticityEnergy.component (fullVorticityLaplacian u x) h) ≤ 0 := by
  rw [integral_normal_mul_laplacian_eq h u hu]
  exact neg_nonpos.mpr (integral_nonneg (fun _ ↦ Finset.sum_nonneg (fun _ _ ↦ sq_nonneg _)))

/-- The full square rate at the left endpoint. In a radial image application,
`q` is the periodic endpoint difference and `h` is its chosen image lift.
The relative velocity, including the normalization's length derivative,
is retained. This definition is not a spatial-mean time derivative. -/
def squareMaterialRate (u : FourierVelocity) (nu : ℝ) (q : T3) (h : R3) (x : T3) : ℝ :=
  2 * NormalVorticityEnergy.component (fullVorticity u x) h *
    NormalVorticityEnergy.rate (fullVorticity u x) h
      (fullStrainOperator u x (fullVorticity u x) + nu • fullVorticityLaplacian u x)
      (velocity u x - velocity u (x - q))

theorem hasDerivAt_square_component_path {nu T B : ℝ} {u₀ : FourierVelocity}
    (s : LocalInfiniteVelocitySolution nu u₀ T B)
    (g : Wavevector → ℝ) (hg : ∀ q, 0 ≤ g q) (hSum : Summable g)
    (hu : ∀ τ ∈ Set.Icc (0 : ℝ) T, ∀ q, fourierMoment 3 (s.coefficients τ) q ≤ g q)
    (a b : ℝ) (hab : a ≤ b) (hI : Set.Icc a b ⊆ Set.Ioo (0 : ℝ) T)
    (X Y : ℝ → Fin 3 → ℝ) (t : ℝ) (ht : t ∈ Set.Ioo a b)
    (hX : HasDerivAt X (liftedVelocity s t (X t)) t)
    (hY : HasDerivAt Y (liftedVelocity s t (Y t)) t)
    (z : R3) (hz : imageSeparation z (X t) (Y t) ≠ 0) :
    HasDerivAt (fun τ ↦ component z (s.coefficients τ) (X τ) (Y τ) (torusPoint (X τ)) ^ 2)
      (squareMaterialRate (s.coefficients t) nu (torusPoint (X t) - torusPoint (Y t))
        (imageSeparation z (X t) (Y t)) (torusPoint (X t))) t := by
  have hd := hasDerivAt_component_path s g hg hSum hu a b hab hI X Y X t ht hX hY hX z hz
  rw [squareMaterialRate, sub_sub_cancel,
    rate_eq z (s.coefficients t) nu (X t) (Y t) (torusPoint (X t)) hz]
  convert hd.pow 2 using 1 <;> first | rfl | simp [component]

theorem squareMaterialRate_eq_nonviscous_add (u : FourierVelocity) (nu : ℝ)
    (q : T3) (h : R3) (x : T3) :
    squareMaterialRate u nu q h x = squareMaterialRate u 0 q h x +
      2 * nu * (NormalVorticityEnergy.component (fullVorticity u x) h *
        NormalVorticityEnergy.component (fullVorticityLaplacian u x) h) := by
  simp only [squareMaterialRate, NormalVorticityEnergy.rate, NormalVorticityEnergy.component,
    inner_add_right, real_inner_smul_right, zero_smul, add_zero]
  ring

theorem continuous_squareMaterialRate (u : FourierVelocity) (nu : ℝ)
    (hu : Summable (fourierMoment 3 u)) (q : T3) (h : R3) :
    Continuous (squareMaterialRate u nu q h) := by
  have hu1 := summable_fourierMoment_of_le u (by omega : 1 ≤ 3) hu
  have hw := continuous_fullVorticity u hu1
  have hs := continuous_fullStrainOperator u hu1
  have hl := LocalPairedDiffusion.continuous_fullVorticityLaplacian u hu
  have hv := continuous_velocity u
  have hdiff : Continuous (fun x : T3 ↦ velocity u x - velocity u (x - q)) :=
    hv.sub (hv.comp (continuous_id.sub continuous_const))
  have hc : Continuous (fun x ↦ NormalVorticityEnergy.component (fullVorticity u x) h) :=
    (continuous_const.inner hw).div_const _
  unfold squareMaterialRate NormalVorticityEnergy.rate
  exact (continuous_const.mul hc).mul
    (((hdiff.inner hw).add (continuous_const.inner ((hs.clm_apply hw).add (hl.const_smul nu)))).div_const _ |>.sub
      ((hc.mul (continuous_const.inner hdiff)).div_const _))

/-- Signed normal dissipation survives the common-translation spatial
integral. The nonviscous relative transport still has no assigned sign. -/
theorem integral_squareMaterialRate_add_dissipation_eq (u : FourierVelocity) (nu : ℝ)
    (hu : Summable (fourierMoment 3 u)) (q : T3) (h : R3) :
    (∫ x : T3, squareMaterialRate u nu q h x) +
      2 * nu * (∫ x : T3, ∑ j : Fin 3, NormalVorticityEnergy.component (fullCurlGradient u j x) h ^ 2) =
      ∫ x : T3, squareMaterialRate u 0 q h x := by
  have h0 : Integrable (squareMaterialRate u 0 q h) :=
    (continuous_squareMaterialRate u 0 hu q h).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)
  have hw := continuous_fullVorticity u (summable_fourierMoment_of_le u (by omega : 1 ≤ 3) hu)
  have hl := LocalPairedDiffusion.continuous_fullVorticityLaplacian u hu
  have hc : Continuous (fun x ↦ NormalVorticityEnergy.component (fullVorticity u x) h *
      NormalVorticityEnergy.component (fullVorticityLaplacian u x) h) :=
    ((continuous_const.inner hw).div_const _).mul ((continuous_const.inner hl).div_const _)
  have hi : Integrable (fun x : T3 ↦ NormalVorticityEnergy.component (fullVorticity u x) h *
      NormalVorticityEnergy.component (fullVorticityLaplacian u x) h) :=
    hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  simp_rw [squareMaterialRate_eq_nonviscous_add u nu q h]
  rw [integral_add h0 (hi.const_mul (2 * nu)), integral_const_mul, integral_normal_mul_laplacian_eq h u hu]
  ring

end Mettapedia.FluidDynamics.NavierStokes.LocalNormalVorticity
