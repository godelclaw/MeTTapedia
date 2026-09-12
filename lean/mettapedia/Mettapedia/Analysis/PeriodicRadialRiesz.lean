import Mettapedia.Analysis.RadialRieszTensor
import Mettapedia.Analysis.RadialRieszMoments
import Mettapedia.Analysis.UnitTorusSchwartzLattice
import Mettapedia.Analysis.UnitTorusFourierL1Uniqueness

/-!
# Periodization of the explicitly radial Riesz construction

The periodic entries have the intended regularized Fourier coefficients
and cutoff-independent positive spatial moments. The operator is an
absolutely convergent sum over Euclidean images away from the origin.
Its signed stretching formula retains each image displacement separately;
the resulting periodic operator is not asserted to be radial.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.Analysis.PeriodicRadialRiesz

open MeasureTheory UnitTorusLattice UnitTorusPeriodization UnitTorusSchwartzLattice
open scoped SchwartzMap FourierTransform Topology RealInnerProductSpace

variable {d : ℕ}
local notation "Rd" => EuclideanSpace ℝ (Fin d)
local notation "Td" => UnitAddTorus (Fin d)
local notation "Lat" => LatticeSubmodule (ι := Fin d)
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
local instance : Measure.IsNegInvariant (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsNegInvariant AddCircle.haarAddCircle)

def entry (N : ℕ) (i j : Fin d) (q : Td) : ℂ :=
  periodize (RadialRieszRegularization.kernel N i j) q

theorem measurable_entry (N : ℕ) (i j : Fin d) : Measurable (entry N i j) :=
  measurable_periodize _ (RadialRieszRegularization.kernel N i j).continuous.measurable

theorem integrable_entry (N : ℕ) (i j : Fin d) : Integrable (entry N i j) :=
  integrable_periodize _

theorem mFourierCoeff_entry (N : ℕ) (i j : Fin d) (k : Fin d → ℤ) :
    UnitAddTorus.mFourierCoeff (entry N i j) k =
      ((RadialRieszRegularization.weight N (frequency k) *
        AnnularRieszKernel.rieszEntry i j (frequency k) : ℝ) : ℂ) := by
  change UnitAddTorus.mFourierCoeff (periodize (RadialRieszRegularization.kernel N i j)) k = _
  rw [mFourierCoeff_periodize _ (RadialRieszRegularization.kernel N i j).continuous.measurable
    (RadialRieszRegularization.kernel N i j).integrable, ← SchwartzMap.fourier_coe,
    RadialRieszRegularization.fourier_kernel_apply]

theorem mFourierCoeff_entry_neg (N : ℕ) (i j : Fin d) (k : Fin d → ℤ) :
    UnitAddTorus.mFourierCoeff (entry N i j) (-k) =
      UnitAddTorus.mFourierCoeff (entry N i j) k := by
  have hf : frequency (-k) = -frequency k := by ext i; simp [frequency]
  have hw : RadialRieszRegularization.weight N (-frequency k) =
      RadialRieszRegularization.weight N (frequency k) :=
    RadialRieszRegularization.weight_isometry N (LinearIsometryEquiv.neg ℝ) (frequency k)
  simp only [mFourierCoeff_entry, hf, hw, AnnularRieszKernel.rieszEntry_neg]

theorem mFourierCoeff_re_entry (N : ℕ) (i j : Fin d) (k : Fin d → ℤ) :
    UnitAddTorus.mFourierCoeff (fun q ↦ ((entry N i j q).re : ℂ)) k =
      ((RadialRieszRegularization.weight N (frequency k) *
        AnnularRieszKernel.rieszEntry i j (frequency k) : ℝ) : ℂ) := by
  apply UnitTorusFourierReal.mFourierCoeff_realPart_of_coefficients _ (integrable_entry N i j)
  · exact mFourierCoeff_entry N i j k
  · rw [mFourierCoeff_entry_neg, mFourierCoeff_entry]

theorem entry_neg_ae (N : ℕ) (i j : Fin d) :
    (fun q ↦ entry N i j (-q)) =ᵐ[volume] entry N i j := by
  apply UnitTorusFourierL1Uniqueness.ae_eq_of_mFourierCoeff_eq
    (integrable_entry N i j).comp_neg (integrable_entry N i j)
  intro k
  rw [UnitTorusFourierReal.mFourierCoeff_comp_neg, mFourierCoeff_entry_neg]

theorem tendsto_mFourierCoeff_entry (i j : Fin d) (k : Fin d → ℤ) :
    Filter.Tendsto (fun N : ℕ ↦ UnitAddTorus.mFourierCoeff (entry N i j) k)
      Filter.atTop (𝓝 (AnnularRieszKernel.rieszEntry i j (frequency k) : ℂ)) := by
  by_cases hk : k = 0
  · subst k
    simp [mFourierCoeff_entry, frequency, AnnularRieszKernel.rieszEntry]
  · have h := (RadialRieszRegularization.tendsto_weight (frequency k)
        (PeriodicRieszKernel.one_le_norm_frequency k hk)).mul_const
        (AnnularRieszKernel.rieszEntry i j (frequency k))
    simpa only [mFourierCoeff_entry, one_mul, Function.comp_def] using
      Complex.continuous_ofReal.continuousAt.tendsto.comp h

theorem integrable_moment_entry (N m : ℕ) (i j : Fin d) :
    Integrable (fun q : Td ↦ ‖q‖ ^ m * ‖entry N i j q‖) :=
  integrable_moment_periodize _ m

theorem moment_entry_le (N m : ℕ) (hm : 0 < m) (i j : Fin d) :
    (∫ q : Td, ‖q‖ ^ m * ‖entry N i j q‖) ≤
      (1 - (1 / 2 : ℝ) ^ m)⁻¹ * RadialRieszRegularization.baseMoment m i j :=
  (integral_moment_periodize_le _ m).trans
    (RadialRieszRegularization.moment_kernel_le N m hm i j)

def tensor (N : ℕ) (q : Td) : Rd →L[ℝ] Rd :=
  ∑ i, ∑ j, (entry N i j q).re • PeriodicRieszOperator.basisOperator i j

theorem tensor_apply_component (N : ℕ) (q : Td) (a : Rd) (i : Fin d) :
    (tensor N q a) i = ∑ j : Fin d, (entry N i j q).re * a j := by
  simp only [tensor, sum_apply, smul_apply, PeriodicRieszOperator.basisOperator_apply, smul_smul]
  simp [Pi.single_apply]

theorem tensor_neg_ae (N : ℕ) : (fun q : Td ↦ tensor N (-q)) =ᵐ[volume] tensor N := by
  have h : ∀ᵐ q : Td, ∀ i j : Fin d, entry N i j (-q) = entry N i j q := by
    simp only [ae_all_iff]
    exact fun i j ↦ entry_neg_ae N i j
  filter_upwards [h] with q hq
  simp only [tensor, hq]

theorem hasSum_tensor_images (N : ℕ) {q : Td} (hq : q ≠ 0) :
    HasSum (fun z : Lat ↦ RadialRieszRegularization.tensor N (displacement q z)) (tensor N q) := by
  have hs (i j : Fin d) : HasSum
      (fun z : Lat ↦ (RadialRieszRegularization.kernel N i j (displacement q z)).re •
        PeriodicRieszOperator.basisOperator i j)
      ((entry N i j q).re • PeriodicRieszOperator.basisOperator i j) := by
    have h := (summable_norm_images (RadialRieszRegularization.kernel N i j) hq).of_norm.hasSum
    have hr := Complex.reCLM.hasSum h
    exact hr.smul_const _
  exact hasSum_sum (s := Finset.univ) (fun i _ ↦
    hasSum_sum (s := Finset.univ) (fun j _ ↦ hs i j))

theorem tensor_eq_tsum_images (N : ℕ) {q : Td} (hq : q ≠ 0) :
    tensor N q = ∑' z : Lat, RadialRieszRegularization.tensor N (displacement q z) :=
  (hasSum_tensor_images N hq).tsum_eq.symm

theorem hasSum_pairedStretch_images (N n : ℕ)
    (e : EuclideanSpace ℝ (Fin 3)) (he : ‖e‖ = 1)
    {q : UnitAddTorus (Fin 3)} (hq : q ≠ 0) (a b : EuclideanSpace ℝ (Fin 3)) :
    HasSum (fun z : LatticeSubmodule (ι := Fin 3) ↦
      RadialRieszRegularization.radialCoefficient N e (displacement q z) *
        EuclideanCrossProduct.tripleProduct a b (displacement q z) *
          ⟪displacement q z, RadialPower.radialPower n a - RadialPower.radialPower n b⟫)
      (SignedCrossKernel.pairedStretch n (tensor N q) a b) := by
  have h := (innerSL ℝ (EuclideanCrossProduct.cross a b)).hasSum
    ((ContinuousLinearMap.apply ℝ (EuclideanSpace ℝ (Fin 3))
      (RadialPower.radialPower n a - RadialPower.radialPower n b)).hasSum
        (hasSum_tensor_images N hq))
  apply h.congr_fun
  intro z
  exact (RadialRieszRegularization.pairedStretch_tensor N n e he (displacement_ne_zero hq z) a b).symm

theorem norm_tensor_le (N : ℕ) (q : Td) :
    ‖tensor N q‖ ≤ ∑ i : Fin d, ∑ j : Fin d, ‖entry N i j q‖ := by
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum (fun i _ ↦ ?_))
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum (fun j _ ↦ ?_))
  simp only [norm_smul, PeriodicRieszOperator.norm_basisOperator, mul_one, Real.norm_eq_abs]
  exact Complex.abs_re_le_norm _

theorem measurable_tensor (N : ℕ) : Measurable (tensor (d := d) N) := by
  unfold tensor
  exact Finset.measurable_sum _ (fun i _ ↦ Finset.measurable_sum _ (fun j _ ↦
    (Complex.continuous_re.measurable.comp (measurable_entry N i j)).smul_const _))

theorem integrable_moment_tensor (N m : ℕ) :
    Integrable (fun q : Td ↦ ‖q‖ ^ m * ‖tensor N q‖) := by
  have hi := integrable_finsetSum Finset.univ (fun i (_ : i ∈ (Finset.univ : Finset (Fin d))) ↦
    integrable_finsetSum Finset.univ (fun j _ ↦ integrable_moment_entry N m i j))
  apply hi.mono' (((continuous_norm.pow m).measurable.mul (measurable_tensor N).norm).aestronglyMeasurable)
  filter_upwards [] with q
  rw [Real.norm_of_nonneg (by positivity)]
  simpa only [Finset.mul_sum] using mul_le_mul_of_nonneg_left (norm_tensor_le N q) (by positivity : 0 ≤ ‖q‖ ^ m)

theorem moment_tensor_le (N m : ℕ) (hm : 0 < m) :
    (∫ q : Td, ‖q‖ ^ m * ‖tensor N q‖) ≤
      (1 - (1 / 2 : ℝ) ^ m)⁻¹ *
        ∑ i : Fin d, ∑ j : Fin d, RadialRieszRegularization.baseMoment m i j := by
  calc
    _ ≤ ∫ q : Td, ∑ i : Fin d, ∑ j : Fin d, ‖q‖ ^ m * ‖entry N i j q‖ := by
      apply integral_mono (integrable_moment_tensor N m)
        (integrable_finsetSum _ (fun i _ ↦ integrable_finsetSum _ (fun j _ ↦ integrable_moment_entry N m i j)))
      intro q
      simpa only [Finset.mul_sum] using mul_le_mul_of_nonneg_left (norm_tensor_le N q) (by positivity : 0 ≤ ‖q‖ ^ m)
    _ = ∑ i : Fin d, ∑ j : Fin d, ∫ q : Td, ‖q‖ ^ m * ‖entry N i j q‖ := by
      rw [integral_finsetSum _ (fun i _ ↦ integrable_finsetSum _ (fun j _ ↦ integrable_moment_entry N m i j))]
      apply Finset.sum_congr rfl
      intro i _
      exact integral_finsetSum _ (fun j _ ↦ integrable_moment_entry N m i j)
    _ ≤ ∑ i : Fin d, ∑ j : Fin d, (1 - (1 / 2 : ℝ) ^ m)⁻¹ *
        RadialRieszRegularization.baseMoment m i j :=
      Finset.sum_le_sum (fun i _ ↦ Finset.sum_le_sum (fun j _ ↦ moment_entry_le N m hm i j))
    _ = _ := by simp only [Finset.mul_sum]

end Mettapedia.Analysis.PeriodicRadialRiesz
