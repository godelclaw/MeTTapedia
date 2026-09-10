import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalVorticityTime
import Mettapedia.Analysis.LocallyLipschitz

/-!
# Constant extensions of actual local fields

Clamping time to a compact interior interval extends the actual fields
without extending the solution of the PDE. The extended full vorticity
and filtered strain have locally Lipschitz real space-time lifts. This
supplies the regularity needed by the weak material chain rule.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.LocalSpaceTimeExtension

open scoped Topology NNReal Matrix.Norms.Elementwise
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeFrequencyProjectorCommutator
open PancakeInfiniteFourierDerivative PancakeInfiniteSpatialCurl PancakeCurlOutputTail
open PancakeGalerkinKineticEnergy PancakeInfiniteVelocityEnvelope PancakeHigherDerivativeMoments
open PancakeLocalInfiniteVelocity PancakeFourierMaterialPaths PancakeDyadicDirectionEvolution
open PancakeFilteredStrainDynamics PancakeLocallyLipschitzEnergy PancakeSpacetimeSpectralDifferentiability
open PancakeInfiniteVelocityLipschitz PancakeMeasurableMaterialRate
open LocalVorticityDiffusion LocalLowDiffusionBudget LocalAlignmentTransport LocalAlignmentContinuity
open LocalVorticityTime
open PancakeFourierPressureStrain PancakePeriodicVorticityEquation

local notation "T3" => UnitAddTorus (Fin 3)
local notation "X3" => Fin 3 → ℝ
local notation "R3" => EuclideanSpace ℝ (Fin 3)
local notation "ST" => ℝ × X3

variable {nu T B : ℝ} {u₀ : FourierVelocity}

/-- This is a constant extension of data, not a global velocity solution. -/
def coefficients (s : LocalInfiniteVelocitySolution nu u₀ T B)
    (a b : ℝ) (hab : a ≤ b) (t : ℝ) : FourierVelocity :=
  s.coefficients (Set.projIcc a b hab t)

theorem coefficients_eq (s : LocalInfiniteVelocitySolution nu u₀ T B)
    (a b : ℝ) (hab : a ≤ b) (t : ℝ) (ht : t ∈ Set.Icc a b) :
    coefficients s a b hab t = s.coefficients t := by
  simp only [coefficients, Set.projIcc_of_mem hab ht]

variable (s : LocalInfiniteVelocitySolution nu u₀ T B)
  (a b : ℝ) (hab : a ≤ b) (hI : Set.Icc a b ⊆ Set.Ioo (0 : ℝ) T)
  (g : Wavevector → ℝ) (hg : ∀ q, 0 ≤ g q) (hSum : Summable g)
  (hu : ∀ τ ∈ Set.Icc (0 : ℝ) T, ∀ q, fourierMoment 3 (s.coefficients τ) q ≤ g q)

include hI hu in
theorem moment_bound (t : ℝ) (q : Wavevector) : fourierMoment 3 (coefficients s a b hab t) q ≤ g q :=
  hu _ (Set.Ioo_subset_Icc_self (hI (Set.projIcc a b hab t).2)) q

include hI hSum hu in
theorem summable_moment (m : ℕ) (hm : m ≤ 3) (t : ℝ) :
    Summable (fourierMoment m (coefficients s a b hab t)) :=
  summable_fourierMoment_of_le _ hm
    (hSum.of_nonneg_of_le (fourierMoment_nonneg _ _) (moment_bound s a b hab hI g hu t))

include hI hg hSum hu in
theorem exists_lipschitzWith_fullCurl_lift : ∃ K,
    LipschitzWith K (fun z : ST ↦ fullFourierField id
      (fourierCurl (coefficients s a b hab z.1)) (torusPoint z.2)) := by
  let Kt := Real.toNNReal (∑' q, (2 * Real.pi) * velocityEnvelope nu g q)
  let Kx := Real.toNNReal (3 * (2 * Real.pi) * ∑' q, (2 * Real.pi) * g q)
  have ht : LipschitzWith Kt (fun t ↦ fullFourierField id (fourierCurl (coefficients s a b hab t))) := by
    simpa only [mul_one, Kt, coefficients, Set.restrict, Function.comp_def] using
      (lipschitzOnWith_fullCurlField s g hg hSum hu hI).to_restrict.comp (LipschitzWith.projIcc hab)
  have htime (r : X3) : LipschitzWith Kt (fun t ↦ fullFourierField id
      (fourierCurl (coefficients s a b hab t)) (torusPoint r)) := by
    apply LipschitzWith.of_dist_le_mul
    intro t τ
    exact (ContinuousMap.dist_apply_le_dist (torusPoint r)).trans (ht.dist_le_mul t τ)
  have hspace (t : ℝ) : LipschitzWith Kx (fun r : X3 ↦ fullFourierField id
      (fourierCurl (coefficients s a b hab t)) (torusPoint r)) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    rw [dist_eq_norm, dist_eq_norm]
    have hb (q : Wavevector) : fourierMoment 1 (fourierCurl (coefficients s a b hab t)) q ≤
        (2 * Real.pi) * g q :=
      (fourierMoment_curl_le 1 _ q).trans (mul_le_mul_of_nonneg_left
        ((fourierMoment_mono _ (by omega : 2 ≤ 3) q).trans (moment_bound s a b hab hI g hu t q))
        (by positivity))
    have h := norm_fullFourierField_lift_sub_le _ (fun q ↦ (2 * Real.pi) * g q)
      (fun q ↦ mul_nonneg (by positivity) (hg q)) (hSum.mul_left _) hb x y
    exact h.trans (mul_le_mul_of_nonneg_right (Real.le_coe_toNNReal _) (norm_nonneg _))
  exact ⟨Kt + Kx, LipschitzWith.uncurry htime hspace⟩

include hI hg hSum hu in
theorem locallyLipschitz_fullVorticity :
    LocallyLipschitz (fun z : ST ↦ fullVorticity (coefficients s a b hab z.1) (torusPoint z.2)) := by
  obtain ⟨K, hK⟩ := exists_lipschitzWith_fullCurl_lift s a b hab hI g hg hSum hu
  have he (t : ℝ) : spatialCurl (fullFourierField id (coefficients s a b hab t)) =
      fullFourierField id (fourierCurl (coefficients s a b hab t)) :=
    spatialCurl_velocity _ (summable_fourierMoment_of_le _ (by omega : 1 ≤ 3)
      (hSum.of_nonneg_of_le (fourierMoment_nonneg _ _) (moment_bound s a b hab hI g hu t)))
  simp only [fullVorticity, he]
  exact complexRealPartEuclideanCLM.lipschitz.locallyLipschitz.comp hK.locallyLipschitz

include hI in
theorem locallyLipschitz_coefficients (hB : 0 ≤ B) (q : Wavevector) (i : Fin 3) :
    LocallyLipschitz (fun t ↦ coefficients s a b hab t q i) := by
  have hc : ContDiffOn ℝ 1 (fun t ↦ s.coefficients t q i) (Set.Icc a b) := by
    have h := LocalFilteredSpectralDefect.contDiffOn_coefficients s hB (a := a) (b := b)
      (by simpa only [Set.uIcc_of_le hab] using hI) q i
    simpa only [Set.uIcc_of_le hab] using h
  obtain ⟨K, hK⟩ := hc.exists_lipschitzOnWith (by norm_num) (convex_Icc a b) isCompact_Icc
  exact (hK.to_restrict.comp (LipschitzWith.projIcc hab)).locallyLipschitz

include hI in
theorem locallyLipschitz_strain (hB : 0 ≤ B) (chi : Wavevector → ℂ) (modes : Finset Wavevector) :
    LocallyLipschitz (fun z : ST ↦
      (spatialStrain modes (filteredVelocity chi (coefficients s a b hab z.1)) (torusPoint z.2)).1) := by
  apply realMatrixOperatorCLM.lipschitz.locallyLipschitz.comp
  apply LocallyLipschitz.pi
  intro i
  apply LocallyLipschitz.pi
  intro j
  simp only [matrixReconstruction_apply]
  apply LocallyLipschitz.finsetSum
  intro q _
  have hi : LocallyLipschitz (fun z : ST ↦ coefficients s a b hab z.1 q i) :=
    (locallyLipschitz_coefficients s a b hab hI hB q i).comp
    LipschitzWith.prod_fst.locallyLipschitz
  have hj : LocallyLipschitz (fun z : ST ↦ coefficients s a b hab z.1 q j) :=
    (locallyLipschitz_coefficients s a b hab hI hB q j).comp
    LipschitzWith.prod_fst.locallyLipschitz
  have hp : ContDiff ℝ 1 (fun c : ℂ × ℂ ↦ (1 / 2 : ℂ) *
      (unitTorusDerivativePhase * (q j : ℂ) * (chi q * c.1) +
        unitTorusDerivativePhase * (q i : ℂ) * (chi q * c.2))) := by fun_prop
  have hcoef : LocallyLipschitz (fun z : ST ↦
      strainCoeff (filteredVelocity chi (coefficients s a b hab z.1)) q i j) := by
    simpa only [Function.comp_def, strainCoeff, gradientCoeff, filteredVelocity,
      Matrix.smul_apply, Matrix.add_apply, Matrix.transpose_apply, Pi.smul_apply, smul_eq_mul]
      using hp.locallyLipschitz.comp (hi.prodMk hj)
  exact (contDiff_real_character q).locallyLipschitz.mul_algebra hcoef

include hI hg hSum hu in
theorem locallyLipschitz_alignmentEnergy (hB : 0 ≤ B) (chi : Wavevector → ℂ)
    (modes : Finset Wavevector) (delta : ℝ) :
    LocallyLipschitz (fun z : ST ↦ alignmentEnergy chi modes
      (coefficients s a b hab z.1) delta (torusPoint z.2)) :=
  locallyLipschitz_regularizedEnergy_of_locallyLipschitz
    (fun z : ST ↦ spatialStrain modes (filteredVelocity chi (coefficients s a b hab z.1)) (torusPoint z.2))
    (fun z : ST ↦ fullVorticity (coefficients s a b hab z.1) (torusPoint z.2)) delta
    (locallyLipschitz_strain s a b hab hI hB chi modes)
    (locallyLipschitz_fullVorticity s a b hab hI g hg hSum hu)

include hI hSum hu in
theorem continuous_alignmentEnergy (chi : Wavevector → ℂ) (modes : Finset Wavevector) (delta : ℝ) :
    Continuous (fun z : ℝ × T3 ↦ alignmentEnergy chi modes (coefficients s a b hab z.1) delta z.2) := by
  have hu2 (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) T) (q : Wavevector) :
      fourierMoment 2 (s.coefficients t) q ≤ g q :=
    (fourierMoment_mono _ (by omega : 2 ≤ 3) q).trans (hu t ht q)
  let time : ℝ → Set.Icc (0 : ℝ) T := fun t ↦
    ⟨Set.projIcc a b hab t, Set.Ioo_subset_Icc_self (hI (Set.projIcc a b hab t).2)⟩
  have hp : Continuous (fun t : ℝ ↦ (Set.projIcc a b hab t : ℝ)) :=
    continuous_subtype_val.comp (LipschitzWith.projIcc hab).continuous
  have hc : Continuous time := hp.subtype_mk _
  exact (continuous_alignmentEnergy_spaceTime s g hSum hu2 chi modes delta).comp
    (f := fun z : ℝ × T3 ↦ (time z.1, z.2))
    ((hc.comp continuous_fst).prodMk continuous_snd)

end Mettapedia.FluidDynamics.NavierStokes.LocalSpaceTimeExtension
