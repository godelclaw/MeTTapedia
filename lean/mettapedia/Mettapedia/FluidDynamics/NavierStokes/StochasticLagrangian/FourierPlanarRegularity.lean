import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.FourierSymmetry

/-!
# Global regularity of planar flows, for data of any size

A Fourier field is planar when only modes with `k₂ = 0` are present and the
third velocity component vanishes. Planar data are invariant under the
translations and the reflection in the third coordinate, so by uniqueness the
solution stays planar. For a planar field the vorticity is normal to the plane
and the strain has no third row or column, hence `⟪ω, S ω⟫ = 0` at every
point: there is no vortex stretching. The exact enstrophy identity then keeps
the enstrophy below its initial value, which bounds the order-one energy on
every horizon, so planar data of any size have a unique global solution.

This is the classical two-dimensional theorem. It shows the complete chain at
work for large data and isolates the only three-dimensional obstruction, the
stretching term.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.FourierPlanarRegularity

open scoped BigOperators RealInnerProductSpace Matrix.Norms.Elementwise
open MeasureTheory Set
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeFrequencyProjectorCommutator
open PancakeSobolevWeights PancakeSobolevVelocityRate PancakeHigherSobolevWeights
open PancakeHigherSobolevVelocityRate PancakeCurlOutputTail PancakeLocalInfiniteVelocity
open PancakeBlockReality PancakeGalerkinKineticEnergy PancakePeriodicComplexStretch
open PancakeFourierPressureStrain PancakeFourierMaterialPaths PancakeInfiniteFourierDerivative
open PancakeHigherDerivativeMoments PancakeInfiniteSpatialCurl PancakeDyadicDirectionEvolution
open LocalLowDiffusionBudget LocalAlignmentForcing FullStrainFourierSeries
open FourierTameContinuation FourierVorticitySupContinuation FourierUniqueness
open FourierGlobalSolution FourierSymmetry LocalEnstrophyDiffusion
open FourierEighthMomentControl

local notation "T3" => UnitAddTorus (Fin 3)
local notation "R3" => EuclideanSpace ℝ (Fin 3)

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

/-- A planar Fourier field: only modes with `k₂ = 0`, and no third component. -/
def IsPlanar (u : FourierVelocity) : Prop := (∀ k, k 2 ≠ 0 → u k = 0) ∧ ∀ k, u k 2 = 0

section Invariance

theorem shiftZ_eq_of_planar {u : FourierVelocity} (hu : IsPlanar u) (a : ℝ) : shiftZ a u = u := by
  funext k
  by_cases hk : k 2 = 0
  · simp [shiftZ, zPhase_eq_one_of a hk]
  · simp [shiftZ, hu.1 k hk]

theorem reflectZ_eq_of_planar {u : FourierVelocity} (hu : IsPlanar u) : reflectZ u = u := by
  funext k
  by_cases hk : k 2 = 0
  · have hR : reflectVec k = k := by
      funext i
      fin_cases i <;> simp [hk]
    funext i
    fin_cases i <;> simp [reflectZ, hR, hu.2 k]
  · have hR : reflectVec k 2 ≠ 0 := by simpa using hk
    rw [hu.1 k hk]
    funext i
    fin_cases i <;> simp [reflectZ, hu.1 _ hR]

/-- **Planarity is preserved.** A tame solution of order at least seven with
planar data is planar at every time. -/
theorem isPlanar_of_tame {m : ℕ} (hm : 7 ≤ m) {nu : ℝ} (hnu : 0 < nu) {u₀ : FourierVelocity}
    (hu : IsPlanar u₀) {T : ℝ} (c : TameSolutionOn nu m u₀ T) {t : ℝ} (ht : t ∈ Ico (0 : ℝ) T) :
    IsPlanar (c.coefficients t) := by
  have h1 : ∀ k, k 2 ≠ 0 → c.coefficients t k = 0 := by
    intro k hk
    have h := congrFun (shiftZ_coefficients_eq hm hnu c (1 / (2 * (k 2 : ℝ)))
      (shiftZ_eq_of_planar hu _) ht) k
    simp only [shiftZ, zPhase_half k hk, neg_smul, one_smul] at h
    have h2 : (2 : ℂ) • c.coefficients t k = 0 := by
      rw [two_smul]
      nth_rewrite 1 [← h]
      simp
    exact (smul_eq_zero.mp h2).resolve_left two_ne_zero
  refine ⟨h1, fun k ↦ ?_⟩
  by_cases hk : k 2 = 0
  · have hR : reflectVec k = k := by
      funext i
      fin_cases i <;> simp [hk]
    have h := congrFun (congrFun (reflectZ_coefficients_eq hm hnu c (reflectZ_eq_of_planar hu) ht)
      k) 2
    simp only [reflectZ, hR, reflectCoeff_two_apply] at h
    have h2 : (2 : ℂ) * c.coefficients t k 2 = 0 := by linear_combination -h
    exact (mul_eq_zero.mp h2).resolve_left two_ne_zero
  · rw [h1 k hk]
    rfl

end Invariance

section Stretching

theorem fourierCurl_planar_zero {u : FourierVelocity} (hu : IsPlanar u) (k : Wavevector) :
    fourierCurl u k 0 = 0 ∧ fourierCurl u k 1 = 0 := by
  by_cases hk : k 2 = 0
  · simp [fourierCurl, coefficientCross, wavevectorCoefficient, hk, hu.2 k]
  · simp [fourierCurl, coefficientCross, hu.1 k hk]

theorem strainCoeff_planar_zero {u : FourierVelocity} (hu : IsPlanar u) (q : Wavevector)
    (i : Fin 3) : strainCoeff u q i 2 = 0 := by
  by_cases hq : q 2 = 0
  · simp [strainCoeff, gradientCoeff, hq, hu.2 q]
  · simp [strainCoeff, gradientCoeff, hu.1 q hq]

theorem fullVorticity_planar (u : FourierVelocity) (hu1 : Summable (fourierMoment 1 u))
    (hu : IsPlanar u) (x : T3) (i : Fin 3) (hi : i ≠ 2) : fullVorticity u x i = 0 := by
  have hs := FullVorticityFourierCoefficients.summable_norm_fourierCurl u hu1
  have hc : fullFourierField id (fourierCurl u) x i = 0 := by
    rw [InfiniteFourierParseval.fullFourierField_component_eq _ hs i,
      fullFourierField_apply id _ ((hs.of_nonneg_of_le (fun _ ↦ norm_nonneg _)
        (fun q ↦ norm_le_pi_norm (fourierCurl u q) i)))]
    refine (tsum_congr fun q ↦ ?_).trans tsum_zero
    fin_cases i
    · simp [(fourierCurl_planar_zero hu q).1]
    · simp [(fourierCurl_planar_zero hu q).2]
    · exact absurd rfl hi
  unfold fullVorticity
  rw [spatialCurl_velocity u hu1, complexRealPartEuclideanCLM_apply]
  change (fullFourierField id (fourierCurl u) x i).re = 0
  rw [hc, Complex.zero_re]

/-- **No stretching for planar fields.** -/
theorem stretchingDensity_planar (u : FourierVelocity) (hu1 : Summable (fourierMoment 1 u))
    (hu : IsPlanar u) (x : T3) : stretchingDensity u x = 0 := by
  set w := fullVorticity u x
  have hw0 : w 0 = 0 := fullVorticity_planar u hu1 hu x 0 (by decide)
  have hw1 : w 1 = 0 := fullVorticity_planar u hu1 hu x 1 (by decide)
  have hA : ∀ i, PancakeLocalStrainEquation.spatialStrain (fullFourierField id u) x i 2 = 0 := by
    intro i
    rw [strain_entry_eq u hu1 x i 2, fullFourierField_apply id _
      (summable_norm_strainCoeff_entry u hu1 i 2)]
    exact (tsum_congr fun q ↦ by simp [strainCoeff_planar_zero hu q i]).trans tsum_zero
  have hSw : fullStrainOperator u x w = 0 := by
    ext i
    change realMatrixOperator (PancakeLocalStrainEquation.spatialStrain (fullFourierField id u) x)
      w i = 0
    rw [realMatrixOperator_apply, Fin.sum_univ_three, hw0, hw1, hA i]
    simp
  change ⟪w, fullStrainOperator u x w⟫ = 0
  rw [hSw, inner_zero_right]

end Stretching

section Global

/-- **Enstrophy never grows for planar solutions.** -/
theorem meanEnstrophy_le_of_planar {m : ℕ} (hm : 7 ≤ m) {nu : ℝ} (hnu : 0 < nu)
    {u₀ : FourierVelocity} (hu : IsPlanar u₀) {T : ℝ} (c : TameSolutionOn nu m u₀ T) {τ : ℝ}
    (hτ : τ ∈ Ico (0 : ℝ) T) : meanEnstrophy (c.coefficients τ) ≤ meanEnstrophy u₀ := by
  set S := (τ + T) / 2 with hSdef
  have hτS : τ < S := by linarith [hτ.2]
  have hST : S < T := by linarith [hτ.2]
  have hS0 : 0 < S := lt_of_le_of_lt hτ.1 hτS
  obtain ⟨B, s, hs, g, hg, hSum, hu3⟩ := local_envelope_at hm c hST
  have hid := enstrophy_identity s g hg hSum hu3 hS0 τ ⟨hτ.1, hτS.le⟩
  have hzero : ∀ r ∈ Icc (0 : ℝ) τ, stretching (s.coefficients r) = 0 := by
    intro r hr
    have hrT : r ∈ Ico (0 : ℝ) T := ⟨hr.1, hr.2.trans_lt (hτS.trans hST)⟩
    have hrS : r ∈ Icc (0 : ℝ) S := ⟨hr.1, hr.2.trans hτS.le⟩
    have hu1 : Summable (fourierMoment 1 (s.coefficients r)) :=
      hSum.of_nonneg_of_le (fourierMoment_nonneg 1 _)
        (fun k ↦ (fourierMoment_mono _ (by omega : 1 ≤ 3) k).trans (hu3 r hrS k))
    have hp : IsPlanar (s.coefficients r) := by
      rw [hs]
      exact isPlanar_of_tame hm hnu hu c hrT
    unfold stretching
    exact (integral_congr_ae (Filter.Eventually.of_forall fun x ↦
      stretchingDensity_planar _ hu1 hp x)).trans (by simp)
  have hint : (∫ r in (0 : ℝ)..τ, stretching (s.coefficients r)) = 0 := by
    rw [intervalIntegral.integral_congr (g := fun _ ↦ (0 : ℝ)) fun r hr ↦ by
      rw [uIcc_of_le hτ.1] at hr
      exact hzero r hr]
    simp
  have hP : 0 ≤ nu * ∫ r in (0 : ℝ)..τ, palinstrophy (s.coefficients r) :=
    mul_nonneg hnu.le (intervalIntegral.integral_nonneg hτ.1 fun r _ ↦ palinstrophy_nonneg _)
  rw [hint] at hid
  rw [← hs]
  linarith

/-- **Global regularity of planar flows.** Planar admissible data of order at
least seven, of any size, have a unique global solution, and it stays
planar. -/
theorem nonempty_globalSolution_of_planar (m : ℕ) (hm : 7 ≤ m) {nu : ℝ} (hnu : 0 < nu)
    (u₀ : FourierVelocity) (hr : ∀ q, u₀ (-q) = coefficientConjugate (u₀ q))
    (hd : ∀ q, modeDot q (u₀ q) = 0) (hz : u₀ 0 = 0) {E₀ : ℝ} (hE₀0 : 0 ≤ E₀)
    (hE₀ : ∀ F, velocityEnergy m F u₀ ≤ E₀) (hu : IsPlanar u₀) :
    Nonempty (GlobalSolution nu m u₀) := by
  refine nonempty_globalSolution hm hnu ?_
  refine exists_tameSolutionOn_of_orderOne m (by omega) hnu u₀ hr hd hz hE₀0 hE₀ ?_
  intro H _
  refine ⟨meanEnstrophy u₀ / Real.pi ^ 2, fun T _ c τ hτ F ↦ ?_⟩
  obtain ⟨B, hB⟩ := c.order_local τ hτ.2
  have hB5 : ∀ G : Finset Wavevector, velocityEnergy 5 G (c.coefficients τ) ≤ B :=
    fun G ↦ (velocityEnergy_le_of_order_le (by omega) _ G).trans (hB τ ⟨hτ.1, le_rfl⟩ G)
  calc velocityEnergy 1 F (c.coefficients τ)
      ≤ (∫ x : T3, ‖fullVorticity (c.coefficients τ) x‖ ^ 2) / Real.pi ^ 2 :=
        velocityEnergy_one_le _ (summable_fourierMoment_one _ hB5) (c.reality τ)
          (c.transverse τ) (c.zero τ) F
    _ ≤ meanEnstrophy u₀ / Real.pi ^ 2 :=
        div_le_div_of_nonneg_right (meanEnstrophy_le_of_planar hm hnu hu c hτ) (by positivity)

end Global

end Mettapedia.FluidDynamics.NavierStokes.FourierPlanarRegularity
