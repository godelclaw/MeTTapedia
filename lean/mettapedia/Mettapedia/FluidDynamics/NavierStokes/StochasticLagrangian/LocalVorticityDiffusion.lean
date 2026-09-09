import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalMaterialVorticity
import Mettapedia.Analysis.ODE.QuadraticFormBound

/-!
# Continuity of the actual viscous vorticity source

A common third absolute Fourier moment controls `Δ curl u` uniformly on
the local existence interval. This supplies continuity of the actual source
in the material vorticity equation, rather than an assumed forcing path.

The final integrating-factor estimate uses this source and the actual strain.
It is conditional only on the stated scalar growth bound; it does not assert
that the resulting strain or diffusion budget stays finite at a maximal time.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.LocalVorticityDiffusion

open scoped BigOperators Topology RealInnerProductSpace
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeCurlOutputTail
open PancakeHigherDerivativeMoments PancakeFrequencyProjectorCommutator
open PancakeInfiniteSpatialCurl PancakeInfiniteSpatialLaplacian PancakeInfiniteFourierDerivative
open PancakeFourierTranslationCurve PancakeInfiniteFourierTime PancakeIndexedFourierMoments
open PancakeGalerkinKineticEnergy PancakePeriodicVorticityEquation PancakeIncomingLowSourceEnergy
open PancakeLocalInfiniteVelocity PancakeLocalSpatialVelocity PancakeLocalMaterialTrajectories
open PancakeFourierMaterialPaths PancakeDyadicDirectionEvolution LocalMaterialVorticity
open PancakePeriodicComplexStretch PancakeTransverseEnergyFreezing

local notation "T3" => UnitAddTorus (Fin 3)
local notation "X3" => Fin 3 → ℝ
local notation "R3" => EuclideanSpace ℝ (Fin 3)

/-- Curl costs one absolute Fourier moment, with the unit-torus factor. -/
theorem fourierMoment_curl_le (m : ℕ) (u : FourierVelocity) (q : Wavevector) :
    fourierMoment m (fourierCurl u) q ≤ (2 * Real.pi) * fourierMoment (m + 1) u q := by
  unfold fourierMoment
  calc
    _ ≤ (1 + ‖frequencyVec q‖)^m *
        ((2 * Real.pi) * ‖frequencyVec q‖ * ‖coefficientVec (u q)‖) :=
      mul_le_mul_of_nonneg_left (norm_fourierCurl_le u q) (by positivity)
    _ ≤ (1 + ‖frequencyVec q‖)^m *
        ((2 * Real.pi) * (1 + ‖frequencyVec q‖) * ‖coefficientVec (u q)‖) := by
      gcongr
      exact le_add_of_nonneg_left zero_le_one
    _ = _ := by rw [pow_succ]; ring

/-- The Laplacian costs two absolute Fourier moments. -/
theorem fourierMoment_laplacian_le (m : ℕ) (u : FourierVelocity) (q : Wavevector) :
    fourierMoment m (laplacianCoeff u) q ≤ (2 * Real.pi)^2 * fourierMoment (m + 2) u q := by
  change (1 + ‖frequencyVec q‖)^m *
    ‖(unitTorusDerivativePhase^2 * modeSquare q) • coefficientVec (u q)‖ ≤ _
  rw [norm_smul, norm_mul, norm_pow, norm_derivativePhase, norm_modeSquare]
  calc
    _ ≤ (1 + ‖frequencyVec q‖)^m *
        ((2 * Real.pi)^2 * (1 + ‖frequencyVec q‖)^2 * ‖coefficientVec (u q)‖) := by
      gcongr
      exact le_add_of_nonneg_left zero_le_one
    _ = _ := by simp only [fourierMoment, pow_add]; ring

theorem norm_laplacianCurlCoeff_le (u : FourierVelocity) (q : Wavevector) :
    ‖laplacianCoeff (fourierCurl u) q‖ ≤ (2 * Real.pi)^3 * fourierMoment 3 u q := by
  calc
    _ ≤ fourierMoment 0 (laplacianCoeff (fourierCurl u)) q := by
      simpa only [fourierMoment, pow_zero, one_mul] using
        norm_coefficient_sup_le_euclidean (laplacianCoeff (fourierCurl u) q)
    _ ≤ (2 * Real.pi)^2 * fourierMoment 2 (fourierCurl u) q :=
      fourierMoment_laplacian_le 0 _ q
    _ ≤ (2 * Real.pi)^2 * ((2 * Real.pi) * fourierMoment 3 u q) :=
      mul_le_mul_of_nonneg_left (fourierMoment_curl_le 2 u q) (sq_nonneg _)
    _ = _ := by ring

/-- Dominated coefficient continuity gives continuity in the uniform norm
of continuous Fourier fields. -/
theorem continuous_fullFourierField_of_norm_le {Z : Type*} [TopologicalSpace Z]
    (a : Z → FourierVelocity) (hc : ∀ q i, Continuous (fun z ↦ a z q i))
    (g : Wavevector → ℝ) (hSum : Summable g) (ha : ∀ z q, ‖a z q‖ ≤ g q) :
    Continuous (fun z ↦ fullFourierField id (a z)) :=
  continuous_tsum (fun q ↦ (modeFieldCLM q).continuous.comp (continuous_pi (hc q))) hSum
    (fun q z ↦ (norm_modeField_le q _).trans (ha z q))

variable {nu T B : ℝ} {u₀ : FourierVelocity}
  (s : LocalInfiniteVelocitySolution nu u₀ T B)
  (g : Wavevector → ℝ) (hg : ∀ q, 0 ≤ g q) (hSum : Summable g)
  (hu : ∀ τ ∈ Set.Icc (0 : ℝ) T, ∀ q, fourierMoment 3 (s.coefficients τ) q ≤ g q)

include hSum hu

theorem continuous_laplacianCurl_field :
    Continuous (fun t : Set.Icc (0 : ℝ) T ↦
      fullFourierField id (laplacianCoeff (fourierCurl (s.coefficients t)))) := by
  refine continuous_fullFourierField_of_norm_le _ ?_ (fun q ↦ (2 * Real.pi)^3 * g q)
    (hSum.mul_left _) ?_
  · intro q i
    have hc (j : Fin 3) : Continuous (fun t : Set.Icc (0 : ℝ) T ↦ s.coefficients t q j) :=
      (s.continuous q j).comp continuous_subtype_val
    fin_cases i <;> simp only [laplacianCoeff, fourierCurl, coefficientCross,
      Pi.smul_apply, smul_eq_mul] <;> fun_prop
  · intro t q
    exact (norm_laplacianCurlCoeff_le _ q).trans
      (mul_le_mul_of_nonneg_left (hu t t.2 q) (by positivity))

theorem spatialLaplacian_curl_eq (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) T) :
    spatialLaplacian (spatialCurl (spatialField s t)) =
      fullFourierField id (laplacianCoeff (fourierCurl (s.coefficients t))) := by
  have hm := hSum.of_nonneg_of_le (fourierMoment_nonneg _ _) (hu t ht)
  have hm1 := summable_fourierMoment_of_le _ (by omega : 1 ≤ 3) hm
  have hcurl := (hm.mul_left (2 * Real.pi)).of_nonneg_of_le (fourierMoment_nonneg _ _)
    (fourierMoment_curl_le 2 (s.coefficients t))
  simp only [spatialField, spatialCurl_velocity _ hm1, spatialLaplacian_fullFourierField _ hcurl]

theorem continuous_diffusion_spaceTime :
    Continuous (fun z : Set.Icc (0 : ℝ) T × T3 ↦
      nu • complexRealPartEuclideanCLM
        (spatialLaplacian (spatialCurl (spatialField s z.1)) z.2)) := by
  have hc := continuous_eval.comp
    (((continuous_laplacianCurl_field s g hSum hu).comp continuous_fst).prodMk continuous_snd)
  simpa only [Function.comp_def, spatialLaplacian_curl_eq s g hSum hu _ (Subtype.prop _)] using
    (complexRealPartEuclideanCLM.continuous.comp hc).const_smul nu

/-- Restrict joint continuity to an actual material path and a compact
subinterval of the local existence interval. -/
theorem continuousOn_diffusionAlong (X : ℝ → X3)
    (hX : ∀ τ ∈ Set.Ioo (0 : ℝ) T, HasDerivAt X (liftedVelocity s τ (X τ)) τ)
    {a b : ℝ} (hI : Set.Icc a b ⊆ Set.Ioo (0 : ℝ) T) :
    ContinuousOn (diffusionAlong s X) (Set.Icc a b) := by
  have hcX : Continuous (fun τ : Set.Icc a b ↦ X τ) :=
    ContinuousOn.restrict (fun τ hτ ↦ (hX τ (hI hτ)).continuousAt.continuousWithinAt)
  have hcpoint : Continuous (fun τ : Set.Icc a b ↦ torusPoint (X τ)) := by
    exact continuous_pi (fun i ↦ (AddCircle.continuous_mk' (1 : ℝ)).comp
      ((continuous_apply i).comp hcX))
  let time : Set.Icc a b → Set.Icc (0 : ℝ) T :=
    fun τ ↦ ⟨τ, (Set.Ioo_subset_Icc_self (hI τ.2))⟩
  have hctime : Continuous time := continuous_subtype_val.subtype_mk _
  have hc := (continuous_diffusion_spaceTime s g hSum hu).comp (hctime.prodMk hcpoint)
  apply continuousOn_iff_continuous_restrict.mpr
  convert! hc using 1

include hg

/-- A weighted norm estimate for the curl of the actual unforced local
Navier--Stokes solution. The source is the constructed viscous term; its
continuity and the vorticity differential equation are not hypotheses.

The scalar quadratic-form bound on strain remains explicit. In particular,
this does not infer a uniform-in-time growth bound from initial energy. -/
theorem norm_vorticityAlong_le_weight_mul_integral (X : ℝ → X3)
    (hX : ∀ τ ∈ Set.Ioo (0 : ℝ) T, HasDerivAt X (liftedVelocity s τ (X τ)) τ)
    {a b : ℝ} (hI : Set.Icc a b ⊆ Set.Ioo (0 : ℝ) T)
    (growth P : ℝ → ℝ) (hPpos : ∀ t, 0 < P t)
    (hP : ∀ t, HasDerivAt P (growth t * P t) t)
    (hstrain : ∀ t ∈ Set.Ico a b, ∀ w : R3,
      ⟪w, strainAlong s X t w⟫ ≤ growth t * ‖w‖^2) :
    ∀ t ∈ Set.Icc a b, ‖vorticityAlong s X t‖ ≤ P t *
      (‖vorticityAlong s X a‖ / P a + ∫ τ in a..t, ‖diffusionAlong s X τ‖ / P τ) := by
  have hd (t : ℝ) (ht : t ∈ Set.Icc a b) :=
    hasDerivAt_vorticityAlong s g hg hSum hu X hX t (hI ht)
  have hc : ContinuousOn (vorticityAlong s X) (Set.Icc a b) :=
    fun t ht ↦ (hd t ht).continuousAt.continuousWithinAt
  have h := Mettapedia.Analysis.ODE.norm_le_exp_mul_weight_mul_integral_on
    (strainAlong s X) growth P (μ := 0) le_rfl hPpos hP hc
    (continuousOn_diffusionAlong s g hSum hu X hX hI)
    (fun t ht ↦ (hd t (Set.Ico_subset_Icc_self ht)).hasDerivWithinAt)
    (by simpa only [add_zero] using hstrain)
  simpa only [zero_mul, Real.exp_zero, one_mul] using h

end Mettapedia.FluidDynamics.NavierStokes.LocalVorticityDiffusion
