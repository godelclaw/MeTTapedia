import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.BetchovIdentity
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.StrainEigenvalueContinuity
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalInitialSpectral
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.FourierCoherenceRegularity

/-!
# Enstrophy grows only through sheet-forming strain

At each point the strain of the actual periodic field has ordered eigenvalues
`λ₀ ≥ λ₁ ≥ λ₂` summing to zero. By Betchov's identity the enstrophy production is
`∫ ⟪ω, S ω⟫ = -(4/3) ∫ tr(S³)`, and `-(4/3) tr(S³) ≤ 2 max(λ₁, 0) |S|²` pointwise, while
`∫ |S|² = (1/2) ∫ |ω|²`. Hence

```text
∫ ⟪ω, S ω⟫ ≤ (sup_x max(λ₁, 0)) ∫ |ω|²,
```

where the strain has at most one expanding direction (`λ₁ ≤ 0`: line stretching, the
configuration of a vortex tube), its share of the exactly integrated production is not
positive. Only a positive middle eigenvalue, two expanding directions flattening fluid
elements into sheets, can raise the enstrophy.

Along a tame solution the enstrophy identity and Grönwall's inequality give
`Z(τ) ≤ Z(0) exp(2 ∫₀^τ sup_x max(λ₁, 0))`; the order-one energy is controlled by the
enstrophy, so a finite-horizon bound on the time integral of the spatial supremum of the
positive middle eigenvalue gives global solutions and the official periodic statement.
Nothing here bounds that integral.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.MiddleEigenvalueCriterion

open scoped RealInnerProductSpace Topology
open MeasureTheory Filter Set
open PeriodicFourierTriad PancakeCurlOutputTail PancakeHigherDerivativeMoments
open PancakeIndexedFourierMoments PancakeInfiniteFourierDerivative PancakeInfiniteSpatialCurl
open PancakeInfiniteRealCurl PancakeFourierMaterialPaths PancakeDyadicDirectionEvolution
open PancakeTransverseEnergyFreezing PancakeLocalStrainEquation PancakeLocalGradientEquation
open PancakeSpectralProjectorRegularity PancakeSpectralProjectorRegularity.SymmetricStrain
open FullLambVector FullVorticityGradientTransport LocalLowDiffusionBudget LocalVorticitySeparation
open LocalEnstrophyDiffusion LocalAlignmentForcing LocalInitialSpectral StrainEigenvalueContinuity
open MiddleEigenvalueAlgebra BetchovIdentity PancakeFilteredStrainDynamics

local notation "T3" => UnitAddTorus (Fin 3)
local notation "R3" => EuclideanSpace ℝ (Fin 3)
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

/-! ## Pointwise identifications -/

theorem gradMat_eq_re (u : FourierVelocity) (hu : Summable (fourierMoment 1 u)) (x : T3)
    (a b : Fin 3) :
    gradMat u x a b = (coordinateDerivative (fullFourierField id u) b x a).re := by
  have hm : Summable (indexedFirstMoment id u) := by simpa only [indexedFirstMoment_id] using hu
  rw [coordinateDerivative_fullFourierField id u hm]
  rfl

theorem fullVorticity_eq_vort (u : FourierVelocity) (hu : Summable (fourierMoment 1 u)) (x : T3)
    (a : Fin 3) : fullVorticity u x a = vort (gradMat u x) a := by
  have h (a b : Fin 3) := gradMat_eq_re u hu x a b
  fin_cases a <;>
    simp [fullVorticity, spatialCurl, vort, h, complexRealPartEuclideanCLM_apply,
      complexRealPartEuclidean]

theorem norm_sq_fullVorticity (u : FourierVelocity) (hu : Summable (fourierMoment 1 u))
    (x : T3) : ‖fullVorticity u x‖ ^ 2 = vortSq (gradMat u x) := by
  rw [EuclideanSpace.norm_sq_eq, vortSq]
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  rw [Real.norm_eq_abs, sq_abs, fullVorticity_eq_vort u hu x a]

theorem stretchingDensity_eq_stretch (u : FourierVelocity) (hu : Summable (fourierMoment 1 u))
    (x : T3) : stretchingDensity u x = stretch (gradMat u x) := by
  rw [stretchingDensity, ← gradient_vorticity, ← directional_velocityJet u hu x]
  simp only [inner_eq_sum, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, stretch,
    fullVorticity_eq_vort u hu x, gradMat, Fin.sum_univ_three]
  ring

/-- The symmetric part of the gradient matrix is the route's strain operator. -/
theorem toStrain_eq_fullSymmetricStrain (u : FourierVelocity) (hu : Summable (fourierMoment 1 u))
    (x : T3) : toStrain (MiddleEigenvalueAlgebra.symm (gradMat u x))
      (MiddleEigenvalueAlgebra.symm_symm _) = fullSymmetricStrain u x := by
  apply Subtype.ext
  refine ContinuousLinearMap.ext fun v ↦ ?_
  ext a
  change matCLM (MiddleEigenvalueAlgebra.symm (gradMat u x)) v a = fullStrainOperator u x v a
  rw [matCLM_apply, fullStrainOperator, realMatrixOperator_apply]
  refine Finset.sum_congr rfl fun b _ ↦ ?_
  congr 1
  rw [symm_apply, gradMat_eq_re u hu x, gradMat_eq_re u hu x]
  simp only [PancakeLocalStrainEquation.spatialStrain, symmetrize, LinearMap.coe_mk,
    AddHom.coe_mk, Matrix.smul_apply, Matrix.add_apply, Matrix.transpose_apply,
    spatialVelocityGradient, smul_eq_mul, Complex.mul_re, Complex.add_re]
  norm_num
  ring

/-! ## The positive middle eigenvalue -/

/-- The positive part of the middle strain eigenvalue: positive exactly where two
directions are stretched. -/
def middlePos (u : FourierVelocity) (x : T3) : ℝ :=
  max (secondEigenvalue (fullSymmetricStrain u x)) 0

/-- Its spatial supremum. -/
def middleSup (u : FourierVelocity) : ℝ := ⨆ x : T3, middlePos u x

theorem middlePos_nonneg (u : FourierVelocity) (x : T3) : 0 ≤ middlePos u x := le_max_right _ _

theorem middleSup_nonneg (u : FourierVelocity) : 0 ≤ middleSup u :=
  Real.iSup_nonneg fun x ↦ middlePos_nonneg u x

theorem continuous_fullSymmetricStrain (u : FourierVelocity)
    (hu : Summable (fourierMoment 1 u)) : Continuous (fullSymmetricStrain u) :=
  (continuous_fullStrainOperator u hu).subtype_mk _

theorem continuous_middlePos (u : FourierVelocity) (hu : Summable (fourierMoment 1 u)) :
    Continuous (middlePos u) :=
  (continuous_secondEigenvalue.comp (continuous_fullSymmetricStrain u hu)).max continuous_const

theorem middlePos_le_middleSup (u : FourierVelocity) (hu : Summable (fourierMoment 1 u))
    (x : T3) : middlePos u x ≤ middleSup u :=
  le_ciSup (isCompact_range (continuous_middlePos u hu)).bddAbove x

/-- **The pointwise cube bound.** -/
theorem neg_trCube_le_middlePos (u : FourierVelocity) (hu : Summable (fourierMoment 2 u))
    (hd : ∀ q, modeDot q (u q) = 0) (x : T3) :
    -(4 / 3) * trCube (MiddleEigenvalueAlgebra.symm (gradMat u x)) ≤
      2 * middlePos u x * normSq (MiddleEigenvalueAlgebra.symm (gradMat u x)) := by
  have htr : MiddleEigenvalueAlgebra.symm (gradMat u x) 0 0 +
      MiddleEigenvalueAlgebra.symm (gradMat u x) 1 1 +
      MiddleEigenvalueAlgebra.symm (gradMat u x) 2 2 = 0 := by
    rw [symm_trace]
    exact gradMat_trace u hu hd x
  have h := neg_trCube_le (MiddleEigenvalueAlgebra.symm (gradMat u x))
    (MiddleEigenvalueAlgebra.symm_symm _) htr
  rwa [toStrain_eq_fullSymmetricStrain u (summable_firstMoment_of_second u hu)] at h

/-! ## Betchov's identity and the stretching bound -/

theorem continuous_gradMat_entry (u : FourierVelocity) (a b : Fin 3) :
    Continuous (fun x ↦ gradMat u x a b) :=
  (EuclideanSpace.proj a : R3 →L[ℝ] ℝ).continuous.comp (continuous_velocityJet u b)

theorem integrable_poly {f : T3 → ℝ} (hf : Continuous f) : Integrable f :=
  hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

theorem continuous_symm_entry (u : FourierVelocity) (a b : Fin 3) :
    Continuous (fun x ↦ MiddleEigenvalueAlgebra.symm (gradMat u x) a b) := by
  simp only [symm_apply]
  exact ((continuous_gradMat_entry u a b).add (continuous_gradMat_entry u b a)).div_const 2

theorem continuous_trCube_symm (u : FourierVelocity) :
    Continuous (fun x ↦ trCube (MiddleEigenvalueAlgebra.symm (gradMat u x))) := by
  have hc := continuous_symm_entry u
  simp only [trCube]
  exact continuous_finsetSum _ fun a _ ↦ continuous_finsetSum _ fun b _ ↦
    continuous_finsetSum _ fun c _ ↦ ((hc a b).mul (hc b c)).mul (hc c a)

theorem continuous_normSq_symm (u : FourierVelocity) :
    Continuous (fun x ↦ normSq (MiddleEigenvalueAlgebra.symm (gradMat u x))) := by
  have hc := continuous_symm_entry u
  simp only [normSq]
  exact continuous_finsetSum _ fun a _ ↦ continuous_finsetSum _ fun b _ ↦ (hc a b).pow 2

theorem continuous_vort_entry (u : FourierVelocity) (a : Fin 3) :
    Continuous (fun x ↦ vort (gradMat u x) a) := by
  have hc := continuous_gradMat_entry u
  fin_cases a <;> simp only [vort, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons] <;> exact (hc _ _).sub (hc _ _)

theorem continuous_stretch (u : FourierVelocity) :
    Continuous (fun x ↦ stretch (gradMat u x)) := by
  have hc := continuous_gradMat_entry u
  have hv := continuous_vort_entry u
  simp only [stretch]
  exact continuous_finsetSum _ fun a _ ↦ continuous_finsetSum _ fun b _ ↦
    ((hv a).mul (hc a b)).mul (hv b)

theorem continuous_vortSq (u : FourierVelocity) :
    Continuous (fun x ↦ vortSq (gradMat u x)) := by
  have hv := continuous_vort_entry u
  simp only [vortSq]
  exact continuous_finsetSum _ fun a _ ↦ (hv a).pow 2

/-- **Betchov's identity**: `∫ ⟪ω, S ω⟫ = -(4/3) ∫ tr(S³)`. -/
theorem stretching_eq_trCube (u : FourierVelocity) (hu : Summable (fourierMoment 3 u))
    (hd : ∀ q, modeDot q (u q) = 0) :
    stretching u = -(4 / 3) * ∫ x : T3, trCube (MiddleEigenvalueAlgebra.symm (gradMat u x)) := by
  have hu2 := summable_fourierMoment_of_le u (by omega : 2 ≤ 3) hu
  have hu1 := summable_firstMoment_of_second u hu2
  have hcS := continuous_trCube_symm u
  have hcSt := continuous_stretch u
  have h0 := integral_trCube_eq_zero u hu hd
  have hpt (x : T3) : trCube (gradMat u x) =
      trCube (MiddleEigenvalueAlgebra.symm (gradMat u x)) + 3 / 4 * stretch (gradMat u x) :=
    trCube_eq _ (gradMat_trace u hu2 hd x)
  simp only [hpt] at h0
  rw [integral_add (integrable_poly hcS) ((integrable_poly hcSt).const_mul _),
    integral_const_mul] at h0
  have hs : stretching u = ∫ x : T3, stretch (gradMat u x) :=
    integral_congr_ae (Eventually.of_forall fun x ↦ stretchingDensity_eq_stretch u hu1 x)
  rw [hs]
  linarith

/-- The strain carries half of the enstrophy. -/
theorem integral_normSq_eq (u : FourierVelocity) (hu : Summable (fourierMoment 3 u))
    (hd : ∀ q, modeDot q (u q) = 0) :
    ∫ x : T3, normSq (MiddleEigenvalueAlgebra.symm (gradMat u x)) = meanEnstrophy u / 2 := by
  have hu2 := summable_fourierMoment_of_le u (by omega : 2 ≤ 3) hu
  have hu1 := summable_firstMoment_of_second u hu2
  have hcN := continuous_normSq_symm u
  have hcV := continuous_vortSq u
  have h0 := integral_trSq_eq_zero u hu hd
  simp only [trSq_eq] at h0
  rw [integral_sub (integrable_poly hcN) ((integrable_poly hcV).div_const 2),
    integral_div] at h0
  have hZ : meanEnstrophy u = ∫ x : T3, vortSq (gradMat u x) := by
    rw [meanEnstrophy_eq]
    exact integral_congr_ae (Eventually.of_forall fun x ↦ norm_sq_fullVorticity u hu1 x)
  rw [hZ]
  linarith

/-- **Enstrophy grows only through sheet-forming strain.** -/
theorem stretching_le_middleSup (u : FourierVelocity) (hu : Summable (fourierMoment 3 u))
    (hd : ∀ q, modeDot q (u q) = 0) : stretching u ≤ middleSup u * meanEnstrophy u := by
  have hu2 := summable_fourierMoment_of_le u (by omega : 2 ≤ 3) hu
  have hu1 := summable_firstMoment_of_second u hu2
  have hcS := continuous_trCube_symm u
  have hcN := continuous_normSq_symm u
  have hN0 (x : T3) : 0 ≤ normSq (MiddleEigenvalueAlgebra.symm (gradMat u x)) := by
    unfold normSq
    positivity
  have hpt (x : T3) : -(4 / 3) * trCube (MiddleEigenvalueAlgebra.symm (gradMat u x)) ≤
      2 * middleSup u * normSq (MiddleEigenvalueAlgebra.symm (gradMat u x)) :=
    (neg_trCube_le_middlePos u hu2 hd x).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (middlePos_le_middleSup u hu1 x) (by norm_num)) (hN0 x))
  have hmono := integral_mono ((integrable_poly hcS).const_mul _)
    ((integrable_poly hcN).const_mul _) hpt
  rw [integral_const_mul, integral_const_mul, integral_normSq_eq u hu hd] at hmono
  rw [stretching_eq_trCube u hu hd]
  linarith

/-! ## Continuity along a local solution -/

theorem continuousOn_middleSup {nu T B : ℝ} {u₀ : FourierVelocity}
    (s : PancakeLocalInfiniteVelocity.LocalInfiniteVelocitySolution nu u₀ T B)
    (g : Wavevector → ℝ) (hSum : Summable g)
    (hu : ∀ t ∈ Icc (0 : ℝ) T, ∀ q, fourierMoment 2 (s.coefficients t) q ≤ g q) :
    ContinuousOn (fun t ↦ middleSup (s.coefficients t)) (Icc 0 T) := by
  have hS := LocalAlignmentContinuity.continuous_fullStrainOperator_parametric
    (fun t : Icc (0 : ℝ) T ↦ s.coefficients t)
    (fun q i ↦ (s.continuous q i).comp continuous_subtype_val) g hSum (fun t ↦ hu t t.2)
  have hM : Continuous (fun z : Icc (0 : ℝ) T × T3 ↦ middlePos (s.coefficients z.1) z.2) :=
    (continuous_secondEigenvalue.comp (hS.subtype_mk _)).max continuous_const
  have h := IsCompact.continuous_sSup
    (f := fun (t : Icc (0 : ℝ) T) (x : T3) ↦ middlePos (s.coefficients t) x)
    (K := univ) isCompact_univ hM
  refine continuousOn_iff_continuous_domRestrict.mpr ?_
  have h' : Continuous fun t : Icc (0 : ℝ) T ↦ ⨆ x : T3, middlePos (s.coefficients t) x := by
    simpa only [image_univ, sSup_range] using h
  exact h'

/-! ## Dynamics -/

section Dynamics

open PancakeSobolevWeights PancakeSobolevVelocityRate PancakeHigherSobolevWeights
open PancakeHigherSobolevVelocityRate PancakeLatticeDecayEnvelope PancakeHigherLocalVelocity
open PancakeLocalInfiniteVelocity InfiniteConvectionEnergy PancakeBlockReality
open FourierTameTriad FourierContinuation FourierTameContinuation FourierEighthMomentControl
open FourierVorticitySupContinuation FourierGlobalSolution FourierRegularityEquivalence
open FourierUniqueness PancakeFrequencyProjectorCommutator

variable {m : ℕ} {nu : ℝ} {u₀ : FourierVelocity}

/-- **The enstrophy is controlled by the time integral of sheet-forming strain.** -/
theorem meanEnstrophy_le_of_middle (hm : 7 ≤ m) (hnu : 0 < nu) {T : ℝ}
    (c : TameSolutionOn nu m u₀ T) (τ : ℝ) (hτ : τ ∈ Ico (0 : ℝ) T) :
    meanEnstrophy (c.coefficients τ) ≤
      meanEnstrophy u₀ * Real.exp (2 * ∫ r in (0 : ℝ)..τ, middleSup (c.coefficients r)) := by
  obtain ⟨S, hSdef⟩ : ∃ S, S = (τ + T) / 2 := ⟨_, rfl⟩
  have hτS : τ < S := by rw [hSdef]; linarith [hτ.2]
  have hST : S < T := by rw [hSdef]; linarith [hτ.2]
  have hS0 : 0 < S := lt_of_le_of_lt hτ.1 hτS
  obtain ⟨B, s, hs, g, hg, hSum, hu3⟩ := local_envelope_at hm c hST
  have hu2 : ∀ t ∈ Icc (0 : ℝ) S, ∀ q, fourierMoment 2 (s.coefficients t) q ≤ g q :=
    fun t ht q ↦ (fourierMoment_mono _ (by omega : 2 ≤ 3) q).trans (hu3 t ht q)
  have hZc := continuousOn_meanEnstrophy s g hSum hu3
  have hMc := continuousOn_middleSup s g hSum hu2
  have hSc := continuousOn_stretching s g hSum hu3
  have hbound : ∀ t ∈ Icc (0 : ℝ) S, stretching (s.coefficients t) ≤
      middleSup (s.coefficients t) * meanEnstrophy (s.coefficients t) := fun t ht ↦
    stretching_le_middleSup _ (hSum.of_nonneg_of_le (fourierMoment_nonneg _ _) (hu3 t ht))
      (s.transverse t)
  have hineq : ∀ t ∈ Icc (0 : ℝ) τ, meanEnstrophy (s.coefficients t) ≤
      meanEnstrophy u₀ + 2 * ∫ r in (0 : ℝ)..t,
        middleSup (s.coefficients r) * meanEnstrophy (s.coefficients r) := by
    intro t ht
    have htS : t ∈ Icc (0 : ℝ) S := ⟨ht.1, ht.2.trans hτS.le⟩
    have hsub : Icc (0 : ℝ) t ⊆ Icc 0 S := Icc_subset_Icc le_rfl htS.2
    have hid := enstrophy_identity s g hg hSum hu3 hS0 t htS
    have hS' := (hSc.mono hsub).intervalIntegrable_of_Icc (μ := volume) ht.1
    have hMZ := ((hMc.mul hZc).mono hsub).intervalIntegrable_of_Icc (μ := volume) ht.1
    have hi : (∫ r in (0 : ℝ)..t, stretching (s.coefficients r)) ≤
        ∫ r in (0 : ℝ)..t, middleSup (s.coefficients r) * meanEnstrophy (s.coefficients r) :=
      intervalIntegral.integral_mono_on ht.1 hS' hMZ (fun r hr ↦ hbound r (hsub hr))
    have hG0 : 0 ≤ ∫ r in (0 : ℝ)..t, palinstrophy (s.coefficients r) :=
      intervalIntegral.integral_nonneg ht.1 (fun r _ ↦ palinstrophy_nonneg _)
    have hnG := mul_nonneg hnu.le hG0
    linarith
  have hsubτ : Icc (0 : ℝ) τ ⊆ Icc 0 S := Icc_subset_Icc le_rfl hτS.le
  have hG := le_mul_exp_of_le_add_integral hτ.1 (by norm_num : (0 : ℝ) ≤ 2) (hZc.mono hsubτ)
    (hMc.mono hsubτ) (fun t _ ↦ middleSup_nonneg _) hineq
  rw [hs] at hG
  exact hG

/-- **Global existence from sheet-forming strain.** If on every finite horizon the time
integral of the spatial supremum of the positive middle strain eigenvalue is bounded along
the tame solutions, tame solutions exist on every interval. -/
theorem exists_tameSolutionOn_of_middleBound (hm : 7 ≤ m) (hnu : 0 < nu)
    (hr : ∀ q, u₀ (-q) = coefficientConjugate (u₀ q)) (hd : ∀ q, modeDot q (u₀ q) = 0)
    (hz : u₀ 0 = 0) {E₀ : ℝ} (hE₀0 : 0 ≤ E₀) (hE₀ : ∀ F, velocityEnergy m F u₀ ≤ E₀)
    (hmid : ∀ H, 0 < H → ∃ G, ∀ T, T ≤ H → ∀ c : TameSolutionOn nu m u₀ T,
      ∀ τ ∈ Ico (0 : ℝ) T, ∫ r in (0 : ℝ)..τ, middleSup (c.coefficients r) ≤ G) :
    ∀ H, 0 < H → Nonempty (TameSolutionOn nu m u₀ H) := by
  refine exists_tameSolutionOn_of_orderOne m (by omega) hnu u₀ hr hd hz hE₀0 hE₀ ?_
  intro H hH
  obtain ⟨G, hG⟩ := hmid H hH
  refine ⟨meanEnstrophy u₀ * Real.exp (2 * G) / Real.pi ^ 2, fun T hT c τ hτ F ↦ ?_⟩
  obtain ⟨B, hB⟩ := c.order_local τ hτ.2
  have hB5 : ∀ G' : Finset Wavevector, velocityEnergy 5 G' (c.coefficients τ) ≤ B := by
    intro G'
    refine le_trans ?_ (hB τ ⟨hτ.1, le_rfl⟩ G')
    rw [velocityEnergy_eq, velocityEnergy_eq]
    refine Finset.sum_le_sum fun k _ ↦ ?_
    have hE : 0 ≤ coefficientEnergy (c.coefficients τ k) := by
      rw [← norm_coefficientVec_sq]
      positivity
    have hw : orderWeight 5 k ^ 2 ≤ orderWeight m k ^ 2 := by
      unfold orderWeight
      rw [← pow_mul, ← pow_mul]
      exact pow_le_pow_right₀ (by linarith [norm_nonneg (frequencyVec k)]) (by omega)
    exact mul_le_mul_of_nonneg_right hw hE
  have h1 := velocityEnergy_one_le (c.coefficients τ) (summable_fourierMoment_one _ hB5)
    (c.reality τ) (c.transverse τ) (c.zero τ) F
  have h2 := meanEnstrophy_le_of_middle hm hnu c τ hτ
  have hZ : (∫ x : T3, ‖fullVorticity (c.coefficients τ) x‖ ^ 2) =
      meanEnstrophy (c.coefficients τ) := rfl
  rw [hZ] at h1
  have hexp : Real.exp (2 * ∫ r in (0 : ℝ)..τ, middleSup (c.coefficients r)) ≤
      Real.exp (2 * G) := Real.exp_le_exp.mpr (by linarith [hG T hT c τ hτ])
  have h3 : meanEnstrophy (c.coefficients τ) ≤ meanEnstrophy u₀ * Real.exp (2 * G) :=
    h2.trans (mul_le_mul_of_nonneg_left hexp (meanEnstrophy_nonneg _))
  exact h1.trans (div_le_div_of_nonneg_right h3 (by positivity))

theorem nonempty_globalSolution_of_middleBound (hm : 7 ≤ m) (hnu : 0 < nu)
    (hr : ∀ q, u₀ (-q) = coefficientConjugate (u₀ q)) (hd : ∀ q, modeDot q (u₀ q) = 0)
    (hz : u₀ 0 = 0) {E₀ : ℝ} (hE₀0 : 0 ≤ E₀) (hE₀ : ∀ F, velocityEnergy m F u₀ ≤ E₀)
    (hmid : ∀ H, 0 < H → ∃ G, ∀ T, T ≤ H → ∀ c : TameSolutionOn nu m u₀ T,
      ∀ τ ∈ Ico (0 : ℝ) T, ∫ r in (0 : ℝ)..τ, middleSup (c.coefficients r) ≤ G) :
    Nonempty (GlobalSolution nu m u₀) :=
  nonempty_globalSolution hm hnu
    (exists_tameSolutionOn_of_middleBound hm hnu hr hd hz hE₀0 hE₀ hmid)

/-- **Global solution ⟺ bounded sheet-forming strain.** A datum has a global solution if
and only if, on every finite horizon, the time integral of the spatial supremum of the
positive middle strain eigenvalue is bounded along the tame solutions. -/
theorem nonempty_globalSolution_iff_middleBound (hm : 7 ≤ m) (hnu : 0 < nu)
    (hr : ∀ q, u₀ (-q) = coefficientConjugate (u₀ q)) (hd : ∀ q, modeDot q (u₀ q) = 0)
    (hz : u₀ 0 = 0) {E₀ : ℝ} (hE₀0 : 0 ≤ E₀) (hE₀ : ∀ F, velocityEnergy m F u₀ ≤ E₀) :
    Nonempty (GlobalSolution nu m u₀) ↔
      ∀ H, 0 < H → ∃ G, ∀ T, T ≤ H → ∀ c : TameSolutionOn nu m u₀ T,
        ∀ τ ∈ Ico (0 : ℝ) T, ∫ r in (0 : ℝ)..τ, middleSup (c.coefficients r) ≤ G := by
  refine ⟨fun ⟨g⟩ H _ ↦ ?_, nonempty_globalSolution_of_middleBound hm hnu hr hd hz hE₀0 hE₀⟩
  obtain ⟨B, s, hs, e, _, hSum, hu⟩ := GlobalSolution.local_envelope hm g H
  have hu2 : ∀ t ∈ Icc (0 : ℝ) H, ∀ k, fourierMoment 2 (s.coefficients t) k ≤ e k :=
    fun t ht k ↦ (fourierMoment_mono _ (by omega : 2 ≤ 3) k).trans (hu t ht k)
  have hc := continuousOn_middleSup s e hSum hu2
  rw [hs] at hc
  exact integral_bound_of_global hm hnu g middleSup H hc

/-- **The open problem in terms of sheet-forming strain.** Periodic regularity holds exactly
when, for every positive viscosity and admissible datum, the time integral of the spatial
supremum of the positive middle strain eigenvalue is bounded on every finite horizon. -/
theorem periodicRegularity_iff_middleBound (hm : 7 ≤ m) :
    PeriodicRegularity m ↔ ∀ nu : ℝ, 0 < nu → ∀ u₀ : FourierVelocity, Admissible m u₀ →
      ∀ H, 0 < H → ∃ G, ∀ T, T ≤ H → ∀ c : TameSolutionOn nu m u₀ T,
        ∀ τ ∈ Ico (0 : ℝ) T, ∫ r in (0 : ℝ)..τ, middleSup (c.coefficients r) ≤ G := by
  refine forall₂_congr fun nu hnu ↦ forall₂_congr fun u₀ hu ↦ ?_
  obtain ⟨hr, hd, hz, E₀, hE₀⟩ := hu
  have hE₀0 : 0 ≤ E₀ := le_trans (by simp [velocityEnergy_eq]) (hE₀ ∅)
  exact nonempty_globalSolution_iff_middleBound hm hnu hr hd hz hE₀0 hE₀

/-- **Sheet-forming strain and the official statement.** If, for every positive viscosity
and admissible datum, the time integral of the spatial supremum of the positive middle
strain eigenvalue is bounded on every finite horizon along the tame solutions, the official
periodic statement holds. -/
theorem periodicStatementB_of_middleBound (hm : 7 ≤ m)
    (h : ∀ nu : ℝ, 0 < nu → ∀ u₀ : FourierVelocity, Admissible m u₀ →
      ∀ H, 0 < H → ∃ G, ∀ T, T ≤ H → ∀ c : TameSolutionOn nu m u₀ T,
        ∀ τ ∈ Ico (0 : ℝ) T, ∫ r in (0 : ℝ)..τ, middleSup (c.coefficients r) ≤ G) :
    OfficialPeriodicProblem.PeriodicStatementB := by
  apply FourierOfficialTheorems.periodicStatementB_of_periodicRegularity hm
  intro nu hnu u₀ hu
  have hmid := h nu hnu u₀ hu
  obtain ⟨hr, hd, hz, E₀, hE₀⟩ := hu
  have hE₀0 : 0 ≤ E₀ := le_trans (by simp [velocityEnergy_eq]) (hE₀ ∅)
  exact nonempty_globalSolution_of_middleBound hm hnu hr hd hz hE₀0 hE₀ hmid

end Dynamics

end Mettapedia.FluidDynamics.NavierStokes.MiddleEigenvalueCriterion
