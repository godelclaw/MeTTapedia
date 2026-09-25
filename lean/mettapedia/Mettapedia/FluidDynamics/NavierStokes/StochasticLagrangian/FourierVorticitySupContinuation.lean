import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalEnstrophyBalance
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.FourierEighthMomentControl
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.FullStrainFourierSeries
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeIncomingLowSourceEnergy
import Mettapedia.Analysis.ODE.VariableGronwall

/-!
# Continuation of the Fourier solutions under a vorticity-supremum bound

The Beale–Kato–Majda form of the continuation theorem for the actual
periodic Fourier solutions. The integrand is the spatial supremum

```text
vorticitySup u = sup_x |ω(x)|
```

of the actual vorticity; along every local solution it is continuous in
time, including the initial endpoint.

Parseval for each entry of the strain matrix gives `∑ᵢⱼ ∫ |Sᵢⱼ|² ≤ 9 ∫ |ω|²`,
and hence the signed stretching bound

```text
∫ ⟪ω, S ω⟫ ≤ 45 ‖ω‖_∞ ∫ |ω|².
```

With the exact enstrophy identity and Grönwall's inequality,

```text
∫ |ω(t)|² ≤ ∫ |ω₀|² · exp (90 ∫₀ᵗ ‖ω‖_∞).
```

This bounds the order-one energy. `exists_tameSolutionOn_of_vorticitySup`
then gives tame solutions on every interval `[0, H)`, provided the time
integral of the vorticity supremum of every tame solution is bounded on each
finite horizon. That bound is the open dynamical input and is not supplied
here.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.FourierVorticitySupContinuation

open scoped BigOperators RealInnerProductSpace Matrix.Norms.Elementwise
open MeasureTheory Set
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeFrequencyProjectorCommutator
open PancakeSobolevWeights PancakeSobolevVelocityRate PancakeHigherSobolevWeights
open PancakeHigherSobolevVelocityRate PancakeCurlOutputTail PancakeLatticeDecayEnvelope PancakeHigherLocalVelocity
open PancakeGalerkinKineticEnergy PancakeBlockReality PancakeLocalInfiniteVelocity
open InfiniteConvectionEnergy InfiniteKineticCancellation InfiniteFourierParseval
open FullVorticityFourierCoefficients LocalLowDiffusionBudget LocalAlignmentForcing
open PancakeFourierPressureStrain PancakeFourierMaterialPaths PancakeInfiniteFourierDerivative
open PancakeHigherDerivativeMoments PancakeFourierStrainGradient FullStrainFourierSeries
open FourierTameTriad FourierContinuation FourierTameContinuation FourierEighthMomentControl
open LocalEnstrophyDiffusion

local notation "T3" => UnitAddTorus (Fin 3)

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

section Supremum

/-- The spatial supremum of the actual vorticity, `‖ω‖_∞`. -/
def vorticitySup (u : FourierVelocity) : ℝ := ⨆ x : T3, ‖fullVorticity u x‖

theorem vorticitySup_nonneg (u : FourierVelocity) : 0 ≤ vorticitySup u :=
  Real.iSup_nonneg fun _ ↦ norm_nonneg _

theorem norm_fullVorticity_le_vorticitySup (u : FourierVelocity)
    (hu : Summable (fourierMoment 1 u)) (x : T3) :
    ‖fullVorticity u x‖ ≤ vorticitySup u :=
  le_ciSup (isCompact_range (continuous_fullVorticity u hu).norm).bddAbove x

/-- Along a local solution with a common second-moment envelope, the vorticity
supremum is continuous on the closed time interval. -/
theorem continuousOn_vorticitySup {nu T B : ℝ} {u₀ : FourierVelocity}
    (s : LocalInfiniteVelocitySolution nu u₀ T B) (g : Wavevector → ℝ) (hSum : Summable g)
    (hu : ∀ t ∈ Icc (0 : ℝ) T, ∀ q, fourierMoment 2 (s.coefficients t) q ≤ g q) :
    ContinuousOn (fun t ↦ vorticitySup (s.coefficients t)) (Icc 0 T) := by
  have hc := (continuous_fullVorticity_spaceTime s g hSum hu).norm
  have h := IsCompact.continuous_sSup
    (f := fun (t : Icc (0 : ℝ) T) (x : T3) ↦ ‖fullVorticity (s.coefficients t) x‖)
    (K := univ) isCompact_univ hc
  refine continuousOn_iff_continuous_domRestrict.mpr ?_
  have h' : Continuous fun t : Icc (0 : ℝ) T ↦ ⨆ x : T3, ‖fullVorticity (s.coefficients t) x‖ := by
    simpa only [image_univ, sSup_range] using h
  exact h'

end Supremum

section Strain

theorem norm_sq_le_sum_entries (A : MatrixCoefficient) :
    ‖A‖ ^ 2 ≤ ∑ i : Fin 3, ∑ j : Fin 3, ‖A i j‖ ^ 2 := by
  have hs : 0 ≤ ∑ i : Fin 3, ∑ j : Fin 3, ‖A i j‖ ^ 2 := by positivity
  have h : ‖A‖ ≤ Real.sqrt (∑ i : Fin 3, ∑ j : Fin 3, ‖A i j‖ ^ 2) := by
    refine (Matrix.norm_le_iff (Real.sqrt_nonneg _)).mpr fun i j ↦ ?_
    apply Real.le_sqrt_of_sq_le
    exact (Finset.single_le_sum (f := fun j ↦ ‖A i j‖ ^ 2) (fun _ _ ↦ by positivity)
      (Finset.mem_univ j)).trans (Finset.single_le_sum (f := fun i ↦ ∑ j : Fin 3, ‖A i j‖ ^ 2)
        (fun _ _ ↦ by positivity) (Finset.mem_univ i))
  calc ‖A‖ ^ 2 ≤ Real.sqrt (∑ i : Fin 3, ∑ j : Fin 3, ‖A i j‖ ^ 2) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h 2
    _ = _ := Real.sq_sqrt hs

theorem summable_norm_strainCoeff_entry (u : FourierVelocity)
    (hu : Summable (fourierMoment 1 u)) (i j : Fin 3) :
    Summable (fun q ↦ ‖strainCoeff u q i j‖) :=
  (summable_norm_strainCoeff u hu).of_nonneg_of_le (fun _ ↦ norm_nonneg _)
    (fun q ↦ Matrix.norm_entry_le_entrywise_sup_norm (strainCoeff u q))

/-- Each entry of the actual strain matrix is the scalar Fourier series of the
corresponding strain coefficients. -/
theorem strain_entry_eq (u : FourierVelocity) (hu : Summable (fourierMoment 1 u)) (x : T3)
    (i j : Fin 3) :
    PancakeLocalStrainEquation.spatialStrain (fullFourierField id u) x i j =
      fullFourierField id (fun q ↦ strainCoeff u q i j) x := by
  have h := (Pi.hasSum.mp ((Pi.hasSum.mp (hasSum_strain_matrix u hu x)) i)) j
  have h' : HasSum (fun k ↦ UnitAddTorus.mFourier k x • strainCoeff u k i j)
      (PancakeLocalStrainEquation.spatialStrain (fullFourierField id u) x i j) := by
    simpa only [Pi.smul_apply, Matrix.smul_apply] using h
  rw [fullFourierField_apply id _ (summable_norm_strainCoeff_entry u hu i j)]
  exact h'.tsum_eq.symm

/-- Parseval for the strain entries: the strain energy is at most nine times
the vorticity energy. -/
theorem sum_integral_strainEntry_sq_le (u : FourierVelocity) (hu : Summable (fourierMoment 1 u))
    (hr : ∀ k, u (-k) = coefficientConjugate (u k)) (hd : ∀ k, modeDot k (u k) = 0) :
    ∑ i : Fin 3, ∑ j : Fin 3, ∫ x : T3, ‖fullFourierField id (fun q ↦ strainCoeff u q i j) x‖ ^ 2 ≤
      9 * meanEnstrophy u := by
  have hsum : HasSum (fun q ↦ ∑ i : Fin 3, ∑ j : Fin 3, ‖strainCoeff u q i j‖ ^ 2)
      (∑ i : Fin 3, ∑ j : Fin 3,
        ∫ x : T3, ‖fullFourierField id (fun q ↦ strainCoeff u q i j) x‖ ^ 2) :=
    hasSum_sum fun i _ ↦ hasSum_sum fun j _ ↦
      hasSum_norm_scalarFullFourierField_sq _ (summable_norm_strainCoeff_entry u hu i j)
  have hcurl := hasSum_coefficientEnergy (fourierCurl u)
    (FullVorticityFourierCoefficients.summable_norm_fourierCurl u hu)
  have hZ : meanEnstrophy u = ∑' q, coefficientEnergy (fourierCurl u q) := by
    rw [meanEnstrophy_eq, integral_norm_fullVorticity_sq_eq u hu hr,
      kineticEnergy_eq_tsum_coefficientEnergy]
  rw [hZ, ← hsum.tsum_eq, ← tsum_mul_left]
  refine hsum.summable.tsum_le_tsum (fun q ↦ ?_) (hcurl.summable.mul_left 9)
  have hentry : ∑ i : Fin 3, ∑ j : Fin 3, ‖strainCoeff u q i j‖ ^ 2 ≤
      9 * ‖strainCoeff u q‖ ^ 2 := by
    have h (i j : Fin 3) : ‖strainCoeff u q i j‖ ^ 2 ≤ ‖strainCoeff u q‖ ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) (Matrix.norm_entry_le_entrywise_sup_norm _) 2
    calc ∑ i : Fin 3, ∑ j : Fin 3, ‖strainCoeff u q i j‖ ^ 2
        ≤ ∑ _i : Fin 3, ∑ _j : Fin 3, ‖strainCoeff u q‖ ^ 2 :=
          Finset.sum_le_sum fun i _ ↦ Finset.sum_le_sum fun j _ ↦ h i j
      _ = 9 * ‖strainCoeff u q‖ ^ 2 := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          ring
  have hcoef : ‖strainCoeff u q‖ ^ 2 ≤ coefficientEnergy (fourierCurl u q) := by
    rw [fourierCurl_energy q u (hd q), ← norm_coefficientVec_sq]
    have h := norm_strainCoeff_le u q
    rw [PancakeIncomingLowSourceEnergy.norm_derivativePhase] at h
    calc ‖strainCoeff u q‖ ^ 2
        ≤ (2 * Real.pi * ‖frequencyVec q‖ * ‖coefficientVec (u q)‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) h 2
      _ = _ := by ring
  linarith

/-- **The stretching bound.** If the vorticity is bounded by `M`, the signed
stretching is at most `45 M ∫ |ω|²`. -/
theorem stretching_le_of_norm_le (u : FourierVelocity) (hu : Summable (fourierMoment 1 u))
    (hr : ∀ k, u (-k) = coefficientConjugate (u k)) (hd : ∀ k, modeDot k (u k) = 0)
    {M : ℝ} (hM0 : 0 ≤ M) (hM : ∀ x, ‖fullVorticity u x‖ ≤ M) :
    stretching u ≤ 45 * M * meanEnstrophy u := by
  let a : Fin 3 → Fin 3 → T3 → ℝ := fun i j x ↦
    ‖fullFourierField id (fun q ↦ strainCoeff u q i j) x‖
  have hpt : ∀ x, stretchingDensity u x ≤
      9 * M / 2 * (‖fullVorticity u x‖ ^ 2 + ∑ i : Fin 3, ∑ j : Fin 3, a i j x ^ 2) := by
    intro x
    set w := fullVorticity u x
    set A := PancakeLocalStrainEquation.spatialStrain (fullFourierField id u) x
    have h1 : stretchingDensity u x ≤ 9 * ‖A‖ * ‖w‖ ^ 2 := by
      have hS : ‖fullStrainOperator u x‖ ≤ 9 * ‖A‖ := norm_realMatrixOperator_le A
      calc stretchingDensity u x ≤ ‖w‖ * ‖fullStrainOperator u x w‖ := real_inner_le_norm _ _
        _ ≤ ‖w‖ * (‖fullStrainOperator u x‖ * ‖w‖) :=
          mul_le_mul_of_nonneg_left (ContinuousLinearMap.le_opNorm _ _) (norm_nonneg _)
        _ ≤ ‖w‖ * (9 * ‖A‖ * ‖w‖) := by gcongr
        _ = 9 * ‖A‖ * ‖w‖ ^ 2 := by ring
    have h2 : ‖A‖ ^ 2 ≤ ∑ i : Fin 3, ∑ j : Fin 3, a i j x ^ 2 := by
      have h := norm_sq_le_sum_entries A
      simpa only [a, A, strain_entry_eq u hu x] using h
    have hw : ‖w‖ ≤ M := hM x
    nlinarith [mul_nonneg (mul_nonneg (norm_nonneg A) (norm_nonneg w)) (sub_nonneg.mpr hw),
      mul_nonneg hM0 (sq_nonneg (‖A‖ - ‖w‖)), mul_nonneg hM0 (sub_nonneg.mpr h2)]
  have hia (i j : Fin 3) : Integrable (fun x ↦ a i j x ^ 2) :=
    ((fullFourierField id (fun q ↦ strainCoeff u q i j)).continuous.norm.pow 2).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hiw : Integrable (fun x : T3 ↦ ‖fullVorticity u x‖ ^ 2) :=
    ((continuous_fullVorticity u hu).norm.pow 2).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hiS : Integrable (stretchingDensity u) :=
    (continuous_stretchingDensity u hu).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hiA : Integrable (fun x ↦ ∑ i : Fin 3, ∑ j : Fin 3, a i j x ^ 2) :=
    integrable_finsetSum _ fun i _ ↦ integrable_finsetSum _ fun j _ ↦ hia i j
  have hA : (∫ x : T3, ∑ i : Fin 3, ∑ j : Fin 3, a i j x ^ 2) =
      ∑ i : Fin 3, ∑ j : Fin 3, ∫ x : T3, a i j x ^ 2 := by
    rw [integral_finsetSum _ fun i _ ↦ integrable_finsetSum _ fun j _ ↦ hia i j]
    exact Finset.sum_congr rfl fun i _ ↦ integral_finsetSum _ fun j _ ↦ hia i j
  have hmono := integral_mono hiS ((hiw.add hiA).const_mul (9 * M / 2)) hpt
  simp only [Pi.add_apply] at hmono
  rw [integral_const_mul, integral_add hiw hiA, hA] at hmono
  have hE := sum_integral_strainEntry_sq_le u hu hr hd
  have hZ : (∫ x : T3, ‖fullVorticity u x‖ ^ 2) = meanEnstrophy u := rfl
  rw [hZ] at hmono
  have hZ0 := meanEnstrophy_nonneg u
  change stretching u ≤ 9 * M / 2 * (meanEnstrophy u + _) at hmono
  nlinarith [mul_le_mul_of_nonneg_left hE (by positivity : (0 : ℝ) ≤ 9 * M / 2)]

end Strain

section Gronwall

/-- Grönwall's inequality in integral form with a continuous nonnegative
coefficient. -/
theorem le_mul_exp_of_le_add_integral {Z M : ℝ → ℝ} {t Z₀ κ : ℝ} (ht : 0 ≤ t) (hκ : 0 ≤ κ)
    (hZ : ContinuousOn Z (Icc 0 t)) (hM : ContinuousOn M (Icc 0 t))
    (hM0 : ∀ s ∈ Icc (0 : ℝ) t, 0 ≤ M s)
    (h : ∀ s ∈ Icc (0 : ℝ) t, Z s ≤ Z₀ + κ * ∫ τ in (0 : ℝ)..s, M τ * Z τ) :
    Z t ≤ Z₀ * Real.exp (κ * ∫ τ in (0 : ℝ)..t, M τ) := by
  set Φ : ℝ → ℝ := fun s ↦ Z₀ + κ * ∫ τ in (0 : ℝ)..s, M τ * Z τ with hΦ
  have hMZ : ContinuousOn (fun τ ↦ M τ * Z τ) (Icc 0 t) := hM.mul hZ
  have hint : IntegrableOn (fun τ ↦ M τ * Z τ) (uIcc 0 t) := by
    rw [uIcc_of_le ht]
    exact hMZ.integrableOn_Icc
  have hprim : ContinuousOn (fun s ↦ ∫ τ in (0 : ℝ)..s, M τ * Z τ) (Icc 0 t) := by
    have hc := intervalIntegral.continuousOn_primitive_interval hint
    rwa [uIcc_of_le ht] at hc
  have hΦc : ContinuousOn Φ (Icc 0 t) := continuousOn_const.add (hprim.const_smul κ)
  have hder : ∀ s ∈ Ioo (0 : ℝ) t,
      HasDerivWithinAt Φ (κ * (M s * Z s)) (Icc 0 t) s := by
    intro s hs
    have hsub : Icc (0 : ℝ) s ⊆ Icc 0 t := Icc_subset_Icc le_rfl hs.2.le
    have hi : IntervalIntegrable (fun τ ↦ M τ * Z τ) volume 0 s :=
      (hMZ.mono hsub).intervalIntegrable_of_Icc hs.1.le
    have hm : StronglyMeasurableAtFilter (fun τ ↦ M τ * Z τ) (nhds s) :=
      (hMZ.mono Ioo_subset_Icc_self).stronglyMeasurableAtFilter isOpen_Ioo s hs
    have hc : ContinuousAt (fun τ ↦ M τ * Z τ) s :=
      hMZ.continuousAt (Icc_mem_nhds hs.1 hs.2)
    exact (((intervalIntegral.integral_hasDerivAt_right hi hm hc).const_mul κ).const_add
      Z₀).hasDerivWithinAt
  have hbound : ∀ s ∈ Ioo (0 : ℝ) t, κ * (M s * Z s) ≤ κ * M s * Φ s := by
    intro s hs
    have hs' : s ∈ Icc (0 : ℝ) t := Ioo_subset_Icc_self hs
    have hκM : 0 ≤ κ * M s := mul_nonneg hκ (hM0 s hs')
    have hZΦ : Z s ≤ Φ s := h s hs'
    nlinarith
  have hG := Mettapedia.Analysis.ODE.le_initial_mul_exp_integral_of_deriv_le_mul hΦc
    (hM.const_smul κ) hder hbound t ⟨ht, le_rfl⟩
  have hΦ0 : Φ 0 = Z₀ := by simp only [Φ, intervalIntegral.integral_same, mul_zero, add_zero]
  have hint' : (∫ τ in (0 : ℝ)..t, (κ • M) τ) = κ * ∫ τ in (0 : ℝ)..t, M τ := by
    simp only [Pi.smul_apply, smul_eq_mul, intervalIntegral.integral_const_mul]
  rw [hΦ0, hint'] at hG
  exact (h t ⟨ht, le_rfl⟩).trans hG

end Gronwall

section Continuation

/-- A half-open solution restricts to a closed-interval local solution on
every shorter interval where its Sobolev energy is bounded. -/
def restrictLocal {nu : ℝ} {u₀ : FourierVelocity} {T : ℝ} (c : SolutionOn nu u₀ T) {S B : ℝ}
    (hST : S < T)
    (hB : ∀ t ∈ Icc (0 : ℝ) S, ∀ F : Finset Wavevector, sobolevEnergy F (c.coefficients t) ≤ B) :
    LocalInfiniteVelocitySolution nu u₀ S B where
  coefficients := c.coefficients
  continuous := c.continuous
  initial := c.initial
  reality := c.reality
  transverse := c.transverse
  zero := c.zero
  sobolev_bound := hB
  equation := fun t ht ↦ c.equation t ⟨ht.1, ht.2.trans hST⟩

theorem velocityEnergy_le_of_order_le {m n : ℕ} (hmn : m ≤ n) (u : FourierVelocity)
    (F : Finset Wavevector) : velocityEnergy m F u ≤ velocityEnergy n F u := by
  rw [velocityEnergy_eq, velocityEnergy_eq]
  refine Finset.sum_le_sum fun k _ ↦ ?_
  have hE : 0 ≤ coefficientEnergy (u k) := by
    rw [← norm_coefficientVec_sq]
    positivity
  have hw : orderWeight m k ^ 2 ≤ orderWeight n k ^ 2 := by
    unfold orderWeight
    rw [← pow_mul, ← pow_mul]
    exact pow_le_pow_right₀ (by linarith [norm_nonneg (frequencyVec k)]) (by omega)
  exact mul_le_mul_of_nonneg_right hw hE

/-- **Enstrophy growth along a tame solution.** For order `m ≥ 7`, the vorticity
energy at every time is at most its initial value times the exponential of
`90` times the integrated vorticity supremum. -/
theorem meanEnstrophy_le_of_tame (m : ℕ) (hm : 7 ≤ m) {nu : ℝ} (hnu : 0 ≤ nu)
    {u₀ : FourierVelocity} {T : ℝ} (c : TameSolutionOn nu m u₀ T) (τ : ℝ)
    (hτ : τ ∈ Ico (0 : ℝ) T) :
    meanEnstrophy (c.coefficients τ) ≤
      meanEnstrophy u₀ * Real.exp (90 * ∫ t in (0 : ℝ)..τ, vorticitySup (c.coefficients t)) := by
  set S := (τ + T) / 2 with hSdef
  have hτS : τ < S := by linarith [hτ.2]
  have hST : S < T := by linarith [hτ.2]
  have hS0 : 0 < S := lt_of_le_of_lt hτ.1 hτS
  obtain ⟨B, hB⟩ := c.sobolev_local S hST
  obtain ⟨E, hE⟩ := c.order_local S hST
  let s : LocalInfiniteVelocitySolution nu u₀ S B := restrictLocal c.toSolutionOn hST hB
  have h7 : ∀ t ∈ Icc (0 : ℝ) S, ∀ F : Finset Wavevector,
      velocityEnergy (3 + 4) F (s.coefficients t) ≤ E :=
    fun t ht F ↦ (velocityEnergy_le_of_order_le (by omega) _ F).trans (hE t ht F)
  let g : Wavevector → ℝ := fun k ↦ Real.sqrt E * latticeDecayWeight k
  have hg : ∀ k, 0 ≤ g k := fun k ↦ mul_nonneg (Real.sqrt_nonneg E) (latticeDecayWeight_pos k).le
  have hSum : Summable g := summable_latticeDecayWeight.mul_left _
  have hu3 : ∀ t ∈ Icc (0 : ℝ) S, ∀ k, fourierMoment 3 (s.coefficients t) k ≤ g k :=
    fun t ht k ↦ orderMoment_le_latticeEnvelope 3 _ E (h7 t ht) k
  have hu2 : ∀ t ∈ Icc (0 : ℝ) S, ∀ k, fourierMoment 2 (s.coefficients t) k ≤ g k :=
    fun t ht k ↦ (fourierMoment_mono _ (by omega : 2 ≤ 3) k).trans (hu3 t ht k)
  have hu1 : ∀ t ∈ Icc (0 : ℝ) S, Summable (fourierMoment 1 (s.coefficients t)) :=
    fun t ht ↦ hSum.of_nonneg_of_le (fourierMoment_nonneg 1 _)
      (fun k ↦ (fourierMoment_mono _ (by omega : 1 ≤ 3) k).trans (hu3 t ht k))
  have hsubτ : Icc (0 : ℝ) τ ⊆ Icc 0 S := Icc_subset_Icc le_rfl hτS.le
  have hZc := continuousOn_meanEnstrophy s g hSum hu3
  have hMc := continuousOn_vorticitySup s g hSum hu2
  have hineq : ∀ t ∈ Icc (0 : ℝ) τ, meanEnstrophy (s.coefficients t) ≤ meanEnstrophy u₀ +
      90 * ∫ r in (0 : ℝ)..t, vorticitySup (s.coefficients r) * meanEnstrophy (s.coefficients r) := by
    intro t ht
    have htS : t ∈ Icc (0 : ℝ) S := hsubτ ht
    have hid := enstrophy_identity s g hg hSum hu3 hS0 t htS
    have hsub : Icc (0 : ℝ) t ⊆ Icc 0 S := Icc_subset_Icc le_rfl htS.2
    have hP : 0 ≤ nu * ∫ r in (0 : ℝ)..t, palinstrophy (s.coefficients r) :=
      mul_nonneg hnu (intervalIntegral.integral_nonneg ht.1 fun r _ ↦ palinstrophy_nonneg _)
    have hstr : (∫ r in (0 : ℝ)..t, stretching (s.coefficients r)) ≤
        ∫ r in (0 : ℝ)..t, 45 * (vorticitySup (s.coefficients r) * meanEnstrophy (s.coefficients r)) := by
      apply intervalIntegral.integral_mono_on ht.1
      · exact ((continuousOn_stretching s g hSum hu3).mono hsub).intervalIntegrable_of_Icc ht.1
      · exact (((hMc.mul hZc).mono hsub).const_smul (45 : ℝ)).intervalIntegrable_of_Icc ht.1
      · intro r hr
        have hrS := hsub hr
        have h := stretching_le_of_norm_le (s.coefficients r) (hu1 r hrS) (s.reality r)
          (s.transverse r) (vorticitySup_nonneg _)
          (norm_fullVorticity_le_vorticitySup _ (hu1 r hrS))
        linarith
    rw [intervalIntegral.integral_const_mul] at hstr
    linarith
  have hG := le_mul_exp_of_le_add_integral hτ.1 (by norm_num) (hZc.mono hsubτ) (hMc.mono hsubτ)
    (fun t _ ↦ vorticitySup_nonneg _) hineq
  exact hG

/-- **Global existence under a vorticity-supremum bound (Beale–Kato–Majda
form).** For order `m ≥ 7`, if on every finite horizon the time integral of
the vorticity supremum of every tame solution from `u₀` is bounded by a common
constant, tame solutions exist on every interval `[0, H)`. -/
theorem exists_tameSolutionOn_of_vorticitySup (m : ℕ) (hm : 7 ≤ m) {nu : ℝ} (hnu : 0 < nu)
    (u₀ : FourierVelocity) (hr : ∀ q, u₀ (-q) = coefficientConjugate (u₀ q))
    (hd : ∀ q, modeDot q (u₀ q) = 0) (hz : u₀ 0 = 0) {E₀ : ℝ} (hE₀0 : 0 ≤ E₀)
    (hE₀ : ∀ F, velocityEnergy m F u₀ ≤ E₀)
    (hsup : ∀ H, 0 < H → ∃ A, ∀ T, T ≤ H → ∀ c : TameSolutionOn nu m u₀ T,
      ∀ τ ∈ Ico (0 : ℝ) T, ∫ t in (0 : ℝ)..τ, vorticitySup (c.coefficients t) ≤ A) :
    ∀ H, 0 < H → Nonempty (TameSolutionOn nu m u₀ H) := by
  refine exists_tameSolutionOn_of_orderOne m (by omega) hnu u₀ hr hd hz hE₀0 hE₀ ?_
  intro H hH
  obtain ⟨A, hA⟩ := hsup H hH
  refine ⟨meanEnstrophy u₀ * Real.exp (90 * A) / Real.pi ^ 2, fun T hT c τ hτ F ↦ ?_⟩
  obtain ⟨B, hB⟩ := c.order_local τ hτ.2
  have hB5 : ∀ G : Finset Wavevector, velocityEnergy 5 G (c.coefficients τ) ≤ B :=
    fun G ↦ (velocityEnergy_le_of_order_le (by omega) _ G).trans (hB τ ⟨hτ.1, le_rfl⟩ G)
  have hZ := meanEnstrophy_le_of_tame m hm hnu.le c τ hτ
  have hexp : Real.exp (90 * ∫ t in (0 : ℝ)..τ, vorticitySup (c.coefficients t)) ≤
      Real.exp (90 * A) :=
    Real.exp_le_exp.mpr (by linarith [hA T hT c τ hτ])
  have hZ' : meanEnstrophy (c.coefficients τ) ≤ meanEnstrophy u₀ * Real.exp (90 * A) :=
    hZ.trans (mul_le_mul_of_nonneg_left hexp (meanEnstrophy_nonneg _))
  calc velocityEnergy 1 F (c.coefficients τ)
      ≤ (∫ x : T3, ‖fullVorticity (c.coefficients τ) x‖ ^ 2) / Real.pi ^ 2 :=
        velocityEnergy_one_le _ (summable_fourierMoment_one _ hB5) (c.reality τ)
          (c.transverse τ) (c.zero τ) F
    _ ≤ _ := div_le_div_of_nonneg_right hZ' (by positivity)

end Continuation

end Mettapedia.FluidDynamics.NavierStokes.FourierVorticitySupContinuation
