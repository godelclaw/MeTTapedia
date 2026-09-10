import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalKineticEnergy
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeLocalPressureContinuity

/-!
# Initial-data budgets for the actual low-output pressure and feedback

The pressure uses the complete infinite convection, including interactions
with two unresolved inputs. Only its output set is finite. Its Hessian
cost times full enstrophy is integrable and paid by the energy-squared
identity of the actual local solution. The output-cutoff weight remains
explicit; this is not an estimate uniform over an expanding output set.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.LocalLowFrequencyBudget

open scoped BigOperators
open MeasureTheory
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeFrequencyProjectorCommutator
open PancakePeriodicVorticityEquation PancakeGalerkinKineticEnergy PancakeCurlOutputTail
open PancakeInfinitePressureCoefficients PancakeLocalPressureContinuity
open PancakeIndexedFourierMoments PancakeLocalInfiniteVelocity
open PancakeInfiniteFourierDerivative
open InfiniteConvectionEnergy LocalKineticEnergy InfiniteFilteredEquation
open PancakeConcreteSmoothCellCutoff
open PancakeViscousMisalignmentAbsorption PancakeIncomingLowSourceEnergy
open InfiniteKineticCancellation

local notation "C3" => EuclideanSpace ℂ (Fin 3)
local notation "T3" => UnitAddTorus (Fin 3)

/-- The Hessian coefficient of the pressure of the full velocity. -/
def pressureHessianOperator (u : FourierVelocity) (q : Wavevector) : C3 →L[ℂ] C3 :=
  (unitTorusDerivativePhase ^ 2 * infinitePressureCoeff u q) •
    InnerProductSpace.rankOne ℂ (frequencyVec q) (frequencyVec q)

/-- The operator acts by the actual mixed second-derivative coefficients. -/
theorem pressureHessianOperator_apply (u : FourierVelocity) (q : Wavevector)
    (v : VelocityCoefficient) (i : Fin 3) :
    pressureHessianOperator u q (coefficientVec v) i =
      ∑ j : Fin 3, indexedDerivativeCoeff id j
        (indexedDerivativeCoeff id i (infinitePressureCoeff u)) q * v j := by
  simp only [pressureHessianOperator, smul_apply, InnerProductSpace.rankOne_apply,
    inner_frequencyVec]
  change (unitTorusDerivativePhase ^ 2 * infinitePressureCoeff u q) *
    (modeDot q v * (q i : ℂ)) = _
  simp only [indexedDerivativeCoeff, id_eq, smul_eq_mul, modeDot,
    Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem norm_pressureHessianOperator (u : FourierVelocity) (q : Wavevector) :
    ‖pressureHessianOperator u q‖ =
      (2 * Real.pi) ^ 2 * ‖frequencyVec q‖ ^ 2 * ‖infinitePressureCoeff u q‖ := by
  simp only [pressureHessianOperator, norm_smul, norm_mul, norm_pow,
    PancakeIncomingLowSourceEnergy.norm_derivativePhase, InnerProductSpace.norm_rankOne]
  ring

theorem norm_pressureHessianOperator_le_kineticEnergy (u : FourierVelocity)
    (hu : Summable (fun q ↦ ‖coefficientVec (u q)‖ ^ 2)) (q : Wavevector) :
    ‖pressureHessianOperator u q‖ ≤
      (2 * Real.pi) ^ 2 * ‖frequencyVec q‖ ^ 2 * kineticEnergy u := by
  rw [norm_pressureHessianOperator]
  exact mul_le_mul_of_nonneg_left (norm_infinitePressureCoeff_le_kineticEnergy u hu q)
    (by positivity)

def pressureHessianAmplitude (outputs : Finset Wavevector) (u : FourierVelocity) : ℝ :=
  ∑ q ∈ outputs, ‖pressureHessianOperator u q‖

def pressureHessianField (outputs : Finset Wavevector) (u : FourierVelocity)
    (x : T3) : C3 →L[ℂ] C3 :=
  ∑ q ∈ outputs, UnitAddTorus.mFourier q x • pressureHessianOperator u q

theorem norm_pressureHessianField_le_amplitude (outputs : Finset Wavevector)
    (u : FourierVelocity) (x : T3) :
    ‖pressureHessianField outputs u x‖ ≤ pressureHessianAmplitude outputs u := by
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro q _
  rw [norm_smul, norm_mFourier_apply, one_mul]

theorem pressureHessianAmplitude_le_kineticEnergy (outputs : Finset Wavevector)
    (u : FourierVelocity) (hu : Summable (fun q ↦ ‖coefficientVec (u q)‖ ^ 2)) :
    pressureHessianAmplitude outputs u ≤
      PancakeLowPressureBudget.pressureCutoffWeight outputs * kineticEnergy u := by
  calc
    _ ≤ ∑ q ∈ outputs, (2 * Real.pi) ^ 2 * ‖frequencyVec q‖ ^ 2 * kineticEnergy u :=
      Finset.sum_le_sum (fun q _ ↦ norm_pressureHessianOperator_le_kineticEnergy u hu q)
    _ = _ := by
      simp only [PancakeLowPressureBudget.pressureCutoffWeight, Finset.mul_sum, Finset.sum_mul]

theorem norm_pressureHessianField_le_kineticEnergy (outputs : Finset Wavevector)
    (u : FourierVelocity) (hu : Summable (fun q ↦ ‖coefficientVec (u q)‖ ^ 2)) (x : T3) :
    ‖pressureHessianField outputs u x‖ ≤
      PancakeLowPressureBudget.pressureCutoffWeight outputs * kineticEnergy u :=
  (norm_pressureHessianField_le_amplitude outputs u x).trans
    (pressureHessianAmplitude_le_kineticEnergy outputs u hu)

theorem continuousOn_pressureHessianAmplitude {nu T B : ℝ} {u₀ : FourierVelocity}
    (s : LocalInfiniteVelocitySolution nu u₀ T B) (hB : 0 ≤ B) (outputs : Finset Wavevector) :
    ContinuousOn (fun t ↦ pressureHessianAmplitude outputs (s.coefficients t))
      (Set.Icc (0 : ℝ) T) := by
  unfold pressureHessianAmplitude
  apply continuousOn_finsetSum
  intro q _
  simp only [norm_pressureHessianOperator]
  exact continuousOn_const.mul
    (continuousOn_iff_continuous_restrict.mpr (continuous_infinitePressureCoeff s hB q)).norm

/-- A sufficient pressure-anisotropy cost, using the full receiver enstrophy. -/
def lowPressureCost (outputs : Finset Wavevector) (u : FourierVelocity) : ℝ :=
  2 * pressureHessianAmplitude outputs u * kineticEnergy (fourierCurl u)

theorem lowPressureCost_le (outputs : Finset Wavevector) (u : FourierVelocity)
    (hu : Summable (fun q ↦ ‖coefficientVec (u q)‖ ^ 2)) :
    lowPressureCost outputs u ≤ (2 * PancakeLowPressureBudget.pressureCutoffWeight outputs) *
      (kineticEnergy u * kineticEnergy (fourierCurl u)) := by
  have h := mul_le_mul_of_nonneg_right
    (pressureHessianAmplitude_le_kineticEnergy outputs u hu) (kineticEnergy_nonneg (fourierCurl u))
  dsimp only [lowPressureCost]
  nlinarith

/-- The actual low-pressure cost has an initial-data-only time integral.
No pressure estimate or enstrophy budget is assumed. -/
theorem lowPressureCost_integral_le_initial {nu T B : ℝ} {u₀ : FourierVelocity}
    (s : LocalInfiniteVelocitySolution nu u₀ T B) (hnu : 0 < nu) (hB : 0 ≤ B)
    (g : Wavevector → ℝ) (hg : ∀ q, 0 ≤ g q) (hSum : Summable g)
    (hu : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ q, fourierMoment 2 (s.coefficients t) q ≤ g q)
    (outputs : Finset Wavevector) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) T) :
    (∫ τ in (0 : ℝ)..t, lowPressureCost outputs (s.coefficients τ)) ≤
      PancakeLowPressureBudget.pressureCutoffWeight outputs * kineticEnergy u₀ ^ 2 / (2 * nu) := by
  have hcont : ContinuousOn (fun τ ↦ lowPressureCost outputs (s.coefficients τ))
      (Set.Icc (0 : ℝ) T) := (continuousOn_const.mul
    (continuousOn_pressureHessianAmplitude s hB outputs)).mul
      (continuousOn_enstrophy s g hg hSum hu)
  have hi : IntervalIntegrable (fun τ ↦ lowPressureCost outputs (s.coefficients τ)) volume 0 t :=
    ContinuousOn.intervalIntegrable_of_Icc ht.1 (hcont.mono
      (fun _ hτ ↦ ⟨hτ.1, hτ.2.trans ht.2⟩))
  have h := integral_le_of_energy_enstrophy_majorant s hnu g hg hSum hu t ht
    (fun τ ↦ lowPressureCost outputs (s.coefficients τ))
    (2 * PancakeLowPressureBudget.pressureCutoffWeight outputs)
    (mul_nonneg (by norm_num) (PancakeLowPressureBudget.pressureCutoffWeight_nonneg outputs)) hi
    (fun τ hτ ↦ lowPressureCost_le outputs _
      (local_kineticEnergy s τ ⟨hτ.1, hτ.2.trans ht.2⟩).1)
  convert h using 1
  ring

/-- A spatially uniform retained-pressure bound, paid by initial energy. -/
theorem norm_local_pressureHessianField_le_initial {nu T B : ℝ} {u₀ : FourierVelocity}
    (s : LocalInfiniteVelocitySolution nu u₀ T B) (hnu : 0 ≤ nu)
    (g : Wavevector → ℝ) (hg : ∀ q, 0 ≤ g q) (hSum : Summable g)
    (hu : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ q, fourierMoment 2 (s.coefficients t) q ≤ g q)
    (outputs : Finset Wavevector) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) T) (x : T3) :
    ‖pressureHessianField outputs (s.coefficients t) x‖ ≤
      PancakeLowPressureBudget.pressureCutoffWeight outputs * kineticEnergy u₀ :=
  (norm_pressureHessianField_le_kineticEnergy outputs _ (local_kineticEnergy s t ht).1 x).trans
    (mul_le_mul_of_nonneg_left (energy_le_initial s hnu g hg hSum hu t ht)
      (PancakeLowPressureBudget.pressureCutoffWeight_nonneg outputs))

/-- The retained unresolved force is bounded by initial energy, not the
local Sobolev bound. The frequency cost is still present. -/
theorem norm_local_subgridForce_le_initial {nu T B : ℝ} {u₀ : FourierVelocity}
    (s : LocalInfiniteVelocitySolution nu u₀ T B) (hnu : 0 ≤ nu)
    (g : Wavevector → ℝ) (hg : ∀ q, 0 ≤ g q) (hSum : Summable g)
    (hu : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ q, fourierMoment 2 (s.coefficients t) q ≤ g q)
    (modes : Finset Wavevector) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) T) (x : T3) :
    ‖coefficientVec (finiteFourierReconstruction modes
      (subgridForce (sharpFilter modes) (s.coefficients t)) x)‖ ≤
      (2 * Real.pi) * (∑ q ∈ modes, ‖frequencyVec q‖) * kineticEnergy u₀ :=
  (norm_reconstructed_subgridForce_le_kineticEnergy modes _ (local_kineticEnergy s t ht).1 x).trans
    (mul_le_mul_of_nonneg_left (energy_le_initial s hnu g hg hSum hu t ht) (by positivity))

theorem fullEnergy_le_kineticEnergy (modes : Finset Wavevector) (u : FourierVelocity)
    (hu : Summable (fun q ↦ coefficientEnergy (u q))) :
    fullEnergy modes u ≤ kineticEnergy u := by
  rw [kineticEnergy_eq_tsum_coefficientEnergy]
  exact hu.sum_le_tsum modes (fun _ _ ↦ PancakeArbitraryDataBlocks.coefficientEnergy_nonneg _)

theorem velocityAmplitude_fourierCurl (sources : Finset Wavevector) (u : FourierVelocity)
    (hk : ∀ k ∈ sources, frequencyVec k ≠ 0) (hd : ∀ k, modeDot k (u k) = 0) :
    velocityAmplitude sources (fourierCurl u) = sourceAmplitude sources u := by
  apply Finset.sum_congr rfl
  intro k hkm
  rw [physicalVelocity, physicalBiotSavart_fourierCurl k u (hk k hkm) (hd k)]

/-- The existing incoming low-source cost, evaluated on the actual full
vorticity, is dominated independently of the finite receiver set. -/
theorem lowSourceCost_le_energy_enstrophy (nu : ℝ) (hnu : 0 < nu)
    (sources receivers : Finset Wavevector) (u : FourierVelocity)
    (hk : ∀ k ∈ sources, frequencyVec k ≠ 0) (hd : ∀ k, modeDot k (u k) = 0)
    (hu : Summable (fourierMoment 2 u)) :
    lowSourceCost nu sources receivers (fourierCurl u) (fourierCurl u) ≤
      (36 * (sources.card : ℝ) / nu) * (kineticEnergy u * kineticEnergy (fourierCurl u)) := by
  have h := lowSourceCost_le_kinetic nu hnu sources receivers (fourierCurl u) (fourierCurl u)
  rw [sourceKineticEnergy_fourierCurl sources u hk (fun k _ ↦ hd k)] at h
  have he := fullEnergy_le_kineticEnergy sources u
    (summable_coefficientEnergy u (summable_amplitude u (summable_firstMoment_of_second u hu)))
  have ho := fullEnergy_le_kineticEnergy receivers (fourierCurl u) (summable_curlEnergy u hu)
  have hC : 0 ≤ 36 * (sources.card : ℝ) / nu := by positivity
  calc
    _ ≤ (36 * (sources.card : ℝ) / nu * fullEnergy sources u) *
        fullEnergy receivers (fourierCurl u) := h
    _ ≤ (36 * (sources.card : ℝ) / nu * kineticEnergy u) * kineticEnergy (fourierCurl u) :=
      mul_le_mul (mul_le_mul_of_nonneg_left he hC) ho (fullEnergy_nonneg _ _)
        (mul_nonneg hC (kineticEnergy_nonneg u))
    _ = _ := by ring

theorem continuousOn_lowSourceCost {nu T B : ℝ} {u₀ : FourierVelocity}
    (s : LocalInfiniteVelocitySolution nu u₀ T B) (sources receivers : Finset Wavevector)
    (hk : ∀ k ∈ sources, frequencyVec k ≠ 0) :
    ContinuousOn (fun t ↦ lowSourceCost nu sources receivers
      (fourierCurl (s.coefficients t)) (fourierCurl (s.coefficients t))) (Set.Icc (0 : ℝ) T) := by
  have heq : (fun t ↦ lowSourceCost nu sources receivers
      (fourierCurl (s.coefficients t)) (fourierCurl (s.coefficients t))) =
      fun t ↦ 36 * sourceAmplitude sources (s.coefficients t) ^ 2 / nu *
        fullEnergy receivers (fourierCurl (s.coefficients t)) := by
    funext t
    rw [lowSourceCost, velocityAmplitude_fourierCurl sources _ hk (s.transverse t)]
  rw [heq]
  have hA : Continuous (fun t ↦ sourceAmplitude sources (s.coefficients t)) := by
    apply continuous_finsetSum
    intro q _
    exact ((PiLp.continuous_toLp 2 (fun _ : Fin 3 ↦ ℂ)).comp
      (continuous_pi (s.continuous q))).norm
  exact ((continuousOn_const.mul (hA.continuousOn.pow 2)).div_const nu).mul
    (continuousOn_fullEnergy receivers _ _ (fun q _ ↦
      continuousOn_fourierCurl_coefficient _ _ q (fun i ↦ (s.continuous q i).continuousOn)))

/-- The low-source cost is paid for the actual infinite solution, uniformly
over finite receiver sets. The fixed source count and viscosity cost remain. -/
theorem lowSourceCost_integral_le_initial {nu T B : ℝ} {u₀ : FourierVelocity}
    (s : LocalInfiniteVelocitySolution nu u₀ T B) (hnu : 0 < nu)
    (g : Wavevector → ℝ) (hg : ∀ q, 0 ≤ g q) (hSum : Summable g)
    (hu : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ q, fourierMoment 2 (s.coefficients t) q ≤ g q)
    (sources receivers : Finset Wavevector) (hk : ∀ k ∈ sources, frequencyVec k ≠ 0)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) T) :
    (∫ τ in (0 : ℝ)..t, lowSourceCost nu sources receivers
      (fourierCurl (s.coefficients τ)) (fourierCurl (s.coefficients τ))) ≤
        9 * (sources.card : ℝ) * kineticEnergy u₀ ^ 2 / nu ^ 2 := by
  have hi : IntervalIntegrable (fun τ ↦ lowSourceCost nu sources receivers
      (fourierCurl (s.coefficients τ)) (fourierCurl (s.coefficients τ))) volume 0 t :=
    ContinuousOn.intervalIntegrable_of_Icc ht.1
      ((continuousOn_lowSourceCost s sources receivers hk).mono
        (fun _ hτ ↦ ⟨hτ.1, hτ.2.trans ht.2⟩))
  have h := integral_le_of_energy_enstrophy_majorant s hnu g hg hSum hu t ht _
    (36 * (sources.card : ℝ) / nu) (by positivity) hi
    (fun τ hτ ↦ lowSourceCost_le_energy_enstrophy nu hnu sources receivers _ hk
      (s.transverse τ) (hSum.of_nonneg_of_le (fourierMoment_nonneg _ _)
        (hu τ ⟨hτ.1, hτ.2.trans ht.2⟩)))
  convert h using 1
  ring

end Mettapedia.FluidDynamics.NavierStokes.LocalLowFrequencyBudget
