import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.StrainGradientEnergy
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.GaussianRootInputBudget
import Mettapedia.Analysis.SqrtEnergyAbsorption

/-!
# Adaptive pressure localization paid by actual vorticity-gradient energy

For real divergence-free data the absolute Fourier-moment cost is replaced
by spatial diffusion energy. The adaptive cover and all input-scale patch
families are constructed. Vorticity-supremum and geometric cutoff costs
remain explicit; no time-integrated nonlinear budget is asserted.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.GaussianRootDiffusionBudget

open MeasureTheory
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeBlockReality
open PancakeCurlOutputTail PancakeHigherDerivativeMoments PancakeFrequencyProjectorCommutator
open PancakeFourierStrainGradient PancakeFilteredStrainDynamics LocalSpatialVorticityJets
open LocalSquaredGapPressure LocalGaussianPressurePartition LocalLowDiffusionBudget
open UniformGaussianGradientBudget GaussianRootInputBudget GaussianSquaredRootTranslation
open AdaptiveGaussianLinePartition VorticityGradientEnergy StrainGradientEnergy

local notation "T3" => UnitAddTorus (Fin 3)
local notation "R3" => EuclideanSpace ℝ (Fin 3)

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

def energyMultiplier (gamma W A : ℝ) : ℝ :=
  4 * A / gamma ^ 2 + (72 + 1600 * A) * W ^ 2 / gamma ^ 4

theorem energyMultiplier_nonneg (gamma W A : ℝ) (hA : 0 ≤ A) :
    0 ≤ energyMultiplier gamma W A := by unfold energyMultiplier; positivity

/-- The explicit remainder after absorbing a scalar pairing against this
pressure norm. Identifying a signed dynamical term with such a pairing is
a separate obligation. -/
theorem input_bound_absorb (C N W L D R Y epsilon : ℝ)
    (hN : 0 < N) (hL : 0 ≤ L) (hD : 0 ≤ D) (hY : 0 ≤ Y) (hepsilon : 0 < epsilon)
    (hR : R ≤ (2 * C / N) * (W ^ 2 * Real.sqrt (6 * (L * D)))) :
    R * Y ≤ epsilon * D + 6 * C ^ 2 * L * W ^ 4 * Y ^ 2 / (epsilon * N ^ 2) := by
  let K := (2 * C / N) * W ^ 2 * Real.sqrt (6 * L) * Y
  have hK := Mettapedia.Analysis.SqrtEnergyAbsorption.mul_sqrt_le K D epsilon hD hepsilon
  have hsq := Real.sq_sqrt (show 0 ≤ 6 * L by positivity)
  calc
    _ ≤ ((2 * C / N) * (W ^ 2 * Real.sqrt (6 * (L * D)))) * Y :=
      mul_le_mul_of_nonneg_right hR hY
    _ = K * Real.sqrt D := by
      rw [show 6 * (L * D) = (6 * L) * D by ring, Real.sqrt_mul (by positivity : 0 ≤ 6 * L)]
      dsimp [K]
      ring
    _ ≤ _ := hK
    _ = _ := by
      congr 1
      dsimp [K]
      simp only [mul_pow, div_pow, hsq]
      field_simp
      ring

theorem integral_gradientDensity_le_energy (gamma W A : ℝ) (hA : 0 ≤ A)
    (chi : Wavevector → ℂ) (modes : Finset Wavevector) (hchi : ∀ q ∈ modes, ‖chi q‖ ≤ 1)
    (u : FourierVelocity) (hu : Summable (fourierMoment 2 u))
    (hr : ∀ q, u (-q) = coefficientConjugate (u q))
    (hd : ∀ q ∈ modes, modeDot q (u q) = 0) :
    (∫ x : T3, gradientDensity gamma W A chi modes u x) ≤
      energyMultiplier gamma W A * gradientEnergy u := by
  have hiF : Integrable (fun x : T3 ↦ ∑ j : Fin 3, ‖fullCurlGradient u j x‖ ^ 2) :=
    (continuous_finsetSum _ (fun j _ ↦
      (LocalSquaredGapGradient.continuous_fullCurlGradient u j).norm.pow 2)
      ).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hiS : Integrable (fun x : T3 ↦
      ∑ j : Fin 3, ‖strainGradient modes (filteredVelocity chi u) x j‖ ^ 2) :=
    (continuous_finsetSum _ (fun j _ ↦
      (FourierMatrixEnergy.continuous_operatorField modes
        (strainDerivativeCoeff j (filteredVelocity chi u))).norm.pow 2)
      ).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  simp only [gradientDensity]
  rw [integral_add (hiF.const_mul _) (hiS.const_mul _), integral_const_mul, integral_const_mul]
  calc
    _ ≤ (4 * A / gamma ^ 2) * gradientEnergy u +
        ((72 + 1600 * A) * W ^ 2 / gamma ^ 4) * gradientEnergy u :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left
        (integral_sum_strainGradient_sq_le chi modes hchi u hu hr hd) (by positivity))
    _ = _ := by unfold energyMultiplier; ring

/-- The full pressure-output norm is summed over high input scales with
no Fourier-moment cost in its bound. Reality and incompressibility are
actual coefficient conditions, not analytic-budget assumptions. -/
theorem exists_uniform_input_diffusion_budget :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : FourierVelocity, ∀ hu : Summable (fourierMoment 3 u),
      (∀ q, u (-q) = coefficientConjugate (u q)) → (∀ q, modeDot q (u q) = 0) →
      ∀ gamma : ℝ, 0 < gamma → ∀ rho : ℝ, 0 < rho →
      let w : C(T3, R3) := ⟨fullVorticity u, continuous_fullVorticity u
        (summable_fourierMoment_of_le u (by omega : 1 ≤ 3) hu)⟩
      ∃ M : ℕ, 0 < M ∧ ∀ N : ℝ, ∀ hN : 0 < N,
        ∀ chi : ℕ → Wavevector → ℂ, ∀ modes : ℕ → Finset Wavevector,
        (∀ j q, q ∈ modes j → ‖chi j q‖ ≤ 1) →
        ∃ centers : ℕ → Finset T3,
          (∀ j, (centers j).Nonempty ∧ (centers j).card ≤ M ∧
            let tau := temperature (centers j).card rho
            (∀ x, (∑ i : ↑(centers j), patch gamma (chi j) (modes j) u (centers j) tau i x ^ 2) =
              localWeight gamma (chi j) (modes j) u x) ∧
            (∀ x, (∑ i : ↑(centers j), patch gamma (chi j) (modes j) u (centers j) tau i x ^ 2 *
              SpectralTiltFreezing.lineDistanceSq (localDirection (chi j) (modes j) u x)
                (localDirection (chi j) (modes j) u i.1)) ≤ rho ^ 2)) ∧
          Summable (fun j : ℕ ↦ fullOutputNorm (inputScale N j) (inputScale_pos N hN j)
            gamma (chi j) (modes j) u (centers j) rho) ∧
          (∑' j : ℕ, fullOutputNorm (inputScale N j) (inputScale_pos N hN j)
            gamma (chi j) (modes j) u (centers j) rho) ≤
            (2 * C / N) * (‖w‖ ^ 2 * Real.sqrt (6 *
              (energyMultiplier gamma ‖w‖ (partitionMultiplier M gamma ‖w‖ rho) * gradientEnergy u))) ∧
          (∀ epsilon : ℝ, 0 < epsilon → ∀ Y : ℝ, 0 ≤ Y →
            (∑' j : ℕ, fullOutputNorm (inputScale N j) (inputScale_pos N hN j)
              gamma (chi j) (modes j) u (centers j) rho) * Y ≤
              epsilon * gradientEnergy u +
                6 * C ^ 2 * energyMultiplier gamma ‖w‖ (partitionMultiplier M gamma ‖w‖ rho) *
                  ‖w‖ ^ 4 * Y ^ 2 / (epsilon * N ^ 2)) := by
  obtain ⟨C, hC, hpressure⟩ := exists_uniform_input_operator_budget
  refine ⟨C, hC, ?_⟩
  intro u hu hr hd gamma hg rho hrho
  let w : C(T3, R3) := ⟨fullVorticity u, continuous_fullVorticity u
    (summable_fourierMoment_of_le u (by omega : 1 ≤ 3) hu)⟩
  have hu2 := summable_fourierMoment_of_le u (by omega : 2 ≤ 3) hu
  obtain ⟨M, hM, hgeometry⟩ := exists_uniform_root_gradient_budget gamma hg ‖w‖ rho hrho
  refine ⟨M, hM, ?_⟩
  intro N hN chi modes hchi
  choose centers hc hcard hT hTle hmass hline hiG hAE hG using
    (fun j : ℕ ↦ hgeometry (chi j) (modes j) u hu w.norm_coe_le_norm)
  let A := partitionMultiplier M gamma ‖w‖ rho
  let E := energyMultiplier gamma ‖w‖ A * gradientEnergy u
  have hE (j : ℕ) :
      (∫ x : T3, squaredRootGradientSquare gamma (chi j) (modes j) u (centers j)
        (temperature (centers j).card rho) x) ≤ E :=
    (hG j).trans (integral_gradientDensity_le_energy gamma ‖w‖ A
      (partitionMultiplier_nonneg M gamma ‖w‖ rho) (chi j) (modes j) (hchi j)
      u hu2 hr (fun q _ ↦ hd q))
  have hp := hpressure u hu2 gamma hg N hN chi modes centers hc rho E hE
  refine ⟨centers, fun j ↦ ⟨hc j, hcard j, hmass j, hline j⟩, hp.1, hp.2, ?_⟩
  intro epsilon hepsilon Y hY
  exact input_bound_absorb C N ‖w‖ (energyMultiplier gamma ‖w‖ A) (gradientEnergy u) _ Y epsilon
    hN (energyMultiplier_nonneg gamma ‖w‖ A (partitionMultiplier_nonneg M gamma ‖w‖ rho))
    (gradientEnergy_nonneg u) hY hepsilon hp.2

end Mettapedia.FluidDynamics.NavierStokes.GaussianRootDiffusionBudget
