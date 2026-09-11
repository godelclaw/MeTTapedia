import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PressureHighInputLocalization
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.GaussianRootFixedOutputBudget

/-!
# The Gaussian localization budget for the complete high-input operator

The left-hand side is the actual localization of the infinite input sum,
not an abstract residual or an unevaluated sum of bandwise bounds. The
vorticity supremum and patch-gradient energy are explicit spatial costs.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.GaussianRootHighInputBudget

open MeasureTheory PeriodicFourierTriad PancakeCurlOutputTail PancakeHigherDerivativeMoments
open LocalLowDiffusionBudget LocalGaussianPressurePartition GaussianSquaredRootTranslation
open GaussianRootOperatorBudget GaussianRootFixedOutputBudget PressureHighInputLocalization
open PressureFixedOutputLocalization

local notation "R3" => EuclideanSpace ℝ (Fin 3)
local notation "C3" => EuclideanSpace ℂ (Fin 3)
local notation "T3" => UnitAddTorus (Fin 3)
local instance : CompleteSpace C3 := PiLp.completeSpace 2 (fun _ : Fin 3 ↦ ℂ)
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

theorem exists_uniform_root_budget :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℝ, ∀ hN : 0 < N, ∀ J : ℕ,
      ∀ gamma : ℝ, ∀ hg : 0 < gamma, ∀ chi : Wavevector → ℂ, ∀ modes : Finset Wavevector,
      ∀ u : FourierVelocity, ∀ hu : Summable (fourierMoment 2 u),
      ∀ centers : Finset T3, ∀ hc : centers.Nonempty, ∀ tau W : ℝ,
      (∀ x : T3, ‖fullVorticity u x‖ ≤ W) →
      let hu1 := summable_fourierMoment_of_le u (by omega : 1 ≤ 2) hu
      let w := complexVorticityField u hu1
      let c := complexRootPatch gamma hg chi modes u hu1 centers hc tau
      Real.sqrt (∫ x : T3, ∑ i : ↑centers,
        ‖tailLocalization N hN J (localDirection chi modes u i.1) w w (c i) (c i) x‖ ^ 2) ≤
        ((C / N) * (1 / 4 : ℝ) ^ J) * (W ^ 2 * Real.sqrt (6 *
          ∫ x : T3, squaredRootGradientSquare gamma chi modes u centers tau x)) := by
  obtain ⟨C, hC, hb⟩ := exists_uniform_tail_budget
  refine ⟨C, hC, ?_⟩
  intro N hN J gamma hg chi modes u hu centers hc tau W hW
  let hu1 := summable_fourierMoment_of_le u (by omega : 1 ≤ 2) hu
  let w := complexVorticityField u hu1
  let c := complexRootPatch gamma hg chi modes u hu1 centers hc tau
  obtain ⟨hs, ht⟩ := hb N hN gamma hg chi modes u hu centers hc tau W hW J
  have heq (j : ℕ) : Real.sqrt (∫ x : T3, ∑ i : ↑centers,
      ‖localization N hN (J + j) (localDirection chi modes u i.1) w w (c i) (c i) x‖ ^ 2) =
      sumActionNorm N hN (J + j) gamma chi modes u centers tau := by
    unfold sumActionNorm
    simp_rw [sumAction_eq N hN (J + j) gamma hg chi modes u hu1 centers hc tau]
    rfl
  have hs' : Summable (fun j : ℕ ↦ Real.sqrt (∫ x : T3, ∑ i : ↑centers,
      ‖localization N hN (J + j) (localDirection chi modes u i.1) w w (c i) (c i) x‖ ^ 2)) := by
    simpa only [heq] using hs
  have h := finite_tailLocalization_spatial_norm_le N hN J
    (fun i : ↑centers ↦ localDirection chi modes u i.1)
    (fun _ ↦ PancakeSpectralFiniteDifference.topVector_norm _) w w c c hs'
  simp only [heq] at h
  exact h.trans ht

end Mettapedia.FluidDynamics.NavierStokes.GaussianRootHighInputBudget
