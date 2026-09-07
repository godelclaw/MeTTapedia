import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeCompactMeanDerivative

/-!
# Zero mean of a periodic translation derivative

Haar invariance fixes the mean of every translated scalar field. Uniform
local Lipschitz control and AE differentiability justify differentiating
that identity. Applied to flux components, this is the weak periodic
divergence cancellation needed for transport.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PancakeHaarTransportRate

open scoped Topology NNReal
open MeasureTheory Filter
open PancakeCompactMeanDerivative PancakeFourierTranslationCurve PancakeFourierMaterialPaths
open PancakeFourierStrainGradient

local notation "T3" => UnitAddTorus (Fin 3)

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

def shiftRate (f : T3 → ℝ) (s : ℝ → T3) (x : T3) : ℝ :=
  deriv (fun h ↦ f (x + s h)) 0

theorem continuous_shiftFamily (f : T3 → ℝ) (s : ℝ → T3)
    (hf : Continuous f) (hs : Continuous s) :
    Continuous (fun z : ℝ × T3 ↦ f (z.2 + s z.1)) :=
  hf.comp (continuous_snd.add (hs.comp continuous_fst))

theorem measurable_shiftRate (f : T3 → ℝ) (s : ℝ → T3)
    (hf : Continuous f) (hs : Continuous s) : Measurable (shiftRate f s) :=
  measurable_parameterRate (fun h x ↦ f (x + s h)) (continuous_shiftFamily f s hf hs) 0

theorem integral_shiftRate_zero (f : T3 → ℝ) (s : ℝ → T3)
    (hf : Continuous f) (hs : Continuous s) (J : Set ℝ) (hJ : J ∈ 𝓝 (0 : ℝ)) (C : ℝ≥0)
    (hlip : ∀ x, LipschitzOnWith C (fun h ↦ f (x + s h)) J)
    (hd : ∀ᵐ x : T3, DifferentiableAt ℝ (fun h ↦ f (x + s h)) 0) :
    Integrable (shiftRate f s) ∧ (∫ x : T3, shiftRate f s x) = 0 := by
  obtain ⟨hi, hm⟩ := hasDerivAt_mean_of_uniform_lipschitz
    (fun h x ↦ f (x + s h)) (continuous_shiftFamily f s hf hs) 0 J hJ C hlip hd
  have he : (fun h ↦ ∫ x : T3, f (x + s h)) = (fun _ : ℝ ↦ ∫ x : T3, f x) := by
    funext h
    exact integral_add_right_eq_self f (s h)
  rw [he] at hm
  exact ⟨hi, hm.unique (hasDerivAt_const 0 _)⟩

theorem shiftRate_mul (f g : T3 → ℝ) (s : ℝ → T3) (x : T3) (hs0 : s 0 = 0)
    (hf : DifferentiableAt ℝ (fun h ↦ f (x + s h)) 0)
    (hg : DifferentiableAt ℝ (fun h ↦ g (x + s h)) 0) :
    shiftRate (fun y ↦ f y * g y) s x = shiftRate f s x * g x + f x * shiftRate g s x := by
  simpa only [shiftRate, hs0, add_zero] using (hf.hasDerivAt.fun_mul hg.hasDerivAt).deriv

theorem continuous_coordinateShift (j : Fin 3) : Continuous (coordinateShift j) := by
  apply continuous_pi
  intro i
  change Continuous (fun h : ℝ ↦ ((coordinateLine 0 j h i : ℝ) : UnitAddCircle))
  apply continuous_quot_mk.comp
  by_cases hij : i = j
  · simp only [coordinateLine, hij, ite_true, Pi.zero_apply, zero_add, mul_one]
    fun_prop
  · simp only [coordinateLine, hij, ite_false, Pi.zero_apply, zero_add, mul_zero]
    fun_prop

theorem coordinateShift_zero (j : Fin 3) : coordinateShift j 0 = 0 := by
  ext i
  by_cases hij : i = j <;> simp [coordinateShift, torusPoint, coordinateLine, hij]

end Mettapedia.FluidDynamics.NavierStokes.PancakeHaarTransportRate
