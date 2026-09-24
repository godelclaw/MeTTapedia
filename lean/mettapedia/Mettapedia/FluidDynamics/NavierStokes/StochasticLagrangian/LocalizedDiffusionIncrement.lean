import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.DepletedLaplacianDiffusion
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.Calculus.Deriv.Slope

/-!
# Local gradient density in the alignment-depleted diffusion cost

The Lipschitz constant dominates normalized increments only for passage
to the limit. The final cost retains the actual spatial derivative norm
inside the integral, multiplied by the capped alignment weight.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.LocalizedDiffusionIncrement

open scoped Topology RealInnerProductSpace
open Filter MeasureTheory PancakeHaarDiffusionIncrement PancakeRegularizedMaterialRate
open PancakeWeakDiffusionLimit PancakeRegularizedDiffusion PancakeSpectralProjectorRegularity
open DepletedLaplacianDiffusion SpectralDiffusionWeight

local notation "R3" => EuclideanSpace ℝ (Fin 3)
local notation "T3" => UnitAddTorus (Fin 3)

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

def normalizedShiftCost (S : T3 → SymmetricStrain) (w : T3 → R3)
    (epsilon h : ℝ) (s x : T3) : ℝ :=
  (h ^ 2)⁻¹ * DepletedLaplacianDiffusion.shiftCost S w epsilon s x

theorem normalizedShiftCost_eq (S : T3 → SymmetricStrain) (w : T3 → R3)
    (epsilon h : ℝ) (s x : T3) :
    normalizedShiftCost S w epsilon h s x =
      ‖h⁻¹ • ((S (x + s)).1 - (S x).1)‖ ^ 2 * weight (S x) (w x) epsilon := by
  simp only [normalizedShiftCost, DepletedLaplacianDiffusion.shiftCost, norm_smul,
    Real.norm_eq_abs, mul_pow, sq_abs, inv_pow, mul_assoc]

theorem continuous_normalizedShiftCost (S : T3 → SymmetricStrain) (w : T3 → R3)
    (epsilon h : ℝ) (s : T3) (heps : 0 < epsilon) (hS : Continuous S) (hw : Continuous w) :
    Continuous (normalizedShiftCost S w epsilon h s) :=
  (DepletedLaplacianDiffusion.continuous_shiftCost S w epsilon heps s hS hw).const_mul _

theorem norm_normalizedShiftCost_le (S : T3 → SymmetricStrain) (w : T3 → R3)
    (epsilon L h : ℝ) (s x : T3) (heps : 0 < epsilon) (hL : 0 ≤ L) (hh : h ≠ 0)
    (hp : ‖(S (x + s)).1 - (S x).1‖ ≤ L * |h|) :
    ‖normalizedShiftCost S w epsilon h s x‖ ≤ L ^ 2 * weight (S x) (w x) epsilon := by
  have hn : 0 ≤ normalizedShiftCost S w epsilon h s x := by
    rw [normalizedShiftCost_eq]
    exact mul_nonneg (sq_nonneg _) (weight_nonneg _ _ epsilon heps)
  rw [Real.norm_of_nonneg hn]
  have hb := mul_le_mul_of_nonneg_left
    (DepletedLaplacianDiffusion.shiftCost_le S w epsilon L h s x heps hL hp)
    (inv_nonneg.mpr (sq_nonneg h))
  change normalizedShiftCost S w epsilon h s x ≤ _ at hb
  convert hb using 1
  field_simp

theorem tendsto_normalizedShiftCost (S : T3 → SymmetricStrain) (w : T3 → R3)
    (epsilon : ℝ) (shift : ℝ → T3) (x : T3) (A : R3 →L[ℝ] R3)
    (hzero : shift 0 = 0)
    (hA : HasDerivAt (fun h ↦ (S (x + shift h)).1) A 0) :
    Tendsto (fun h ↦ normalizedShiftCost S w epsilon h (shift h) x) (𝓝[≠] (0 : ℝ))
      (𝓝 (‖A‖ ^ 2 * weight (S x) (w x) epsilon)) := by
  have h := ((hA.tendsto_slope_zero.norm).pow 2).mul_const (weight (S x) (w x) epsilon)
  simpa only [zero_add, hzero, add_zero, normalizedShiftCost_eq] using h

theorem tendsto_integral_normalizedShiftCost (S : T3 → SymmetricStrain) (w : T3 → R3)
    (epsilon L : ℝ) (shift : ℝ → T3) (A : T3 → R3 →L[ℝ] R3)
    (heps : 0 < epsilon) (hL : 0 ≤ L) (hS : Continuous S) (hw : Continuous w)
    (hzero : shift 0 = 0)
    (hA : ∀ x, HasDerivAt (fun h ↦ (S (x + shift h)).1) (A x) 0)
    (hp : ∀ h ≠ 0, ∀ x, ‖(S (x + shift h)).1 - (S x).1‖ ≤ L * |h|) :
    Tendsto (fun h ↦ ∫ x : T3, normalizedShiftCost S w epsilon h (shift h) x) (𝓝[≠] (0 : ℝ))
      (𝓝 (∫ x : T3, ‖A x‖ ^ 2 * weight (S x) (w x) epsilon)) := by
  apply tendsto_integral_filter_of_dominated_convergence
    (fun x ↦ L ^ 2 * weight (S x) (w x) epsilon)
  · exact Eventually.of_forall (fun h ↦
      (continuous_normalizedShiftCost S w epsilon h (shift h) heps hS hw).measurable.aestronglyMeasurable)
  · filter_upwards [self_mem_nhdsWithin] with h hh
    exact Eventually.of_forall (fun x ↦ norm_normalizedShiftCost_le S w epsilon L h (shift h) x
      heps hL hh (hp h hh x))
  · exact ((continuous_weight S w epsilon heps hS hw).const_mul _).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  · exact Eventually.of_forall (fun x ↦ tendsto_normalizedShiftCost S w epsilon shift x (A x) hzero (hA x))

theorem integral_centralUpper_eq (S : T3 → SymmetricStrain) (w : T3 → R3)
    (delta epsilon h : ℝ) (s : T3) (heps : 0 < epsilon) (hS : Continuous S) (hw : Continuous w) :
    (∫ x : T3, centralUpper S w delta epsilon h s x) = (8 / delta) *
      ((∫ x : T3, normalizedShiftCost S w epsilon h s x) +
       (∫ x : T3, normalizedShiftCost S w epsilon h (-s) x)) := by
  have hEp : Integrable (shiftEnergy S w delta s) :=
    (continuous_shiftEnergy S w delta s hS hw).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hEm : Integrable (shiftEnergy S w delta (-s)) :=
    (continuous_shiftEnergy S w delta (-s) hS hw).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hCp : Integrable (DepletedLaplacianDiffusion.shiftCost S w epsilon s) :=
    (DepletedLaplacianDiffusion.continuous_shiftCost S w epsilon heps s hS hw).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hCm : Integrable (DepletedLaplacianDiffusion.shiftCost S w epsilon (-s)) :=
    (DepletedLaplacianDiffusion.continuous_shiftCost S w epsilon heps (-s) hS hw).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  unfold centralUpper normalizedShiftCost
  rw [integral_const_mul,
    integral_add (f := fun x ↦ shiftEnergy S w delta s x + shiftEnergy S w delta (-s) x)
      (g := fun x ↦ (8 / delta) * (DepletedLaplacianDiffusion.shiftCost S w epsilon s x +
        DepletedLaplacianDiffusion.shiftCost S w epsilon (-s) x))
      (hEp.add hEm) ((hCp.add hCm).const_mul (8 / delta)),
    integral_add hEp hEm, integral_const_mul, integral_add hCp hCm]
  simp only [integral_const_mul, integral_shiftEnergy_zero S w delta s hS hw,
    integral_shiftEnergy_zero S w delta (-s) hS hw]
  ring

end Mettapedia.FluidDynamics.NavierStokes.LocalizedDiffusionIncrement
