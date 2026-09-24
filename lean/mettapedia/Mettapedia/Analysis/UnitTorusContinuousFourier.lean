import Mettapedia.Analysis.UnitTorusFourierEnergy
import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap
import Mathlib.Topology.Algebra.InfiniteSum.Module

/-!
# Continuous-field Fourier coefficient maps on the unit torus

Each coefficient is a continuous complex-linear map of norm at most one.
Consequently coefficient extraction commutes with Banach-space convergent
series, including vector-valued and product-indexed reconstructions.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.Analysis.UnitTorusContinuousFourier

open MeasureTheory UnitAddTorus

variable {d E : Type*} [Fintype d]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

omit [CompleteSpace E] in
theorem integrable_coefficient_integrand (q : d → ℤ) (f : C(UnitAddTorus d, E)) :
    Integrable (fun x : UnitAddTorus d ↦ mFourier (-q) x • f x) :=
  ((mFourier (-q)).continuous.smul f.continuous).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

def coefficientLinear (q : d → ℤ) : C(UnitAddTorus d, E) →ₗ[ℂ] E where
  toFun f := mFourierCoeff f q
  map_add' f g := by
    simp only [mFourierCoeff, ContinuousMap.add_apply, smul_add]
    exact integral_add (integrable_coefficient_integrand q f) (integrable_coefficient_integrand q g)
  map_smul' a f := by
    simp only [mFourierCoeff, ContinuousMap.smul_apply, smul_comm (mFourier (-q) _) a]
    exact integral_smul a _

omit [CompleteSpace E] in
theorem norm_coefficientLinear_le (q : d → ℤ) (f : C(UnitAddTorus d, E)) :
    ‖coefficientLinear q f‖ ≤ 1 * ‖f‖ := by
  change ‖∫ x : UnitAddTorus d, mFourier (-q) x • f x‖ ≤ 1 * ‖f‖
  have hbound (x : UnitAddTorus d) : ‖mFourier (-q) x • f x‖ ≤ ‖f‖ := by
    have h := (norm_smul_le (mFourier (-q) x) (f x)).trans
      (mul_le_mul ((mFourier (-q)).norm_coe_le_norm x) (f.norm_coe_le_norm x)
        (norm_nonneg _) (norm_nonneg _))
    simpa only [mFourier_norm, one_mul] using h
  have hi : Integrable (fun _ : UnitAddTorus d ↦ ‖f‖) volume := integrable_const _
  have h := norm_integral_le_of_norm_le hi
    (Filter.Eventually.of_forall hbound)
  simpa only [mFourier_norm, one_mul, integral_const, probReal_univ, one_smul] using h

def coefficientCLM (q : d → ℤ) : C(UnitAddTorus d, E) →L[ℂ] E :=
  (coefficientLinear q).mkContinuous 1 (norm_coefficientLinear_le q)

omit [CompleteSpace E] in
@[simp] theorem coefficientCLM_apply (q : d → ℤ) (f : C(UnitAddTorus d, E)) :
    coefficientCLM q f = mFourierCoeff f q := rfl

omit [CompleteSpace E] in
theorem norm_coefficientCLM_le (q : d → ℤ) : ‖coefficientCLM (E := E) q‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

theorem mFourierCoeff_monomial (q k : d → ℤ) (a : E) :
    mFourierCoeff (fun x : UnitAddTorus d ↦ mFourier k x • a) q =
      if q = k then a else 0 := by
  classical
  unfold mFourierCoeff
  simp_rw [smul_smul]
  rw [integral_smul_const]
  change mFourierCoeff (mFourier k) q • a = _
  rw [UnitTorusFourierEnergy.mFourierCoeff_character]
  split <;> simp_all

omit [CompleteSpace E] in
theorem hasSum_mFourierCoeff {ι : Type*} (f : ι → C(UnitAddTorus d, E))
    (hf : Summable f) (q : d → ℤ) :
    HasSum (fun i ↦ mFourierCoeff (f i) q)
      (mFourierCoeff (↑(∑' i, f i) : UnitAddTorus d → E) q) :=
  (coefficientCLM q).hasSum hf.hasSum

end Mettapedia.Analysis.UnitTorusContinuousFourier
