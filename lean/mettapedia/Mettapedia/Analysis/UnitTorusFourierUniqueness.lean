import Mettapedia.Analysis.UnitTorusContinuousFourier
import Mathlib.Analysis.Normed.Module.Dual

/-!
# Uniqueness and finite reconstruction for continuous torus fields

Scalar uniqueness follows from the complete Fourier basis in `L²` and
full support of Haar measure. Continuous linear functionals then give
uniqueness for Banach-valued fields. No pointwise convergence theorem for
an arbitrary Fourier series is used.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.Analysis.UnitTorusFourierUniqueness

open MeasureTheory UnitAddTorus UnitTorusContinuousFourier

variable {d E F : Type*} [Fintype d]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

theorem scalar_eq_of_mFourierCoeff_eq (f g : C(UnitAddTorus d, ℂ))
    (h : ∀ q, mFourierCoeff f q = mFourierCoeff g q) : f = g := by
  have hf := hasSum_mFourier_series_L2 (f.toLp 2 volume ℂ)
  have hg := hasSum_mFourier_series_L2 (g.toLp 2 volume ℂ)
  simp only [mFourierCoeff_toLp, h] at hf hg
  exact ContinuousMap.toLp_injective volume (hf.unique hg)

theorem mFourierCoeff_map (L : E →L[ℂ] F) (f : C(UnitAddTorus d, E)) (q : d → ℤ) :
    mFourierCoeff (fun x ↦ L (f x)) q = L (mFourierCoeff f q) := by
  unfold mFourierCoeff
  simp_rw [← L.map_smul]
  exact L.integral_comp_comm (integrable_coefficient_integrand q f)

theorem eq_of_mFourierCoeff_eq (f g : C(UnitAddTorus d, E))
    (h : ∀ q, mFourierCoeff f q = mFourierCoeff g q) : f = g := by
  apply ContinuousMap.ext
  intro x
  apply (SeparatingDual.eq_iff_forall_dual_eq (R := ℂ)).mpr
  intro L
  let fL : C(UnitAddTorus d, ℂ) := ⟨fun y ↦ L (f y), L.continuous.comp f.continuous⟩
  let gL : C(UnitAddTorus d, ℂ) := ⟨fun y ↦ L (g y), L.continuous.comp g.continuous⟩
  have he : fL = gL := scalar_eq_of_mFourierCoeff_eq fL gL (fun q ↦ by
    change mFourierCoeff (fun y ↦ L (f y)) q = mFourierCoeff (fun y ↦ L (g y)) q
    rw [mFourierCoeff_map, mFourierCoeff_map, h q])
  exact congrArg (fun v : C(UnitAddTorus d, ℂ) ↦ v x) he

def polynomial (P : Finset (d → ℤ)) (a : (d → ℤ) → E) : C(UnitAddTorus d, E) :=
  ∑ q ∈ P, ⟨fun x ↦ mFourier q x • a q, (mFourier q).continuous.smul continuous_const⟩

omit [CompleteSpace E] in
@[simp] theorem polynomial_apply (P : Finset (d → ℤ)) (a : (d → ℤ) → E)
    (x : UnitAddTorus d) : polynomial P a x = ∑ q ∈ P, mFourier q x • a q := by
  simp [polynomial]

theorem mFourierCoeff_polynomial (P : Finset (d → ℤ)) (a : (d → ℤ) → E) (q : d → ℤ) :
    mFourierCoeff (polynomial P a) q = if q ∈ P then a q else 0 := by
  classical
  change coefficientCLM q (polynomial P a) = _
  simp only [polynomial, map_sum, coefficientCLM_apply]
  change (∑ k ∈ P, mFourierCoeff (fun x : UnitAddTorus d ↦ mFourier k x • a k) q) = _
  simp only [mFourierCoeff_monomial]
  simp

/-- Vanishing coefficients off a finite set give exact pointwise reconstruction. -/
theorem eq_polynomial (f : C(UnitAddTorus d, E)) (P : Finset (d → ℤ))
    (h : ∀ q ∉ P, mFourierCoeff f q = 0) :
    f = polynomial P (fun q ↦ mFourierCoeff f q) := by
  apply eq_of_mFourierCoeff_eq
  intro q
  rw [mFourierCoeff_polynomial]
  split_ifs with hq
  · rfl
  · exact h q hq

end Mettapedia.Analysis.UnitTorusFourierUniqueness
