import Mettapedia.Analysis.UnitTorusFiniteFilter

/-!
# Finite-filter adjoint checks

The complex-symbol regression distinguishes adjointness from an incorrect
self-adjointness claim. The other tests exercise empty support and a mode
excluded from a nonsymmetric retained set.
-/

noncomputable section

namespace Mettapedia.Analysis.UnitTorusFiniteFilterTests

open scoped InnerProductSpace ComplexConjugate
open MeasureTheory UnitAddTorus Mettapedia.Analysis
open UnitTorusFiniteFilter

local notation "T3" => UnitAddTorus (Fin 3)
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

example (χ : (Fin 3 → ℤ) → ℂ) (f : T3 → ℂ) (x : T3) :
    finiteFilter ∅ χ f x = 0 := finiteFilter_empty χ f x

example (P : Finset (Fin 3 → ℤ)) (q : Fin 3 → ℤ) (hq : q ∉ P)
    (χ : (Fin 3 → ℤ) → ℂ) (x : T3) :
    finiteFilter P χ (fun y ↦ mFourier q y • (1 : ℂ)) x = 0 := by
  rw [finiteFilter_monomial, if_neg hq]

example :
    (∫ x : T3, ⟪(1 : ℂ), finiteFilter {0} (fun _ ↦ Complex.I) (fun _ ↦ (1 : ℂ)) x⟫_ℂ) ≠
      ∫ x : T3, ⟪finiteFilter {0} (fun _ ↦ Complex.I) (fun _ ↦ (1 : ℂ)) x, (1 : ℂ)⟫_ℂ := by
  have hf (x : T3) : finiteFilter {0} (fun _ ↦ Complex.I) (fun _ : T3 ↦ (1 : ℂ)) x = Complex.I := by
    simpa only [mFourier_zero, ContinuousMap.one_apply, one_smul, Finset.mem_singleton,
      ite_true, smul_eq_mul, mul_one, one_mul] using finiteFilter_monomial ({0} : Finset (Fin 3 → ℤ)) (fun _ ↦ Complex.I) 0 (1 : ℂ) x
  simp_rw [hf]
  norm_num
  intro h
  have him := congrArg Complex.im h
  norm_num at him

end Mettapedia.Analysis.UnitTorusFiniteFilterTests
