import Mathlib.Analysis.Fourier.AddCircleMulti
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! Product-Haar integration in finite torus coordinates. -/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.Analysis.FiniteTorusProduct

open MeasureTheory

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

def splitEquiv (m n : ℕ) :
    UnitAddTorus (Fin (m + n)) ≃ᵐ UnitAddTorus (Fin m) × UnitAddTorus (Fin n) :=
  (MeasurableEquiv.piCongrLeft (fun _ : Fin m ⊕ Fin n ↦ UnitAddCircle)
    finSumFinEquiv.symm).trans (MeasurableEquiv.sumPiEquivProdPi _)

theorem splitEquiv_apply (m n : ℕ) (x : UnitAddTorus (Fin (m + n))) :
    splitEquiv m n x = (fun i ↦ x (Fin.castAdd n i), fun j ↦ x (Fin.natAdd m j)) := by
  ext i <;> simp [splitEquiv, MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft,
    MeasurableEquiv.sumPiEquivProdPi]

theorem measurePreserving_splitEquiv (m n : ℕ) :
    MeasurePreserving (splitEquiv m n) volume volume :=
  (volume_measurePreserving_sumPiEquivProdPi _).comp
    (volume_measurePreserving_piCongrLeft _ finSumFinEquiv.symm)

theorem integral_split {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (m n : ℕ) (F : UnitAddTorus (Fin m) → UnitAddTorus (Fin n) → E)
    (hF : Continuous (Function.uncurry F)) :
    (∫ x : UnitAddTorus (Fin (m + n)),
      F (fun i ↦ x (Fin.castAdd n i)) (fun j ↦ x (Fin.natAdd m j))) =
      ∫ y : UnitAddTorus (Fin m), ∫ z : UnitAddTorus (Fin n), F y z := by
  have he (x : UnitAddTorus (Fin (m + n))) :
      F (fun i ↦ x (Fin.castAdd n i)) (fun j ↦ x (Fin.natAdd m j)) =
        Function.uncurry F (splitEquiv m n x) := by rw [splitEquiv_apply]; rfl
  simp_rw [he]
  rw [(measurePreserving_splitEquiv m n).integral_comp']
  exact integral_prod _ (hF.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))

theorem integral_bilinear {E F G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    [NormedAddCommGroup G] [NormedSpace ℂ G] [CompleteSpace G]
    (m n : ℕ) (B : E →L[ℂ] F →L[ℂ] G)
    (f : UnitAddTorus (Fin m) → E) (g : UnitAddTorus (Fin n) → F)
    (hf : Continuous f) (hg : Continuous g) :
    (∫ x : UnitAddTorus (Fin (m + n)),
      B (f (fun i ↦ x (Fin.castAdd n i))) (g (fun j ↦ x (Fin.natAdd m j)))) =
      B (∫ y, f y) (∫ z, g z) := by
  rw [integral_split m n (fun y z ↦ B (f y) (g z)) (by fun_prop)]
  have hin (y : UnitAddTorus (Fin m)) : (∫ z, B (f y) (g z)) = B (f y) (∫ z, g z) :=
    (B (f y)).integral_comp_comm
      (hg.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
  simp_rw [hin]
  exact (B.flip _).integral_comp_comm
    (hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))

end Mettapedia.Analysis.FiniteTorusProduct
