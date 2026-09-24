import Mettapedia.Analysis.UnitTorusMaterialBalance
import Mettapedia.Analysis.FiniteTorusProduct

/-!
# Two-endpoint periodic transport

Sum-index torus coordinates represent a pair of spatial points. Their product
velocity has divergence equal to the sum of the two endpoint divergences.
The coordinate identification preserves normalized Haar measure.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.Analysis.UnitTorusProductTransport

open MeasureTheory UnitTorusWeakDerivative

variable {d e : Type*} [Fintype d] [Fintype e] [DecidableEq d] [DecidableEq e]

local notation "Td" => UnitAddTorus d
local notation "Te" => UnitAddTorus e
local notation "Tde" => UnitAddTorus (d ⊕ e)

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

def leftPoint (x : Tde) : Td := fun i ↦ x (Sum.inl i)
def rightPoint (x : Tde) : Te := fun i ↦ x (Sum.inr i)

def pairVelocity (v : Td → d → ℝ) (w : Te → e → ℝ) (x : Tde) : d ⊕ e → ℝ :=
  Sum.elim (v (leftPoint x)) (w (rightPoint x))

omit [Fintype d] [Fintype e] [DecidableEq d] [DecidableEq e] in
theorem continuous_leftPoint : Continuous (leftPoint (d := d) (e := e)) := by
  unfold leftPoint
  fun_prop

omit [Fintype d] [Fintype e] [DecidableEq d] [DecidableEq e] in
theorem continuous_rightPoint : Continuous (rightPoint (d := d) (e := e)) := by
  unfold rightPoint
  fun_prop

omit [Fintype d] [Fintype e] [DecidableEq d] [DecidableEq e] in
theorem continuous_pairVelocity {v : Td → d → ℝ} {w : Te → e → ℝ}
    (hv : Continuous v) (hw : Continuous w) : Continuous (pairVelocity v w) := by
  apply continuous_pi
  intro i
  cases i with
  | inl i => exact (continuous_apply i).comp (hv.comp continuous_leftPoint)
  | inr i => exact (continuous_apply i).comp (hw.comp continuous_rightPoint)

theorem coordinateDivergence_pairVelocity (v : Td → d → ℝ) (w : Te → e → ℝ) (x : Tde) :
    coordinateDivergence (fun j y ↦ pairVelocity v w y j) x =
      coordinateDivergence (fun j y ↦ v y j) (leftPoint x) +
        coordinateDivergence (fun j y ↦ w y j) (rightPoint x) := by
  simp only [coordinateDivergence, Fintype.sum_sum_type]
  congr 1
  · apply Finset.sum_congr rfl
    intro j _
    unfold shiftRate
    congr 1
    funext h
    change v (leftPoint (x + coordinateShift (Sum.inl j) h)) j =
      v (leftPoint x + coordinateShift j h) j
    congr 1
    ext i
    simp [leftPoint, coordinateShift, torusPoint, coordinateLine]
  · apply Finset.sum_congr rfl
    intro j _
    unfold shiftRate
    congr 1
    funext h
    change w (rightPoint (x + coordinateShift (Sum.inr j) h)) j =
      w (rightPoint x + coordinateShift j h) j
    congr 1
    ext i
    simp [rightPoint, coordinateShift, torusPoint, coordinateLine]

omit [DecidableEq d] [DecidableEq e] in
theorem lipschitzWith_restrict_left :
    LipschitzWith 1 (fun r : d ⊕ e → ℝ ↦ fun i : d ↦ r (Sum.inl i)) := by
  apply LipschitzWith.of_dist_le_mul
  intro r s
  simp only [NNReal.coe_one, one_mul]
  apply (dist_pi_le_iff dist_nonneg).mpr
  intro i
  exact (dist_pi_le_iff dist_nonneg).mp (le_refl (dist r s)) (Sum.inl i)

omit [DecidableEq d] [DecidableEq e] in
theorem lipschitzWith_restrict_right :
    LipschitzWith 1 (fun r : d ⊕ e → ℝ ↦ fun i : e ↦ r (Sum.inr i)) := by
  apply LipschitzWith.of_dist_le_mul
  intro r s
  simp only [NNReal.coe_one, one_mul]
  apply (dist_pi_le_iff dist_nonneg).mpr
  intro i
  exact (dist_pi_le_iff dist_nonneg).mp (le_refl (dist r s)) (Sum.inr i)

omit [DecidableEq d] [DecidableEq e] in
theorem locallyLipschitz_pairVelocity
    (v : Td → d → ℝ) (w : Te → e → ℝ)
    (hv : ∀ j, LocallyLipschitz (fun r : d → ℝ ↦ v (torusPoint r) j))
    (hw : ∀ j, LocallyLipschitz (fun r : e → ℝ ↦ w (torusPoint r) j)) (j : d ⊕ e) :
    LocallyLipschitz (fun r : d ⊕ e → ℝ ↦ pairVelocity v w (torusPoint r) j) := by
  cases j with
  | inl j => exact (hv j).comp lipschitzWith_restrict_left.locallyLipschitz
  | inr j => exact (hw j).comp lipschitzWith_restrict_right.locallyLipschitz

omit [DecidableEq d] [DecidableEq e] in
theorem integral_pair {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : Td → Te → E) (hf : Integrable f.uncurry) :
    (∫ x : Tde, f (leftPoint x) (rightPoint x)) = ∫ x : Td, ∫ y : Te, f x y := by
  change (∫ x : Tde, f.uncurry (MeasurableEquiv.sumPiEquivProdPi
    (fun _ : d ⊕ e ↦ UnitAddCircle) x)) = _
  rw [(volume_measurePreserving_sumPiEquivProdPi (fun _ : d ⊕ e ↦ UnitAddCircle)).integral_comp']
  exact integral_prod _ hf

end Mettapedia.Analysis.UnitTorusProductTransport
