import Mettapedia.Computability.PNP.FiniteCoinPostprocessingFoundationBias

/-!
# Finite-coin postprocessing: tolerance and defect bounds

Approximate finite-count tolerance and max-defect bounds under deterministic
postprocessing with finite output fibers.
-/

namespace Mettapedia.Computability.PNP

/-- Deterministic postprocessing with fibers of size at most `m` turns
finite-coin output tolerance `τ` into tolerance `m * τ`. -/
theorem countIndependentWithinToleranceOutput_finiteCoinOutput_postcompose
    {Coin α β : Type*} [Fintype Coin] [Fintype α]
    [DecidableEq α] [DecidableEq β]
    (r : Bool → Coin → α) (g : α → β) {m τ : Nat}
    (hbound : finiteOutputMapFiberCardBound g m)
    (happrox : CountIndependentWithinToleranceOutput (Ω := Bool × Coin)
      (fun _ω => True)
      (finiteCoinSourceTrue (Coin := Coin))
      (finiteCoinOutput r) τ) :
    CountIndependentWithinToleranceOutput (Ω := Bool × Coin)
      (fun _ω => True)
      (finiteCoinSourceTrue (Coin := Coin))
      (finiteCoinOutput (fun b c => g (r b c))) (m * τ) := by
  classical
  refine
    (countIndependentWithinToleranceOutput_finiteCoinOutput_iff_forall_scaled_fiberImbalance_le
      (fun b c => g (r b c)) (m * τ)).mpr ?_
  intro z
  let s := finiteOutputPreimageFiber g z
  have himb := finiteCoinFiberImbalance_postcompose_le_sum_preimage r g z
  have hscaled :
      ∀ y : α, Fintype.card Coin * finiteCoinFiberImbalance r y ≤ τ :=
    (countIndependentWithinToleranceOutput_finiteCoinOutput_iff_forall_scaled_fiberImbalance_le
      r τ).mp happrox
  calc
    Fintype.card Coin *
        finiteCoinFiberImbalance (fun b c => g (r b c)) z
        ≤ Fintype.card Coin *
            (∑ y ∈ s, finiteCoinFiberImbalance r y) :=
          Nat.mul_le_mul_left (Fintype.card Coin) himb
    _ = ∑ y ∈ s, Fintype.card Coin * finiteCoinFiberImbalance r y := by
          rw [Finset.mul_sum]
    _ ≤ ∑ _y ∈ s, τ := by
          refine Finset.sum_le_sum ?_
          intro y _hy
          exact hscaled y
    _ = s.card * τ := by
          simp [Nat.mul_comm]
    _ ≤ m * τ := by
          exact Nat.mul_le_mul_right τ (by simpa [s] using hbound z)

/-- The trivial finite-output bound: postprocessing by any map out of `α`
turns tolerance `τ` into tolerance `|α| * τ`. -/
theorem countIndependentWithinToleranceOutput_finiteCoinOutput_postcompose_card
    {Coin α β : Type*} [Fintype Coin] [Fintype α]
    [DecidableEq α] [DecidableEq β]
    (r : Bool → Coin → α) (g : α → β) {τ : Nat}
    (happrox : CountIndependentWithinToleranceOutput (Ω := Bool × Coin)
      (fun _ω => True)
      (finiteCoinSourceTrue (Coin := Coin))
      (finiteCoinOutput r) τ) :
    CountIndependentWithinToleranceOutput (Ω := Bool × Coin)
      (fun _ω => True)
      (finiteCoinSourceTrue (Coin := Coin))
      (finiteCoinOutput (fun b c => g (r b c))) (Fintype.card α * τ) :=
  countIndependentWithinToleranceOutput_finiteCoinOutput_postcompose
    r g (finiteOutputMapFiberCardBound_card g) happrox

/-- Finite-output max defect obeys the same finite-preimage postprocessing
bound as the pointwise tolerance certificate. -/
theorem countIndependentWithinOutputDefect_finiteCoinOutput_postcompose_le
    {Coin α β : Type*} [Fintype Coin] [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β]
    (r : Bool → Coin → α) (g : α → β) {m : Nat}
    (hbound : finiteOutputMapFiberCardBound g m) :
    countIndependentWithinOutputDefect (Ω := Bool × Coin)
      (fun _ω => True)
      (finiteCoinSourceTrue (Coin := Coin))
      (finiteCoinOutput (fun b c => g (r b c))) ≤
    m *
      countIndependentWithinOutputDefect (Ω := Bool × Coin)
        (fun _ω => True)
        (finiteCoinSourceTrue (Coin := Coin))
        (finiteCoinOutput r) := by
  let D :=
    countIndependentWithinOutputDefect (Ω := Bool × Coin)
      (fun _ω => True)
      (finiteCoinSourceTrue (Coin := Coin))
      (finiteCoinOutput r)
  have happrox :
      CountIndependentWithinToleranceOutput (Ω := Bool × Coin)
        (fun _ω => True)
        (finiteCoinSourceTrue (Coin := Coin))
        (finiteCoinOutput r) D := by
    exact (countIndependentWithinToleranceOutput_iff_outputDefect_le
      (fun _ω : Bool × Coin => True)
      (finiteCoinSourceTrue (Coin := Coin))
      (finiteCoinOutput r) D).mpr le_rfl
  have hpost :
      CountIndependentWithinToleranceOutput (Ω := Bool × Coin)
        (fun _ω => True)
        (finiteCoinSourceTrue (Coin := Coin))
        (finiteCoinOutput (fun b c => g (r b c))) (m * D) :=
    countIndependentWithinToleranceOutput_finiteCoinOutput_postcompose
      r g hbound happrox
  exact (countIndependentWithinToleranceOutput_iff_outputDefect_le
    (fun _ω : Bool × Coin => True)
    (finiteCoinSourceTrue (Coin := Coin))
    (finiteCoinOutput (fun b c => g (r b c))) (m * D)).mp hpost

/-- With the trivial finite-output bound, any deterministic postprocessing by a
map out of `α` multiplies max defect by at most `|α|`. -/
theorem countIndependentWithinOutputDefect_finiteCoinOutput_postcompose_le_card
    {Coin α β : Type*} [Fintype Coin] [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β]
    (r : Bool → Coin → α) (g : α → β) :
    countIndependentWithinOutputDefect (Ω := Bool × Coin)
      (fun _ω => True)
      (finiteCoinSourceTrue (Coin := Coin))
      (finiteCoinOutput (fun b c => g (r b c))) ≤
    Fintype.card α *
      countIndependentWithinOutputDefect (Ω := Bool × Coin)
        (fun _ω => True)
        (finiteCoinSourceTrue (Coin := Coin))
        (finiteCoinOutput r) :=
  countIndependentWithinOutputDefect_finiteCoinOutput_postcompose_le
    r g (finiteOutputMapFiberCardBound_card g)

end Mettapedia.Computability.PNP
