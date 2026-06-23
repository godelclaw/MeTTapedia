import Mettapedia.Computability.PNP.FiniteCoinPostprocessingFoundationExactCore

/-!
# Finite-coin postprocessing: observed injectivity

Only collisions on actually observed finite-coin samples matter for exact
preservation of balanced fibers and fiber counts.
-/

namespace Mettapedia.Computability.PNP

/-- A postprocessor that is injective on the actually observed finite-coin
outputs cannot create balanced fibers that were not already present.  This is
weaker than global injectivity and avoids choosing an explicit recovery map:
only collisions on the finite observed support matter. -/
theorem finiteCoinRecodingFiberBalanced_of_postcompose_observedInjective
    {Coin α β : Type*} [Fintype Coin] [DecidableEq α] [DecidableEq β]
    (r : Bool → Coin → α) (g : α → β)
    (hinjObs :
      ∀ b1 c1 b2 c2,
        g (r b1 c1) = g (r b2 c2) → r b1 c1 = r b2 c2)
    (hbal : FiniteCoinRecodingFiberBalanced (fun b c => g (r b c))) :
    FiniteCoinRecodingFiberBalanced r := by
  intro y
  by_cases hobs : ∃ b : Bool, ∃ c : Coin, r b c = y
  · rcases hobs with ⟨b0, c0, hy⟩
    have htrue :
        coinTrueFiberCount (fun b c => g (r b c)) (g y) =
          coinTrueFiberCount r y := by
      apply le_antisymm
      · simpa [coinTrueFiberCount] using
          (finiteEventCount_le_of_imp (Ω := Coin)
            (fun c h => by
              have hgy : g (r true c) = g (r b0 c0) := by
                simpa [hy] using h
              exact (hinjObs true c b0 c0 hgy).trans hy))
      · simpa [coinTrueFiberCount] using
          (finiteEventCount_le_of_imp (Ω := Coin)
            (fun c h => by simp [h]))
    have hfalse :
        coinFalseFiberCount (fun b c => g (r b c)) (g y) =
          coinFalseFiberCount r y := by
      apply le_antisymm
      · simpa [coinFalseFiberCount] using
          (finiteEventCount_le_of_imp (Ω := Coin)
            (fun c h => by
              have hgy : g (r false c) = g (r b0 c0) := by
                simpa [hy] using h
              exact (hinjObs false c b0 c0 hgy).trans hy))
      · simpa [coinFalseFiberCount] using
          (finiteEventCount_le_of_imp (Ω := Coin)
            (fun c h => by simp [h]))
    calc
      coinTrueFiberCount r y =
          coinTrueFiberCount (fun b c => g (r b c)) (g y) := htrue.symm
      _ = coinFalseFiberCount (fun b c => g (r b c)) (g y) := hbal (g y)
      _ = coinFalseFiberCount r y := hfalse
  · have htrue_zero : coinTrueFiberCount r y = 0 := by
      exact finiteEventCount_zero_of_forall_not (Ω := Coin)
        (fun c => r true c = y)
        (fun c hc => hobs ⟨true, c, hc⟩)
    have hfalse_zero : coinFalseFiberCount r y = 0 := by
      exact finiteEventCount_zero_of_forall_not (Ω := Coin)
        (fun c => r false c = y)
        (fun c hc => hobs ⟨false, c, hc⟩)
    rw [htrue_zero, hfalse_zero]

/-- For postprocessors injective on the observed finite-coin support, balanced
fibers are exactly preserved.  Hence postprocessing can repair an imbalance
only by creating a collision between distinct observed original outputs. -/
theorem finiteCoinRecodingFiberBalanced_postcompose_iff_of_observedInjective
    {Coin α β : Type*} [Fintype Coin] [DecidableEq α] [DecidableEq β]
    (r : Bool → Coin → α) (g : α → β)
    (hinjObs :
      ∀ b1 c1 b2 c2,
        g (r b1 c1) = g (r b2 c2) → r b1 c1 = r b2 c2) :
    FiniteCoinRecodingFiberBalanced (fun b c => g (r b c)) ↔
      FiniteCoinRecodingFiberBalanced r := by
  constructor
  · exact finiteCoinRecodingFiberBalanced_of_postcompose_observedInjective
      r g hinjObs
  · exact finiteCoinRecodingFiberBalanced_postcompose r g

/-- On any actually observed output value, an observed-support-injective
postprocessor preserves the true-side fiber count exactly. -/
theorem coinTrueFiberCount_postcompose_observedInjective
    {Coin α β : Type*} [Fintype Coin] [DecidableEq α] [DecidableEq β]
    (r : Bool → Coin → α) (g : α → β)
    (hinjObs :
      ∀ b1 c1 b2 c2,
        g (r b1 c1) = g (r b2 c2) → r b1 c1 = r b2 c2)
    {y : α} (hobs : ∃ b : Bool, ∃ c : Coin, r b c = y) :
    coinTrueFiberCount (fun b c => g (r b c)) (g y) =
      coinTrueFiberCount r y := by
  rcases hobs with ⟨b0, c0, hy⟩
  apply le_antisymm
  · simpa [coinTrueFiberCount] using
      (finiteEventCount_le_of_imp (Ω := Coin)
        (fun c h => by
          have hgy : g (r true c) = g (r b0 c0) := by
            simpa [hy] using h
          exact (hinjObs true c b0 c0 hgy).trans hy))
  · simpa [coinTrueFiberCount] using
      (finiteEventCount_le_of_imp (Ω := Coin)
        (fun c h => by simp [h]))

/-- On any actually observed output value, an observed-support-injective
postprocessor preserves the false-side fiber count exactly. -/
theorem coinFalseFiberCount_postcompose_observedInjective
    {Coin α β : Type*} [Fintype Coin] [DecidableEq α] [DecidableEq β]
    (r : Bool → Coin → α) (g : α → β)
    (hinjObs :
      ∀ b1 c1 b2 c2,
        g (r b1 c1) = g (r b2 c2) → r b1 c1 = r b2 c2)
    {y : α} (hobs : ∃ b : Bool, ∃ c : Coin, r b c = y) :
    coinFalseFiberCount (fun b c => g (r b c)) (g y) =
      coinFalseFiberCount r y := by
  rcases hobs with ⟨b0, c0, hy⟩
  apply le_antisymm
  · simpa [coinFalseFiberCount] using
      (finiteEventCount_le_of_imp (Ω := Coin)
        (fun c h => by
          have hgy : g (r false c) = g (r b0 c0) := by
            simpa [hy] using h
          exact (hinjObs false c b0 c0 hgy).trans hy))
  · simpa [coinFalseFiberCount] using
      (finiteEventCount_le_of_imp (Ω := Coin)
        (fun c h => by simp [h]))

end Mettapedia.Computability.PNP
