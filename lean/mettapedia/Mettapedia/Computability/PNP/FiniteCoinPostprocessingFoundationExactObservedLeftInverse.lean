import Mettapedia.Computability.PNP.FiniteCoinPostprocessingFoundationExactCore

/-!
# Finite-coin postprocessing: observed left inverses

Postprocessors with a left inverse on the actually observed samples preserve
finite-coin balanced-fiber certificates exactly.
-/

namespace Mettapedia.Computability.PNP

/-- A postprocessor with a left inverse on the actually observed finite-coin
outputs cannot create balanced fibers that were not already present.  This
blocks the repair where a many-to-one coarsening is claimed to preserve the
original recoding on the proof-relevant samples. -/
theorem finiteCoinRecodingFiberBalanced_of_postcompose_observedLeftInverse
    {Coin α β : Type*} [Fintype Coin] [DecidableEq α] [DecidableEq β]
    (r : Bool → Coin → α) (g : α → β) (recover : β → α)
    (hrecover : ∀ b c, recover (g (r b c)) = r b c)
    (hbal : FiniteCoinRecodingFiberBalanced (fun b c => g (r b c))) :
    FiniteCoinRecodingFiberBalanced r := by
  have herase :
      FiniteCoinOutputPredicateErasing (fun b c => g (r b c)) :=
    finiteCoinOutputPredicateErasing_of_fiberBalanced
      (fun b c => g (r b c)) hbal
  intro y
  have hpred := herase (fun z => recover z = y)
  have htrue :
      finiteEventCount Coin (fun c => recover (g (r true c)) = y) =
        coinTrueFiberCount r y := by
    apply le_antisymm
    · simpa [coinTrueFiberCount] using
        (finiteEventCount_le_of_imp (Ω := Coin)
          (fun c h => by
            rw [hrecover true c] at h
            exact h))
    · simpa [coinTrueFiberCount] using
        (finiteEventCount_le_of_imp (Ω := Coin)
          (fun c h => by
            rw [hrecover true c]
            exact h))
  have hfalse :
      finiteEventCount Coin (fun c => recover (g (r false c)) = y) =
        coinFalseFiberCount r y := by
    apply le_antisymm
    · simpa [coinFalseFiberCount] using
        (finiteEventCount_le_of_imp (Ω := Coin)
          (fun c h => by
            rw [hrecover false c] at h
            exact h))
    · simpa [coinFalseFiberCount] using
        (finiteEventCount_le_of_imp (Ω := Coin)
          (fun c h => by
            rw [hrecover false c]
            exact h))
  calc
    coinTrueFiberCount r y =
        finiteEventCount Coin (fun c => recover (g (r true c)) = y) :=
          htrue.symm
    _ = finiteEventCount Coin (fun c => recover (g (r false c)) = y) := hpred
    _ = coinFalseFiberCount r y := hfalse

/-- For postprocessors with a left inverse on the observed finite-coin samples,
balanced fibers are exactly preserved.  Non-injective postprocessing can only
repair an imbalance by losing original-output information on the observed
support. -/
theorem finiteCoinRecodingFiberBalanced_postcompose_iff_of_observedLeftInverse
    {Coin α β : Type*} [Fintype Coin] [DecidableEq α] [DecidableEq β]
    (r : Bool → Coin → α) (g : α → β) (recover : β → α)
    (hrecover : ∀ b c, recover (g (r b c)) = r b c) :
    FiniteCoinRecodingFiberBalanced (fun b c => g (r b c)) ↔
      FiniteCoinRecodingFiberBalanced r := by
  constructor
  · exact finiteCoinRecodingFiberBalanced_of_postcompose_observedLeftInverse
      r g recover hrecover
  · exact finiteCoinRecodingFiberBalanced_postcompose r g

end Mettapedia.Computability.PNP
