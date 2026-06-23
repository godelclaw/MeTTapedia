import Mettapedia.Computability.PNP.FiniteCoinPostprocessingFoundationExactCore

/-!
# Finite-coin postprocessing: globally injective maps

Lossless deterministic postprocessing preserves finite-coin fiber counts and
balanced-fiber certificates exactly.
-/

namespace Mettapedia.Computability.PNP

/-- The true-side fiber count is unchanged by an injective deterministic
postprocessing map. -/
theorem coinTrueFiberCount_postcompose_injective
    {Coin α β : Type*} [Fintype Coin] [DecidableEq α] [DecidableEq β]
    (r : Bool → Coin → α) (g : α → β)
    (hinj : Function.Injective g) (y : α) :
    coinTrueFiberCount (fun b c => g (r b c)) (g y) =
      coinTrueFiberCount r y := by
  apply le_antisymm
  · simpa [coinTrueFiberCount] using
      (finiteEventCount_le_of_imp (Ω := Coin)
        (fun c h => hinj h))
  · simpa [coinTrueFiberCount] using
      (finiteEventCount_le_of_imp (Ω := Coin)
        (fun c h => by simp [h]))

/-- The false-side fiber count is unchanged by an injective deterministic
postprocessing map. -/
theorem coinFalseFiberCount_postcompose_injective
    {Coin α β : Type*} [Fintype Coin] [DecidableEq α] [DecidableEq β]
    (r : Bool → Coin → α) (g : α → β)
    (hinj : Function.Injective g) (y : α) :
    coinFalseFiberCount (fun b c => g (r b c)) (g y) =
      coinFalseFiberCount r y := by
  apply le_antisymm
  · simpa [coinFalseFiberCount] using
      (finiteEventCount_le_of_imp (Ω := Coin)
        (fun c h => hinj h))
  · simpa [coinFalseFiberCount] using
      (finiteEventCount_le_of_imp (Ω := Coin)
        (fun c h => by simp [h]))

/-- Injective deterministic postprocessing cannot create balanced finite-coin
fibers that were not already present before postprocessing. -/
theorem finiteCoinRecodingFiberBalanced_of_postcompose_injective
    {Coin α β : Type*} [Fintype Coin] [DecidableEq α] [DecidableEq β]
    (r : Bool → Coin → α) (g : α → β)
    (hinj : Function.Injective g)
    (hbal : FiniteCoinRecodingFiberBalanced (fun b c => g (r b c))) :
    FiniteCoinRecodingFiberBalanced r := by
  intro y
  have hpost := hbal (g y)
  have htrue := coinTrueFiberCount_postcompose_injective r g hinj y
  have hfalse := coinFalseFiberCount_postcompose_injective r g hinj y
  calc
    coinTrueFiberCount r y =
        coinTrueFiberCount (fun b c => g (r b c)) (g y) := htrue.symm
    _ = coinFalseFiberCount (fun b c => g (r b c)) (g y) := hpost
    _ = coinFalseFiberCount r y := hfalse

/-- For injective deterministic postprocessing, balanced finite-coin fibers are
exactly preserved.  Lossless recoding therefore cannot be the step that repairs
an unbalanced finite-coin source/output relation. -/
theorem finiteCoinRecodingFiberBalanced_postcompose_iff_of_injective
    {Coin α β : Type*} [Fintype Coin] [DecidableEq α] [DecidableEq β]
    (r : Bool → Coin → α) (g : α → β)
    (hinj : Function.Injective g) :
    FiniteCoinRecodingFiberBalanced (fun b c => g (r b c)) ↔
      FiniteCoinRecodingFiberBalanced r := by
  constructor
  · exact finiteCoinRecodingFiberBalanced_of_postcompose_injective r g hinj
  · exact finiteCoinRecodingFiberBalanced_postcompose r g

end Mettapedia.Computability.PNP
