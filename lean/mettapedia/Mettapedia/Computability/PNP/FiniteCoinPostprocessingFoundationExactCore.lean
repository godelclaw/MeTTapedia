import Mettapedia.Computability.PNP.FiniteCoinToleranceQuantization

/-!
# Finite-coin postprocessing: exact core

Basic finite-output fibers and forward preservation under deterministic
postprocessing.
-/

namespace Mettapedia.Computability.PNP

/-- The finite preimage of one postprocessed output value. -/
def finiteOutputPreimageFiber {α β : Type*} [Fintype α] [DecidableEq β]
    (g : α → β) (z : β) : Finset α :=
  (Finset.univ : Finset α).filter (fun y => g y = z)

/-- A deterministic finite-output postprocessing map has fibers of size at most
`m`. -/
def finiteOutputMapFiberCardBound {α β : Type*} [Fintype α] [DecidableEq β]
    (g : α → β) (m : Nat) : Prop :=
  ∀ z : β, (finiteOutputPreimageFiber g z).card ≤ m

/-- Every finite-output postprocessing map has the trivial fiber bound
`|α|`. -/
theorem finiteOutputMapFiberCardBound_card
    {α β : Type*} [Fintype α] [DecidableEq β] (g : α → β) :
    finiteOutputMapFiberCardBound g (Fintype.card α) := by
  intro z
  exact Finset.card_le_card (Finset.filter_subset (fun y => g y = z)
    (Finset.univ : Finset α))

/-- Predicate neutrality is preserved by deterministic postprocessing. -/
theorem finiteCoinOutputPredicateNeutral_postcompose
    {Coin α β : Type*} [Fintype Coin]
    (r : Bool → Coin → α) (g : α → β)
    (P : β → Prop) [DecidablePred P]
    (hneutral : finiteCoinOutputPredicateNeutral r (fun y => P (g y))) :
    finiteCoinOutputPredicateNeutral (fun b c => g (r b c)) P := by
  simpa [finiteCoinOutputPredicateNeutral] using hneutral

/-- Predicate erasure is preserved by deterministic postprocessing. -/
theorem finiteCoinOutputPredicateErasing_postcompose
    {Coin α β : Type*} [Fintype Coin]
    (r : Bool → Coin → α) (g : α → β)
    (herase : FiniteCoinOutputPredicateErasing r) :
    FiniteCoinOutputPredicateErasing (fun b c => g (r b c)) := by
  intro P _hP
  exact finiteCoinOutputPredicateNeutral_postcompose r g P
    (herase (fun y => P (g y)))

/-- Balanced finite-coin fibers are preserved by deterministic postprocessing. -/
theorem finiteCoinRecodingFiberBalanced_postcompose
    {Coin α β : Type*} [Fintype Coin] [DecidableEq α] [DecidableEq β]
    (r : Bool → Coin → α) (g : α → β)
    (hbal : FiniteCoinRecodingFiberBalanced r) :
    FiniteCoinRecodingFiberBalanced (fun b c => g (r b c)) := by
  exact finiteCoinRecodingFiberBalanced_of_outputPredicateErasing
    (fun b c => g (r b c))
    (finiteCoinOutputPredicateErasing_postcompose r g
      (finiteCoinOutputPredicateErasing_of_fiberBalanced r hbal))

end Mettapedia.Computability.PNP
