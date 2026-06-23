import Mettapedia.Computability.PNP.FiniteCoinPostprocessingFoundationExactInjective
import Mettapedia.Computability.PNP.FiniteCoinPostprocessingFoundationExactObservedInjective
import Mettapedia.Computability.PNP.FiniteCoinPostprocessingFoundationExactObservedLeftInverse

/-!
# Finite-coin postprocessing: collision and erasure consequences

Exact preservation turns a successful many-to-one postprocessing repair into a
concrete observed collision, and gives predicate-erasure iff boundaries for
lossless postprocessors.
-/

namespace Mettapedia.Computability.PNP

/-- If postprocessing creates balanced fibers from an originally unbalanced
finite-coin recoding, then it must identify two distinct observed original
outputs.  This is the collision-level obstruction for many-to-one coarsening
repairs. -/
theorem exists_observedOutput_collision_of_postcompose_fiberBalanced_of_not_fiberBalanced
    {Coin α β : Type*} [Fintype Coin] [DecidableEq α] [DecidableEq β]
    (r : Bool → Coin → α) (g : α → β)
    (hbal : FiniteCoinRecodingFiberBalanced (fun b c => g (r b c)))
    (hnot : ¬ FiniteCoinRecodingFiberBalanced r) :
    ∃ b1 : Bool, ∃ c1 : Coin, ∃ b2 : Bool, ∃ c2 : Coin,
      r b1 c1 ≠ r b2 c2 ∧ g (r b1 c1) = g (r b2 c2) := by
  by_contra hnone
  apply hnot
  exact finiteCoinRecodingFiberBalanced_of_postcompose_observedInjective
    r g
    (fun b1 c1 b2 c2 hEq => by
      by_contra hne
      exact hnone ⟨b1, c1, b2, c2, hne, hEq⟩)
    hbal

/-- Under injective deterministic postprocessing, predicate erasure is exactly
preserved.  Any repair that creates erasure by postprocessing must therefore
use a genuinely many-to-one map. -/
theorem finiteCoinOutputPredicateErasing_postcompose_iff_of_injective
    {Coin α β : Type*} [Fintype Coin] [DecidableEq α] [DecidableEq β]
    (r : Bool → Coin → α) (g : α → β)
    (hinj : Function.Injective g) :
    FiniteCoinOutputPredicateErasing (fun b c => g (r b c)) ↔
      FiniteCoinOutputPredicateErasing r := by
  constructor
  · intro herase
    exact finiteCoinOutputPredicateErasing_of_fiberBalanced r
      (finiteCoinRecodingFiberBalanced_of_postcompose_injective r g hinj
        ((finiteCoinRecodingFiberBalanced_iff_outputPredicateErasing
          (fun b c => g (r b c))).mpr herase))
  · exact finiteCoinOutputPredicateErasing_postcompose r g

/-- If a postprocessor is injective on the observed finite-coin support,
predicate erasure after postprocessing is equivalent to predicate erasure before
postprocessing. -/
theorem finiteCoinOutputPredicateErasing_postcompose_iff_of_observedInjective
    {Coin α β : Type*} [Fintype Coin] [DecidableEq α] [DecidableEq β]
    (r : Bool → Coin → α) (g : α → β)
    (hinjObs :
      ∀ b1 c1 b2 c2,
        g (r b1 c1) = g (r b2 c2) → r b1 c1 = r b2 c2) :
    FiniteCoinOutputPredicateErasing (fun b c => g (r b c)) ↔
      FiniteCoinOutputPredicateErasing r := by
  constructor
  · intro herase
    exact finiteCoinOutputPredicateErasing_of_fiberBalanced r
      (finiteCoinRecodingFiberBalanced_of_postcompose_observedInjective
        r g hinjObs
        ((finiteCoinRecodingFiberBalanced_iff_outputPredicateErasing
          (fun b c => g (r b c))).mpr herase))
  · exact finiteCoinOutputPredicateErasing_postcompose r g

/-- If a postprocessor has a left inverse on the observed finite-coin samples,
predicate erasure after postprocessing is equivalent to predicate erasure before
postprocessing. -/
theorem finiteCoinOutputPredicateErasing_postcompose_iff_of_observedLeftInverse
    {Coin α β : Type*} [Fintype Coin] [DecidableEq α] [DecidableEq β]
    (r : Bool → Coin → α) (g : α → β) (recover : β → α)
    (hrecover : ∀ b c, recover (g (r b c)) = r b c) :
    FiniteCoinOutputPredicateErasing (fun b c => g (r b c)) ↔
      FiniteCoinOutputPredicateErasing r := by
  constructor
  · intro herase
    exact finiteCoinOutputPredicateErasing_of_fiberBalanced r
      (finiteCoinRecodingFiberBalanced_of_postcompose_observedLeftInverse
        r g recover hrecover
        ((finiteCoinRecodingFiberBalanced_iff_outputPredicateErasing
          (fun b c => g (r b c))).mpr herase))
  · exact finiteCoinOutputPredicateErasing_postcompose r g

end Mettapedia.Computability.PNP
