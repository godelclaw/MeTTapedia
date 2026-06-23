import Mettapedia.Computability.PNP.ApproximateDecorrelationCoinRetained

namespace Mettapedia.Computability.PNP

/-- For a retained side channel, a true pair fiber is the simultaneous output
and side equality class on the true source side. -/
theorem coinTrueFiberCount_withSide
    {Coin α Side : Type*} [Fintype Coin] [DecidableEq α] [DecidableEq Side]
    (r : Bool → Coin → α) (side : Coin → Side) (y : α) (s : Side) :
    coinTrueFiberCount (fun b c => (r b c, side c)) (y, s) =
      finiteEventCount Coin (fun c => r true c = y ∧ side c = s) := by
  unfold coinTrueFiberCount
  exact finiteEventCount_congr_approximate (Ω := Coin) (fun c => by
    constructor
    · intro h
      exact ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩
    · intro h
      exact Prod.ext h.1 h.2)

/-- For a retained side channel, a false pair fiber is the simultaneous output
and side equality class on the false source side. -/
theorem coinFalseFiberCount_withSide
    {Coin α Side : Type*} [Fintype Coin] [DecidableEq α] [DecidableEq Side]
    (r : Bool → Coin → α) (side : Coin → Side) (y : α) (s : Side) :
    coinFalseFiberCount (fun b c => (r b c, side c)) (y, s) =
      finiteEventCount Coin (fun c => r false c = y ∧ side c = s) := by
  unfold coinFalseFiberCount
  exact finiteEventCount_congr_approximate (Ω := Coin) (fun c => by
    constructor
    · intro h
      exact ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩
    · intro h
      exact Prod.ext h.1 h.2)

/-- Retaining an arbitrary side channel turns balanced recoding fibers into
side-fiber balance: for every certified output and retained side value, the
true and false coin counts inside that side fiber must agree. -/
theorem finiteCoinRecodingFiberBalanced_sideRetained_iff_sideFiber_count_eq
    {Coin α Side : Type*} [Fintype Coin] [DecidableEq α] [DecidableEq Side]
    (r : Bool → Coin → α) (side : Coin → Side) :
    FiniteCoinRecodingFiberBalanced (fun b c => (r b c, side c)) ↔
      ∀ (y : α) (s : Side),
        finiteEventCount Coin (fun c => r true c = y ∧ side c = s) =
          finiteEventCount Coin (fun c => r false c = y ∧ side c = s) := by
  constructor
  · intro hbal y s
    calc
      finiteEventCount Coin (fun c => r true c = y ∧ side c = s) =
          coinTrueFiberCount (fun b c => (r b c, side c)) (y, s) := by
        exact (coinTrueFiberCount_withSide r side y s).symm
      _ = coinFalseFiberCount (fun b c => (r b c, side c)) (y, s) :=
        hbal (y, s)
      _ = finiteEventCount Coin (fun c => r false c = y ∧ side c = s) := by
        exact coinFalseFiberCount_withSide r side y s
  · intro hside ys
    rcases ys with ⟨y, s⟩
    calc
      coinTrueFiberCount (fun b c => (r b c, side c)) (y, s) =
          finiteEventCount Coin (fun c => r true c = y ∧ side c = s) := by
        exact coinTrueFiberCount_withSide r side y s
      _ = finiteEventCount Coin (fun c => r false c = y ∧ side c = s) :=
        hside y s
      _ = coinFalseFiberCount (fun b c => (r b c, side c)) (y, s) := by
        exact (coinFalseFiberCount_withSide r side y s).symm

/-- Source lower-bound retained-side quantization: below one lower-bounded
source/coin block, approximate independence of the output retaining side
information is equivalent to exact true/false balance inside every
output/side fiber. -/
theorem countIndependentWithinToleranceOutput_sideRetained_sourceLowerBounds_lt_coinProduct_iff_sideFiber_count_eq
    {Ω Coin α Side : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq α]
    [DecidableEq Side]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (side : Coin → Side) {τ loTrue loFalse : Nat}
    (htrue : loTrue ≤ finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hfalse : loFalse ≤ finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω))
    (hlt : τ < loTrue * loFalse * Fintype.card Coin) :
    CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => (r (decide (E xr.1)) xr.2, side xr.2)) τ ↔
    ∀ (y : α) (s : Side),
      finiteEventCount Coin (fun c => r true c = y ∧ side c = s) =
        finiteEventCount Coin (fun c => r false c = y ∧ side c = s) := by
  calc
    CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
        (fun xr => C xr.1) (fun xr => E xr.1)
        (fun xr => (r (decide (E xr.1)) xr.2, side xr.2)) τ
        ↔ FiniteCoinRecodingFiberBalanced (fun b c => (r b c, side c)) :=
          countIndependentWithinToleranceOutput_sourceLowerBounds_lt_coinProduct_iff_finiteCoinRecoding_fiberBalanced
            C E (fun b c => (r b c, side c)) htrue hfalse hlt
    _ ↔ ∀ (y : α) (s : Side),
          finiteEventCount Coin (fun c => r true c = y ∧ side c = s) =
            finiteEventCount Coin (fun c => r false c = y ∧ side c = s) :=
          finiteCoinRecodingFiberBalanced_sideRetained_iff_sideFiber_count_eq r side

/-- Exact source-count specialization of retained-side quantization. -/
theorem countIndependentWithinToleranceOutput_sideRetained_lt_sourceCoinProduct_iff_sideFiber_count_eq
    {Ω Coin α Side : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq α]
    [DecidableEq Side]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (side : Coin → Side) {τ : Nat}
    (hlt :
      τ <
        finiteEventCount Ω (fun ω => C ω ∧ E ω) *
          finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω) *
            Fintype.card Coin) :
    CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => (r (decide (E xr.1)) xr.2, side xr.2)) τ ↔
    ∀ (y : α) (s : Side),
      finiteEventCount Coin (fun c => r true c = y ∧ side c = s) =
        finiteEventCount Coin (fun c => r false c = y ∧ side c = s) := by
  exact
    countIndependentWithinToleranceOutput_sideRetained_sourceLowerBounds_lt_coinProduct_iff_sideFiber_count_eq
      C E r side le_rfl le_rfl hlt

end Mettapedia.Computability.PNP
