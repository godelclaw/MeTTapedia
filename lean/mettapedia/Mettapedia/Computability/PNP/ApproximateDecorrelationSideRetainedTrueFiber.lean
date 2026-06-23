import Mettapedia.Computability.PNP.ApproximateDecorrelationSideRetainedBalance

namespace Mettapedia.Computability.PNP

/-- For a retained side channel, the true-side fiber at a fixed side value is
the true output/side equality class.  This generalizes the retained-coin
singleton calculation to arbitrary side information. -/
theorem coinTrueFiberCount_withSide_trueFiber
    {Coin α Side : Type*} [Fintype Coin] [DecidableEq α] [DecidableEq Side]
    (r : Bool → Coin → α) (side : Coin → Side) (c₀ : Coin) :
    coinTrueFiberCount (fun b c => (r b c, side c)) (r true c₀, side c₀) =
      finiteEventCount Coin
        (fun c => r true c = r true c₀ ∧ side c = side c₀) := by
  unfold coinTrueFiberCount
  exact finiteEventCount_congr_approximate (Ω := Coin) (fun c => by
    constructor
    · intro h
      exact ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩
    · intro h
      exact Prod.ext h.1 h.2)

/-- If a retained side-channel fiber has no false-side output matching the
selected true-side output, then the corresponding false-side pair fiber is
empty. -/
theorem coinFalseFiberCount_withSide_trueFiber_eq_zero_of_forall_ne
    {Coin α Side : Type*} [Fintype Coin] [DecidableEq α] [DecidableEq Side]
    (r : Bool → Coin → α) (side : Coin → Side) (c₀ : Coin)
    (hsep : ∀ c : Coin, side c = side c₀ → r false c ≠ r true c₀) :
    coinFalseFiberCount (fun b c => (r b c, side c)) (r true c₀, side c₀) = 0 := by
  unfold coinFalseFiberCount
  exact finiteEventCount_zero_of_forall_not
    (fun c => (r false c, side c) = (r true c₀, side c₀)) (fun c h => by
      have hside : side c = side c₀ := congrArg Prod.snd h
      have hout : r false c = r true c₀ := congrArg Prod.fst h
      exact hsep c hside hout)

/-- Exact forward defect for an arbitrary retained side-channel output fiber.
Keeping enough side information to isolate a true-side output from all
false-side outputs in that side fiber revives the source-product obstruction,
scaled by the true-side size of the selected side-channel fiber. -/
theorem countIndependentWithinForwardGap_sideRetained_trueFiber
    {Ω Coin α Side : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq α]
    [DecidableEq Side]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (side : Coin → Side) (c₀ : Coin)
    (hsep : ∀ c : Coin, side c = side c₀ → r false c ≠ r true c₀) :
    countIndependentWithinForwardGap (Ω := Ω × Coin)
        (fun xr => C xr.1) (fun xr => E xr.1)
        (fun xr => (r (decide (E xr.1)) xr.2, side xr.2) = (r true c₀, side c₀)) =
      finiteEventCount Ω (fun ω => C ω ∧ E ω) *
        finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω) *
          Fintype.card Coin *
            finiteEventCount Coin
              (fun c => r true c = r true c₀ ∧ side c = side c₀) := by
  have hgap :=
    countIndependentWithinForwardGap_finiteCoinRecoding_fiber
      C E (fun b c => (r b c, side c)) (r true c₀, side c₀)
  have htrue := coinTrueFiberCount_withSide_trueFiber r side c₀
  have hfalse := coinFalseFiberCount_withSide_trueFiber_eq_zero_of_forall_ne
    r side c₀ hsep
  simpa [htrue, hfalse, Nat.mul_assoc] using hgap

/-- Approximate independence of an output that retains a side channel forces
the tolerance to dominate the side-fiber source-product defect. -/
theorem sideChannelProduct_le_of_CountIndependentWithinToleranceOutput_sideRetained_trueFiber
    {Ω Coin α Side : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq α]
    [DecidableEq Side]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (side : Coin → Side) (c₀ : Coin) (τ : Nat)
    (hsep : ∀ c : Coin, side c = side c₀ → r false c ≠ r true c₀)
    (happrox : CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => (r (decide (E xr.1)) xr.2, side xr.2)) τ) :
    finiteEventCount Ω (fun ω => C ω ∧ E ω) *
      finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω) *
        Fintype.card Coin *
          finiteEventCount Coin
            (fun c => r true c = r true c₀ ∧ side c = side c₀) ≤ τ := by
  have hgap := countIndependentWithinForwardGap_sideRetained_trueFiber
    C E r side c₀ hsep
  have hcert :
      countIndependentWithinForwardGap (Ω := Ω × Coin)
          (fun xr => C xr.1) (fun xr => E xr.1)
          (fun xr => (r (decide (E xr.1)) xr.2, side xr.2) =
            (r true c₀, side c₀)) ≤ τ :=
    (happrox (r true c₀, side c₀)).1
  rw [hgap] at hcert
  exact hcert

/-- Source and side-fiber lower-bound form of the retained-side-channel
obstruction. -/
theorem sourceSideLowerBounds_product_le_of_CountIndependentWithinToleranceOutput_sideRetained_trueFiber
    {Ω Coin α Side : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq α]
    [DecidableEq Side]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (side : Coin → Side) (c₀ : Coin)
    (τ loTrue loFalse loSide : Nat)
    (hsep : ∀ c : Coin, side c = side c₀ → r false c ≠ r true c₀)
    (htrue : loTrue ≤ finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hfalse : loFalse ≤ finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω))
    (hside : loSide ≤ finiteEventCount Coin
      (fun c => r true c = r true c₀ ∧ side c = side c₀))
    (happrox : CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => (r (decide (E xr.1)) xr.2, side xr.2)) τ) :
    loTrue * loFalse * Fintype.card Coin * loSide ≤ τ := by
  exact le_trans
    (Nat.mul_le_mul
      (Nat.mul_le_mul_right (Fintype.card Coin) (Nat.mul_le_mul htrue hfalse))
      hside)
    (sideChannelProduct_le_of_CountIndependentWithinToleranceOutput_sideRetained_trueFiber
      C E r side c₀ τ hsep happrox)

/-- Strict-tolerance blocker for retained side-channel outputs. -/
theorem not_countIndependentWithinToleranceOutput_of_sideRetained_trueFiber_product_gt
    {Ω Coin α Side : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq α]
    [DecidableEq Side]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (side : Coin → Side) (c₀ : Coin) (τ : Nat)
    (hsep : ∀ c : Coin, side c = side c₀ → r false c ≠ r true c₀)
    (htol :
      τ <
        finiteEventCount Ω (fun ω => C ω ∧ E ω) *
          finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω) *
            Fintype.card Coin *
              finiteEventCount Coin
                (fun c => r true c = r true c₀ ∧ side c = side c₀)) :
    ¬ CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => (r (decide (E xr.1)) xr.2, side xr.2)) τ := by
  intro happrox
  exact (Nat.not_le_of_gt htol)
    (sideChannelProduct_le_of_CountIndependentWithinToleranceOutput_sideRetained_trueFiber
      C E r side c₀ τ hsep happrox)

/-- Source/side lower-bound strict-tolerance blocker for retained side-channel
outputs. -/
theorem not_countIndependentWithinToleranceOutput_of_sideRetained_trueFiber_sourceSideLowerBounds_mul_gt
    {Ω Coin α Side : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq α]
    [DecidableEq Side]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (side : Coin → Side) (c₀ : Coin)
    (τ loTrue loFalse loSide : Nat)
    (hsep : ∀ c : Coin, side c = side c₀ → r false c ≠ r true c₀)
    (htrue : loTrue ≤ finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hfalse : loFalse ≤ finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω))
    (hside : loSide ≤ finiteEventCount Coin
      (fun c => r true c = r true c₀ ∧ side c = side c₀))
    (htol : τ < loTrue * loFalse * Fintype.card Coin * loSide) :
    ¬ CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => (r (decide (E xr.1)) xr.2, side xr.2)) τ := by
  intro happrox
  exact (Nat.not_le_of_gt htol)
    (sourceSideLowerBounds_product_le_of_CountIndependentWithinToleranceOutput_sideRetained_trueFiber
      C E r side c₀ τ loTrue loFalse loSide hsep htrue hfalse hside happrox)

end Mettapedia.Computability.PNP
