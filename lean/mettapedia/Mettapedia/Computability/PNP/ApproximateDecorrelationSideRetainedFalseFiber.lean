import Mettapedia.Computability.PNP.ApproximateDecorrelationSideRetainedBalance

namespace Mettapedia.Computability.PNP

/-- For a retained side channel, the false-side fiber at a fixed side value is
the false output/side equality class. -/
theorem coinFalseFiberCount_withSide_falseFiber
    {Coin α Side : Type*} [Fintype Coin] [DecidableEq α] [DecidableEq Side]
    (r : Bool → Coin → α) (side : Coin → Side) (c₀ : Coin) :
    coinFalseFiberCount (fun b c => (r b c, side c)) (r false c₀, side c₀) =
      finiteEventCount Coin
        (fun c => r false c = r false c₀ ∧ side c = side c₀) := by
  unfold coinFalseFiberCount
  exact finiteEventCount_congr_approximate (Ω := Coin) (fun c => by
    constructor
    · intro h
      exact ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩
    · intro h
      exact Prod.ext h.1 h.2)

/-- If a retained side-channel fiber has no true-side output matching the
selected false-side output, then the corresponding true-side pair fiber is
empty. -/
theorem coinTrueFiberCount_withSide_falseFiber_eq_zero_of_forall_ne
    {Coin α Side : Type*} [Fintype Coin] [DecidableEq α] [DecidableEq Side]
    (r : Bool → Coin → α) (side : Coin → Side) (c₀ : Coin)
    (hsep : ∀ c : Coin, side c = side c₀ → r true c ≠ r false c₀) :
    coinTrueFiberCount (fun b c => (r b c, side c)) (r false c₀, side c₀) = 0 := by
  unfold coinTrueFiberCount
  exact finiteEventCount_zero_of_forall_not
    (fun c => (r true c, side c) = (r false c₀, side c₀)) (fun c h => by
      have hside : side c = side c₀ := congrArg Prod.snd h
      have hout : r true c = r false c₀ := congrArg Prod.fst h
      exact hsep c hside hout)

/-- Exact backward defect for an arbitrary retained side-channel false-side
output fiber.  This is the symmetric companion to
`countIndependentWithinForwardGap_sideRetained_trueFiber`. -/
theorem countIndependentWithinBackwardGap_sideRetained_falseFiber
    {Ω Coin α Side : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq α]
    [DecidableEq Side]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (side : Coin → Side) (c₀ : Coin)
    (hsep : ∀ c : Coin, side c = side c₀ → r true c ≠ r false c₀) :
    countIndependentWithinBackwardGap (Ω := Ω × Coin)
        (fun xr => C xr.1) (fun xr => E xr.1)
        (fun xr => (r (decide (E xr.1)) xr.2, side xr.2) = (r false c₀, side c₀)) =
      finiteEventCount Ω (fun ω => C ω ∧ E ω) *
        finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω) *
          Fintype.card Coin *
            finiteEventCount Coin
              (fun c => r false c = r false c₀ ∧ side c = side c₀) := by
  have hgap :=
    countIndependentWithinBackwardGap_finiteCoinRecoding_fiber
      C E (fun b c => (r b c, side c)) (r false c₀, side c₀)
  have hfalse := coinFalseFiberCount_withSide_falseFiber r side c₀
  have htrue := coinTrueFiberCount_withSide_falseFiber_eq_zero_of_forall_ne
    r side c₀ hsep
  simpa [htrue, hfalse, Nat.mul_assoc] using hgap

/-- Approximate independence of an output that retains a side channel forces
the tolerance to dominate a false-side side-fiber source-product defect. -/
theorem sideChannelProduct_le_of_CountIndependentWithinToleranceOutput_sideRetained_falseFiber
    {Ω Coin α Side : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq α]
    [DecidableEq Side]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (side : Coin → Side) (c₀ : Coin) (τ : Nat)
    (hsep : ∀ c : Coin, side c = side c₀ → r true c ≠ r false c₀)
    (happrox : CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => (r (decide (E xr.1)) xr.2, side xr.2)) τ) :
    finiteEventCount Ω (fun ω => C ω ∧ E ω) *
      finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω) *
        Fintype.card Coin *
          finiteEventCount Coin
            (fun c => r false c = r false c₀ ∧ side c = side c₀) ≤ τ := by
  have hgap := countIndependentWithinBackwardGap_sideRetained_falseFiber
    C E r side c₀ hsep
  have hcert :
      countIndependentWithinBackwardGap (Ω := Ω × Coin)
          (fun xr => C xr.1) (fun xr => E xr.1)
          (fun xr => (r (decide (E xr.1)) xr.2, side xr.2) =
            (r false c₀, side c₀)) ≤ τ :=
    (happrox (r false c₀, side c₀)).2
  rw [hgap] at hcert
  exact hcert

/-- Source and side-fiber lower-bound form of the false-side retained
side-channel obstruction. -/
theorem sourceSideLowerBounds_product_le_of_CountIndependentWithinToleranceOutput_sideRetained_falseFiber
    {Ω Coin α Side : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq α]
    [DecidableEq Side]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (side : Coin → Side) (c₀ : Coin)
    (τ loTrue loFalse loSide : Nat)
    (hsep : ∀ c : Coin, side c = side c₀ → r true c ≠ r false c₀)
    (htrue : loTrue ≤ finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hfalse : loFalse ≤ finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω))
    (hside : loSide ≤ finiteEventCount Coin
      (fun c => r false c = r false c₀ ∧ side c = side c₀))
    (happrox : CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => (r (decide (E xr.1)) xr.2, side xr.2)) τ) :
    loTrue * loFalse * Fintype.card Coin * loSide ≤ τ := by
  exact le_trans
    (Nat.mul_le_mul
      (Nat.mul_le_mul_right (Fintype.card Coin) (Nat.mul_le_mul htrue hfalse))
      hside)
    (sideChannelProduct_le_of_CountIndependentWithinToleranceOutput_sideRetained_falseFiber
      C E r side c₀ τ hsep happrox)

/-- Strict-tolerance blocker for retained side-channel false-side outputs. -/
theorem not_countIndependentWithinToleranceOutput_of_sideRetained_falseFiber_product_gt
    {Ω Coin α Side : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq α]
    [DecidableEq Side]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (side : Coin → Side) (c₀ : Coin) (τ : Nat)
    (hsep : ∀ c : Coin, side c = side c₀ → r true c ≠ r false c₀)
    (htol :
      τ <
        finiteEventCount Ω (fun ω => C ω ∧ E ω) *
          finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω) *
            Fintype.card Coin *
              finiteEventCount Coin
                (fun c => r false c = r false c₀ ∧ side c = side c₀)) :
    ¬ CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => (r (decide (E xr.1)) xr.2, side xr.2)) τ := by
  intro happrox
  exact (Nat.not_le_of_gt htol)
    (sideChannelProduct_le_of_CountIndependentWithinToleranceOutput_sideRetained_falseFiber
      C E r side c₀ τ hsep happrox)

/-- Source/side lower-bound strict-tolerance blocker for retained side-channel
false-side outputs. -/
theorem not_countIndependentWithinToleranceOutput_of_sideRetained_falseFiber_sourceSideLowerBounds_mul_gt
    {Ω Coin α Side : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq α]
    [DecidableEq Side]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (side : Coin → Side) (c₀ : Coin)
    (τ loTrue loFalse loSide : Nat)
    (hsep : ∀ c : Coin, side c = side c₀ → r true c ≠ r false c₀)
    (htrue : loTrue ≤ finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hfalse : loFalse ≤ finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω))
    (hside : loSide ≤ finiteEventCount Coin
      (fun c => r false c = r false c₀ ∧ side c = side c₀))
    (htol : τ < loTrue * loFalse * Fintype.card Coin * loSide) :
    ¬ CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => (r (decide (E xr.1)) xr.2, side xr.2)) τ := by
  intro happrox
  exact (Nat.not_le_of_gt htol)
    (sourceSideLowerBounds_product_le_of_CountIndependentWithinToleranceOutput_sideRetained_falseFiber
      C E r side c₀ τ loTrue loFalse loSide hsep htrue hfalse hside happrox)

end Mettapedia.Computability.PNP
