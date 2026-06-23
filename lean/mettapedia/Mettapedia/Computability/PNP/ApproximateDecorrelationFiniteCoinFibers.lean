import Mettapedia.Computability.PNP.ApproximateDecorrelationCoupledGaps
import Mettapedia.Computability.PNP.ApproximateDecorrelationCoupledTolerance
import Mettapedia.Computability.PNP.ApproximateDecorrelationCoupledFiberRecoding
import Mettapedia.Computability.PNP.ApproximateDecorrelationCoupledOutput
import Mathlib.Tactic.Ring

/-!
# Finite-coin recoding fiber counts and gaps
-/

namespace Mettapedia.Computability.PNP

/-- Count of the true-side part of an arbitrary finite-coin recoding fiber. -/
theorem finiteEventCount_finiteCoinRecoding_trueFiber
    {Ω Coin α : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq α]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (y : α) :
    finiteEventCount (Ω × Coin)
        (fun xr => C xr.1 ∧ E xr.1 ∧ r (decide (E xr.1)) xr.2 = y) =
      finiteEventCount Ω (fun ω => C ω ∧ E ω) * coinTrueFiberCount r y := by
  have hcongr :
      finiteEventCount (Ω × Coin)
          (fun xr => C xr.1 ∧ E xr.1 ∧ r (decide (E xr.1)) xr.2 = y) =
        finiteEventCount (Ω × Coin)
          (fun xr => (C xr.1 ∧ E xr.1) ∧ r true xr.2 = y) := by
    exact finiteEventCount_congr_approximate (Ω := Ω × Coin) (fun xr => by
      constructor
      · intro h
        exact ⟨⟨h.1, h.2.1⟩, by simpa [h.2.1] using h.2.2⟩
      · intro h
        exact ⟨h.1.1, h.1.2, by simpa [h.1.2] using h.2⟩)
  calc
    finiteEventCount (Ω × Coin)
        (fun xr => C xr.1 ∧ E xr.1 ∧ r (decide (E xr.1)) xr.2 = y)
        = finiteEventCount (Ω × Coin)
          (fun xr => (C xr.1 ∧ E xr.1) ∧ r true xr.2 = y) := hcongr
    _ = finiteEventCount Ω (fun ω => C ω ∧ E ω) * coinTrueFiberCount r y := by
          simpa [coinTrueFiberCount] using
            finiteEventCount_prod (Ω := Ω) (Coin := Coin)
              (fun ω => C ω ∧ E ω) (fun c => r true c = y)

/-- Count of the false-side part of an arbitrary finite-coin recoding fiber. -/
theorem finiteEventCount_finiteCoinRecoding_falseFiber
    {Ω Coin α : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq α]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (y : α) :
    finiteEventCount (Ω × Coin)
        (fun xr => C xr.1 ∧ ¬ E xr.1 ∧ r (decide (E xr.1)) xr.2 = y) =
      finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω) * coinFalseFiberCount r y := by
  have hcongr :
      finiteEventCount (Ω × Coin)
          (fun xr => C xr.1 ∧ ¬ E xr.1 ∧ r (decide (E xr.1)) xr.2 = y) =
        finiteEventCount (Ω × Coin)
          (fun xr => (C xr.1 ∧ ¬ E xr.1) ∧ r false xr.2 = y) := by
    exact finiteEventCount_congr_approximate (Ω := Ω × Coin) (fun xr => by
      constructor
      · intro h
        exact ⟨⟨h.1, h.2.1⟩, by simpa [h.2.1] using h.2.2⟩
      · intro h
        exact ⟨h.1.1, h.1.2, by simpa [h.1.2] using h.2⟩)
  calc
    finiteEventCount (Ω × Coin)
        (fun xr => C xr.1 ∧ ¬ E xr.1 ∧ r (decide (E xr.1)) xr.2 = y)
        = finiteEventCount (Ω × Coin)
          (fun xr => (C xr.1 ∧ ¬ E xr.1) ∧ r false xr.2 = y) := hcongr
    _ = finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω) * coinFalseFiberCount r y := by
          simpa [coinFalseFiberCount] using
            finiteEventCount_prod (Ω := Ω) (Coin := Coin)
              (fun ω => C ω ∧ ¬ E ω) (fun c => r false c = y)

/-- Count of an arbitrary finite-coin recoding fiber, split by the source bit.
This is the finite-count surface where randomized recodings can cancel: only
the balance of the two coin fibers matters. -/
theorem finiteEventCount_finiteCoinRecoding_fiber
    {Ω Coin α : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq α]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (y : α) :
    finiteEventCount (Ω × Coin)
        (fun xr => C xr.1 ∧ r (decide (E xr.1)) xr.2 = y) =
      finiteEventCount Ω (fun ω => C ω ∧ E ω) * coinTrueFiberCount r y +
        finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω) * coinFalseFiberCount r y := by
  have hsplit :=
    finiteEventCount_split_by_approximate
      (Ω := Ω × Coin)
      (fun xr => C xr.1 ∧ r (decide (E xr.1)) xr.2 = y)
      (fun xr => E xr.1)
  have htrue :
      finiteEventCount (Ω × Coin)
          (fun xr => (C xr.1 ∧ r (decide (E xr.1)) xr.2 = y) ∧ E xr.1) =
        finiteEventCount Ω (fun ω => C ω ∧ E ω) * coinTrueFiberCount r y := by
    have hcongr :
        finiteEventCount (Ω × Coin)
            (fun xr => (C xr.1 ∧ r (decide (E xr.1)) xr.2 = y) ∧ E xr.1) =
          finiteEventCount (Ω × Coin)
            (fun xr => C xr.1 ∧ E xr.1 ∧ r (decide (E xr.1)) xr.2 = y) := by
      exact finiteEventCount_congr_approximate (Ω := Ω × Coin) (fun xr => by
        constructor
        · intro h
          exact ⟨h.1.1, h.2, h.1.2⟩
        · intro h
          exact ⟨⟨h.1, h.2.2⟩, h.2.1⟩)
    simpa [hcongr] using finiteEventCount_finiteCoinRecoding_trueFiber C E r y
  have hfalse :
      finiteEventCount (Ω × Coin)
          (fun xr => (C xr.1 ∧ r (decide (E xr.1)) xr.2 = y) ∧ ¬ E xr.1) =
        finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω) * coinFalseFiberCount r y := by
    have hcongr :
        finiteEventCount (Ω × Coin)
            (fun xr => (C xr.1 ∧ r (decide (E xr.1)) xr.2 = y) ∧ ¬ E xr.1) =
          finiteEventCount (Ω × Coin)
            (fun xr => C xr.1 ∧ ¬ E xr.1 ∧ r (decide (E xr.1)) xr.2 = y) := by
      exact finiteEventCount_congr_approximate (Ω := Ω × Coin) (fun xr => by
        constructor
        · intro h
          exact ⟨h.1.1, h.2, h.1.2⟩
        · intro h
          exact ⟨⟨h.1, h.2.2⟩, h.2.1⟩)
    simpa [hcongr] using finiteEventCount_finiteCoinRecoding_falseFiber C E r y
  simpa [htrue, hfalse] using hsplit

/-- Exact forward defect for an arbitrary finite-coin recoding output fiber.
It is the source-fiber product times the number of coins times the positive
part of the true-minus-false coin-fiber imbalance. -/
theorem countIndependentWithinForwardGap_finiteCoinRecoding_fiber
    {Ω Coin α : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq α]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (y : α) :
    countIndependentWithinForwardGap (Ω := Ω × Coin)
        (fun xr => C xr.1) (fun xr => E xr.1)
        (fun xr => r (decide (E xr.1)) xr.2 = y) =
      finiteEventCount Ω (fun ω => C ω ∧ E ω) *
        finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω) *
          Fintype.card Coin *
            (coinTrueFiberCount r y - coinFalseFiberCount r y) := by
  let A := finiteEventCount Ω (fun ω => C ω ∧ E ω)
  let B := finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω)
  let N := Fintype.card Coin
  let T := coinTrueFiberCount r y
  let F := coinFalseFiberCount r y
  have hC :
      finiteEventCount (Ω × Coin) (fun xr => C xr.1) = (A + B) * N := by
    have hlift :=
      finiteEventCount_fst_lift (Ω := Ω) (Coin := Coin) C
    have hsplit := finiteEventCount_split_by_approximate (Ω := Ω) C E
    calc
      finiteEventCount (Ω × Coin) (fun xr => C xr.1)
          = finiteEventCount Ω C * Fintype.card Coin := hlift
      _ = (A + B) * N := by
            simp [A, B, N, hsplit]
  have hCE :
      finiteEventCount (Ω × Coin) (fun xr => C xr.1 ∧ E xr.1) = A * N := by
    simpa [A, N] using
      finiteEventCount_fst_lift (Ω := Ω) (Coin := Coin)
        (fun ω => C ω ∧ E ω)
  have hCEF :
      finiteEventCount (Ω × Coin)
          (fun xr => C xr.1 ∧ E xr.1 ∧
            r (decide (E xr.1)) xr.2 = y) = A * T := by
    simpa [A, T] using finiteEventCount_finiteCoinRecoding_trueFiber C E r y
  have hCF :
      finiteEventCount (Ω × Coin)
          (fun xr => C xr.1 ∧ r (decide (E xr.1)) xr.2 = y) =
        A * T + B * F := by
    simpa [A, B, T, F] using finiteEventCount_finiteCoinRecoding_fiber C E r y
  calc
    countIndependentWithinForwardGap (Ω := Ω × Coin)
        (fun xr => C xr.1) (fun xr => E xr.1)
        (fun xr => r (decide (E xr.1)) xr.2 = y)
        = ((A + B) * N) * (A * T) - (A * N) * (A * T + B * F) := by
          simp [countIndependentWithinForwardGap, hC, hCE, hCEF, hCF]
    _ = A * B * N * (T - F) := by
          calc
            ((A + B) * N) * (A * T) - (A * N) * (A * T + B * F)
                = (A * N) * ((A + B) * T) - (A * N) * (A * T + B * F) := by
                  ring_nf
            _ = (A * N) * (((A + B) * T) - (A * T + B * F)) := by
                  rw [Nat.mul_sub_left_distrib]
            _ = (A * N) * ((A * T + B * T) - (A * T + B * F)) := by
                  ring_nf
            _ = (A * N) * (B * T - B * F) := by
                  rw [Nat.add_sub_add_left]
            _ = (A * N) * (B * (T - F)) := by
                  rw [← Nat.mul_sub_left_distrib B T F]
            _ = A * B * N * (T - F) := by
                  ring_nf

/-- Exact backward defect for an arbitrary finite-coin recoding output fiber.
It is the source-fiber product times the number of coins times the positive
part of the false-minus-true coin-fiber imbalance. -/
theorem countIndependentWithinBackwardGap_finiteCoinRecoding_fiber
    {Ω Coin α : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq α]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (y : α) :
    countIndependentWithinBackwardGap (Ω := Ω × Coin)
        (fun xr => C xr.1) (fun xr => E xr.1)
        (fun xr => r (decide (E xr.1)) xr.2 = y) =
      finiteEventCount Ω (fun ω => C ω ∧ E ω) *
        finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω) *
          Fintype.card Coin *
            (coinFalseFiberCount r y - coinTrueFiberCount r y) := by
  let A := finiteEventCount Ω (fun ω => C ω ∧ E ω)
  let B := finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω)
  let N := Fintype.card Coin
  let T := coinTrueFiberCount r y
  let F := coinFalseFiberCount r y
  have hC :
      finiteEventCount (Ω × Coin) (fun xr => C xr.1) = (A + B) * N := by
    have hlift :=
      finiteEventCount_fst_lift (Ω := Ω) (Coin := Coin) C
    have hsplit := finiteEventCount_split_by_approximate (Ω := Ω) C E
    calc
      finiteEventCount (Ω × Coin) (fun xr => C xr.1)
          = finiteEventCount Ω C * Fintype.card Coin := hlift
      _ = (A + B) * N := by
            simp [A, B, N, hsplit]
  have hCE :
      finiteEventCount (Ω × Coin) (fun xr => C xr.1 ∧ E xr.1) = A * N := by
    simpa [A, N] using
      finiteEventCount_fst_lift (Ω := Ω) (Coin := Coin)
        (fun ω => C ω ∧ E ω)
  have hCEF :
      finiteEventCount (Ω × Coin)
          (fun xr => C xr.1 ∧ E xr.1 ∧
            r (decide (E xr.1)) xr.2 = y) = A * T := by
    simpa [A, T] using finiteEventCount_finiteCoinRecoding_trueFiber C E r y
  have hCF :
      finiteEventCount (Ω × Coin)
          (fun xr => C xr.1 ∧ r (decide (E xr.1)) xr.2 = y) =
        A * T + B * F := by
    simpa [A, B, T, F] using finiteEventCount_finiteCoinRecoding_fiber C E r y
  calc
    countIndependentWithinBackwardGap (Ω := Ω × Coin)
        (fun xr => C xr.1) (fun xr => E xr.1)
        (fun xr => r (decide (E xr.1)) xr.2 = y)
        = (A * N) * (A * T + B * F) - ((A + B) * N) * (A * T) := by
          simp [countIndependentWithinBackwardGap, hC, hCE, hCEF, hCF]
    _ = A * B * N * (F - T) := by
          calc
            (A * N) * (A * T + B * F) - ((A + B) * N) * (A * T)
                = (A * N) * (A * T + B * F) - (A * N) * ((A + B) * T) := by
                  ring_nf
            _ = (A * N) * ((A * T + B * F) - ((A + B) * T)) := by
                  rw [Nat.mul_sub_left_distrib]
            _ = (A * N) * ((A * T + B * F) - (A * T + B * T)) := by
                  ring_nf
            _ = (A * N) * (B * F - B * T) := by
                  rw [Nat.add_sub_add_left]
            _ = (A * N) * (B * (F - T)) := by
                  rw [← Nat.mul_sub_left_distrib B F T]
            _ = A * B * N * (F - T) := by
                  ring_nf

/-- Balanced finite-coin output fibers exactly decorrelate the marginal output
from the same source bit at zero tolerance.  This theorem is the formal
cancellation case: if every output value occurs equally often on the true and
false source sides, the output variable alone no longer carries finite-count
fiber evidence for `E`. -/
theorem countIndependentWithinToleranceOutput_zero_of_finiteCoinRecoding_fiberBalanced
    {Ω Coin α : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq α]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α)
    (hbal : FiniteCoinRecodingFiberBalanced r) :
    CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => r (decide (E xr.1)) xr.2) 0 := by
  intro y
  constructor
  · rw [countIndependentWithinForwardGap_finiteCoinRecoding_fiber]
    simp [hbal y]
  · rw [countIndependentWithinBackwardGap_finiteCoinRecoding_fiber]
    simp [hbal y]

end Mettapedia.Computability.PNP
