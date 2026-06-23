import Mettapedia.Computability.PNP.ApproximateDecorrelationFiniteCoinFibers

/-!
# Balanced finite-coin recoding evidence boundaries
-/

namespace Mettapedia.Computability.PNP

/-- The true-side fiber containing the output produced at a particular coin is
nonempty, hence has positive finite count. -/
theorem coinTrueFiberCount_self_pos
    {Coin α : Type*} [Fintype Coin] [DecidableEq α]
    (r : Bool → Coin → α) (c₀ : Coin) :
    0 < coinTrueFiberCount r (r true c₀) := by
  unfold coinTrueFiberCount finiteEventCount
  exact Fintype.card_pos_iff.mpr ⟨⟨c₀, rfl⟩⟩

/-- A balanced finite-coin marginal recoding cannot have an output property
that separates the source bit at a particular coin.  If all true-side outputs
satisfy `P` and all false-side outputs fail `P`, the true-side fiber of
`r true c₀` is nonempty while the corresponding false-side fiber is empty,
contradicting balance. -/
theorem not_finiteCoinRecodingFiberBalanced_of_outputPredicate_separates_at_coin
    {Coin α : Type*} [Fintype Coin] [DecidableEq α]
    (r : Bool → Coin → α) (P : α → Prop) (c₀ : Coin)
    (htrue : ∀ c : Coin, P (r true c))
    (hfalse : ∀ c : Coin, ¬ P (r false c)) :
    ¬ FiniteCoinRecodingFiberBalanced r := by
  intro hbal
  let y := r true c₀
  have hfalseEmpty : coinFalseFiberCount r y = 0 := by
    unfold coinFalseFiberCount
    exact finiteEventCount_zero_of_forall_not
      (fun c => r false c = y) (fun c hc => by
        exact hfalse c (by simpa [hc] using htrue c₀))
  have htrueZero : coinTrueFiberCount r y = 0 := by
    exact (hbal y).trans hfalseEmpty
  exact (Nat.ne_of_gt (coinTrueFiberCount_self_pos r c₀)) htrueZero

/-- Nonempty balanced finite-coin marginal recodings cannot have any
output-only predicate that separates the source bit uniformly on all coins. -/
theorem not_finiteCoinRecodingFiberBalanced_of_outputPredicate_separates
    {Coin α : Type*} [Fintype Coin] [Nonempty Coin] [DecidableEq α]
    (r : Bool → Coin → α) (P : α → Prop)
    (htrue : ∀ c : Coin, P (r true c))
    (hfalse : ∀ c : Coin, ¬ P (r false c)) :
    ¬ FiniteCoinRecodingFiberBalanced r := by
  obtain ⟨c₀⟩ := ‹Nonempty Coin›
  exact
    not_finiteCoinRecodingFiberBalanced_of_outputPredicate_separates_at_coin
      r P c₀ htrue hfalse

/-- A balanced finite-coin marginal recoding cannot also have an output-only
Boolean decoder that recovers the source bit at a particular coin.  If the
decoder maps every true-side output to `true` and every false-side output to
`false`, the true-side fiber of `r true c₀` is nonempty while the corresponding
false-side fiber is empty, contradicting balance. -/
theorem not_finiteCoinRecodingFiberBalanced_of_outputDecoder_recovers_at_coin
    {Coin α : Type*} [Fintype Coin] [DecidableEq α]
    (r : Bool → Coin → α) (decode : α → Bool) (c₀ : Coin)
    (htrue : ∀ c : Coin, decode (r true c) = true)
    (hfalse : ∀ c : Coin, decode (r false c) = false) :
    ¬ FiniteCoinRecodingFiberBalanced r := by
  exact
    not_finiteCoinRecodingFiberBalanced_of_outputPredicate_separates_at_coin
      r (fun y => decode y = true) c₀ htrue (fun c h => by
        have hdecodeFalse : decode (r false c) = false := hfalse c
        rw [h] at hdecodeFalse
        cases hdecodeFalse)

/-- Nonempty balanced finite-coin marginal recodings cannot have an output-only
Boolean decoder that recovers the source bit uniformly on all coins.  The only
way for balanced marginal fibers to decorrelate exactly is to erase such
output-only source evidence. -/
theorem not_finiteCoinRecodingFiberBalanced_of_outputDecoder_recovers
    {Coin α : Type*} [Fintype Coin] [Nonempty Coin] [DecidableEq α]
    (r : Bool → Coin → α) (decode : α → Bool)
    (htrue : ∀ c : Coin, decode (r true c) = true)
    (hfalse : ∀ c : Coin, decode (r false c) = false) :
    ¬ FiniteCoinRecodingFiberBalanced r := by
  obtain ⟨c₀⟩ := ‹Nonempty Coin›
  exact
    not_finiteCoinRecodingFiberBalanced_of_outputDecoder_recovers_at_coin
      r decode c₀ htrue hfalse

/-- Balanced finite-coin marginal recodings give every output-only predicate
the same number of true-side and false-side coin witnesses.  Thus the balanced
escape can preserve only source-blind output statistics; any predicate-level
advantage for either source bit contradicts fiber balance. -/
theorem finiteCoinRecodingFiberBalanced_outputPredicate_count_eq
    {Coin α : Type*} [Fintype Coin] [DecidableEq α]
    (r : Bool → Coin → α) (P : α → Prop) [DecidablePred P]
    (hbal : FiniteCoinRecodingFiberBalanced r) :
    finiteEventCount Coin (fun c => P (r true c)) =
      finiteEventCount Coin (fun c => P (r false c)) := by
  classical
  let s : Finset α :=
    (Finset.univ.image (fun c : Coin => r true c)) ∪
      (Finset.univ.image (fun c : Coin => r false c))
  have htrueRange : ∀ c : Coin, r true c ∈ s := by
    intro c
    exact Finset.mem_union.mpr
      (Or.inl (Finset.mem_image.mpr ⟨c, Finset.mem_univ c, rfl⟩))
  have hfalseRange : ∀ c : Coin, r false c ∈ s := by
    intro c
    exact Finset.mem_union.mpr
      (Or.inr (Finset.mem_image.mpr ⟨c, Finset.mem_univ c, rfl⟩))
  rw [finiteEventCount_comp_eq_sum_fibers_of_mapsTo
        (fun c : Coin => r true c) s P htrueRange,
      finiteEventCount_comp_eq_sum_fibers_of_mapsTo
        (fun c : Coin => r false c) s P hfalseRange]
  refine Finset.sum_congr rfl ?_
  intro y _hy
  simpa [coinTrueFiberCount, coinFalseFiberCount] using hbal y

/-- A true-side advantage for any decidable output predicate is incompatible
with balanced finite-coin recoding fibers. -/
theorem not_finiteCoinRecodingFiberBalanced_of_outputPredicate_trueCount_gt_falseCount
    {Coin α : Type*} [Fintype Coin] [DecidableEq α]
    (r : Bool → Coin → α) (P : α → Prop) [DecidablePred P]
    (hgt : finiteEventCount Coin (fun c => P (r false c)) <
      finiteEventCount Coin (fun c => P (r true c))) :
    ¬ FiniteCoinRecodingFiberBalanced r := by
  intro hbal
  exact (Nat.ne_of_gt hgt)
    (finiteCoinRecodingFiberBalanced_outputPredicate_count_eq r P hbal)

/-- A false-side advantage for any decidable output predicate is incompatible
with balanced finite-coin recoding fibers. -/
theorem not_finiteCoinRecodingFiberBalanced_of_outputPredicate_falseCount_gt_trueCount
    {Coin α : Type*} [Fintype Coin] [DecidableEq α]
    (r : Bool → Coin → α) (P : α → Prop) [DecidablePred P]
    (hgt : finiteEventCount Coin (fun c => P (r true c)) <
      finiteEventCount Coin (fun c => P (r false c))) :
    ¬ FiniteCoinRecodingFiberBalanced r := by
  intro hbal
  exact (Nat.ne_of_gt hgt)
    (finiteCoinRecodingFiberBalanced_outputPredicate_count_eq r P hbal).symm

/-- A balanced finite-coin marginal recoding gives every Boolean output
decoder exactly half aggregate accuracy across the two source sides.  Written
without division: the number of true-side coins decoded as `true` plus the
number of false-side coins decoded as `false` is exactly the coin count. -/
theorem finiteCoinRecodingFiberBalanced_outputDecoder_correctCount_eq_card
    {Coin α : Type*} [Fintype Coin] [DecidableEq α]
    (r : Bool → Coin → α) (decode : α → Bool)
    (hbal : FiniteCoinRecodingFiberBalanced r) :
    finiteEventCount Coin (fun c => decode (r true c) = true) +
      finiteEventCount Coin (fun c => decode (r false c) = false) =
        Fintype.card Coin := by
  have hpred :=
    finiteCoinRecodingFiberBalanced_outputPredicate_count_eq
      r (fun y => decode y = true) hbal
  rw [hpred]
  exact finiteEventCount_bool_true_add_false (fun c => decode (r false c))

/-- Any Boolean output decoder with better-than-half aggregate accuracy across
the two source sides contradicts balanced finite-coin recoding fibers. -/
theorem not_finiteCoinRecodingFiberBalanced_of_outputDecoder_correctCount_gt_card
    {Coin α : Type*} [Fintype Coin] [DecidableEq α]
    (r : Bool → Coin → α) (decode : α → Bool)
    (hgt : Fintype.card Coin <
      finiteEventCount Coin (fun c => decode (r true c) = true) +
        finiteEventCount Coin (fun c => decode (r false c) = false)) :
    ¬ FiniteCoinRecodingFiberBalanced r := by
  intro hbal
  exact (Nat.ne_of_gt hgt)
    (finiteCoinRecodingFiberBalanced_outputDecoder_correctCount_eq_card
      r decode hbal)


end Mettapedia.Computability.PNP
