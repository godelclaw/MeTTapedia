import Mettapedia.Computability.PNP.ConditioningObstructionLabelFiber
import Mettapedia.Computability.PNP.ConditioningObstructionCountIndependence
import Mettapedia.Computability.PNP.ConditioningObstructionBoolRecoding
import Mettapedia.Computability.PNP.ConditioningObstructionAnyRecoding
import Mettapedia.Computability.PNP.ConditioningObstructionBoolPair

/-!
# P vs NP crux: approximate decorrelation has a finite-count lower bound

The exact conditioning obstruction says that deterministic coupling or
anti-coupling inside a conditioning event destroys the cross-multiplied
finite-count independence equation unless the conditioned source bit is
degenerate.  This file records the quantitative version needed to audit
``approximate decorrelation'' repairs.

Instead of merely saying that exact independence fails, we define the two
oriented natural-number defects of the cross-multiplied equation.  A coupled
conditioned bit has forward defect exactly
`#(C ∩ E) * #(C ∩ ¬ E)`, while an anti-coupled bit has the same product as
backward defect.  Any approximate replacement must therefore bound this
explicit product; it cannot repair the conditioning step by renaming exact
independence as approximate independence.
-/

namespace Mettapedia.Computability.PNP

/-- The forward oriented defect of the conditional finite-count independence
equation.  It is zero when the left cross product is no larger than the right
cross product, and otherwise records the natural-number excess. -/
def countIndependentWithinForwardGap {Ω : Type*} [Fintype Ω]
    (C E F : Ω → Prop) [DecidablePred C] [DecidablePred E] [DecidablePred F] :
    Nat :=
  finiteEventCount Ω C * finiteEventCount Ω (fun ω => C ω ∧ E ω ∧ F ω) -
    finiteEventCount Ω (fun ω => C ω ∧ E ω) *
      finiteEventCount Ω (fun ω => C ω ∧ F ω)

/-- The backward oriented defect of the conditional finite-count independence
equation.  Together with the forward defect, this gives a division-free
finite-count notion of symmetric tolerance around exact independence. -/
def countIndependentWithinBackwardGap {Ω : Type*} [Fintype Ω]
    (C E F : Ω → Prop) [DecidablePred C] [DecidablePred E] [DecidablePred F] :
    Nat :=
  finiteEventCount Ω (fun ω => C ω ∧ E ω) *
      finiteEventCount Ω (fun ω => C ω ∧ F ω) -
    finiteEventCount Ω C * finiteEventCount Ω (fun ω => C ω ∧ E ω ∧ F ω)

/-- Symmetric finite-count approximate conditional independence with tolerance
`τ`: both oriented cross-multiplied defects are bounded by `τ`. -/
def CountIndependentWithinTolerance {Ω : Type*} [Fintype Ω]
    (C E F : Ω → Prop) [DecidablePred C] [DecidablePred E] [DecidablePred F]
    (τ : Nat) : Prop :=
  countIndependentWithinForwardGap (Ω := Ω) C E F ≤ τ ∧
    countIndependentWithinBackwardGap (Ω := Ω) C E F ≤ τ

/-- Output-variable form of symmetric finite-count approximate conditional
independence: every decidable output fiber of `Y` is independent of `E` inside
`C`, up to the same tolerance `τ`.  This prevents a repair from hiding an
informative recoding by certifying only the aggregate output variable. -/
def CountIndependentWithinToleranceOutput {Ω α : Type*} [Fintype Ω]
    [DecidableEq α]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (Y : Ω → α) (τ : Nat) : Prop :=
  ∀ y : α, CountIndependentWithinTolerance (Ω := Ω) C E (fun ω => Y ω = y) τ

/-- The product of the two source-bit fibers inside the conditioning event.
This is the exact finite-count obstruction term that an approximate
decorrelation theorem must dominate on coupled same-source surfaces. -/
def conditionedSourceFiberProduct {Ω : Type*} [Fintype Ω]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E] : Nat :=
  finiteEventCount Ω (fun ω => C ω ∧ E ω) *
    finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω)

private noncomputable def approximateEventSplitEquiv {Ω : Type*}
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E] :
    {ω : Ω // C ω} ≃
      ({ω : Ω // C ω ∧ E ω} ⊕ {ω : Ω // C ω ∧ ¬ E ω}) where
  toFun ω :=
    if hE : E ω.1 then Sum.inl ⟨ω.1, ⟨ω.2, hE⟩⟩
    else Sum.inr ⟨ω.1, ⟨ω.2, hE⟩⟩
  invFun ω :=
    match ω with
    | Sum.inl h => ⟨h.1, h.2.1⟩
    | Sum.inr h => ⟨h.1, h.2.1⟩
  left_inv ω := by
    rcases ω with ⟨ω, hC⟩
    by_cases hE : E ω <;> simp [hE]
  right_inv ω := by
    cases ω with
    | inl h =>
        rcases h with ⟨ω, hC, hE⟩
        simp [hE]
    | inr h =>
        rcases h with ⟨ω, hC, hE⟩
        simp [hE]

theorem finiteEventCount_split_by_approximate {Ω : Type*} [Fintype Ω]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E] :
    finiteEventCount Ω C =
      finiteEventCount Ω (fun ω => C ω ∧ E ω) +
        finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω) := by
  classical
  simpa [finiteEventCount, Fintype.card_sum] using
    Fintype.card_congr (approximateEventSplitEquiv C E)

theorem finiteEventCount_congr_approximate {Ω : Type*} [Fintype Ω]
    {E F : Ω → Prop} [DecidablePred E] [DecidablePred F]
    (h : ∀ ω, E ω ↔ F ω) :
    finiteEventCount Ω E = finiteEventCount Ω F := by
  exact le_antisymm
    (finiteEventCount_le_of_imp (fun ω hE => (h ω).1 hE))
    (finiteEventCount_le_of_imp (fun ω hF => (h ω).2 hF))

private noncomputable def fstLiftEventEquiv {Ω Coin : Type*}
    (P : Ω → Prop) [DecidablePred P] :
    {xr : Ω × Coin // P xr.1} ≃ ({ω : Ω // P ω} × Coin) where
  toFun xr := (⟨xr.1.1, xr.2⟩, xr.1.2)
  invFun pc := ⟨(pc.1.1, pc.2), pc.1.2⟩
  left_inv xr := by
    rcases xr with ⟨⟨ω, c⟩, hP⟩
    rfl
  right_inv pc := by
    rcases pc with ⟨⟨ω, hP⟩, c⟩
    rfl

/-- Counting a source-only event on a source/coin product factors as the source
event count times the number of coins. -/
theorem finiteEventCount_fst_lift
    {Ω Coin : Type*} [Fintype Ω] [Fintype Coin]
    (P : Ω → Prop) [DecidablePred P] :
    finiteEventCount (Ω × Coin) (fun xr => P xr.1) =
      finiteEventCount Ω P * Fintype.card Coin := by
  classical
  simpa [finiteEventCount] using
    Fintype.card_congr (fstLiftEventEquiv (Ω := Ω) (Coin := Coin) P)

/-- Source-only positivity lifts to a source/coin product as soon as the finite
coin space is nonempty. -/
theorem finiteEventCount_fst_lift_pos_of_pos
    {Ω Coin : Type*} [Fintype Ω] [Fintype Coin] [Nonempty Coin]
    (P : Ω → Prop) [DecidablePred P]
    (hpos : 0 < finiteEventCount Ω P) :
    0 < finiteEventCount (Ω × Coin) (fun xr => P xr.1) := by
  rw [finiteEventCount_fst_lift (Ω := Ω) (Coin := Coin) P]
  exact Nat.mul_pos hpos Fintype.card_pos

private noncomputable def prodEventEquiv {Ω Coin : Type*}
    (P : Ω → Prop) (Q : Coin → Prop) [DecidablePred P] [DecidablePred Q] :
    {xr : Ω × Coin // P xr.1 ∧ Q xr.2} ≃
      ({ω : Ω // P ω} × {c : Coin // Q c}) where
  toFun xr := (⟨xr.1.1, xr.2.1⟩, ⟨xr.1.2, xr.2.2⟩)
  invFun pc := ⟨(pc.1.1, pc.2.1), pc.1.2, pc.2.2⟩
  left_inv xr := by
    rcases xr with ⟨⟨ω, c⟩, hP, hQ⟩
    rfl
  right_inv pc := by
    rcases pc with ⟨⟨ω, hP⟩, ⟨c, hQ⟩⟩
    rfl

/-- Counting a rectangular event on a finite product factors as the product of
the two event counts. -/
theorem finiteEventCount_prod
    {Ω Coin : Type*} [Fintype Ω] [Fintype Coin]
    (P : Ω → Prop) (Q : Coin → Prop) [DecidablePred P] [DecidablePred Q] :
    finiteEventCount (Ω × Coin) (fun xr => P xr.1 ∧ Q xr.2) =
      finiteEventCount Ω P * finiteEventCount Coin Q := by
  classical
  simpa [finiteEventCount] using
    Fintype.card_congr (prodEventEquiv (Ω := Ω) (Coin := Coin) P Q)

/-- Number of coin values for which an output fiber `y` is selected when the
source bit is `true`. -/
def coinTrueFiberCount {Coin α : Type*} [Fintype Coin] [DecidableEq α]
    (r : Bool → Coin → α) (y : α) : Nat :=
  finiteEventCount Coin (fun c => r true c = y)

/-- Number of coin values for which an output fiber `y` is selected when the
source bit is `false`. -/
def coinFalseFiberCount {Coin α : Type*} [Fintype Coin] [DecidableEq α]
    (r : Bool → Coin → α) (y : α) : Nat :=
  finiteEventCount Coin (fun c => r false c = y)

/-- A finite-coin recoding has balanced output fibers when every output value
appears equally often on the true and false source sides.  This is the exact
finite-count cancellation condition for the same-source randomized recoding
surface. -/
def FiniteCoinRecodingFiberBalanced {Coin α : Type*} [Fintype Coin] [DecidableEq α]
    (r : Bool → Coin → α) : Prop :=
  ∀ y : α, coinTrueFiberCount r y = coinFalseFiberCount r y

/-- The finite count of a singleton equality event is one. -/
theorem finiteEventCount_eq_self
    {α : Type*} [Fintype α] [DecidableEq α] (a : α) :
    finiteEventCount α (fun x => x = a) = 1 := by
  classical
  simp [finiteEventCount]

/-- If an event is pointwise false, its finite event count is zero. -/
theorem finiteEventCount_zero_of_forall_not
    {Ω : Type*} [Fintype Ω] (P : Ω → Prop) [DecidablePred P]
    (hfalse : ∀ ω, ¬ P ω) :
    finiteEventCount Ω P = 0 := by
  have hcongr :
      finiteEventCount Ω P = finiteEventCount Ω (fun _ω => False) := by
    exact finiteEventCount_congr_approximate (Ω := Ω) (fun ω => by
      constructor
      · intro h
        exact False.elim (hfalse ω h)
      · intro h
        cases h)
  simpa [finiteEventCount] using hcongr

/-- Count the preimage of an output predicate by summing the counts of its
output fibers over any finite support containing the image of the map.  This is
the aggregate form needed for randomized recodings whose output type need not
itself be finite. -/
theorem finiteEventCount_comp_eq_sum_fibers_of_mapsTo
    {Coin α : Type*} [Fintype Coin] [DecidableEq α]
    (r : Coin → α) (s : Finset α) (P : α → Prop) [DecidablePred P]
    (hr : ∀ c : Coin, r c ∈ s) :
    finiteEventCount Coin (fun c => P (r c)) =
      ∑ y ∈ s.filter P, finiteEventCount Coin (fun c => r c = y) := by
  classical
  have hfiber := Finset.sum_card_fiberwise_eq_card_filter
    (s := (Finset.univ : Finset Coin))
    (t := (s.filter P : Finset α))
    (g := r)
  symm
  calc
    ∑ y ∈ s.filter P, finiteEventCount Coin (fun c => r c = y)
        = ∑ y ∈ s.filter P,
            ((Finset.univ : Finset Coin).filter (fun c => r c = y)).card := by
          refine Finset.sum_congr rfl ?_
          intro y _hy
          simpa [finiteEventCount] using
            (Fintype.card_subtype (fun c : Coin => r c = y))
    _ = ((Finset.univ : Finset Coin).filter (fun c => r c ∈ s.filter P)).card := hfiber
    _ = finiteEventCount Coin (fun c => P (r c)) := by
          simpa [finiteEventCount, Finset.mem_filter, hr] using
            (Fintype.card_subtype (fun c : Coin => P (r c))).symm

/-- A Boolean-valued event partitions a finite type into its `true` and
`false` fibers. -/
theorem finiteEventCount_bool_true_add_false
    {Ω : Type*} [Fintype Ω] (B : Ω → Bool) :
    finiteEventCount Ω (fun ω => B ω = true) +
      finiteEventCount Ω (fun ω => B ω = false) = Fintype.card Ω := by
  have hsplit :=
    finiteEventCount_split_by_approximate (Ω := Ω)
      (fun _ω => True) (fun ω => B ω = true)
  have htruePart :
      finiteEventCount Ω (fun ω => True ∧ B ω = true) =
        finiteEventCount Ω (fun ω => B ω = true) := by
    exact finiteEventCount_congr_approximate (Ω := Ω) (fun _ω => by simp)
  have hfalsePart :
      finiteEventCount Ω (fun ω => True ∧ ¬ B ω = true) =
        finiteEventCount Ω (fun ω => B ω = false) := by
    exact finiteEventCount_congr_approximate (Ω := Ω) (fun ω => by
      cases B ω <;> simp)
  have htrueAll : finiteEventCount Ω (fun _ω => True) = Fintype.card Ω := by
    simp [finiteEventCount]
  rw [htrueAll, htruePart, hfalsePart] at hsplit
  exact hsplit.symm

end Mettapedia.Computability.PNP
