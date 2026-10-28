import Mettapedia.Computability.PNP.ConditioningObstructionLabelFiber

open scoped BigOperators

/-!
## Conditioning can also destroy independence

The previous section shows collapse of a uniform label map after conditioning on
one label fiber.  The Boolean countermodel below records the sharper v11-style
audit point: even exact unconditioned independence between two coordinates need
not survive conditioning on a promise event that couples them.
-/

namespace Mettapedia.Computability.PNP

/-- Uniform-count independence: `E` and `F` satisfy the cross-multiplied
finite-probability independence equation. -/
def CountIndependent {Ω : Type*} [Fintype Ω]
    (E F : Ω → Prop) [DecidablePred E] [DecidablePred F]
    [DecidablePred (fun ω => E ω ∧ F ω)] : Prop :=
  Fintype.card Ω * finiteEventCount Ω (fun ω => E ω ∧ F ω) =
    finiteEventCount Ω E * finiteEventCount Ω F

/-- Conditional uniform-count independence inside a conditioning event `C`.
The equation is cross-multiplied to avoid division and therefore remains a pure
finite counting obligation. -/
def CountIndependentWithin {Ω : Type*} [Fintype Ω]
    (C E F : Ω → Prop) [DecidablePred C]
    [DecidablePred (fun ω => C ω ∧ E ω)]
    [DecidablePred (fun ω => C ω ∧ F ω)]
    [DecidablePred (fun ω => C ω ∧ E ω ∧ F ω)] : Prop :=
  finiteEventCount Ω C * finiteEventCount Ω (fun ω => C ω ∧ E ω ∧ F ω) =
    finiteEventCount Ω (fun ω => C ω ∧ E ω) *
      finiteEventCount Ω (fun ω => C ω ∧ F ω)

private noncomputable def eventSplitEquiv {Ω : Type*}
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

private theorem finiteEventCount_split_by {Ω : Type*} [Fintype Ω]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E] :
    finiteEventCount Ω C =
      finiteEventCount Ω (fun ω => C ω ∧ E ω) +
        finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω) := by
  classical
  simpa [finiteEventCount, Fintype.card_sum] using
    Fintype.card_congr (eventSplitEquiv C E)

private theorem finiteEventCount_congr_local {Ω : Type*} [Fintype Ω]
    {E F : Ω → Prop} [DecidablePred E] [DecidablePred F]
    (h : ∀ ω, E ω ↔ F ω) :
    finiteEventCount Ω E = finiteEventCount Ω F := by
  exact le_antisymm
    (finiteEventCount_le_of_imp (fun ω hE => (h ω).1 hE))
    (finiteEventCount_le_of_imp (fun ω hF => (h ω).2 hF))

/-- Under deterministic coupling inside `C`, conditional independence is
equivalent to a degenerate conditional event: either `E` never occurs inside
`C`, or `E` always occurs inside `C`.  This is the exact finite-count boundary
behind the diagonal Boolean obstruction. -/
theorem countIndependentWithin_coupled_iff_degenerate_on_condition
    {Ω : Type*} [Fintype Ω]
    (C E F : Ω → Prop) [DecidablePred C] [DecidablePred E] [DecidablePred F]
    (hcouple : ∀ ω, C ω → (E ω ↔ F ω)) :
    CountIndependentWithin (Ω := Ω) C E F ↔
      finiteEventCount Ω (fun ω => C ω ∧ E ω) = 0 ∨
        finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω) = 0 := by
  have hCEF :
      finiteEventCount Ω (fun ω => C ω ∧ E ω ∧ F ω) =
        finiteEventCount Ω (fun ω => C ω ∧ E ω) := by
    exact finiteEventCount_congr_local (Ω := Ω) (fun ω => by
      constructor
      · intro h
        exact ⟨h.1, h.2.1⟩
      · intro h
        exact ⟨h.1, h.2, (hcouple ω h.1).1 h.2⟩)
  have hCF :
      finiteEventCount Ω (fun ω => C ω ∧ F ω) =
        finiteEventCount Ω (fun ω => C ω ∧ E ω) := by
    exact finiteEventCount_congr_local (Ω := Ω) (fun ω => by
      constructor
      · intro h
        exact ⟨h.1, (hcouple ω h.1).2 h.2⟩
      · intro h
        exact ⟨h.1, (hcouple ω h.1).1 h.2⟩)
  constructor
  · intro hind
    have hind' :
        finiteEventCount Ω C * finiteEventCount Ω (fun ω => C ω ∧ E ω) =
          finiteEventCount Ω (fun ω => C ω ∧ E ω) *
            finiteEventCount Ω (fun ω => C ω ∧ E ω) := by
      simpa [CountIndependentWithin, hCEF, hCF] using hind
    by_cases hce : finiteEventCount Ω (fun ω => C ω ∧ E ω) = 0
    · exact Or.inl hce
    · right
      have hpos : 0 < finiteEventCount Ω (fun ω => C ω ∧ E ω) :=
        Nat.pos_of_ne_zero hce
      have hcancel :
          finiteEventCount Ω C = finiteEventCount Ω (fun ω => C ω ∧ E ω) :=
        Nat.mul_right_cancel hpos hind'
      have hsplit := finiteEventCount_split_by (Ω := Ω) C E
      omega
  · intro hdeg
    rcases hdeg with hce | hneg
    · simp [CountIndependentWithin, hCEF, hCF, hce]
    · have hsplit := finiteEventCount_split_by (Ω := Ω) C E
      have hcancel :
          finiteEventCount Ω C = finiteEventCount Ω (fun ω => C ω ∧ E ω) := by
        omega
      simp [CountIndependentWithin, hCEF, hCF, hcancel]

/-- If, inside a conditioning event `C`, the events `E` and `F` are pointwise
equivalent but `E` is nonconstant on `C`, then `E` and `F` cannot be
conditionally independent under uniform finite counting.  This is the abstract
form of the diagonal Boolean obstruction: deterministic coupling plus both
truth values kills conditional independence. -/
theorem not_countIndependentWithin_of_coupled_nonconstant_on_condition
    {Ω : Type*} [Fintype Ω]
    (C E F : Ω → Prop) [DecidablePred C] [DecidablePred E] [DecidablePred F]
    (hcouple : ∀ ω, C ω → (E ω ↔ F ω))
    (hpos : 0 < finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hneg : 0 < finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω)) :
    ¬ CountIndependentWithin (Ω := Ω) C E F := by
  intro hind
  have hCEF :
      finiteEventCount Ω (fun ω => C ω ∧ E ω ∧ F ω) =
        finiteEventCount Ω (fun ω => C ω ∧ E ω) := by
    exact finiteEventCount_congr_local (Ω := Ω) (fun ω => by
      constructor
      · intro h
        exact ⟨h.1, h.2.1⟩
      · intro h
        exact ⟨h.1, h.2, (hcouple ω h.1).1 h.2⟩)
  have hCF :
      finiteEventCount Ω (fun ω => C ω ∧ F ω) =
        finiteEventCount Ω (fun ω => C ω ∧ E ω) := by
    exact finiteEventCount_congr_local (Ω := Ω) (fun ω => by
      constructor
      · intro h
        exact ⟨h.1, (hcouple ω h.1).2 h.2⟩
      · intro h
        exact ⟨h.1, (hcouple ω h.1).1 h.2⟩)
  have hcancel :
      finiteEventCount Ω C = finiteEventCount Ω (fun ω => C ω ∧ E ω) := by
    have hind' :
        finiteEventCount Ω C * finiteEventCount Ω (fun ω => C ω ∧ E ω) =
          finiteEventCount Ω (fun ω => C ω ∧ E ω) *
            finiteEventCount Ω (fun ω => C ω ∧ E ω) := by
      simpa [CountIndependentWithin, hCEF, hCF] using hind
    exact Nat.mul_right_cancel hpos hind'
  have hsplit := finiteEventCount_split_by (Ω := Ω) C E
  rw [hcancel] at hsplit
  have hlt :
      finiteEventCount Ω (fun ω => C ω ∧ E ω) <
        finiteEventCount Ω (fun ω => C ω ∧ E ω) := by
    calc
      finiteEventCount Ω (fun ω => C ω ∧ E ω)
          < finiteEventCount Ω (fun ω => C ω ∧ E ω) +
              finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω) :=
            Nat.lt_add_of_pos_right hneg
      _ = finiteEventCount Ω (fun ω => C ω ∧ E ω) := hsplit.symm
  exact (Nat.lt_irrefl _ hlt)

/-- Under deterministic anti-coupling inside `C`, conditional independence is
equivalent to a degenerate conditional event: either `E` never occurs inside
`C`, or `E` always occurs inside `C`.  This is the complement-coded version of
the diagonal Boolean obstruction. -/
theorem countIndependentWithin_anticoupled_iff_degenerate_on_condition
    {Ω : Type*} [Fintype Ω]
    (C E F : Ω → Prop) [DecidablePred C] [DecidablePred E] [DecidablePred F]
    (hanti : ∀ ω, C ω → (E ω ↔ ¬ F ω)) :
    CountIndependentWithin (Ω := Ω) C E F ↔
      finiteEventCount Ω (fun ω => C ω ∧ E ω) = 0 ∨
        finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω) = 0 := by
  have hCEF :
      finiteEventCount Ω (fun ω => C ω ∧ E ω ∧ F ω) = 0 := by
    apply Nat.eq_zero_of_le_zero
    have hle :
        finiteEventCount Ω (fun ω => C ω ∧ E ω ∧ F ω) ≤
          finiteEventCount Ω (fun _ω : Ω => False) :=
      finiteEventCount_le_of_imp (Ω := Ω) (fun ω h => by
        exact False.elim ((hanti ω h.1).1 h.2.1 h.2.2))
    simpa [finiteEventCount] using hle
  have hCF :
      finiteEventCount Ω (fun ω => C ω ∧ F ω) =
        finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω) := by
    exact finiteEventCount_congr_local (Ω := Ω) (fun ω => by
      constructor
      · intro h
        exact ⟨h.1, fun hE => (hanti ω h.1).1 hE h.2⟩
      · intro h
        refine ⟨h.1, ?_⟩
        by_cases hF : F ω
        · exact hF
        · exact False.elim (h.2 ((hanti ω h.1).2 hF)))
  constructor
  · intro hind
    have hprod :
        finiteEventCount Ω (fun ω => C ω ∧ E ω) *
            finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω) = 0 := by
      simpa [CountIndependentWithin, hCEF, hCF] using hind.symm
    exact Nat.mul_eq_zero.mp hprod
  · intro hdeg
    rcases hdeg with hce | hneg
    · simp [CountIndependentWithin, hCEF, hCF, hce]
    · simp [CountIndependentWithin, hCEF, hCF, hneg]

/-- If, inside a conditioning event `C`, the events `E` and `F` are pointwise
opposite and `E` is nonconstant on `C`, then `E` and `F` cannot be conditionally
independent under uniform finite counting. -/
theorem not_countIndependentWithin_of_anticoupled_nonconstant_on_condition
    {Ω : Type*} [Fintype Ω]
    (C E F : Ω → Prop) [DecidablePred C] [DecidablePred E] [DecidablePred F]
    (hanti : ∀ ω, C ω → (E ω ↔ ¬ F ω))
    (hpos : 0 < finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hneg : 0 < finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω)) :
    ¬ CountIndependentWithin (Ω := Ω) C E F := by
  intro hind
  rcases (countIndependentWithin_anticoupled_iff_degenerate_on_condition
      C E F hanti).mp hind with hce | hne
  · exact (Nat.ne_of_gt hpos) hce
  · exact (Nat.ne_of_gt hneg) hne

/-- If the right event is false throughout the conditioning event, it is
conditionally independent of every left event in the cross-multiplied finite
counting sense. -/
theorem countIndependentWithin_of_right_false_on_condition
    {Ω : Type*} [Fintype Ω]
    (C E F : Ω → Prop) [DecidablePred C] [DecidablePred E] [DecidablePred F]
    (hfalse : ∀ ω, C ω → ¬ F ω) :
    CountIndependentWithin (Ω := Ω) C E F := by
  have hCF :
      finiteEventCount Ω (fun ω => C ω ∧ F ω) = 0 := by
    have hcongr :
        finiteEventCount Ω (fun ω => C ω ∧ F ω) =
          finiteEventCount Ω (fun _ω : Ω => False) :=
      finiteEventCount_congr_local (Ω := Ω) (fun ω => by
        constructor
        · intro h
          exact False.elim (hfalse ω h.1 h.2)
        · intro h
          exact False.elim h)
    simpa [finiteEventCount] using hcongr
  have hCEF :
      finiteEventCount Ω (fun ω => C ω ∧ E ω ∧ F ω) = 0 := by
    have hcongr :
        finiteEventCount Ω (fun ω => C ω ∧ E ω ∧ F ω) =
          finiteEventCount Ω (fun _ω : Ω => False) :=
      finiteEventCount_congr_local (Ω := Ω) (fun ω => by
        constructor
        · intro h
          exact False.elim (hfalse ω h.1 h.2.2)
        · intro h
          exact False.elim h)
    simpa [finiteEventCount] using hcongr
  simp [CountIndependentWithin, hCF, hCEF]

/-- If the right event is true throughout the conditioning event, it is
conditionally independent of every left event in the cross-multiplied finite
counting sense. -/
theorem countIndependentWithin_of_right_true_on_condition
    {Ω : Type*} [Fintype Ω]
    (C E F : Ω → Prop) [DecidablePred C] [DecidablePred E] [DecidablePred F]
    (htrue : ∀ ω, C ω → F ω) :
    CountIndependentWithin (Ω := Ω) C E F := by
  have hCF :
      finiteEventCount Ω (fun ω => C ω ∧ F ω) =
        finiteEventCount Ω C := by
    exact finiteEventCount_congr_local (Ω := Ω) (fun ω => by
      constructor
      · intro h
        exact h.1
      · intro hC
        exact ⟨hC, htrue ω hC⟩)
  have hCEF :
      finiteEventCount Ω (fun ω => C ω ∧ E ω ∧ F ω) =
        finiteEventCount Ω (fun ω => C ω ∧ E ω) := by
    exact finiteEventCount_congr_local (Ω := Ω) (fun ω => by
      constructor
      · intro h
        exact ⟨h.1, h.2.1⟩
      · intro h
        exact ⟨h.1, h.2, htrue ω h.1⟩)
  simp [CountIndependentWithin, hCF, hCEF, Nat.mul_comm]

end Mettapedia.Computability.PNP
