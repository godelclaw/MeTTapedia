import Mettapedia.Computability.PNP.ConditioningObstructionBoolRecoding

/-!
The previous Boolean-recoding theorem is not limited to Boolean output labels.
Any deterministic recoding of the same conditioned bit into an arbitrary
decidable codomain has an informative fiber.  If the two source-bit images are
different, the fiber over the `true` image is just the original source bit, so
conditional independence of that fiber has the same degenerate boundary.
-/

namespace Mettapedia.Computability.PNP

/-- Exact finite-count classification for the true-image fiber of an arbitrary
deterministic recoding `Bool → α`.  Conditional independence between the source
bit and that output fiber holds precisely when the recoding collapses the two
source-bit values, or when the source bit is itself degenerate on the
conditioning event. -/
theorem countIndependentWithin_boolToAnyRecoding_trueFiber_iff_constant_or_degenerate_on_condition
    {Ω α : Type*} [Fintype Ω] [DecidableEq α]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → α) :
    CountIndependentWithin (Ω := Ω) C E
        (fun ω => r (decide (E ω)) = r true) ↔
      r true = r false ∨
        finiteEventCount Ω (fun ω => C ω ∧ E ω) = 0 ∨
          finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω) = 0 := by
  have hcouple_of_nonconstant
      (hnonconstant : r true ≠ r false) :
      ∀ ω, C ω → (E ω ↔ r (decide (E ω)) = r true) := by
    intro ω _hC
    by_cases hE : E ω
    · simp [hE]
    · have hfalse : r false ≠ r true := fun h => hnonconstant h.symm
      simp [hE, hfalse]
  have hconst_independent
      (hconstant : r true = r false) :
      CountIndependentWithin (Ω := Ω) C E
        (fun ω => r (decide (E ω)) = r true) := by
    refine countIndependentWithin_of_right_true_on_condition
      C E (fun ω => r (decide (E ω)) = r true) ?_
    intro ω _hC
    by_cases hE : E ω <;> simp [hE, hconstant]
  constructor
  · intro hind
    by_cases hconstant : r true = r false
    · exact Or.inl hconstant
    · exact Or.inr
        ((countIndependentWithin_coupled_iff_degenerate_on_condition
          C E (fun ω => r (decide (E ω)) = r true)
          (hcouple_of_nonconstant hconstant)).mp hind)
  · intro h
    rcases h with hconstant | hdeg
    · exact hconst_independent hconstant
    · by_cases hconstant : r true = r false
      · exact hconst_independent hconstant
      · exact
          (countIndependentWithin_coupled_iff_degenerate_on_condition
            C E (fun ω => r (decide (E ω)) = r true)
            (hcouple_of_nonconstant hconstant)).mpr hdeg

/-- A nonconstant arbitrary-codomain deterministic recoding of a nondegenerate
conditioned source bit has an informative output fiber that cannot be
conditionally independent of the source bit. -/
theorem not_countIndependentWithin_of_boolToAnyRecoding_trueFiber_nonconstant_on_condition
    {Ω α : Type*} [Fintype Ω] [DecidableEq α]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → α)
    (hnonconstant : r true ≠ r false)
    (hpos : 0 < finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hneg : 0 < finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω)) :
    ¬ CountIndependentWithin (Ω := Ω) C E
      (fun ω => r (decide (E ω)) = r true) := by
  intro hind
  rcases
      (countIndependentWithin_boolToAnyRecoding_trueFiber_iff_constant_or_degenerate_on_condition
        C E r).mp hind with hconstant | hdeg
  · exact hnonconstant hconstant
  · rcases hdeg with hce | hne
    · exact (Nat.ne_of_gt hpos) hce
    · exact (Nat.ne_of_gt hneg) hne

/-- Contrapositive form: if the true-image fiber of an arbitrary-codomain
deterministic recoding remains conditionally independent of a nondegenerate
source bit, the recoding must collapse the two source-bit values. -/
theorem boolToAnyRecoding_trueFiber_constant_of_countIndependentWithin_of_nonconstant_on_condition
    {Ω α : Type*} [Fintype Ω] [DecidableEq α]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → α)
    (hind : CountIndependentWithin (Ω := Ω) C E
      (fun ω => r (decide (E ω)) = r true))
    (hpos : 0 < finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hneg : 0 < finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω)) :
    r true = r false := by
  by_contra hnonconstant
  exact
    not_countIndependentWithin_of_boolToAnyRecoding_trueFiber_nonconstant_on_condition
      C E r hnonconstant hpos hneg hind

/-- On a nondegenerate conditioned source bit, the true-image fiber of an
arbitrary-codomain deterministic recoding is conditionally independent of the
source exactly when the recoding collapses the two source-bit values. -/
theorem countIndependentWithin_boolToAnyRecoding_trueFiber_iff_constant_of_nonconstant_on_condition
    {Ω α : Type*} [Fintype Ω] [DecidableEq α]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → α)
    (hpos : 0 < finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hneg : 0 < finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω)) :
    CountIndependentWithin (Ω := Ω) C E
        (fun ω => r (decide (E ω)) = r true) ↔
      r true = r false := by
  constructor
  · intro hind
    exact
      boolToAnyRecoding_trueFiber_constant_of_countIndependentWithin_of_nonconstant_on_condition
        C E r hind hpos hneg
  · intro hconstant
    exact
      (countIndependentWithin_boolToAnyRecoding_trueFiber_iff_constant_or_degenerate_on_condition
        C E r).mpr (Or.inl hconstant)

/-- Exact finite-count classification for every output fiber of an arbitrary
deterministic recoding `Bool → α`.  Conditional independence between the source
bit and the fiber `r (decide (E ω)) = y` holds precisely when that fiber does
not distinguish the two source-bit values, or when the source bit is itself
degenerate on the conditioning event. -/
theorem countIndependentWithin_boolToAnyRecoding_fiber_iff_fiber_constant_or_degenerate_on_condition
    {Ω α : Type*} [Fintype Ω] [DecidableEq α]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → α) (y : α) :
    CountIndependentWithin (Ω := Ω) C E
        (fun ω => r (decide (E ω)) = y) ↔
      (r true = y ↔ r false = y) ∨
        finiteEventCount Ω (fun ω => C ω ∧ E ω) = 0 ∨
          finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω) = 0 := by
  have hconst_independent
      (hfiber : (r true = y ↔ r false = y)) :
      CountIndependentWithin (Ω := Ω) C E
        (fun ω => r (decide (E ω)) = y) := by
    by_cases ht : r true = y
    · have hf : r false = y := hfiber.mp ht
      refine countIndependentWithin_of_right_true_on_condition
        C E (fun ω => r (decide (E ω)) = y) ?_
      intro ω _hC
      by_cases hE : E ω <;> simp [hE, ht, hf]
    · have hf : r false ≠ y := fun h => ht (hfiber.mpr h)
      refine countIndependentWithin_of_right_false_on_condition
        C E (fun ω => r (decide (E ω)) = y) ?_
      intro ω _hC hF
      by_cases hE : E ω <;> simp [hE, ht, hf] at hF
  have hcouple_of_true_false
      (ht : r true = y) (hf : r false ≠ y) :
      ∀ ω, C ω → (E ω ↔ r (decide (E ω)) = y) := by
    intro ω _hC
    by_cases hE : E ω
    · simp [hE, ht]
    · simp [hE, hf]
  have hanti_of_false_true
      (ht : r true ≠ y) (hf : r false = y) :
      ∀ ω, C ω → (E ω ↔ ¬ r (decide (E ω)) = y) := by
    intro ω _hC
    by_cases hE : E ω
    · have hnotF : ¬ r (decide (E ω)) = y := by simpa [hE] using ht
      exact iff_of_true hE hnotF
    · have hF : r (decide (E ω)) = y := by simpa [hE] using hf
      exact iff_of_false hE (not_not.mpr hF)
  constructor
  · intro hind
    by_cases hfiber : (r true = y ↔ r false = y)
    · exact Or.inl hfiber
    · by_cases ht : r true = y
      · by_cases hf : r false = y
        · exact False.elim (hfiber (iff_of_true ht hf))
        · exact Or.inr
            ((countIndependentWithin_coupled_iff_degenerate_on_condition
              C E (fun ω => r (decide (E ω)) = y)
              (hcouple_of_true_false ht hf)).mp hind)
      · by_cases hf : r false = y
        · exact Or.inr
            ((countIndependentWithin_anticoupled_iff_degenerate_on_condition
              C E (fun ω => r (decide (E ω)) = y)
              (hanti_of_false_true ht hf)).mp hind)
        · exact False.elim (hfiber (iff_of_false ht hf))
  · intro h
    rcases h with hfiber | hdeg
    · exact hconst_independent hfiber
    · by_cases ht : r true = y
      · by_cases hf : r false = y
        · exact hconst_independent (iff_of_true ht hf)
        · exact
            (countIndependentWithin_coupled_iff_degenerate_on_condition
              C E (fun ω => r (decide (E ω)) = y)
              (hcouple_of_true_false ht hf)).mpr hdeg
      · by_cases hf : r false = y
        · exact
            (countIndependentWithin_anticoupled_iff_degenerate_on_condition
              C E (fun ω => r (decide (E ω)) = y)
              (hanti_of_false_true ht hf)).mpr hdeg
        · exact hconst_independent (iff_of_false ht hf)

/-- If some output fiber of an arbitrary deterministic recoding distinguishes a
nondegenerate conditioned source bit, that fiber cannot be conditionally
independent of the source bit. -/
theorem not_countIndependentWithin_of_boolToAnyRecoding_fiber_distinguishes_on_condition
    {Ω α : Type*} [Fintype Ω] [DecidableEq α]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → α) (y : α)
    (hdistinguish : ¬ (r true = y ↔ r false = y))
    (hpos : 0 < finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hneg : 0 < finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω)) :
    ¬ CountIndependentWithin (Ω := Ω) C E
      (fun ω => r (decide (E ω)) = y) := by
  intro hind
  rcases
      (countIndependentWithin_boolToAnyRecoding_fiber_iff_fiber_constant_or_degenerate_on_condition
        C E r y).mp hind with hfiber | hdeg
  · exact hdistinguish hfiber
  · rcases hdeg with hce | hne
    · exact (Nat.ne_of_gt hpos) hce
    · exact (Nat.ne_of_gt hneg) hne

/-- Contrapositive form: on a nondegenerate conditioned source bit, every
deterministic output fiber that remains conditionally independent must be unable
to distinguish the two source-bit values. -/
theorem boolToAnyRecoding_fiber_constant_of_countIndependentWithin_of_nonconstant_on_condition
    {Ω α : Type*} [Fintype Ω] [DecidableEq α]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → α) (y : α)
    (hind : CountIndependentWithin (Ω := Ω) C E
      (fun ω => r (decide (E ω)) = y))
    (hpos : 0 < finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hneg : 0 < finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω)) :
    (r true = y ↔ r false = y) := by
  by_contra hdistinguish
  exact
    not_countIndependentWithin_of_boolToAnyRecoding_fiber_distinguishes_on_condition
      C E r y hdistinguish hpos hneg hind

/-- On a nondegenerate conditioned source bit, an arbitrary deterministic output
fiber is conditionally independent of the source exactly when that fiber does
not distinguish the two source-bit values. -/
theorem countIndependentWithin_boolToAnyRecoding_fiber_iff_fiber_constant_of_nonconstant_on_condition
    {Ω α : Type*} [Fintype Ω] [DecidableEq α]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → α) (y : α)
    (hpos : 0 < finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hneg : 0 < finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω)) :
    CountIndependentWithin (Ω := Ω) C E
        (fun ω => r (decide (E ω)) = y) ↔
      (r true = y ↔ r false = y) := by
  constructor
  · intro hind
    exact
      boolToAnyRecoding_fiber_constant_of_countIndependentWithin_of_nonconstant_on_condition
        C E r y hind hpos hneg
  · intro hfiber
    exact
      (countIndependentWithin_boolToAnyRecoding_fiber_iff_fiber_constant_or_degenerate_on_condition
        C E r y).mpr (Or.inl hfiber)


end Mettapedia.Computability.PNP
