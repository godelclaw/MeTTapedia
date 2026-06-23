import Mettapedia.Computability.PNP.ConditioningObstructionCountIndependence

/-!
# Boolean recoding under conditioning

A deterministic Boolean recoding of the conditioned source bit is
conditionally independent only in the constant or degenerate cases.
-/

namespace Mettapedia.Computability.PNP

/-- A nonconstant Boolean recoding of a conditioned bit has the same exact
degeneracy boundary as the copied-bit and complemented-bit cases.  Thus a
repair cannot evade the conditioning obstruction merely by renaming or
recoding the determined conditioned bit. -/
theorem countIndependentWithin_boolRecoding_iff_degenerate_on_condition
    {Ω : Type*} [Fintype Ω]
    (C E F : Ω → Prop) [DecidablePred C] [DecidablePred E] [DecidablePred F]
    (r : Bool → Bool)
    (hrec : ∀ ω, C ω → (F ω ↔ r (decide (E ω)) = true))
    (hnonconstant : r true ≠ r false) :
    CountIndependentWithin (Ω := Ω) C E F ↔
      finiteEventCount Ω (fun ω => C ω ∧ E ω) = 0 ∨
        finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω) = 0 := by
  cases ht : r true <;> cases hf : r false
  · exact False.elim (hnonconstant (by simp [ht, hf]))
  · have hanti : ∀ ω, C ω → (E ω ↔ ¬ F ω) := by
      intro ω hC
      have h := hrec ω hC
      by_cases hE : E ω
      · have hnotF : ¬ F ω := by
          intro hF
          have hfalse := h.mp hF
          simp [hE, ht] at hfalse
        exact iff_of_true hE hnotF
      · have hF : F ω := by
          apply h.mpr
          simp [hE, hf]
        exact iff_of_false hE (not_not.mpr hF)
    exact countIndependentWithin_anticoupled_iff_degenerate_on_condition
      C E F hanti
  · have hcouple : ∀ ω, C ω → (E ω ↔ F ω) := by
      intro ω hC
      have h := hrec ω hC
      by_cases hE : E ω
      · have hF : F ω := by
          apply h.mpr
          simp [hE, ht]
        exact iff_of_true hE hF
      · have hnotF : ¬ F ω := by
          intro hF
          have hfalse := h.mp hF
          simp [hE, hf] at hfalse
        exact iff_of_false hE hnotF
    exact countIndependentWithin_coupled_iff_degenerate_on_condition
      C E F hcouple
  · exact False.elim (hnonconstant (by simp [ht, hf]))

/-- A constant Boolean recoding is conditionally independent of the source bit
for the trivial reason that it is constant on the conditioning event. -/
theorem countIndependentWithin_of_boolRecoding_constant_on_condition
    {Ω : Type*} [Fintype Ω]
    (C E F : Ω → Prop) [DecidablePred C] [DecidablePred E] [DecidablePred F]
    (r : Bool → Bool)
    (hrec : ∀ ω, C ω → (F ω ↔ r (decide (E ω)) = true))
    (hconstant : r true = r false) :
    CountIndependentWithin (Ω := Ω) C E F := by
  cases ht : r true <;> cases hf : r false
  · apply countIndependentWithin_of_right_false_on_condition C E F
    intro ω hC hF
    have h := (hrec ω hC).mp hF
    by_cases hE : E ω <;> simp [hE, ht, hf] at h
  · simp [ht, hf] at hconstant
  · simp [ht, hf] at hconstant
  · apply countIndependentWithin_of_right_true_on_condition C E F
    intro ω hC
    apply (hrec ω hC).mpr
    by_cases hE : E ω <;> simp [hE, ht, hf]

/-- Exact finite-count classification for deterministic Boolean recodings:
conditional independence holds precisely when the recoding is constant, or the
conditioned source bit is degenerate on the conditioning event. -/
theorem countIndependentWithin_boolRecoding_iff_constant_or_degenerate_on_condition
    {Ω : Type*} [Fintype Ω]
    (C E F : Ω → Prop) [DecidablePred C] [DecidablePred E] [DecidablePred F]
    (r : Bool → Bool)
    (hrec : ∀ ω, C ω → (F ω ↔ r (decide (E ω)) = true)) :
    CountIndependentWithin (Ω := Ω) C E F ↔
      r true = r false ∨
        finiteEventCount Ω (fun ω => C ω ∧ E ω) = 0 ∨
          finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω) = 0 := by
  constructor
  · intro hind
    by_cases hconstant : r true = r false
    · exact Or.inl hconstant
    · exact Or.inr
        ((countIndependentWithin_boolRecoding_iff_degenerate_on_condition
          C E F r hrec hconstant).mp hind)
  · intro h
    rcases h with hconstant | hdeg
    · exact countIndependentWithin_of_boolRecoding_constant_on_condition
        C E F r hrec hconstant
    · by_cases hconstant : r true = r false
      · exact countIndependentWithin_of_boolRecoding_constant_on_condition
          C E F r hrec hconstant
      · exact
          (countIndependentWithin_boolRecoding_iff_degenerate_on_condition
            C E F r hrec hconstant).mpr hdeg

/-- If the conditioned source bit takes both truth values, a nonconstant
deterministic Boolean recoding cannot be conditionally independent of that
source bit. -/
theorem not_countIndependentWithin_of_boolRecoding_nonconstant_on_condition
    {Ω : Type*} [Fintype Ω]
    (C E F : Ω → Prop) [DecidablePred C] [DecidablePred E] [DecidablePred F]
    (r : Bool → Bool)
    (hrec : ∀ ω, C ω → (F ω ↔ r (decide (E ω)) = true))
    (hnonconstant : r true ≠ r false)
    (hpos : 0 < finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hneg : 0 < finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω)) :
    ¬ CountIndependentWithin (Ω := Ω) C E F := by
  intro hind
  rcases (countIndependentWithin_boolRecoding_iff_degenerate_on_condition
      C E F r hrec hnonconstant).mp hind with hce | hne
  · exact (Nat.ne_of_gt hpos) hce
  · exact (Nat.ne_of_gt hneg) hne

/-- Contrapositive form: on a nondegenerate conditioned source bit, every
deterministic Boolean recoding that remains conditionally independent of the
source must be a constant recoding. -/
theorem boolRecoding_constant_of_countIndependentWithin_of_nonconstant_on_condition
    {Ω : Type*} [Fintype Ω]
    (C E F : Ω → Prop) [DecidablePred C] [DecidablePred E] [DecidablePred F]
    (r : Bool → Bool)
    (hrec : ∀ ω, C ω → (F ω ↔ r (decide (E ω)) = true))
    (hind : CountIndependentWithin (Ω := Ω) C E F)
    (hpos : 0 < finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hneg : 0 < finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω)) :
    r true = r false := by
  by_contra hnonconstant
  exact not_countIndependentWithin_of_boolRecoding_nonconstant_on_condition
    C E F r hrec hnonconstant hpos hneg hind

/-- On a nondegenerate conditioned source bit, deterministic Boolean recodings
are conditionally independent of the source exactly when they are constant. -/
theorem countIndependentWithin_boolRecoding_iff_constant_of_nonconstant_on_condition
    {Ω : Type*} [Fintype Ω]
    (C E F : Ω → Prop) [DecidablePred C] [DecidablePred E] [DecidablePred F]
    (r : Bool → Bool)
    (hrec : ∀ ω, C ω → (F ω ↔ r (decide (E ω)) = true))
    (hpos : 0 < finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hneg : 0 < finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω)) :
    CountIndependentWithin (Ω := Ω) C E F ↔ r true = r false := by
  constructor
  · intro hind
    exact boolRecoding_constant_of_countIndependentWithin_of_nonconstant_on_condition
      C E F r hrec hind hpos hneg
  · intro hconstant
    exact countIndependentWithin_of_boolRecoding_constant_on_condition
      C E F r hrec hconstant

end Mettapedia.Computability.PNP
