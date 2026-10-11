import Std

/-!
# Predictive value projection

An authored grammar can have several whitespace trees for the same value.
The compiler folds regular lexical spans and erases value-inert whitespace,
then checks disjoint lookahead choices. This model states the obligations for
replacing the complete candidate family by one direct value producer.

The source-to-branch correspondence and lookahead coverage are premises. The
native generator, DFA compiler, UTF-8 decoder and allocation implementation
are not verified by this file; differential checks exercise those boundaries.
-/
set_option autoImplicit false

namespace Mettapedia.GSLT.Parsing.PredictiveValueProjection

structure Alternative (Input Value : Type) where
  chooses : Input → Bool
  produce : Input → Option Value

def predict {Input Value : Type} (input : Input) :
    List (Alternative Input Value) → Option Value
  | [] => none
  | alternative :: rest =>
      if alternative.chooses input then alternative.produce input
      else predict input rest

def Covers {Input Value : Type} (input : Input)
    (alternatives : List (Alternative Input Value)) : Prop :=
  ∀ alternative ∈ alternatives, ∀ value,
    alternative.produce input = some value → alternative.chooses input = true

def Disjoint {Input Value : Type} (input : Input)
    (alternatives : List (Alternative Input Value)) : Prop :=
  ∀ left ∈ alternatives, ∀ right ∈ alternatives,
    left.chooses input = true → right.chooses input = true → left = right

theorem predict_sound {Input Value : Type} (input : Input)
    (alternatives : List (Alternative Input Value)) (value : Value)
    (h : predict input alternatives = some value) :
    ∃ alternative ∈ alternatives, alternative.produce input = some value := by
  induction alternatives with
  | nil => simp [predict] at h
  | cons alternative rest ih =>
    by_cases chosen : alternative.chooses input = true
    · exact ⟨alternative, by simp, by simpa [predict, chosen] using h⟩
    · obtain ⟨found, member, result⟩ := ih (by simpa [predict, chosen] using h)
      exact ⟨found, by simp [member], result⟩

theorem predict_complete {Input Value : Type} (input : Input)
    (alternatives : List (Alternative Input Value)) (value : Value)
    (covers : Covers input alternatives) (disjoint : Disjoint input alternatives)
    (h : ∃ alternative ∈ alternatives, alternative.produce input = some value) :
    predict input alternatives = some value := by
  induction alternatives with
  | nil => simp at h
  | cons alternative rest ih =>
    obtain ⟨found, member, result⟩ := h
    by_cases chosen : alternative.chooses input = true
    · have same : alternative = found := disjoint alternative (by simp) found member chosen
        (covers found member value result)
      subst found
      simpa [predict, chosen] using result
    · have found_rest : found ∈ rest := by
        rcases List.mem_cons.mp member with same | tail
        · subst found
          exact False.elim (chosen (covers alternative (by simp) value result))
        · exact tail
      have covers_rest : Covers input rest := by
        intro a ha v hv
        exact covers a (by simp [ha]) v hv
      have disjoint_rest : Disjoint input rest := by
        intro a ha b hb ca cb
        exact disjoint a (by simp [ha]) b (by simp [hb]) ca cb
      simpa [predict, chosen] using ih covers_rest disjoint_rest ⟨found, found_rest, result⟩

theorem predict_exact {Input Value : Type} (input : Input)
    (alternatives : List (Alternative Input Value)) (value : Value)
    (covers : Covers input alternatives) (disjoint : Disjoint input alternatives) :
    predict input alternatives = some value ↔
      ∃ alternative ∈ alternatives, alternative.produce input = some value :=
  ⟨predict_sound input alternatives value,
   predict_complete input alternatives value covers disjoint⟩

/-- A complete source candidate family need not be materialized at runtime
when its value relation is realized by covered, disjoint alternatives. -/
theorem forest_free_value_exact {Input Value : Type} (input : Input)
    (candidates : List Value) (alternatives : List (Alternative Input Value))
    (covers : Covers input alternatives) (disjoint : Disjoint input alternatives)
    (correspondence : ∀ value, value ∈ candidates ↔
       ∃ alternative ∈ alternatives, alternative.produce input = some value)
    (value : Value) : predict input alternatives = some value ↔ value ∈ candidates := by
  rw [predict_exact input alternatives value covers disjoint, correspondence]

def selectionChecks {Input Value : Type} (input : Input) :
    List (Alternative Input Value) → Nat
  | [] => 0
  | alternative :: rest =>
      if alternative.chooses input then 1 else 1 + selectionChecks input rest

theorem selectionChecks_le {Input Value : Type} (input : Input)
    (alternatives : List (Alternative Input Value)) :
    selectionChecks input alternatives ≤ alternatives.length := by
  induction alternatives with
  | nil => simp [selectionChecks]
  | cons alternative rest ih =>
    by_cases chosen : alternative.chooses input = true
    · simp [selectionChecks, chosen]
    · simpa [selectionChecks, chosen, Nat.add_comm] using Nat.add_le_add_left ih 1

/-- Choice work is bounded by the fixed grammar size per value. This counts
selection only; input decoding and value construction have separate costs. -/
theorem selection_work_linear {Input Value : Type}
    (inputs : List Input) (alternatives : List (Alternative Input Value)) :
    (inputs.map fun input => selectionChecks input alternatives).sum ≤
      inputs.length * alternatives.length := by
  induction inputs with
  | nil => simp
  | cons input rest ih =>
    simpa [Nat.add_mul, Nat.add_comm] using
      Nat.add_le_add (selectionChecks_le input alternatives) ih

#print axioms predict_exact
#print axioms forest_free_value_exact
#print axioms selection_work_linear

end Mettapedia.GSLT.Parsing.PredictiveValueProjection
