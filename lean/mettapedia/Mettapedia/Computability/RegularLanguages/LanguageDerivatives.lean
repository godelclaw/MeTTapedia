import Mathlib.Computability.MyhillNerode

/-!
# Left derivatives of formal languages

A derivative removes a specified initial letter from each word of a language:
it is Mathlib's left quotient by a one-letter word. The equations for sums,
products and Kleene star are proved directly from Mathlib's set-of-words
semantics and its nonempty-factor description of Kleene star. Continuation
languages also give a recognition-bisimulation principle for state machines.
Neither construction presupposes a regex matcher or its derivative algorithm.
-/

open scoped Computability

namespace Mettapedia.Computability.RegularLanguages

variable {α : Type*}

/-- The words obtained by removing the initial letter `a` from words of `L`:
the left quotient of `L` by the one-letter word. -/
def leftDerivative (a : α) (L : Language α) : Language α :=
  L.leftQuotient [a]

theorem leftDerivative_eq_leftQuotient (a : α) (L : Language α) :
    leftDerivative a L = L.leftQuotient [a] := rfl

@[simp]
theorem mem_leftDerivative (a : α) (L : Language α) (w : List α) :
    w ∈ leftDerivative a L ↔ a :: w ∈ L := Iff.rfl

/-- The left quotient by a word removes its letters one at a time. -/
theorem leftQuotient_cons (a : α) (word : List α) (L : Language α) :
    L.leftQuotient (a :: word) = (leftDerivative a L).leftQuotient word :=
  Language.leftQuotient_append L [a] word

@[simp]
theorem leftDerivative_zero (a : α) : leftDerivative a (0 : Language α) = 0 :=
  Set.preimage_empty

@[simp]
theorem leftDerivative_one (a : α) : leftDerivative a (1 : Language α) = 0 := by
  ext w
  simp

/-- Removing the first letter from a singleton word gives its singleton tail. -/
@[simp]
theorem leftDerivative_singleton_cons (a : α) (w : List α) :
    leftDerivative a ({a :: w} : Language α) = {w} := by
  ext v
  change (a :: v = a :: w) ↔ v = w
  simp

/-- A different initial letter cannot match a singleton word. -/
theorem leftDerivative_singleton_cons_of_ne {a b : α} (h : a ≠ b) (w : List α) :
    leftDerivative a ({b :: w} : Language α) = 0 := by
  ext v
  change (a :: v = b :: w) ↔ v ∈ (0 : Language α)
  simp [h]

/-- A one-letter language accepts the derivative precisely at its own letter. -/
theorem leftDerivative_singleton [DecidableEq α] (a b : α) :
    leftDerivative a ({[b]} : Language α) = if a = b then 1 else 0 := by
  by_cases h : a = b
  · subst b
    rw [if_pos rfl]
    exact leftDerivative_singleton_cons a []
  · simpa [h] using leftDerivative_singleton_cons_of_ne h []

/-- The derivative of a one-letter character class depends only on whether
the consumed letter belongs to the class. -/
theorem mem_leftDerivative_letters (a : α) (P : α → Prop) (w : List α) :
    w ∈ leftDerivative a ({v | ∃ b, P b ∧ v = [b]} : Language α) ↔
      P a ∧ w = [] := by
  change (∃ b, P b ∧ a :: w = [b]) ↔ P a ∧ w = []
  simp only [List.cons.injEq]
  aesop

theorem leftDerivative_letters (a : α) (P : α → Prop) [Decidable (P a)] :
    leftDerivative a ({v | ∃ b, P b ∧ v = [b]} : Language α) =
      if P a then 1 else 0 := by
  ext w
  rw [mem_leftDerivative_letters]
  by_cases h : P a <;> simp [h]

@[simp]
theorem leftDerivative_add (a : α) (L M : Language α) :
    leftDerivative a (L + M) = leftDerivative a L + leftDerivative a M := Set.preimage_union

/-- Consuming a letter commutes with an arbitrary union of languages. -/
theorem leftDerivative_sSup (a : α) (S : Set (Language α)) :
    leftDerivative a (sSup S) = sSup (leftDerivative a '' S) := by
  ext w
  change (∃ K ∈ S, a :: w ∈ K) ↔ ∃ K ∈ leftDerivative a '' S, w ∈ K
  simp only [Set.mem_image]
  aesop

/-- Concatenation can consume the initial letter in the first factor, or in the
second factor when the first factor accepts the empty word. -/
theorem mem_leftDerivative_mul (a : α) (L M : Language α) (w : List α) :
    w ∈ leftDerivative a (L * M) ↔
      w ∈ leftDerivative a L * M ∨ ([] ∈ L ∧ w ∈ leftDerivative a M) := by
  simp only [mem_leftDerivative, Language.mem_mul, List.append_eq_cons_iff]
  aesop

/-- The language equation for concatenation, with an explicit nullability guard. -/
theorem leftDerivative_mul (a : α) (L M : Language α) [Decidable ([] ∈ L)] :
    leftDerivative a (L * M) =
      leftDerivative a L * M + if [] ∈ L then leftDerivative a M else 0 := by
  ext w
  rw [mem_leftDerivative_mul, Language.mem_add]
  by_cases h : [] ∈ L <;> simp [h]

/-- A nonempty starred word starts with a nonempty word of the base language.
Discarding empty factors makes this equation valid even for nullable `L`. -/
theorem leftDerivative_kstar (a : α) (L : Language α) :
    leftDerivative a L∗ = leftDerivative a L * L∗ := by
  ext w
  constructor
  · intro member
    obtain ⟨parts, eq, all⟩ := Language.mem_kstar.mp member
    obtain ⟨before, first, rest, rfl, _, eq⟩ := List.cons_eq_flatten_iff.mp eq
    exact Language.mem_mul.mpr ⟨first, all _ (by simp), rest.flatten,
      Language.join_mem_kstar (fun v hv => all v (by simp [hv])), eq.symm⟩
  · intro member
    obtain ⟨u, hu, v, hv, rfl⟩ := Language.mem_mul.mp member
    obtain ⟨parts, rfl, all⟩ := Language.mem_kstar.mp hv
    exact Language.mem_kstar.mpr ⟨(a :: u) :: parts, rfl, List.forall_mem_cons.mpr ⟨hu, all⟩⟩

/-- A language equation remains valid after consuming a letter. -/
theorem leftDerivative_congr (a : α) {L M : Language α}
    (h : ∀ w, w ∈ L ↔ w ∈ M) : leftDerivative a L = leftDerivative a M :=
  congrArg (leftDerivative a) (Language.ext h)

/-- Consuming a letter preserves language inclusion. -/
theorem leftDerivative_mono (a : α) {L M : Language α} (h : L ≤ M) :
    leftDerivative a L ≤ leftDerivative a M :=
  fun _ hw => h hw

/-- A relation respecting acceptance and each letter transition preserves all
continuation observations, even for different and infinite state carriers. -/
theorem acceptsFrom_eq_of_bisimulation {σ τ : Type*}
    (M : DFA α σ) (N : DFA α τ) (R : σ → τ → Prop)
    (observe : ∀ s t, R s t → (s ∈ M.accept ↔ t ∈ N.accept))
    (step : ∀ s t, R s t → ∀ a, R (M.step s a) (N.step t a))
    (s : σ) (t : τ) (related : R s t) : M.acceptsFrom s = N.acceptsFrom t := by
  ext w
  change M.evalFrom s w ∈ M.accept ↔ N.evalFrom t w ∈ N.accept
  induction w generalizing s t with
  | nil => exact observe s t related
  | cons a rest ih => exact ih _ _ (step s t related a)

namespace Controls

/-- The empty-word alternative allows a concatenation to consume its second
factor directly. -/
theorem nullable_concat_consumes_second :
    [] ∈ leftDerivative true
      ((1 + ({[false]} : Language Bool)) * ({[true]} : Language Bool)) := by
  rw [mem_leftDerivative_mul]
  right
  exact ⟨Or.inl Language.nil_mem_one, rfl⟩

/-- Empty factors in a star do not prevent a nonempty factor from matching. -/
theorem nullable_kstar_consumes :
    [] ∈ leftDerivative true ((1 + ({[true]} : Language Bool))∗) := by
  rw [leftDerivative_kstar, leftDerivative_add, leftDerivative_one]
  rw [leftDerivative_singleton_cons, zero_add]
  exact Language.mem_mul.mpr ⟨[], rfl, [], Language.nil_mem_kstar _, rfl⟩

/-- The empty-word alternative still cannot manufacture an unmatched letter. -/
theorem nullable_kstar_rejects_other_letter :
    [] ∉ leftDerivative false ((1 + ({[true]} : Language Bool))∗) := by
  rw [leftDerivative_kstar, leftDerivative_add, leftDerivative_one]
  rw [leftDerivative_singleton_cons_of_ne Bool.false_ne_true, zero_add, zero_mul]
  exact Language.notMem_zero _

end Controls

end Mettapedia.Computability.RegularLanguages
