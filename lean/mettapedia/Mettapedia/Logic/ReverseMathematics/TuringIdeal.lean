import Mettapedia.Logic.ReverseMathematics.RelativeComputability
import Mathlib.Computability.Halting

/-!
# Turing ideals

A *Turing ideal* is a nonempty family of sets of naturals closed under the
recursive join `A ⊕ B` and downward closed under Turing reducibility
(Simpson, *Subsystems of Second Order Arithmetic*, §VIII.1). Turing
reducibility of sets is Mathlib's `TuringReducible` applied to
characteristic functions.

* `SetTuringLE`: `A ≤ᵀ B` for sets.
* `join`: `A ⊕ B = {2n | n ∈ A} ∪ {2n+1 | n ∈ B}`, the least upper bound of
  `A` and `B` (`left_le_join`, `right_le_join`, `join_le`).
* `IsRecursiveSet`: computable membership, and `isRecursiveSet_iff_partrec`.
* `IsTuringIdeal`; `recursiveSets_isTuringIdeal`, `univ_isTuringIdeal`,
  `principal_isTuringIdeal`; every Turing ideal contains the recursive sets
  (`IsTuringIdeal.recursive_mem`); finitely many members have a common upper
  bound inside the ideal (`IsTuringIdeal.exists_upper`).

The same closure conditions appear in Cameron Freer's Lean development
`reverse-mathlib` (`ReverseMathlib/Omega/Computability.lean`, structure
`IsTuringIdeal` with fields `nonempty`, `downward`, `join`); the definitions
here are written independently over Mathlib's `TuringReducible`.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.ReverseMathematics

open Encodable RelComp

/-- Turing reducibility of sets of naturals. -/
def SetTuringLE (A B : Set ℕ) : Prop :=
  TuringReducible (charFn A) (charFn B)

theorem setTuringLE_iff_nat {A B : Set ℕ} :
    SetTuringLE A B ↔ Nat.RecursiveIn {charFn B} (charFn A) :=
  RecursiveIn.iff_nat

theorem SetTuringLE.refl (A : Set ℕ) : SetTuringLE A A :=
  TuringReducible.refl _

theorem SetTuringLE.trans {A B C : Set ℕ} (hAB : SetTuringLE A B) (hBC : SetTuringLE B C) :
    SetTuringLE A C :=
  TuringReducible.trans hAB hBC

/-- A set is reducible to `B` when its decision procedure is computable
relative to `B`. -/
theorem setTuringLE_of_decide {A B : Set ℕ} [DecidablePred (· ∈ A)]
    (h : ComputableIn {charFn B} fun n : ℕ => decide (n ∈ A)) : SetTuringLE A B :=
  setTuringLE_iff_nat.mpr (charFn_of_decide h)

theorem decide_of_setTuringLE {A B : Set ℕ} [DecidablePred (· ∈ A)] (h : SetTuringLE A B) :
    ComputableIn {charFn B} fun n : ℕ => decide (n ∈ A) :=
  decide_of_charFn (setTuringLE_iff_nat.mp h)

/-- The membership test of `B` relative to the oracle `B`. -/
theorem decide_mem_self (B : Set ℕ) [DecidablePred (· ∈ B)] :
    ComputableIn {charFn B} fun n : ℕ => decide (n ∈ B) :=
  mem (Set.mem_singleton _)

/-! ## The recursive join -/

/-- The recursive join `A ⊕ B`. -/
def join (A B : Set ℕ) : Set ℕ :=
  {n | (n % 2 = 0 ∧ n / 2 ∈ A) ∨ (n % 2 = 1 ∧ n / 2 ∈ B)}

theorem mem_join_double (A B : Set ℕ) (n : ℕ) : 2 * n ∈ join A B ↔ n ∈ A := by
  simp only [join, Set.mem_ofPred_eq]
  constructor
  · rintro (⟨_, h⟩ | ⟨odd, _⟩)
    · simpa using h
    · omega
  · intro h
    exact Or.inl ⟨by omega, by simpa using h⟩

theorem mem_join_double_succ (A B : Set ℕ) (n : ℕ) : 2 * n + 1 ∈ join A B ↔ n ∈ B := by
  simp only [join, Set.mem_ofPred_eq]
  have half : (2 * n + 1) / 2 = n := by omega
  constructor
  · rintro (⟨even, _⟩ | ⟨_, h⟩)
    · omega
    · rwa [half] at h
  · intro h
    exact Or.inr ⟨by omega, by rwa [half]⟩

theorem left_le_join (A B : Set ℕ) : SetTuringLE A (join A B) := by
  classical
  refine setTuringLE_of_decide ?_
  have query := mem_comp (A := join A B) (Set.mem_singleton _)
    (ofPrimrec₂ Primrec.nat_mul (const 2) id')
  refine query.of_eq fun n => ?_
  simp only [mem_join_double]

theorem right_le_join (A B : Set ℕ) : SetTuringLE B (join A B) := by
  classical
  refine setTuringLE_of_decide ?_
  have query := mem_comp (A := join A B) (Set.mem_singleton _)
    (ofPrimrec₂ Primrec.nat_add (ofPrimrec₂ Primrec.nat_mul (const 2) id') (const 1))
  refine query.of_eq fun n => ?_
  simp only [mem_join_double_succ]

/-- The selector used by the join: the parity of `n` picks a component. -/
private theorem primrec_select :
    Primrec₂ fun (n : ℕ) (p : Bool × Bool) => bif n % 2 == 0 then p.1 else p.2 :=
  Primrec.cond
    (Primrec.beq.comp (Primrec.nat_mod.comp Primrec.fst (Primrec.const 2)) (Primrec.const 0))
    (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)

/-- **The join is the least upper bound.** -/
theorem join_le {A B C : Set ℕ} (hA : SetTuringLE A C) (hB : SetTuringLE B C) :
    SetTuringLE (join A B) C := by
  classical
  refine setTuringLE_of_decide ?_
  have half : ComputableIn {charFn C} fun n : ℕ => n / 2 :=
    ofPrimrec₂ Primrec.nat_div id' (const 2)
  have combined := ofPrimrec₂ primrec_select id'
    (pair (comp' (decide_of_setTuringLE hA) half) (comp' (decide_of_setTuringLE hB) half))
  refine combined.of_eq fun n => ?_
  simp only [join, Set.mem_ofPred_eq]
  rcases Nat.mod_two_eq_zero_or_one n with parity | parity <;> simp [parity]

/-! ## Recursive sets -/

/-- A set with computable membership. -/
def IsRecursiveSet (A : Set ℕ) : Prop :=
  ComputablePred (· ∈ A)

/-- The recursive sets. -/
def recursiveSets : Set (Set ℕ) :=
  {A | IsRecursiveSet A}

theorem isRecursiveSet_iff_computableIn {A : Set ℕ} [DecidablePred (· ∈ A)] :
    IsRecursiveSet A ↔ ComputableIn (∅ : Set (ℕ →. ℕ)) fun n : ℕ => decide (n ∈ A) := by
  constructor
  · intro h
    exact (ComputablePred.decide h).computableIn
  · intro h
    exact ⟨inferInstance, (recursiveIn_empty_iff.mp h : Partrec _)⟩

theorem isRecursiveSet_iff_partrec {A : Set ℕ} : IsRecursiveSet A ↔ Nat.Partrec (charFn A) := by
  classical
  rw [isRecursiveSet_iff_computableIn]
  constructor
  · intro h
    exact (charFn_of_decide h).partrec_of_oracle fun _ absurd => absurd.elim
  · intro h
    exact decide_of_charFn (Nat.Partrec.recursiveIn h)

/-- A recursive set is reducible to every set. -/
theorem IsRecursiveSet.le {A : Set ℕ} (h : IsRecursiveSet A) (B : Set ℕ) : SetTuringLE A B :=
  setTuringLE_iff_nat.mpr (Nat.Partrec.recursiveIn (isRecursiveSet_iff_partrec.mp h))

/-- A set reducible to a recursive set is recursive. -/
theorem IsRecursiveSet.of_le {A B : Set ℕ} (hB : IsRecursiveSet B) (h : SetTuringLE A B) :
    IsRecursiveSet A := by
  refine isRecursiveSet_iff_partrec.mpr ?_
  exact (setTuringLE_iff_nat.mp h).partrec_of_oracle fun g member =>
    (Set.mem_singleton_iff.mp member) ▸ isRecursiveSet_iff_partrec.mp hB

theorem isRecursiveSet_empty : IsRecursiveSet (∅ : Set ℕ) := by
  classical
  refine ⟨inferInstance, (Computable.const false).of_eq fun n => ?_⟩
  simp

theorem isRecursiveSet_univ : IsRecursiveSet (Set.univ : Set ℕ) := by
  classical
  refine ⟨inferInstance, (Computable.const true).of_eq fun n => ?_⟩
  simp

/-! ## Turing ideals -/

/-- A Turing ideal (Simpson §VIII.1). -/
structure IsTuringIdeal (S : Set (Set ℕ)) : Prop where
  nonempty : S.Nonempty
  join_mem : ∀ {A B : Set ℕ}, A ∈ S → B ∈ S → join A B ∈ S
  down : ∀ {A B : Set ℕ}, B ∈ S → SetTuringLE A B → A ∈ S

/-- Every Turing ideal contains every recursive set. -/
theorem IsTuringIdeal.recursive_mem {S : Set (Set ℕ)} (hS : IsTuringIdeal S) {A : Set ℕ}
    (hA : IsRecursiveSet A) : A ∈ S := by
  obtain ⟨B, member⟩ := hS.nonempty
  exact hS.down member (hA.le B)

theorem IsTuringIdeal.recursiveSets_subset {S : Set (Set ℕ)} (hS : IsTuringIdeal S) :
    recursiveSets ⊆ S :=
  fun _ hA => hS.recursive_mem hA

/-- **The recursive sets form a Turing ideal**, the least one. -/
theorem recursiveSets_isTuringIdeal : IsTuringIdeal recursiveSets where
  nonempty := ⟨∅, isRecursiveSet_empty⟩
  join_mem := fun hA hB =>
    IsRecursiveSet.of_le isRecursiveSet_empty
      (join_le (IsRecursiveSet.le hA ∅) (IsRecursiveSet.le hB ∅))
  down := fun hB h => IsRecursiveSet.of_le hB h

/-- The full power set is a Turing ideal. -/
theorem univ_isTuringIdeal : IsTuringIdeal (Set.univ : Set (Set ℕ)) where
  nonempty := ⟨∅, trivial⟩
  join_mem := fun _ _ => trivial
  down := fun _ _ => trivial

/-- The sets reducible to `B`. -/
def principal (B : Set ℕ) : Set (Set ℕ) :=
  {A | SetTuringLE A B}

theorem principal_isTuringIdeal (B : Set ℕ) : IsTuringIdeal (principal B) where
  nonempty := ⟨B, SetTuringLE.refl B⟩
  join_mem := fun hA hB => join_le hA hB
  down := fun hB h => h.trans hB

/-- Negative example: the empty family is not a Turing ideal. -/
theorem not_isTuringIdeal_empty : ¬ IsTuringIdeal (∅ : Set (Set ℕ)) :=
  fun h => Set.not_nonempty_empty h.nonempty

/-- Negative example: `{∅}` is not a Turing ideal, since it misses the
recursive set `ℕ`. -/
theorem not_isTuringIdeal_singleton_empty : ¬ IsTuringIdeal ({∅} : Set (Set ℕ)) := by
  intro h
  have member : (Set.univ : Set ℕ) ∈ ({∅} : Set (Set ℕ)) := h.recursive_mem isRecursiveSet_univ
  rw [Set.mem_singleton_iff] at member
  exact (Set.univ_nonempty : (Set.univ : Set ℕ).Nonempty).ne_empty member

/-- **Finitely many members of a Turing ideal have a common upper bound in
the ideal.** -/
theorem IsTuringIdeal.exists_upper {S : Set (Set ℕ)} (hS : IsTuringIdeal S) (V : ℕ → Set ℕ)
    (inS : ∀ j, V j ∈ S) : ∀ k : ℕ, ∃ B ∈ S, ∀ j < k, SetTuringLE (V j) B := by
  intro k
  induction k with
  | zero =>
      obtain ⟨B, member⟩ := hS.nonempty
      exact ⟨B, member, fun j hj => absurd hj (Nat.not_lt_zero j)⟩
  | succ k ih =>
      obtain ⟨B, member, below⟩ := ih
      refine ⟨join B (V k), hS.join_mem member (inS k), fun j hj => ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with lt | rfl
      · exact (below j lt).trans (left_le_join B (V k))
      · exact right_le_join B (V j)

/-- The oracles of the first `k` sets of an environment. -/
def envOracles (V : ℕ → Set ℕ) (k : ℕ) : Set (ℕ →. ℕ) :=
  {g | ∃ j < k, g = charFn (V j)}

theorem charFn_mem_envOracles (V : ℕ → Set ℕ) {k j : ℕ} (hj : j < k) :
    charFn (V j) ∈ envOracles V k :=
  ⟨j, hj, rfl⟩

/-- A function computable from the first `k` sets of an environment is
computable from any common upper bound of them. -/
theorem recursiveIn_of_envOracles {V : ℕ → Set ℕ} {k : ℕ} {B : Set ℕ}
    (below : ∀ j < k, SetTuringLE (V j) B) {f : ℕ →. ℕ}
    (hf : Nat.RecursiveIn (envOracles V k) f) : Nat.RecursiveIn {charFn B} f :=
  hf.subst fun _ ⟨j, hj, same⟩ => same ▸ setTuringLE_iff_nat.mp (below j hj)

#print axioms join_le
#print axioms recursiveSets_isTuringIdeal
#print axioms IsTuringIdeal.exists_upper

end Mettapedia.Logic.ReverseMathematics
