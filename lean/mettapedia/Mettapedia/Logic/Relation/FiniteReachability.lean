import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.Card
import Mathlib.Logic.Relation

/-!
# Reachability in a finite relation, computed by saturation

A finite set of points is saturated under a successor function `next` by repeatedly
adding the successors of its members, stopping at the first round that adds nothing.
On a finite type `Fintype.card α` rounds always suffice, and the result `reachSet next s`
is exactly the set of points reachable from `s` (`mem_reachSet_iff`): reflexive-transitive
closure is computed, not merely bounded.

For a decidable relation `r` the successor function is `fun a => {b | r a b}`; then
`reachFrom r a` is the set of `b` with `Relation.ReflTransGen r a b`, which makes
`ReflTransGen r` and `TransGen r` decidable on a finite type.  Everything here is a plain
finset computation, so the kernel evaluates it on concrete data; for sparse relations a
successor function given by adjacency lists keeps each round cheap.  Reachability is the
single-premise case of Horn-clause saturation (`Mettapedia.Logic.LP.saturate`); working
along a successor function avoids scanning one rule per pair of points in every round.

## Main results

* `mem_reachSet_iff`: membership in the saturation is reachability from the seed set.
* `mem_reachFrom_iff`: the same for one seed and a decidable relation.
* `decidableReflTransGen`, `decidableTransGen`: the induced decision procedures.
* `forall_reflTransGen_iff`: every point reaches every point iff every saturation is total.
-/

namespace Mettapedia.Logic.Relation

open _root_.Relation

variable {α : Type*} [DecidableEq α]

section Successors

variable (next : α → Finset α)

/-- One saturation round: add the successors of every member. -/
def saturateStep (s : Finset α) : Finset α :=
  s ∪ s.biUnion next

/-- Saturation with `n` rounds of fuel, stopping at the first round that adds nothing. -/
def saturate : ℕ → Finset α → Finset α
  | 0, s => s
  | n + 1, s =>
      if (saturateStep next s).card ≤ s.card then s else saturate n (saturateStep next s)

variable {next}

theorem mem_saturateStep {s : Finset α} {b : α} :
    b ∈ saturateStep next s ↔ b ∈ s ∨ ∃ a ∈ s, b ∈ next a := by
  simp [saturateStep]

theorem subset_saturateStep (s : Finset α) : s ⊆ saturateStep next s :=
  Finset.subset_union_left

/-- A round that does not grow the set changes nothing. -/
theorem saturateStep_eq_of_card_le {s : Finset α} (h : (saturateStep next s).card ≤ s.card) :
    saturateStep next s = s :=
  (Finset.eq_of_subset_of_card_le (subset_saturateStep s) h).symm

theorem subset_saturate (n : ℕ) (s : Finset α) : s ⊆ saturate next n s := by
  induction n generalizing s with
  | zero => exact Finset.Subset.refl s
  | succ n ih =>
      rw [saturate]
      split_ifs
      · exact Finset.Subset.refl s
      · exact (subset_saturateStep s).trans (ih _)

/-- Every member of a saturation lies in each successor-closed superset of the seed. -/
theorem saturate_subset_of_closed {t : Finset α} (htnext : ∀ a ∈ t, next a ⊆ t) :
    ∀ (n : ℕ) (s : Finset α), s ⊆ t → saturate next n s ⊆ t := by
  intro n
  induction n with
  | zero => intro s hs; exact hs
  | succ n ih =>
      intro s hs
      rw [saturate]
      split_ifs
      · exact hs
      · refine ih _ ?_
        intro b hb
        rcases mem_saturateStep.mp hb with hb | ⟨a, ha, hab⟩
        · exact hs hb
        · exact htnext a (hs ha) hab

/-- With enough fuel the saturation is closed under successors. -/
theorem saturateStep_saturate [Fintype α] :
    ∀ (n : ℕ) (s : Finset α), Fintype.card α ≤ n + s.card →
      saturateStep next (saturate next n s) = saturate next n s := by
  intro n
  induction n with
  | zero =>
      intro s hs
      have huniv : s = Finset.univ :=
        Finset.eq_univ_of_card s (le_antisymm (Finset.card_le_univ s) (by simpa using hs))
      subst huniv
      show saturateStep next Finset.univ = Finset.univ
      exact Finset.eq_univ_of_forall fun b => mem_saturateStep.mpr (Or.inl (Finset.mem_univ b))
  | succ n ih =>
      intro s hs
      rw [saturate]
      split_ifs with hle
      · exact saturateStep_eq_of_card_le hle
      · exact ih _ (by omega)

end Successors

section Reach

variable [Fintype α] (next : α → Finset α)

/-- The points reachable from `s` along `next`. -/
def reachSet (s : Finset α) : Finset α :=
  saturate next (Fintype.card α) s

variable {next}

/-- **The saturation is exactly the reachable set.** -/
theorem mem_reachSet_iff {s : Finset α} {b : α} :
    b ∈ reachSet next s ↔ ∃ a ∈ s, ReflTransGen (fun x y => y ∈ next x) a b := by
  classical
  constructor
  · intro hb
    -- the reachable points form a successor-closed superset of the seed
    let t : Finset α := Finset.univ.filter fun c =>
      ∃ a ∈ s, ReflTransGen (fun x y => y ∈ next x) a c
    have hst : s ⊆ t := fun a ha => Finset.mem_filter.mpr ⟨Finset.mem_univ a, a, ha, .refl⟩
    have ht : ∀ c ∈ t, next c ⊆ t := by
      intro c hc d hd
      obtain ⟨a, ha, hac⟩ := (Finset.mem_filter.mp hc).2
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ d, a, ha, hac.tail hd⟩
    exact (Finset.mem_filter.mp (saturate_subset_of_closed ht _ s hst hb)).2
  · rintro ⟨a, ha, hab⟩
    have hclosed := saturateStep_saturate (next := next) (Fintype.card α) s (by omega)
    induction hab with
    | refl => exact subset_saturate _ s ha
    | tail _ hcd ih =>
        rw [reachSet, ← hclosed]
        exact mem_saturateStep.mpr (Or.inr ⟨_, ih, hcd⟩)

theorem subset_reachSet (s : Finset α) : s ⊆ reachSet next s :=
  subset_saturate _ s

/-- The reachable set is the least successor-closed superset of the seed. -/
theorem reachSet_subset_of_closed {s t : Finset α} (hst : s ⊆ t)
    (ht : ∀ a ∈ t, next a ⊆ t) : reachSet next s ⊆ t :=
  saturate_subset_of_closed ht _ s hst

theorem saturateStep_reachSet (s : Finset α) :
    saturateStep next (reachSet next s) = reachSet next s :=
  saturateStep_saturate _ s (by omega)

end Reach

section Relation

variable [Fintype α] (r : α → α → Prop) [DecidableRel r]

/-- The points `r`-reachable from `a`, computed by saturation. -/
def reachFrom (a : α) : Finset α :=
  reachSet (fun x => Finset.univ.filter (r x)) {a}

variable {r}

/-- **The computed reachable set is exact.** -/
theorem mem_reachFrom_iff {a b : α} : b ∈ reachFrom r a ↔ ReflTransGen r a b := by
  rw [reachFrom, mem_reachSet_iff]
  simp only [Finset.mem_singleton, exists_eq_left, Finset.mem_filter, Finset.mem_univ, true_and]

theorem self_mem_reachFrom (a : α) : a ∈ reachFrom r a :=
  mem_reachFrom_iff.mpr .refl

/-- Reflexive-transitive closure of a decidable relation on a finite type is decidable,
by saturation. -/
instance decidableReflTransGen : DecidableRel (ReflTransGen r) := fun _ _ =>
  decidable_of_iff _ mem_reachFrom_iff

/-- Transitive closure of a decidable relation on a finite type is decidable. -/
instance decidableTransGen : DecidableRel (TransGen r) := fun a b =>
  decidable_of_iff (∃ c, r a c ∧ b ∈ reachFrom r c) <| by
    simp only [mem_reachFrom_iff]
    exact TransGen.head'_iff.symm

/-- Every point reaches every point exactly when each computed reachable set is total. -/
theorem forall_reflTransGen_iff :
    (∀ a b, ReflTransGen r a b) ↔ ∀ a, reachFrom r a = Finset.univ := by
  constructor
  · intro h a
    exact Finset.eq_univ_of_forall fun b => mem_reachFrom_iff.mpr (h a b)
  · intro h a b
    exact mem_reachFrom_iff.mp (h a ▸ Finset.mem_univ b)

end Relation

end Mettapedia.Logic.Relation
