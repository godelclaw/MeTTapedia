import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Card
import Mathlib.Logic.Relation

/-!
# Computable reachability closure on a finite vertex type

For a Boolean adjacency `adj`, `reachFrom adj u` is the closure of `{u}` under one-step
extension, iterated as many times as there are vertices; it is exactly the set of vertices
reachable from `u` by the reflexive-transitive closure of `adj` (`mem_reachFrom_iff`).
The kernel can evaluate it for a concrete adjacency.
-/

namespace Mettapedia.GraphTheory.FourColor
namespace ReachClosure

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- One closure step: add every vertex adjacent from a member. -/
def step (adj : V → V → Bool) (S : Finset V) : Finset V :=
  S ∪ Finset.univ.filter fun v => ∃ u ∈ S, adj u v = true

/-- `n` closure steps. -/
def closure (adj : V → V → Bool) (S : Finset V) : Nat → Finset V
  | 0 => S
  | n + 1 => step adj (closure adj S n)

/-- The vertices reachable from `u`. -/
def reachFrom (adj : V → V → Bool) (u : V) : Finset V :=
  closure adj {u} (Fintype.card V)

/-- The step relation of a Boolean adjacency. -/
def Adj (adj : V → V → Bool) (u v : V) : Prop := adj u v = true

theorem mem_step_iff (adj : V → V → Bool) (S : Finset V) (v : V) :
    v ∈ step adj S ↔ v ∈ S ∨ ∃ u ∈ S, adj u v = true := by
  simp [step]

theorem subset_step (adj : V → V → Bool) (S : Finset V) : S ⊆ step adj S :=
  Finset.subset_union_left

theorem closure_subset_succ (adj : V → V → Bool) (S : Finset V) (n : Nat) :
    closure adj S n ⊆ closure adj S (n + 1) :=
  subset_step _ _

theorem closure_mono (adj : V → V → Bool) (S : Finset V) {m n : Nat} (h : m ≤ n) :
    closure adj S m ⊆ closure adj S n := by
  induction h with
  | refl => exact Finset.Subset.refl _
  | step _ ih => exact Finset.Subset.trans ih (closure_subset_succ _ _ _)

/-- Soundness: closure members are reachable. -/
theorem reflTransGen_of_mem_closure (adj : V → V → Bool) (u : V) (n : Nat) :
    ∀ v ∈ closure adj {u} n, Relation.ReflTransGen (Adj adj) u v := by
  induction n with
  | zero =>
    intro v hv
    simp only [closure, Finset.mem_singleton] at hv
    subst hv
    exact Relation.ReflTransGen.refl
  | succ n ih =>
    intro v hv
    rw [closure, mem_step_iff] at hv
    rcases hv with hv | ⟨w, hw, hadj⟩
    · exact ih v hv
    · exact (ih w hw).tail hadj

/-- A stable closure contains everything reachable from its members. -/
theorem mem_closure_of_reflTransGen (adj : V → V → Bool) (S : Finset V) (n : Nat)
    (hstable : closure adj S n = closure adj S (n + 1))
    {u v : V} (h : Relation.ReflTransGen (Adj adj) u v) (hu : u ∈ closure adj S n) :
    v ∈ closure adj S n := by
  induction h with
  | refl => exact hu
  | tail _ hstep ih =>
    rw [hstable, closure, mem_step_iff]
    exact Or.inr ⟨_, ih, hstep⟩

theorem closure_add_of_stable (adj : V → V → Bool) (S : Finset V) {n : Nat}
    (h : closure adj S n = closure adj S (n + 1)) :
    ∀ m, closure adj S (n + m) = closure adj S n := by
  intro m
  induction m with
  | zero => rfl
  | succ m ih =>
    show step adj (closure adj S (n + m)) = _
    rw [ih]
    exact h.symm

theorem card_closure_ge (adj : V → V → Bool) (S : Finset V) :
    ∀ k, (∀ j < k, closure adj S j ≠ closure adj S (j + 1)) →
      S.card + k ≤ (closure adj S k).card := by
  intro k
  induction k with
  | zero => intro _; simp [closure]
  | succ k ih =>
    intro hstrict
    have h1 := ih fun j hj => hstrict j (by omega)
    have hlt : (closure adj S k).card < (closure adj S (k + 1)).card :=
      Finset.card_lt_card
        (Finset.ssubset_iff_subset_ne.2 ⟨closure_subset_succ adj S k, hstrict k (by omega)⟩)
    omega

theorem exists_stable_le (adj : V → V → Bool) (S : Finset V) (hS : S.Nonempty) :
    ∃ n ≤ Fintype.card V, closure adj S n = closure adj S (n + 1) := by
  by_contra hcon
  simp only [not_exists, not_and] at hcon
  have h1 := card_closure_ge adj S (Fintype.card V) fun j hj => hcon j hj.le
  have h2 := Finset.card_le_univ (closure adj S (Fintype.card V))
  have h3 := hS.card_pos
  omega

theorem closure_card_stable (adj : V → V → Bool) (S : Finset V) (hS : S.Nonempty) :
    closure adj S (Fintype.card V) = closure adj S (Fintype.card V + 1) := by
  obtain ⟨n, hn, hstable⟩ := exists_stable_le adj S hS
  have h1 := closure_add_of_stable adj S hstable (Fintype.card V - n)
  have h2 := closure_add_of_stable adj S hstable (Fintype.card V + 1 - n)
  rw [show n + (Fintype.card V - n) = Fintype.card V by omega] at h1
  rw [show n + (Fintype.card V + 1 - n) = Fintype.card V + 1 by omega] at h2
  rw [h1, h2]

/-- **The computed reachable set is exact.** -/
theorem mem_reachFrom_iff (adj : V → V → Bool) (u v : V) :
    v ∈ reachFrom adj u ↔ Relation.ReflTransGen (Adj adj) u v := by
  constructor
  · exact reflTransGen_of_mem_closure adj u _ v
  · intro h
    exact mem_closure_of_reflTransGen adj {u} _
      (closure_card_stable adj {u} (Finset.singleton_nonempty u)) h
      (closure_mono adj {u} (Nat.zero_le _) (by simp [closure]))

/-- Everything is reachable from everything. -/
def allReach (adj : V → V → Bool) : Bool :=
  decide (∀ u, reachFrom adj u = Finset.univ)

theorem reflTransGen_of_allReach (adj : V → V → Bool) (h : allReach adj = true) (u v : V) :
    Relation.ReflTransGen (Adj adj) u v := by
  rw [← mem_reachFrom_iff, of_decide_eq_true h u]
  exact Finset.mem_univ v

end ReachClosure
end Mettapedia.GraphTheory.FourColor
