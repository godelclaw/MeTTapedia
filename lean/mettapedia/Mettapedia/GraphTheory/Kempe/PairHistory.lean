import Mettapedia.GraphTheory.Kempe.PairDecomposition

/-!
# Normal form of a fixed-pair Kempe history

Every finite history using one fixed colour pair is a proper partial
transposition of the original colouring. Its changed set is a union of
original bichromatic components. Thus the possible boundary endpoints of
an arbitrarily long phase are determined by choices on the original
components meeting the boundary. Switching other colour pairs can change
those components, so this normal form does not extend to mixed-pair histories.
-/

namespace SimpleGraph.KempePairHistory

variable {V α : Type*} {G : SimpleGraph V} [DecidableEq α]

def Step (a b : α) (C D : G.Coloring α) : Prop :=
  ∃ K : (C.bicoloredSubgraph a b).ConnectedComponent, D = C.swapOnKempeComponent a b K

/-- Arbitrarily many fixed-pair switches have just a partial transposition
as their net effect. No finiteness or planarity hypothesis is needed. -/
theorem pointwise {a b : α} {C D : G.Coloring α}
    (history : Relation.ReflTransGen (Step a b) C D) :
    ∀ v, D v = C v ∨ D v = Equiv.swap a b (C v) := by
  induction history with
  | refl => exact fun _ => Or.inl rfl
  | @tail D E history step ih =>
      obtain ⟨K, rfl⟩ := step
      intro v
      by_cases hv : v ∈ D.kempeComponentSet a b K
      · rw [D.swapOnKempeComponent_apply_of_mem hv]
        rcases ih v with he | he
        · exact Or.inr (congrArg (Equiv.swap a b) he)
        · exact Or.inl (by rw [he, Equiv.swap_apply_self])
      · rw [D.swapOnKempeComponent_apply_of_not_mem hv]
        exact ih v

/-- A changed vertex forces its entire *original* component to change.
This is the normal form used to exhaust fixed-pair boundary endpoints. -/
theorem component_changed {a b : α} {C D : G.Coloring α}
    (history : Relation.ReflTransGen (Step a b) C D)
    {u : V} (changed : D u ≠ C u) (active : u ∈ C.bicoloredSet a b) :
    C.kempeComponentSet a b
      ((C.bicoloredSubgraph a b).connectedComponentMk ⟨u, active⟩) ⊆
        {v | D v ≠ C v} :=
  C.component_changed_of_pointwise_swap D a b (pointwise history) changed active

theorem physical {a b : α} {C D : G.Coloring α}
    (history : Relation.ReflTransGen (Step a b) C D) : D ∈ G.KempeClosure C :=
  Relation.ReflTransGen.mono (fun _ _ h => by
    obtain ⟨K, rfl⟩ := h
    exact ⟨a, b, K, rfl⟩) _ _ history

end SimpleGraph.KempePairHistory
