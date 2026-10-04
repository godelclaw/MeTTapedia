import Mettapedia.GraphTheory.Kempe.ListPropagation

/-!
# Composing conditional colour implications

A local implication uses one actual edge and the allowed colours at its
destination. Chaining such implications preserves the same colouring
witness throughout. Two paths forcing opposite choices at one vertex
refute a list colouring, even when every individual list has local support.
-/

namespace SimpleGraph.ColoringListPropagation

variable {V A : Type*} {G : SimpleGraph V}

/-- Fixing the first literal forces the second through one actual edge. -/
def Forces (G : SimpleGraph V) (L : V → Finset A) (p q : V × A) : Prop :=
  G.Adj p.1 q.1 ∧ ∀ a ∈ L q.1, a ≠ p.2 → a = q.2

theorem forces_sound (L : V → Finset A) (C : G.Coloring A)
    (fit : ∀ v, C v ∈ L v) {p q : V × A} (step : Forces G L p q)
    (start : C p.1 = p.2) : C q.1 = q.2 :=
  step.2 _ (fit q.1) (start ▸ (C.valid step.1).symm)

/-- An arbitrary-length implication path retains one common witness. -/
theorem path_forces {n : ℕ} (L : V → Finset A) (C : G.Coloring A)
    (fit : ∀ v, C v ∈ L v) (p : Fin (n+1) → V × A)
    (steps : ∀ i : Fin n, Forces G L (p i.castSucc) (p i.succ))
    (start : C (p 0).1 = (p 0).2) : ∀ i, C (p i).1 = (p i).2 := by
  refine Fin.induction start ?_
  intro i ih
  exact forces_sound L C fit (steps i) ih

end SimpleGraph.ColoringListPropagation
