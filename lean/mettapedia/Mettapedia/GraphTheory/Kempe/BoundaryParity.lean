import Mettapedia.GraphTheory.Kempe.ComponentDetach
import Mathlib.Combinatorics.SimpleGraph.Coloring.Constructions

/-!
# An odd external boundary prevents component detachment

The external neighbours of a closed two-colour region use only the two
remaining colours. Their induced graph must therefore be bipartite. An
odd closed walk among those neighbours obstructs the proposed region in
**every** proper four-colouring, independently of the length or choice of
preparatory recolourings. Enlarging the region changes this obstruction.
-/

namespace SimpleGraph.KempeBoundaryParity

variable {V : Type*} {G : SimpleGraph V}

/-- Neighbours outside the retained region, with adjacency witnesses. -/
def outside (G : SimpleGraph V) (S : Set V) : Set V :=
  {y | y ∉ S ∧ ∃ x ∈ S, G.Adj x y}

/-- Closure under neighbours carrying either selected colour. -/
def Closed (C : G.Coloring (Fin 4)) (a b : Fin 4) (S : Set V) : Prop :=
  ∀ x ∈ S, ∀ y, G.Adj x y → (C y = a ∨ C y = b) → y ∈ S

private theorem remaining_two (a b : Fin 4) (different : a ≠ b) :
    ∃ p q : Fin 4, ∀ k : Fin 4, k ≠ a → k ≠ b → k = p ∨ k = q := by
  have h : ∀ a b : Fin 4, a ≠ b →
      ∃ p q : Fin 4, ∀ k : Fin 4, k ≠ a → k ≠ b → k = p ∨ k = q := by decide +kernel
  exact h a b different

/-- A necessary geometric condition for isolating any proposed region. -/
theorem outside_two_colorable (C : G.Coloring (Fin 4)) (a b : Fin 4)
    (different : a ≠ b) (S : Set V) (closed : Closed C a b S) :
    (G.induce (outside G S)).Colorable 2 := by
  classical
  obtain ⟨p, q, cover⟩ := remaining_two a b different
  have remaining (v : outside G S) : C v = p ∨ C v = q := by
    obtain ⟨notin, x, hx, edge⟩ := v.property
    apply cover
    · exact fun h => notin (closed x hx v edge (Or.inl h))
    · exact fun h => notin (closed x hx v edge (Or.inr h))
  let D : (G.induce (outside G S)).Coloring Bool := .mk (fun v => decide (C v = p)) (by
    intro u v edge equal
    have hu := remaining u
    have hv := remaining v
    apply C.valid edge
    by_cases up : C u = p <;> by_cases vp : C v = p
    · exact up.trans vp.symm
    · simp [up, vp] at equal
    · simp [up, vp] at equal
    · exact (hu.resolve_left up).trans (hv.resolve_left vp).symm)
  simpa using D.colorable

/-- An odd boundary walk forces some selected-colour exit, in every proper
four-colouring. The walk need not be simple or the graph finite or planar. -/
theorem not_closed_of_odd_walk (S : Set V) {v : V} (w : G.Walk v v)
    (external : ∀ x ∈ w.support, x ∈ outside G S) (odd : Odd w.length)
    (C : G.Coloring (Fin 4)) (a b : Fin 4) (different : a ≠ b) :
    ¬ Closed C a b S := by
  intro closed
  have colourable := outside_two_colorable C a b different S closed
  have even := (two_colorable_iff_forall_loop_even.mp colourable) _
    (w.induce (outside G S) external)
  have length_eq : (w.induce (outside G S) external).length = w.length := by
    have h := congrArg List.length (Walk.support_induce (G := G) (s := outside G S) w external)
    simp only [Walk.length_support, List.length_attachWith] at h
    omega
  rw [length_eq] at even
  exact (Nat.not_even_iff_odd.mpr odd) even

/-- A proposed region with an odd external boundary cannot be the exact
support of a component after any sequence of preparation steps. -/
theorem component_ne_of_odd_walk (S : Set V) {v : V} (w : G.Walk v v)
    (external : ∀ x ∈ w.support, x ∈ outside G S) (odd : Odd w.length)
    (C : G.Coloring (Fin 4)) (a b : Fin 4) (different : a ≠ b)
    (K : (C.bicoloredSubgraph a b).ConnectedComponent) :
    C.kempeComponentSet a b K ≠ S := by
  intro equal
  apply not_closed_of_odd_walk S w external odd C a b different
  intro x hx y edge active
  rw [← equal] at hx ⊢
  exact C.mem_kempeComponentSet_of_adj hx edge active

/-- A closed enlargement must absorb a vertex of every obstructing odd
walk. This is a necessary condition on region growth, not a supply law. -/
theorem absorb_odd_walk (S T : Set V) (inclusion : S ⊆ T) {v : V}
    (w : G.Walk v v) (external : ∀ x ∈ w.support, x ∈ outside G S)
    (odd : Odd w.length) (C : G.Coloring (Fin 4)) (a b : Fin 4)
    (different : a ≠ b) (closed : Closed C a b T) :
    ∃ x ∈ w.support, x ∈ T := by
  classical
  by_contra none
  apply not_closed_of_odd_walk T w ?_ odd C a b different closed
  intro x hx
  obtain ⟨_, y, hy, edge⟩ := external x hx
  exact ⟨fun h => none ⟨x, hx, h⟩, y, inclusion hy, edge⟩

end SimpleGraph.KempeBoundaryParity
