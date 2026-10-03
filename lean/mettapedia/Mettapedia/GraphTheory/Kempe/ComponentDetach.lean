import Mettapedia.GraphTheory.Kempe.Boundary

/-!
# Detaching a component by switching its active exits

Consider a set of vertices using colours `a,c`. A separate `a,b`
component contains all its active exits. If no vertex of colour `b` in
that component is adjacent to the set, swapping the component removes
every active exit and introduces none. The set becomes closed for `a,c`.
Connectivity of the set then identifies a new physical component.

The statement permits arbitrarily large sets and switching components.
It derives closure from the old colouring; it does not assume that the
desired second switch is already available.
-/

namespace SimpleGraph.KempeComponentDetach

variable {V α : Type*} {G : SimpleGraph V} [DecidableEq α]

/-- The old active exits disappear, without new active neighbours entering. -/
theorem closed_after_swap (C : G.Coloring α) (a b c : α)
    (K : (C.bicoloredSubgraph a b).ConnectedComponent) (S : Set V)
    (ba : b ≠ a) (bc : b ≠ c)
    (exits : ∀ x ∈ S, ∀ y, y ∉ S → G.Adj x y →
      (C y = a ∨ C y = c) → y ∈ C.kempeComponentSet a b K)
    (no_entry : ∀ x ∈ S, ∀ y ∈ C.kempeComponentSet a b K,
      G.Adj x y → C y ≠ b) :
    ∀ x ∈ S, ∀ y, G.Adj x y →
      ((C.swapOnKempeComponent a b K) y = a ∨
        (C.swapOnKempeComponent a b K) y = c) → y ∈ S := by
  intro x hx y edge active
  by_contra outside
  by_cases switched : y ∈ C.kempeComponentSet a b K
  · have old : C y = a := switched.1.resolve_right (no_entry x hx y switched edge)
    have newColour : (C.swapOnKempeComponent a b K) y = b := by
      rw [C.swapOnKempeComponent_apply_of_mem switched, old, Equiv.swap_apply_left]
    rcases active with active | active
    · exact ba (newColour.symm.trans active)
    · exact bc (newColour.symm.trans active)
  · have old : C y = a ∨ C y = c := by
      simpa only [C.swapOnKempeComponent_apply_of_not_mem switched] using active
    exact switched (exits x hx y outside edge old)

/-- The detached set retains its old colours when the first component is
disjoint. Its existing connected paths can be reused by the next switch. -/
theorem active_after_swap (C : G.Coloring α) (a b c : α)
    (K : (C.bicoloredSubgraph a b).ConnectedComponent) (S : Set V)
    (apart : Disjoint S (C.kempeComponentSet a b K))
    (active : ∀ x ∈ S, C x = a ∨ C x = c) :
    ∀ x ∈ S, (C.swapOnKempeComponent a b K) x = a ∨
      (C.swapOnKempeComponent a b K) x = c := by
  intro x hx
  have outside := Set.disjoint_left.mp apart hx
  simpa only [C.swapOnKempeComponent_apply_of_not_mem outside] using active x hx

end SimpleGraph.KempeComponentDetach
