import Mettapedia.GraphTheory.Kempe.ComponentDetach
import Mettapedia.GraphTheory.Kempe.SeparatedChains

/-!
# Releasing a vertex after a component switch

A vertex has colour b and has no neighbour of colour c. Switching an a/b
component containing it makes that vertex a complete singleton a/c
component. Both the old-exit and no-new-entry conditions follow from the
old colouring. The graph, palette and first component may be arbitrarily
large. The resulting two-step history changes only that component.
-/

namespace SimpleGraph.KempeSingletonRelease

open Mettapedia.GraphTheory.FourColor.KempeChainCertificate

variable {V α : Type*} {G : SimpleGraph V} [DecidableEq V] [DecidableEq α]
  (C : G.Coloring α) (a b c : α)
  (K : (C.bicoloredSubgraph a b).ConnectedComponent) (v : V)
  (colour : C v = b) (member : v ∈ C.kempeComponentSet a b K)
  (ba : b ≠ a) (bc : b ≠ c)
  (missing : ∀ y, G.Adj v y → C y ≠ c)

include colour member ba bc missing in
omit [DecidableEq V] in
/-- Closure of the second component is derived entirely from the old state. -/
theorem singleton_closed : ∀ x ∈ ([v] : List V), ∀ y, G.Adj x y →
    ((C.swapOnKempeComponent a b K) y = a ∨
      (C.swapOnKempeComponent a b K) y = c) → y ∈ ([v] : List V) := by
  have exits : ∀ x ∈ ({v} : Set V), ∀ y, y ∉ ({v} : Set V) → G.Adj x y →
      (C y = a ∨ C y = c) → y ∈ C.kempeComponentSet a b K := by
    intro x hx y _ edge active
    have eq : x = v := hx
    subst x
    exact C.mem_kempeComponentSet_of_adj member edge (active.elim
      (fun h => Or.inl h) (fun h => (missing y edge h).elim))
  have no_entry : ∀ x ∈ ({v} : Set V), ∀ y ∈ C.kempeComponentSet a b K,
      G.Adj x y → C y ≠ b := by
    intro x hx y _ edge h
    have eq : x = v := hx
    subst x
    exact C.valid edge (colour.trans h.symm)
  have closed := KempeComponentDetach.closed_after_swap C a b c K {v} ba bc exits no_entry
  intro x hx y edge active
  exact List.mem_singleton.mpr (closed x (List.mem_singleton.mp hx) y edge active)

/-- The second physical component, obtained without checking a new colouring. -/
noncomputable def second :
    KempeSeparatedChains.Certificate (C.swapOnKempeComponent a b K) a c where
  vertices := [v]
  root := v
  root_mem := by simp
  connected := by simp
  active := by
    intro x hx
    have eq := List.mem_singleton.mp hx
    subst x
    left
    rw [C.swapOnKempeComponent_apply_of_mem member,colour,Equiv.swap_apply_right]
  closed := singleton_closed C a b c K v colour member ba bc missing

noncomputable def history :
    History C (second C a b c K v colour member ba bc missing).swap :=
  .cons (.switch C a b K)
    (.cons (second C a b c K v colour member ba bc missing).step (.refl _))

theorem history_length : (history C a b c K v colour member ba bc missing).length = 2 := rfl

theorem endpoint (x : V) :
    (second C a b c K v colour member ba bc missing).swap x =
      if x = v then c else (C.swapOnKempeComponent a b K) x := by
  rw [KempeSeparatedChains.Certificate.swap_apply]
  change (if x ∈ [v] then _ else _) = _
  by_cases h : x = v
  · subst x
    simp only [List.mem_singleton,ite_true]
    rw [C.swapOnKempeComponent_apply_of_mem member,colour,
      Equiv.swap_apply_right,Equiv.swap_apply_left]
  · simp [h]

theorem fixed_outside (x : V) (outside : x ∉ C.kempeComponentSet a b K) :
    (second C a b c K v colour member ba bc missing).swap x = C x := by
  have ne : x ≠ v := fun h => outside (h ▸ member)
  rw [endpoint,ite_eq_right ne,C.swapOnKempeComponent_apply_of_not_mem outside]

end SimpleGraph.KempeSingletonRelease
