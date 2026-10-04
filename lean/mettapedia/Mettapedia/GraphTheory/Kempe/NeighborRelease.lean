import Mettapedia.GraphTheory.Kempe.ComponentDetach
import Mettapedia.GraphTheory.Kempe.SeparatedChains

/-! # Releasing an unchanged vertex by switching its neighbours

A vertex of colour c stays outside an a/b component. If that component
contains every a-coloured neighbour and no b-coloured neighbour, switching
it makes the vertex a singleton a/c component. The second switch follows
from the old colouring. Graph, palette and component sizes are unrestricted.
-/

namespace SimpleGraph.KempeNeighborRelease

open Mettapedia.GraphTheory.FourColor.KempeChainCertificate

variable {V α : Type*} {G : SimpleGraph V} [DecidableEq V] [DecidableEq α]
  (C : G.Coloring α) (a b c : α)
  (K : (C.bicoloredSubgraph a b).ConnectedComponent) (v : V)
  (colour : C v = c) (ca : c ≠ a) (cb : c ≠ b) (ba : b ≠ a)
  (exits : ∀ y, G.Adj v y → C y = a → y ∈ C.kempeComponentSet a b K)
  (no_entry : ∀ y ∈ C.kempeComponentSet a b K, G.Adj v y → C y ≠ b)

include colour ca cb in
omit [DecidableEq V] in
theorem outside : v ∉ C.kempeComponentSet a b K := by
  intro h
  have active := C.mem_bicoloredSet_of_mem_kempeComponentSet h
  rw [colour] at active
  exact active.elim ca cb

include colour ca cb ba exits no_entry in
omit [DecidableEq V] in
theorem singleton_closed : ∀ x ∈ ([v] : List V), ∀ y, G.Adj x y →
    ((C.swapOnKempeComponent a b K) y = a ∨
      (C.swapOnKempeComponent a b K) y = c) → y ∈ ([v] : List V) := by
  have old_exits : ∀ x ∈ ({v} : Set V), ∀ y, y ∉ ({v} : Set V) → G.Adj x y →
      (C y = a ∨ C y = c) → y ∈ C.kempeComponentSet a b K := by
    intro x hx y _ edge active
    have eq : x = v := hx
    subst x
    rcases active with h | h
    · exact exits y edge h
    · exact (C.valid edge (colour.trans h.symm)).elim
  have old_entry : ∀ x ∈ ({v} : Set V), ∀ y ∈ C.kempeComponentSet a b K,
      G.Adj x y → C y ≠ b := by
    intro x hx y hy edge
    have eq : x = v := hx
    subst x
    exact no_entry y hy edge
  have closed := KempeComponentDetach.closed_after_swap C a b c K {v} ba cb.symm
    old_exits old_entry
  intro x hx y edge active
  exact List.mem_singleton.mpr (closed x (List.mem_singleton.mp hx) y edge active)

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
    right
    rw [C.swapOnKempeComponent_apply_of_not_mem (outside C a b c K v colour ca cb)]
    exact colour
  closed := singleton_closed C a b c K v colour ca cb ba exits no_entry

noncomputable def history :
    History C (second C a b c K v colour ca cb ba exits no_entry).swap :=
  .cons (.switch C a b K)
    (.cons (second C a b c K v colour ca cb ba exits no_entry).step (.refl _))

theorem history_length :
    (history C a b c K v colour ca cb ba exits no_entry).length = 2 := rfl

theorem endpoint (x : V) :
    (second C a b c K v colour ca cb ba exits no_entry).swap x =
      if x = v then a else (C.swapOnKempeComponent a b K) x := by
  rw [KempeSeparatedChains.Certificate.swap_apply]
  change (if x ∈ [v] then _ else _) = _
  by_cases h : x = v
  · subst x
    simp only [List.mem_singleton,ite_true]
    rw [C.swapOnKempeComponent_apply_of_not_mem (outside C a b c K v colour ca cb),
      colour,Equiv.swap_apply_right]
  · simp [h]

end SimpleGraph.KempeNeighborRelease
