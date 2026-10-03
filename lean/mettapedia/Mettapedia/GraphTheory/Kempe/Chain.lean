import Mettapedia.GraphTheory.Kempe
import Mathlib.Data.List.Chain

/-!
# Physical components certified by saturated chains

A connected list of active vertices closed under active neighbours is an
actual Kempe component. Its swap is therefore the pointwise transposition
on that list. This finite certificate does not enumerate walks.
-/

namespace SimpleGraph.Coloring

variable {V α : Type*} {G : SimpleGraph V}
variable (C : G.Coloring α) (a b : α)
variable (K : (C.bicoloredSubgraph a b).ConnectedComponent)

/-- A connected, saturated list describes an actual component, not merely
a set on which swapping happens to preserve properness. -/
theorem kempe_component_iff_mem_chain (chain : List V)
    (hchain : chain.IsChain G.Adj)
    (hactive : ∀ x ∈ chain, C x = a ∨ C x = b)
    (hclosed : ∀ x ∈ chain, ∀ y, G.Adj x y → (C y = a ∨ C y = b) → y ∈ chain)
    {x : V} (hx : x ∈ chain) (hxK : x ∈ C.kempeComponentSet a b K) (y : V) :
    y ∈ C.kempeComponentSet a b K ↔ y ∈ chain := by
  constructor
  · rintro ⟨hy, hyK⟩
    obtain ⟨hxa, hxc⟩ := hxK
    obtain ⟨w⟩ := ConnectedComponent.exact (hxc.trans hyK.symm)
    have carries {u v : C.bicoloredSet a b}
        (p : (C.bicoloredSubgraph a b).Walk u v) : u.val ∈ chain → v.val ∈ chain := by
      induction p with
      | nil => exact id
      | @cons u v z huv p ih => exact fun hu => ih (hclosed u.val hu v.val huv v.property)
    exact carries w hx
  · intro hy
    have hc : chain.IsChain (fun u v =>
        u ∈ C.kempeComponentSet a b K ↔ v ∈ C.kempeComponentSet a b K) :=
      hchain.imp_of_mem_imp fun u v hu hv huv =>
        ⟨fun h => C.mem_kempeComponentSet_of_adj h huv (hactive v hv),
          fun h => C.mem_kempeComponentSet_of_adj h huv.symm (hactive u hu)⟩
    cases chain with
    | nil => simp at hx
    | cons root rest =>
        have fromRoot (z : V) (hz : z ∈ root :: rest) :
            root ∈ C.kempeComponentSet a b K ↔ z ∈ C.kempeComponentSet a b K := by
          rcases List.mem_cons.mp hz with rfl | hz
          · rfl
          · exact hc.rel_cons hz
        exact (fromRoot y hy).mp ((fromRoot x hx).mpr hxK)

/-- The existing component operation agrees pointwise with its saturated
chain certificate. -/
theorem swap_apply_of_chain [DecidableEq V] [DecidableEq α] (chain : List V)
    (hchain : chain.IsChain G.Adj)
    (hactive : ∀ x ∈ chain, C x = a ∨ C x = b)
    (hclosed : ∀ x ∈ chain, ∀ y, G.Adj x y → (C y = a ∨ C y = b) → y ∈ chain)
    {x : V} (hx : x ∈ chain) (hxK : x ∈ C.kempeComponentSet a b K) (y : V) :
    C.swapOnKempeComponent a b K y =
      if y ∈ chain then Equiv.swap a b (C y) else C y := by
  classical
  by_cases hy : y ∈ chain
  · rw [ite_eq_left hy]
    exact C.swapOnKempeComponent_apply_of_mem
      ((C.kempe_component_iff_mem_chain a b K chain hchain hactive hclosed hx hxK y).mpr hy)
  · rw [ite_eq_right hy]
    exact C.swapOnKempeComponent_apply_of_not_mem (fun h =>
      hy ((C.kempe_component_iff_mem_chain a b K chain hchain hactive hclosed hx hxK y).mp h))

end SimpleGraph.Coloring
