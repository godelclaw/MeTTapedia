import Mettapedia.GraphTheory.Kempe.Chain
import Mettapedia.GraphTheory.Kempe.Boundary

/-!
# Boundary anchors freeze a colouring

Connected bichromatic chains give a small certificate that every component
meets the protected boundary. Saturation of the chains is unnecessary:
their only purpose is to connect each active vertex to an anchor.
-/

namespace SimpleGraph.Coloring

variable {V α : Type*} {G : SimpleGraph V} (C : G.Coloring α)

theorem mem_component_along_chain (a b : α)
    (K : (C.bicoloredSubgraph a b).ConnectedComponent)
    (chain : List V) (connected : chain.IsChain G.Adj)
    (active : ∀ x ∈ chain, C x = a ∨ C x = b)
    {u v : V} (hu : u ∈ chain) (hv : v ∈ chain)
    (member : u ∈ C.kempeComponentSet a b K) :
    v ∈ C.kempeComponentSet a b K := by
  have carries : chain.IsChain (fun x y =>
      x ∈ C.kempeComponentSet a b K ↔ y ∈ C.kempeComponentSet a b K) :=
    connected.imp_of_mem_imp fun x y hx hy edge =>
      ⟨fun h => C.mem_kempeComponentSet_of_adj h edge (active y hy),
       fun h => C.mem_kempeComponentSet_of_adj h edge.symm (active x hx)⟩
  cases chain with
  | nil => simp at hu
  | cons root rest =>
    have fromRoot (x) (hx : x ∈ root :: rest) :
        root ∈ C.kempeComponentSet a b K ↔ x ∈ C.kempeComponentSet a b K := by
      rcases List.mem_cons.mp hx with rfl | hx
      · rfl
      · exact carries.rel_cons hx
    exact (fromRoot v hv).mp ((fromRoot u hu).mpr member)

theorem isTransparent_of_chains (B : Set V)
    (paths : ∀ a b : α, a ≠ b → ∀ v, (C v = a ∨ C v = b) →
      ∃ chain : List V, chain.IsChain G.Adj ∧
        (∀ x ∈ chain, C x = a ∨ C x = b) ∧ v ∈ chain ∧
        ∃ w ∈ chain, w ∈ B) : C.IsTransparent B := by
  intro a b hab K
  obtain ⟨v, hv, rfl⟩ := C.exists_eq_mk_of_kempeComponent K
  obtain ⟨chain, connected, active, member, w, hw, anchor⟩ := paths a b hab v hv
  exact ⟨w, C.mem_component_along_chain a b _ chain connected active member hw
    (C.mem_kempeComponentSet_self hv), anchor⟩

/-- This also covers the semantic formulation in which each individual
step is required to leave the boundary colours unchanged. -/
theorem IsTransparent.eq_of_boundary_fixed_history [DecidableEq α]
    {C D : G.Coloring α} {B : Set V} (frozen : C.IsTransparent B)
    (history : Relation.ReflTransGen (fun X Y : G.Coloring α =>
      G.KempeStep X Y ∧ Y.boundaryWord B = X.boundaryWord B) C D) : D = C := by
  induction history with
  | refl => rfl
  | tail _ step ih =>
    subst ih
    obtain ⟨⟨a,b,K,rfl⟩, fixed⟩ := step
    by_cases hab : a = b
    · subst b; exact Coloring.swapOnKempeComponent_self _ a K
    · exact (frozen.boundaryWord_swap_ne hab K fixed).elim

end SimpleGraph.Coloring
