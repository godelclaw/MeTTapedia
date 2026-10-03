import Mettapedia.GraphTheory.Kempe.PairDecomposition

/-!
# Faithful colour renaming of physical histories

An injective palette map takes every boundary-avoiding Kempe history to a
boundary-avoiding Kempe history on the same finite graph. This is forward
transport; no assertion about additional colours in the target palette occurs.
-/

namespace SimpleGraph

open Relation

variable {V α β : Type*} {G : SimpleGraph V}
  [Fintype V] [DecidableEq α] [DecidableEq β]

/-- A physical switch remains a proper partial transposition under injective
colour renaming, hence has a physical realization with the same fixed context. -/
theorem KempeStepAvoiding.recolor_path (e : α ↪ β) {B : Set V} {C D : G.Coloring α}
    (h : G.KempeStepAvoiding B C D) :
    ReflTransGen (G.KempeStepAvoiding B) (G.recolorOfEmbedding e C) (G.recolorOfEmbedding e D) := by
  obtain ⟨a, b, K, avoids, rfl⟩ := h
  apply Coloring.avoiding_of_pointwise_swap _ _ (e a) (e b) B
  · intro x hx
    exact congrArg e (C.swapOnKempeComponent_apply_of_not_mem
      (fun hk => Set.disjoint_left.mp avoids hk hx)).symm
  · intro x
    by_cases hx : x ∈ C.kempeComponentSet a b K
    · right
      change e (C.swapOnKempeComponent a b K x) = Equiv.swap (e a) (e b) (e (C x))
      rw [C.swapOnKempeComponent_apply_of_mem hx]
      exact (e.injective.swap_apply a b (C x)).symm
    · exact Or.inl (congrArg e (C.swapOnKempeComponent_apply_of_not_mem hx))

theorem kempe_path_recolor (e : α ↪ β) {B : Set V} {C D : G.Coloring α}
    (h : ReflTransGen (G.KempeStepAvoiding B) C D) :
    ReflTransGen (G.KempeStepAvoiding B) (G.recolorOfEmbedding e C) (G.recolorOfEmbedding e D) := by
  induction h with
  | refl => exact .refl
  | tail _ step ih => exact ih.trans (step.recolor_path e)

end SimpleGraph
