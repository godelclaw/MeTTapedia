import Mettapedia.GraphTheory.Kempe.PairDecomposition

/-!
# Projecting physical Kempe histories along graph homomorphisms

A full component may split into several components after restriction. Its
pointwise effect is still a proper partial transposition, so it is realized
by a sequence of actual switches on the finite observing graph. Fixed
context pulls back along the homomorphism. No converse lifting is assumed.
-/

namespace SimpleGraph

open Relation

variable {V W α : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
  [Fintype W] [DecidableEq α]

/-- Restricting one physical switch gives a physical history, with the
preimage of the protected context fixed throughout. -/
theorem KempeStepAvoiding.comp_path (f : H →g G) {B : Set V} {C D : G.Coloring α}
    (h : G.KempeStepAvoiding B C D) :
    ReflTransGen (H.KempeStepAvoiding (f ⁻¹' B)) (C.comp f) (D.comp f) := by
  obtain ⟨a, b, K, avoids, rfl⟩ := h
  apply Coloring.avoiding_of_pointwise_swap (C.comp f) _ a b (f ⁻¹' B)
  · intro x hx
    exact (C.swapOnKempeComponent_apply_of_not_mem
      (fun hk => Set.disjoint_left.mp avoids hk hx)).symm
  · intro x
    by_cases hx : f x ∈ C.kempeComponentSet a b K
    · exact Or.inr (C.swapOnKempeComponent_apply_of_mem hx)
    · exact Or.inl (C.swapOnKempeComponent_apply_of_not_mem hx)

/-- Whole histories project, including arbitrary finite preparation steps. -/
theorem kempe_path_comp (f : H →g G) {B : Set V} {C D : G.Coloring α}
    (h : ReflTransGen (G.KempeStepAvoiding B) C D) :
    ReflTransGen (H.KempeStepAvoiding (f ⁻¹' B)) (C.comp f) (D.comp f) := by
  induction h with
  | refl => exact .refl
  | tail _ step ih => exact ih.trans (step.comp_path f)

end SimpleGraph
