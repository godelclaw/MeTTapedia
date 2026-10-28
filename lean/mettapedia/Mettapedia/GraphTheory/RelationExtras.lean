import Mathlib.Logic.Relation

namespace Mettapedia.GraphTheory

/-- Reverse a reflexive-transitive path when the underlying relation is symmetric. -/
theorem ReflTransGen.reverse_of_symmetric {α : Type*} {R : α → α → Prop}
    (hSym : Symmetric R) {a b : α} (h : Relation.ReflTransGen R a b) :
    Relation.ReflTransGen R b a := by
  induction h with
  | refl => exact .refl
  | tail _ hab ih =>
      exact .head (hSym hab) ih

/-- Transport a reflexive-transitive path along a relation-preserving map. -/
theorem ReflTransGen.map_rel {α β : Type*} {R : α → α → Prop} {Q : β → β → Prop}
    (f : α → β) (h : ∀ a b, R a b → Q (f a) (f b))
    {a b : α} (p : Relation.ReflTransGen R a b) :
    Relation.ReflTransGen Q (f a) (f b) := by
  induction p with
  | refl => exact .refl
  | tail _ hab ih => exact .tail ih (h _ _ hab)

/-- If a reflexive-transitive path through `R ∪ S` is not already an `R`-path, some step of
the path uses `S`. The returned prefix is an `R`-path up to the first such step. -/
theorem ReflTransGen.exists_new_step_of_not_left {α : Type*} {R S : α → α → Prop} {a b : α}
    (h_path : Relation.ReflTransGen (fun x y => R x y ∨ S x y) a b)
    (h_not_R : ¬ Relation.ReflTransGen R a b) :
    ∃ x y,
      Relation.ReflTransGen R a x ∧
      S x y ∧
      x ≠ y ∧
      Relation.ReflTransGen (fun x y => R x y ∨ S x y) y b := by
  induction h_path using Relation.ReflTransGen.head_induction_on with
  | refl =>
      exact False.elim (h_not_R .refl)
  | head h_step h_rest IH =>
      rename_i a' c
      rcases h_step with hR | hS
      · by_cases h_R_rest : Relation.ReflTransGen R c b
        · exact False.elim (h_not_R (.head hR h_R_rest))
        · rcases IH h_R_rest with ⟨x, y, hcx, hSxy, hne, hyb⟩
          exact ⟨x, y, .head hR hcx, hSxy, hne, hyb⟩
      · by_cases h_eq : a' = c
        · subst h_eq
          exact IH h_not_R
        · exact ⟨a', c, .refl, hS, h_eq, h_rest⟩

end Mettapedia.GraphTheory
