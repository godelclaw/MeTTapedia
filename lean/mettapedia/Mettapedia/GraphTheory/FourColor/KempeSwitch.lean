import Mettapedia.GraphTheory.FourColor.ColorAlgebra

open scoped BigOperators

namespace Mettapedia.GraphTheory.FourColor

/-- A Kempe switch preserves each vertex sum when the switched two-color set has even incidence
at every vertex. This is the reusable algebraic content of the old standalone FourColor
`KempeSwap` module, stated independently of any particular graph representation. -/
theorem switch_preserves_incidence_sum {E V : Type*} [DecidableEq E]
    (incident : V → Finset E)
    (x : E → Color) (C : Finset E) (α β : Color)
    (even_at :
      ∀ v : V, Even ((C ∩ incident v).filter (fun e => x e = α ∨ x e = β)).card) :
    ∀ v, (∑ e ∈ incident v, x e) =
      ∑ e ∈ incident v, switch α β (C : Set E) x e := by
  intro v
  let S := (C ∩ incident v).filter (fun e => x e = α ∨ x e = β)
  have h_swap :
      ∀ e, switch α β (C : Set E) x e
        = x e + if e ∈ C ∧ (x e = α ∨ x e = β) then α + β else 0 := by
    intro e
    exact switch_finset_apply_eq_add_selected_delta (α := α) (β := β) (S := C) (C := x) e
  symm
  calc
    ∑ e ∈ incident v, switch α β (C : Set E) x e
        = ∑ e ∈ incident v,
            (x e + if e ∈ C ∧ (x e = α ∨ x e = β) then α + β else 0) := by
          refine Finset.sum_congr rfl ?_
          intro e _he
          exact h_swap e
    _ = (∑ e ∈ incident v, x e) +
          ∑ e ∈ incident v,
            (if e ∈ C ∧ (x e = α ∨ x e = β) then α + β else 0) := by
          rw [Finset.sum_add_distrib]
    _ = (∑ e ∈ incident v, x e) + ∑ e ∈ S, (α + β) := by
          congr 1
          rw [← Finset.sum_filter]
          congr 1
          ext e
          simp [S, and_left_comm, and_assoc]
    _ = (∑ e ∈ incident v, x e) + S.card • (α + β) := by
          rw [sum_const]
    _ = (∑ e ∈ incident v, x e) + 0 := by
          rw [nsmul_even_eq_zero (even_at v)]
    _ = ∑ e ∈ incident v, x e := by
          simp

/-- Predicate-form Kempe switch preservation. This is the reusable content of the old
standalone `swap_preserves_vertex_sum_pred`, stated against the modern `switch` API. -/
theorem switch_preserves_incidence_sum_pred {E V : Type*} [DecidableEq E]
    (incident : V → Finset E)
    (x : E → Color) (p : E → Prop) [DecidablePred p] (α β : Color)
    (even_at :
      ∀ v : V, Even ((incident v).filter (fun e => p e ∧ (x e = α ∨ x e = β))).card) :
    ∀ v, (∑ e ∈ incident v, x e) =
      ∑ e ∈ incident v, switch α β {e | p e} x e := by
  intro v
  let S := (incident v).filter (fun e => p e ∧ (x e = α ∨ x e = β))
  have h_swap :
      ∀ e, switch α β {e | p e} x e =
        x e + if p e ∧ (x e = α ∨ x e = β) then α + β else 0 := by
    intro e
    by_cases he : p e
    · simp [switch, he, Color.swap_eq_add_delta, Color.delta]
    · simp [switch, he]
  symm
  calc
    ∑ e ∈ incident v, switch α β {e | p e} x e
        = ∑ e ∈ incident v,
            (x e + if p e ∧ (x e = α ∨ x e = β) then α + β else 0) := by
          refine Finset.sum_congr rfl ?_
          intro e _he
          exact h_swap e
    _ = (∑ e ∈ incident v, x e) +
          ∑ e ∈ incident v,
            (if p e ∧ (x e = α ∨ x e = β) then α + β else 0) := by
          rw [Finset.sum_add_distrib]
    _ = (∑ e ∈ incident v, x e) + ∑ e ∈ S, (α + β) := by
          congr 1
          rw [← Finset.sum_filter]
    _ = (∑ e ∈ incident v, x e) + S.card • (α + β) := by
          rw [sum_const]
    _ = (∑ e ∈ incident v, x e) + 0 := by
          rw [nsmul_even_eq_zero (even_at v)]
    _ = ∑ e ∈ incident v, x e := by
          simp

/-- Predicate-form Kempe switches preserve a zero boundary sum at every vertex when the
switched two-color predicate has even incidence at every vertex. -/
theorem switch_preserves_zero_incidence_sum_pred {E V : Type*} [DecidableEq E]
    (incident : V → Finset E)
    (x : E → Color) (p : E → Prop) [DecidablePred p] (α β : Color)
    (zero_at : ∀ v : V, (∑ e ∈ incident v, x e) = 0)
    (even_at :
      ∀ v : V, Even ((incident v).filter (fun e => p e ∧ (x e = α ∨ x e = β))).card) :
    ∀ v, (∑ e ∈ incident v, switch α β {e | p e} x e) = 0 := by
  intro v
  exact ((switch_preserves_incidence_sum_pred
    (incident := incident) (x := x) (p := p) (α := α) (β := β) even_at v).symm).trans
      (zero_at v)

end Mettapedia.GraphTheory.FourColor
