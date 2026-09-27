import Mettapedia.GraphTheory.FourColor.BoundaryTriangleSubdivision
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Logic.Equiv.Sum

/-!
# Complete colouring alternatives for a boundary-triangle subdivision

Every target colouring either distinguishes the endpoints of the deleted
edge, or identifies them. The first branch is the old graph's colouring
space. The second is the colouring space of its edge contraction, together
with a fresh colour avoiding the merged vertex and the third triangle vertex.

This is an equivalence of actual colouring witnesses. It remains exact under
any further constraint on the target colouring, including prescribed boundary
colours. It does not assert that a chosen branch meets every exterior, or that
subdivision preserves reducibility. Contraction uses Mathlib's graph map;
the removed endpoint is absent from its vertex type.
-/

namespace Mettapedia.GraphTheory.FourColor.BoundaryTriangleSubdivision

universe u

variable {V : Type u} [DecidableEq V]

/-- Identify `b` with `a`, retaining exactly the vertices other than `b`. -/
def collapse (a b : V) (hab : a ≠ b) (v : V) : {v : V // v ≠ b} :=
  if h : v = b then ⟨a, hab⟩ else ⟨v, h⟩

@[simp] theorem collapse_kept (a b : V) (hab : a ≠ b) (v : {v : V // v ≠ b}) :
    collapse a b hab v.val = v := by
  simp [collapse, v.property]

@[simp] theorem collapse_a (a b : V) (hab : a ≠ b) :
    collapse a b hab a = ⟨a, hab⟩ := by simp [collapse, hab]

@[simp] theorem collapse_b (a b : V) (hab : a ≠ b) :
    collapse a b hab b = ⟨a, hab⟩ := by simp [collapse]

theorem collapse_eq_iff (a b : V) (hab : a ≠ b) (x y : V) :
    collapse a b hab x = collapse a b hab y ↔ x = y ∨ removed a b x y := by
  by_cases hx : x = b <;> by_cases hy : y = b <;>
    simp_all [collapse, removed, Subtype.ext_iff, eq_comm]

/-- The simple graph obtained by contracting `a-b`; loops disappear under `map`. -/
def contracted (G : SimpleGraph V) (a b : V) (hab : a ≠ b) :
    SimpleGraph {v : V // v ≠ b} := G.map (collapse a b hab)

variable (G : SimpleGraph V) (a b c : V) (hne : a ≠ b)

theorem contracted_adj (h : G.Adj a c) (hbc : b ≠ c) :
    (contracted G a b hne).Adj (collapse a b hne a) (collapse a b hne c) := by
  apply SimpleGraph.map_adj_apply' h
  intro heq
  rcases (collapse_eq_iff a b hne a c).mp heq with heq | heq
  · exact h.ne heq
  · rcases heq with ⟨_, heq⟩ | ⟨heq, _⟩
    · exact hbc heq.symm
    · exact hne heq

theorem retained_collapsed (coloring : (subdivide G a b c).Coloring (Fin 4))
    (equal : coloring (some a) = coloring (some b)) (v : V) :
    coloring (some (collapse a b hne v).val) = coloring (some v) := by
  by_cases hv : v = b
  · subst v
    simpa using equal
  · simp [collapse, hv]

/-- Restrict an equal-endpoint colouring to the contracted graph. -/
def contractColoring (coloring : (subdivide G a b c).Coloring (Fin 4))
    (equal : coloring (some a) = coloring (some b)) :
    (contracted G a b hne).Coloring (Fin 4) :=
  .mk (fun v => coloring (some v.val)) (by
    intro x y adjacent
    rcases adjacent with ⟨distinct, v, w, adjacent, rfl, rfl⟩
    rw [retained_collapsed G a b c hne coloring equal v,
      retained_collapsed G a b c hne coloring equal w]
    apply coloring.valid
    exact ⟨adjacent, fun removed => distinct ((collapse_eq_iff a b hne v w).mpr
      (Or.inr removed))⟩)

/-- The contracted colouring and the actual new colour are retained together. -/
structure EqualChoice where
  coloring : (contracted G a b hne).Coloring (Fin 4)
  fresh : Fin 4
  fresh_a : fresh ≠ coloring (collapse a b hne a)
  fresh_c : fresh ≠ coloring (collapse a b hne c)

@[ext] theorem EqualChoice.ext {x y : EqualChoice G a b c hne}
    (hcoloring : x.coloring = y.coloring) (hfresh : x.fresh = y.fresh) : x = y := by
  cases x
  cases y
  cases hcoloring
  cases hfresh
  rfl

/-- Expand the contracted graph, cloning the merged colour at both endpoints. -/
def expandEqual (choice : EqualChoice G a b c hne) :
    (subdivide G a b c).Coloring (Fin 4) :=
  .mk (fun vertex => match vertex with
    | some v => choice.coloring (collapse a b hne v)
    | none => choice.fresh) (by
      intro x y adjacent
      cases x with
      | none =>
        cases y with
        | none => exact False.elim adjacent
        | some v =>
          rcases adjacent with rfl | rfl | rfl
          · exact choice.fresh_a
          · simpa using choice.fresh_a
          · exact choice.fresh_c
      | some v =>
        cases y with
        | none =>
          rcases adjacent with rfl | rfl | rfl
          · exact choice.fresh_a.symm
          · simpa using choice.fresh_a.symm
          · exact choice.fresh_c.symm
        | some w =>
          apply choice.coloring.valid
          apply SimpleGraph.map_adj_apply' adjacent.1
          intro equal
          rcases (collapse_eq_iff a b hne v w).mp equal with equal | removed
          · exact adjacent.1.ne equal
          · exact adjacent.2 removed)

@[simp] theorem expandEqual_some (choice : EqualChoice G a b c hne) (v : V) :
    expandEqual G a b c hne choice (some v) = choice.coloring (collapse a b hne v) := rfl

@[simp] theorem expandEqual_none (choice : EqualChoice G a b c hne) :
    expandEqual G a b c hne choice none = choice.fresh := rfl

theorem expandEqual_equal (choice : EqualChoice G a b c hne) :
    expandEqual G a b c hne choice (some a) =
      expandEqual G a b c hne choice (some b) := by simp

def selectEqual (coloring : (subdivide G a b c).Coloring (Fin 4))
    (equal : coloring (some a) = coloring (some b)) : EqualChoice G a b c hne where
  coloring := contractColoring G a b c hne coloring equal
  fresh := coloring none
  fresh_a := by
    change coloring none ≠ coloring (some (collapse a b hne a).val)
    rw [retained_collapsed G a b c hne coloring equal a]
    exact coloring.valid (Or.inl rfl)
  fresh_c := by
    change coloring none ≠ coloring (some (collapse a b hne c).val)
    rw [retained_collapsed G a b c hne coloring equal c]
    exact coloring.valid (Or.inr (Or.inr rfl))

theorem expand_selectEqual (coloring : (subdivide G a b c).Coloring (Fin 4))
    (equal : coloring (some a) = coloring (some b)) :
    expandEqual G a b c hne (selectEqual G a b c hne coloring equal) = coloring := by
  apply DFunLike.ext
  intro vertex
  cases vertex with
  | none => rfl
  | some v => exact retained_collapsed G a b c hne coloring equal v

theorem select_expandEqual (choice : EqualChoice G a b c hne) :
    selectEqual G a b c hne (expandEqual G a b c hne choice)
      (expandEqual_equal G a b c hne choice) = choice := by
  apply EqualChoice.ext
  · apply DFunLike.ext
    intro v
    change choice.coloring (collapse a b hne v.val) = choice.coloring v
    rw [collapse_kept]
  · rfl

def equalColoringEquiv : EqualChoice G a b c hne ≃
    {coloring : (subdivide G a b c).Coloring (Fin 4) //
      coloring (some a) = coloring (some b)} where
  toFun choice := ⟨expandEqual G a b c hne choice, expandEqual_equal G a b c hne choice⟩
  invFun coloring := selectEqual G a b c hne coloring.val coloring.property
  left_inv := select_expandEqual G a b c hne
  right_inv coloring := Subtype.ext (expand_selectEqual G a b c hne
    coloring.val coloring.property)

/-- Both branches together cover every target colouring exactly once. -/
def alternativesEquiv (hab : G.Adj a b) (hac : G.Adj a c) (hbc : G.Adj b c) :
    (G.Coloring (Fin 4) ⊕ EqualChoice G a b c hne) ≃
      (subdivide G a b c).Coloring (Fin 4) :=
  ((coloringEquiv G a b c hab hac hbc).sumCongr
    ((equalColoringEquiv G a b c hne).trans
      (Equiv.subtypeEquivRight fun _ => not_not.symm))).trans
        (Equiv.sumCompl fun coloring : (subdivide G a b c).Coloring (Fin 4) =>
          coloring (some a) ≠ coloring (some b))

/-- An arbitrary additional constraint is satisfied exactly when one of the
two explicit constructions supplies a compatible witness. -/
theorem compatible_iff (hab : G.Adj a b) (hac : G.Adj a c) (hbc : G.Adj b c)
    (context : (subdivide G a b c).Coloring (Fin 4) → Prop) :
    (∃ coloring, context coloring) ↔
      (∃ coloring : G.Coloring (Fin 4), context (extend G a b c coloring)) ∨
      (∃ choice : EqualChoice G a b c hne, context (expandEqual G a b c hne choice)) := by
  constructor
  · rintro ⟨coloring, hcontext⟩
    obtain ⟨choice, rfl⟩ := (alternativesEquiv G a b c hne hab hac hbc).surjective coloring
    cases choice with
    | inl coloring => exact Or.inl ⟨coloring, hcontext⟩
    | inr choice => exact Or.inr ⟨choice, hcontext⟩
  · rintro (⟨coloring, hcontext⟩ | ⟨choice, hcontext⟩)
    · exact ⟨_, hcontext⟩
    · exact ⟨_, hcontext⟩

private theorem available_card (x y : Fin 4) (hne : x ≠ y) :
    Fintype.card {z : Fin 4 // z ≠ x ∧ z ≠ y} = 2 := by
  revert x y
  decide +kernel

noncomputable def freshEquiv (hac : G.Adj a c) (hbc : b ≠ c)
    (coloring : (contracted G a b hne).Coloring (Fin 4)) :
    {z : Fin 4 // z ≠ coloring (collapse a b hne a) ∧
      z ≠ coloring (collapse a b hne c)} ≃ Fin 2 :=
  Fintype.equivFinOfCardEq (available_card _ _
    (coloring.valid (contracted_adj G a b c hne hac hbc)))

noncomputable def equalChoiceEquiv (hac : G.Adj a c) (hbc : b ≠ c) :
    EqualChoice G a b c hne ≃ ((contracted G a b hne).Coloring (Fin 4) × Fin 2) where
  toFun choice := ⟨choice.coloring, freshEquiv G a b c hne hac hbc choice.coloring
    ⟨choice.fresh, choice.fresh_a, choice.fresh_c⟩⟩
  invFun choice :=
    let fresh := (freshEquiv G a b c hne hac hbc choice.1).symm choice.2
    ⟨choice.1, fresh.val, fresh.property.1, fresh.property.2⟩
  left_inv choice := by
    apply EqualChoice.ext G a b c hne
    · rfl
    · exact congrArg Subtype.val
        ((freshEquiv G a b c hne hac hbc choice.coloring).symm_apply_apply _)
  right_inv choice := by
    apply Prod.ext
    · rfl
    · exact (freshEquiv G a b c hne hac hbc choice.1).apply_symm_apply choice.2

/-- The complete four-colouring count, including the formerly omitted branch. -/
theorem alternatives_card [Finite V]
    (hab : G.Adj a b) (hac : G.Adj a c) (hbc : G.Adj b c) :
    Nat.card ((subdivide G a b c).Coloring (Fin 4)) =
      Nat.card (G.Coloring (Fin 4)) +
        2 * Nat.card ((contracted G a b hne).Coloring (Fin 4)) := by
  classical
  let _ := Fintype.ofFinite V
  have choiceFinite : Finite (EqualChoice G a b c hne) :=
    Finite.of_equiv _ (equalChoiceEquiv G a b c hne hac hbc.ne).symm
  rw [← Nat.card_congr (alternativesEquiv G a b c hne hab hac hbc), Nat.card_sum,
    Nat.card_congr (equalChoiceEquiv G a b c hne hac hbc.ne), Nat.card_prod]
  simp [Nat.mul_comm]

end Mettapedia.GraphTheory.FourColor.BoundaryTriangleSubdivision
