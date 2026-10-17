import Mettapedia.SetTheory.OpenTower.AntiFounded.AFAStages

/-!
# `B_κ` has exactly `κ` members for `κ` inaccessible

Every member of `B_κ` is the picture of a graph with fewer than `κ` nodes
(`exists_small_picture`), so it is the decoration of a graph on the ordinals below some cardinal
`μ < κ`. These graphs, with a chosen node, are indexed by a type of at most `κ` elements: for
each `μ < κ` there are `2 ^ (μ * μ) * μ < κ` of them (`mk_pointedGraphs_lt`), and there are `κ`
values of `μ` (`mk_pointedGraphIndex_le`). The ordinals below `κ` are `κ` distinct members. So
the members of `B_κ`, presented without repetition, are exactly `κ` many
(`exists_members_card_branching`).

At `ω` the law fails: `B_ℵ₀` is uncountable (`not_smallMembers_succ_aleph0_branching`).
-/

set_option autoImplicit false

namespace Mettapedia.SetTheory.OpenTower.AntiFounded

open Mettapedia.TypeTheory.MaterialSets
open Mettapedia.TypeTheory.MaterialSets.Hypersets
open Cardinal
open scoped ZFSet

universe u

/-- A type of `μ` elements for each ordinal `t` below `κ`, with `μ` the cardinality of `t`. -/
abbrev nodesBelow {κ : Cardinal.{u}} (t : κ.ord.ToType) : Type u :=
  ((Ordinal.typein (α := κ.ord.ToType) (· < ·)).toRelEmbedding t).card.ord.ToType

/-- The pointed graphs on the types `nodesBelow t`. -/
abbrev PointedGraphIndex (κ : Cardinal.{u}) : Type u :=
  Σ t : κ.ord.ToType, (nodesBelow t → nodesBelow t → Prop) × nodesBelow t

/-- The pointed graphs on a type of fewer than `κ` elements are fewer than `κ`, for `κ`
inaccessible. -/
theorem mk_pointedGraphs_lt {κ : Cardinal.{u}} (hκ : κ.IsInaccessible) {α : Type u}
    (h : #α < κ) : #((α → α → Prop) × α) < κ := by
  have graphs : #(α → α → Prop) = 2 ^ (#α * #α) := by
    rw [mk_congr (Equiv.curry α α Prop).symm]
    change #(Set (α × α)) = _
    rw [mk_set, mk_prod, lift_id]
  rw [mk_prod, lift_id, lift_id, graphs]
  exact mul_lt_of_lt hκ.aleph0_lt.le
    (hκ.isStrongLimit.isStrongPrelimit (mul_lt_of_lt hκ.aleph0_lt.le h h)) h

theorem mk_pointedGraphIndex_le {κ : Cardinal.{u}} (hκ : κ.IsInaccessible) :
    #(PointedGraphIndex κ) ≤ κ := by
  have each : ∀ t : κ.ord.ToType, #((nodesBelow t → nodesBelow t → Prop) × nodesBelow t) < κ :=
    fun t => mk_pointedGraphs_lt hκ (by
      rw [mk_ord_toType]
      exact Cardinal.lt_ord.mp (Ordinal.typein_lt_self t))
  calc #(PointedGraphIndex κ)
      = sum fun t : κ.ord.ToType => #((nodesBelow t → nodesBelow t → Prop) × nodesBelow t) :=
        mk_sigma _
    _ ≤ #κ.ord.ToType * ⨆ t : κ.ord.ToType,
          #((nodesBelow t → nodesBelow t → Prop) × nodesBelow t) := sum_le_mk_mul_iSup _
    _ ≤ κ * κ := by
        rw [mk_ord_toType]
        exact mul_le_mul' le_rfl (ciSup_le' fun t => (each t).le)
    _ = κ := mul_eq_self hκ.aleph0_lt.le

/-- Every member of `B_κ` is the decoration of an indexed pointed graph. -/
theorem exists_pointedGraph {κ : Cardinal.{u}} (hκ : κ.IsInaccessible) {y : HSet.{u}}
    (hy : y ∈ branching κ) :
    ∃ p : PointedGraphIndex κ, HSet.decorate p.2.1 p.2.2 = y := by
  obtain ⟨G, hG, rfl⟩ := exists_small_picture hκ.isRegular hκ.aleph0_lt (mem_branching.mp hy)
  obtain ⟨t, ht⟩ := Ordinal.typein_surj (α := κ.ord.ToType) (· < ·)
    (by rw [Ordinal.type_toType]; exact ord_lt_ord.mpr hG)
  have size : #G.Node = #(nodesBelow t) := by
    rw [mk_ord_toType, ht, card_ord]
  obtain ⟨e⟩ := Cardinal.eq.mp size
  refine ⟨⟨t, fun a b => G.edge (e.symm a) (e.symm b), e G.point⟩, ?_⟩
  rw [HSet.mk_eq_decorate]
  refine (HSet.decorate_eq_of_bisimilar (bisimilar_apply (r := G.edge)
    (s := fun a b => G.edge (e.symm a) (e.symm b)) (f := e) (fun a b h => ?_)
    (fun a b h => ⟨e.symm b, by simpa only [Equiv.symm_apply_apply] using h,
      by simp only [Equiv.apply_symm_apply]⟩) G.point)).symm
  simp only [Equiv.symm_apply_apply]
  exact h

/-- **`B_κ` has exactly `κ` members**, for `κ` inaccessible. -/
theorem exists_members_card_branching {κ : Cardinal.{u}} (hκ : κ.IsInaccessible) :
    ∃ (ι : Type u) (g : ι → HSet.{u}), Function.Injective g ∧
      (∀ y, y ∈ branching κ ↔ ∃ i, g i = y) ∧ #ι = κ := by
  obtain ⟨ι, g, injective, hg⟩ := exists_injective_members (branching κ)
  refine ⟨ι, g, injective, hg, le_antisymm ?_ ?_⟩
  · have hit : ∀ i, ∃ p : PointedGraphIndex κ, HSet.decorate p.2.1 p.2.2 = g i :=
      fun i => exists_pointedGraph hκ ((hg _).mpr ⟨i, rfl⟩)
    choose φ hφ using hit
    have φinjective : Function.Injective φ := fun i j e =>
      injective ((hφ i).symm.trans ((congrArg (fun p : PointedGraphIndex κ =>
        HSet.decorate p.2.1 p.2.2) e).trans (hφ j)))
    exact (mk_le_of_injective φinjective).trans (mk_pointedGraphIndex_le hκ)
  · have hit : ∀ t : κ.ord.ToType, ∃ i, g i = HSet.ofZFSet
        ((Ordinal.typein (α := κ.ord.ToType) (· < ·)).toRelEmbedding t).toZFSet :=
      fun t => (hg _).mp (mem_branching.mpr (herSmall_ofZFSet_toZFSet
        (Cardinal.lt_ord.mp (Ordinal.typein_lt_self t))))
    choose φ hφ using hit
    have φinjective : Function.Injective φ := fun t t' e =>
      Ordinal.typein_injective _ (Ordinal.toZFSet_injective (HSet.ofZFSet_injective
        ((hφ t).symm.trans ((congrArg g e).trans (hφ t')))))
    have := mk_le_of_injective φinjective
    rwa [mk_ord_toType] at this

#print axioms mk_pointedGraphIndex_le
#print axioms exists_members_card_branching

end Mettapedia.SetTheory.OpenTower.AntiFounded
