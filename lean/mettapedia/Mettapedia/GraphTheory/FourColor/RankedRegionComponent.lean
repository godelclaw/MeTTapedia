import Mettapedia.GraphTheory.FourColor.VertexSeparatorBond

/-!
# Exact complementary components from ranked spanning witnesses

A candidate component lies outside the deleted set, contains the anchor,
is closed under allowed adjacent steps, and has a rank-decreasing parent
edge from every other vertex. These finite facts identify the complete
reachable component. The intended consumer is a full-interface obstruction,
where a purported small side must not silently omit a complementary pocket.
-/

namespace Mettapedia.GraphTheory.FourColor.RankedRegionComponent

open SimpleGraph VertexSeparatorBond

variable {V : Type*} (G : SimpleGraph V)

theorem flood_subset_of_closed {S C : Set V} {b : V} (hb : b ∈ C)
    (hc : ∀ v ∈ C, ∀ w, G.Adj v w → w ∉ S → w ∈ C) :
    flood G Sᶜ {b} ⊆ C := by
  have hw {u v : V} (p : G.Walk u v) (hu : u ∈ C)
      (hp : ∀ x ∈ p.support, x ∉ S) : v ∈ C := by
    induction p with
    | nil => exact hu
    | @cons u w v hadj p ih =>
      exact ih (hc u hu w hadj (hp w (by simp)))
        (fun x hx => hp x (by simp [hx]))
  rintro v ⟨a, ha, p, hp⟩
  obtain rfl : a = b := ha
  exact hw p hb hp

/-- The supplied finite witness proves equality with the full flood. -/
theorem flood_eq_of_rank {S C : Set V} {b : V}
    (hb : b ∈ C) (hCS : C ⊆ Sᶜ)
    (parent : V → V) (rank : V → ℕ)
    (hparent : ∀ v ∈ C, v ≠ b →
      parent v ∈ C ∧ G.Adj (parent v) v ∧ rank (parent v) < rank v)
    (hclosed : ∀ v ∈ C, ∀ w, G.Adj v w → w ∉ S → w ∈ C) :
    flood G Sᶜ {b} = C := by
  apply Set.Subset.antisymm (flood_subset_of_closed G hb hclosed)
  have hr : ∀ n v, rank v = n → v ∈ C → v ∈ flood G Sᶜ {b} := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro v hv hvc
      by_cases heq : v = b
      · subst v
        exact mem_flood G Sᶜ {b} (hCS hb) rfl
      · obtain ⟨hp, hadj, hlt⟩ := hparent v hvc heq
        exact flood_adj G (ih (rank (parent v)) (by omega) (parent v) rfl hp) hadj (hCS hvc)
  exact fun v hv => hr (rank v) v rfl hv

end Mettapedia.GraphTheory.FourColor.RankedRegionComponent
