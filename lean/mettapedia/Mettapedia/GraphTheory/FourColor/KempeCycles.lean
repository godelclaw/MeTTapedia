import Mettapedia.GraphTheory.FourColor.BoundaryChains

namespace Mettapedia.GraphTheory.FourColor

variable {V E : Type*} [DecidableEq E]

/-- A bicolored, degree-bounded edge set for the selected pair of colors.

This is the reusable part of the old standalone `isKempeCycle` predicate.  It deliberately does
not call itself a cycle: degree `≤ 2` still allows dangling degree-one endpoints. -/
def IsKempeSubgraph (incident : V → Finset E) (x : E → Color)
    (C : Finset E) (α β : Color) : Prop :=
  (∀ e ∈ C, x e = α ∨ x e = β) ∧
  (∀ v : V, (C ∩ incident v).card ≤ 2)

/-- A degree-bounded edge set has no path endpoints when every vertex has incidence count other
than one. -/
def HasNoDanglingVertices (incident : V → Finset E) (C : Finset E) : Prop :=
  ∀ v : V, (C ∩ incident v).card ≠ 1

/-- A true Kempe cycle: bicolored, degree-bounded, and with no dangling degree-one vertices. -/
def IsKempeCycle (incident : V → Finset E) (x : E → Color)
    (C : Finset E) (α β : Color) : Prop :=
  IsKempeSubgraph incident x C α β ∧ HasNoDanglingVertices incident C

/-- An interior Kempe cycle is disjoint from the distinguished boundary edges. -/
def IsInteriorKempeCycle (D : ZeroBoundaryData V E)
    (x : E → Color) (C : Finset E) (α β : Color) : Prop :=
  IsKempeCycle D.incident x C α β ∧
  ∀ e ∈ C, e ∉ D.boundaryEdges

theorem kempeSubgraph_filter_incidence_eq (incident : V → Finset E) (x : E → Color)
    (C : Finset E) (α β : Color) (hC : IsKempeSubgraph incident x C α β)
    (v : V) :
    (C ∩ incident v).filter (fun e => x e = α ∨ x e = β) = C ∩ incident v := by
  ext e
  constructor
  · intro he
    exact (Finset.mem_filter.1 he).1
  · intro he
    exact Finset.mem_filter.2 ⟨he, hC.1 e (Finset.mem_inter.1 he).1⟩

/-- A true Kempe cycle has even selected-color incidence at every vertex.  The explicit
`HasNoDanglingVertices` part of `IsKempeCycle` is the missing hypothesis from the old standalone
proof attempt. -/
theorem kempeCycle_even_at (incident : V → Finset E) (x : E → Color)
    (C : Finset E) (α β : Color)
    (hC : IsKempeCycle incident x C α β) :
    ∀ v : V, Even ((C ∩ incident v).filter (fun e => x e = α ∨ x e = β)).card := by
  intro v
  rw [kempeSubgraph_filter_incidence_eq incident x C α β hC.1 v]
  have hdeg : (C ∩ incident v).card ≤ 2 := hC.1.2 v
  have hnot_one : (C ∩ incident v).card ≠ 1 := hC.2 v
  have hcases : (C ∩ incident v).card = 0 ∨ (C ∩ incident v).card = 2 := by
    omega
  rcases hcases with h0 | h2
  · rw [h0]
    exact ⟨0, by simp⟩
  · rw [h2]
    exact ⟨1, by simp⟩

/-- If a degree-bounded bicolored subgraph has two distinct edges incident at a vertex, then the
incidence count at that vertex is exactly two. -/
theorem kempeSubgraph_degree_two_of_two_incident (incident : V → Finset E) (x : E → Color)
    (C : Finset E) (α β : Color) (v : V)
    (hC : IsKempeSubgraph incident x C α β)
    (h_interior :
      ∃ e₁ e₂ : E, e₁ ∈ C ∧ e₂ ∈ C ∧ e₁ ≠ e₂ ∧
        e₁ ∈ incident v ∧ e₂ ∈ incident v) :
    (C ∩ incident v).card = 2 := by
  have h_deg := hC.2 v
  rcases h_interior with ⟨e₁, e₂, he₁_C, he₂_C, hne, he₁_v, he₂_v⟩
  have h_two_in : ({e₁, e₂} : Finset E) ⊆ C ∩ incident v := by
    intro e he
    simp only [Finset.mem_insert, Finset.mem_singleton] at he
    rcases he with rfl | rfl
    · exact Finset.mem_inter.2 ⟨he₁_C, he₁_v⟩
    · exact Finset.mem_inter.2 ⟨he₂_C, he₂_v⟩
  have h_card_two : ({e₁, e₂} : Finset E).card = 2 := by
    simp [hne]
  have h_le := Finset.card_le_card h_two_in
  omega

end Mettapedia.GraphTheory.FourColor
