import Mettapedia.GraphTheory.FourColor.GoertzelV24KempeComponentEmbeddingBoundary

/-!
# The exact obstruction to lifting one Kempe component switch

The map on connected components, not mere contact with the image boundary,
controls restriction.  A component fuses when a distinct source component has
the same image component.  For distinct selected colours this is exactly the
obstruction to lifting its switch by one switch with the same colour pair.

No planarity, finiteness, or counterexample assumptions are needed here.
-/

namespace Mettapedia.GraphTheory.FourColor.KempeEmbeddingFusion

open SimpleGraph GoertzelV24KempeComponentEmbeddingBoundary

universe u v w
variable {A : Type u} {B : Type v} {C : Type w}
  {G : SimpleGraph A} {H : SimpleGraph B}

/-- A distinct component of the source joins this component in the target. -/
def Fuses (f : G ↪g H) (K : G.ConnectedComponent) : Prop :=
  ∃ L : G.ConnectedComponent, L ≠ K ∧ L.map f.toHom = K.map f.toHom

theorem mem_map (f : G ↪g H) (K : G.ConnectedComponent) {x : A}
    (hx : x ∈ K) : f x ∈ K.map f.toHom := by
  change G.connectedComponentMk x = K at hx
  rw [← hx]
  rfl

theorem mem_map_iff_of_not_fuses (f : G ↪g H) (K : G.ConnectedComponent)
    (h : ¬ Fuses f K) (x : A) : x ∈ K ↔ f x ∈ K.map f.toHom := by
  constructor
  · exact mem_map f K
  · intro hx
    by_contra hnot
    exact h ⟨G.connectedComponentMk x, hnot, hx⟩

/-- A fused component contains a source vertex connected upstairs, but not
downstairs, to a vertex of the specified component. -/
theorem fuses_iff_reachable (f : G ↪g H) (K : G.ConnectedComponent) :
    Fuses f K ↔ ∃ x y : A, x ∈ K ∧ y ∉ K ∧ H.Reachable (f x) (f y) := by
  constructor
  · rintro ⟨L, hne, hmap⟩
    obtain ⟨x, hx⟩ := K.nonempty_supp
    obtain ⟨y, hy⟩ := L.nonempty_supp
    refine ⟨x, y, hx, ?_, ?_⟩
    · intro hyK
      exact hne (hy.symm.trans hyK)
    · apply ConnectedComponent.exact
      exact (mem_map f K hx).trans (hmap.symm.trans (mem_map f L hy).symm)
  · rintro ⟨x, y, hx, hy, hreach⟩
    refine ⟨G.connectedComponentMk y, hy, ?_⟩
    exact (ConnectedComponent.sound hreach).symm.trans (mem_map f K hx)

/-- A walk entirely in the image of an embedding connects preimages. -/
theorem reachable_of_walk_in_range (f : G ↪g H) {x y : B} (p : H.Walk x y)
    (h : ∀ z ∈ p.support, ∃ a, f a = z) :
    ∃ a b, f a = x ∧ f b = y ∧ G.Reachable a b := by
  induction p with
  | @nil x =>
      obtain ⟨a, ha⟩ := h x (by simp)
      exact ⟨a, a, ha, ha, .refl a⟩
  | @cons x y z hadj p ih =>
      obtain ⟨a, ha⟩ := h x (by simp)
      obtain ⟨b, c, hb, hc, hbc⟩ := ih (fun t ht => h t (by simp [ht]))
      refine ⟨a, c, ha, hc, ?_⟩
      have hab : G.Adj a b := f.map_rel_iff.mp (by simpa [ha, hb] using hadj)
      exact hab.reachable.trans hbc

/-- Every ambient walk joining distinct small components leaves the image;
mere existence of an outside neighbour would not establish this. -/
theorem walk_leaves_range (f : G ↪g H) {x y : A}
    (hnot : ¬ G.Reachable x y) (p : H.Walk (f x) (f y)) :
    ∃ z ∈ p.support, ¬ ∃ a, f a = z := by
  classical
  by_contra hn
  push Not at hn
  obtain ⟨a, b, ha, hb, hab⟩ := reachable_of_walk_in_range f p hn
  have hax := f.injective ha
  have hby := f.injective hb
  subst a
  subst b
  exact hnot hab

/-- Fusion supplies an actual ambient walk joining distinct small components,
with an outside-image vertex on that walk. -/
theorem exists_fusion_walk (f : G ↪g H) (K : G.ConnectedComponent) (h : Fuses f K) :
    ∃ x y : A, x ∈ K ∧ y ∉ K ∧
      ∃ p : H.Walk (f x) (f y), ∃ z ∈ p.support, ¬ ∃ a, f a = z := by
  obtain ⟨x, y, hx, hy, ⟨p⟩⟩ := (fuses_iff_reachable f K).mp h
  refine ⟨x, y, hx, hy, p, walk_leaves_range f ?_ p⟩
  intro hxy
  exact hy ((ConnectedComponent.sound hxy).symm.trans hx)

variable [DecidableEq C]

abbrev ComponentFuses (coloring : H.EdgeColoring C) (embedding : G ↪g H)
    (first second : C)
    (K : ((coloring.pullbackEmbedding embedding).bicoloredSubgraph
      first second).ConnectedComponent) : Prop :=
  Fuses (bicoloredSubgraphEmbedding coloring embedding first second) K

omit [DecidableEq C] in
/-- A selected edge with no selected preimage has no edge preimage at all. -/
theorem not_edge_in_range_of_not_selected_in_range
    (coloring : H.EdgeColoring C) (embedding : G ↪g H) (first second : C)
    (z : coloring.bicoloredSet first second)
    (h : ¬ ∃ x, bicoloredSubgraphEmbedding coloring embedding first second x = z) :
    ¬ ∃ edge, embedding.mapEdgeSet edge = z.val := by
  rintro ⟨edge, heq⟩
  apply h
  have hs : edge ∈ (coloring.pullbackEmbedding embedding).bicoloredSet first second := by
    change coloring (embedding.mapEdgeSet edge) = first ∨
      coloring (embedding.mapEdgeSet edge) = second
    rw [heq]
    exact z.property
  exact ⟨⟨edge, hs⟩, Subtype.ext heq⟩

/-- A singleton fibre of the component map gives an exact lifted switch,
even when the ambient component has vertices outside the embedding. -/
theorem lifted_switch_of_not_fuses
    (coloring : H.EdgeColoring C) (embedding : G ↪g H) (first second : C)
    (K : ((coloring.pullbackEmbedding embedding).bicoloredSubgraph
      first second).ConnectedComponent)
    (h : ¬ ComponentFuses coloring embedding first second K) :
    EdgeColoring.pullbackEmbedding (coloring.swapOnKempeComponent first second
      (K.map (bicoloredSubgraphEmbedding coloring embedding first second).toHom)) embedding =
      (coloring.pullbackEmbedding embedding).swapOnKempeComponent first second K := by
  let f := bicoloredSubgraphEmbedding coloring embedding first second
  apply DFunLike.ext _ _
  intro edge
  have hmem : edge ∈ (coloring.pullbackEmbedding embedding).kempeComponentSet first second K ↔
      embedding.mapEdgeSet edge ∈ coloring.kempeComponentSet first second (K.map f.toHom) := by
    constructor
    · rintro ⟨hs, hx⟩
      exact ⟨hs, (mem_map_iff_of_not_fuses f K h ⟨edge, hs⟩).mp hx⟩
    · rintro ⟨hs, hx⟩
      exact ⟨hs, (mem_map_iff_of_not_fuses f K h ⟨edge, hs⟩).mpr hx⟩
  by_cases hedge : edge ∈ (coloring.pullbackEmbedding embedding).kempeComponentSet first second K
  · rw [EdgeColoring.pullbackEmbedding_apply,
      coloring.swapOnKempeComponent_apply_of_mem (hmem.mp hedge),
      Coloring.swapOnKempeComponent_apply_of_mem _ hedge]
    rfl
  · rw [EdgeColoring.pullbackEmbedding_apply,
      coloring.swapOnKempeComponent_apply_of_not_mem (fun hx => hedge (hmem.mpr hx)),
      Coloring.swapOnKempeComponent_apply_of_not_mem _ hedge]
    rfl

/-- With distinct colours, the set of changed edges is exactly the selected
component.  Equality of switches therefore forces equality of their supports. -/
theorem membership_iff_of_lifted_switch
    (coloring : H.EdgeColoring C) (embedding : G ↪g H) {first second : C}
    (hne : first ≠ second)
    (K : ((coloring.pullbackEmbedding embedding).bicoloredSubgraph
      first second).ConnectedComponent)
    (L : (coloring.bicoloredSubgraph first second).ConnectedComponent)
    (heq : EdgeColoring.pullbackEmbedding (coloring.swapOnKempeComponent first second L) embedding =
      (coloring.pullbackEmbedding embedding).swapOnKempeComponent first second K)
    (edge : G.edgeSet) :
    edge ∈ (coloring.pullbackEmbedding embedding).kempeComponentSet first second K ↔
      embedding.mapEdgeSet edge ∈ coloring.kempeComponentSet first second L := by
  have happly := DFunLike.congr_fun heq edge
  rw [EdgeColoring.pullbackEmbedding_apply] at happly
  constructor
  · intro hx
    by_contra hy
    rw [coloring.swapOnKempeComponent_apply_of_not_mem hy,
      Coloring.swapOnKempeComponent_apply_of_mem _ hx] at happly
    exact (Equiv.swap_apply_ne_self_iff.mpr
      ⟨hne, Coloring.mem_bicoloredSet_of_mem_kempeComponentSet _ hx⟩) happly.symm
  · intro hy
    by_contra hx
    rw [coloring.swapOnKempeComponent_apply_of_mem hy,
      Coloring.swapOnKempeComponent_apply_of_not_mem _ hx] at happly
    exact (Equiv.swap_apply_ne_self_iff.mpr
      ⟨hne, Coloring.mem_bicoloredSet_of_mem_kempeComponentSet _ hy⟩) happly

/-- **Exact single-switch criterion.** Fusion, rather than boundary contact,
is precisely what prevents one same-pair ambient component switch from lifting. -/
theorem exists_lifted_switch_iff_not_fuses
    (coloring : H.EdgeColoring C) (embedding : G ↪g H) {first second : C}
    (hne : first ≠ second)
    (K : ((coloring.pullbackEmbedding embedding).bicoloredSubgraph
      first second).ConnectedComponent) :
    (∃ L : (coloring.bicoloredSubgraph first second).ConnectedComponent,
      EdgeColoring.pullbackEmbedding (coloring.swapOnKempeComponent first second L) embedding =
        (coloring.pullbackEmbedding embedding).swapOnKempeComponent first second K) ↔
      ¬ ComponentFuses coloring embedding first second K := by
  constructor
  · rintro ⟨L, heq⟩ ⟨other, hneOther, hmap⟩
    let f := bicoloredSubgraphEmbedding coloring embedding first second
    obtain ⟨x, hx⟩ := K.nonempty_supp
    obtain ⟨y, hy⟩ := other.nonempty_supp
    have hxL := (membership_iff_of_lifted_switch coloring embedding hne K L heq x.val).mp
      ⟨x.property, hx⟩
    have hKL : K.map f.toHom = L := (mem_map f K hx).symm.trans hxL.choose_spec
    have hyL : embedding.mapEdgeSet y.val ∈ coloring.kempeComponentSet first second L :=
      ⟨y.property, (mem_map f other hy).trans (hmap.trans hKL)⟩
    have hyK := (membership_iff_of_lifted_switch coloring embedding hne K L heq y.val).mpr hyL
    exact hneOther (hy.symm.trans hyK.choose_spec)
  · intro h
    exact ⟨_, lifted_switch_of_not_fuses coloring embedding first second K h⟩

end Mettapedia.GraphTheory.FourColor.KempeEmbeddingFusion
