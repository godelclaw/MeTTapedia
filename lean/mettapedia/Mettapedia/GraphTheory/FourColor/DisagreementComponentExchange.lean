import Mettapedia.GraphTheory.FourColor.DeletionAbsoluteMinimum

/-!
# Copying whole disagreement components

Copy the donor colouring on a set of common edges closed under disagreement
adjacency. If no incident recipient edge leaves the common graph, the copy
is proper and removes every selected disagreement. At an absolute minimum,
each nonempty disagreement component therefore touches both embedding
boundaries. No Kempe reachability or planarity is used.
-/

namespace Mettapedia.GraphTheory.FourColor.DisagreementComponentExchange

open SimpleGraph GoertzelV24LocalSwapKempeGeneration
open GoertzelV24KempeComponentEmbeddingBoundary DeletionAbsoluteMinimum
open KempeTargetFusion

attribute [-instance]
  GoertzelV24RetainedVertexRotationSplice.retainedVertexFintype
  GoertzelV24SeamFaceArcPartition.hitPointFintype

noncomputable section
universe u v w
variable {A : Type u} {B : Type v} {C : Type w}
  [Fintype A] [DecidableEq A] {G : SimpleGraph A} [DecidableRel G.Adj]
  {H : SimpleGraph B} {J : SimpleGraph C}

def copyFunction (f : G ↪g H) (c : H.EdgeColoring Color)
    (d : G.EdgeColoring Color) (s : Finset G.edgeSet) (e : H.edgeSet) : Color := by
  classical
  exact if h : ∃ x ∈ s, f.mapEdgeSet x = e then d h.choose else c e

omit [Fintype A] [DecidableRel G.Adj] in
theorem copyFunction_map (f : G ↪g H) (c : H.EdgeColoring Color)
    (d : G.EdgeColoring Color) (s : Finset G.edgeSet) (e : G.edgeSet) :
    copyFunction f c d s (f.mapEdgeSet e) = if e ∈ s then d e else c (f.mapEdgeSet e) := by
  classical
  unfold copyFunction
  by_cases he : e ∈ s
  · have h : ∃ x ∈ s, f.mapEdgeSet x = f.mapEdgeSet e := ⟨e, he, rfl⟩
    rw [dif_pos h, if_pos he]
    congr 1
    exact f.mapEdgeSet.injective h.choose_spec.2
  · have h : ¬ ∃ x ∈ s, f.mapEdgeSet x = f.mapEdgeSet e := by
      rintro ⟨x, hx, hxe⟩
      exact he (f.mapEdgeSet.injective hxe ▸ hx)
    rw [dif_neg h, if_neg he]

omit [Fintype A] [DecidableRel G.Adj] in
private theorem copy_ne_of_selected (f : G ↪g H) (c : H.EdgeColoring Color)
    (d : G.EdgeColoring Color) (s : Finset G.edgeSet)
    (frontier : ∀ x ∈ s, ∀ y, G.lineGraph.Adj x y →
      y ∈ s ∨ c (f.mapEdgeSet y) = d y)
    (boundary : ∀ x ∈ s, ∀ z, H.lineGraph.Adj (f.mapEdgeSet x) z →
      ∃ y, f.mapEdgeSet y = z)
    {x : G.edgeSet} (hx : x ∈ s) {z : H.edgeSet}
    (hadj : H.lineGraph.Adj (f.mapEdgeSet x) z) :
    copyFunction f c d s (f.mapEdgeSet x) ≠ copyFunction f c d s z := by
  classical
  obtain ⟨y, rfl⟩ := boundary x hx z hadj
  have hxy : G.lineGraph.Adj x y := f.toCopy.toLineGraphEmbedding.map_rel_iff.mp hadj
  rw [copyFunction_map, copyFunction_map, if_pos hx]
  split_ifs with hy
  · exact d.valid hxy
  · rw [(frontier x hx y hxy).resolve_left hy]
    exact d.valid hxy

def copyColoring (f : G ↪g H) (c : H.EdgeColoring Color)
    (d : G.EdgeColoring Color) (s : Finset G.edgeSet)
    (frontier : ∀ x ∈ s, ∀ y, G.lineGraph.Adj x y →
      y ∈ s ∨ c (f.mapEdgeSet y) = d y)
    (boundary : ∀ x ∈ s, ∀ z, H.lineGraph.Adj (f.mapEdgeSet x) z →
      ∃ y, f.mapEdgeSet y = z) : H.EdgeColoring Color :=
  SimpleGraph.Coloring.mk (copyFunction f c d s) (by
    classical
    intro e z hadj
    by_cases he : ∃ x ∈ s, f.mapEdgeSet x = e
    · obtain ⟨x, hx, rfl⟩ := he
      exact copy_ne_of_selected f c d s frontier boundary hx hadj
    · by_cases hz : ∃ x ∈ s, f.mapEdgeSet x = z
      · obtain ⟨x, hx, rfl⟩ := hz
        exact Ne.symm (copy_ne_of_selected f c d s frontier boundary hx hadj.symm)
      · simpa only [copyFunction, dif_neg he, dif_neg hz] using c.valid hadj)

omit [Fintype A] [DecidableRel G.Adj] in
theorem copyColoring_tait (f : G ↪g H) (c : H.EdgeColoring Color)
    (d : G.EdgeColoring Color) (s : Finset G.edgeSet) (frontier boundary)
    (hc : IsTaitEdgeColoring H c) (hd : IsTaitEdgeColoring G d) :
    IsTaitEdgeColoring H (copyColoring f c d s frontier boundary) := by
  classical
  intro e
  change copyFunction f c d s e ≠ 0
  unfold copyFunction
  split_ifs with h
  · exact hd _
  · exact hc _

theorem copyColoring_decreases (f : G ↪g H) (c : H.EdgeColoring Color)
    (d : G.EdgeColoring Color) (s : Finset G.edgeSet) (frontier boundary)
    (hs : s.Nonempty) (hwrong : ∀ e ∈ s, c (f.mapEdgeSet e) ≠ d e) :
    (disagreementEdges ((copyColoring f c d s frontier boundary).pullbackEmbedding f) d).card <
      (disagreementEdges (c.pullbackEmbedding f) d).card := by
  classical
  have value (e : G.edgeSet) :
      (copyColoring f c d s frontier boundary).pullbackEmbedding f e =
        if e ∈ s then d e else c (f.mapEdgeSet e) := copyFunction_map f c d s e
  apply Finset.card_lt_card
  apply Finset.ssubset_iff_subset_ne.mpr
  constructor
  · intro e he
    have hn := (mem_disagreementEdges _ _ e).mp he
    rw [value] at hn
    split_ifs at hn with h
    · exact (hn rfl).elim
    · exact (mem_disagreementEdges _ _ e).mpr hn
  · obtain ⟨e, he⟩ := hs
    intro heq
    have hm := (mem_disagreementEdges (c.pullbackEmbedding f) d e).mpr (hwrong e he)
    rw [← heq] at hm
    have hn := (mem_disagreementEdges _ _ e).mp hm
    rw [value, if_pos he] at hn
    exact hn rfl

/-- Every nonempty closed disagreement set at a one-sided absolute minimum
has an actual adjacent edge outside the embedding image. -/
theorem boundary_of_minimum (f : G ↪g H) (c : H.EdgeColoring Color)
    (d : G.EdgeColoring Color) (hc : IsTaitEdgeColoring H c) (hd : IsTaitEdgeColoring G d)
    (hmin : ∀ next : H.EdgeColoring Color, IsTaitEdgeColoring H next →
      (disagreementEdges (c.pullbackEmbedding f) d).card ≤
        (disagreementEdges (next.pullbackEmbedding f) d).card)
    (s : Finset G.edgeSet) (hs : s.Nonempty)
    (hwrong : ∀ e ∈ s, c (f.mapEdgeSet e) ≠ d e)
    (frontier : ∀ x ∈ s, ∀ y, G.lineGraph.Adj x y →
      y ∈ s ∨ c (f.mapEdgeSet y) = d y) :
    ∃ x ∈ s, ∃ z, H.lineGraph.Adj (f.mapEdgeSet x) z ∧
      ¬ ∃ y, f.mapEdgeSet y = z := by
  classical
  by_contra hn
  push Not at hn
  let next := copyColoring f c d s frontier hn
  exact (Nat.not_lt_of_ge (hmin next (copyColoring_tait f c d s frontier hn hc hd)))
    (copyColoring_decreases f c d s frontier hn hs hwrong)

def graph (c d : G.EdgeColoring Color) : SimpleGraph {e : G.edgeSet // c e ≠ d e} :=
  G.lineGraph.induce {e | c e ≠ d e}

def componentEdges (c d : G.EdgeColoring Color) (K : (graph c d).ConnectedComponent) :
    Finset G.edgeSet := by
  classical
  exact Finset.univ.filter fun e => ∃ h : c e ≠ d e, (⟨e, h⟩ : {e // c e ≠ d e}) ∈ K

omit [DecidableEq A] in
theorem componentEdges_nonempty (c d : G.EdgeColoring Color)
    (K : (graph c d).ConnectedComponent) : (componentEdges c d K).Nonempty := by
  classical
  obtain ⟨x, hx⟩ := K.nonempty_supp
  exact ⟨x.val, Finset.mem_filter.mpr ⟨Finset.mem_univ _, x.property, hx⟩⟩

omit [DecidableEq A] in
theorem componentEdges_wrong (c d : G.EdgeColoring Color)
    (K : (graph c d).ConnectedComponent) {e} (he : e ∈ componentEdges c d K) : c e ≠ d e := by
  classical
  exact (Finset.mem_filter.mp he).2.choose

omit [DecidableEq A] in
theorem componentEdges_frontier (c d : G.EdgeColoring Color)
    (K : (graph c d).ConnectedComponent) {x} (hx : x ∈ componentEdges c d K)
    {y} (hxy : G.lineGraph.Adj x y) : y ∈ componentEdges c d K ∨ c y = d y := by
  classical
  by_cases hy : c y = d y
  · exact Or.inr hy
  left
  obtain ⟨hxx, hxK⟩ := (Finset.mem_filter.mp hx).2
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hy,
    K.mem_supp_of_adj_mem_supp hxK (show (graph c d).Adj ⟨x, hxx⟩ ⟨y, hy⟩ from hxy)⟩

/-- Both boundary contacts belong to the same whole-disagreement component,
including when local colour differences branch. -/
theorem absolute_component_touches_both (le : G ↪g H) (re : G ↪g J)
    (left : H.EdgeColoring Color) (right : J.EdgeColoring Color)
    (h : AbsoluteMinimum le re left right)
    (K : (graph (left.pullbackEmbedding le) (right.pullbackEmbedding re)).ConnectedComponent) :
    let s := componentEdges (left.pullbackEmbedding le) (right.pullbackEmbedding re) K
    (∃ x ∈ s, ∃ z, H.lineGraph.Adj (le.mapEdgeSet x) z ∧ ¬ ∃ y, le.mapEdgeSet y = z) ∧
    (∃ x ∈ s, ∃ z, J.lineGraph.Adj (re.mapEdgeSet x) z ∧ ¬ ∃ y, re.mapEdgeSet y = z) := by
  dsimp only
  constructor
  · exact boundary_of_minimum le left (right.pullbackEmbedding re) h.left_tait
      (isTaitEdgeColoring_pullbackEmbedding right re h.right_tait)
      (fun next hn => h.minimal next right hn h.right_tait) _
      (componentEdges_nonempty _ _ K) (fun e he => componentEdges_wrong _ _ K he)
      (fun x hx y hxy => componentEdges_frontier _ _ K hx hxy)
  · apply boundary_of_minimum re right (left.pullbackEmbedding le) h.right_tait
      (isTaitEdgeColoring_pullbackEmbedding left le h.left_tait)
    · intro next hn
      simpa only [disagreementEdges_symm (right.pullbackEmbedding re),
        disagreementEdges_symm (next.pullbackEmbedding re)] using h.minimal left next h.left_tait hn
    · exact componentEdges_nonempty _ _ K
    · intro e he
      exact Ne.symm (componentEdges_wrong _ _ K he)
    · intro x hx y hxy
      exact (componentEdges_frontier _ _ K hx hxy).imp_right Eq.symm

/-- Distinct components cannot use the same incident vertex. -/
theorem component_eq_of_incident (c d : G.EdgeColoring Color)
    (K L : (graph c d).ConnectedComponent) {e f : G.edgeSet}
    (he : e ∈ componentEdges c d K) (hf : f ∈ componentEdges c d L)
    {v : A} (hv : v ∈ e.val) (hw : v ∈ f.val) : K = L := by
  classical
  obtain ⟨he', heK⟩ := (Finset.mem_filter.mp he).2
  obtain ⟨hf', hfL⟩ := (Finset.mem_filter.mp hf).2
  by_cases hef : e = f
  · subst f
    exact heK.symm.trans hfL
  · have hK := K.mem_supp_of_adj_mem_supp heK
      (show (graph c d).Adj ⟨e, he'⟩ ⟨f, hf'⟩ from ⟨hef, v, hv, hw⟩)
    exact hK.symm.trans hfL

end
end Mettapedia.GraphTheory.FourColor.DisagreementComponentExchange
