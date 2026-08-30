import Mettapedia.Combinatorics.Matching.GraphBridge
import Mettapedia.GraphTheory.FourColor.CDLFlow
import Mettapedia.GraphTheory.FourColor.Goal

/-!
# Tait colourings as three perfect matchings

This file gives the exact bridge between the Tait-colouring language used by
the four-colour route and the shared perfect-matching API.  A decomposition is
not merely three matchings supported by the graph: their three partners are
distinct at every vertex and every graph edge occurs in one of them.

For a cubic graph, a Tait colouring produces such a decomposition by taking
its three colour classes.  Conversely, the index of the unique matching that
contains an edge is a proper three-edge-colouring.  The converse does not use
cubicity; cubicity is needed only to show that the three colour classes cover
all incident edges.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24TaitMatchingDecomposition

open SimpleGraph
open MatchingParity

variable {V : Type*} [DecidableEq V]

/-- The three nonzero Tait colours, indexed by `Fin 3`. -/
def taitColor : Fin 3 → Color := ![red, blue, purple]

@[simp] theorem taitColor_zero : taitColor 0 = red := rfl
@[simp] theorem taitColor_one : taitColor 1 = blue := rfl
@[simp] theorem taitColor_two : taitColor 2 = purple := rfl

theorem taitColor_ne_zero (i : Fin 3) : taitColor i ≠ 0 := by
  fin_cases i <;> simp [taitColor]

theorem taitColor_injective : Function.Injective taitColor := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all [taitColor, red, blue, purple]

/-- Every nonzero `F₂²` colour has a unique `Fin 3` index. -/
theorem exists_unique_taitColor_index (c : Color) (hc : c ≠ 0) :
    ∃! i : Fin 3, taitColor i = c := by
  rcases eq_red_or_eq_blue_or_eq_purple_of_ne_zero c hc with rfl | rfl | rfl
  · refine ⟨0, rfl, ?_⟩
    intro i hi
    exact taitColor_injective (hi.trans rfl)
  · refine ⟨1, rfl, ?_⟩
    intro i hi
    exact taitColor_injective (hi.trans rfl)
  · refine ⟨2, rfl, ?_⟩
    intro i hi
    exact taitColor_injective (hi.trans rfl)

/-- Three pairwise-distinct nonzero colours contain every nonzero colour. -/
theorem localTaitTriple_contains_taitColor {a b c : Color}
    (h : IsLocalTaitTriple a b c) (i : Fin 3) :
    a = taitColor i ∨ b = taitColor i ∨ c = taitColor i := by
  fin_cases i <;>
    rcases eq_red_or_eq_blue_or_eq_purple_of_ne_zero a h.1.1 with rfl | rfl | rfl <;>
    rcases eq_red_or_eq_blue_or_eq_purple_of_ne_zero b h.1.2.1 with rfl | rfl | rfl <;>
    rcases eq_red_or_eq_blue_or_eq_purple_of_ne_zero c h.1.2.2 with rfl | rfl | rfl <;>
    simp_all [IsLocalTaitTriple, IsLocalNowhereZeroTriple,
      taitColor, red, blue, purple]

/-- The spanning subgraph formed by one colour class of an edge colouring. -/
def colorClassSubgraph {G : SimpleGraph V} (C : G.EdgeColoring Color)
    (c : Color) : G.Subgraph where
  verts := Set.univ
  Adj v w := ∃ h : G.Adj v w, C ⟨s(v, w), h⟩ = c
  adj_sub := by
    intro v w h
    exact h.choose
  edge_vert := by simp
  symm := by
    constructor
    intro v w hw
    rcases hw with ⟨h, hc⟩
    exact ⟨h.symm, by simpa [Sym2.eq_swap] using hc⟩

@[simp] theorem colorClassSubgraph_verts {G : SimpleGraph V}
    (C : G.EdgeColoring Color) (c : Color) :
    (colorClassSubgraph C c).verts = Set.univ := rfl

theorem colorClassSubgraph_adj {G : SimpleGraph V}
    (C : G.EdgeColoring Color) (c : Color) {v w : V} :
    (colorClassSubgraph C c).Adj v w ↔
      ∃ h : G.Adj v w, C ⟨s(v, w), h⟩ = c :=
  Iff.rfl

/-- At a cubic vertex, every nonzero colour occurs on exactly one incident
edge.  Thus each colour class of a Tait colouring is a perfect matching. -/
theorem colorClassSubgraph_isPerfectMatching
    {G : SimpleGraph V} [Fintype G.edgeSet]
    (hG : HasCubicIncidentEdgeTriples G)
    (C : G.EdgeColoring Color) (hC : IsTaitEdgeColoring G C)
    (i : Fin 3) :
    (colorClassSubgraph C (taitColor i)).IsPerfectMatching := by
  rw [SimpleGraph.Subgraph.isPerfectMatching_iff]
  intro v
  rcases hG v with ⟨e₁, e₂, e₃, hincident⟩
  have hlocal :=
    isLocalTaitTriple_of_taitEdgeColoring_at_incidentTriple hincident hC
  have uniqueFor (e : G.edgeSet) (hemem : e ∈ incidentEdgeFinset G v)
      (hcolour : C e = taitColor i) :
      ∃! w, (colorClassSubgraph C (taitColor i)).Adj v w := by
    have hv : v ∈ (e : Sym2 V) := by
      simpa [incidentEdgeFinset] using hemem
    rcases (Sym2.mem_iff_exists.mp hv) with ⟨w, heq⟩
    have hadj : G.Adj v w := by
      rw [← SimpleGraph.mem_edgeSet, ← heq]
      exact e.property
    have hedge : (⟨s(v, w), hadj⟩ : G.edgeSet) = e :=
      Subtype.ext heq.symm
    have hcolour0 : C (⟨s(v, w), hadj⟩ : G.edgeSet) = taitColor i := by
      simpa [hedge] using hcolour
    refine ⟨w, ⟨hadj, hcolour0⟩, ?_⟩
    intro w' hw'
    rcases hw' with ⟨hadj', hcolour'⟩
    by_contra hne
    let e' : G.edgeSet := ⟨s(v, w'), hadj'⟩
    have hedges_ne : (⟨s(v, w), hadj⟩ : G.edgeSet) ≠ e' := by
      intro he
      apply hne
      exact (Sym2.congr_right.mp (congrArg Subtype.val he)).symm
    have hline : G.lineGraph.Adj (⟨s(v, w), hadj⟩ : G.edgeSet) e' :=
      (SimpleGraph.lineGraph_adj_iff_exists).2
        ⟨hedges_ne, ⟨v, Sym2.mem_mk_left _ _, Sym2.mem_mk_left _ _⟩⟩
    exact (C.valid hline) (hcolour0.trans hcolour'.symm)
  rcases localTaitTriple_contains_taitColor hlocal i with hcolour | hcolour | hcolour
  · apply uniqueFor e₁
    · rw [hincident.1]
      simp
    · exact hcolour
  · apply uniqueFor e₂
    · rw [hincident.1]
      simp
    · exact hcolour
  · apply uniqueFor e₃
    · rw [hincident.1]
      simp
    · exact hcolour

/-- An exact decomposition of a simple graph into three perfect matchings.
`covers` rules out a mere three-matching subgraph; `partners_injective` rules
out an edge receiving two colours. -/
structure ThreeMatchingDecomposition (G : SimpleGraph V) where
  skeleton : Skeleton V
  supported : ∀ i, (skeleton.matching i).SupportedBy G
  partners_injective : ∀ v, Function.Injective (skeleton.partners v)
  covers : ∀ ⦃v w⦄, G.Adj v w → ∃ i, skeleton.partners v i = w

namespace ThreeMatchingDecomposition

variable {G : SimpleGraph V}

/-- The matching index of an oriented graph edge. -/
noncomputable def indexOfAdj (D : ThreeMatchingDecomposition G)
    {v w : V} (h : G.Adj v w) : Fin 3 :=
  Classical.choose (D.covers h)

theorem partners_indexOfAdj (D : ThreeMatchingDecomposition G)
    {v w : V} (h : G.Adj v w) :
    D.skeleton.partners v (D.indexOfAdj h) = w :=
  Classical.choose_spec (D.covers h)

theorem indexOfAdj_unique (D : ThreeMatchingDecomposition G)
    {v w : V} (h : G.Adj v w) {i : Fin 3}
    (hi : D.skeleton.partners v i = w) :
    D.indexOfAdj h = i := by
  apply D.partners_injective v
  rw [D.partners_indexOfAdj h, hi]

theorem indexOfAdj_symm (D : ThreeMatchingDecomposition G)
    {v w : V} (h : G.Adj v w) :
    D.indexOfAdj h.symm = D.indexOfAdj h := by
  apply D.indexOfAdj_unique h.symm
  have hp := (D.skeleton.matching (D.indexOfAdj h)).partner_partner v
  have hforward := D.partners_indexOfAdj h
  unfold Skeleton.partners at hforward ⊢
  rw [hforward] at hp
  exact hp

/-- The endpoints selected by an edge of `G` are adjacent. -/
theorem out_adj (e : G.edgeSet) : G.Adj e.1.out.1 e.1.out.2 := by
  rw [← SimpleGraph.mem_edgeSet, Sym2.mk, e.1.out_eq]
  exact e.2

/-- The unique matching index of an unoriented edge. -/
noncomputable def edgeIndex (D : ThreeMatchingDecomposition G)
    (e : G.edgeSet) : Fin 3 :=
  D.indexOfAdj (out_adj e)

/-- At either endpoint, the edge joins that vertex to its partner in the
edge's selected matching. -/
theorem edge_eq_vertex_partner (D : ThreeMatchingDecomposition G)
    (e : G.edgeSet) {v : V} (hv : v ∈ (e : Sym2 V)) :
    (e : Sym2 V) = s(v, D.skeleton.partners v (D.edgeIndex e)) := by
  have heq : s(e.1.out.1, e.1.out.2) = (e : Sym2 V) := by
    simpa [Sym2.mk] using e.1.out_eq
  have hv' : v = e.1.out.1 ∨ v = e.1.out.2 := by
    rw [← heq] at hv
    simpa using hv
  rcases hv' with rfl | rfl
  · change (e : Sym2 V) =
      s(e.1.out.1, D.skeleton.partners e.1.out.1
        (D.indexOfAdj (out_adj e)))
    rw [D.partners_indexOfAdj (out_adj e)]
    exact heq.symm
  · have hpartner :
        D.skeleton.partners e.1.out.2 (D.edgeIndex e) = e.1.out.1 := by
      have hp :=
        (D.skeleton.matching (D.indexOfAdj (out_adj e))).partner_partner e.1.out.1
      have hforward := D.partners_indexOfAdj (out_adj e)
      unfold Skeleton.partners at hforward
      change
        (D.skeleton.matching (D.indexOfAdj (out_adj e))).partner e.1.out.2 =
          e.1.out.1
      rw [hforward] at hp
      exact hp
    rw [hpartner, Sym2.eq_swap]
    exact heq.symm

/-- Distinct adjacent graph edges receive distinct matching indices. -/
theorem edgeIndex_ne_of_lineGraph_adj (D : ThreeMatchingDecomposition G)
    {e f : G.edgeSet} (h : G.lineGraph.Adj e f) :
    D.edgeIndex e ≠ D.edgeIndex f := by
  rcases (SimpleGraph.lineGraph_adj_iff_exists).1 h with ⟨hef, v, hve, hvf⟩
  intro hindex
  apply hef
  apply Subtype.ext
  rw [D.edge_eq_vertex_partner e hve, D.edge_eq_vertex_partner f hvf, hindex]

/-- A three-matching decomposition yields a proper three-edge-colouring. -/
noncomputable def edgeColoring (D : ThreeMatchingDecomposition G) :
    G.EdgeColoring Color :=
  SimpleGraph.Coloring.mk (fun e => taitColor (D.edgeIndex e)) (by
    intro e f h
    exact taitColor_injective.ne (D.edgeIndex_ne_of_lineGraph_adj h))

theorem edgeColoring_isTait (D : ThreeMatchingDecomposition G) :
    IsTaitEdgeColoring G D.edgeColoring := by
  intro e
  exact taitColor_ne_zero (D.edgeIndex e)

end ThreeMatchingDecomposition

/-- Extract the three exact colour-class matchings from a Tait colouring of a
cubic graph. -/
noncomputable def decompositionOfTaitColoring
    {G : SimpleGraph V} [Fintype G.edgeSet]
    (hG : HasCubicIncidentEdgeTriples G)
    (C : G.EdgeColoring Color) (hC : IsTaitEdgeColoring G C) :
    ThreeMatchingDecomposition G where
  skeleton :=
    ⟨fun i => Pairing.ofPerfectMatching
      (colorClassSubgraph_isPerfectMatching hG C hC i)⟩
  supported := by
    intro i
    exact Pairing.ofPerfectMatching_supportedBy
      (colorClassSubgraph_isPerfectMatching hG C hC i)
  partners_injective := by
    intro v i j hij
    let Mi := colorClassSubgraph C (taitColor i)
    let Mj := colorClassSubgraph C (taitColor j)
    have hiAdj : Mi.Adj v
        ((Pairing.ofPerfectMatching
          (colorClassSubgraph_isPerfectMatching hG C hC i)).partner v) :=
      ((colorClassSubgraph_isPerfectMatching hG C hC i).1
        ((colorClassSubgraph_isPerfectMatching hG C hC i).2 v)).choose_spec.1
    have hjAdj : Mj.Adj v
        ((Pairing.ofPerfectMatching
          (colorClassSubgraph_isPerfectMatching hG C hC j)).partner v) :=
      ((colorClassSubgraph_isPerfectMatching hG C hC j).1
        ((colorClassSubgraph_isPerfectMatching hG C hC j).2 v)).choose_spec.1
    rcases hiAdj with ⟨hiG, hiColour⟩
    rcases hjAdj with ⟨hjG, hjColour⟩
    apply taitColor_injective
    have hij' :
        (Pairing.ofPerfectMatching
          (colorClassSubgraph_isPerfectMatching hG C hC i)).partner v =
        (Pairing.ofPerfectMatching
          (colorClassSubgraph_isPerfectMatching hG C hC j)).partner v := by
      simpa [Skeleton.partners] using hij
    have hedge :
        (⟨s(v,
          (Pairing.ofPerfectMatching
            (colorClassSubgraph_isPerfectMatching hG C hC i)).partner v), hiG⟩ :
          G.edgeSet) =
        ⟨s(v,
          (Pairing.ofPerfectMatching
            (colorClassSubgraph_isPerfectMatching hG C hC j)).partner v), hjG⟩ := by
      apply Subtype.ext
      exact congrArg (fun w => s(v, w)) hij'
    exact hiColour.symm.trans ((congrArg C hedge).trans hjColour)
  covers := by
    intro v w hvw
    let e : G.edgeSet := ⟨s(v, w), hvw⟩
    obtain ⟨i, hi, _⟩ := exists_unique_taitColor_index (C e) (hC e)
    refine ⟨i, ?_⟩
    apply Pairing.ofPerfectMatching_partner_eq_of_adj
      (colorClassSubgraph_isPerfectMatching hG C hC i)
    exact ⟨hvw, hi.symm⟩

/-- On cubic graphs, Tait colourability is exactly decomposition into three
graph-supported perfect matchings. -/
theorem taitColorable_iff_nonempty_threeMatchingDecomposition
    {G : SimpleGraph V} [Fintype G.edgeSet]
    (hG : HasCubicIncidentEdgeTriples G) :
    TaitColorable G ↔ Nonempty (ThreeMatchingDecomposition G) := by
  constructor
  · rintro ⟨C, hC⟩
    exact ⟨decompositionOfTaitColoring hG C hC⟩
  · rintro ⟨D⟩
    exact ⟨D.edgeColoring, D.edgeColoring_isTait⟩

/-- Contrapositive form used by the minimal-counterexample route. -/
theorem no_threeMatchingDecomposition_of_not_taitColorable
    {G : SimpleGraph V} [Fintype G.edgeSet]
    (hG : HasCubicIncidentEdgeTriples G) (hnot : ¬ TaitColorable G) :
    IsEmpty (ThreeMatchingDecomposition G) := by
  constructor
  intro D
  exact hnot ((taitColorable_iff_nonempty_threeMatchingDecomposition hG).2 ⟨D⟩)

end GoertzelV24TaitMatchingDecomposition

end Mettapedia.GraphTheory.FourColor
