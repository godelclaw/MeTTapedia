import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mettapedia.GraphTheory.FourColor.GoertzelV24TwoEdgeCut
import Mettapedia.GraphTheory.FourColor.GoertzelV24RotationCutDartDecomposition
import Mettapedia.GraphTheory.FourColor.GoertzelV24RotorProfile
import Mettapedia.GraphTheory.FourColor.GoertzelV24SquareGraphSplit

namespace Mettapedia.GraphTheory.FourColor

open SimpleGraph
open GoertzelV24RotationCutDartDecomposition

noncomputable section

/-- In a finite graph, if `u` is odd and the only possible odd vertices are
`u,v`, then `u` and `v` lie in the same component. The proof applies the
handshaking lemma inside the component of `u`. -/
theorem reachable_of_odd_degree_pair
    {N : Type*} [Fintype N] [DecidableEq N]
    (G : SimpleGraph N) [DecidableRel G.Adj] (u v : N)
    (hu : Odd (G.degree u))
    (hodd : ∀ w, Odd (G.degree w) -> w = u ∨ w = v) :
    G.Reachable u v := by
  classical
  let component : Set N := {w | G.Reachable u w}
  let u' : component := ⟨u, SimpleGraph.Reachable.rfl⟩
  have huNeighbors : G.neighborSet u ⊆ component := by
    intro w huw
    exact huw.reachable
  have huDegree : (G.induce component).degree u' = G.degree u :=
    G.degree_induce_of_neighborSet_subset huNeighbors
  have huOdd : Odd ((G.induce component).degree u') := huDegree.symm ▸ hu
  rcases (G.induce component).exists_ne_odd_degree_of_exists_odd_degree
      u' huOdd with ⟨w, hwu, hwOdd⟩
  have hwNeighbors : G.neighborSet w.1 ⊆ component := by
    intro z hwz
    exact w.2.trans hwz.reachable
  have hwDegree : (G.induce component).degree w = G.degree w.1 :=
    G.degree_induce_of_neighborSet_subset hwNeighbors
  have hwGlobal : Odd (G.degree w.1) := hwDegree ▸ hwOdd
  rcases hodd w.1 hwGlobal with hwu' | hwv
  · exact False.elim (hwu (Subtype.ext hwu'))
  · have hwReach : G.Reachable u w.1 := w.2
    exact hwv ▸ hwReach

namespace RotationSystem

variable {V E : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E]
variable (RS : RotationSystem V E)

/-- Dart graph for bicolored routing through one retained vertex side.
Selected alpha-pairs cross every edge touching the side; at retained vertices,
selected darts on the two tracked incident edges are paired. -/
def sideDartTrackedGraph (keep : V -> Prop) [DecidablePred keep]
    (C : E -> Color) (a b : Color) : SimpleGraph RS.D where
  Adj d e :=
    IsTrackedColor a b (C (RS.edgeOf d)) ∧
    IsTrackedColor a b (C (RS.edgeOf e)) ∧
    ((e = RS.alpha d ∧ (keep (RS.vertOf d) ∨ keep (RS.vertOf e))) ∨
      (d ≠ e ∧ keep (RS.vertOf d) ∧ RS.vertOf d = RS.vertOf e))
  symm := ⟨by
    intro d e h
    refine ⟨h.2.1, h.1, ?_⟩
    rcases h.2.2 with ⟨rfl, hkeep⟩ | ⟨hne, hd, hvert⟩
    · left
      refine ⟨?_, hkeep.symm⟩
      simpa using (RS.alpha_involutive d).symm
    · right
      exact ⟨hne.symm, hvert ▸ hd, hvert.symm⟩⟩
  loopless := ⟨by
    intro d h
    rcases h.2.2 with ⟨halpha, _⟩ | ⟨hne, _⟩
    · exact RS.alpha_fixfree d halpha.symm
    · exact hne rfl⟩

instance sideDartTrackedGraphDecidableRel
    (keep : V -> Prop) [DecidablePred keep]
    (C : E -> Color) (a b : Color) :
    DecidableRel (RS.sideDartTrackedGraph keep C a b).Adj :=
  fun d e => by
    change Decidable
      (IsTrackedColor a b (C (RS.edgeOf d)) ∧
        IsTrackedColor a b (C (RS.edgeOf e)) ∧
        ((e = RS.alpha d ∧ (keep (RS.vertOf d) ∨ keep (RS.vertOf e))) ∨
          (d ≠ e ∧ keep (RS.vertOf d) ∧ RS.vertOf d = RS.vertOf e)))
    infer_instance

/-- A route in the side dart graph projects to an actual route in the ambient
tracked edge-adjacency graph. Alpha steps collapse to equality of the
underlying edge; retained-vertex steps become genuine edge adjacencies. -/
theorem sideDartTrackedGraph_reachable_edgeOf
    (keep : V -> Prop) [DecidablePred keep]
    (C : E -> Color) (a b : Color) {d e : RS.D}
    (hreach : (RS.sideDartTrackedGraph keep C a b).Reachable d e) :
    (RS.trackedEdgeGraph C a b).Reachable (RS.edgeOf d) (RS.edgeOf e) := by
  have hpath := (SimpleGraph.reachable_iff_reflTransGen d e).mp hreach
  apply (SimpleGraph.reachable_iff_reflTransGen (RS.edgeOf d) (RS.edgeOf e)).mpr
  exact Relation.ReflTransGen.trans_induction_on
    (motive := fun {x y} _ =>
      Relation.ReflTransGen (RS.trackedEdgeGraph C a b).Adj
        (RS.edgeOf x) (RS.edgeOf y)) hpath
    (fun _ => Relation.ReflTransGen.refl)
    (fun {x y} hxy => by
      rcases hxy.2.2 with ⟨hAlpha, _htouch⟩ | ⟨hxyDart, _hxKeep, hvert⟩
      · have hedge : RS.edgeOf x = RS.edgeOf y := by
          rw [hAlpha, RS.edge_alpha]
        exact hedge ▸ Relation.ReflTransGen.refl
      · have hxMem : x ∈ RS.dartsAt (RS.vertOf x) := by
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩
        have hyMem : y ∈ RS.dartsAt (RS.vertOf x) := by
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hvert.symm⟩
        have hedgeNe : RS.edgeOf x ≠ RS.edgeOf y := by
          intro hedge
          exact hxyDart (RS.edgeOf_injOn_dartsAt _ hxMem hyMem hedge)
        have hxIncident : RS.edgeOf x ∈ RS.incidentEdges (RS.vertOf x) :=
          RS.mem_incidentEdges_iff.mpr ⟨x, rfl, rfl⟩
        have hyIncident : RS.edgeOf y ∈ RS.incidentEdges (RS.vertOf x) :=
          RS.mem_incidentEdges_iff.mpr ⟨y, rfl, hvert.symm⟩
        exact Relation.ReflTransGen.single
          ⟨RS.edgeAdjacencyGraph_adj_of_mem_incidentEdges
              hedgeNe hxIncident hyIncident,
            hxy.1, hxy.2.1⟩)
    (fun _ _ ihxy ihyz => ihxy.trans ihyz)

/-- At a cubic vertex, an actual Tait coloring uses each of the three nonzero
colors exactly once on the computed incident-edge finset. -/
theorem incidentEdges_image_color_eq_nonzeroColors
    (hCubic : RS.IsCubic)
    (C : RS.EdgeColoring Color) (hC : RS.IsTaitEdgeColoring C) (v : V) :
    (RS.incidentEdges v).image C =
      (Finset.univ.filter fun color : Color => color ≠ 0) := by
  have hinjective : Set.InjOn C (RS.incidentEdges v : Set E) := by
    intro e he f hf hef
    by_contra hne
    exact (C.valid (RS.edgeAdjacencyGraph_adj_of_mem_incidentEdges
      hne he hf)) hef
  have hsubset :
      (RS.incidentEdges v).image C ⊆
        (Finset.univ.filter fun color : Color => color ≠ 0) := by
    intro color hcolor
    rcases Finset.mem_image.mp hcolor with ⟨e, _he, rfl⟩
    simp [hC e]
  apply Finset.eq_of_subset_of_card_le hsubset
  rw [Finset.card_image_iff.mpr hinjective,
    RS.incidentEdges_card_eq_three_of_isCubic hCubic]
  decide

/-- Every nonzero color occurs on a unique edge incident to a cubic vertex. -/
theorem existsUnique_incidentEdge_color
    (hCubic : RS.IsCubic)
    (C : RS.EdgeColoring Color) (hC : RS.IsTaitEdgeColoring C)
    (v : V) (color : Color) (hcolor : color ≠ 0) :
    ∃! e : E, e ∈ RS.incidentEdges v ∧ C e = color := by
  have hmem : color ∈ (RS.incidentEdges v).image C := by
    rw [RS.incidentEdges_image_color_eq_nonzeroColors hCubic C hC v]
    simp [hcolor]
  rcases Finset.mem_image.mp hmem with ⟨e, he, heColor⟩
  refine ⟨e, ⟨he, heColor⟩, ?_⟩
  intro f hf
  by_contra hne
  exact (C.valid (RS.edgeAdjacencyGraph_adj_of_mem_incidentEdges
    hne hf.1 he)) (hf.2.trans heColor.symm)

/-- Every nonzero color occurs on a unique dart based at a cubic vertex. -/
theorem existsUnique_dartAt_color
    (hCubic : RS.IsCubic)
    (C : RS.EdgeColoring Color) (hC : RS.IsTaitEdgeColoring C)
    (v : V) (color : Color) (hcolor : color ≠ 0) :
    ∃! d : RS.D, RS.vertOf d = v ∧ C (RS.edgeOf d) = color := by
  rcases RS.existsUnique_incidentEdge_color hCubic C hC v color hcolor with
    ⟨e, he, heUnique⟩
  rcases (RS.mem_incidentEdges_iff.mp he.1) with ⟨d, hdEdge, hdVert⟩
  refine ⟨d, ⟨hdVert, hdEdge ▸ he.2⟩, ?_⟩
  intro d' hd'
  have hd'EdgeMem : RS.edgeOf d' ∈ RS.incidentEdges v :=
    RS.mem_incidentEdges_iff.mpr ⟨d', rfl, hd'.1⟩
  have hedge : RS.edgeOf d' = e :=
    heUnique (RS.edgeOf d') ⟨hd'EdgeMem, hd'.2⟩
  apply RS.edgeOf_injOn_dartsAt v
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hd'.1⟩
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hdVert⟩
  · exact hedge.trans hdEdge.symm

noncomputable def dartAtColor
    (hCubic : RS.IsCubic)
    (C : RS.EdgeColoring Color) (hC : RS.IsTaitEdgeColoring C)
    (v : V) (color : Color) (hcolor : color ≠ 0) : RS.D :=
  Classical.choose (RS.existsUnique_dartAt_color hCubic C hC v color hcolor)

theorem dartAtColor_spec
    (hCubic : RS.IsCubic)
    (C : RS.EdgeColoring Color) (hC : RS.IsTaitEdgeColoring C)
    (v : V) (color : Color) (hcolor : color ≠ 0) :
    RS.vertOf (RS.dartAtColor hCubic C hC v color hcolor) = v ∧
      C (RS.edgeOf (RS.dartAtColor hCubic C hC v color hcolor)) = color :=
  (Classical.choose_spec
    (RS.existsUnique_dartAt_color hCubic C hC v color hcolor)).1

theorem eq_dartAtColor
    (hCubic : RS.IsCubic)
    (C : RS.EdgeColoring Color) (hC : RS.IsTaitEdgeColoring C)
    (v : V) (color : Color) (hcolor : color ≠ 0) (d : RS.D)
    (hd : RS.vertOf d = v ∧ C (RS.edgeOf d) = color) :
    d = RS.dartAtColor hCubic C hC v color hcolor :=
  (Classical.choose_spec
    (RS.existsUnique_dartAt_color hCubic C hC v color hcolor)).2 d hd

theorem sideDartTrackedGraph_swap
    (keep : V -> Prop) [DecidablePred keep]
    (C : E -> Color) (a b : Color) :
    RS.sideDartTrackedGraph keep C a b =
      RS.sideDartTrackedGraph keep C b a := by
  ext d e
  simp only [sideDartTrackedGraph, IsTrackedColor]
  tauto

/-- At a retained vertex, a selected dart has exactly two side-routing
neighbors: its alpha mate and the unique dart of the other tracked color. -/
theorem sideDartTrackedGraph_neighborFinset_inside_of_color_left
    (keep : V -> Prop) [DecidablePred keep]
    (hCubic : RS.IsCubic)
    (C : RS.EdgeColoring Color) (hC : RS.IsTaitEdgeColoring C)
    (a b : Color) (ha : a ≠ 0) (hb : b ≠ 0) (hab : a ≠ b)
    (d : RS.D) (hkeep : keep (RS.vertOf d))
    (hdColor : C (RS.edgeOf d) = a) :
    (RS.sideDartTrackedGraph keep C a b).neighborFinset d =
      {RS.alpha d,
        RS.dartAtColor hCubic C hC (RS.vertOf d) b hb} := by
  classical
  let mate := RS.dartAtColor hCubic C hC (RS.vertOf d) b hb
  have hmate := RS.dartAtColor_spec hCubic C hC (RS.vertOf d) b hb
  have hmateNe : mate ≠ d := by
    intro h
    have : C (RS.edgeOf d) = b := by simpa [mate, h] using hmate.2
    exact hab (hdColor.symm.trans this)
  ext x
  simp only [SimpleGraph.mem_neighborFinset, Finset.mem_insert,
    Finset.mem_singleton]
  constructor
  · intro hx
    rcases hx.2.2 with ⟨hxa, _⟩ | ⟨hxd, _hdKeep, hvertex⟩
    · exact Or.inl hxa
    · right
      rcases hx.2.1 with hxColorA | hxColorB
      · have hxd' : x = d := by
          have hxAt : RS.vertOf x = RS.vertOf d ∧
              C (RS.edgeOf x) = a := ⟨hvertex.symm, hxColorA⟩
          have hdAt : RS.vertOf d = RS.vertOf d ∧
              C (RS.edgeOf d) = a := ⟨rfl, hdColor⟩
          exact (RS.eq_dartAtColor hCubic C hC _ a ha x hxAt).trans
            (RS.eq_dartAtColor hCubic C hC _ a ha d hdAt).symm
        exact False.elim (hxd hxd'.symm)
      · exact RS.eq_dartAtColor hCubic C hC _ b hb x
          ⟨hvertex.symm, hxColorB⟩
  · rintro (rfl | rfl)
    · refine ⟨Or.inl ?_, Or.inl ?_, Or.inl ⟨rfl, Or.inl hkeep⟩⟩
      · exact hdColor
      · simpa [RS.edge_alpha] using hdColor
    · refine ⟨Or.inl hdColor, Or.inr hmate.2, Or.inr ?_⟩
      exact ⟨hmateNe.symm, hkeep, hmate.1.symm⟩

theorem sideDartTrackedGraph_degree_inside_of_color_left
    (keep : V -> Prop) [DecidablePred keep]
    (hCubic : RS.IsCubic)
    (C : RS.EdgeColoring Color) (hC : RS.IsTaitEdgeColoring C)
    (a b : Color) (ha : a ≠ 0) (hb : b ≠ 0) (hab : a ≠ b)
    (d : RS.D) (hkeep : keep (RS.vertOf d))
    (hdColor : C (RS.edgeOf d) = a) :
    (RS.sideDartTrackedGraph keep C a b).degree d = 2 := by
  classical
  rw [← SimpleGraph.card_neighborFinset_eq_degree,
    RS.sideDartTrackedGraph_neighborFinset_inside_of_color_left
      keep hCubic C hC a b ha hb hab d hkeep hdColor]
  have hne : RS.alpha d ≠
      RS.dartAtColor hCubic C hC (RS.vertOf d) b hb := by
    intro h
    have hvertex := (RS.dartAtColor_spec
      hCubic C hC (RS.vertOf d) b hb).1
    exact RS.no_self_loops d (by simpa [h] using hvertex.symm)
  simp [hne]

theorem sideDartTrackedGraph_neighborFinset_inside_of_color_right
    (keep : V -> Prop) [DecidablePred keep]
    (hCubic : RS.IsCubic)
    (C : RS.EdgeColoring Color) (hC : RS.IsTaitEdgeColoring C)
    (a b : Color) (ha : a ≠ 0) (hb : b ≠ 0) (hab : a ≠ b)
    (d : RS.D) (hkeep : keep (RS.vertOf d))
    (hdColor : C (RS.edgeOf d) = b) :
    (RS.sideDartTrackedGraph keep C a b).neighborFinset d =
      {RS.alpha d,
        RS.dartAtColor hCubic C hC (RS.vertOf d) a ha} := by
  classical
  let mate := RS.dartAtColor hCubic C hC (RS.vertOf d) a ha
  have hmate := RS.dartAtColor_spec hCubic C hC (RS.vertOf d) a ha
  have hmateNe : mate ≠ d := by
    intro h
    have : C (RS.edgeOf d) = a := by simpa [mate, h] using hmate.2
    exact hab (this.symm.trans hdColor)
  ext x
  simp only [SimpleGraph.mem_neighborFinset, Finset.mem_insert,
    Finset.mem_singleton]
  constructor
  · intro hx
    rcases hx.2.2 with ⟨hxa, _⟩ | ⟨hxd, _hdKeep, hvertex⟩
    · exact Or.inl hxa
    · right
      rcases hx.2.1 with hxColorA | hxColorB
      · exact RS.eq_dartAtColor hCubic C hC _ a ha x
          ⟨hvertex.symm, hxColorA⟩
      · have hxd' : x = d := by
          have hxAt : RS.vertOf x = RS.vertOf d ∧
              C (RS.edgeOf x) = b := ⟨hvertex.symm, hxColorB⟩
          have hdAt : RS.vertOf d = RS.vertOf d ∧
              C (RS.edgeOf d) = b := ⟨rfl, hdColor⟩
          exact (RS.eq_dartAtColor hCubic C hC _ b hb x hxAt).trans
            (RS.eq_dartAtColor hCubic C hC _ b hb d hdAt).symm
        exact False.elim (hxd hxd'.symm)
  · rintro (rfl | rfl)
    · refine ⟨Or.inr ?_, Or.inr ?_, Or.inl ⟨rfl, Or.inl hkeep⟩⟩
      · exact hdColor
      · simpa [RS.edge_alpha] using hdColor
    · refine ⟨Or.inr hdColor, Or.inl hmate.2, Or.inr ?_⟩
      exact ⟨hmateNe.symm, hkeep, hmate.1.symm⟩

theorem sideDartTrackedGraph_degree_inside_of_color_right
    (keep : V -> Prop) [DecidablePred keep]
    (hCubic : RS.IsCubic)
    (C : RS.EdgeColoring Color) (hC : RS.IsTaitEdgeColoring C)
    (a b : Color) (ha : a ≠ 0) (hb : b ≠ 0) (hab : a ≠ b)
    (d : RS.D) (hkeep : keep (RS.vertOf d))
    (hdColor : C (RS.edgeOf d) = b) :
    (RS.sideDartTrackedGraph keep C a b).degree d = 2 := by
  classical
  rw [← SimpleGraph.card_neighborFinset_eq_degree,
    RS.sideDartTrackedGraph_neighborFinset_inside_of_color_right
      keep hCubic C hC a b ha hb hab d hkeep hdColor]
  have hne : RS.alpha d ≠
      RS.dartAtColor hCubic C hC (RS.vertOf d) a ha := by
    intro h
    have hvertex := (RS.dartAtColor_spec
      hCubic C hC (RS.vertOf d) a ha).1
    exact RS.no_self_loops d (by simpa [h] using hvertex.symm)
  simp [hne]

/-- Every selected dart based on the retained side has degree two in the side
routing graph. -/
theorem sideDartTrackedGraph_degree_inside
    (keep : V -> Prop) [DecidablePred keep]
    (hCubic : RS.IsCubic)
    (C : RS.EdgeColoring Color) (hC : RS.IsTaitEdgeColoring C)
    (a b : Color) (ha : a ≠ 0) (hb : b ≠ 0) (hab : a ≠ b)
    (d : RS.D) (hkeep : keep (RS.vertOf d))
    (htracked : IsTrackedColor a b (C (RS.edgeOf d))) :
    (RS.sideDartTrackedGraph keep C a b).degree d = 2 := by
  rcases htracked with hdColor | hdColor
  · exact RS.sideDartTrackedGraph_degree_inside_of_color_left
      keep hCubic C hC a b ha hb hab d hkeep hdColor
  · exact RS.sideDartTrackedGraph_degree_inside_of_color_right
      keep hCubic C hC a b ha hb hab d hkeep hdColor

theorem sideDartTrackedGraph_degree_untracked
    (keep : V -> Prop) [DecidablePred keep]
    (C : E -> Color) (a b : Color) (d : RS.D)
    (huntracked : ¬ IsTrackedColor a b (C (RS.edgeOf d))) :
    (RS.sideDartTrackedGraph keep C a b).degree d = 0 := by
  classical
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  have hempty :
      (RS.sideDartTrackedGraph keep C a b).neighborFinset d = ∅ := by
    ext x
    simp [SimpleGraph.mem_neighborFinset, sideDartTrackedGraph, huntracked]
  rw [hempty]
  simp

theorem sideDartTrackedGraph_degree_outside_untouched
    (keep : V -> Prop) [DecidablePred keep]
    (C : E -> Color) (a b : Color) (d : RS.D)
    (houtside : ¬ keep (RS.vertOf d))
    (hopposite : ¬ keep (RS.vertOf (RS.alpha d))) :
    (RS.sideDartTrackedGraph keep C a b).degree d = 0 := by
  classical
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  have hempty :
      (RS.sideDartTrackedGraph keep C a b).neighborFinset d = ∅ := by
    ext x
    simp only [SimpleGraph.mem_neighborFinset, Finset.notMem_empty, iff_false]
    intro hx
    rcases hx.2.2 with ⟨rfl, htouch⟩ | ⟨_ne, hd, _⟩
    · exact htouch.elim houtside hopposite
    · exact houtside hd
  rw [hempty]
  simp

/-- The deleted-side dart opposite a retained boundary dart has the retained
dart as its unique neighbor in the side routing graph. -/
theorem sideDartTrackedGraph_neighborFinset_outsideBoundary
    (keep : V -> Prop) [DecidablePred keep]
    (C : E -> Color) (a b : Color)
    (d : BoundaryDart RS keep)
    (htracked : IsTrackedColor a b (C (RS.edgeOf d.1.1))) :
    (RS.sideDartTrackedGraph keep C a b).neighborFinset
        (RS.alpha d.1.1) = {d.1.1} := by
  classical
  ext x
  simp only [SimpleGraph.mem_neighborFinset, Finset.mem_singleton]
  constructor
  · intro hx
    rcases hx.2.2 with ⟨hxa, _hkeep⟩ | ⟨_hne, hout, _hvert⟩
    · exact hxa.trans (RS.alpha_involutive d.1.1)
    · exact False.elim (d.2 (by simpa using hout))
  · intro hx
    subst x
    refine ⟨?_, htracked, Or.inl ⟨?_, Or.inr d.1.2⟩⟩
    · simpa [RS.edge_alpha] using htracked
    · simpa using (RS.alpha_involutive d.1.1).symm

theorem sideDartTrackedGraph_degree_outsideBoundary
    (keep : V -> Prop) [DecidablePred keep]
    (C : E -> Color) (a b : Color)
    (d : BoundaryDart RS keep)
    (htracked : IsTrackedColor a b (C (RS.edgeOf d.1.1))) :
    (RS.sideDartTrackedGraph keep C a b).degree (RS.alpha d.1.1) = 1 := by
  classical
  rw [← SimpleGraph.card_neighborFinset_eq_degree,
    RS.sideDartTrackedGraph_neighborFinset_outsideBoundary
      keep C a b d htracked]
  simp

/-- With exactly two retained boundary darts, a selected deleted-side portal
is forced to connect to the other portal in the bicolored component. This is the
handshaking step in the manuscript's two-cut routing argument. -/
theorem twoBoundaryDarts_bicolored_reachable
    (keep : V -> Prop) [DecidablePred keep]
    (hCubic : RS.IsCubic)
    (C : RS.EdgeColoring Color) (hC : RS.IsTaitEdgeColoring C)
    (a b : Color) (ha : a ≠ 0) (hb : b ≠ 0) (hab : a ≠ b)
    (left right : BoundaryDart RS keep)
    (hleftTracked : IsTrackedColor a b (C (RS.edgeOf left.1.1)))
    (hcover : ∀ d : BoundaryDart RS keep, d = left ∨ d = right) :
    (RS.sideDartTrackedGraph keep C a b).Reachable
      (RS.alpha left.1.1) (RS.alpha right.1.1) := by
  classical
  apply reachable_of_odd_degree_pair
    (RS.sideDartTrackedGraph keep C a b)
  · rw [RS.sideDartTrackedGraph_degree_outsideBoundary
      keep C a b left hleftTracked]
    exact odd_one
  · intro d hdOdd
    by_cases htracked : IsTrackedColor a b (C (RS.edgeOf d))
    · by_cases hinside : keep (RS.vertOf d)
      · have hdegree := RS.sideDartTrackedGraph_degree_inside
          keep hCubic C hC a b ha hb hab d hinside htracked
        have hnotOdd : ¬ Odd
            ((RS.sideDartTrackedGraph keep C a b).degree d) := by
          rw [hdegree]
          decide
        exact False.elim (hnotOdd hdOdd)
      · by_cases hopposite : keep (RS.vertOf (RS.alpha d))
        · let boundary : BoundaryDart RS keep :=
            ⟨⟨RS.alpha d, hopposite⟩, by
              simpa [RS.alpha_involutive] using hinside⟩
          rcases hcover boundary with hleft | hright
          · left
            have h := congrArg
              (fun x : BoundaryDart RS keep => RS.alpha x.1.1) hleft
            simpa [boundary, RS.alpha_involutive] using h
          · right
            have h := congrArg
              (fun x : BoundaryDart RS keep => RS.alpha x.1.1) hright
            simpa [boundary, RS.alpha_involutive] using h
        · have hdegree := RS.sideDartTrackedGraph_degree_outside_untouched
            keep C a b d hinside hopposite
          have hnotOdd : ¬ Odd
              ((RS.sideDartTrackedGraph keep C a b).degree d) := by
            rw [hdegree]
            decide
          exact False.elim (hnotOdd hdOdd)
    · have hdegree := RS.sideDartTrackedGraph_degree_untracked
          keep C a b d htracked
      have hnotOdd : ¬ Odd
          ((RS.sideDartTrackedGraph keep C a b).degree d) := by
        rw [hdegree]
        decide
      exact False.elim (hnotOdd hdOdd)

/-- A retained boundary dart is supported on the computed edge boundary of
the retained vertex finset. -/
theorem boundaryDart_edge_mem_vertexSideEdgeBoundary
    (side : Finset V)
    (d : BoundaryDart RS (fun v => v ∈ side)) :
    RS.edgeOf d.1.1 ∈ RS.vertexSideEdgeBoundary side := by
  rw [RS.mem_vertexSideEdgeBoundary_iff]
  have hdmem : d.1.1 ∈ RS.dartsOn (RS.edgeOf d.1.1) := by simp
  rw [RS.endpoints_eq_pair_of_mem hdmem]
  have hinter :
      ({RS.vertOf d.1.1, RS.vertOf (RS.alpha d.1.1)} : Finset V) ∩ side =
        {RS.vertOf d.1.1} := by
    ext v
    simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨rfl | rfl, hv⟩
      · rfl
      · exact False.elim (d.2 hv)
    · intro hv
      subst v
      exact ⟨Or.inl rfl, d.1.2⟩
  rw [hinter]
  simp

/-- Every edge in the computed boundary has a retained orientation, obtained
from the unique endpoint lying in the side. -/
theorem exists_boundaryDart_edgeOf_of_mem_vertexSideEdgeBoundary
    (side : Finset V) {e : E}
    (he : e ∈ RS.vertexSideEdgeBoundary side) :
    ∃ d : BoundaryDart RS (fun v => v ∈ side), RS.edgeOf d.1.1 = e := by
  have hcard : (RS.endpoints e ∩ side).card = 1 :=
    RS.mem_vertexSideEdgeBoundary_iff.mp he
  rcases Finset.card_eq_one.mp hcard with ⟨v, hinter⟩
  have hvInter : v ∈ RS.endpoints e ∩ side := by rw [hinter]; simp
  have hvEndpoint : v ∈ RS.endpoints e := (Finset.mem_inter.mp hvInter).1
  have hvSide : v ∈ side := (Finset.mem_inter.mp hvInter).2
  rcases RS.mem_endpoints_iff.mp hvEndpoint with ⟨d, hdDarts, hdVert⟩
  have hdEdge : RS.edgeOf d = e := RS.mem_dartsOn.mp hdDarts
  have hAlphaOutside : RS.vertOf (RS.alpha d) ∉ side := by
    intro hAlphaSide
    have hpairSubset :
        ({RS.vertOf d, RS.vertOf (RS.alpha d)} : Finset V) ⊆
          RS.endpoints e ∩ side := by
      intro w hw
      rw [RS.endpoints_eq_pair_of_mem hdDarts]
      simp only [Finset.mem_inter, Finset.mem_insert,
        Finset.mem_singleton] at hw ⊢
      rcases hw with rfl | rfl
      · exact ⟨Or.inl rfl, by simpa [hdVert] using hvSide⟩
      · exact ⟨Or.inr rfl, hAlphaSide⟩
    have hpairCard :
        ({RS.vertOf d, RS.vertOf (RS.alpha d)} : Finset V).card = 2 :=
      Finset.card_pair (RS.no_self_loops d)
    have hle := Finset.card_le_card hpairSubset
    rw [hpairCard, hcard] at hle
    omega
  exact ⟨⟨⟨d, by simpa [hdVert] using hvSide⟩, hAlphaOutside⟩, hdEdge⟩

noncomputable def boundaryDartOfCrossingEdge
    (side : Finset V) (e : E)
    (he : e ∈ RS.vertexSideEdgeBoundary side) :
    BoundaryDart RS (fun v => v ∈ side) :=
  Classical.choose
    (RS.exists_boundaryDart_edgeOf_of_mem_vertexSideEdgeBoundary side he)

@[simp]
theorem boundaryDartOfCrossingEdge_edgeOf
    (side : Finset V) (e : E)
    (he : e ∈ RS.vertexSideEdgeBoundary side) :
    RS.edgeOf (RS.boundaryDartOfCrossingEdge side e he).1.1 = e :=
  Classical.choose_spec
    (RS.exists_boundaryDart_edgeOf_of_mem_vertexSideEdgeBoundary side he)

/-- Exact two-edge-cut routing: for every second nonzero color, the two cut
portals are connected through either chosen vertex side in the corresponding
bicolored dart graph. The cut-edge color equality and the through-route are
both derived from the computed two-edge boundary. -/
theorem twoEdgeCut_bicolored_portals_reachable
    (hCubic : RS.IsCubic)
    (C : RS.EdgeColoring Color) (hC : RS.IsTaitEdgeColoring C)
    (side : Finset V) {e f : E} (hne : e ≠ f)
    (hboundary : RS.vertexSideEdgeBoundary side = {e, f})
    (other : Color) (hother : other ≠ 0) (hneColor : C e ≠ other) :
    let he : e ∈ RS.vertexSideEdgeBoundary side := by rw [hboundary]; simp
    let hf : f ∈ RS.vertexSideEdgeBoundary side := by rw [hboundary]; simp
    let left := RS.boundaryDartOfCrossingEdge side e he
    let right := RS.boundaryDartOfCrossingEdge side f hf
    C e = C f ∧
      (RS.sideDartTrackedGraph (fun v => v ∈ side) C (C e) other).Reachable
        (RS.alpha left.1.1) (RS.alpha right.1.1) ∧
      (RS.trackedEdgeGraph C (C e) other).Reachable e f := by
  classical
  dsimp only
  let he : e ∈ RS.vertexSideEdgeBoundary side := by rw [hboundary]; simp
  let hf : f ∈ RS.vertexSideEdgeBoundary side := by rw [hboundary]; simp
  let left := RS.boundaryDartOfCrossingEdge side e he
  let right := RS.boundaryDartOfCrossingEdge side f hf
  have hcolors := RS.twoEdgeCut_colors_eq hCubic C hC side hne hboundary
  have hDart :
      (RS.sideDartTrackedGraph (fun v => v ∈ side) C (C e) other).Reachable
        (RS.alpha left.1.1) (RS.alpha right.1.1) := by
    apply RS.twoBoundaryDarts_bicolored_reachable
        (fun v => v ∈ side) hCubic C hC (C e) other
        (hC e) hother hneColor left right
    · left
      simp [left]
    · intro d
      have hdBoundary := RS.boundaryDart_edge_mem_vertexSideEdgeBoundary side d
      rw [hboundary] at hdBoundary
      simp only [Finset.mem_insert, Finset.mem_singleton] at hdBoundary
      rcases hdBoundary with hdEdge | hdEdge
      · left
        apply boundaryDart_eq_of_edgeOf_eq RS
        simpa [left] using hdEdge
      · right
        apply boundaryDart_eq_of_edgeOf_eq RS
        simpa [right] using hdEdge
  refine ⟨hcolors, hDart, ?_⟩
  have hProjected := RS.sideDartTrackedGraph_reachable_edgeOf
    (fun v => v ∈ side) C (C e) other hDart
  simpa [left, right, RS.edge_alpha] using hProjected

end RotationSystem

end

end Mettapedia.GraphTheory.FourColor
