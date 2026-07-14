import Mettapedia.GraphTheory.FourColor.Orthogonality
import Mettapedia.GraphTheory.FourColor.RotationSystem
import Mettapedia.GraphTheory.Kempe

namespace Mettapedia.GraphTheory.FourColor

open SimpleGraph
open scoped BigOperators

noncomputable section

namespace RotationSystem

variable {V E : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E]
variable (RS : RotationSystem V E)

/-- Two rotation-system edges are adjacent when they are distinct and share
an endpoint. Unlike a `SimpleGraph` edge carrier, `E` may contain parallel
edges, so this graph is the faithful edge-coloring domain for digon steps. -/
def edgeAdjacencyGraph : SimpleGraph E where
  Adj e f := e ≠ f ∧
    ∃ v : V, v ∈ RS.endpoints e ∧ v ∈ RS.endpoints f
  symm := ⟨by
    intro e f h
    rcases h with ⟨hne, v, hve, hvf⟩
    exact ⟨hne.symm, v, hvf, hve⟩
  ⟩
  loopless := ⟨by
    intro e h
    exact h.1 rfl
  ⟩

@[simp]
theorem edgeAdjacencyGraph_adj_iff {e f : E} :
    RS.edgeAdjacencyGraph.Adj e f ↔
      e ≠ f ∧ ∃ v : V, v ∈ RS.endpoints e ∧ v ∈ RS.endpoints f := by
  rfl

/-- Endpoint membership and dart-computed edge incidence are the same
rotation-system relation. -/
theorem mem_endpoints_iff_mem_incidentEdges {e : E} {v : V} :
    v ∈ RS.endpoints e ↔ e ∈ RS.incidentEdges v := by
  constructor
  · intro hv
    rcases (RS.mem_endpoints_iff).1 hv with ⟨d, hd, hdv⟩
    exact (RS.mem_incidentEdges_iff).2
      ⟨d, (RS.mem_dartsOn).1 hd, hdv⟩
  · intro he
    rcases (RS.mem_incidentEdges_iff).1 he with ⟨d, hde, hdv⟩
    exact (RS.mem_endpoints_iff).2
      ⟨d, (RS.mem_dartsOn).2 hde, hdv⟩

/-- Incident edges are the image of the darts based at the vertex. -/
theorem incidentEdges_eq_image_dartsAt (v : V) :
    RS.incidentEdges v = (RS.dartsAt v).image RS.edgeOf := by
  ext e
  constructor
  · intro he
    rcases (RS.mem_incidentEdges_iff).1 he with ⟨d, hde, hdv⟩
    exact Finset.mem_image.2 ⟨d, by simp [dartsAt, hdv], hde⟩
  · intro he
    rcases Finset.mem_image.1 he with ⟨d, hd, hde⟩
    exact (RS.mem_incidentEdges_iff).2
      ⟨d, hde, by simpa [dartsAt] using hd⟩

/-- At one vertex, two darts over the same edge coincide. The alpha-opposite
alternative is excluded by the no-self-loop field. -/
theorem edgeOf_injOn_dartsAt (v : V) :
    Set.InjOn RS.edgeOf (RS.dartsAt v : Set RS.D) := by
  intro d hd d' hd' hEdge
  have hdv : RS.vertOf d = v := by simpa [dartsAt] using hd
  have hd'v : RS.vertOf d' = v := by simpa [dartsAt] using hd'
  rcases RS.edge_fiber_two_cases (e := RS.edgeOf d) (d := d) (y := d')
      rfl hEdge.symm with hsame | hopposite
  · exact hsame.symm
  · exfalso
    apply RS.no_self_loops d
    have halpha : RS.vertOf (RS.alpha d) = v := by
      simpa [hopposite] using hd'v
    exact hdv.trans halpha.symm

/-- Dart-degree and edge-degree agree even when parallel edges are present. -/
theorem incidentEdges_card_eq_dartsAt_card (v : V) :
    (RS.incidentEdges v).card = (RS.dartsAt v).card := by
  rw [RS.incidentEdges_eq_image_dartsAt v]
  exact Finset.card_image_iff.mpr (RS.edgeOf_injOn_dartsAt v)

/-- Cubicity in dart form gives exactly three incident edges at every vertex. -/
theorem incidentEdges_card_eq_three_of_isCubic
    (hCubic : RS.IsCubic) (v : V) :
    (RS.incidentEdges v).card = 3 := by
  rw [RS.incidentEdges_card_eq_dartsAt_card]
  exact hCubic v

/-- Distinct edges incident to one rotation-system vertex are adjacent in the
edge-adjacency graph, including parallel edges. -/
theorem edgeAdjacencyGraph_adj_of_mem_incidentEdges
    {e f : E} {v : V} (hne : e ≠ f)
    (he : e ∈ RS.incidentEdges v) (hf : f ∈ RS.incidentEdges v) :
    RS.edgeAdjacencyGraph.Adj e f := by
  exact (RS.edgeAdjacencyGraph_adj_iff).2
    ⟨hne, v, (RS.mem_endpoints_iff_mem_incidentEdges).2 he,
      (RS.mem_endpoints_iff_mem_incidentEdges).2 hf⟩

/-- Proper edge colorings for a rotation system are ordinary vertex colorings
of its edge-adjacency graph. -/
abbrev EdgeColoring (α : Type*) := RS.edgeAdjacencyGraph.Coloring α

/-- A rotation-system Tait coloring uses only the three nonzero `V₄` colors. -/
def IsTaitEdgeColoring (C : RS.EdgeColoring Color) : Prop :=
  ∀ e : E, C e ≠ 0

/-- The unoriented `V₄` sum of the colors incident to a vertex. -/
def vertexColorSum (C : E → Color) (v : V) : Color :=
  ∑ e ∈ RS.incidentEdges v, C e

private theorem three_distinct_nonzero_sum_eq_zero {a b c : Color}
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    a + b + c = 0 := by
  rcases eq_red_or_eq_blue_or_eq_purple_of_ne_zero a ha with rfl | rfl | rfl <;>
    rcases eq_red_or_eq_blue_or_eq_purple_of_ne_zero b hb with rfl | rfl | rfl <;>
    rcases eq_red_or_eq_blue_or_eq_purple_of_ne_zero c hc with rfl | rfl | rfl <;>
    simp at hab hac hbc ⊢

/-- Rotation-system form of the Tait/`V₄`-flow implication. On a cubic
rotation system, every proper nonzero three-edge-coloring has zero incident
sum at each vertex. This proof does not assume absence of parallel edges. -/
theorem vertexColorSum_eq_zero_of_isCubic_of_isTaitEdgeColoring
    (hCubic : RS.IsCubic) (C : RS.EdgeColoring Color)
    (hC : RS.IsTaitEdgeColoring C) (v : V) :
    RS.vertexColorSum C v = 0 := by
  rcases Finset.card_eq_three.mp
      (RS.incidentEdges_card_eq_three_of_isCubic hCubic v) with
    ⟨e, f, g, hef, heg, hfg, hincident⟩
  have heMem : e ∈ RS.incidentEdges v := by rw [hincident]; simp
  have hfMem : f ∈ RS.incidentEdges v := by rw [hincident]; simp
  have hgMem : g ∈ RS.incidentEdges v := by rw [hincident]; simp
  have hColorEF : C e ≠ C f :=
    C.valid (RS.edgeAdjacencyGraph_adj_of_mem_incidentEdges hef heMem hfMem)
  have hColorEG : C e ≠ C g :=
    C.valid (RS.edgeAdjacencyGraph_adj_of_mem_incidentEdges heg heMem hgMem)
  have hColorFG : C f ≠ C g :=
    C.valid (RS.edgeAdjacencyGraph_adj_of_mem_incidentEdges hfg hfMem hgMem)
  have hsum := three_distinct_nonzero_sum_eq_zero
    (hC e) (hC f) (hC g) hColorEF hColorEG hColorFG
  simp [vertexColorSum, hincident, hef, heg, hfg, add_assoc] at hsum ⊢
  exact hsum

end RotationSystem

end

end Mettapedia.GraphTheory.FourColor
