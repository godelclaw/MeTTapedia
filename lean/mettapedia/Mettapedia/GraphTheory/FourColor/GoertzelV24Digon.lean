import Mettapedia.GraphTheory.FourColor.GoertzelDefinition48
import Mettapedia.GraphTheory.FourColor.RotationSystemEdgeColoring

namespace Mettapedia.GraphTheory.FourColor

open SimpleGraph

noncomputable section

namespace RotationSystem

variable {V E : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E]
variable (RS : RotationSystem V E)

/-- Two distinct rotation-system edges are parallel when their computed
endpoint sets agree. This is expressible on the bare rotation system even
though `SimpleGraph` and `PlanarGeometry` exclude it. -/
def AreParallelEdges (e f : E) : Prop :=
  e ≠ f ∧ RS.endpoints e = RS.endpoints f

/-- Distinct parallel edges are adjacent in the rotation-system edge graph. -/
theorem edgeAdjacencyGraph_adj_of_areParallelEdges
    {e f : E} (hparallel : RS.AreParallelEdges e f) :
    RS.edgeAdjacencyGraph.Adj e f := by
  have hnonempty : (RS.endpoints e).Nonempty := by
    rw [← Finset.card_pos, RS.endpoints_card_two]
    decide
  rcases hnonempty with ⟨v, hv⟩
  exact (RS.edgeAdjacencyGraph_adj_iff).2
    ⟨hparallel.1, v, hv, by simpa [hparallel.2] using hv⟩

/-- In the two-color subgraph selected by a digon's edge colors, the only
neighbor of the first parallel edge is the second. -/
theorem bicolored_adjacent_to_digon_left_eq_right
    {e f : E} (hparallel : RS.AreParallelEdges e f)
    (C : RS.EdgeColoring Color)
    (x : C.bicoloredSet (C e) (C f))
    (hx : RS.edgeAdjacencyGraph.Adj e x.val) :
    x.val = f := by
  have hxColor : C x.val = C f := by
    rcases x.property with hxe | hxf
    · exact False.elim ((C.valid hx) hxe.symm)
    · exact hxf
  rcases (RS.edgeAdjacencyGraph_adj_iff).1 hx with
    ⟨_hex, v, hve, hvx⟩
  by_contra hxf
  have hvf : v ∈ RS.endpoints f := by
    simpa [← hparallel.2] using hve
  have hAdjXF : RS.edgeAdjacencyGraph.Adj x.val f :=
    (RS.edgeAdjacencyGraph_adj_iff).2 ⟨hxf, v, hvx, hvf⟩
  exact (C.valid hAdjXF) hxColor

/-- Symmetrically, the only selected-color neighbor of the second digon edge
is the first. -/
theorem bicolored_adjacent_to_digon_right_eq_left
    {e f : E} (hparallel : RS.AreParallelEdges e f)
    (C : RS.EdgeColoring Color)
    (x : C.bicoloredSet (C e) (C f))
    (hx : RS.edgeAdjacencyGraph.Adj f x.val) :
    x.val = e := by
  have hxColor : C x.val = C e := by
    rcases x.property with hxe | hxf
    · exact hxe
    · exact False.elim ((C.valid hx) hxf.symm)
  rcases (RS.edgeAdjacencyGraph_adj_iff).1 hx with
    ⟨_hfx, v, hvf, hvx⟩
  by_contra hxe
  have hve : v ∈ RS.endpoints e := by
    simpa [hparallel.2] using hvf
  have hAdjXE : RS.edgeAdjacencyGraph.Adj x.val e :=
    (RS.edgeAdjacencyGraph_adj_iff).2 ⟨hxe, v, hvx, hve⟩
  exact (C.valid hAdjXE) hxColor

/-- The digon's two edges form one isolated two-vertex Kempe component for
their two colors. This is the structural content behind digon suppression's
two internal coloring states. -/
theorem digon_kempeComponentSet_eq_pair
    {e f : E} (hparallel : RS.AreParallelEdges e f)
    (C : RS.EdgeColoring Color) :
    C.kempeComponentSet (C e) (C f)
        ((C.bicoloredSubgraph (C e) (C f)).connectedComponentMk
          ⟨e, Or.inl rfl⟩) =
      ({e, f} : Set E) := by
  let H := C.bicoloredSubgraph (C e) (C f)
  let eH : C.bicoloredSet (C e) (C f) := ⟨e, Or.inl rfl⟩
  have hefRaw := RS.edgeAdjacencyGraph_adj_of_areParallelEdges hparallel
  have hef : H.Adj eH ⟨f, Or.inr rfl⟩ := hefRaw
  ext x
  constructor
  · rintro ⟨hxBi, hxComponent⟩
    let xH : C.bicoloredSet (C e) (C f) := ⟨x, hxBi⟩
    have hreach : H.Reachable xH eH :=
      ConnectedComponent.exact hxComponent
    have hrt : Relation.ReflTransGen H.Adj xH eH :=
      (SimpleGraph.reachable_iff_reflTransGen xH eH).1 hreach
    have hxPair : xH.val = e ∨ xH.val = f := by
      refine Relation.ReflTransGen.head_induction_on
        (motive := fun a _ => a.val = e ∨ a.val = f)
        hrt (Or.inl rfl) ?_
      intro a c hac _ ih
      rcases ih with hc | hc
      · have hacRaw : RS.edgeAdjacencyGraph.Adj a.val c.val := hac
        have hea : RS.edgeAdjacencyGraph.Adj e a.val := by
          rw [hc] at hacRaw
          exact hacRaw.symm
        exact Or.inr
          (RS.bicolored_adjacent_to_digon_left_eq_right
            hparallel C a hea)
      · have hacRaw : RS.edgeAdjacencyGraph.Adj a.val c.val := hac
        have hfa : RS.edgeAdjacencyGraph.Adj f a.val := by
          rw [hc] at hacRaw
          exact hacRaw.symm
        exact Or.inl
          (RS.bicolored_adjacent_to_digon_right_eq_left
            hparallel C a hfa)
    simpa [xH] using hxPair
  · intro hx
    rcases hx with hxe | hxf
    · subst x
      exact C.mem_kempeComponentSet_self (Or.inl rfl)
    · subst x
      refine ⟨Or.inr rfl, ?_⟩
      exact (ConnectedComponent.connectedComponentMk_eq_of_adj hef).symm

/-- A Tait coloring assigns a valid pair of distinct nonzero colors to the
two parallel edges of a digon. -/
theorem validColorPair_of_areParallelEdges
    {e f : E} (hparallel : RS.AreParallelEdges e f)
    (C : RS.EdgeColoring Color) (hC : RS.IsTaitEdgeColoring C) :
    ValidColorPair (C e) (C f) := by
  exact ⟨hC e, hC f,
    C.valid (RS.edgeAdjacencyGraph_adj_of_areParallelEdges hparallel)⟩

/-- Exact digon switch formula: the Kempe move on the isolated component
exchanges the two parallel-edge colors and fixes every other edge. -/
theorem digon_swapOnKempeComponent_apply
    {e f : E} (hparallel : RS.AreParallelEdges e f)
    (C : RS.EdgeColoring Color) (x : E) :
    C.swapOnKempeComponent (C e) (C f)
        ((C.bicoloredSubgraph (C e) (C f)).connectedComponentMk
          ⟨e, Or.inl rfl⟩) x =
      if x = e then C f else if x = f then C e else C x := by
  have hcomponent := RS.digon_kempeComponentSet_eq_pair hparallel C
  by_cases hxe : x = e
  · subst x
    rw [C.swapOnKempeComponent_apply_of_mem]
    · simp
    · rw [hcomponent]
      simp
  · by_cases hxf : x = f
    · subst x
      rw [C.swapOnKempeComponent_apply_of_mem]
      · simp [hxe]
      · rw [hcomponent]
        simp
    · rw [C.swapOnKempeComponent_apply_of_not_mem]
      · simp [hxe, hxf]
      · rw [hcomponent]
        simp [hxe, hxf]

/-- The digon switch connects two proper internal Tait states: nonzero colors
remain nonzero while the parallel-edge colors are exchanged. -/
theorem digon_swap_preserves_isTaitEdgeColoring
    {e f : E} (hparallel : RS.AreParallelEdges e f)
    (C : RS.EdgeColoring Color) (hC : RS.IsTaitEdgeColoring C) :
    RS.IsTaitEdgeColoring
      (C.swapOnKempeComponent (C e) (C f)
        ((C.bicoloredSubgraph (C e) (C f)).connectedComponentMk
          ⟨e, Or.inl rfl⟩)) := by
  intro x
  rw [RS.digon_swapOnKempeComponent_apply hparallel C x]
  by_cases hxe : x = e
  · simp [hxe, hC f]
  · by_cases hxf : x = f
    · subst x
      simp [hxe, hC e]
    · simp [hxe, hxf, hC x]

/-- Digon rung, assembled: the two parallel edges are exactly one Kempe
component, switching it is a real Kempe step, and the pointwise result is the
other internal coloring with all exterior edges fixed. -/
theorem digon_internalColorings_connected
    {e f : E} (hparallel : RS.AreParallelEdges e f)
    (C : RS.EdgeColoring Color) :
    RS.edgeAdjacencyGraph.KempeStep C
        (C.swapOnKempeComponent (C e) (C f)
          ((C.bicoloredSubgraph (C e) (C f)).connectedComponentMk
            ⟨e, Or.inl rfl⟩)) ∧
      C.kempeComponentSet (C e) (C f)
          ((C.bicoloredSubgraph (C e) (C f)).connectedComponentMk
            ⟨e, Or.inl rfl⟩) = ({e, f} : Set E) ∧
      ∀ x : E,
        C.swapOnKempeComponent (C e) (C f)
            ((C.bicoloredSubgraph (C e) (C f)).connectedComponentMk
              ⟨e, Or.inl rfl⟩) x =
          if x = e then C f else if x = f then C e else C x := by
  exact ⟨RS.edgeAdjacencyGraph.kempeStep_swapOnKempeComponent
      C (C e) (C f) _,
    RS.digon_kempeComponentSet_eq_pair hparallel C,
    RS.digon_swapOnKempeComponent_apply hparallel C⟩

end RotationSystem

end

end Mettapedia.GraphTheory.FourColor
