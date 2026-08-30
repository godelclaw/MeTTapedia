import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairStateReversal

/-!
# Reversing an adjacent-pair Kempe closure

The canonical graph isomorphism between the two orders of an adjacent-pair
deletion transports bicoloured components, commutes with a switch on one such
component, and therefore transports every finite Kempe-move sequence.

This is an isomorphism-invariance result.  It uses no planarity, cancellation,
or wall-exclusion hypothesis.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24AdjacentPairKempeClosureReversal

open GoertzelV24AdjacentPairBoundary
open GoertzelV24AdjacentPairInsertion.AdjacentPairData
open GoertzelV24AdjacentPairReversal
open GoertzelV24AdjacentPairStateReversal
open SimpleGraph

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Reversing the ordered adjacent-pair data twice restores it. -/
@[simp] theorem reverse_reverse (data : AdjacentPairData G) :
    reverse (reverse data) = data := by
  cases data
  simp [reverse]

/-- Reversing a transported deletion colouring restores the original
colouring. -/
@[simp] theorem reverseColoring_reverseColoring
    (data : AdjacentPairData G)
    (coloring : (OriginalGraph data).EdgeColoring Color) :
    reverseColoring (reverse data) (reverseColoring data coloring) =
      coloring := by
  apply DFunLike.ext _ _
  intro edge
  change coloring _ = coloring edge
  congr 1
  apply Subtype.ext
  rcases edge with ⟨edge, hedge⟩
  induction edge using Sym2.inductionOn with
  | _ left right => rfl

/-- The same involution law, starting from the reversed presentation. -/
@[simp] theorem reverseColoring_reverseColoring_reversed
    (data : AdjacentPairData G)
    (coloring : (ReversedGraph data).EdgeColoring Color) :
    reverseColoring data (reverseColoring (reverse data) coloring) =
      coloring := by
  have h := reverseColoring_reverseColoring (reverse data) coloring
  change reverseColoring data (reverseColoring (reverse data) coloring) =
    coloring at h
  exact h

/-- The Kempe component obtained by transporting an original component across
the endpoint-order swap. -/
def reverseKempeComponent
    (data : AdjacentPairData G)
    (coloring : (OriginalGraph data).EdgeColoring Color)
    (firstColor secondColor : Color)
    (component : (coloring.bicoloredSubgraph firstColor
      secondColor).ConnectedComponent) :
    ((reverseColoring data coloring).bicoloredSubgraph firstColor
      secondColor).ConnectedComponent :=
  (bicoloredSubgraphIso data coloring firstColor secondColor).connectedComponentEquiv
    component

/-- Membership in a selected Kempe component is preserved and reflected by
the endpoint-order swap. -/
theorem mapEdgeSet_mem_reverseKempeComponent_iff
    (data : AdjacentPairData G)
    (coloring : (OriginalGraph data).EdgeColoring Color)
    (firstColor secondColor : Color)
    (component : (coloring.bicoloredSubgraph firstColor
      secondColor).ConnectedComponent)
    (edge : (OriginalGraph data).edgeSet) :
    (swapIso data).mapEdgeSet edge ∈
        (reverseColoring data coloring).kempeComponentSet
          firstColor secondColor
          (reverseKempeComponent data coloring firstColor secondColor component) ↔
      edge ∈ coloring.kempeComponentSet firstColor secondColor component := by
  let iso := bicoloredSubgraphIso data coloring firstColor secondColor
  have hselected : edge ∈ coloring.bicoloredSet firstColor secondColor ↔
      (swapIso data).mapEdgeSet edge ∈
        (reverseColoring data coloring).bicoloredSet firstColor secondColor := by
    change (coloring edge = firstColor ∨ coloring edge = secondColor) ↔
      (reverseColoring data coloring ((swapIso data).mapEdgeSet edge) = firstColor ∨
        reverseColoring data coloring ((swapIso data).mapEdgeSet edge) = secondColor)
    rw [reverseColoring_mapEdgeSet]
  constructor
  · rintro ⟨hreversedSelected, hcomponent⟩
    have horiginalSelected := hselected.mpr hreversedSelected
    refine ⟨horiginalSelected, ?_⟩
    have hmapped :
        ((reverseColoring data coloring).bicoloredSubgraph firstColor
            secondColor).connectedComponentMk
            (iso ⟨edge, horiginalSelected⟩) =
          iso.connectedComponentEquiv component := by
      have hvertex : iso ⟨edge, horiginalSelected⟩ =
          ⟨(swapIso data).mapEdgeSet edge, hreversedSelected⟩ := by
        apply Subtype.ext
        rfl
      rw [hvertex]
      simpa [iso, reverseKempeComponent] using hcomponent
    exact
      (SimpleGraph.ConnectedComponent.iso_image_comp_eq_map_iff_eq_comp
        (G := coloring.bicoloredSubgraph firstColor secondColor)
        (G' := (reverseColoring data coloring).bicoloredSubgraph
          firstColor secondColor)
        (φ := iso) (v := ⟨edge, horiginalSelected⟩)
        (C := component)).mp hmapped
  · rintro ⟨horiginalSelected, hcomponent⟩
    have hreversedSelected := hselected.mp horiginalSelected
    refine ⟨hreversedSelected, ?_⟩
    have hmapped :
        ((reverseColoring data coloring).bicoloredSubgraph firstColor
            secondColor).connectedComponentMk
            (iso ⟨edge, horiginalSelected⟩) =
          iso.connectedComponentEquiv component :=
      (SimpleGraph.ConnectedComponent.iso_image_comp_eq_map_iff_eq_comp
        (G := coloring.bicoloredSubgraph firstColor secondColor)
        (G' := (reverseColoring data coloring).bicoloredSubgraph
          firstColor secondColor)
        (φ := iso) (v := ⟨edge, horiginalSelected⟩)
        (C := component)).mpr hcomponent
    have hvertex : iso ⟨edge, horiginalSelected⟩ =
        ⟨(swapIso data).mapEdgeSet edge, hreversedSelected⟩ := by
      apply Subtype.ext
      rfl
    rw [hvertex] at hmapped
    simpa [iso, reverseKempeComponent] using hmapped

/-- Reversing a colouring commutes with switching the transported Kempe
component. -/
theorem reverseColoring_swapOnKempeComponent
    (data : AdjacentPairData G)
    (coloring : (OriginalGraph data).EdgeColoring Color)
    (firstColor secondColor : Color)
    (component : (coloring.bicoloredSubgraph firstColor
      secondColor).ConnectedComponent) :
    reverseColoring data
        (coloring.swapOnKempeComponent firstColor secondColor component) =
      (reverseColoring data coloring).swapOnKempeComponent
        firstColor secondColor
        (reverseKempeComponent data coloring firstColor secondColor component) := by
  apply DFunLike.ext _ _
  intro reversedEdge
  let edge := (swapIso data).mapEdgeSet.symm reversedEdge
  have hreversedEdge : (swapIso data).mapEdgeSet edge = reversedEdge :=
    (swapIso data).mapEdgeSet.apply_symm_apply reversedEdge
  rw [← hreversedEdge, reverseColoring_mapEdgeSet]
  by_cases hmember :
      edge ∈ coloring.kempeComponentSet firstColor secondColor component
  · have hreversedMember :=
      (mapEdgeSet_mem_reverseKempeComponent_iff data coloring
        firstColor secondColor component edge).2 hmember
    rw [coloring.swapOnKempeComponent_apply_of_mem hmember,
      (reverseColoring data coloring).swapOnKempeComponent_apply_of_mem
        hreversedMember, reverseColoring_mapEdgeSet]
  · have hreversedMember : (swapIso data).mapEdgeSet edge ∉
        (reverseColoring data coloring).kempeComponentSet
          firstColor secondColor
          (reverseKempeComponent data coloring firstColor secondColor component) :=
      fun h => hmember ((mapEdgeSet_mem_reverseKempeComponent_iff data coloring
        firstColor secondColor component edge).1 h)
    rw [coloring.swapOnKempeComponent_apply_of_not_mem hmember,
      (reverseColoring data coloring).swapOnKempeComponent_apply_of_not_mem
        hreversedMember, reverseColoring_mapEdgeSet]

/-- One Kempe move transports across endpoint-order reversal. -/
theorem edgeKempeStep_reverseColoring
    (data : AdjacentPairData G)
    {source target : (OriginalGraph data).EdgeColoring Color}
    (hstep : (OriginalGraph data).EdgeKempeStep source target) :
    (ReversedGraph data).EdgeKempeStep
      (reverseColoring data source) (reverseColoring data target) := by
  rcases hstep with ⟨firstColor, secondColor, component, rfl⟩
  exact ⟨firstColor, secondColor,
    reverseKempeComponent data source firstColor secondColor component,
    reverseColoring_swapOnKempeComponent
      data source firstColor secondColor component⟩

/-- Every finite Kempe-move sequence transports across endpoint-order
reversal. -/
theorem mem_edgeKempeClosure_reverseColoring
    (data : AdjacentPairData G)
    {base coloring : (OriginalGraph data).EdgeColoring Color}
    (hclosure : coloring ∈ (OriginalGraph data).EdgeKempeClosure base) :
    reverseColoring data coloring ∈
      (ReversedGraph data).EdgeKempeClosure (reverseColoring data base) := by
  induction hclosure with
  | refl => exact SimpleGraph.mem_edgeKempeClosure_self _
  | tail hpath hstep ih =>
      exact SimpleGraph.mem_edgeKempeClosure_of_step ih
        (edgeKempeStep_reverseColoring data hstep)

/-- Endpoint-order reversal identifies the two Kempe closures exactly. -/
theorem mem_edgeKempeClosure_reverseColoring_iff
    (data : AdjacentPairData G)
    {base coloring : (OriginalGraph data).EdgeColoring Color} :
    reverseColoring data coloring ∈
        (ReversedGraph data).EdgeKempeClosure (reverseColoring data base) ↔
      coloring ∈ (OriginalGraph data).EdgeKempeClosure base := by
  constructor
  · intro hclosure
    have hback := mem_edgeKempeClosure_reverseColoring
      (data := reverse data) hclosure
    change reverseColoring (reverse data) (reverseColoring data coloring) ∈
      (OriginalGraph data).EdgeKempeClosure
        (reverseColoring (reverse data) (reverseColoring data base)) at hback
    simpa using hback
  · exact mem_edgeKempeClosure_reverseColoring data

end

end GoertzelV24AdjacentPairKempeClosureReversal

end Mettapedia.GraphTheory.FourColor
