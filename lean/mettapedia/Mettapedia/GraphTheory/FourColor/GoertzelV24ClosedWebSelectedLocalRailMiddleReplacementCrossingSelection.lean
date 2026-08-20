import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebSelectedLocalRailMiddleReplacementSeparator

/-!
# L1: provenance-aware crossing selections for replacement cycles

A replacement cycle fixes the facial-dual walk and retains a complete primal
crossing choice, including one literal source-rung anchor.  Later pointed-rail
geometry may supply two further literal crossings.  This module separates
those choices from the already-proved walk geometry: a `CrossingSelection`
chooses a shared primal edge at every step, while the anchor-plus-two
constructor retains all three source edges definitionally.

This is representation infrastructure.  It does not locate the two pointed
rail edges at square steps, classify the resulting primal cut, reroute a rail,
attach end caps, or close Fable flag L1.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebAtGoodWord

open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAnnularEmbedding.ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24FaceOrbitIncidence
open GoertzelV24SelectedDualCycleSeparator

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

attribute [-instance]
  GoertzelV24RetainedVertexRotationSplice.retainedVertexFintype
  GoertzelV24RetainedVertexRotationSplice.retainedVertexDecidableEq
  GoertzelV24SeamFaceArcPartition.hitPointFintype

namespace Instance.SelectedLocalLayerFormation.SelectedSourceLocalRailAssembly

variable
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring}

namespace MiddleReplacementShortDualCycle

variable {face : AmbientFace
  (Finset.univ : Finset (OrbitFace web.annular.RS))}

/-- A complete choice of literal primal crossing at every step of the fixed
replacement-cycle walk. -/
structure CrossingSelection
    (cycle : MiddleReplacementShortDualCycle (web := web) face) where
  crossingEdge : Fin cycle.walk.length → G.edgeSet
  crossing_mem_shared : ∀ step,
    crossingEdge step ∈ sharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS))
      (cycle.walk.getVert step.val).1
      (cycle.walk.getVert (step.val + 1)).1

/-- Package a crossing selection as the generic selected-cycle separator
input, without changing the underlying walk. -/
def CrossingSelection.toSelectedDualCycle
    {cycle : MiddleReplacementShortDualCycle (web := web) face}
    (selection : cycle.CrossingSelection) :
    SelectedDualCycle web.annular.RS cycle.start where
  walk := cycle.walk
  isCycle := cycle.isCycle
  crossingEdge := selection.crossingEdge
  crossing_mem_shared := selection.crossing_mem_shared

/-- Replace only the complete primal crossing choice of a short cycle.  Its
facial walk, simplicity, support, and anchor data are retained verbatim. -/
def CrossingSelection.reselect
    {cycle : MiddleReplacementShortDualCycle (web := web) face}
    (selection : cycle.CrossingSelection)
    (hanchor : selection.crossingEdge cycle.anchor = cycle.anchorEdge) :
    MiddleReplacementShortDualCycle (web := web) face where
  start := cycle.start
  walk := cycle.walk
  isCycle := cycle.isCycle
  length_eq_three_or_four := cycle.length_eq_three_or_four
  face_mem_support := cycle.face_mem_support
  support_internal := cycle.support_internal
  anchor := cycle.anchor
  anchorEdge := cycle.anchorEdge
  anchorEdge_mem_shared := cycle.anchorEdge_mem_shared
  crossingEdge := selection.crossingEdge
  crossing_mem_shared := selection.crossing_mem_shared
  crossingEdge_anchor := hanchor

@[simp] theorem CrossingSelection.reselect_walk
    {cycle : MiddleReplacementShortDualCycle (web := web) face}
    (selection : cycle.CrossingSelection)
    (hanchor : selection.crossingEdge cycle.anchor = cycle.anchorEdge) :
    (selection.reselect hanchor).walk = cycle.walk := rfl

@[simp] theorem CrossingSelection.reselect_crossingEdge
    {cycle : MiddleReplacementShortDualCycle (web := web) face}
    (selection : cycle.CrossingSelection)
    (hanchor : selection.crossingEdge cycle.anchor = cycle.anchorEdge)
    (step : Fin cycle.walk.length) :
    (selection.reselect hanchor).crossingEdge step = selection.crossingEdge step := rfl

/-- The original anchor-only presentation as a crossing selection. -/
noncomputable def anchoredSelection
    (cycle : MiddleReplacementShortDualCycle (web := web) face) :
    cycle.CrossingSelection where
  crossingEdge := cycle.selectedCycle.crossingEdge
  crossing_mem_shared := cycle.selectedCycle.crossing_mem_shared

@[simp] theorem anchoredSelection_crossingEdge_anchor
    (cycle : MiddleReplacementShortDualCycle (web := web) face) :
    cycle.anchoredSelection.crossingEdge cycle.anchor = cycle.anchorEdge := by
  exact cycle.selectedCycle_crossingEdge_anchor

/-- Retain the source rung and two additional literal rail crossings at three
pairwise-distinct steps of the already-proved replacement cycle. -/
noncomputable def anchorAndTwoSelection
    (cycle : MiddleReplacementShortDualCycle (web := web) face)
    (first second : Fin cycle.walk.length)
    (hfirstAnchor : first ≠ cycle.anchor)
    (hsecondAnchor : second ≠ cycle.anchor)
    (hfirstSecond : first ≠ second)
    (firstEdge secondEdge : G.edgeSet)
    (hfirstEdge : firstEdge ∈ sharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS))
      (cycle.walk.getVert first.val).1
      (cycle.walk.getVert (first.val + 1)).1)
    (hsecondEdge : secondEdge ∈ sharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS))
      (cycle.walk.getVert second.val).1
      (cycle.walk.getVert (second.val + 1)).1) :
    cycle.CrossingSelection where
  crossingEdge := fun step =>
    if step = cycle.anchor then cycle.anchorEdge
    else if step = first then firstEdge
    else if step = second then secondEdge
    else cycle.anchoredSelection.crossingEdge step
  crossing_mem_shared := by
    intro step
    by_cases hanchor : step = cycle.anchor
    · simpa [hanchor] using cycle.anchorEdge_mem_shared
    · by_cases hfirst : step = first
      · subst step
        simpa [hfirstAnchor] using hfirstEdge
      · by_cases hsecond : step = second
        · subst step
          simpa [hsecondAnchor, hfirstSecond.symm] using hsecondEdge
        · simp only [hanchor, hfirst, hsecond, ↓reduceIte]
          exact cycle.anchoredSelection.crossing_mem_shared step

@[simp] theorem anchorAndTwoSelection_crossingEdge_anchor
    (cycle : MiddleReplacementShortDualCycle (web := web) face)
    (first second : Fin cycle.walk.length)
    (hfirstAnchor : first ≠ cycle.anchor)
    (hsecondAnchor : second ≠ cycle.anchor)
    (hfirstSecond : first ≠ second)
    (firstEdge secondEdge : G.edgeSet)
    (hfirstEdge : firstEdge ∈ sharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS))
      (cycle.walk.getVert first.val).1
      (cycle.walk.getVert (first.val + 1)).1)
    (hsecondEdge : secondEdge ∈ sharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS))
      (cycle.walk.getVert second.val).1
      (cycle.walk.getVert (second.val + 1)).1) :
    (cycle.anchorAndTwoSelection first second hfirstAnchor hsecondAnchor
      hfirstSecond firstEdge secondEdge hfirstEdge hsecondEdge).crossingEdge
        cycle.anchor = cycle.anchorEdge := by
  simp [anchorAndTwoSelection]

@[simp] theorem anchorAndTwoSelection_crossingEdge_first
    (cycle : MiddleReplacementShortDualCycle (web := web) face)
    (first second : Fin cycle.walk.length)
    (hfirstAnchor : first ≠ cycle.anchor)
    (hsecondAnchor : second ≠ cycle.anchor)
    (hfirstSecond : first ≠ second)
    (firstEdge secondEdge : G.edgeSet)
    (hfirstEdge : firstEdge ∈ sharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS))
      (cycle.walk.getVert first.val).1
      (cycle.walk.getVert (first.val + 1)).1)
    (hsecondEdge : secondEdge ∈ sharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS))
      (cycle.walk.getVert second.val).1
      (cycle.walk.getVert (second.val + 1)).1) :
    (cycle.anchorAndTwoSelection first second hfirstAnchor hsecondAnchor
      hfirstSecond firstEdge secondEdge hfirstEdge hsecondEdge).crossingEdge
        first = firstEdge := by
  simp [anchorAndTwoSelection, hfirstAnchor]

@[simp] theorem anchorAndTwoSelection_crossingEdge_second
    (cycle : MiddleReplacementShortDualCycle (web := web) face)
    (first second : Fin cycle.walk.length)
    (hfirstAnchor : first ≠ cycle.anchor)
    (hsecondAnchor : second ≠ cycle.anchor)
    (hfirstSecond : first ≠ second)
    (firstEdge secondEdge : G.edgeSet)
    (hfirstEdge : firstEdge ∈ sharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS))
      (cycle.walk.getVert first.val).1
      (cycle.walk.getVert (first.val + 1)).1)
    (hsecondEdge : secondEdge ∈ sharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS))
      (cycle.walk.getVert second.val).1
      (cycle.walk.getVert (second.val + 1)).1) :
    (cycle.anchorAndTwoSelection first second hfirstAnchor hsecondAnchor
      hfirstSecond firstEdge secondEdge hfirstEdge hsecondEdge).crossingEdge
        second = secondEdge := by
  simp [anchorAndTwoSelection, hsecondAnchor, hfirstSecond.symm]

/-- Promote the anchor-plus-two receipt selection to a complete short-cycle
packet, so the existing separator/component/bond tower can be reused without
reconstructing its facial geometry. -/
noncomputable def anchorAndTwoCycle
    (cycle : MiddleReplacementShortDualCycle (web := web) face)
    (first second : Fin cycle.walk.length)
    (hfirstAnchor : first ≠ cycle.anchor)
    (hsecondAnchor : second ≠ cycle.anchor)
    (hfirstSecond : first ≠ second)
    (firstEdge secondEdge : G.edgeSet)
    (hfirstEdge : firstEdge ∈ sharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS))
      (cycle.walk.getVert first.val).1
      (cycle.walk.getVert (first.val + 1)).1)
    (hsecondEdge : secondEdge ∈ sharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS))
      (cycle.walk.getVert second.val).1
      (cycle.walk.getVert (second.val + 1)).1) :
    MiddleReplacementShortDualCycle (web := web) face :=
  let selection := cycle.anchorAndTwoSelection first second hfirstAnchor
    hsecondAnchor hfirstSecond firstEdge secondEdge hfirstEdge hsecondEdge
  selection.reselect
    (cycle.anchorAndTwoSelection_crossingEdge_anchor first second hfirstAnchor
      hsecondAnchor hfirstSecond firstEdge secondEdge hfirstEdge hsecondEdge)

@[simp] theorem anchorAndTwoCycle_crossingEdge_anchor
    (cycle : MiddleReplacementShortDualCycle (web := web) face)
    (first second : Fin cycle.walk.length)
    (hfirstAnchor : first ≠ cycle.anchor)
    (hsecondAnchor : second ≠ cycle.anchor)
    (hfirstSecond : first ≠ second)
    (firstEdge secondEdge : G.edgeSet)
    (hfirstEdge : firstEdge ∈ sharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS))
      (cycle.walk.getVert first.val).1
      (cycle.walk.getVert (first.val + 1)).1)
    (hsecondEdge : secondEdge ∈ sharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS))
      (cycle.walk.getVert second.val).1
      (cycle.walk.getVert (second.val + 1)).1) :
    (cycle.anchorAndTwoCycle first second hfirstAnchor hsecondAnchor hfirstSecond
      firstEdge secondEdge hfirstEdge hsecondEdge).crossingEdge cycle.anchor =
        cycle.anchorEdge := by
  simp [anchorAndTwoCycle]

@[simp] theorem anchorAndTwoCycle_crossingEdge_first
    (cycle : MiddleReplacementShortDualCycle (web := web) face)
    (first second : Fin cycle.walk.length)
    (hfirstAnchor : first ≠ cycle.anchor)
    (hsecondAnchor : second ≠ cycle.anchor)
    (hfirstSecond : first ≠ second)
    (firstEdge secondEdge : G.edgeSet)
    (hfirstEdge : firstEdge ∈ sharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS))
      (cycle.walk.getVert first.val).1
      (cycle.walk.getVert (first.val + 1)).1)
    (hsecondEdge : secondEdge ∈ sharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS))
      (cycle.walk.getVert second.val).1
      (cycle.walk.getVert (second.val + 1)).1) :
    (cycle.anchorAndTwoCycle first second hfirstAnchor hsecondAnchor hfirstSecond
      firstEdge secondEdge hfirstEdge hsecondEdge).crossingEdge first =
        firstEdge := by
  simp [anchorAndTwoCycle]

@[simp] theorem anchorAndTwoCycle_crossingEdge_second
    (cycle : MiddleReplacementShortDualCycle (web := web) face)
    (first second : Fin cycle.walk.length)
    (hfirstAnchor : first ≠ cycle.anchor)
    (hsecondAnchor : second ≠ cycle.anchor)
    (hfirstSecond : first ≠ second)
    (firstEdge secondEdge : G.edgeSet)
    (hfirstEdge : firstEdge ∈ sharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS))
      (cycle.walk.getVert first.val).1
      (cycle.walk.getVert (first.val + 1)).1)
    (hsecondEdge : secondEdge ∈ sharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS))
      (cycle.walk.getVert second.val).1
      (cycle.walk.getVert (second.val + 1)).1) :
    (cycle.anchorAndTwoCycle first second hfirstAnchor hsecondAnchor hfirstSecond
      firstEdge secondEdge hfirstEdge hsecondEdge).crossingEdge second =
        secondEdge := by
  simp [anchorAndTwoCycle]

end MiddleReplacementShortDualCycle

end Instance.SelectedLocalLayerFormation.SelectedSourceLocalRailAssembly

end

end GoertzelV24ClosedWebAtGoodWord

end Mettapedia.GraphTheory.FourColor
