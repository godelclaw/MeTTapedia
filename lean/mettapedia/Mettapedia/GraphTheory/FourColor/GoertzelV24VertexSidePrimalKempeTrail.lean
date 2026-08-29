import Mettapedia.GraphTheory.FourColor.GoertzelV24PortTanglePrimalKempeGraph
import Mettapedia.GraphTheory.FourColor.GoertzelV24VertexSideOpenTangle

/-!
# Physical Kempe trails in a literal vertex shore

This file restores the graph backing forgotten by the colouring-only
`PortTangle` reduct.  For a literal vertex side of a graph-backed rotation
system, every edge of the primal Kempe graph is an actual internal ambient
edge.  Hence its simple paths map injectively to ambient primal trails.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24VertexSidePrimalKempeTrail

open SimpleGraph
open SimpleGraphDartRotation
open GoertzelV24HexagonPairingTargetAwareBoundary
open GoertzelV24OpenTangleComposition
open GoertzelV24OpenTangleComposition.OpenTangleData
open GoertzelV24PortTangleCommonKempeWeb
open GoertzelV24PortTangleGluing
open GoertzelV24PortTangleGluing.PortTangle
open GoertzelV24PortTanglePrimalKempeGraph
open GoertzelV24RotationCutDartDecomposition

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance graphEdgeSetDecidableEq : DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

/-- The colouring-only reduct of one literal vertex shore. -/
abbrev vertexSidePortTangle
    (graphData : Data G) (keep : V → Prop)
    (outer : RetainedDart graphData.toRotationSystem keep) :=
  ofOpenTangleData
    (ofVertexSide graphData.toRotationSystem keep outer)

/-- The selected primal Kempe graph of one literal vertex shore. -/
abbrev vertexSidePrimalKempeGraph
    (graphData : Data G) (keep : V → Prop)
    (outer : RetainedDart graphData.toRotationSystem keep)
    (coloring : Coloring (vertexSidePortTangle graphData keep outer))
    (pair : TaitColorPair) :=
  primalKempeGraph (vertexSidePortTangle graphData keep outer) coloring pair

/-- Inclusion of the selected primal Kempe graph into the literal induced
shore graph. -/
def primalKempeToSide
    (graphData : Data G) (keep : V → Prop)
    (outer : RetainedDart graphData.toRotationSystem keep)
    (coloring : Coloring (vertexSidePortTangle graphData keep outer))
    (pair : TaitColorPair) :
    vertexSidePrimalKempeGraph graphData keep outer coloring pair →g
      G.induce {vertex | keep vertex} where
  toFun := id
  map_rel' := by
    rintro first second ⟨dart, _hactive, hforward | hreverse⟩
    · have hfirst := congrArg Subtype.val hforward.1
      have hsecond := congrArg Subtype.val hforward.2
      change G.Adj first.1 second.1
      rw [← hfirst, ← hsecond]
      exact dart.1.1.adj
    · have hfirst := congrArg Subtype.val hreverse.2
      have hsecond := congrArg Subtype.val hreverse.1
      change G.Adj first.1 second.1
      rw [← hfirst, ← hsecond]
      exact dart.1.1.adj.symm

/-- Regard a selected primal Kempe walk as a walk in the induced shore. -/
def primalKempeWalkToSide
    (graphData : Data G) (keep : V → Prop)
    (outer : RetainedDart graphData.toRotationSystem keep)
    (coloring : Coloring (vertexSidePortTangle graphData keep outer))
    (pair : TaitColorPair) {first second : {vertex : V // keep vertex}}
    (walk : (vertexSidePrimalKempeGraph graphData keep outer coloring pair).Walk
      first second) :
    (G.induce {vertex | keep vertex}).Walk first second :=
  (walk.map (primalKempeToSide graphData keep outer coloring pair)).copy rfl rfl

/-- The induced-shore image of a primal Kempe path is a path. -/
theorem primalKempeWalkToSide_isPath
    (graphData : Data G) (keep : V → Prop)
    (outer : RetainedDart graphData.toRotationSystem keep)
    (coloring : Coloring (vertexSidePortTangle graphData keep outer))
    (pair : TaitColorPair) {first second : {vertex : V // keep vertex}}
    {walk : (vertexSidePrimalKempeGraph graphData keep outer coloring pair).Walk
      first second} (hwalk : walk.IsPath) :
    (primalKempeWalkToSide graphData keep outer coloring pair walk).IsPath := by
  simpa [primalKempeWalkToSide] using
    Walk.map_isPath_of_injective (fun _ _ heq ↦ heq) hwalk

/-- Edge-disjoint primal Kempe walks remain edge-disjoint in the induced
shore graph. -/
theorem primalKempeWalkToSide_edges_disjoint
    (graphData : Data G) (keep : V → Prop)
    (outer : RetainedDart graphData.toRotationSystem keep)
    (coloring : Coloring (vertexSidePortTangle graphData keep outer))
    (pair : TaitColorPair)
    {firstLeft firstRight secondLeft secondRight :
      {vertex : V // keep vertex}}
    (first : (vertexSidePrimalKempeGraph
      graphData keep outer coloring pair).Walk firstLeft firstRight)
    (second : (vertexSidePrimalKempeGraph
      graphData keep outer coloring pair).Walk secondLeft secondRight)
    (hdisjoint : first.edges.Disjoint second.edges) :
    (primalKempeWalkToSide graphData keep outer coloring pair first).edges.Disjoint
      (primalKempeWalkToSide graphData keep outer coloring pair second).edges := by
  simp only [primalKempeWalkToSide, Walk.edges_copy, Walk.edges_map]
  exact hdisjoint.map (Sym2.map.injective (fun _ _ heq ↦ heq))

/-- Inclusion of the physical primal Kempe graph into the ambient graph. -/
def primalKempeToAmbient
    (graphData : Data G) (keep : V → Prop)
    (outer : RetainedDart graphData.toRotationSystem keep)
    (coloring : Coloring (vertexSidePortTangle graphData keep outer))
    (pair : TaitColorPair) :
    vertexSidePrimalKempeGraph graphData keep outer coloring pair →g G where
  toFun := Subtype.val
  map_rel' := by
    rintro first second ⟨dart, _hactive, hforward | hreverse⟩
    · have hfirst := congrArg Subtype.val hforward.1
      have hsecond := congrArg Subtype.val hforward.2
      change G.Adj first.1 second.1
      rw [← hfirst, ← hsecond]
      exact dart.1.1.adj
    · have hfirst := congrArg Subtype.val hreverse.2
      have hsecond := congrArg Subtype.val hreverse.1
      change G.Adj first.1 second.1
      rw [← hfirst, ← hsecond]
      exact dart.1.1.adj.symm

/-- Map one primal Kempe walk in the literal shore to the ambient graph. -/
def primalKempeWalkToAmbient
    (graphData : Data G) (keep : V → Prop)
    (outer : RetainedDart graphData.toRotationSystem keep)
    (coloring : Coloring (vertexSidePortTangle graphData keep outer))
    (pair : TaitColorPair) {first second : {vertex : V // keep vertex}}
    (walk : (vertexSidePrimalKempeGraph graphData keep outer coloring pair).Walk
      first second) : G.Walk first.1 second.1 :=
  (walk.map (primalKempeToAmbient graphData keep outer coloring pair)).copy rfl rfl

/-- Injective vertex inclusion preserves pathhood. -/
theorem primalKempeWalkToAmbient_isPath
    (graphData : Data G) (keep : V → Prop)
    (outer : RetainedDart graphData.toRotationSystem keep)
    (coloring : Coloring (vertexSidePortTangle graphData keep outer))
    (pair : TaitColorPair) {first second : {vertex : V // keep vertex}}
    {walk : (vertexSidePrimalKempeGraph graphData keep outer coloring pair).Walk
      first second} (hwalk : walk.IsPath) :
    (primalKempeWalkToAmbient graphData keep outer coloring pair walk).IsPath := by
  simpa [primalKempeWalkToAmbient] using
    Walk.map_isPath_of_injective Subtype.val_injective hwalk

/-- Injective vertex inclusion preserves trailhood. -/
theorem primalKempeWalkToAmbient_isTrail
    (graphData : Data G) (keep : V → Prop)
    (outer : RetainedDart graphData.toRotationSystem keep)
    (coloring : Coloring (vertexSidePortTangle graphData keep outer))
    (pair : TaitColorPair) {first second : {vertex : V // keep vertex}}
    {walk : (vertexSidePrimalKempeGraph graphData keep outer coloring pair).Walk
      first second} (hwalk : walk.IsTrail) :
    (primalKempeWalkToAmbient graphData keep outer coloring pair walk).IsTrail := by
  simpa [primalKempeWalkToAmbient] using
    Walk.map_isTrail_of_injective Subtype.val_injective hwalk

/-- Edge-disjoint primal Kempe walks remain edge-disjoint in the ambient
graph because the retained-vertex inclusion is injective. -/
theorem primalKempeWalkToAmbient_edges_disjoint
    (graphData : Data G) (keep : V → Prop)
    (outer : RetainedDart graphData.toRotationSystem keep)
    (coloring : Coloring (vertexSidePortTangle graphData keep outer))
    (pair : TaitColorPair)
    {firstLeft firstRight secondLeft secondRight :
      {vertex : V // keep vertex}}
    (first : (vertexSidePrimalKempeGraph
      graphData keep outer coloring pair).Walk firstLeft firstRight)
    (second : (vertexSidePrimalKempeGraph
      graphData keep outer coloring pair).Walk secondLeft secondRight)
    (hdisjoint : first.edges.Disjoint second.edges) :
    (primalKempeWalkToAmbient graphData keep outer coloring pair first).edges.Disjoint
      (primalKempeWalkToAmbient graphData keep outer coloring pair second).edges := by
  simp only [primalKempeWalkToAmbient, Walk.edges_copy, Walk.edges_map]
  exact hdisjoint.map (Sym2.map.injective Subtype.val_injective)

end

end GoertzelV24VertexSidePrimalKempeTrail

end Mettapedia.GraphTheory.FourColor
