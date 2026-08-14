import Mettapedia.GraphTheory.FourColor.GoertzelV24PentagonCapCyclicCutPullback
import Mettapedia.GraphTheory.FourColor.GoertzelV24TwoPentagonCapOpening

/-!
# L1: one-sided cyclic-cut pullback for the two-cap laboratory

The simultaneous two-cap opening is a useful closed-carrier laboratory: it
deletes exactly the ten cycle edges of two separated facial pentagons.  If a
chosen cut side avoids all ten cap vertices, none of those restored edges
crosses the cut.  A cycle on the chosen side of the opened graph and either
restored facial pentagon on the complementary side therefore give a literal
small cyclic cut of the closed ambient graph.

This closes the cyclic branch for the two-cap laboratory without asserting
cyclic connectivity of the stub-bearing opened carrier.  It is **not** the
Addendum-V source construction: the source opens one interior cap of a
frontier tangle whose outer stubs are already present.  A separate
source-formation comparison is still required before this laboratory theorem
can be used at the live rail-append site.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24FacialPentagonCapPairCyclicCutPullback

open GoertzelV24DeleteEdgesCyclicCutPullback
open GoertzelV24FacialPentagonCap
open GoertzelV24FacialPentagonCapSideCycle
open GoertzelV24FiniteDeletionCyclicCut
open GoertzelV24PentagonCapCyclicCutPullback
open GoertzelV24TwoPentagonCapOpening
open SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]
  {data : SimpleGraphDartRotation.Data G}

noncomputable section

namespace PentagonCapPair

omit [DecidableRel G.Adj] in
/-- If a chosen side avoids both cap vertex sets, no edge restored by the
simultaneous opening crosses that side. -/
theorem cycleValueSet_noncrossing_of_vertices_outside_side
    (caps : PentagonCapPair G) (side : V → Prop)
    (hinnerOutside : ∀ step : Fin 5, ¬ side (caps.inner.vertex step))
    (houterOutside : ∀ step : Fin 5, ¬ side (caps.outer.vertex step)) :
    ∀ edge : G.edgeSet,
      edge.1 ∈ edgeFinsetValueSet caps.cycleSupport →
        ¬ EdgeCrossesVertexSide G side edge := by
  intro edge hremoved
  rcases (mem_edgeFinsetValueSet_iff caps.cycleSupport edge.1).1 hremoved with
    ⟨storedEdge, hstored, hstoredValue⟩
  change storedEdge ∈ caps.inner.cycleSupport ∪ caps.outer.cycleSupport at hstored
  rcases Finset.mem_union.mp hstored with hinner | houter
  · apply PentagonCap.cycleValueSet_noncrossing_of_vertices_outside_side
      caps.inner side hinnerOutside edge
    exact (mem_edgeFinsetValueSet_iff caps.inner.cycleSupport edge.1).2
      ⟨storedEdge, hinner, hstoredValue⟩
  · apply PentagonCap.cycleValueSet_noncrossing_of_vertices_outside_side
      caps.outer side houterOutside edge
    exact (mem_edgeFinsetValueSet_iff caps.outer.cycleSupport edge.1).2
      ⟨storedEdge, houter, hstoredValue⟩

end PentagonCapPair

namespace OrientedFacialPentagonCapPair

/-- Pull a one-sided cyclic cut from the simultaneous two-cap opening back to
the closed laboratory carrier.  The inner restored facial pentagon supplies
the complementary ambient cycle. -/
def pullbackOpenGraphOneSided_of_vertices_outside
    (caps : OrientedFacialPentagonCapPair data)
    (edgeCut : Finset
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.edgeSet)
    (side : V → Prop)
    (hcut_eq : ∀ edge :
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.edgeSet,
      edge ∈ edgeCut ↔
        EdgeCrossesVertexSide
          caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph side edge)
    (hcard_le_four : edgeCut.card ≤ 4)
    (hinside_cycle : HasCycleOnSide
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph side)
    (hinnerOutside : ∀ step : Fin 5,
      ¬ side (caps.toFacialPentagonCapPair.toPentagonCapPair.inner.vertex step))
    (houterOutside : ∀ step : Fin 5,
      ¬ side (caps.toFacialPentagonCapPair.toPentagonCapPair.outer.vertex step)) :
    SmallCyclicEdgeCut G :=
  pullbackDeleteEdgesOfAmbientOutsideCycle
    (edgeFinsetValueSet
      caps.toFacialPentagonCapPair.toPentagonCapPair.cycleSupport)
    edgeCut side hcut_eq hcard_le_four hinside_cycle
    (GoertzelV24FacialPentagonCapSideCycle.OrientedFacialPentagonCap.hasCycleOnSide_of_vertices
      caps.innerOriented (fun vertex => ¬ side vertex) hinnerOutside)
    (PentagonCapPair.cycleValueSet_noncrossing_of_vertices_outside_side
      caps.toFacialPentagonCapPair.toPentagonCapPair side
      hinnerOutside houterOutside)

@[simp]
theorem pullbackOpenGraphOneSided_of_vertices_outside_card
    (caps : OrientedFacialPentagonCapPair data)
    (edgeCut : Finset
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.edgeSet)
    (side : V → Prop)
    (hcut_eq : ∀ edge :
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.edgeSet,
      edge ∈ edgeCut ↔
        EdgeCrossesVertexSide
          caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph side edge)
    (hcard_le_four : edgeCut.card ≤ 4)
    (hinside_cycle : HasCycleOnSide
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph side)
    (hinnerOutside : ∀ step : Fin 5,
      ¬ side (caps.toFacialPentagonCapPair.toPentagonCapPair.inner.vertex step))
    (houterOutside : ∀ step : Fin 5,
      ¬ side (caps.toFacialPentagonCapPair.toPentagonCapPair.outer.vertex step)) :
    (pullbackOpenGraphOneSided_of_vertices_outside caps edgeCut side hcut_eq
      hcard_le_four hinside_cycle hinnerOutside houterOutside).edgeCut.card =
        edgeCut.card := by
  exact pullbackDeleteEdgesOfAmbientOutsideCycle_edgeCut_card
    (edgeFinsetValueSet
      caps.toFacialPentagonCapPair.toPentagonCapPair.cycleSupport)
    edgeCut side hcut_eq hcard_le_four hinside_cycle
    (GoertzelV24FacialPentagonCapSideCycle.OrientedFacialPentagonCap.hasCycleOnSide_of_vertices
      caps.innerOriented (fun vertex => ¬ side vertex) hinnerOutside)
    (PentagonCapPair.cycleValueSet_noncrossing_of_vertices_outside_side
      caps.toFacialPentagonCapPair.toPentagonCapPair side
      hinnerOutside houterOutside)

end OrientedFacialPentagonCapPair

end

end GoertzelV24FacialPentagonCapPairCyclicCutPullback

end Mettapedia.GraphTheory.FourColor
