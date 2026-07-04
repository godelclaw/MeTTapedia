import Mettapedia.GraphTheory.FourColor.GoertzelLemma818ClosedCollarWinding

namespace Mettapedia.GraphTheory.FourColor

/-!
# Closed-collar winding witness realization interface

This module pins the first geometric obstruction found by the direct
realization audit for the `tau,tau::rrbb` winding-freedom witness.  The
witness remains a valid closed-collar winding-freedom witness, but the direct
closed-collar graph has parallel endpoint edges, so it cannot already be the
simple endpoint model required by the normal-form route.
-/

namespace GoertzelLemma818ClosedCollarWindingRealization

open GoertzelLemma814
open GoertzelLemma818ClosedCollarBridgeTarget
open GoertzelLemma818ClosedCollarWinding

def closedCollarEdgesHaveSameUnorderedEndpoints
    (orients : List TauOrient) (e f : ChainEdge) : Bool :=
  let ep := closedCollarEdgeEndpoints orients e
  let fp := closedCollarEdgeEndpoints orients f
  ((ep.1 == fp.1) && (ep.2 == fp.2)) ||
    ((ep.1 == fp.2) && (ep.2 == fp.1))

def closedCollarHasParallelEndpointEdges (orients : List TauOrient) : Prop :=
  ∃ e f,
    e ∈ closedCollarEdges orients ∧
      f ∈ closedCollarEdges orients ∧
      e ≠ f ∧
      closedCollarEdgesHaveSameUnorderedEndpoints orients e f = true

def closedCollarSimpleEndpointRealization (orients : List TauOrient) : Prop :=
  ¬ closedCollarHasParallelEndpointEdges orients

def windingFreedomParallelEdgeA : ChainEdge :=
  { occ := 0, edge := TauEdge.B5 }

def windingFreedomParallelEdgeB : ChainEdge :=
  { occ := 0, edge := TauEdge.B6 }

theorem windingFreedomParallelEdgeA_mem :
    windingFreedomParallelEdgeA ∈ closedCollarEdges windingFreedomWord := by
  decide

theorem windingFreedomParallelEdgeB_mem :
    windingFreedomParallelEdgeB ∈ closedCollarEdges windingFreedomWord := by
  decide

theorem windingFreedomParallelEdges_distinct :
    windingFreedomParallelEdgeA ≠ windingFreedomParallelEdgeB := by
  decide

theorem windingFreedomParallelEdges_same_endpoints :
    closedCollarEdgesHaveSameUnorderedEndpoints windingFreedomWord
      windingFreedomParallelEdgeA windingFreedomParallelEdgeB = true := by
  decide

theorem windingFreedomWord_hasParallelEndpointEdges :
    closedCollarHasParallelEndpointEdges windingFreedomWord := by
  exact
    ⟨windingFreedomParallelEdgeA, windingFreedomParallelEdgeB,
      windingFreedomParallelEdgeA_mem, windingFreedomParallelEdgeB_mem,
      windingFreedomParallelEdges_distinct,
      windingFreedomParallelEdges_same_endpoints⟩

theorem windingFreedomWord_not_simpleEndpointRealization :
    ¬ closedCollarSimpleEndpointRealization windingFreedomWord := by
  intro hsimple
  exact hsimple windingFreedomWord_hasParallelEndpointEdges

def ClosedCollarWindingFreedomWitnessRealizationData : Prop :=
  windingFreedomWord ∈ closedCollarL1Words ∧
    windingFreedomKey ∈ colorAssignments4 ∧
    windingFreedomStateNoWinding ∈
      closedCollarFiber windingFreedomWord windingFreedomKey ∧
    windingFreedomStateWithWinding ∈
      closedCollarFiber windingFreedomWord windingFreedomKey ∧
    closedCollarAggregateCutParityProfile windingFreedomWord
        windingFreedomStateNoWinding =
      closedCollarAggregateCutParityProfile windingFreedomWord
        windingFreedomStateWithWinding ∧
    closedCollarWindingProfile windingFreedomWord
        windingFreedomStateNoWinding ≠
      closedCollarWindingProfile windingFreedomWord
        windingFreedomStateWithWinding

theorem closedCollarWindingFreedomWitnessRealizationData :
    ClosedCollarWindingFreedomWitnessRealizationData := by
  refine
    ⟨?_, ?_, windingFreedom_stateNoWinding_mem,
      windingFreedom_stateWithWinding_mem, ?_, windingFreedom_profiles_differ⟩
  · decide
  · decide
  · exact
      windingFreedom_aggregateParity_same.1.trans
        windingFreedom_aggregateParity_same.2.symm

/--
The direct finite winding-freedom witness is not an honest simple endpoint
normal-form realization.  This is a first-blocker statement for the direct
witness only; it does not rule out a later filler or subdivision search.
-/
def ClosedCollarWindingFreedomDirectWitnessBlockedBySimpleNormalForm : Prop :=
  ClosedCollarWindingFreedomWitnessRealizationData ∧
    closedCollarHasParallelEndpointEdges windingFreedomWord ∧
    ¬ closedCollarSimpleEndpointRealization windingFreedomWord

theorem closedCollarWindingFreedomDirectWitnessBlockedBySimpleNormalForm :
    ClosedCollarWindingFreedomDirectWitnessBlockedBySimpleNormalForm := by
  exact
    ⟨closedCollarWindingFreedomWitnessRealizationData,
      windingFreedomWord_hasParallelEndpointEdges,
      windingFreedomWord_not_simpleEndpointRealization⟩

end GoertzelLemma818ClosedCollarWindingRealization

end Mettapedia.GraphTheory.FourColor
