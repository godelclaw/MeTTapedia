import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairOverlap
import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairKempeTerminalProfile
import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairKempeSwitchSquare

/-!
# A representative-independent finite state for two adjacent-pair orbits

The common-orbit theorem chooses a base colouring of each adjacent-pair
deletion, but that base is not canonical.  The invariant object is the set of
finite boundary states realised by the entire Kempe orbit.  This file records
the exact four-port word, every two-colour port-connectivity bit, the literal
source/target port-overlap profile, and whether the two colourings agree after
restriction to their common deletion.

No transition or wall-exclusion claim is made here.  The main theorem proves
that the realised state set is independent of the selected representative of
either Kempe orbit.
-/

namespace Mettapedia.GraphTheory.FourColor

open GoertzelV24AdjacentPairBoundary
open GoertzelV24AdjacentPairInsertion
open GoertzelV24FourDefectBoundary
open SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

namespace GoertzelV24AdjacentPairInsertion.AdjacentPairData

open GoertzelV24AdjacentPairBoundary.AdjacentPairData

/-- The complete finite four-port observation of one deletion colouring:
its exact boundary word and every labelled two-colour port-connectivity bit. -/
abbrev BoundaryKempeState :=
  (Fin 4 → Color) × (Color → Color → Fin 4 → Fin 4 → Bool)

/-- Booleanize the exact statement that two ports meet the same selected
Kempe component. -/
def kempePortConnectivityBit
    (data : AdjacentPairData G)
    (coloring : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color)
    (firstColor secondColor : Color) (firstPort secondPort : Fin 4) : Bool := by
  classical
  exact if data.degreeTwoBoundaryData.KempePortsConnected coloring
      firstColor secondColor firstPort secondPort then true else false

/-- The finite boundary observation carried by one deletion colouring. -/
def boundaryKempeState
    (data : AdjacentPairData G)
    (coloring : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color) : BoundaryKempeState :=
  (data.degreeTwoBoundaryData.colorWord coloring,
    kempePortConnectivityBit data coloring)

/-- Literal coincidences between the four source ports and four target
ports.  This geometric coordinate does not depend on either colouring. -/
def portOverlapProfile (source target : AdjacentPairData G) :
    Fin 4 → Fin 4 → Bool := fun sourcePort targetPort =>
  if source.portVertex sourcePort = target.portVertex targetPort then true else false

/-- Whether two deletion colourings agree on every edge of their exact
common four-vertex deletion. -/
def commonRestrictionAgreementBit
    (source target : AdjacentPairData G)
    (sourceColoring : (DeletedAdjacentPairGraph G source.firstVertex
      source.secondVertex).EdgeColoring Color)
    (targetColoring : (DeletedAdjacentPairGraph G target.firstVertex
      target.secondVertex).EdgeColoring Color) : Bool :=
  if firstDeletionCommonCoreColoring
        (third := target.firstVertex) (fourth := target.secondVertex)
        sourceColoring =
      secondDeletionCommonCoreColoring
        (first := source.firstVertex) (second := source.secondVertex)
        targetColoring then true else false

/-- The finite observation attached to a pair of deletion colourings. -/
structure OverlapKempeState where
  overlapProfile : Fin 4 → Fin 4 → Bool
  sourceBoundary : BoundaryKempeState
  targetBoundary : BoundaryKempeState
  commonRestrictionAgrees : Bool
deriving DecidableEq

/-- A product code exhibiting that the overlap observation space is finite. -/
abbrev OverlapKempeStateCode :=
  (Fin 4 → Fin 4 → Bool) ×
    BoundaryKempeState × BoundaryKempeState × Bool

/-- Forget the record labels and recover the finite product code. -/
def overlapKempeStateEquiv : OverlapKempeState ≃ OverlapKempeStateCode where
  toFun state :=
    (state.overlapProfile, state.sourceBoundary, state.targetBoundary,
      state.commonRestrictionAgrees)
  invFun code :=
    { overlapProfile := code.1
      sourceBoundary := code.2.1
      targetBoundary := code.2.2.1
      commonRestrictionAgrees := code.2.2.2 }
  left_inv state := by cases state; rfl
  right_inv code := by rcases code with ⟨_, _, _, _⟩; rfl

noncomputable instance overlapKempeStateFintype : Fintype OverlapKempeState := by
  letI : Fintype (Fin 4 → Fin 4 → Bool) := Fintype.ofFinite _
  letI : Fintype BoundaryKempeState := Fintype.ofFinite _
  exact Fintype.ofEquiv OverlapKempeStateCode overlapKempeStateEquiv.symm

/-- Evaluate the finite overlap observation on two concrete colourings. -/
def overlapKempeState
    (source target : AdjacentPairData G)
    (sourceColoring : (DeletedAdjacentPairGraph G source.firstVertex
      source.secondVertex).EdgeColoring Color)
    (targetColoring : (DeletedAdjacentPairGraph G target.firstVertex
      target.secondVertex).EdgeColoring Color) : OverlapKempeState where
  overlapProfile := portOverlapProfile source target
  sourceBoundary := boundaryKempeState source sourceColoring
  targetBoundary := boundaryKempeState target targetColoring
  commonRestrictionAgrees :=
    commonRestrictionAgreementBit source target sourceColoring targetColoring

/-- The canonical finite relation realised by all proper nonzero colourings
in two independently selected Kempe orbits.  Quantifying over the orbit is
load-bearing: a chosen boundary word is not representative-independent. -/
def overlapKempeStateSupport
    (source target : AdjacentPairData G)
    (sourceBase : (DeletedAdjacentPairGraph G source.firstVertex
      source.secondVertex).EdgeColoring Color)
    (targetBase : (DeletedAdjacentPairGraph G target.firstVertex
      target.secondVertex).EdgeColoring Color) : Set OverlapKempeState :=
  {state | ∃ sourceColoring,
      sourceColoring ∈
        (DeletedAdjacentPairGraph G source.firstVertex
          source.secondVertex).EdgeKempeClosure sourceBase ∧
      IsTaitEdgeColoring
        (DeletedAdjacentPairGraph G source.firstVertex source.secondVertex)
        sourceColoring ∧
      ∃ targetColoring,
        targetColoring ∈
          (DeletedAdjacentPairGraph G target.firstVertex
            target.secondVertex).EdgeKempeClosure targetBase ∧
        IsTaitEdgeColoring
          (DeletedAdjacentPairGraph G target.firstVertex target.secondVertex)
          targetColoring ∧
        state = overlapKempeState source target sourceColoring targetColoring}

/-- Replacing either base colouring by a reachable representative does not
change the finite overlap relation. -/
theorem overlapKempeStateSupport_eq_of_mem
    (source target : AdjacentPairData G)
    {sourceBase sourceRepresentative :
      (DeletedAdjacentPairGraph G source.firstVertex
        source.secondVertex).EdgeColoring Color}
    {targetBase targetRepresentative :
      (DeletedAdjacentPairGraph G target.firstVertex
        target.secondVertex).EdgeColoring Color}
    (hsource : sourceRepresentative ∈
      (DeletedAdjacentPairGraph G source.firstVertex
        source.secondVertex).EdgeKempeClosure sourceBase)
    (htarget : targetRepresentative ∈
      (DeletedAdjacentPairGraph G target.firstVertex
        target.secondVertex).EdgeKempeClosure targetBase) :
    overlapKempeStateSupport source target sourceBase targetBase =
      overlapKempeStateSupport source target
        sourceRepresentative targetRepresentative := by
  have hsourceClosure :
      (DeletedAdjacentPairGraph G source.firstVertex
          source.secondVertex).EdgeKempeClosure sourceBase =
        (DeletedAdjacentPairGraph G source.firstVertex
          source.secondVertex).EdgeKempeClosure sourceRepresentative :=
    SimpleGraph.Coloring.kempeClosure_eq_of_mem hsource
  have htargetClosure :
      (DeletedAdjacentPairGraph G target.firstVertex
          target.secondVertex).EdgeKempeClosure targetBase =
        (DeletedAdjacentPairGraph G target.firstVertex
          target.secondVertex).EdgeKempeClosure targetRepresentative :=
    SimpleGraph.Coloring.kempeClosure_eq_of_mem htarget
  simp only [overlapKempeStateSupport, hsourceClosure, htargetClosure]

/-- Proper nonzero base colourings realize at least one overlap state. -/
theorem overlapKempeStateSupport_nonempty
    (source target : AdjacentPairData G)
    (sourceBase : (DeletedAdjacentPairGraph G source.firstVertex
      source.secondVertex).EdgeColoring Color)
    (targetBase : (DeletedAdjacentPairGraph G target.firstVertex
      target.secondVertex).EdgeColoring Color)
    (hsource : IsTaitEdgeColoring
      (DeletedAdjacentPairGraph G source.firstVertex source.secondVertex)
      sourceBase)
    (htarget : IsTaitEdgeColoring
      (DeletedAdjacentPairGraph G target.firstVertex target.secondVertex)
      targetBase) :
    (overlapKempeStateSupport source target sourceBase targetBase).Nonempty := by
  refine ⟨overlapKempeState source target sourceBase targetBase, ?_⟩
  exact ⟨sourceBase,
    SimpleGraph.mem_edgeKempeClosure_self sourceBase, hsource,
    targetBase, SimpleGraph.mem_edgeKempeClosure_self targetBase, htarget, rfl⟩

end GoertzelV24AdjacentPairInsertion.AdjacentPairData

end


/-! Publication-facing aliases for the two consumer theorems. -/

alias GoertzelV24AdjacentPairOverlapKempeState.overlapKempeStateSupport_eq_of_mem :=
  GoertzelV24AdjacentPairInsertion.AdjacentPairData.overlapKempeStateSupport_eq_of_mem

alias GoertzelV24AdjacentPairOverlapKempeState.overlapKempeStateSupport_nonempty :=
  GoertzelV24AdjacentPairInsertion.AdjacentPairData.overlapKempeStateSupport_nonempty

end Mettapedia.GraphTheory.FourColor
