import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairOverlapKempeHolonomyResidue
import Mettapedia.GraphTheory.FourColor.GoertzelV24OrderedMeshBoundaryWalk

/-!
# Exact shared-witness sections on a complete ordered-mesh boundary

The complete boundary carrier chooses one adjacent-pair Kempe orbit at every
oriented subdivision step.  This file states the global lifting problem with
its quantifiers in the right order.

First choose one realised finite overlap state on every step-to-successor
relation.  A boundary section is then one concrete deletion colouring at
every site, reused definitionally by its incoming and outgoing relations.
This is the arbitrary-perimeter version of the four-corner shared-witness
condition.  It is an incidence theorem only: no embedded-disc, flatness,
support-replacement, or wall-exclusion conclusion is asserted.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24OrderedMeshBoundaryHolonomy

open GoertzelV24AdjacentPairBoundary
open GoertzelV24AdjacentPairInsertion
open GoertzelV24AdjacentPairInsertion.AdjacentPairData
open GoertzelV24MeshIsoperimetry
open GoertzelV24OrderedInjectiveMeshWidthFactorization
open GoertzelV24OrderedMeshAdjacentPairSites
open GoertzelV24OrderedMeshBoundaryWalk
open GoertzelV24RotationMultigraphAdapter
open GoertzelV24TwoEdgeCutMinimality
open SimpleGraph
open SimpleGraphDartRotation

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]
  {a b : Nat}

variable
  (rotation : Data G)
  (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
  (ordered : OrderedInjectiveMesh
    (toMultigraph rotation.toRotationSystem) a b)
  (cell : CellIndex a b)

abbrev Step := CellBoundaryStep rotation ordered cell

abbrev Site (step : Step rotation ordered cell) :=
  BoundaryKempeSite rotation minimal ordered cell step

abbrev SiteColoring (step : Step rotation ordered cell) :=
  DeletionColoring
    (selectedBoundaryKempeSite rotation minimal ordered cell step).data

/-- One finite overlap-state choice on every oriented boundary edge.  Each
choice is already realised pairwise; the open question is whether all choices
can reuse one concrete colouring at every common site. -/
structure BoundaryOverlapStateAssignment where
  state : Step rotation ordered cell → OverlapKempeState
  state_mem : ∀ step,
    state step ∈ successorOverlapKempeStateSupport
      rotation minimal ordered cell step

/-- Pairwise nonemptiness supplies at least one global assignment of finite
states.  This uses choice across the finite step carrier, not a lifting of
their concrete witnesses. -/
noncomputable def defaultBoundaryOverlapStateAssignment :
    BoundaryOverlapStateAssignment rotation minimal ordered cell where
  state step := Classical.choose
    (successorOverlapKempeStateSupport_nonempty
      rotation minimal ordered cell step)
  state_mem step := Classical.choose_spec
    (successorOverlapKempeStateSupport_nonempty
      rotation minimal ordered cell step)

/-- The concrete witness relation selected on one boundary step. -/
def successorWitnessRelation
    (assignment : BoundaryOverlapStateAssignment
      rotation minimal ordered cell)
    (step : Step rotation ordered cell) :
    SiteColoring rotation minimal ordered cell step →
      SiteColoring rotation minimal ordered cell
        (boundarySuccessor rotation ordered cell step) → Prop :=
  let source := selectedBoundaryKempeSite rotation minimal ordered cell step
  let target := selectedBoundaryKempeSite rotation minimal ordered cell
    (boundarySuccessor rotation ordered cell step)
  overlapStateWitnessRelation source.data target.data source.base target.base
    (assignment.state step)

/-- Every selected one-step relation has a concrete witness pair. -/
theorem successorWitnessRelation_nonempty
    (assignment : BoundaryOverlapStateAssignment
      rotation minimal ordered cell)
    (step : Step rotation ordered cell) :
    RelationNonempty
      (successorWitnessRelation rotation minimal ordered cell assignment step) := by
  exact (mem_overlapKempeStateSupport_iff_relationNonempty
    (selectedBoundaryKempeSite rotation minimal ordered cell step).data
    (selectedBoundaryKempeSite rotation minimal ordered cell
      (boundarySuccessor rotation ordered cell step)).data
    (selectedBoundaryKempeSite rotation minimal ordered cell step).base
    (selectedBoundaryKempeSite rotation minimal ordered cell
      (boundarySuccessor rotation ordered cell step)).base
    (assignment.state step)).1 (assignment.state_mem step)

/-- A genuine section of the complete cyclic relation.  The same dependent
function `coloring` is read by both sides incident with every site, ruling out
the pairwise-witness mismatch by construction. -/
structure BoundaryWitnessSection
    (assignment : BoundaryOverlapStateAssignment
      rotation minimal ordered cell) where
  coloring : ∀ step : Step rotation ordered cell,
    SiteColoring rotation minimal ordered cell step
  follows : ∀ step,
    successorWitnessRelation rotation minimal ordered cell assignment step
      (coloring step)
      (coloring (boundarySuccessor rotation ordered cell step))

/-- Failure of global shared-witness lifting for this exact state assignment. -/
def HasBoundaryWitnessObstruction
    (assignment : BoundaryOverlapStateAssignment
      rotation minimal ordered cell) : Prop :=
  ¬ Nonempty (BoundaryWitnessSection
    rotation minimal ordered cell assignment)

/-- The exact boundary-wide lifting dichotomy.  Unlike a four-corner logical
dichotomy, its positive horn already reuses one colouring at every actual
subdivision step.  A geometric consumer is still needed for the negative
horn. -/
theorem boundaryWitnessSection_or_obstruction
    (assignment : BoundaryOverlapStateAssignment
      rotation minimal ordered cell) :
    Nonempty (BoundaryWitnessSection
        rotation minimal ordered cell assignment) ∨
      HasBoundaryWitnessObstruction
        rotation minimal ordered cell assignment := by
  exact Classical.em _

namespace BoundaryWitnessSection

/-- A section's site colouring lies in the globally selected Kempe orbit. -/
theorem coloring_mem
    {assignment : BoundaryOverlapStateAssignment
      rotation minimal ordered cell}
    (witness : BoundaryWitnessSection
      rotation minimal ordered cell assignment)
    (step : Step rotation ordered cell) :
    witness.coloring step ∈
      (DeletedAdjacentPairGraph G
        (selectedBoundaryKempeSite rotation minimal ordered cell step).data.firstVertex
        (selectedBoundaryKempeSite rotation minimal ordered cell step).data.secondVertex).EdgeKempeClosure
            (selectedBoundaryKempeSite rotation minimal ordered cell step).base :=
  (witness.follows step).1

/-- A section's site colouring remains a proper nonzero Tait colouring. -/
theorem coloring_isTait
    {assignment : BoundaryOverlapStateAssignment
      rotation minimal ordered cell}
    (witness : BoundaryWitnessSection
      rotation minimal ordered cell assignment)
    (step : Step rotation ordered cell) :
    IsTaitEdgeColoring
      (DeletedAdjacentPairGraph G
        (selectedBoundaryKempeSite rotation minimal ordered cell step).data.firstVertex
        (selectedBoundaryKempeSite rotation minimal ordered cell step).data.secondVertex)
      (witness.coloring step) :=
  (witness.follows step).2.1

/-- The chosen finite state on every successor edge is realised by the two
concrete colourings supplied by the global section. -/
theorem state_eq_overlapKempeState
    {assignment : BoundaryOverlapStateAssignment
      rotation minimal ordered cell}
    (witness : BoundaryWitnessSection
      rotation minimal ordered cell assignment)
    (step : Step rotation ordered cell) :
    assignment.state step = overlapKempeState
      (selectedBoundaryKempeSite rotation minimal ordered cell step).data
      (selectedBoundaryKempeSite rotation minimal ordered cell
        (boundarySuccessor rotation ordered cell step)).data
      (witness.coloring step)
      (witness.coloring (boundarySuccessor rotation ordered cell step)) :=
  (witness.follows step).2.2.2.2

end BoundaryWitnessSection

end

end GoertzelV24OrderedMeshBoundaryHolonomy

end Mettapedia.GraphTheory.FourColor
