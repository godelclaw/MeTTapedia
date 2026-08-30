import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairOverlapKempeHolonomyResidue
import Mettapedia.GraphTheory.FourColor.GoertzelV24OrderedMeshOrientedGlobalSites

/-!
# Complete boundary holonomy from one global mesh-site choice

The earlier complete-boundary construction selected an adjacent-pair Kempe
site independently in each coordinate rectangle.  Here every physical row or
column step first receives one global forward site.  Each cell then uses that
site directly on north/east and through the canonical reversal on south/west.

The resulting boundary relation has the same exact section-versus-obstruction
dichotomy, but its sites are now comparable across neighbouring cells.  This
is the final choice-coherence layer needed before a genuinely two-dimensional
holonomy or cancellation argument.  No such cancellation, flatness, or wall
exclusion is asserted here.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24OrderedMeshGlobalBoundaryHolonomy

open GoertzelV24AdjacentPairBoundary
open GoertzelV24AdjacentPairInsertion
open GoertzelV24AdjacentPairInsertion.AdjacentPairData
open GoertzelV24MeshIsoperimetry
open GoertzelV24OrderedInjectiveMeshWidthFactorization
open GoertzelV24OrderedMeshAdjacentPairSites
open GoertzelV24OrderedMeshBoundaryWalk
open GoertzelV24OrderedMeshOrientedGlobalSites
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
    (orientedGlobalBoundaryKempeSite
      rotation minimal ordered cell step).data

/-- The successor support built from the unique global physical site at both
ends. -/
def globalSuccessorOverlapKempeStateSupport
    (step : Step rotation ordered cell) : Set OverlapKempeState :=
  let source := orientedGlobalBoundaryKempeSite
    rotation minimal ordered cell step
  let target := orientedGlobalBoundaryKempeSite
    rotation minimal ordered cell
      (boundarySuccessor rotation ordered cell step)
  overlapKempeStateSupport source.data target.data source.base target.base

/-- The globally coherent bases inhabit every successor support. -/
theorem globalSuccessorOverlapKempeStateSupport_nonempty
    (step : Step rotation ordered cell) :
    (globalSuccessorOverlapKempeStateSupport
      rotation minimal ordered cell step).Nonempty := by
  exact overlapKempeStateSupport_nonempty
    (orientedGlobalBoundaryKempeSite
      rotation minimal ordered cell step).data
    (orientedGlobalBoundaryKempeSite rotation minimal ordered cell
      (boundarySuccessor rotation ordered cell step)).data
    (orientedGlobalBoundaryKempeSite
      rotation minimal ordered cell step).base
    (orientedGlobalBoundaryKempeSite rotation minimal ordered cell
      (boundarySuccessor rotation ordered cell step)).base
    (orientedGlobalBoundaryKempeSite
      rotation minimal ordered cell step).baseTait
    (orientedGlobalBoundaryKempeSite rotation minimal ordered cell
      (boundarySuccessor rotation ordered cell step)).baseTait

/-- One realised finite state on each successor relation, all evaluated from
the single global mesh-site family. -/
structure GlobalBoundaryOverlapStateAssignment where
  state : Step rotation ordered cell → OverlapKempeState
  state_mem : ∀ step,
    state step ∈ globalSuccessorOverlapKempeStateSupport
      rotation minimal ordered cell step

/-- Pairwise nonemptiness supplies a default assignment.  This chooses only
finite states; the physical Kempe sites and bases were already chosen once
globally. -/
noncomputable def defaultGlobalBoundaryOverlapStateAssignment :
    GlobalBoundaryOverlapStateAssignment rotation minimal ordered cell where
  state step := Classical.choose
    (globalSuccessorOverlapKempeStateSupport_nonempty
      rotation minimal ordered cell step)
  state_mem step := Classical.choose_spec
    (globalSuccessorOverlapKempeStateSupport_nonempty
      rotation minimal ordered cell step)

/-- The globally chosen base colourings determine a canonical successor
state on every boundary step.  Unlike an arbitrary independent choice from
each pairwise support, these states are jointly realised by construction. -/
noncomputable def baseGlobalBoundaryOverlapStateAssignment :
    GlobalBoundaryOverlapStateAssignment rotation minimal ordered cell where
  state step :=
    let source := orientedGlobalBoundaryKempeSite
      rotation minimal ordered cell step
    let target := orientedGlobalBoundaryKempeSite
      rotation minimal ordered cell
        (boundarySuccessor rotation ordered cell step)
    overlapKempeState source.data target.data source.base target.base
  state_mem step := by
    let source := orientedGlobalBoundaryKempeSite
      rotation minimal ordered cell step
    let target := orientedGlobalBoundaryKempeSite
      rotation minimal ordered cell
        (boundarySuccessor rotation ordered cell step)
    exact ⟨source.base,
      SimpleGraph.mem_edgeKempeClosure_self source.base, source.baseTait,
      target.base, SimpleGraph.mem_edgeKempeClosure_self target.base,
      target.baseTait, rfl⟩

/-- Concrete witnesses of one globally based successor state. -/
def globalSuccessorWitnessRelation
    (assignment : GlobalBoundaryOverlapStateAssignment
      rotation minimal ordered cell)
    (step : Step rotation ordered cell) :
    SiteColoring rotation minimal ordered cell step →
      SiteColoring rotation minimal ordered cell
        (boundarySuccessor rotation ordered cell step) → Prop :=
  let source := orientedGlobalBoundaryKempeSite
    rotation minimal ordered cell step
  let target := orientedGlobalBoundaryKempeSite
    rotation minimal ordered cell
      (boundarySuccessor rotation ordered cell step)
  overlapStateWitnessRelation source.data target.data source.base target.base
    (assignment.state step)

/-- Each selected globally based successor relation has a concrete witness
pair. -/
theorem globalSuccessorWitnessRelation_nonempty
    (assignment : GlobalBoundaryOverlapStateAssignment
      rotation minimal ordered cell)
    (step : Step rotation ordered cell) :
    RelationNonempty
      (globalSuccessorWitnessRelation
        rotation minimal ordered cell assignment step) := by
  exact (mem_overlapKempeStateSupport_iff_relationNonempty
    (orientedGlobalBoundaryKempeSite
      rotation minimal ordered cell step).data
    (orientedGlobalBoundaryKempeSite rotation minimal ordered cell
      (boundarySuccessor rotation ordered cell step)).data
    (orientedGlobalBoundaryKempeSite
      rotation minimal ordered cell step).base
    (orientedGlobalBoundaryKempeSite rotation minimal ordered cell
      (boundarySuccessor rotation ordered cell step)).base
    (assignment.state step)).1 (assignment.state_mem step)

/-- A simultaneous concrete section of the complete globally based boundary
relation. -/
structure GlobalBoundaryWitnessSection
    (assignment : GlobalBoundaryOverlapStateAssignment
      rotation minimal ordered cell) where
  coloring : ∀ step : Step rotation ordered cell,
    SiteColoring rotation minimal ordered cell step
  follows : ∀ step,
    globalSuccessorWitnessRelation
      rotation minimal ordered cell assignment step
      (coloring step)
      (coloring (boundarySuccessor rotation ordered cell step))

/-- The canonical state assignment supplied by the global base colourings
has a simultaneous boundary section: use those same base colourings at all
sites.  Thus a mesh does not force a relational obstruction merely from
pairwise support nonemptiness and shared-site coherence. -/
noncomputable def baseGlobalBoundaryWitnessSection :
    GlobalBoundaryWitnessSection rotation minimal ordered cell
      (baseGlobalBoundaryOverlapStateAssignment
        rotation minimal ordered cell) where
  coloring step :=
    (orientedGlobalBoundaryKempeSite
      rotation minimal ordered cell step).base
  follows step := by
    let source := orientedGlobalBoundaryKempeSite
      rotation minimal ordered cell step
    let target := orientedGlobalBoundaryKempeSite
      rotation minimal ordered cell
        (boundarySuccessor rotation ordered cell step)
    exact ⟨SimpleGraph.mem_edgeKempeClosure_self source.base,
      source.baseTait,
      SimpleGraph.mem_edgeKempeClosure_self target.base,
      target.baseTait,
      rfl⟩

/-- Failure of simultaneous lifting for one globally based finite-state
assignment. -/
def HasGlobalBoundaryWitnessObstruction
    (assignment : GlobalBoundaryOverlapStateAssignment
      rotation minimal ordered cell) : Prop :=
  ¬ Nonempty (GlobalBoundaryWitnessSection
    rotation minimal ordered cell assignment)

/-- In particular, the canonical globally based assignment is not
obstructed.  Any wall-facing holonomy argument must therefore constrain the
finite states by additional ambient or replacement data; it cannot obtain an
obstruction from the mesh carrier and pairwise nonemptiness alone. -/
theorem not_hasGlobalBoundaryWitnessObstruction_base :
    ¬ HasGlobalBoundaryWitnessObstruction rotation minimal ordered cell
      (baseGlobalBoundaryOverlapStateAssignment
        rotation minimal ordered cell) := by
  intro obstruction
  exact obstruction
    ⟨baseGlobalBoundaryWitnessSection rotation minimal ordered cell⟩

/-- The exact section-versus-obstruction dichotomy after all physical site
choices have been made globally. -/
theorem globalBoundaryWitnessSection_or_obstruction
    (assignment : GlobalBoundaryOverlapStateAssignment
      rotation minimal ordered cell) :
    Nonempty (GlobalBoundaryWitnessSection
        rotation minimal ordered cell assignment) ∨
      HasGlobalBoundaryWitnessObstruction
        rotation minimal ordered cell assignment := by
  exact Classical.em _

namespace GlobalBoundaryWitnessSection

/-- A section realises the assigned finite state on every successor edge. -/
theorem state_eq_overlapKempeState
    {assignment : GlobalBoundaryOverlapStateAssignment
      rotation minimal ordered cell}
    (witness : GlobalBoundaryWitnessSection
      rotation minimal ordered cell assignment)
    (step : Step rotation ordered cell) :
    assignment.state step = overlapKempeState
      (orientedGlobalBoundaryKempeSite
        rotation minimal ordered cell step).data
      (orientedGlobalBoundaryKempeSite rotation minimal ordered cell
        (boundarySuccessor rotation ordered cell step)).data
      (witness.coloring step)
      (witness.coloring
        (boundarySuccessor rotation ordered cell step)) :=
  (witness.follows step).2.2.2.2

end GlobalBoundaryWitnessSection

end

end GoertzelV24OrderedMeshGlobalBoundaryHolonomy

end Mettapedia.GraphTheory.FourColor
