import Mettapedia.GraphTheory.FourColor.GoertzelV24OrderedMeshBoundaryHolonomy

/-!
# Exact relational residue on a complete ordered-mesh boundary

Cut the complete cyclic boundary immediately before its north-west root.
The resulting endorelation on the root colouring fibre records every
successor relation exactly once.  A boundary section exists precisely when
this endorelation has a fixed point.

Consequently, a shared-witness obstruction is either a relational break or
an inhabited fixed-point-free holonomy.  In the latter case the existing
generic residue theorem gives support drift, branching, or a genuine stable
fixed-point-free permutation.  No geometric or wall-exclusion consequence
is asserted here.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24OrderedMeshBoundaryHolonomyResidue

open GoertzelV24AdjacentPairBoundary
open GoertzelV24AdjacentPairInsertion
open GoertzelV24AdjacentPairInsertion.AdjacentPairData
open GoertzelV24MeshIsoperimetry
open GoertzelV24OrderedInjectiveMeshWidthFactorization
open GoertzelV24OrderedMeshAdjacentPairSites
open GoertzelV24OrderedMeshBoundaryHolonomy
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

abbrev SiteColoring (step : Step rotation ordered cell) :=
  DeletionColoring
    (selectedBoundaryKempeSite rotation minimal ordered cell step).data

/-- The north-west first step is the root at which the boundary is cut. -/
def boundaryRoot : Step rotation ordered cell :=
  .north ⟨0, northLength_pos rotation ordered cell⟩

/-- The last west-side step immediately precedes the north-west root. -/
def boundaryRootPredecessor : Step rotation ordered cell :=
  .west ⟨westLength rotation ordered cell - 1, by
    have hpositive := westLength_pos rotation ordered cell
    omega⟩

theorem boundarySuccessor_rootPredecessor :
    boundarySuccessor rotation ordered cell
        (boundaryRootPredecessor rotation ordered cell) =
      boundaryRoot rotation ordered cell := by
  simp only [boundaryRootPredecessor, boundarySuccessor, boundaryRoot]
  split
  · rename_i hlt
    have hpositive := westLength_pos rotation ordered cell
    omega
  · rfl

theorem cast_dependent_apply
    {Index : Type*} (Family : Index → Type*)
    (value : ∀ index, Family index) {source target : Index}
    (hindex : source = target) :
    cast (congrArg Family hindex) (value source) = value target := by
  cases hindex
  rfl

/-- Regard a root colouring as a colouring at the successor of the cut
predecessor. -/
def rootColoringAtPredecessorTarget
    (coloring : SiteColoring rotation minimal ordered cell
      (boundaryRoot rotation ordered cell)) :
    SiteColoring rotation minimal ordered cell
      (boundarySuccessor rotation ordered cell
      (boundaryRootPredecessor rotation ordered cell)) :=
  cast
    (congrArg (SiteColoring rotation minimal ordered cell)
      (boundarySuccessor_rootPredecessor
        rotation ordered cell).symm)
    coloring

theorem rootColoringAtPredecessorTarget_eq
    (coloring : ∀ step : Step rotation ordered cell,
      SiteColoring rotation minimal ordered cell step) :
    rootColoringAtPredecessorTarget rotation minimal ordered cell
        (coloring (boundaryRoot rotation ordered cell)) =
      coloring (boundarySuccessor rotation ordered cell
        (boundaryRootPredecessor rotation ordered cell)) := by
  exact cast_dependent_apply
    (SiteColoring rotation minimal ordered cell) coloring
    (boundarySuccessor_rootPredecessor
      rotation ordered cell).symm

/-- The complete boundary relation, cut at the north-west root and composed
back to the same root fibre. -/
def boundaryRelationalHolonomy
    (assignment : BoundaryOverlapStateAssignment
      rotation minimal ordered cell) :
    SiteColoring rotation minimal ordered cell
        (boundaryRoot rotation ordered cell) →
      SiteColoring rotation minimal ordered cell
        (boundaryRoot rotation ordered cell) → Prop :=
  fun start finish => ∃ coloring : ∀ step : Step rotation ordered cell,
    SiteColoring rotation minimal ordered cell step,
      coloring (boundaryRoot rotation ordered cell) = start ∧
      (∀ step, step ≠ boundaryRootPredecessor rotation ordered cell →
        successorWitnessRelation rotation minimal ordered cell assignment step
          (coloring step)
          (coloring (boundarySuccessor rotation ordered cell step))) ∧
      successorWitnessRelation rotation minimal ordered cell assignment
        (boundaryRootPredecessor rotation ordered cell)
        (coloring (boundaryRootPredecessor rotation ordered cell))
        (rootColoringAtPredecessorTarget rotation minimal ordered cell finish)

/-- A concrete boundary section is exactly a fixed point of the cut-open
complete boundary relation. -/
theorem nonempty_boundaryWitnessSection_iff_fixedPoint
    (assignment : BoundaryOverlapStateAssignment
      rotation minimal ordered cell) :
    Nonempty (BoundaryWitnessSection
        rotation minimal ordered cell assignment) ↔
      ∃ start, boundaryRelationalHolonomy
        rotation minimal ordered cell assignment start start := by
  constructor
  · rintro ⟨witness⟩
    refine ⟨witness.coloring (boundaryRoot rotation ordered cell),
      witness.coloring, rfl, ?_, ?_⟩
    · intro step _
      exact witness.follows step
    · simpa only [rootColoringAtPredecessorTarget_eq] using
        witness.follows (boundaryRootPredecessor rotation ordered cell)
  · rintro ⟨start, coloring, hroot, hsteps, hlast⟩
    refine ⟨{ coloring := coloring, follows := ?_ }⟩
    intro step
    by_cases hstep : step = boundaryRootPredecessor rotation ordered cell
    · subst step
      have htarget :
          rootColoringAtPredecessorTarget rotation minimal ordered cell start =
            coloring (boundarySuccessor rotation ordered cell
              (boundaryRootPredecessor rotation ordered cell)) := by
        calc
          rootColoringAtPredecessorTarget rotation minimal ordered cell start =
              rootColoringAtPredecessorTarget rotation minimal ordered cell
                (coloring (boundaryRoot rotation ordered cell)) :=
            congrArg
              (rootColoringAtPredecessorTarget
                rotation minimal ordered cell) hroot.symm
          _ = coloring (boundarySuccessor rotation ordered cell
                (boundaryRootPredecessor rotation ordered cell)) :=
            rootColoringAtPredecessorTarget_eq
              rotation minimal ordered cell coloring
      simpa only [htarget] using hlast
    · exact hsteps step hstep

/-- The one-step relations are inhabited, but they do not concatenate into
even one complete clockwise return. -/
def HasBoundaryRelationalBreak
    (assignment : BoundaryOverlapStateAssignment
      rotation minimal ordered cell) : Prop :=
  ¬ RelationNonempty
    (boundaryRelationalHolonomy rotation minimal ordered cell assignment)

/-- At least one complete clockwise return exists, but every such return
changes its root colouring. -/
def HasNonemptyFixedPointFreeBoundaryHolonomy
    (assignment : BoundaryOverlapStateAssignment
      rotation minimal ordered cell) : Prop :=
  RelationNonempty
      (boundaryRelationalHolonomy rotation minimal ordered cell assignment) ∧
    ∀ start finish,
      boundaryRelationalHolonomy rotation minimal ordered cell assignment
          start finish →
        start ≠ finish

/-- The exact arbitrary-perimeter analogue of the four-corner residue:
failure of a shared-witness section is either a relational break or a proper
inhabited fixed-point-free return. -/
theorem hasBoundaryWitnessObstruction_iff_break_or_nonempty
    (assignment : BoundaryOverlapStateAssignment
      rotation minimal ordered cell) :
    HasBoundaryWitnessObstruction rotation minimal ordered cell assignment ↔
      HasBoundaryRelationalBreak rotation minimal ordered cell assignment ∨
        HasNonemptyFixedPointFreeBoundaryHolonomy
          rotation minimal ordered cell assignment := by
  have hsection := nonempty_boundaryWitnessSection_iff_fixedPoint
    rotation minimal ordered cell assignment
  constructor
  · intro hobstruction
    have hnoFixed : ¬ ∃ start,
        boundaryRelationalHolonomy
          rotation minimal ordered cell assignment start start := by
      intro hfixed
      exact hobstruction (hsection.2 hfixed)
    by_cases hreturn : RelationNonempty
        (boundaryRelationalHolonomy
          rotation minimal ordered cell assignment)
    · right
      refine ⟨hreturn, ?_⟩
      intro start finish hholonomy heq
      subst finish
      exact hnoFixed ⟨start, hholonomy⟩
    · exact Or.inl hreturn
  · rintro (hbreak | hproper)
    · intro hsectionWitness
      rcases hsection.1 hsectionWitness with ⟨start, hfixed⟩
      exact hbreak ⟨start, start, hfixed⟩
    · intro hsectionWitness
      rcases hsection.1 hsectionWitness with ⟨start, hfixed⟩
      exact hproper.2 start start hfixed rfl

/-- Pairwise support is automatic on the complete boundary; the only
remaining alternatives are therefore the two global residues above. -/
theorem hasBoundaryWitnessObstruction_iff_pairwise_and_residue
    (assignment : BoundaryOverlapStateAssignment
      rotation minimal ordered cell) :
    HasBoundaryWitnessObstruction rotation minimal ordered cell assignment ↔
      (∀ step,
        RelationNonempty
          (successorWitnessRelation
            rotation minimal ordered cell assignment step)) ∧
      (HasBoundaryRelationalBreak rotation minimal ordered cell assignment ∨
        HasNonemptyFixedPointFreeBoundaryHolonomy
          rotation minimal ordered cell assignment) := by
  constructor
  · intro hobstruction
    refine ⟨fun step => successorWitnessRelation_nonempty
      rotation minimal ordered cell assignment step, ?_⟩
    exact (hasBoundaryWitnessObstruction_iff_break_or_nonempty
      rotation minimal ordered cell assignment).1 hobstruction
  · rintro ⟨_, hresidue⟩
    exact (hasBoundaryWitnessObstruction_iff_break_or_nonempty
      rotation minimal ordered cell assignment).2 hresidue

/-- An inhabited fixed-point-free perimeter return has the same three exact
finite residues as the four-corner relation: support drift, branching, or a
stable fixed-point-free permutation on its active support. -/
theorem nonemptyFixedPointFreeBoundaryHolonomy_residue
    (assignment : BoundaryOverlapStateAssignment
      rotation minimal ordered cell)
    (hproper : HasNonemptyFixedPointFreeBoundaryHolonomy
      rotation minimal ordered cell assignment) :
    let holonomy := boundaryRelationalHolonomy
      rotation minimal ordered cell assignment
    HasRelationSupportDrift holonomy ∨
      HasRelationBranching holonomy ∨
      ∃ transport : StableRelationalTransport holonomy,
        Nonempty (RelationDomain holonomy) ∧
          ∀ source, transport.equivalence source ≠ source := by
  exact nonemptyFixedPointFreeRelation_residue
    (boundaryRelationalHolonomy rotation minimal ordered cell assignment)
    hproper.1 hproper.2

/-- Consumer-facing form of the full obstruction.  The relational-break
horn remains separate; every proper return has drift, branching, or stable
permutation holonomy. -/
theorem boundaryWitnessObstruction_residue
    (assignment : BoundaryOverlapStateAssignment
      rotation minimal ordered cell)
    (hobstruction : HasBoundaryWitnessObstruction
      rotation minimal ordered cell assignment) :
    (∀ step,
      RelationNonempty
        (successorWitnessRelation
          rotation minimal ordered cell assignment step)) ∧
    let holonomy := boundaryRelationalHolonomy
      rotation minimal ordered cell assignment
    HasBoundaryRelationalBreak rotation minimal ordered cell assignment ∨
      HasRelationSupportDrift holonomy ∨
      HasRelationBranching holonomy ∨
      ∃ transport : StableRelationalTransport holonomy,
        Nonempty (RelationDomain holonomy) ∧
          ∀ source, transport.equivalence source ≠ source := by
  have hpairwise : ∀ step,
      RelationNonempty
        (successorWitnessRelation
          rotation minimal ordered cell assignment step) :=
    fun step => successorWitnessRelation_nonempty
      rotation minimal ordered cell assignment step
  refine ⟨hpairwise, ?_⟩
  rcases (hasBoundaryWitnessObstruction_iff_break_or_nonempty
      rotation minimal ordered cell assignment).1 hobstruction with
    hbreak | hproper
  · exact Or.inl hbreak
  · rcases nonemptyFixedPointFreeBoundaryHolonomy_residue
      rotation minimal ordered cell assignment hproper with
      hdrift | hbranch | hstable
    · exact Or.inr (Or.inl hdrift)
    · exact Or.inr (Or.inr (Or.inl hbranch))
    · exact Or.inr (Or.inr (Or.inr hstable))

end

end GoertzelV24OrderedMeshBoundaryHolonomyResidue

end Mettapedia.GraphTheory.FourColor
