import Mettapedia.GraphTheory.FourColor.GoertzelV24OrderedMeshCommonCoreDisagreementResidue

/-!
# Arc consistency without a common-core section on nine mesh sites

The periodic-repair theorem uses the absence of branching and boundary
escape only to choose one repair successor at each finite state.  The same
hypothesis has a stronger pairwise consequence.  Any Tait colouring at one
selected deletion can be repaired inside its valid-pair Kempe orbit to agree
on the common core with any Tait colouring at any other selected deletion.

Thus the exact remaining object is a finite binary constraint system which
is arc-consistent but has no global section.  This file does not turn that
constraint obstruction into wall exclusion or a physical replacement.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24OrderedMeshCommonCoreArcConsistencyResidue

open GoertzelV24AdjacentPairCommonCoreDisagreementResidue
open GoertzelV24AdjacentPairCommonCoreKempeBoundary
open GoertzelV24AdjacentPairBoundary
open GoertzelV24AdjacentPairInsertion
open GoertzelV24AdjacentPairInsertion.AdjacentPairData
open GoertzelV24LocalSwapKempeGeneration
open GoertzelV24MeshIsoperimetry
open GoertzelV24OrderedInjectiveMeshWidthFactorization
open GoertzelV24OrderedMeshColoringAtlas
open GoertzelV24OrderedMeshCommonCoreDisagreementResidue
open GoertzelV24OrderedMeshGlobalSites
open GoertzelV24RotationMultigraphAdapter
open GoertzelV24TwoEdgeCutMinimality
open SimpleGraph
open SimpleGraphDartRotation

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]
  {a n : Nat}

variable
  (rotation : Data G)
  (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
  (ordered : OrderedInjectiveMesh
    (toMultigraph rotation.toRotationSystem) a (n + 1))

/-- The proper nonzero colouring carrier at one of the nine selected
adjacent-pair deletions. -/
abbrev NineSiteTaitColoringAt
    (row : Fin a) (slot : Fin 9 ↪ Fin n) (index : Fin 9) :=
  { coloring :
      (DeletedAdjacentPairGraph G
        (rowSiteData rotation minimal ordered row slot index).firstVertex
        (rowSiteData rotation minimal ordered row slot index).secondVertex).EdgeColoring
        Color //
    IsTaitEdgeColoring
      (DeletedAdjacentPairGraph G
        (rowSiteData rotation minimal ordered row slot index).firstVertex
        (rowSiteData rotation minimal ordered row slot index).secondVertex)
      coloring }

/-- The canonical selected colourings give a base point in the nine-site
state space. -/
def baseNineSiteTaitAssignment
    (row : Fin a) (slot : Fin 9 ↪ Fin n) :
    NineSiteTaitAssignment rotation minimal ordered row slot :=
  fun index =>
    ⟨(selectedGlobalKempeSite rotation minimal ordered
        (globalRowStep rotation ordered row (slot index))).base,
      (selectedGlobalKempeSite rotation minimal ordered
        (globalRowStep rotation ordered row (slot index))).baseTait⟩

/-- Put arbitrary Tait colourings at two distinct selected sites and retain
the canonical base colouring elsewhere. -/
def assignmentWithPair
    (row : Fin a) (slot : Fin 9 ↪ Fin n)
    (first second : Fin 9)
    (source : NineSiteTaitColoringAt
      (rotation := rotation) (minimal := minimal) (ordered := ordered)
      row slot first)
    (target : NineSiteTaitColoringAt
      (rotation := rotation) (minimal := minimal) (ordered := ordered)
      row slot second) :
    NineSiteTaitAssignment rotation minimal ordered row slot :=
  Function.update
    (Function.update
      (baseNineSiteTaitAssignment rotation minimal ordered row slot)
      first source)
    second target

@[simp] theorem assignmentWithPair_first
    (row : Fin a) (slot : Fin 9 ↪ Fin n)
    (first second : Fin 9) (hne : first ≠ second)
    (source : NineSiteTaitColoringAt
      (rotation := rotation) (minimal := minimal) (ordered := ordered)
      row slot first)
    (target : NineSiteTaitColoringAt
      (rotation := rotation) (minimal := minimal) (ordered := ordered)
      row slot second) :
    assignmentWithPair rotation minimal ordered row slot first second source target
        first = source := by
  simp [assignmentWithPair, hne]

@[simp] theorem assignmentWithPair_second
    (row : Fin a) (slot : Fin 9 ↪ Fin n)
    (first second : Fin 9)
    (source : NineSiteTaitColoringAt
      (rotation := rotation) (minimal := minimal) (ordered := ordered)
      row slot first)
    (target : NineSiteTaitColoringAt
      (rotation := rotation) (minimal := minimal) (ordered := ordered)
      row slot second) :
    assignmentWithPair rotation minimal ordered row slot first second source target
        second = target := by
  simp [assignmentWithPair]

/-- Every value at either end of every distinct pair can be matched by a
valid-pair Kempe repair at the first site. -/
def HasPairwiseTaitRepairSurjectivity
    (row : Fin a) (slot : Fin 9 ↪ Fin n) : Prop :=
  ∀ first second : Fin 9, first ≠ second →
    ∀ source : NineSiteTaitColoringAt
      (rotation := rotation) (minimal := minimal) (ordered := ordered)
      row slot first,
    ∀ target : NineSiteTaitColoringAt
      (rotation := rotation) (minimal := minimal) (ordered := ordered)
      row slot second,
      ∃ repaired : NineSiteTaitColoringAt
          (rotation := rotation) (minimal := minimal) (ordered := ordered)
          row slot first,
        TaitKempeReachable source.1 repaired.1 ∧
        ¬ CommonCoreColoringsDisagree
          (rowSiteData rotation minimal ordered row slot first)
          (rowSiteData rotation minimal ordered row slot second)
          repaired.1 target.1

/-- A global section is one simultaneous assignment whose every ordered
pair agrees on its exact common deletion. -/
def HasNineSiteCommonCoreSection
    (row : Fin a) (slot : Fin 9 ↪ Fin n) : Prop :=
  ∃ assignment : NineSiteTaitAssignment rotation minimal ordered row slot,
    ∀ first second : Fin 9,
      ¬ CommonCoreColoringsDisagree
        (rowSiteData rotation minimal ordered row slot first)
        (rowSiteData rotation minimal ordered row slot second)
        (assignment first).1 (assignment second).1

/-- The finite constraint residue: all binary repair projections are
surjective, but there is no simultaneous common-core section. -/
def HasArcConsistentNoSectionResidue
    (row : Fin a) (slot : Fin 9 ↪ Fin n) : Prop :=
  HasPairwiseTaitRepairSurjectivity rotation minimal ordered row slot ∧
    ¬ HasNineSiteCommonCoreSection rotation minimal ordered row slot

/-- Absence of the branching and boundary horns makes every distinct
two-site repair constraint surjective. -/
theorem pairwiseTaitRepairSurjectivity_of_no_branchingOrBoundary
    (row : Fin a) (slot : Fin 9 ↪ Fin n)
    (hno : ∀ assignment :
      NineSiteTaitAssignment rotation minimal ordered row slot,
      ¬ HasNineSiteBranchingOrBoundary rotation minimal ordered row slot
          assignment) :
    HasPairwiseTaitRepairSurjectivity rotation minimal ordered row slot := by
  intro first second hne source target
  by_cases hdisagrees :
      CommonCoreColoringsDisagree
        (rowSiteData rotation minimal ordered row slot first)
        (rowSiteData rotation minimal ordered row slot second)
        source.1 target.1
  · rcases branching_or_taitReachesSecondPair_or_strictTaitRepair
        (rowSiteData rotation minimal ordered row slot first)
        (rowSiteData rotation minimal ordered row slot second)
        source.1 target.1 source.2 target.2 hdisagrees with
      hbranch | hboundary | hrepair
    · let assignment := assignmentWithPair
          rotation minimal ordered row slot first second source target
      exfalso
      apply hno assignment
      refine ⟨first, second, Or.inl ?_⟩
      simpa [assignment, assignmentWithPair, hne] using hbranch
    · let assignment := assignmentWithPair
          rotation minimal ordered row slot first second source target
      exfalso
      apply hno assignment
      refine ⟨first, second, Or.inr ?_⟩
      simpa [assignment, assignmentWithPair, hne] using hboundary
    · rcases hrepair with
        ⟨repaired, hreachable, hrepairedTait, hagrees, _hstrict⟩
      refine ⟨⟨repaired, hrepairedTait⟩, hreachable, ?_⟩
      simpa [CommonCoreColoringsDisagree] using hagrees
  · exact ⟨source, Relation.ReflTransGen.refl, hdisagrees⟩

/-- Nine selected row sites never admit a simultaneous common-core section.
This is the colouring-atlas obstruction in section language. -/
theorem not_hasNineSiteCommonCoreSection
    (row : Fin a) (slot : Fin 9 ↪ Fin n) :
    ¬ HasNineSiteCommonCoreSection rotation minimal ordered row slot := by
  rintro ⟨assignment, hall⟩
  let coloring := fun index : Fin 9 => (assignment index).1
  have tait : ∀ index : Fin 9,
      IsTaitEdgeColoring
        (DeletedAdjacentPairGraph G
          (rowSiteData rotation minimal ordered row slot index).firstVertex
          (rowSiteData rotation minimal ordered row slot index).secondVertex)
        (coloring index) := fun index => (assignment index).2
  obtain ⟨first, second, _hne, hdisagrees, _hresidue⟩ :=
    exists_taitCommonCoreResidue_in_any_nine_row_intervals
      rotation minimal ordered row slot coloring tait
  exact (hall first second) hdisagrees

/-- **Arc-consistent no-section residue.**  If branching and boundary escape
never occur, the nine-site system is pairwise repair-surjective but has no
global common-core section. -/
theorem arcConsistentNoSectionResidue_of_no_branchingOrBoundary
    (row : Fin a) (slot : Fin 9 ↪ Fin n)
    (hno : ∀ assignment :
      NineSiteTaitAssignment rotation minimal ordered row slot,
      ¬ HasNineSiteBranchingOrBoundary rotation minimal ordered row slot
          assignment) :
    HasArcConsistentNoSectionResidue rotation minimal ordered row slot :=
  ⟨pairwiseTaitRepairSurjectivity_of_no_branchingOrBoundary
      rotation minimal ordered row slot hno,
    not_hasNineSiteCommonCoreSection rotation minimal ordered row slot⟩

end

end GoertzelV24OrderedMeshCommonCoreArcConsistencyResidue

end Mettapedia.GraphTheory.FourColor
