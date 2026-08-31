import Mettapedia.Logic.PathConstraint
import Mettapedia.GraphTheory.FourColor.GoertzelV24OrderedMeshCommonCoreArcConsistencyResidue
import Mettapedia.GraphTheory.FourColor.GoertzelV24OrderedMeshCommonCoreLocalizationResidue

/-!
# A consecutive common-core section on nine ordered mesh sites

The no-branching/no-boundary residue makes every two-site common-core repair
constraint right-total.  Right-total constraints on a path, unlike constraints
on a complete graph, always admit a section.  Applying the generic path theorem
therefore selects Tait colourings at the nine ordered sites which agree on every
consecutive common deletion.

This does not assert an all-pairs section, nor does it synchronize the absent
colour used to read the sites as matching-overlap states.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace OrderedMeshCommonCorePathSection

open GoertzelV24AdjacentPairCommonCoreLocalization
open GoertzelV24AdjacentPairCommonCoreDisagreementResidue
open GoertzelV24AdjacentPairCommonCoreKempeBoundary
open GoertzelV24LocalSwapKempeGeneration
open GoertzelV24OrderedInjectiveMeshWidthFactorization
open GoertzelV24OrderedMeshColoringAtlas
open GoertzelV24OrderedMeshCommonCoreArcConsistencyResidue
open GoertzelV24OrderedMeshCommonCoreDisagreementResidue
open GoertzelV24OrderedMeshCommonCoreLocalizationResidue
open GoertzelV24RotationMultigraphAdapter
open GoertzelV24TwoEdgeCutMinimality
open Mettapedia.Logic
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

/-- The consecutive-site constraint records both reachability from the
canonical colouring at the source site and literal agreement on the exact
common deletion. -/
def ConsecutiveCommonCoreRepairCompatible
    (row : Fin a) (slot : Fin 9 ↪ Fin n)
    (index : Fin 8)
    (source : NineSiteTaitColoringAt
      (rotation := rotation) (minimal := minimal) (ordered := ordered)
      row slot index.castSucc)
    (target : NineSiteTaitColoringAt
      (rotation := rotation) (minimal := minimal) (ordered := ordered)
      row slot index.succ) : Prop :=
  TaitKempeReachable
      ((baseNineSiteTaitAssignment rotation minimal ordered row slot
        index.castSucc).1)
      source.1 ∧
    CommonCoreAgrees
      (rowSiteData rotation minimal ordered row slot index.castSucc)
      (rowSiteData rotation minimal ordered row slot index.succ)
      source.1 target.1

/-- Pairwise repair-surjectivity makes every consecutive constraint
right-total. -/
theorem consecutiveCommonCoreRepairCompatible_rightTotal
    (row : Fin a) (slot : Fin 9 ↪ Fin n)
    (hsurjective : HasPairwiseTaitRepairSurjectivity
      rotation minimal ordered row slot)
    (index : Fin 8) :
    Relator.RightTotal
      (ConsecutiveCommonCoreRepairCompatible
        rotation minimal ordered row slot index) := by
  intro target
  let source := baseNineSiteTaitAssignment
    rotation minimal ordered row slot index.castSucc
  obtain ⟨repaired, hreachable, hagrees⟩ := hsurjective
    index.castSucc index.succ (Fin.ne_of_lt Fin.castSucc_lt_succ)
    source target
  refine ⟨repaired, hreachable, ?_⟩
  exact (commonCoreAgrees_iff_not_coloringsDisagree
    (rowSiteData rotation minimal ordered row slot index.castSucc)
    (rowSiteData rotation minimal ordered row slot index.succ)
    repaired.1 target.1).2 hagrees

/-- Under the no-horn hypothesis, the nine ordered mesh sites admit a path
section whose consecutive colourings agree on their exact common deletions.
The final state is the canonical colouring at the final selected site. -/
theorem exists_consecutive_commonCoreRepair_pathSection_of_no_branchingOrBoundary
    (row : Fin a) (slot : Fin 9 ↪ Fin n)
    (hno : ∀ assignment :
      NineSiteTaitAssignment rotation minimal ordered row slot,
      ¬ HasNineSiteBranchingOrBoundary rotation minimal ordered row slot
          assignment) :
    ∃ pathSection : PathConstraint.Section
        (fun index : Fin 9 ↦ NineSiteTaitColoringAt
          (rotation := rotation) (minimal := minimal) (ordered := ordered)
          row slot index)
        (ConsecutiveCommonCoreRepairCompatible
          rotation minimal ordered row slot),
      pathSection.state (Fin.last 8) =
        baseNineSiteTaitAssignment rotation minimal ordered row slot
          (Fin.last 8) := by
  let hsurjective := pairwiseTaitRepairSurjectivity_of_no_branchingOrBoundary
    rotation minimal ordered row slot hno
  let hRightTotal := fun index : Fin 8 ↦
    consecutiveCommonCoreRepairCompatible_rightTotal
      rotation minimal ordered row slot hsurjective index
  let terminal := baseNineSiteTaitAssignment
    rotation minimal ordered row slot (Fin.last 8)
  let pathSection := PathConstraint.sectionEndingAt
    (fun index : Fin 9 ↦ NineSiteTaitColoringAt
      (rotation := rotation) (minimal := minimal) (ordered := ordered)
      row slot index)
    (ConsecutiveCommonCoreRepairCompatible
      rotation minimal ordered row slot)
    hRightTotal terminal
  refine ⟨pathSection, ?_⟩
  exact PathConstraint.sectionEndingAt_last _ _ _ _

end

end OrderedMeshCommonCorePathSection

end Mettapedia.GraphTheory.FourColor
