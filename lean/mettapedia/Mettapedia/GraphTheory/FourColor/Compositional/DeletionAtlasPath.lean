import Mettapedia.Logic.PathConstraint
import Mettapedia.GraphTheory.FourColor.Compositional.DeletionSiteGeometry
import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairCommonCoreDisagreementResidue
import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairCommonCoreLocalization
import Mettapedia.GraphTheory.FourColor.GoertzelV24SimpleGraphTaitBridge

/-!
# Coherent paths through a finite deletion atlas

This module isolates the finite constraint argument from its mesh carrier.
Given nine adjacent-pair deletion patches, absence of the branching and
boundary-reaching horns makes every consecutive common-core constraint
right-total.  A path of right-total constraints has a section.

Each selected colouring is then completed to a perfect matching using an
absent Tait colour.  If a supplied residual-defect minimizer is noncentral at
the nine deleted pairs, the exact path colourings carry the full two-sector
return geometry.  No planarity, mesh, or catalogue statement is hidden in the
finite path construction itself.
-/

namespace Mettapedia.GraphTheory.FourColor.Compositional.DeletionAtlasPath

open DeletionColorMatching
open DeletionSiteGeometry
open AlternatingSiteGeometry
open GoertzelV24AdjacentPairBoundary
open GoertzelV24AdjacentPairColoringAtlas
open GoertzelV24AdjacentPairColoringAtlas.PairDeletionColoringFamily
open GoertzelV24AdjacentPairCommonCoreDisagreementResidue
open GoertzelV24AdjacentPairCommonCoreKempeBoundary
open GoertzelV24AdjacentPairCommonCoreLocalization
open GoertzelV24AdjacentPairInsertion
open GoertzelV24AdjacentPairInsertion.AdjacentPairData
open GoertzelV24AdjacentPairMatchingExtraction
open GoertzelV24LocalSwapKempeGeneration
open GoertzelV24SimpleGraphTaitBridge
open GoertzelV24TwoEdgeCutMinimality
open Mettapedia.Logic
open SimpleGraph
open SimpleGraphDartRotation

noncomputable section

attribute [-instance]
  GoertzelV24RetainedVertexRotationSplice.retainedVertexFintype
  GoertzelV24SeamFaceArcPartition.hitPointFintype

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Proper nonzero colourings at one coordinate of a nine-deletion atlas. -/
abbrev TaitColoringAt
    (family : PairDeletionColoringFamily (G := G) (Fin 9))
    (index : Fin 9) :=
  { coloring :
      (DeletedAdjacentPairGraph G (family.data index).firstVertex
        (family.data index).secondVertex).EdgeColoring Color //
    IsTaitEdgeColoring
      (DeletedAdjacentPairGraph G (family.data index).firstVertex
        (family.data index).secondVertex) coloring }

/-- One proper nonzero colouring at every deletion coordinate. -/
abbrev TaitAssignment
    (family : PairDeletionColoringFamily (G := G) (Fin 9)) :=
  ∀ index : Fin 9, TaitColoringAt family index

/-- The canonical colourings stored in the atlas. -/
def baseAssignment
    (family : PairDeletionColoringFamily (G := G) (Fin 9)) :
    TaitAssignment family :=
  fun index => ⟨family.coloring index, family.tait index⟩

/-- Replace two distinct coordinates of an assignment. -/
def assignmentWithPair
    (family : PairDeletionColoringFamily (G := G) (Fin 9))
    (first second : Fin 9)
    (source : TaitColoringAt family first)
    (target : TaitColoringAt family second) : TaitAssignment family :=
  Function.update
    (Function.update (baseAssignment family) first source) second target

@[simp] theorem assignmentWithPair_first
    (family : PairDeletionColoringFamily (G := G) (Fin 9))
    (first second : Fin 9) (hne : first ≠ second)
    (source : TaitColoringAt family first)
    (target : TaitColoringAt family second) :
    assignmentWithPair family first second source target first = source := by
  simp [assignmentWithPair, hne]

@[simp] theorem assignmentWithPair_second
    (family : PairDeletionColoringFamily (G := G) (Fin 9))
    (first second : Fin 9)
    (source : TaitColoringAt family first)
    (target : TaitColoringAt family second) :
    assignmentWithPair family first second source target second = target := by
  simp [assignmentWithPair]

/-- A colouring assignment exposes one of the two geometric horns used by
the compositional route. -/
def HasBranchingOrBoundary
    (family : PairDeletionColoringFamily (G := G) (Fin 9))
    (assignment : TaitAssignment family) : Prop :=
  ∃ first second : Fin 9,
    HasCommonCoreBranchingDiscrepancy
        (family.data first) (family.data second)
        (assignment first).1 (assignment second).1 ∨
      FirstTaitOrbitReachesSecondPair
        (family.data first) (family.data second)
        (assignment first).1

/-- Every value at the second coordinate can be matched by a valid-pair
Kempe repair at the first coordinate. -/
def HasPairwiseRepairSurjectivity
    (family : PairDeletionColoringFamily (G := G) (Fin 9)) : Prop :=
  ∀ first second : Fin 9, first ≠ second →
    ∀ source : TaitColoringAt family first,
    ∀ target : TaitColoringAt family second,
      ∃ repaired : TaitColoringAt family first,
        TaitKempeReachable source.1 repaired.1 ∧
        CommonCoreAgrees (family.data first) (family.data second)
          repaired.1 target.1

/-- If no assignment exposes a horn, all binary common-core repair
constraints are surjective. -/
theorem pairwiseRepairSurjectivity_of_no_branchingOrBoundary
    (family : PairDeletionColoringFamily (G := G) (Fin 9))
    (hno : ∀ assignment : TaitAssignment family,
      ¬ HasBranchingOrBoundary family assignment) :
    HasPairwiseRepairSurjectivity family := by
  intro first second hne source target
  by_cases hagrees : CommonCoreAgrees
      (family.data first) (family.data second) source.1 target.1
  · exact ⟨source, Relation.ReflTransGen.refl, hagrees⟩
  · have hdisagrees :
        firstDeletionCommonCoreColoring
            (third := (family.data second).firstVertex)
            (fourth := (family.data second).secondVertex) source.1 ≠
          secondDeletionCommonCoreColoring
            (first := (family.data first).firstVertex)
            (second := (family.data first).secondVertex) target.1 := by
      simpa [CommonCoreAgrees] using hagrees
    rcases branching_or_taitReachesSecondPair_or_strictTaitRepair
        (family.data first) (family.data second)
        source.1 target.1 source.2 target.2 hdisagrees with
      hbranch | hboundary | hrepair
    · let assignment := assignmentWithPair family first second source target
      exfalso
      apply hno assignment
      refine ⟨first, second, Or.inl ?_⟩
      simpa [assignment, assignmentWithPair, hne] using hbranch
    · let assignment := assignmentWithPair family first second source target
      exfalso
      apply hno assignment
      refine ⟨first, second, Or.inr ?_⟩
      simpa [assignment, assignmentWithPair, hne] using hboundary
    · rcases hrepair with
        ⟨repaired, hreachable, hrepairedTait, hrestriction, _hstrict⟩
      exact ⟨⟨repaired, hrepairedTait⟩, hreachable, hrestriction⟩

/-- Consecutive coordinates agree on their exact common deletion, and the
source remains in the valid-pair orbit of its atlas base point. -/
def ConsecutiveRepairCompatible
    (family : PairDeletionColoringFamily (G := G) (Fin 9))
    (index : Fin 8)
    (source : TaitColoringAt family index.castSucc)
    (target : TaitColoringAt family index.succ) : Prop :=
  TaitKempeReachable (family.coloring index.castSucc) source.1 ∧
    CommonCoreAgrees (family.data index.castSucc) (family.data index.succ)
      source.1 target.1

/-- Pairwise repair-surjectivity makes each consecutive constraint
right-total. -/
theorem consecutiveRepairCompatible_rightTotal
    (family : PairDeletionColoringFamily (G := G) (Fin 9))
    (hsurjective : HasPairwiseRepairSurjectivity family)
    (index : Fin 8) :
    Relator.RightTotal (ConsecutiveRepairCompatible family index) := by
  intro target
  let source : TaitColoringAt family index.castSucc :=
    ⟨family.coloring index.castSucc, family.tait index.castSucc⟩
  obtain ⟨repaired, hreachable, hagrees⟩ := hsurjective
    index.castSucc index.succ (Fin.ne_of_lt Fin.castSucc_lt_succ)
    source target
  exact ⟨repaired, hreachable, hagrees⟩

/-- A horn-free nine-deletion atlas has a coherent consecutive path ending
at the canonical final colouring. -/
theorem exists_pathSection_of_no_branchingOrBoundary
    (family : PairDeletionColoringFamily (G := G) (Fin 9))
    (hno : ∀ assignment : TaitAssignment family,
      ¬ HasBranchingOrBoundary family assignment) :
    ∃ pathSection : PathConstraint.Section
        (fun index : Fin 9 => TaitColoringAt family index)
        (ConsecutiveRepairCompatible family),
      pathSection.state (Fin.last 8) =
        (baseAssignment family) (Fin.last 8) := by
  let hsurjective :=
    pairwiseRepairSurjectivity_of_no_branchingOrBoundary family hno
  let hRightTotal := fun index : Fin 8 =>
    consecutiveRepairCompatible_rightTotal family hsurjective index
  let terminal := (baseAssignment family) (Fin.last 8)
  let pathSection := PathConstraint.sectionEndingAt
    (fun index : Fin 9 => TaitColoringAt family index)
    (ConsecutiveRepairCompatible family) hRightTotal terminal
  exact ⟨pathSection, PathConstraint.sectionEndingAt_last _ _ _ _⟩

/-- Complete one path colouring to a supported perfect matching using a Tait
colour absent from its four boundary requests. -/
noncomputable def matchingState
    (rotation : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    (family : PairDeletionColoringFamily (G := G) (Fin 9))
    (pathSection : PathConstraint.Section
      (fun index : Fin 9 => TaitColoringAt family index)
      (ConsecutiveRepairCompatible family))
    (index : Fin 9) : DeletionMatchingState (family.data index) := by
  have hcubic :=
    ResidualSiteProvenance.incidentEdgeFinset_card_eq_three rotation minimal
  have hnot : ¬ TaitColorable G :=
    graphBackedVertexMinimalTaitCounterexample_not_graphTaitColorable
      rotation minimal
  have hsame :=
    GoertzelV24AdjacentPairInsertion.AdjacentPairData.sameSidePairs_of_not_taitColorable
      (family.data index) hcubic hnot
      (pathSection.state index).1 (pathSection.state index).2
  let hexists := exists_taitColor_absent_of_sameSidePairs
    ((family.data index).degreeTwoBoundaryData.colorWord
      (pathSection.state index).1) hsame.1 hsame.2
  let absentColor := Classical.choose hexists
  have habsent := Classical.choose_spec hexists
  exact {
    coloring := (pathSection.state index).1
    isTait := (pathSection.state index).2
    absentColor := absentColor
    absentAtBoundary := habsent }

/-- Every noncentral coordinate of a coherent path carries the exact
two-sector residual-return geometry. -/
theorem twoSectorReceipt_of_noncentral
    (rotation : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    (family : PairDeletionColoringFamily (G := G) (Fin 9))
    (pathSection : PathConstraint.Section
      (fun index : Fin 9 => TaitColoringAt family index)
      (ConsecutiveRepairCompatible family))
    (minimizer : ResidualDefectMinimizer G)
    (index : Fin 9)
    (hnoncentral : minimizer.pairing.partner
        (family.data index).firstVertex ≠ (family.data index).secondVertex) :
    Nonempty (DeletionTwoSectorReturnReceipt rotation minimal minimizer
      (family.data index)
      (matchingState rotation minimal family pathSection index)) :=
  DeletionTwoSectorReturnReceipt.ofState rotation minimal minimizer
    (family.data index)
    (matchingState rotation minimal family pathSection index) hnoncentral

/-- Two path coordinates use the same absent colour; under pointwise
noncentrality both carry exact two-sector return receipts. -/
theorem exists_pair_sameAbsentColor_with_twoSectorReceipts
    (rotation : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    (family : PairDeletionColoringFamily (G := G) (Fin 9))
    (pathSection : PathConstraint.Section
      (fun index : Fin 9 => TaitColoringAt family index)
      (ConsecutiveRepairCompatible family))
    (minimizer : ResidualDefectMinimizer G)
    (hnoncentral : ∀ index : Fin 9, minimizer.pairing.partner
      (family.data index).firstVertex ≠ (family.data index).secondVertex) :
    ∃ first second : Fin 9, first ≠ second ∧
      (matchingState rotation minimal family pathSection first).absentColor =
        (matchingState rotation minimal family pathSection second).absentColor ∧
      Nonempty (DeletionTwoSectorReturnReceipt rotation minimal minimizer
        (family.data first)
        (matchingState rotation minimal family pathSection first)) ∧
      Nonempty (DeletionTwoSectorReturnReceipt rotation minimal minimizer
        (family.data second)
        (matchingState rotation minimal family pathSection second)) := by
  obtain ⟨first, second, hne, hcolor⟩ :=
    Fintype.exists_ne_map_eq_of_card_lt
      (fun index : Fin 9 =>
        (matchingState rotation minimal family pathSection index).absentColor)
      (by decide)
  exact ⟨first, second, hne, hcolor,
    twoSectorReceipt_of_noncentral rotation minimal family pathSection
      minimizer first (hnoncentral first),
    twoSectorReceipt_of_noncentral rotation minimal family pathSection
      minimizer second (hnoncentral second)⟩

/-- The consumer-facing coherent outcome of a nine-deletion atlas: a path of
common-core-compatible colourings, with two coordinates of the same absent
colour carrying exact two-sector residual-return geometry. -/
def HasCoherentTwoSectorPair
    (rotation : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    (family : PairDeletionColoringFamily (G := G) (Fin 9))
    (minimizer : ResidualDefectMinimizer G) : Prop :=
  ∃ pathSection : PathConstraint.Section
      (fun index : Fin 9 => TaitColoringAt family index)
      (ConsecutiveRepairCompatible family),
    pathSection.state (Fin.last 8) =
        (baseAssignment family) (Fin.last 8) ∧
      ∃ first second : Fin 9, first ≠ second ∧
        (matchingState rotation minimal family pathSection first).absentColor =
          (matchingState rotation minimal family pathSection second).absentColor ∧
        Nonempty (DeletionTwoSectorReturnReceipt rotation minimal minimizer
          (family.data first)
          (matchingState rotation minimal family pathSection first)) ∧
        Nonempty (DeletionTwoSectorReturnReceipt rotation minimal minimizer
          (family.data second)
          (matchingState rotation minimal family pathSection second))

/-- Horn-freeness and pointwise noncentrality produce the coherent two-sector
pair used by the compositional mesh argument. -/
theorem hasCoherentTwoSectorPair_of_no_branchingOrBoundary
    (rotation : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    (family : PairDeletionColoringFamily (G := G) (Fin 9))
    (minimizer : ResidualDefectMinimizer G)
    (hno : ∀ assignment : TaitAssignment family,
      ¬ HasBranchingOrBoundary family assignment)
    (hnoncentral : ∀ index : Fin 9, minimizer.pairing.partner
      (family.data index).firstVertex ≠ (family.data index).secondVertex) :
    HasCoherentTwoSectorPair rotation minimal family minimizer := by
  obtain ⟨pathSection, hterminal⟩ :=
    exists_pathSection_of_no_branchingOrBoundary family hno
  refine ⟨pathSection, hterminal, ?_⟩
  exact exists_pair_sameAbsentColor_with_twoSectorReceipts
    rotation minimal family pathSection minimizer hnoncentral

end

end Mettapedia.GraphTheory.FourColor.Compositional.DeletionAtlasPath
