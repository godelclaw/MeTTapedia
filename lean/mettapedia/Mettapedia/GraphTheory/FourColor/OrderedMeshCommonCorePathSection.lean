import Mettapedia.Logic.PathConstraint
import Mettapedia.GraphTheory.FourColor.Compositional.AlternatingComponentLocalization
import Mettapedia.GraphTheory.FourColor.Compositional.DeletionColorMatching
import Mettapedia.GraphTheory.FourColor.GoertzelV24OrderedMeshCommonCoreArcConsistencyResidue
import Mettapedia.GraphTheory.FourColor.GoertzelV24OrderedMeshCommonCoreLocalizationResidue
import Mettapedia.GraphTheory.FourColor.GoertzelV24SimpleGraphTaitBridge

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

open Amplitude
open Compositional.AlternatingComponentLocalization
open Compositional.AlternatingOverlapGeometry
open Compositional.DeletionColorMatching
open GoertzelV24AdjacentPairBoundary
open GoertzelV24AdjacentPairCommonCoreLocalization
open GoertzelV24AdjacentPairCommonCoreDisagreementResidue
open GoertzelV24AdjacentPairCommonCoreKempeBoundary
open GoertzelV24AdjacentPairInsertion
open GoertzelV24AdjacentPairInsertion.AdjacentPairData
open GoertzelV24AdjacentPairMatchingExtraction
open GoertzelV24AdjacentPairMatchingExtraction.AdjacentPairData
open GoertzelV24AlternatingMatchingComponent
open GoertzelV24LocalSwapKempeGeneration
open GoertzelV24OrderedInjectiveMeshWidthFactorization
open GoertzelV24OrderedMeshColoringAtlas
open GoertzelV24OrderedMeshCommonCoreArcConsistencyResidue
open GoertzelV24OrderedMeshCommonCoreDisagreementResidue
open GoertzelV24OrderedMeshCommonCoreLocalizationResidue
open GoertzelV24RotationMultigraphAdapter
open GoertzelV24SimpleGraphTaitBridge
open GoertzelV24TaitMatchingDecomposition
open GoertzelV24TwoEdgeCutMinimality
open MatchingParity
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
  {a n : Nat}

variable
  (rotation : Data G)
  (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
  (ordered : OrderedInjectiveMesh
    (toMultigraph rotation.toRotationSystem) a (n + 1))

local instance commonCorePathRetainedFintype
    (first second : V) : Fintype (retainedVertexSet first second) :=
  Subtype.fintype _

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

/-- The union of all deletion footprints encountered by a nine-site path
section. -/
def commonCoreRepairPathFootprint
    (row : Fin a) (slot : Fin 9 ↪ Fin n) : Finset G.edgeSet :=
  Finset.univ.biUnion fun index : Fin 9 ↦
    deletionFootprint (rowSiteData rotation minimal ordered row slot index)

/-- Nine adjacent-pair deletion footprints contain at most forty-five ambient
edges. -/
theorem card_commonCoreRepairPathFootprint_le
    (row : Fin a) (slot : Fin 9 ↪ Fin n) :
    (commonCoreRepairPathFootprint rotation minimal ordered row slot).card ≤ 45 := by
  calc
    _ ≤ ∑ index : Fin 9,
        (deletionFootprint
          (rowSiteData rotation minimal ordered row slot index)).card :=
      Finset.card_biUnion_le
    _ = ∑ _index : Fin 9, 5 := by
      apply Finset.sum_congr rfl
      intro index _
      exact card_deletionFootprint _
    _ = 45 := by norm_num

/-- A path section assigns the same colour to an ambient edge at every site
which retains that edge. -/
theorem commonCoreColor_eq
    (row : Fin a) (slot : Fin 9 ↪ Fin n)
    (pathSection : PathConstraint.Section
      (fun index : Fin 9 ↦ NineSiteTaitColoringAt
        (rotation := rotation) (minimal := minimal) (ordered := ordered)
        row slot index)
      (ConsecutiveCommonCoreRepairCompatible
        rotation minimal ordered row slot))
    (edge : G.edgeSet)
    (hretained : ∀ index : Fin 9,
      IsRetainedAmbientEdge
        (rowSiteData rotation minimal ordered row slot index) edge)
    (first second : Fin 9) :
    (pathSection.state first).1
        (ambientEdgeToRetainedEdge
          (rowSiteData rotation minimal ordered row slot first)
          edge (hretained first)) =
      (pathSection.state second).1
        (ambientEdgeToRetainedEdge
          (rowSiteData rotation minimal ordered row slot second)
          edge (hretained second)) := by
  let observe := fun (index : Fin 9)
      (coloring : NineSiteTaitColoringAt
        (rotation := rotation) (minimal := minimal) (ordered := ordered)
        row slot index) ↦
    coloring.1 (ambientEdgeToRetainedEdge
      (rowSiteData rotation minimal ordered row slot index)
      edge (hretained index))
  have hobserve : ∀ (index : Fin 8)
      (source : NineSiteTaitColoringAt
        (rotation := rotation) (minimal := minimal) (ordered := ordered)
        row slot index.castSucc)
      (target : NineSiteTaitColoringAt
        (rotation := rotation) (minimal := minimal) (ordered := ordered)
        row slot index.succ),
      ConsecutiveCommonCoreRepairCompatible
          rotation minimal ordered row slot index source target →
        observe index.castSucc source = observe index.succ target := by
    intro index source target hcompatible
    exact (commonCoreAgrees_iff_ambient
      (rowSiteData rotation minimal ordered row slot index.castSucc)
      (rowSiteData rotation minimal ordered row slot index.succ)
      source.1 target.1).1 hcompatible.2 edge
        (hretained index.castSucc) (hretained index.succ)
  have hfirst := PathConstraint.section_observe_eq_last
    pathSection observe hobserve first
  have hsecond := PathConstraint.section_observe_eq_last
    pathSection observe hobserve second
  exact hfirst.trans hsecond.symm

/-- Complete one path colouring to an ambient perfect matching by choosing a
Tait colour absent from its four boundary requests. -/
noncomputable def pathDeletionMatchingState
    (row : Fin a) (slot : Fin 9 ↪ Fin n)
    (pathSection : PathConstraint.Section
      (fun index : Fin 9 ↦ NineSiteTaitColoringAt
        (rotation := rotation) (minimal := minimal) (ordered := ordered)
        row slot index)
      (ConsecutiveCommonCoreRepairCompatible
        rotation minimal ordered row slot))
    (index : Fin 9) :
    DeletionMatchingState
      (rowSiteData rotation minimal ordered row slot index) := by
  have hnot : ¬ TaitColorable G :=
    graphBackedVertexMinimalTaitCounterexample_not_graphTaitColorable
      rotation minimal
  have hsame :=
    GoertzelV24AdjacentPairInsertion.AdjacentPairData.sameSidePairs_of_not_taitColorable
      (rowSiteData rotation minimal ordered row slot index)
      (Compositional.ResidualSiteProvenance.incidentEdgeFinset_card_eq_three
        rotation minimal)
      hnot (pathSection.state index).1 (pathSection.state index).2
  let hexists := exists_taitColor_absent_of_sameSidePairs
    ((rowSiteData rotation minimal ordered row slot index).degreeTwoBoundaryData.colorWord
      (pathSection.state index).1)
    hsame.1 hsame.2
  let absentColor := Classical.choose hexists
  have habsent := Classical.choose_spec hexists
  exact {
    coloring := (pathSection.state index).1
    isTait := (pathSection.state index).2
    absentColor := absentColor
    absentAtBoundary := habsent }

@[simp] theorem pathDeletionMatchingState_coloring
    (row : Fin a) (slot : Fin 9 ↪ Fin n)
    (pathSection : PathConstraint.Section
      (fun index : Fin 9 ↦ NineSiteTaitColoringAt
        (rotation := rotation) (minimal := minimal) (ordered := ordered)
        row slot index)
      (ConsecutiveCommonCoreRepairCompatible
        rotation minimal ordered row slot))
    (index : Fin 9) :
    (pathDeletionMatchingState rotation minimal ordered row slot
      pathSection index).coloring = (pathSection.state index).1 := by
  rfl

@[simp] theorem pathDeletionMatchingState_isTait
    (row : Fin a) (slot : Fin 9 ↪ Fin n)
    (pathSection : PathConstraint.Section
      (fun index : Fin 9 ↦ NineSiteTaitColoringAt
        (rotation := rotation) (minimal := minimal) (ordered := ordered)
        row slot index)
      (ConsecutiveCommonCoreRepairCompatible
        rotation minimal ordered row slot))
    (index : Fin 9) :
    (pathDeletionMatchingState rotation minimal ordered row slot
      pathSection index).isTait = (pathSection.state index).2 := by
  rfl

/-- Among the nine completed path colourings, two use the same absent Tait
colour. -/
theorem exists_pair_pathDeletionMatchingState_absentColor_eq
    (row : Fin a) (slot : Fin 9 ↪ Fin n)
    (pathSection : PathConstraint.Section
      (fun index : Fin 9 ↦ NineSiteTaitColoringAt
        (rotation := rotation) (minimal := minimal) (ordered := ordered)
        row slot index)
      (ConsecutiveCommonCoreRepairCompatible
        rotation minimal ordered row slot)) :
    ∃ first second : Fin 9, first ≠ second ∧
      (pathDeletionMatchingState rotation minimal ordered row slot
        pathSection first).absentColor =
      (pathDeletionMatchingState rotation minimal ordered row slot
        pathSection second).absentColor := by
  exact Fintype.exists_ne_map_eq_of_card_lt
    (fun index : Fin 9 ↦
      (pathDeletionMatchingState rotation minimal ordered row slot
        pathSection index).absentColor)
    (by decide)

/-- Two equal-absent-colour completions selected from the path make identical
matching decisions outside the union of the nine deletion footprints. -/
theorem exists_pair_pathDeletionMatchings_agree_outside_footprint
    (row : Fin a) (slot : Fin 9 ↪ Fin n)
    (pathSection : PathConstraint.Section
      (fun index : Fin 9 ↦ NineSiteTaitColoringAt
        (rotation := rotation) (minimal := minimal) (ordered := ordered)
        row slot index)
      (ConsecutiveCommonCoreRepairCompatible
        rotation minimal ordered row slot)) :
    ∃ first second : Fin 9, first ≠ second ∧
      ∀ edge : G.edgeSet,
        edge ∉ commonCoreRepairPathFootprint
            rotation minimal ordered row slot →
          (edge.1 ∈ edges
              ((pathDeletionMatchingState rotation minimal ordered row slot
                pathSection first).pairing
                (Compositional.ResidualSiteProvenance.incidentEdgeFinset_card_eq_three
                  rotation minimal)).toPerm ↔
            edge.1 ∈ edges
              ((pathDeletionMatchingState rotation minimal ordered row slot
                pathSection second).pairing
                (Compositional.ResidualSiteProvenance.incidentEdgeFinset_card_eq_three
                  rotation minimal)).toPerm) := by
  obtain ⟨first, second, hne, habsent⟩ :=
    exists_pair_pathDeletionMatchingState_absentColor_eq
      rotation minimal ordered row slot pathSection
  refine ⟨first, second, hne, ?_⟩
  intro edge houtside
  have hretained : ∀ index : Fin 9,
      IsRetainedAmbientEdge
        (rowSiteData rotation minimal ordered row slot index) edge := by
    intro index
    by_contra hnot
    apply houtside
    exact Finset.mem_biUnion.2
      ⟨index, Finset.mem_univ _, (mem_deletionFootprint_iff _ _).2 hnot⟩
  have hcolor := commonCoreColor_eq
    rotation minimal ordered row slot pathSection edge hretained first second
  simp only [DeletionMatchingState.pairing]
  rw [centralCompletionPairing_mem_retainedEdge_iff
    (rowSiteData rotation minimal ordered row slot first)
    (Compositional.ResidualSiteProvenance.incidentEdgeFinset_card_eq_three
      rotation minimal)
    (pathDeletionMatchingState rotation minimal ordered row slot
      pathSection first).coloring
    (pathDeletionMatchingState rotation minimal ordered row slot
      pathSection first).isTait
    (pathDeletionMatchingState rotation minimal ordered row slot
      pathSection first).absentColor
    (pathDeletionMatchingState rotation minimal ordered row slot
      pathSection first).absentAtBoundary edge (hretained first)]
  rw [centralCompletionPairing_mem_retainedEdge_iff
    (rowSiteData rotation minimal ordered row slot second)
    (Compositional.ResidualSiteProvenance.incidentEdgeFinset_card_eq_three
      rotation minimal)
    (pathDeletionMatchingState rotation minimal ordered row slot
      pathSection second).coloring
    (pathDeletionMatchingState rotation minimal ordered row slot
      pathSection second).isTait
    (pathDeletionMatchingState rotation minimal ordered row slot
      pathSection second).absentColor
    (pathDeletionMatchingState rotation minimal ordered row slot
      pathSection second).absentAtBoundary edge (hretained second)]
  simp only [pathDeletionMatchingState_coloring]
  rw [hcolor, habsent]

/-- Taking symmetric difference with any fixed supported matching preserves
the forty-five-edge endpoint bound. -/
theorem exists_pair_pathAlternatingGraph_edgeDisagreement_le
    (row : Fin a) (slot : Fin 9 ↪ Fin n)
    (pathSection : PathConstraint.Section
      (fun index : Fin 9 ↦ NineSiteTaitColoringAt
        (rotation := rotation) (minimal := minimal) (ordered := ordered)
        row slot index)
      (ConsecutiveCommonCoreRepairCompatible
        rotation minimal ordered row slot))
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G) :
    ∃ first second : Fin 9, first ≠ second ∧
      (SimpleGraph.edgeDisagreementFinset
        (alternatingGraph sigma
          ((pathDeletionMatchingState rotation minimal ordered row slot
            pathSection first).pairing
            (Compositional.ResidualSiteProvenance.incidentEdgeFinset_card_eq_three
              rotation minimal)))
        (alternatingGraph sigma
          ((pathDeletionMatchingState rotation minimal ordered row slot
            pathSection second).pairing
            (Compositional.ResidualSiteProvenance.incidentEdgeFinset_card_eq_three
              rotation minimal)))).card ≤ 45 := by
  obtain ⟨first, second, hne, hagrees⟩ :=
    exists_pair_pathDeletionMatchings_agree_outside_footprint
      rotation minimal ordered row slot pathSection
  refine ⟨first, second, hne, ?_⟩
  let hcubic :=
    Compositional.ResidualSiteProvenance.incidentEdgeFinset_card_eq_three
      rotation minimal
  calc
    _ ≤ (commonCoreRepairPathFootprint
        rotation minimal ordered row slot).card :=
      card_alternatingGraph_edgeDisagreement_le_of_pairings_agree_outside
        sigma
        ((pathDeletionMatchingState rotation minimal ordered row slot
          pathSection first).pairing hcubic)
        ((pathDeletionMatchingState rotation minimal ordered row slot
          pathSection second).pairing hcubic)
        hSigma
        ((pathDeletionMatchingState rotation minimal ordered row slot
          pathSection first).pairing_supported hcubic)
        ((pathDeletionMatchingState rotation minimal ordered row slot
          pathSection second).pairing_supported hcubic)
        (commonCoreRepairPathFootprint rotation minimal ordered row slot)
        hagrees
    _ ≤ 45 := card_commonCoreRepairPathFootprint_le
      rotation minimal ordered row slot

end

end OrderedMeshCommonCorePathSection

end Mettapedia.GraphTheory.FourColor
