import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairColoringAtlas

/-!
# Localizing a failure of transitivity between adjacent-pair deletions

Literal common-core agreement is symmetric, but it need not be transitive:
three deletion patches have three different pairwise common carriers.  The
failure is nevertheless geometrically local.  If the first and middle
colourings agree, and the middle and last colourings agree, then the first
and last colourings agree on every edge retained by all three patches.
Consequently any first--last disagreement has a witness edge deleted by the
middle patch.

This is a generic statement about partial edge colourings.  It uses neither
planarity nor minimality, and it does not assert wall exclusion or construct
a replacement.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24AdjacentPairCommonCoreLocalization

open GoertzelV24AdjacentPairBoundary
open GoertzelV24AdjacentPairInsertion
open GoertzelV24AdjacentPairInsertion.AdjacentPairData
open GoertzelV24AdjacentPairColoringAtlas
open SimpleGraph

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

/-- An edge of the exact common deletion, regarded as an ambient edge. -/
def commonCoreEdgeToAmbientEdge
    (source target : AdjacentPairData G)
    (edge : (DeletedTwoPairsGraph G source.firstVertex source.secondVertex
      target.firstVertex target.secondVertex).edgeSet) : G.edgeSet :=
  (commonCoreToAmbientEmbedding source target).mapEdgeSet edge

omit [Fintype V] [DecidableRel G.Adj] in
/-- A common-core edge is retained by the first deletion patch. -/
theorem commonCoreEdgeToAmbientEdge_source_retained
    (source target : AdjacentPairData G)
    (edge : (DeletedTwoPairsGraph G source.firstVertex source.secondVertex
      target.firstVertex target.secondVertex).edgeSet) :
    IsRetainedAmbientEdge source
      (commonCoreEdgeToAmbientEdge source target edge) := by
  apply isRetainedAmbientEdge_of_deleted_vertices_not_mem
  · rcases edge with ⟨edge, hedge⟩
    induction edge using Sym2.inductionOn with
    | _ left right =>
      change source.firstVertex ∉
        (s(left.1, right.1) : Sym2 V).toFinset
      simp only [Sym2.mem_toFinset, Sym2.mem_iff]
      rintro (heq | heq)
      · exact left.property.1 heq.symm
      · exact right.property.1 heq.symm
  · rcases edge with ⟨edge, hedge⟩
    induction edge using Sym2.inductionOn with
    | _ left right =>
      change source.secondVertex ∉
        (s(left.1, right.1) : Sym2 V).toFinset
      simp only [Sym2.mem_toFinset, Sym2.mem_iff]
      rintro (heq | heq)
      · exact left.property.2.1 heq.symm
      · exact right.property.2.1 heq.symm

omit [Fintype V] [DecidableRel G.Adj] in
/-- A common-core edge is retained by the second deletion patch. -/
theorem commonCoreEdgeToAmbientEdge_target_retained
    (source target : AdjacentPairData G)
    (edge : (DeletedTwoPairsGraph G source.firstVertex source.secondVertex
      target.firstVertex target.secondVertex).edgeSet) :
    IsRetainedAmbientEdge target
      (commonCoreEdgeToAmbientEdge source target edge) := by
  apply isRetainedAmbientEdge_of_deleted_vertices_not_mem
  · rcases edge with ⟨edge, hedge⟩
    induction edge using Sym2.inductionOn with
    | _ left right =>
      change target.firstVertex ∉
        (s(left.1, right.1) : Sym2 V).toFinset
      simp only [Sym2.mem_toFinset, Sym2.mem_iff]
      rintro (heq | heq)
      · exact left.property.2.2.1 heq.symm
      · exact right.property.2.2.1 heq.symm
  · rcases edge with ⟨edge, hedge⟩
    induction edge using Sym2.inductionOn with
    | _ left right =>
      change target.secondVertex ∉
        (s(left.1, right.1) : Sym2 V).toFinset
      simp only [Sym2.mem_toFinset, Sym2.mem_iff]
      rintro (heq | heq)
      · exact left.property.2.2.2 heq.symm
      · exact right.property.2.2.2 heq.symm

omit [Fintype V] [DecidableRel G.Adj] in
/-- Converting a common-core edge through the first deletion gives the same
retained edge as converting its ambient image. -/
theorem firstCommonCoreEdge_eq_ambientRetainedEdge
    (source target : AdjacentPairData G)
    (edge : (DeletedTwoPairsGraph G source.firstVertex source.secondVertex
      target.firstVertex target.secondVertex).edgeSet) :
    (deletedTwoPairsToFirstDeletionEmbedding G source.firstVertex
        source.secondVertex target.firstVertex target.secondVertex).mapEdgeSet
        edge =
      ambientEdgeToRetainedEdge source
        (commonCoreEdgeToAmbientEdge source target edge)
        (commonCoreEdgeToAmbientEdge_source_retained source target edge) := by
  apply Subtype.ext
  rcases edge with ⟨edge, hedge⟩
  induction edge using Sym2.inductionOn with
  | _ left right => rfl

omit [Fintype V] [DecidableRel G.Adj] in
/-- Converting a common-core edge through the second deletion gives the same
retained edge as converting its ambient image. -/
theorem secondCommonCoreEdge_eq_ambientRetainedEdge
    (source target : AdjacentPairData G)
    (edge : (DeletedTwoPairsGraph G source.firstVertex source.secondVertex
      target.firstVertex target.secondVertex).edgeSet) :
    (deletedTwoPairsToSecondDeletionEmbedding G source.firstVertex
        source.secondVertex target.firstVertex target.secondVertex).mapEdgeSet
        edge =
      ambientEdgeToRetainedEdge target
        (commonCoreEdgeToAmbientEdge source target edge)
        (commonCoreEdgeToAmbientEdge_target_retained source target edge) := by
  apply Subtype.ext
  rcases edge with ⟨edge, hedge⟩
  induction edge using Sym2.inductionOn with
  | _ left right => rfl

/-- Literal equality of the two restrictions to their exact common deletion. -/
def CommonCoreAgrees
    (source target : AdjacentPairData G)
    (sourceColoring : (DeletedAdjacentPairGraph G source.firstVertex
      source.secondVertex).EdgeColoring Color)
    (targetColoring : (DeletedAdjacentPairGraph G target.firstVertex
      target.secondVertex).EdgeColoring Color) : Prop :=
  firstDeletionCommonCoreColoring
      (third := target.firstVertex) (fourth := target.secondVertex)
      sourceColoring =
    secondDeletionCommonCoreColoring
      (first := source.firstVertex) (second := source.secondVertex)
      targetColoring

/-- Exact common-core agreement is equivalent to equality on every ambient
edge retained by both patches. -/
theorem commonCoreAgrees_iff_ambient
    (source target : AdjacentPairData G)
    (sourceColoring : (DeletedAdjacentPairGraph G source.firstVertex
      source.secondVertex).EdgeColoring Color)
    (targetColoring : (DeletedAdjacentPairGraph G target.firstVertex
      target.secondVertex).EdgeColoring Color) :
    CommonCoreAgrees source target sourceColoring targetColoring ↔
      ∀ (edge : G.edgeSet)
        (hsource : IsRetainedAmbientEdge source edge)
        (htarget : IsRetainedAmbientEdge target edge),
        sourceColoring (ambientEdgeToRetainedEdge source edge hsource) =
          targetColoring (ambientEdgeToRetainedEdge target edge htarget) := by
  constructor
  · intro hagrees edge hsource htarget
    exact coloring_eq_on_common_retained_edge source target
      sourceColoring targetColoring edge hsource htarget
      ((commonRestrictionAgreementBit_eq_true_iff
        source target sourceColoring targetColoring).2 hagrees)
  · intro hambient
    apply DFunLike.ext _ _
    intro edge
    let ambient := commonCoreEdgeToAmbientEdge source target edge
    let hsource := commonCoreEdgeToAmbientEdge_source_retained
      source target edge
    let htarget := commonCoreEdgeToAmbientEdge_target_retained
      source target edge
    have heq := hambient ambient hsource htarget
    change sourceColoring
        ((deletedTwoPairsToFirstDeletionEmbedding G source.firstVertex
          source.secondVertex target.firstVertex target.secondVertex).mapEdgeSet
          edge) =
      targetColoring
        ((deletedTwoPairsToSecondDeletionEmbedding G source.firstVertex
          source.secondVertex target.firstVertex target.secondVertex).mapEdgeSet
          edge)
    rw [firstCommonCoreEdge_eq_ambientRetainedEdge,
      secondCommonCoreEdge_eq_ambientRetainedEdge]
    exact heq

/-- Common-core agreement is symmetric, despite the two orientations using
definitionally different common-deletion carriers. -/
theorem commonCoreAgrees_symm
    (source target : AdjacentPairData G)
    (sourceColoring : (DeletedAdjacentPairGraph G source.firstVertex
      source.secondVertex).EdgeColoring Color)
    (targetColoring : (DeletedAdjacentPairGraph G target.firstVertex
      target.secondVertex).EdgeColoring Color)
    (hagrees : CommonCoreAgrees source target sourceColoring targetColoring) :
    CommonCoreAgrees target source targetColoring sourceColoring := by
  apply (commonCoreAgrees_iff_ambient target source
    targetColoring sourceColoring).2
  intro edge htarget hsource
  exact ((commonCoreAgrees_iff_ambient source target
    sourceColoring targetColoring).1 hagrees edge hsource htarget).symm

/-- A first--last disagreement is localized at a middle deletion when one
of its witness edges is deleted by that middle patch. -/
def CommonCoreDisagreementLocalizedAt
    (source middle target : AdjacentPairData G)
    (sourceColoring : (DeletedAdjacentPairGraph G source.firstVertex
      source.secondVertex).EdgeColoring Color)
    (targetColoring : (DeletedAdjacentPairGraph G target.firstVertex
      target.secondVertex).EdgeColoring Color) : Prop :=
  ∃ edge : G.edgeSet,
    ∃ hsource : IsRetainedAmbientEdge source edge,
    ∃ htarget : IsRetainedAmbientEdge target edge,
      ¬ IsRetainedAmbientEdge middle edge ∧
      sourceColoring (ambientEdgeToRetainedEdge source edge hsource) ≠
        targetColoring (ambientEdgeToRetainedEdge target edge htarget)

/-- **Three-patch localization.**  If source agrees with middle and middle
agrees with target, every source--target discrepancy is witnessed on an
edge deleted by the middle patch. -/
theorem commonCoreDisagreementLocalizedAt_of_chain
    (source middle target : AdjacentPairData G)
    (sourceColoring : (DeletedAdjacentPairGraph G source.firstVertex
      source.secondVertex).EdgeColoring Color)
    (middleColoring : (DeletedAdjacentPairGraph G middle.firstVertex
      middle.secondVertex).EdgeColoring Color)
    (targetColoring : (DeletedAdjacentPairGraph G target.firstVertex
      target.secondVertex).EdgeColoring Color)
    (hsourceMiddle : CommonCoreAgrees source middle
      sourceColoring middleColoring)
    (hmiddleTarget : CommonCoreAgrees middle target
      middleColoring targetColoring)
    (hsourceTarget : ¬ CommonCoreAgrees source target
      sourceColoring targetColoring) :
    CommonCoreDisagreementLocalizedAt source middle target
      sourceColoring targetColoring := by
  have hwitness : ∃ edge,
      firstDeletionCommonCoreColoring
          (third := target.firstVertex) (fourth := target.secondVertex)
          sourceColoring edge ≠
        secondDeletionCommonCoreColoring
          (first := source.firstVertex) (second := source.secondVertex)
          targetColoring edge := by
    by_contra hnone
    push Not at hnone
    apply hsourceTarget
    apply DFunLike.ext _ _
    exact hnone
  rcases hwitness with ⟨commonEdge, hcommonNe⟩
  let edge := commonCoreEdgeToAmbientEdge source target commonEdge
  let hsource := commonCoreEdgeToAmbientEdge_source_retained
    source target commonEdge
  let htarget := commonCoreEdgeToAmbientEdge_target_retained
    source target commonEdge
  have hambientNe :
      sourceColoring (ambientEdgeToRetainedEdge source edge hsource) ≠
        targetColoring (ambientEdgeToRetainedEdge target edge htarget) := by
    intro hambientEq
    apply hcommonNe
    change sourceColoring
        ((deletedTwoPairsToFirstDeletionEmbedding G source.firstVertex
          source.secondVertex target.firstVertex target.secondVertex).mapEdgeSet
          commonEdge) =
      targetColoring
        ((deletedTwoPairsToSecondDeletionEmbedding G source.firstVertex
          source.secondVertex target.firstVertex target.secondVertex).mapEdgeSet
          commonEdge)
    rw [firstCommonCoreEdge_eq_ambientRetainedEdge,
      secondCommonCoreEdge_eq_ambientRetainedEdge]
    exact hambientEq
  refine ⟨edge, hsource, htarget, ?_, hambientNe⟩
  intro hmiddle
  apply hambientNe
  exact ((commonCoreAgrees_iff_ambient source middle
      sourceColoring middleColoring).1 hsourceMiddle edge hsource hmiddle).trans
    ((commonCoreAgrees_iff_ambient middle target
      middleColoring targetColoring).1 hmiddleTarget edge hmiddle htarget)

end

end GoertzelV24AdjacentPairCommonCoreLocalization

end Mettapedia.GraphTheory.FourColor
