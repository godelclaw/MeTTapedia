import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairOverlapKempeState
import Mettapedia.GraphTheory.FourColor.GoertzelV24SimpleGraphTaitBridge

/-!
# Gluing an atlas of adjacent-pair deletion colourings

An adjacent-pair deletion colouring is a partial colouring of the ambient
graph: it assigns colours exactly to the edges not incident with the deleted
pair.  This file gives the exact local-to-global consumer for a coherent
family of such partial colourings.

If the family covers every ambient edge, covers both ends of every adjacency
in the line graph, and assigns the same colour wherever two patches overlap,
then the partial colourings glue to an ambient Tait colouring.  Consequently
no such atlas exists in a graph-backed minimal Tait counterexample.

The theorem is independent of meshes.  A wall-facing argument must now
produce or obstruct the three explicit atlas fields rather than infer a
global colouring from pairwise nonempty finite-state relations.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24AdjacentPairColoringAtlas

open GoertzelV24AdjacentPairBoundary
open GoertzelV24AdjacentPairInsertion
open GoertzelV24AdjacentPairInsertion.AdjacentPairData
open GoertzelV24SimpleGraphTaitBridge
open GoertzelV24TwoEdgeCutMinimality
open SimpleGraph
open SimpleGraphDartRotation

noncomputable section

universe u w

variable {V : Type u} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

/-- The common four-vertex deletion embeds directly into the ambient graph. -/
def commonCoreToAmbientEmbedding
    (source target : AdjacentPairData G) :
    DeletedTwoPairsGraph G source.firstVertex source.secondVertex
        target.firstVertex target.secondVertex ↪g G where
  toFun vertex := vertex.1
  inj' left right heq := Subtype.ext heq
  map_rel_iff' := Iff.rfl

/-- An ambient edge retained by two deletion patches, regarded as an edge of
their exact common four-vertex deletion. -/
def ambientEdgeToCommonCoreEdge
    (source target : AdjacentPairData G) (edge : G.edgeSet)
    (hsource : IsRetainedAmbientEdge source edge)
    (htarget : IsRetainedAmbientEdge target edge) :
    (DeletedTwoPairsGraph G source.firstVertex source.secondVertex
      target.firstVertex target.secondVertex).edgeSet :=
  let hendpoints : ∀ vertex ∈ (edge.1 : Sym2 V),
      vertex ∈ {vertex : V |
        vertex ≠ source.firstVertex ∧ vertex ≠ source.secondVertex ∧
          vertex ≠ target.firstVertex ∧ vertex ≠ target.secondVertex} :=
    fun vertex hvertex =>
      ⟨(endpoints_mem_retainedVertexSet source edge hsource vertex hvertex).1,
        (endpoints_mem_retainedVertexSet source edge hsource vertex hvertex).2,
        (endpoints_mem_retainedVertexSet target edge htarget vertex hvertex).1,
        (endpoints_mem_retainedVertexSet target edge htarget vertex hvertex).2⟩
  ⟨edge.1.attachWith hendpoints, by
    apply ((commonCoreToAmbientEmbedding source target).map_mem_edgeSet_iff).1
    rw [show (edge.1.attachWith hendpoints).map
        (commonCoreToAmbientEmbedding source target) = edge.1 by
      change (edge.1.attachWith hendpoints).map Subtype.val = edge.1
      exact Sym2.attachWith_map_subtypeVal hendpoints]
    exact edge.2⟩

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
theorem firstCommonCoreEdge_eq_retainedEdge
    (source target : AdjacentPairData G) (edge : G.edgeSet)
    (hsource : IsRetainedAmbientEdge source edge)
    (htarget : IsRetainedAmbientEdge target edge) :
    (deletedTwoPairsToFirstDeletionEmbedding G source.firstVertex
        source.secondVertex target.firstVertex target.secondVertex).mapEdgeSet
        (ambientEdgeToCommonCoreEdge source target edge hsource htarget) =
      ambientEdgeToRetainedEdge source edge hsource := by
  apply Subtype.ext
  rcases edge with ⟨edge, hedge⟩
  induction edge using Sym2.inductionOn with
  | _ left right => rfl

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
theorem secondCommonCoreEdge_eq_retainedEdge
    (source target : AdjacentPairData G) (edge : G.edgeSet)
    (hsource : IsRetainedAmbientEdge source edge)
    (htarget : IsRetainedAmbientEdge target edge) :
    (deletedTwoPairsToSecondDeletionEmbedding G source.firstVertex
        source.secondVertex target.firstVertex target.secondVertex).mapEdgeSet
        (ambientEdgeToCommonCoreEdge source target edge hsource htarget) =
      ambientEdgeToRetainedEdge target edge htarget := by
  apply Subtype.ext
  rcases edge with ⟨edge, hedge⟩
  induction edge using Sym2.inductionOn with
  | _ left right => rfl

/-- The Boolean overlap coordinate is true exactly when the two colourings
are equal on their common four-vertex deletion. -/
theorem commonRestrictionAgreementBit_eq_true_iff
    (source target : AdjacentPairData G)
    (sourceColoring : (DeletedAdjacentPairGraph G source.firstVertex
      source.secondVertex).EdgeColoring Color)
    (targetColoring : (DeletedAdjacentPairGraph G target.firstVertex
      target.secondVertex).EdgeColoring Color) :
    commonRestrictionAgreementBit source target sourceColoring targetColoring =
        true ↔
      firstDeletionCommonCoreColoring
          (third := target.firstVertex) (fourth := target.secondVertex)
          sourceColoring =
        secondDeletionCommonCoreColoring
          (first := source.firstVertex) (second := source.secondVertex)
          targetColoring := by
  simp [commonRestrictionAgreementBit]

omit [Fintype V] [DecidableRel G.Adj] in
/-- An ambient edge survives an adjacent-pair deletion whenever neither
deleted vertex is one of its endpoints. -/
theorem isRetainedAmbientEdge_of_deleted_vertices_not_mem
    (data : AdjacentPairData G) (edge : G.edgeSet)
    (hfirst : data.firstVertex ∉ edge.1.toFinset)
    (hsecond : data.secondVertex ∉ edge.1.toFinset) :
    IsRetainedAmbientEdge data edge := by
  by_contra hnot
  rcases (not_isRetainedAmbientEdge_iff data edge).1 hnot with
    hcentral | ⟨port, hport⟩
  · apply hfirst
    apply Sym2.mem_toFinset.mpr
    rw [hcentral, centralEdgeValue]
    exact Sym2.mem_mk_left _ _
  · fin_cases port
    · apply hfirst
      apply Sym2.mem_toFinset.mpr
      rw [hport, boundaryEdgeValue]
      exact Sym2.mem_mk_left _ _
    · apply hfirst
      apply Sym2.mem_toFinset.mpr
      rw [hport, boundaryEdgeValue]
      exact Sym2.mem_mk_left _ _
    · apply hsecond
      apply Sym2.mem_toFinset.mpr
      rw [hport, boundaryEdgeValue]
      exact Sym2.mem_mk_left _ _
    · apply hsecond
      apply Sym2.mem_toFinset.mpr
      rw [hport, boundaryEdgeValue]
      exact Sym2.mem_mk_left _ _

/-- A true common-restriction coordinate forces literal colour agreement on
every ambient edge retained by both deletion patches. -/
theorem coloring_eq_on_common_retained_edge
    (source target : AdjacentPairData G)
    (sourceColoring : (DeletedAdjacentPairGraph G source.firstVertex
      source.secondVertex).EdgeColoring Color)
    (targetColoring : (DeletedAdjacentPairGraph G target.firstVertex
      target.secondVertex).EdgeColoring Color)
    (edge : G.edgeSet)
    (hsource : IsRetainedAmbientEdge source edge)
    (htarget : IsRetainedAmbientEdge target edge)
    (hagrees : commonRestrictionAgreementBit source target sourceColoring
      targetColoring = true) :
    sourceColoring (ambientEdgeToRetainedEdge source edge hsource) =
      targetColoring (ambientEdgeToRetainedEdge target edge htarget) := by
  have hcommon :=
    (commonRestrictionAgreementBit_eq_true_iff source target sourceColoring
      targetColoring).1 hagrees
  have heval := congrArg
    (fun coloring => coloring
      (ambientEdgeToCommonCoreEdge source target edge hsource htarget)) hcommon
  simpa only [firstDeletionCommonCoreColoring,
    secondDeletionCommonCoreColoring,
    SimpleGraph.EdgeColoring.pullbackEmbedding_apply,
    firstCommonCoreEdge_eq_retainedEdge,
    secondCommonCoreEdge_eq_retainedEdge] using heval

/-- A family of proper nonzero colourings of adjacent-pair deletions. -/
structure PairDeletionColoringFamily (I : Type w) where
  data : I → AdjacentPairData G
  coloring : ∀ index,
    (DeletedAdjacentPairGraph G (data index).firstVertex
      (data index).secondVertex).EdgeColoring Color
  tait : ∀ index,
    IsTaitEdgeColoring
      (DeletedAdjacentPairGraph G (data index).firstVertex
        (data index).secondVertex)
      (coloring index)

namespace PairDeletionColoringFamily

variable {I : Type w} (family : PairDeletionColoringFamily (G := G) I)

/-- The colour assigned to a retained ambient edge by one deletion patch. -/
def ambientColor (index : I) (edge : G.edgeSet)
    (hretained : IsRetainedAmbientEdge (family.data index) edge) : Color :=
  family.coloring index
    (ambientEdgeToRetainedEdge (family.data index) edge hretained)

/-- Every ambient edge occurs in at least one deletion patch. -/
def CoversEdges : Prop :=
  ∀ edge : G.edgeSet, ∃ index : I,
    IsRetainedAmbientEdge (family.data index) edge

/-- Every adjacent pair of ambient edges occurs together in one patch.
This is the exact coverage needed to verify properness after gluing. -/
def CoversAdjacentEdges : Prop :=
  ∀ first second : G.edgeSet,
    G.lineGraph.Adj first second →
      ∃ index : I,
        IsRetainedAmbientEdge (family.data index) first ∧
          IsRetainedAmbientEdge (family.data index) second

/-- Two patches give the same colour to every ambient edge retained by
both. -/
def PairwiseAgrees : Prop :=
  ∀ (first second : I) (edge : G.edgeSet)
    (hfirst : IsRetainedAmbientEdge (family.data first) edge)
    (hsecond : IsRetainedAmbientEdge (family.data second) edge),
      family.ambientColor first edge hfirst =
        family.ambientColor second edge hsecond

/-- Every pair of selected patch colourings has true agreement coordinate
on its exact common deletion. -/
def PairwiseCommonRestrictionAgrees : Prop :=
  ∀ first second : I,
    commonRestrictionAgreementBit (family.data first) (family.data second)
      (family.coloring first) (family.coloring second) = true

/-- Agreement of every common-restriction bit supplies the overlap coherence
required by the atlas gluing theorem. -/
theorem pairwiseAgrees_of_commonRestrictionAgrees
    (agreement : family.PairwiseCommonRestrictionAgrees) :
    family.PairwiseAgrees := by
  intro first second edge hfirst hsecond
  exact coloring_eq_on_common_retained_edge
    (family.data first) (family.data second)
    (family.coloring first) (family.coloring second)
    edge hfirst hsecond (agreement first second)

variable (cover : family.CoversEdges)

/-- Choose one patch containing each ambient edge.  The gluing theorem proves
that the resulting colour is independent of this choice. -/
noncomputable def selectedIndex (edge : G.edgeSet) : I :=
  Classical.choose (cover edge)

theorem selectedIndex_retains (edge : G.edgeSet) :
    IsRetainedAmbientEdge
      (family.data (family.selectedIndex cover edge)) edge :=
  Classical.choose_spec (cover edge)

/-- The ambient edge colour obtained from a selected covering patch. -/
noncomputable def gluedColorFunction (edge : G.edgeSet) : Color :=
  family.ambientColor (family.selectedIndex cover edge) edge
    (family.selectedIndex_retains cover edge)

/-- Pairwise agreement makes the selected ambient colour equal to the
colour read from any other patch containing the edge. -/
theorem gluedColorFunction_eq_ambientColor
    (agreement : family.PairwiseAgrees)
    (index : I) (edge : G.edgeSet)
    (hretained : IsRetainedAmbientEdge (family.data index) edge) :
    family.gluedColorFunction cover edge =
      family.ambientColor index edge hretained :=
  agreement (family.selectedIndex cover edge) index edge
    (family.selectedIndex_retains cover edge) hretained

/-- Gluing a coherent covering family gives a proper ambient edge
colouring. -/
noncomputable def gluedColoring
    (adjacentCover : family.CoversAdjacentEdges)
    (agreement : family.PairwiseAgrees) : G.EdgeColoring Color :=
  SimpleGraph.Coloring.mk (family.gluedColorFunction cover) (by
    intro first second hadjacent
    rcases adjacentCover first second hadjacent with
      ⟨index, hfirst, hsecond⟩
    have hlocalAdjacent := ambientEdgeToRetainedEdge_adj
      (family.data index) first second hfirst hsecond hadjacent
    have hlocalNe := (family.coloring index).valid hlocalAdjacent
    intro hequal
    apply hlocalNe
    calc
      family.coloring index
          (ambientEdgeToRetainedEdge (family.data index) first hfirst) =
          family.gluedColorFunction cover first := by
            exact (family.gluedColorFunction_eq_ambientColor cover
              agreement index first hfirst).symm
      _ = family.gluedColorFunction cover second := hequal
      _ = family.coloring index
          (ambientEdgeToRetainedEdge (family.data index) second hsecond) := by
            exact family.gluedColorFunction_eq_ambientColor cover
              agreement index second hsecond)

/-- The glued proper colouring is nonzero on every ambient edge. -/
theorem gluedColoring_isTait
    (adjacentCover : family.CoversAdjacentEdges)
    (agreement : family.PairwiseAgrees) :
    IsTaitEdgeColoring G
      (family.gluedColoring cover adjacentCover agreement) := by
  intro edge
  change family.gluedColorFunction cover edge ≠ 0
  exact family.tait (family.selectedIndex cover edge)
    (ambientEdgeToRetainedEdge
      (family.data (family.selectedIndex cover edge)) edge
      (family.selectedIndex_retains cover edge))

/-- A coherent covering atlas cannot occur in a graph-backed minimal Tait
counterexample: its glued colouring contradicts ambient noncolourability. -/
theorem not_pairwiseAgrees_of_minimal
    (rotation : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    (cover : family.CoversEdges)
    (adjacentCover : family.CoversAdjacentEdges) :
    ¬ family.PairwiseAgrees := by
  intro agreement
  exact
    (graphBackedVertexMinimalTaitCounterexample_not_graphTaitColorable
      rotation minimal)
      ⟨family.gluedColoring cover adjacentCover agreement,
        family.gluedColoring_isTait cover adjacentCover agreement⟩

/-- In a graph-backed minimal Tait counterexample, any deletion-colouring
atlas covering ambient adjacencies has a pair whose finite common-restriction
coordinate is false. -/
theorem not_pairwiseCommonRestrictionAgrees_of_minimal
    (rotation : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    (cover : family.CoversEdges)
    (adjacentCover : family.CoversAdjacentEdges) :
    ¬ family.PairwiseCommonRestrictionAgrees := by
  intro agreement
  exact family.not_pairwiseAgrees_of_minimal rotation minimal cover
    adjacentCover (family.pairwiseAgrees_of_commonRestrictionAgrees agreement)

end PairDeletionColoringFamily

end

end GoertzelV24AdjacentPairColoringAtlas

end Mettapedia.GraphTheory.FourColor
