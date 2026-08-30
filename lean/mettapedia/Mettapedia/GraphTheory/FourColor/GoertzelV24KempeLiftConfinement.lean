import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairCommonCoreKempeBoundary
import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairCommonCoreLocalization

/-!
# Support confinement for lifted Kempe sequences

The common-core lift-or-boundary dichotomy previously retained only the
restriction of the lifted colouring.  In the non-boundary horn considerably
more is true: every lifted component is exactly the image of the corresponding
small component.  Hence the whole lifted sequence leaves every edge outside
the embedded graph unchanged.

This is generic graph theory.  The final theorem specializes it to the exact
common deletion of two adjacent-pair patches.  It does not assert wall
exclusion; it records the support information needed by the periodic repair
consumer.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24KempeLiftConfinement

open GoertzelV24AdjacentPairBoundary
open GoertzelV24AdjacentPairCommonCoreKempeBoundary
open GoertzelV24AdjacentPairCommonCoreLocalization
open GoertzelV24AdjacentPairInsertion
open GoertzelV24AdjacentPairInsertion.AdjacentPairData
open GoertzelV24KempeComponentEmbeddingBoundary
open GoertzelV24LocalSwapKempeGeneration
open SimpleGraph

universe u v w

variable {SmallVertex : Type u} {LargeVertex : Type v} {ColorType : Type w}
  {smallGraph : SimpleGraph SmallVertex}
  {largeGraph : SimpleGraph LargeVertex}

/-- A colouring agrees with its base on every edge outside the image of an
embedded graph. -/
def AgreesOutsideEmbedding
    (base lifted : largeGraph.EdgeColoring ColorType)
    (embedding : smallGraph ↪g largeGraph) : Prop :=
  ∀ edge, (¬ ∃ preimage, embedding.mapEdgeSet preimage = edge) →
    lifted edge = base edge

/-- A neighbour-closed connected component maps onto one whole target
component, not merely into it. -/
theorem exists_target_component_eq_image_of_neighbor_closed
    (embedding : smallGraph ↪g largeGraph)
    (component : smallGraph.ConnectedComponent)
    (hclosed : ∀ smallVertex, smallVertex ∈ component →
      ∀ largeVertex, largeGraph.Adj (embedding smallVertex) largeVertex →
        ∃ nextSmall, nextSmall ∈ component ∧
          embedding nextSmall = largeVertex) :
    ∃ targetComponent : largeGraph.ConnectedComponent,
      ∀ largeVertex, largeVertex ∈ targetComponent ↔
        ∃ smallVertex, smallVertex ∈ component ∧
          embedding smallVertex = largeVertex := by
  rcases component.nonempty_supp with ⟨root, hroot⟩
  let targetComponent := largeGraph.connectedComponentMk (embedding root)
  refine ⟨targetComponent, fun largeVertex => ?_⟩
  constructor
  · intro htarget
    have hreachable : largeGraph.Reachable
        (embedding root) largeVertex := by
      apply ConnectedComponent.exact
      exact htarget.symm
    rcases hreachable with ⟨walk⟩
    let imageOfComponent : LargeVertex → Prop := fun vertex =>
      ∃ sourceVertex, sourceVertex ∈ component ∧
        embedding sourceVertex = vertex
    have hrootImage : imageOfComponent (embedding root) :=
      ⟨root, hroot, rfl⟩
    have himageClosed : ∀ {left right}, imageOfComponent left →
        largeGraph.Adj left right → imageOfComponent right := by
      rintro left right ⟨sourceVertex, hsource, rfl⟩ hadj
      exact hclosed sourceVertex hsource right hadj
    exact Walk.end_mem_of_start_mem_of_adj_closed
      walk imageOfComponent hrootImage himageClosed
  · rintro ⟨smallVertex, hsmall, rfl⟩
    have hreachable : smallGraph.Reachable root smallVertex :=
      component.reachable_of_mem_supp hroot hsmall
    have hmapped : largeGraph.Reachable
        (embedding root) (embedding smallVertex) :=
      hreachable.map embedding.toHom
    exact ConnectedComponent.sound hmapped |>.symm

variable [DecidableEq ColorType]

/-- **One-step confinement.**  A small Kempe component either reaches the
embedding boundary, or its lifted switch has the required restriction and
changes no edge outside the embedded graph. -/
theorem touchesBoundary_or_exists_liftedComponentSwitch_confined
    (coloring : largeGraph.EdgeColoring ColorType)
    (embedding : smallGraph ↪g largeGraph)
    (first second : ColorType)
    (component : ((coloring.pullbackEmbedding embedding).bicoloredSubgraph
      first second).ConnectedComponent) :
    ComponentTouchesEmbeddingBoundary coloring embedding first second component ∨
      ∃ targetComponent :
          (coloring.bicoloredSubgraph first second).ConnectedComponent,
        SimpleGraph.EdgeColoring.pullbackEmbedding
            (coloring.swapOnKempeComponent first second targetComponent)
            embedding =
          (coloring.pullbackEmbedding embedding).swapOnKempeComponent
            first second component ∧
        AgreesOutsideEmbedding coloring
          (coloring.swapOnKempeComponent first second targetComponent)
          embedding := by
  by_cases hboundary : ComponentTouchesEmbeddingBoundary coloring embedding
      first second component
  · exact Or.inl hboundary
  · right
    obtain ⟨targetComponent, htargetImage⟩ :=
      exists_target_component_eq_image_of_neighbor_closed
        (bicoloredSubgraphEmbedding coloring embedding first second)
        component
        (bicolored_image_neighbor_closed_of_not_touchesBoundary
          coloring embedding first second component hboundary)
    refine ⟨targetComponent, ?_, ?_⟩
    · apply DFunLike.ext _ _
      intro edge
      have hmembership : edge ∈
            (coloring.pullbackEmbedding embedding).kempeComponentSet
              first second component ↔
          embedding.mapEdgeSet edge ∈
            coloring.kempeComponentSet first second targetComponent := by
        constructor
        · rintro ⟨hselected, hedge⟩
          refine ⟨hselected, (htargetImage
            ⟨embedding.mapEdgeSet edge, hselected⟩).2 ?_⟩
          exact ⟨⟨edge, hselected⟩, hedge, rfl⟩
        · rintro ⟨hselected, hedge⟩
          rcases (htargetImage
              ⟨embedding.mapEdgeSet edge, hselected⟩).1 hedge with
            ⟨smallEdge, hsmall, hmap⟩
          have hvalue : smallEdge.1 = edge :=
            embedding.mapEdgeSet.injective (congrArg Subtype.val hmap)
          have hsmallSelected : edge ∈
              (coloring.pullbackEmbedding embedding).bicoloredSet
                first second := hselected
          have hsmallEdgeEq : smallEdge = ⟨edge, hsmallSelected⟩ :=
            Subtype.ext hvalue
          exact ⟨hsmallSelected, hsmallEdgeEq ▸ hsmall⟩
      by_cases hedge : edge ∈
          (coloring.pullbackEmbedding embedding).kempeComponentSet
            first second component
      · rw [SimpleGraph.EdgeColoring.pullbackEmbedding_apply,
          coloring.swapOnKempeComponent_apply_of_mem
            (hmembership.1 hedge),
          SimpleGraph.Coloring.swapOnKempeComponent_apply_of_mem
            (coloring.pullbackEmbedding embedding) hedge]
        rfl
      · rw [SimpleGraph.EdgeColoring.pullbackEmbedding_apply,
          coloring.swapOnKempeComponent_apply_of_not_mem
            (fun hmember => hedge (hmembership.2 hmember)),
          SimpleGraph.Coloring.swapOnKempeComponent_apply_of_not_mem
            (coloring.pullbackEmbedding embedding) hedge]
        rfl
    · intro edge houtside
      apply coloring.swapOnKempeComponent_apply_of_not_mem
      intro hmember
      rcases hmember with ⟨hselected, htarget⟩
      rcases (htargetImage ⟨edge, hselected⟩).1 htarget with
        ⟨smallEdge, _hsmall, hmap⟩
      apply houtside
      exact ⟨smallEdge.1, congrArg Subtype.val hmap⟩

/-- **Finite-sequence confinement.**  A valid-pair Tait Kempe sequence on an
embedded graph either reaches the embedding boundary, or lifts to a proper
sequence which is pointwise unchanged outside the embedding. -/
theorem taitBoundaryAlongLiftOrbit_or_exists_confinedLiftedColoring
    (base : largeGraph.EdgeColoring Color)
    (hbase : IsTaitEdgeColoring largeGraph base)
    (embedding : smallGraph ↪g largeGraph)
    (target : smallGraph.EdgeColoring Color)
    (hreachable : TaitKempeReachable
      (base.pullbackEmbedding embedding) target) :
    HasTaitBoundaryStepInLiftOrbit base embedding ∨
      ∃ lifted : largeGraph.EdgeColoring Color,
        TaitKempeReachable base lifted ∧
        IsTaitEdgeColoring largeGraph lifted ∧
        lifted.pullbackEmbedding embedding = target ∧
        AgreesOutsideEmbedding base lifted embedding := by
  induction hreachable with
  | refl =>
      right
      exact ⟨base, Relation.ReflTransGen.refl, hbase, rfl,
        fun _edge _houtside => rfl⟩
  | tail hprefix hstep ih =>
      rcases ih with
        hboundary | ⟨current, hcurrent, hcurrentTait, hrestrict, houtside⟩
      · exact Or.inl hboundary
      · rcases hstep with ⟨first, second, hpair, component, rfl⟩
        subst hrestrict
        rcases touchesBoundary_or_exists_liftedComponentSwitch_confined
            current embedding first second component with
          htouches | ⟨targetComponent, hlift, hstepOutside⟩
        · left
          exact ⟨current, hcurrent, first, second, hpair,
            component, htouches⟩
        · right
          let lifted := current.swapOnKempeComponent
            first second targetComponent
          have hlargeStep : TaitKempeStep current lifted :=
            ⟨first, second, hpair, targetComponent, rfl⟩
          have hliftedReachable : TaitKempeReachable base lifted :=
            hcurrent.tail hlargeStep
          have hliftedTait : IsTaitEdgeColoring largeGraph lifted :=
            isTaitEdgeColoring_of_taitKempeStep hcurrentTait hlargeStep
          refine ⟨lifted, hliftedReachable, hliftedTait, hlift, ?_⟩
          intro edge hedge
          exact (hstepOutside edge hedge).trans (houtside edge hedge)

noncomputable section

variable {V : Type u} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

omit [Fintype V] [DecidableRel G.Adj] in
/-- **Adjacent-pair confined lift-or-boundary dichotomy.**  In the lifted
horn, the first deletion colouring changes only on edges of the exact common
deletion. -/
theorem firstTaitOrbitReachesSecondPair_or_exists_confinedLiftedColoring
    (source target : AdjacentPairData G)
    (base : (DeletedAdjacentPairGraph G source.firstVertex
      source.secondVertex).EdgeColoring Color)
    (hbase : IsTaitEdgeColoring
      (DeletedAdjacentPairGraph G source.firstVertex source.secondVertex)
      base)
    (targetCommon :
      (DeletedTwoPairsGraph G source.firstVertex source.secondVertex
        target.firstVertex target.secondVertex).EdgeColoring Color)
    (hreachable : TaitKempeReachable
      (firstDeletionCommonCoreColoring
        (third := target.firstVertex) (fourth := target.secondVertex)
        base)
      targetCommon) :
    FirstTaitOrbitReachesSecondPair source target base ∨
      ∃ lifted,
        TaitKempeReachable base lifted ∧
        IsTaitEdgeColoring
          (DeletedAdjacentPairGraph G source.firstVertex source.secondVertex)
          lifted ∧
        firstDeletionCommonCoreColoring
          (third := target.firstVertex) (fourth := target.secondVertex)
          lifted = targetCommon ∧
        AgreesOutsideEmbedding base lifted
          (deletedTwoPairsToFirstDeletionEmbedding G source.firstVertex
            source.secondVertex target.firstVertex target.secondVertex) := by
  rcases taitBoundaryAlongLiftOrbit_or_exists_confinedLiftedColoring
      base hbase
      (deletedTwoPairsToFirstDeletionEmbedding G source.firstVertex
        source.secondVertex target.firstVertex target.secondVertex)
      targetCommon hreachable with
    hboundary | hlifted
  · left
    rcases hboundary with
      ⟨current, hcurrent, first, second, hpair, component, htouches⟩
    exact ⟨current, hcurrent, first, second, hpair, component,
      firstComponentReachesSecondPair_of_touchesEmbeddingBoundary
        source target current first second component htouches⟩
  · exact Or.inr hlifted

omit [Fintype V] [DecidableRel G.Adj] in
/-- An ambient edge retained by the first patch but deleted by the second is
outside the exact common-deletion embedding. -/
theorem not_exists_firstCommonCore_preimage_of_not_target_retained
    (source target : AdjacentPairData G)
    (edge : G.edgeSet)
    (hsource : IsRetainedAmbientEdge source edge)
    (htarget : ¬ IsRetainedAmbientEdge target edge) :
    ¬ ∃ preimage :
        (DeletedTwoPairsGraph G source.firstVertex source.secondVertex
          target.firstVertex target.secondVertex).edgeSet,
      (deletedTwoPairsToFirstDeletionEmbedding G source.firstVertex
        source.secondVertex target.firstVertex target.secondVertex).mapEdgeSet
          preimage = ambientEdgeToRetainedEdge source edge hsource := by
  rintro ⟨preimage, hmap⟩
  have hambient : commonCoreEdgeToAmbientEdge source target preimage = edge := by
    calc
      commonCoreEdgeToAmbientEdge source target preimage =
          retainedEdgeToAmbientEdge source
            ((deletedTwoPairsToFirstDeletionEmbedding G source.firstVertex
              source.secondVertex target.firstVertex
              target.secondVertex).mapEdgeSet preimage) := by
            rw [firstCommonCoreEdge_eq_ambientRetainedEdge]
            simp
      _ = retainedEdgeToAmbientEdge source
          (ambientEdgeToRetainedEdge source edge hsource) := by rw [hmap]
      _ = edge := by simp
  apply htarget
  simpa [hambient] using
    (commonCoreEdgeToAmbientEdge_target_retained source target preimage)

/-- **Agreement transport under a confined repair.**  Suppose a source
colouring is repaired only on the exact common deletion with a middle patch.
If the old source agrees with a target patch, while the repaired source agrees
with the middle and the middle agrees with the target, then the repaired
source still agrees with the target.  Edges retained by the middle use the
two new agreements; edges deleted by the middle use confinement and the old
agreement. -/
theorem commonCoreAgrees_of_confined_left_update
    (source middle target : AdjacentPairData G)
    (sourceBefore sourceAfter :
      (DeletedAdjacentPairGraph G source.firstVertex
        source.secondVertex).EdgeColoring Color)
    (middleColoring :
      (DeletedAdjacentPairGraph G middle.firstVertex
        middle.secondVertex).EdgeColoring Color)
    (targetColoring :
      (DeletedAdjacentPairGraph G target.firstVertex
        target.secondVertex).EdgeColoring Color)
    (hsourceMiddle : CommonCoreAgrees source middle
      sourceAfter middleColoring)
    (hmiddleTarget : CommonCoreAgrees middle target
      middleColoring targetColoring)
    (hsourceTargetBefore : CommonCoreAgrees source target
      sourceBefore targetColoring)
    (hconfined : AgreesOutsideEmbedding sourceBefore sourceAfter
      (deletedTwoPairsToFirstDeletionEmbedding G source.firstVertex
        source.secondVertex middle.firstVertex middle.secondVertex)) :
    CommonCoreAgrees source target sourceAfter targetColoring := by
  apply (commonCoreAgrees_iff_ambient source target
    sourceAfter targetColoring).2
  intro edge hsource htarget
  by_cases hmiddle : IsRetainedAmbientEdge middle edge
  · exact ((commonCoreAgrees_iff_ambient source middle
      sourceAfter middleColoring).1 hsourceMiddle
        edge hsource hmiddle).trans
      ((commonCoreAgrees_iff_ambient middle target
        middleColoring targetColoring).1 hmiddleTarget
          edge hmiddle htarget)
  · have houtside := hconfined
      (ambientEdgeToRetainedEdge source edge hsource)
      (not_exists_firstCommonCore_preimage_of_not_target_retained
        source middle edge hsource hmiddle)
    exact houtside.trans
      ((commonCoreAgrees_iff_ambient source target
        sourceBefore targetColoring).1 hsourceTargetBefore
          edge hsource htarget)

/-- Ambient edges on which two partial deletion colourings are both defined
and have different values. -/
noncomputable def ambientDisagreementSupport
    (source target : AdjacentPairData G)
    (sourceColoring : (DeletedAdjacentPairGraph G source.firstVertex
      source.secondVertex).EdgeColoring Color)
    (targetColoring : (DeletedAdjacentPairGraph G target.firstVertex
      target.secondVertex).EdgeColoring Color) : Finset G.edgeSet := by
  classical
  exact Finset.univ.filter fun edge =>
    ∃ hsource : IsRetainedAmbientEdge source edge,
      ∃ htarget : IsRetainedAmbientEdge target edge,
        sourceColoring (ambientEdgeToRetainedEdge source edge hsource) ≠
          targetColoring (ambientEdgeToRetainedEdge target edge htarget)

omit [DecidableEq V] in
theorem mem_ambientDisagreementSupport_iff
    (source target : AdjacentPairData G)
    (sourceColoring : (DeletedAdjacentPairGraph G source.firstVertex
      source.secondVertex).EdgeColoring Color)
    (targetColoring : (DeletedAdjacentPairGraph G target.firstVertex
      target.secondVertex).EdgeColoring Color)
    (edge : G.edgeSet) :
    edge ∈ ambientDisagreementSupport source target
        sourceColoring targetColoring ↔
      ∃ hsource : IsRetainedAmbientEdge source edge,
        ∃ htarget : IsRetainedAmbientEdge target edge,
          sourceColoring (ambientEdgeToRetainedEdge source edge hsource) ≠
            targetColoring (ambientEdgeToRetainedEdge target edge htarget) := by
  classical
  simp [ambientDisagreementSupport]

/-- The ambient disagreement support is nonempty exactly when literal
common-core agreement fails. -/
theorem ambientDisagreementSupport_nonempty_iff
    (source target : AdjacentPairData G)
    (sourceColoring : (DeletedAdjacentPairGraph G source.firstVertex
      source.secondVertex).EdgeColoring Color)
    (targetColoring : (DeletedAdjacentPairGraph G target.firstVertex
      target.secondVertex).EdgeColoring Color) :
    (ambientDisagreementSupport source target
        sourceColoring targetColoring).Nonempty ↔
      ¬ CommonCoreAgrees source target sourceColoring targetColoring := by
  constructor
  · rintro ⟨edge, hedge⟩ hagrees
    rcases (mem_ambientDisagreementSupport_iff
      source target sourceColoring targetColoring edge).1 hedge with
      ⟨hsource, htarget, hne⟩
    exact hne ((commonCoreAgrees_iff_ambient source target
      sourceColoring targetColoring).1 hagrees edge hsource htarget)
  · intro hdisagrees
    have hnotAmbient : ¬ ∀ (edge : G.edgeSet)
        (hsource : IsRetainedAmbientEdge source edge)
        (htarget : IsRetainedAmbientEdge target edge),
        sourceColoring (ambientEdgeToRetainedEdge source edge hsource) =
          targetColoring
            (ambientEdgeToRetainedEdge target edge htarget) := by
      intro hambient
      exact hdisagrees ((commonCoreAgrees_iff_ambient source target
        sourceColoring targetColoring).2 hambient)
    push Not at hnotAmbient
    rcases hnotAmbient with ⟨edge, hsource, htarget, hne⟩
    exact ⟨edge, (mem_ambientDisagreementSupport_iff
      source target sourceColoring targetColoring edge).2
        ⟨hsource, htarget, hne⟩⟩

/-- **Pointwise disagreement transport.**  If a source colouring is changed
only on its common deletion with a middle patch, then every new disagreement
edge with an old agreement partner is retained by the middle patch and is the
same disagreement edge between the middle and that partner. -/
theorem ambientDisagreementSupport_subset_of_confined_left_update
    (source middle target : AdjacentPairData G)
    (sourceBefore sourceAfter :
      (DeletedAdjacentPairGraph G source.firstVertex
        source.secondVertex).EdgeColoring Color)
    (middleColoring :
      (DeletedAdjacentPairGraph G middle.firstVertex
        middle.secondVertex).EdgeColoring Color)
    (targetColoring :
      (DeletedAdjacentPairGraph G target.firstVertex
        target.secondVertex).EdgeColoring Color)
    (hsourceMiddle : CommonCoreAgrees source middle
      sourceAfter middleColoring)
    (hsourceTargetBefore : CommonCoreAgrees source target
      sourceBefore targetColoring)
    (hconfined : AgreesOutsideEmbedding sourceBefore sourceAfter
      (deletedTwoPairsToFirstDeletionEmbedding G source.firstVertex
        source.secondVertex middle.firstVertex middle.secondVertex)) :
    ambientDisagreementSupport source target sourceAfter targetColoring ⊆
      ambientDisagreementSupport middle target middleColoring targetColoring := by
  intro edge hedge
  rcases (mem_ambientDisagreementSupport_iff
      source target sourceAfter targetColoring edge).1 hedge with
    ⟨hsource, htarget, hne⟩
  have hmiddle : IsRetainedAmbientEdge middle edge := by
    by_contra hnotMiddle
    have houtside := hconfined
      (ambientEdgeToRetainedEdge source edge hsource)
      (not_exists_firstCommonCore_preimage_of_not_target_retained
        source middle edge hsource hnotMiddle)
    exact hne (houtside.trans
      ((commonCoreAgrees_iff_ambient source target
        sourceBefore targetColoring).1 hsourceTargetBefore
          edge hsource htarget))
  apply (mem_ambientDisagreementSupport_iff
    middle target middleColoring targetColoring edge).2
  refine ⟨hmiddle, htarget, ?_⟩
  intro hmiddleTarget
  exact hne (((commonCoreAgrees_iff_ambient source middle
    sourceAfter middleColoring).1 hsourceMiddle
      edge hsource hmiddle).trans hmiddleTarget)

end

end GoertzelV24KempeLiftConfinement

end Mettapedia.GraphTheory.FourColor
