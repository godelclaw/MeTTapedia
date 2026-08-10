import Mettapedia.GraphTheory.FourColor.GoertzelV24OpenRegionTaitInheritance
import Mettapedia.GraphTheory.FourColor.GoertzelV24SpliceUnification

/-!
# Reading a shortened splice as a literal open tangle

The compositional splice sews the two exposed corridor sides together.  A
coloring of that shorter map can therefore be read on the retained exterior as
a literal open tangle: an intact old dart reads its intact output edge, while
an exposed old dart and its fresh stub both read the sewn seam edge.

This is the first half of the source's reverse completion calculation.  It
does not assert that the omitted piece can be filled; that later fact must be
obtained from the actual profile semantics.  It does establish the concrete
open coloring and its boundary word on the retained source piece.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24OpenRegionOutputRestriction

open GoertzelV24OpenRegionRotation
open GoertzelV24OpenRegionTaitInheritance
open GoertzelV24OrderedCutRotationSplice
open GoertzelV24RetainedVertexRotationSplice
open GoertzelV24RotationCutDartDecomposition
open GoertzelV24SpliceUnification
open GoertzelV24SpliceUnification.OrderedCutSpliceData

variable {V E : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E]

noncomputable section

namespace OrderedCutSpliceData

variable {RS : RotationSystem V E}
  {n terminalCount faceFragmentCount : Nat}

/-- The old retained dart represented by a literal-open dart.  A fresh stub
remembers the exposed old dart to which it is attached. -/
def openDartUnderlyingRetained
    (data : OrderedCutSpliceData RS n terminalCount faceFragmentCount) :
    Dart RS data.keep → RetainedDart RS data.keep
  | .inl dart => dart
  | .inr boundary => boundary.1

/-- Map a literal-open dart of the retained exterior to the corresponding
dart of the sewn output.  Boundary stubs deliberately map to the same sewn
seam endpoint as their old exposed dart. -/
noncomputable def openDartToOutputDart
    (data : OrderedCutSpliceData RS n terminalCount faceFragmentCount) :
    Dart RS data.keep → data.output.D :=
  fun dart =>
    retainedDartEquivMatchedParts RS data.keep
      (orderedCut data.left.crossingEdge)
      (orderedCut data.right.crossingEdge)
      data.cover data.disjoint
      (openDartUnderlyingRetained data dart)

/-- A root for the literal retained exterior, inherited from the ambient
outer dart. -/
noncomputable def openRoot
    (data : OrderedCutSpliceData RS n terminalCount faceFragmentCount) :
    Dart RS data.keep :=
  Sum.inl ⟨RS.outer, data.outer_kept⟩

/-- The retained exterior as an actual open rotation system. -/
noncomputable def openRegion
    (data : OrderedCutSpliceData RS n terminalCount faceFragmentCount) :
    RotationSystem (GoertzelV24OpenRegionRotation.Vertex RS data.keep)
      (rewiredDartSystem RS data.keep (openRoot data)).Edge :=
  rotationSystem RS data.keep (openRoot data)

/-- Read an output edge coloring on every dart of the literal retained open
region. -/
def outputOpenDartColor
    (data : OrderedCutSpliceData RS n terminalCount faceFragmentCount)
    (coloring : data.output.EdgeColoring Color) :
    Dart RS data.keep → Color :=
  fun dart => coloring (data.output.edgeOf (openDartToOutputDart data dart))

/-- The matched-parts equivalence sends an intact retained dart to its
literal interior summand.  Keeping this elementary transport named avoids
unfolding the whole ordered seam when reading output colors on an open
region. -/
theorem retainedDartEquivMatchedParts_of_internal
    (data : OrderedCutSpliceData RS n terminalCount faceFragmentCount)
    (internal : InternalDart RS data.keep) :
    retainedDartEquivMatchedParts RS data.keep
        (orderedCut data.left.crossingEdge) (orderedCut data.right.crossingEdge)
        data.cover data.disjoint internal.1 = Sum.inl internal := by
  simp [retainedDartEquivMatchedParts,
    retainedDartEquivInternalSumBoundary, internal.2]

/-- On an intact retained edge, the literal open-region flip is represented
by the output flip. -/
theorem openDartToOutputDart_alpha_of_internal
    (data : OrderedCutSpliceData RS n terminalCount faceFragmentCount)
    (dart : RetainedDart RS data.keep)
    (hinternal : data.keep (RS.vertOf (RS.alpha dart.1))) :
    openDartToOutputDart data
        (Sum.inl ⟨RS.alpha dart.1, hinternal⟩) =
      data.output.alpha
        (openDartToOutputDart data (Sum.inl dart)) := by
  let internal : InternalDart RS data.keep := ⟨dart, hinternal⟩
  have hparts :
      retainedDartEquivMatchedParts RS data.keep
          (orderedCut data.left.crossingEdge) (orderedCut data.right.crossingEdge)
          data.cover data.disjoint dart = Sum.inl internal := by
    change retainedDartEquivMatchedParts RS data.keep
        (orderedCut data.left.crossingEdge) (orderedCut data.right.crossingEdge)
        data.cover data.disjoint internal.1 = Sum.inl internal
    exact retainedDartEquivMatchedParts_of_internal data internal
  have hparts_alpha :
      retainedDartEquivMatchedParts RS data.keep
          (orderedCut data.left.crossingEdge) (orderedCut data.right.crossingEdge)
          data.cover data.disjoint ⟨RS.alpha dart.1, hinternal⟩ =
        Sum.inl (internalAlpha RS data.keep internal) := by
    change retainedDartEquivMatchedParts RS data.keep
        (orderedCut data.left.crossingEdge) (orderedCut data.right.crossingEdge)
        data.cover data.disjoint (internalAlpha RS data.keep internal).1 =
      Sum.inl (internalAlpha RS data.keep internal)
    exact retainedDartEquivMatchedParts_of_internal data
      (internalAlpha RS data.keep internal)
  change
    retainedDartEquivMatchedParts RS data.keep
        (orderedCut data.left.crossingEdge) (orderedCut data.right.crossingEdge)
        data.cover data.disjoint ⟨RS.alpha dart.1, hinternal⟩ =
      (orderedCutRetainedVertexRewiredDartSystem RS data.keep
        data.left.crossingEdge data.right.crossingEdge data.leftCrosses
        data.rightCrosses data.leftInjective data.rightInjective data.cover
        data.disjoint data.outer_kept data.seamEndpoints).alpha
        (retainedDartEquivMatchedParts RS data.keep
          (orderedCut data.left.crossingEdge) (orderedCut data.right.crossingEdge)
          data.cover data.disjoint dart)
  rw [hparts]
  change retainedDartEquivMatchedParts RS data.keep
      (orderedCut data.left.crossingEdge) (orderedCut data.right.crossingEdge)
      data.cover data.disjoint ⟨RS.alpha dart.1, hinternal⟩ =
    Sum.inl (internalAlpha RS data.keep internal)
  exact hparts_alpha

/-- On an exposed half-edge, the old open dart and its fresh stub represent
the same sewn output dart. -/
theorem openDartToOutputDart_boundary_eq_stub
    (data : OrderedCutSpliceData RS n terminalCount faceFragmentCount)
    (dart : RetainedDart RS data.keep)
    (hboundary : ¬ data.keep (RS.vertOf (RS.alpha dart.1))) :
    openDartToOutputDart data (Sum.inl dart) =
      openDartToOutputDart data (Sum.inr ⟨dart, hboundary⟩) :=
  rfl

/-- The left ordered boundary stub of the literal open region reads the
sewn output edge at that same source position. -/
theorem outputOpenDartColor_leftBoundary_eq_seamColorWord
    (data : OrderedCutSpliceData RS n terminalCount faceFragmentCount)
    (coloring : data.output.EdgeColoring Color)
    (step : Fin n) :
    outputOpenDartColor data coloring
        (Sum.inl (orderedBoundaryDart RS data.keep
          data.left.crossingEdge data.leftCrosses step).1.1) =
      seamColorWord data coloring step := by
  have hleftmem : data.left.crossingEdge step ∈ orderedCut data.left.crossingEdge :=
    Finset.mem_image.2 ⟨step, Finset.mem_univ _, rfl⟩
  have hparts :
      retainedDartEquivMatchedParts RS data.keep
          (orderedCut data.left.crossingEdge) (orderedCut data.right.crossingEdge)
          data.cover data.disjoint
          (orderedBoundaryDart RS data.keep data.left.crossingEdge
            data.leftCrosses step).1.1 =
        Sum.inr (Sum.inl (orderedBoundaryDart RS data.keep
          data.left.crossingEdge data.leftCrosses step)) := by
    simp [retainedDartEquivMatchedParts,
      retainedDartEquivInternalSumBoundary, boundaryDartEquivCutSum,
      boundaryDartToCutSum,
      (orderedBoundaryDart RS data.keep data.left.crossingEdge
        data.leftCrosses step).1.2,
      hleftmem]
  change coloring (data.output.edgeOf
      (retainedDartEquivMatchedParts RS data.keep
        (orderedCut data.left.crossingEdge) (orderedCut data.right.crossingEdge)
        data.cover data.disjoint
        (orderedBoundaryDart RS data.keep data.left.crossingEdge
          data.leftCrosses step).1.1)) =
    coloring (data.output.edgeOf (Sum.inr (Sum.inl
      (orderedBoundaryDart RS data.keep data.left.crossingEdge
        data.leftCrosses step))))
  rw [hparts]

/-- The right ordered boundary stub reads the same sewn output edge as its
matched left stub.  This is the literal-open form of the splice's boundary
color agreement. -/
theorem outputOpenDartColor_rightBoundary_eq_seamColorWord
    (data : OrderedCutSpliceData RS n terminalCount faceFragmentCount)
    (coloring : data.output.EdgeColoring Color)
    (step : Fin n) :
    outputOpenDartColor data coloring
        (Sum.inl (orderedBoundaryDart RS data.keep
          data.right.crossingEdge data.rightCrosses step).1.1) =
      seamColorWord data coloring step := by
  have hleftmem : data.left.crossingEdge step ∈ orderedCut data.left.crossingEdge :=
    Finset.mem_image.2 ⟨step, Finset.mem_univ _, rfl⟩
  have hrightmem : data.right.crossingEdge step ∈ orderedCut data.right.crossingEdge :=
    Finset.mem_image.2 ⟨step, Finset.mem_univ _, rfl⟩
  have hleftnot : data.right.crossingEdge step ∉ orderedCut data.left.crossingEdge :=
    fun hmem => Finset.disjoint_left.1 data.disjoint hmem hrightmem
  have hparts :
      retainedDartEquivMatchedParts RS data.keep
          (orderedCut data.left.crossingEdge) (orderedCut data.right.crossingEdge)
          data.cover data.disjoint
          (orderedBoundaryDart RS data.keep data.right.crossingEdge
            data.rightCrosses step).1.1 =
        Sum.inr (Sum.inr (orderedBoundaryDart RS data.keep
          data.right.crossingEdge data.rightCrosses step)) := by
    simp [retainedDartEquivMatchedParts,
      retainedDartEquivInternalSumBoundary, boundaryDartEquivCutSum,
      boundaryDartToCutSum,
      (orderedBoundaryDart RS data.keep data.right.crossingEdge
        data.rightCrosses step).1.2,
      hleftnot]
  change coloring (data.output.edgeOf
      (retainedDartEquivMatchedParts RS data.keep
        (orderedCut data.left.crossingEdge) (orderedCut data.right.crossingEdge)
        data.cover data.disjoint
        (orderedBoundaryDart RS data.keep data.right.crossingEdge
          data.rightCrosses step).1.1)) =
    coloring (data.output.edgeOf (Sum.inr (Sum.inl
      (orderedBoundaryDart RS data.keep data.left.crossingEdge
        data.leftCrosses step))))
  rw [hparts]
  have halpha :
      data.output.alpha (Sum.inr (Sum.inl
        (orderedBoundaryDart RS data.keep data.left.crossingEdge
          data.leftCrosses step))) =
        Sum.inr (Sum.inr (orderedBoundaryDart RS data.keep
          data.right.crossingEdge data.rightCrosses step)) := by
    change (orderedCutRetainedVertexRewiredDartSystem RS data.keep
      data.left.crossingEdge data.right.crossingEdge data.leftCrosses
      data.rightCrosses data.leftInjective data.rightInjective data.cover
      data.disjoint data.outer_kept data.seamEndpoints).alpha
        (Sum.inr (Sum.inl (orderedBoundaryDart RS data.keep
          data.left.crossingEdge data.leftCrosses step))) = _
    simp [orderedCutRetainedVertexRewiredDartSystem,
      orderedCutRewiredDartSystem, orderedCutMatchedSeamData,
      GoertzelV24RotationSpliceConstructor.MatchedSeam.Data.toRewiredDartSystem,
      GoertzelV24RotationSpliceConstructor.MatchedSeam.Data.alpha,
      orderedCutSeamMatching_apply]
  rw [← halpha]
  exact congrArg coloring (data.output.edge_alpha
    (Sum.inr (Sum.inl (orderedBoundaryDart RS data.keep
      data.left.crossingEdge data.leftCrosses step))))

/-- On an old dart, the output map preserves the underlying retained vertex.
Fresh stubs are deliberately excluded: their literal-open vertices are new
degree-one vertices rather than vertices of the shortened closed map. -/
theorem output_vertOf_openDartToOutputDart_old
    (data : OrderedCutSpliceData RS n terminalCount faceFragmentCount)
    (dart : RetainedDart RS data.keep) :
    data.output.vertOf (openDartToOutputDart data (Sum.inl dart)) =
      ⟨RS.vertOf dart.1, dart.2⟩ := by
  change matchedPartRetainedVertex RS data.keep
      (orderedCut data.left.crossingEdge) (orderedCut data.right.crossingEdge)
      (retainedDartEquivMatchedParts RS data.keep
        (orderedCut data.left.crossingEdge) (orderedCut data.right.crossingEdge)
        data.cover data.disjoint dart) = _
  apply Subtype.ext
  change RS.vertOf (matchedPartUnderlyingDart RS data.keep
      (orderedCut data.left.crossingEdge) (orderedCut data.right.crossingEdge)
      (retainedDartEquivMatchedParts RS data.keep
        (orderedCut data.left.crossingEdge) (orderedCut data.right.crossingEdge)
        data.cover data.disjoint dart)) = RS.vertOf dart.1
  rw [matchedPartUnderlyingDart_equiv]

/-- Output colors are constant along the literal open-region edge flip. -/
theorem outputOpenDartColor_alpha
    (data : OrderedCutSpliceData RS n terminalCount faceFragmentCount)
    (coloring : data.output.EdgeColoring Color)
    (dart : Dart RS data.keep) :
    outputOpenDartColor data coloring
        ((openRegion data).alpha dart) =
      outputOpenDartColor data coloring dart := by
  rcases dart with dart | boundary
  · by_cases hinternal : data.keep (RS.vertOf (RS.alpha dart.1))
    · change outputOpenDartColor data coloring
          ((rotationSystem RS data.keep (openRoot data)).alpha (Sum.inl dart)) =
        outputOpenDartColor data coloring (Sum.inl dart)
      rw [rotationSystem_alpha_old_of_internal RS data.keep
        (openRoot data) dart hinternal]
      rw [outputOpenDartColor, openDartToOutputDart_alpha_of_internal]
      exact congrArg coloring (data.output.edge_alpha
        (openDartToOutputDart data (Sum.inl dart)))
    · change outputOpenDartColor data coloring
          ((rotationSystem RS data.keep (openRoot data)).alpha (Sum.inl dart)) =
        outputOpenDartColor data coloring (Sum.inl dart)
      rw [rotationSystem_alpha_old_of_boundary RS data.keep
        (openRoot data) dart hinternal]
      change coloring (data.output.edgeOf
        (openDartToOutputDart data (Sum.inr ⟨dart, hinternal⟩))) =
        coloring (data.output.edgeOf (openDartToOutputDart data (Sum.inl dart)))
      rw [← openDartToOutputDart_boundary_eq_stub data dart hinternal]
  · change outputOpenDartColor data coloring
        ((rotationSystem RS data.keep (openRoot data)).alpha (Sum.inr boundary)) =
      outputOpenDartColor data coloring (Sum.inr boundary)
    rw [rotationSystem_alpha_stub RS data.keep (openRoot data) boundary]
    change coloring (data.output.edgeOf
      (openDartToOutputDart data (Sum.inl boundary.1))) =
      coloring (data.output.edgeOf (openDartToOutputDart data (Sum.inr boundary)))
    exact congrArg (fun outputDart => coloring (data.output.edgeOf outputDart))
      (openDartToOutputDart_boundary_eq_stub data boundary.1 boundary.2)

/-- Properness of an output coloring survives on the literal retained open
region.  At an old vertex the output-dart map preserves both its vertex and
the distinction of incident darts; a fresh boundary vertex has one dart. -/
theorem outputOpenDartColor_proper
    (data : OrderedCutSpliceData RS n terminalCount faceFragmentCount)
    (coloring : data.output.EdgeColoring Color) :
    ∀ {left right : Dart RS data.keep},
      (openRegion data).vertOf left = (openRegion data).vertOf right →
        left ≠ right →
        outputOpenDartColor data coloring left ≠
          outputOpenDartColor data coloring right := by
  intro left right hvertex hne
  rcases left with left | left <;> rcases right with right | right
  · have hvertex' : RS.vertOf left.1 = RS.vertOf right.1 :=
      congrArg Subtype.val (Sum.inl.inj hvertex)
    have houtputVertex :
        data.output.vertOf (openDartToOutputDart data (Sum.inl left)) =
          data.output.vertOf (openDartToOutputDart data (Sum.inl right)) := by
      rw [output_vertOf_openDartToOutputDart_old,
        output_vertOf_openDartToOutputDart_old]
      apply Subtype.ext
      exact hvertex'
    have houtDartNe :
        openDartToOutputDart data (Sum.inl left) ≠
          openDartToOutputDart data (Sum.inl right) := by
      intro heq
      apply hne
      apply congrArg Sum.inl
      apply (retainedDartEquivMatchedParts RS data.keep
        (orderedCut data.left.crossingEdge) (orderedCut data.right.crossingEdge)
        data.cover data.disjoint).injective
      exact heq
    have hedgeNe :
        data.output.edgeOf (openDartToOutputDart data (Sum.inl left)) ≠
          data.output.edgeOf (openDartToOutputDart data (Sum.inl right)) := by
      intro hedge
      apply houtDartNe
      apply data.output.edgeOf_injOn_dartsAt
        (data.output.vertOf (openDartToOutputDart data (Sum.inl left)))
      · simp [RotationSystem.dartsAt]
      · simp [RotationSystem.dartsAt, houtputVertex]
      · exact hedge
    unfold outputOpenDartColor
    apply coloring.valid
    apply (data.output.edgeAdjacencyGraph_adj_iff).2
    refine ⟨hedgeNe,
      data.output.vertOf (openDartToOutputDart data (Sum.inl left)), ?_, ?_⟩
    · exact (data.output.mem_endpoints_iff).2
        ⟨openDartToOutputDart data (Sum.inl left), by simp, rfl⟩
    · exact (data.output.mem_endpoints_iff).2
        ⟨openDartToOutputDart data (Sum.inl right), by simp,
          houtputVertex.symm⟩
  · cases hvertex
  · cases hvertex
  · have hboundary : left = right := Sum.inr.inj hvertex
    subst right
    exact (hne rfl).elim

/-- A Tait output coloring remains nonzero on every literal-open dart. -/
theorem outputOpenDartColor_nonzero
    (data : OrderedCutSpliceData RS n terminalCount faceFragmentCount)
    (coloring : data.output.EdgeColoring Color)
    (hcoloring : data.output.IsTaitEdgeColoring coloring)
    (dart : Dart RS data.keep) :
    outputOpenDartColor data coloring dart ≠ 0 :=
  hcoloring _

/-- Restrict a coloring of the shortened splice to the literal open retained
piece.  This is a real open-tangle coloring, not a boundary word supplied as
an extra premise. -/
noncomputable def outputOpenColoring
    (data : OrderedCutSpliceData RS n terminalCount faceFragmentCount)
    (coloring : data.output.EdgeColoring Color) :
    (openRegion data).EdgeColoring Color :=
  (rewiredDartSystem RS data.keep (openRoot data)).descendedColoring
    (outputOpenDartColor data coloring)
    (outputOpenDartColor_alpha data coloring)
    (outputOpenDartColor_proper data coloring)

/-- The literal-open coloring reads exactly as the output coloring on the
corresponding sewn output dart. -/
theorem outputOpenColoring_edgeOf
    (data : OrderedCutSpliceData RS n terminalCount faceFragmentCount)
    (coloring : data.output.EdgeColoring Color)
    (dart : Dart RS data.keep) :
    outputOpenColoring data coloring ((openRegion data).edgeOf dart) =
      outputOpenDartColor data coloring dart := by
  change (rewiredDartSystem RS data.keep (openRoot data)).descendedEdgeColor
      (outputOpenDartColor data coloring)
      ((rewiredDartSystem RS data.keep (openRoot data)).edgeOf dart) = _
  exact (rewiredDartSystem RS data.keep (openRoot data)).descendedEdgeColor_edgeOf
    (outputOpenDartColor data coloring)
    (outputOpenDartColor_alpha data coloring) dart

/-- A Tait coloring of the shortened splice gives a Tait coloring of the
literal retained open region. -/
theorem outputOpenColoring_isTait
    (data : OrderedCutSpliceData RS n terminalCount faceFragmentCount)
    (coloring : data.output.EdgeColoring Color)
    (hcoloring : data.output.IsTaitEdgeColoring coloring) :
    (openRegion data).IsTaitEdgeColoring (outputOpenColoring data coloring) := by
  exact (rewiredDartSystem RS data.keep (openRoot data)).descendedColoring_isTait
    (outputOpenDartColor data coloring)
    (outputOpenDartColor_alpha data coloring)
    (outputOpenDartColor_proper data coloring)
    (outputOpenDartColor_nonzero data coloring hcoloring)

end OrderedCutSpliceData

end

end GoertzelV24OpenRegionOutputRestriction

end Mettapedia.GraphTheory.FourColor
