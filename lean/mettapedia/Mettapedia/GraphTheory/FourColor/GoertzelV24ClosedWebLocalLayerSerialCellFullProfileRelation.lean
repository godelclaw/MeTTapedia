import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalLayerSerialCellFactorization
import Mettapedia.GraphTheory.FourColor.GoertzelV24GraphDerivedCorridorCutProfile

/-!
# Full actual-source profile relation for one serial Cell

The actual terminal-aware prefix and its pre-rebase successor now carry one
joint source relation.  All five finite profile coordinates are computed from
the same edge coloring and the same two regional cut carriers.  The output
tracked and facial connectivity fields additionally expose the exact
predecessor/Cell/residual-seam closure.

The relation is deliberately relational and geometry-indexed.  It is the
semantic target for a later finite receipt and positive-`Count` adequacy
theorem; it does not assert that an input determines a unique output or that
every local `Count` witness already glues to an arbitrary prefix witness.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebAtGoodWord

open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAnnularEmbedding.ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24CorridorProfile
open GoertzelV24FaceOrbitIncidence
open GoertzelV24GraphDerivedCorridorCutProfile
open GoertzelV24HexCorridorSkeleton
open GoertzelV24HexSlabConnectivityProfile
open GoertzelV24RegionalBoundaryProfileFiniteState
open GoertzelV24RotationBoundaryFaceCutProfile
open GoertzelV24SimpleGraphSupResidual
open GoertzelV24TerminalProfileConnectivityUpdate
open GoertzelV24TerminalProfileFaceUpdate
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance closedWebLocalLayerSerialCellFullProfileRelationEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

namespace Instance

namespace LocalLayerFormation

/-- The dependent profile carrier determined by one actual graph cut. -/
abbrev SourceLocalLayerSerialCutProfileState
    {crossingEdgeCount terminalCount faceFragmentCount : Nat}
    {RS : RotationSystem V G.edgeSet}
    (_cutData : GraphCorridorCutData RS crossingEdgeCount terminalCount
      faceFragmentCount) :=
  CorridorCutProfile crossingEdgeCount terminalCount faceFragmentCount

/-- Complete graph-derived cut data immediately after adjoining one literal
Cell and before changing to the successor seam. -/
noncomputable def sourceLocalLayerSerialPreRebaseOutputCutDataAt
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3)) :=
  regionalBoundaryGraphCutData web.annular.RS
    (sourceLocalLayerSerialPreRebaseOutputRegionAt corridor hunique offset)
    (sourceLocalLayerRightCrossingAt corridor hunique offset)

@[simp]
theorem sourceLocalLayerSerialPreRebaseOutputCutDataAt_regionEdges
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3)) :
    (sourceLocalLayerSerialPreRebaseOutputCutDataAt corridor hunique offset).regionEdges =
      sourceLocalLayerSerialPreRebaseOutputRegionAt corridor hunique offset :=
  rfl

@[simp]
theorem sourceLocalLayerSerialPreRebaseOutputCutDataAt_crossingEdge
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3)) (step : Fin 2) :
    (sourceLocalLayerSerialPreRebaseOutputCutDataAt corridor hunique offset).crossingEdge
        step =
      sourceLocalLayerRightCrossingAt corridor hunique offset step :=
  rfl

/-- Every displayed output crossing belongs to the actual enlarged region. -/
theorem sourceLocalLayerSerialPreRebaseOutputCutDataAt_portsInRegion
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3)) :
    (sourceLocalLayerSerialPreRebaseOutputCutDataAt corridor hunique offset
      ).PortsInRegion := by
  apply regionalBoundaryGraphCutData_portsInRegion
  intro step
  rw [← sourceLocalLayerSerialTerminalInputRegionAt_union_cell corridor
    hunique offset]
  exact Finset.mem_union_right _
    (sourceLocalLayerCellRegionAt_rightCrossing corridor hunique offset step)

/-- Both actual cuts have occurrence-sensitive fragments computed inside
their stored regions. -/
theorem sourceLocalLayerSerialPreRebaseOutputCutDataAt_fragmentsOnFaceInRegion
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3)) :
    (sourceLocalLayerSerialPreRebaseOutputCutDataAt corridor hunique offset
      ).FragmentsOnFaceInRegion :=
  regionalBoundaryGraphCutData_fragmentsOnFaceInRegion web.annular.RS
    (sourceLocalLayerSerialPreRebaseOutputRegionAt corridor hunique offset)
    (sourceLocalLayerRightCrossingAt corridor hunique offset)

/-- One source-indexed terminal-prefix update with all five profile fields and
both exact residual-seam closures visible. -/
structure SourceLocalLayerSerialCellFullProfileRelation
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3)) (color : G.edgeSet → Color)
    (input : SourceLocalLayerSerialCutProfileState
      (sourceLocalLayerSerialTerminalInputCutDataAt corridor hunique offset))
    (output : SourceLocalLayerSerialCutProfileState
      (sourceLocalLayerSerialPreRebaseOutputCutDataAt corridor hunique offset)) : Prop where
  inputEdgeColor : ∀ step : Fin 2,
    (input.edgeColor step).toColor =
      color (sourceLocalLayerLeftCrossingAt corridor hunique offset step)
  outputEdgeColor : ∀ step : Fin 2,
    (output.edgeColor step).toColor =
      color (sourceLocalLayerRightCrossingAt corridor hunique offset step)
  inputStrandConnected : ∀ (pair : TrackedColorPair)
      (left right : CorridorPort 2 1),
    (input.strandConnected pair left right = true) ↔
      regionalTrackedConnectivity web.annular.RS
        (sourceLocalLayerSerialTerminalInputRegionAt corridor hunique offset)
        color pair
        ((sourceLocalLayerSerialTerminalInputCutDataAt corridor hunique offset
          ).portEdge left)
        ((sourceLocalLayerSerialTerminalInputCutDataAt corridor hunique offset
          ).portEdge right) = true
  outputStrandConnected : ∀ (pair : TrackedColorPair)
      (left right : Fin 2),
    (output.strandConnected pair (.inl left) (.inl right) = true) ↔
      IsTrackedColor (trackedColorPairColors pair).1
          (trackedColorPairColors pair).2
          (color (sourceLocalLayerRightCrossingAt corridor hunique offset left)) ∧
        IsTrackedColor (trackedColorPairColors pair).1
          (trackedColorPairColors pair).2
          (color (sourceLocalLayerRightCrossingAt corridor hunique offset right)) ∧
        Relation.ReflTransGen
          (ThreeFactorComponentStep
            (regionalTrackedEdgeGraph web.annular.RS
              (sourceLocalLayerSerialTerminalInputRegionAt corridor hunique offset)
              color (trackedColorPairColors pair).1
                (trackedColorPairColors pair).2)
            (regionalTrackedEdgeGraph web.annular.RS
              (sourceLocalLayerCellRegionAt corridor hunique offset)
              color (trackedColorPairColors pair).1
                (trackedColorPairColors pair).2)
            (sourceLocalLayerSerialTerminalTrackedSeamAt corridor hunique offset
              color (trackedColorPairColors pair).1
                (trackedColorPairColors pair).2))
          (sourceLocalLayerRightCrossingAt corridor hunique offset left)
          (sourceLocalLayerRightCrossingAt corridor hunique offset right)
  inputFaceContinues : ∀ left right,
    (input.faceContinues left right = true) ↔
      (sourceLocalLayerSerialTerminalInputCutDataAt corridor hunique offset
          ).fragmentFace left =
        (sourceLocalLayerSerialTerminalInputCutDataAt corridor hunique offset
          ).fragmentFace right
  outputFaceContinues : ∀ left right,
    (output.faceContinues left right = true) ↔
      (sourceLocalLayerSerialPreRebaseOutputCutDataAt corridor hunique offset
          ).fragmentFace left =
        (sourceLocalLayerSerialPreRebaseOutputCutDataAt corridor hunique offset
          ).fragmentFace right
  inputFragmentContainsPort : ∀ index port,
    (input.fragmentContainsPort index port = true) ↔
      (sourceLocalLayerSerialTerminalInputCutDataAt corridor hunique offset
          ).portEdge port ∈
        (sourceLocalLayerSerialTerminalInputCutDataAt corridor hunique offset
          ).regionalFragmentEdges index
  outputFragmentContainsPort : ∀ index port,
    (output.fragmentContainsPort index port = true) ↔
      (sourceLocalLayerSerialPreRebaseOutputCutDataAt corridor hunique offset
          ).portEdge port ∈
        (sourceLocalLayerSerialPreRebaseOutputCutDataAt corridor hunique offset
          ).regionalFragmentEdges index
  inputFaceLengthCap : ∀ index,
    (input.faceLengthCap index).val =
      min ((sourceLocalLayerSerialTerminalInputCutDataAt corridor hunique offset
        ).regionalFragmentEdges index).card 5
  outputFaceLengthCap : ∀ index,
    (output.faceLengthCap index).val =
      min ((sourceLocalLayerSerialPreRebaseOutputCutDataAt corridor hunique offset
        ).regionalFragmentEdges index).card 5
  outputFaceReachable : ∀ (root : web.annular.RS.D)
      (left right : Fin (web.annular.RS.faceOrbit root).card),
    (faceRegionalAmbientPositionGraph web.annular.RS root
      (sourceLocalLayerSerialPreRebaseOutputRegionAt corridor hunique offset)).Reachable
        left right ↔
      Relation.ReflTransGen
        (ThreeFactorComponentStep
          (faceRegionalAmbientPositionGraph web.annular.RS root
            (sourceLocalLayerSerialTerminalInputRegionAt corridor hunique offset))
          (faceRegionalAmbientPositionGraph web.annular.RS root
            (sourceLocalLayerCellRegionAt corridor hunique offset))
          (sourceLocalLayerSerialTerminalFaceSeamAt corridor hunique offset root))
        left right

/-- The two actual graph-derived profiles satisfy the complete serial Cell
relation for every coloring nonzero on the displayed crossings. -/
theorem sourceLocalLayerSerialCellFullProfileRelation
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3)) (color : G.edgeSet → Color)
    (hinputColor : ∀ step,
      color (sourceLocalLayerLeftCrossingAt corridor hunique offset step) ≠ 0)
    (houtputColor : ∀ step,
      color (sourceLocalLayerRightCrossingAt corridor hunique offset step) ≠ 0) :
    SourceLocalLayerSerialCellFullProfileRelation corridor hunique offset color
      ((sourceLocalLayerSerialTerminalInputCutDataAt corridor hunique offset
        ).regionalProfile color hinputColor)
      ((sourceLocalLayerSerialPreRebaseOutputCutDataAt corridor hunique offset
        ).regionalProfile color houtputColor) := by
  let inputData := sourceLocalLayerSerialTerminalInputCutDataAt corridor
    hunique offset
  let outputData := sourceLocalLayerSerialPreRebaseOutputCutDataAt corridor
    hunique offset
  refine {
    inputEdgeColor := ?_
    outputEdgeColor := ?_
    inputStrandConnected := ?_
    outputStrandConnected := ?_
    inputFaceContinues := ?_
    outputFaceContinues := ?_
    inputFragmentContainsPort := ?_
    outputFragmentContainsPort := ?_
    inputFaceLengthCap := ?_
    outputFaceLengthCap := ?_
    outputFaceReachable := ?_ }
  · intro step
    exact inputData.regionalProfile_edgeColor_toColor color hinputColor step
  · intro step
    exact outputData.regionalProfile_edgeColor_toColor color houtputColor step
  · intro pair left right
    rw [inputData.regionalProfile_strandConnected_eq_true_iff,
      regionalTrackedConnectivity_eq_true_iff]
    rfl
  · intro pair left right
    rw [outputData.regionalProfile_strandConnected_eq_true_iff]
    constructor
    · rintro ⟨_leftMem, _rightMem, hleft, hright, hreachable⟩
      exact ⟨hleft, hright,
        (sourceLocalLayerSerialPreRebaseTrackedReachable_iff corridor hunique
          offset color (trackedColorPairColors pair).1
          (trackedColorPairColors pair).2 _ _).1 hreachable⟩
    · rintro ⟨hleft, hright, hreachable⟩
      exact ⟨
        sourceLocalLayerSerialPreRebaseOutputCutDataAt_portsInRegion corridor
          hunique offset (.inl left),
        sourceLocalLayerSerialPreRebaseOutputCutDataAt_portsInRegion corridor
          hunique offset (.inl right),
        hleft, hright,
        (sourceLocalLayerSerialPreRebaseTrackedReachable_iff corridor hunique
          offset color (trackedColorPairColors pair).1
          (trackedColorPairColors pair).2 _ _).2 hreachable⟩
  · intro left right
    exact inputData.regionalProfile_faceContinues_eq_true_iff color
      hinputColor left right
  · intro left right
    exact outputData.regionalProfile_faceContinues_eq_true_iff color
      houtputColor left right
  · intro index port
    exact inputData.regionalProfile_fragmentContainsPort_eq_true_iff color
      hinputColor index port
  · intro index port
    exact outputData.regionalProfile_fragmentContainsPort_eq_true_iff color
      houtputColor index port
  · intro index
    exact inputData.regionalProfile_faceLengthCap_val color hinputColor index
  · intro index
    exact outputData.regionalProfile_faceLengthCap_val color houtputColor index
  · intro root left right
    exact sourceLocalLayerSerialPreRebaseFaceReachable_iff corridor hunique
      offset root left right

/-- The actual source coloring therefore inhabits the relation on the two
bounded profile packages used by the finite-state development. -/
theorem sourceLocalLayerSerialCellFullProfileRelation_of_ambientColoring
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3)) :
    SourceLocalLayerSerialCellFullProfileRelation corridor hunique offset
      coloring
      (sourceLocalLayerSerialTerminalInputBoundedProfileAt corridor hunique
        offset).profile
      (sourceLocalLayerSerialPreRebaseOutputBoundedProfileAt corridor hunique
        offset).profile := by
  exact sourceLocalLayerSerialCellFullProfileRelation corridor hunique offset
    coloring (fun _ => web.tait _) (fun _ => web.tait _)

end LocalLayerFormation

end Instance

end

end GoertzelV24ClosedWebAtGoodWord

end Mettapedia.GraphTheory.FourColor
