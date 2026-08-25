import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalLayerSerialCellUniformSuccessorLetter
import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalLayerSerialBoundaryRebaseOutputColorParametric

/-!
# A colouring-parametric uniform Cell successor letter

The fixed forty-nine-edge and forty-eight-dart Cell--rebase recurrences already
accept the colouring carried by an arbitrary composed witness.  This file
threads that parameter through the combined five-field successor letter.

This distinction is load-bearing for cumulative `Count` factorization: a
positive literal Cell witness need not use the ambient closed-web colouring.
The theorem below therefore identifies the finite letter with the literal next
terminal-aware profile at the supplied colouring.  The earlier ambient letter
is retained as its specialization.  No `Count` composition or reachable-closure
claim is made here.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebLocalLayerSerialCellUniformSuccessorColorParametric

open GoertzelV24BoundaryProfileFiniteState
open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAnnularEmbedding.ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAtGoodWord
open GoertzelV24ClosedWebAtGoodWord.Instance
open GoertzelV24ClosedWebAtGoodWord.Instance.LocalLayerFormation
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24ClosedWebLocalLayerSerialBoundaryRebaseFiniteBoolOutput
open GoertzelV24ClosedWebLocalLayerSerialBoundaryRebaseFiniteBoolReceipt
open GoertzelV24ClosedWebLocalLayerSerialBoundaryRebaseOutputColorParametric
open GoertzelV24ClosedWebLocalLayerSerialBoundaryRebaseTrackedColorParametric
open GoertzelV24ClosedWebLocalLayerSerialCellUniformFaceRecurrence
open GoertzelV24ClosedWebLocalLayerSerialCellUniformSuccessorCoordinates
open GoertzelV24ClosedWebLocalLayerSerialCellUniformSuccessorLetter
open GoertzelV24ClosedWebLocalLayerSerialCellUniformTrackedRecurrence
open GoertzelV24CorridorProfile
open GoertzelV24FaceOrbitIncidence
open GoertzelV24FacialPentagonCap
open GoertzelV24HexCorridorFiniteColorTransition
open GoertzelV24HexSlabConnectivityProfile
open GoertzelV24InterfaceDeletionComponentFactor
open GoertzelV24InterfaceDeletionComponentFactorGraphFree
open GoertzelV24TwoEdgeCutMinimality
open GoertzelV24TwoPentagonCapOpening
open GoertzelV24WindingClassification
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance cellUniformSuccessorColorParametricEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

local instance cellUniformSuccessorColorParametricOpenedGraphDecidableRel
    (caps : OrientedFacialPentagonCapPair (G := G) graphData) :
    DecidableRel
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.Adj :=
  Classical.decRel _

/-- The exact finite uniform successor letter at an arbitrary colouring of the
opened carrier.  Nonzero colours on the four named rebase roles supply both
the tracked colour guards and the two displayed crossing colours. -/
noncomputable def sourceLocalLayerSerialCellUniformSuccessorLetterForColorAt
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (caps : OrientedFacialPentagonCapPair graphData)
    (coloring :
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.EdgeColoring Color)
    (web : GoertzelV24ClosedWebAtGoodWord.Instance
      caps.toFacialPentagonCapPair.toPentagonCapPair.boundaryData coloring)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (color :
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.edgeSet → Color)
    (hrole : ∀ role, color
      (sourceLocalLayerBoundaryRebaseEdgeAt corridor hunique offset hnext role) ≠
        0) :
    SourceLocalLayerSerialCellUniformSuccessorLetter := by
  let output := terminalInputBoundedProfileForColorAt corridor hunique
    (sourceLocalLayerNextOffset offset hnext) color
    (successorCrossingNonzeroForColorAt corridor hunique offset hnext color
      hrole)
  let receipt := finiteBoolOutputLetterCodeForColorAt corridor hunique offset
    hnext color hrole
  let trackedCode :=
    sourceLocalLayerSerialCellRebaseUniformTrackedBoundedSuccessorCodeAt
      graphData minimal caps coloring web corridor hunique offset hnext color
  let faceCode :=
    sourceLocalLayerSerialCellRebaseUniformFaceBoundedSuccessorCodeAt graphData
      minimal caps coloring web corridor hunique offset hnext
  exact {
    outputCount := output.faceFragmentCount
    trackedCode := trackedCode
    faceCode := faceCode
    portColor := fun port => receipt.tracked.roleColor
      (sourceLocalLayerBoundaryRebaseSuccessorPortRole port)
    trackedPortCoordinate := fun port =>
      sourceLocalLayerSerialCellRebaseUniformTrackedPortCoordinateAt graphData
        caps coloring web corridor hunique offset hnext port
    faceFragmentCoordinate := fun fragment =>
      sourceLocalLayerSerialCellRebaseUniformFaceFragmentCoordinateAt corridor
        hunique offset hnext
        (sourceLocalLayerBoundaryRebaseSuccessorFaceFragmentAtIndex corridor
          hunique offset hnext fragment)
    facePortCoordinate := fun port side =>
      sourceLocalLayerSerialCellRebaseUniformFacePortCoordinateAt corridor
        hunique offset hnext port side
    faceContinues := fun left right => receipt.facial.faceContinues
      (sourceLocalLayerBoundaryRebaseSuccessorFaceFragmentSlotAt corridor
        hunique offset hnext
        (sourceLocalLayerBoundaryRebaseSuccessorFaceFragmentAtIndex corridor
          hunique offset hnext left))
      (sourceLocalLayerBoundaryRebaseSuccessorFaceFragmentSlotAt corridor
        hunique offset hnext
        (sourceLocalLayerBoundaryRebaseSuccessorFaceFragmentAtIndex corridor
          hunique offset hnext right))
    faceLengthCap := fun fragment => receipt.facial.faceLengthCap
      (sourceLocalLayerBoundaryRebaseSuccessorFaceFragmentSlotAt corridor
        hunique offset hnext
        (sourceLocalLayerBoundaryRebaseSuccessorFaceFragmentAtIndex corridor
          hunique offset hnext fragment)) }

@[simp]
theorem sourceLocalLayerSerialCellUniformSuccessorLetterForColorAt_edgeColor
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (caps : OrientedFacialPentagonCapPair graphData)
    (coloring :
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.EdgeColoring Color)
    (web : GoertzelV24ClosedWebAtGoodWord.Instance
      caps.toFacialPentagonCapPair.toPentagonCapPair.boundaryData coloring)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (color :
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.edgeSet → Color)
    (hrole : ∀ role, color
      (sourceLocalLayerBoundaryRebaseEdgeAt corridor hunique offset hnext role) ≠
        0)
    (crossing : Fin 2) :
    (sourceLocalLayerSerialCellUniformSuccessorLetterForColorAt graphData minimal
      caps coloring web corridor hunique offset hnext color hrole).portColor
        (.inl crossing) =
      (terminalInputBoundedProfileForColorAt corridor hunique
        (sourceLocalLayerNextOffset offset hnext) color
        (successorCrossingNonzeroForColorAt corridor hunique offset hnext color
          hrole)).profile.edgeColor crossing := by
  apply StrandColor.toColor_injective
  simp only [sourceLocalLayerSerialCellUniformSuccessorLetterForColorAt,
    finiteBoolOutputLetterCodeForColorAt, successorTrackedStateForColorAt,
    strandColorOfNonzero_toColor]
  rw [sourceLocalLayerBoundaryRebaseEdgeAt_successorPortRole]
  exact (sourceLocalLayerBoundaryRebaseSuccessorCutDataAt corridor hunique
    offset hnext).regionalProfile_edgeColor_toColor color
      (successorCrossingNonzeroForColorAt corridor hunique offset hnext color
        hrole) crossing |>.symm

@[simp]
theorem sourceLocalLayerSerialCellUniformSuccessorLetterForColorAt_faceContinues
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (caps : OrientedFacialPentagonCapPair graphData)
    (coloring :
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.EdgeColoring Color)
    (web : GoertzelV24ClosedWebAtGoodWord.Instance
      caps.toFacialPentagonCapPair.toPentagonCapPair.boundaryData coloring)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (color :
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.edgeSet → Color)
    (hrole : ∀ role, color
      (sourceLocalLayerBoundaryRebaseEdgeAt corridor hunique offset hnext role) ≠
        0)
    (left right : Fin
      (terminalInputBoundedProfileForColorAt corridor hunique
        (sourceLocalLayerNextOffset offset hnext) color
        (successorCrossingNonzeroForColorAt corridor hunique offset hnext color
          hrole)).faceFragmentCount.val) :
    (sourceLocalLayerSerialCellUniformSuccessorLetterForColorAt graphData minimal
      caps coloring web corridor hunique offset hnext color hrole).faceContinues
        left right =
      (terminalInputBoundedProfileForColorAt corridor hunique
        (sourceLocalLayerNextOffset offset hnext) color
        (successorCrossingNonzeroForColorAt corridor hunique offset hnext color
          hrole)).profile.faceContinues left right := by
  exact sourceLocalLayerBoundaryRebaseFiniteProfileReceiptAt_faceContinues
    corridor hunique offset hnext left right

@[simp]
theorem sourceLocalLayerSerialCellUniformSuccessorLetterForColorAt_faceLengthCap
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (caps : OrientedFacialPentagonCapPair graphData)
    (coloring :
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.EdgeColoring Color)
    (web : GoertzelV24ClosedWebAtGoodWord.Instance
      caps.toFacialPentagonCapPair.toPentagonCapPair.boundaryData coloring)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (color :
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.edgeSet → Color)
    (hrole : ∀ role, color
      (sourceLocalLayerBoundaryRebaseEdgeAt corridor hunique offset hnext role) ≠
        0)
    (fragment : Fin
      (terminalInputBoundedProfileForColorAt corridor hunique
        (sourceLocalLayerNextOffset offset hnext) color
        (successorCrossingNonzeroForColorAt corridor hunique offset hnext color
          hrole)).faceFragmentCount.val) :
    (sourceLocalLayerSerialCellUniformSuccessorLetterForColorAt graphData minimal
      caps coloring web corridor hunique offset hnext color hrole).faceLengthCap
        fragment =
      (terminalInputBoundedProfileForColorAt corridor hunique
        (sourceLocalLayerNextOffset offset hnext) color
        (successorCrossingNonzeroForColorAt corridor hunique offset hnext color
          hrole)).profile.faceLengthCap fragment := by
  exact sourceLocalLayerBoundaryRebaseFiniteProfileReceiptAt_faceLengthCap
    corridor hunique offset hnext fragment

@[simp]
theorem
    sourceLocalLayerSerialCellUniformSuccessorLetterForColorAt_fragmentContainsPort
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (caps : OrientedFacialPentagonCapPair graphData)
    (coloring :
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.EdgeColoring Color)
    (web : GoertzelV24ClosedWebAtGoodWord.Instance
      caps.toFacialPentagonCapPair.toPentagonCapPair.boundaryData coloring)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (color :
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.edgeSet → Color)
    (hrole : ∀ role, color
      (sourceLocalLayerBoundaryRebaseEdgeAt corridor hunique offset hnext role) ≠
        0)
    (fragment : Fin
      (terminalInputBoundedProfileForColorAt corridor hunique
        (sourceLocalLayerNextOffset offset hnext) color
        (successorCrossingNonzeroForColorAt corridor hunique offset hnext color
          hrole)).faceFragmentCount.val)
    (port : CorridorPort 2 1) :
    (sourceLocalLayerSerialCellUniformSuccessorLetterForColorAt graphData minimal
      caps coloring web corridor hunique offset hnext color hrole
      ).fragmentContainsPort fragment port =
      (terminalInputBoundedProfileForColorAt corridor hunique
        (sourceLocalLayerNextOffset offset hnext) color
        (successorCrossingNonzeroForColorAt corridor hunique offset hnext color
          hrole)).profile.fragmentContainsPort fragment port := by
  apply Bool.eq_iff_iff.mpr
  simp only [SourceLocalLayerSerialCellUniformSuccessorLetter.fragmentContainsPort,
    decide_eq_true_eq]
  let sourceFragment : Fin (Fintype.card
      (SourceLocalLayerBoundaryRebaseSuccessorFaceFragmentAt corridor hunique
        offset hnext)) := fragment
  change
    (∃ side : Fin 2,
      InterfaceExteriorClosure
        (sourceLocalLayerSerialCellRebaseUniformFaceSuccessorRawCodeAt corridor
          hunique offset hnext)
        (sourceLocalLayerSerialCellRebaseUniformFacePortCoordinateAt corridor
          hunique offset hnext port side)
        (sourceLocalLayerSerialCellRebaseUniformFaceFragmentCoordinateAt corridor
          hunique offset hnext
          (sourceLocalLayerBoundaryRebaseSuccessorFaceFragmentAtIndex corridor
            hunique offset hnext sourceFragment))) ↔ _
  rw [sourceLocalLayerSerialCellRebaseUniformFaceFragmentContainsPort_iff]
  have hprofile :=
    sourceLocalLayerBoundaryRebaseFiniteProfileReceiptAt_fragmentContainsPort
      corridor hunique offset hnext sourceFragment port
  simpa [sourceFragment, sourceLocalLayerBoundaryRebaseFiniteProfileReceiptAt,
    terminalInputBoundedProfileForColorAt,
    sourceLocalLayerSerialTerminalInputBoundedProfileAt] using
    congrArg (fun value => value = true) hprofile

@[simp]
theorem sourceLocalLayerSerialCellUniformSuccessorLetterForColorAt_strandConnected
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (caps : OrientedFacialPentagonCapPair graphData)
    (coloring :
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.EdgeColoring Color)
    (web : GoertzelV24ClosedWebAtGoodWord.Instance
      caps.toFacialPentagonCapPair.toPentagonCapPair.boundaryData coloring)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (color :
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.edgeSet → Color)
    (hrole : ∀ role, color
      (sourceLocalLayerBoundaryRebaseEdgeAt corridor hunique offset hnext role) ≠
        0)
    (pair : TrackedColorPair) (left right : CorridorPort 2 1) :
    (sourceLocalLayerSerialCellUniformSuccessorLetterForColorAt graphData minimal
      caps coloring web corridor hunique offset hnext color hrole
      ).strandConnected pair left right =
      (terminalInputBoundedProfileForColorAt corridor hunique
        (sourceLocalLayerNextOffset offset hnext) color
        (successorCrossingNonzeroForColorAt corridor hunique offset hnext color
          hrole)).profile.strandConnected pair left right := by
  apply Bool.eq_iff_iff.mpr
  simp only [SourceLocalLayerSerialCellUniformSuccessorLetter.strandConnected,
    decide_eq_true_eq]
  change
    (IsTrackedColor (trackedColorPairColors pair).1
        (trackedColorPairColors pair).2
        ((successorTrackedStateForColorAt corridor hunique offset hnext color
          hrole).roleColor
            (sourceLocalLayerBoundaryRebaseSuccessorPortRole left)).toColor ∧
      IsTrackedColor (trackedColorPairColors pair).1
        (trackedColorPairColors pair).2
        ((successorTrackedStateForColorAt corridor hunique offset hnext color
          hrole).roleColor
            (sourceLocalLayerBoundaryRebaseSuccessorPortRole right)).toColor ∧
      InterfaceExteriorClosure
        (sourceLocalLayerSerialCellRebaseUniformTrackedSuccessorRawCodeAt
          graphData caps coloring web corridor hunique offset hnext color pair)
        (sourceLocalLayerSerialCellRebaseUniformTrackedPortCoordinateAt graphData
          caps coloring web corridor hunique offset hnext left)
        (sourceLocalLayerSerialCellRebaseUniformTrackedPortCoordinateAt graphData
          caps coloring web corridor hunique offset hnext right)) ↔ _
  simp only [successorTrackedStateForColorAt, strandColorOfNonzero_toColor]
  rw [sourceLocalLayerBoundaryRebaseEdgeAt_successorPortRole,
    sourceLocalLayerBoundaryRebaseEdgeAt_successorPortRole]
  rw [sourceLocalLayerSerialCellRebaseUniformTrackedClosure_port_iff]
  change _ ↔
    ((sourceLocalLayerBoundaryRebaseSuccessorCutDataAt corridor hunique offset
      hnext).regionalProfile color
        (successorCrossingNonzeroForColorAt corridor hunique offset hnext color
          hrole)).strandConnected pair left right = true
  rw [(sourceLocalLayerBoundaryRebaseSuccessorCutDataAt corridor hunique offset
    hnext).regionalProfile_strandConnected_eq_true_iff]
  simp only [successorTrackedGraphForColorAt,
    sourceLocalLayerBoundaryRebaseSuccessorCutDataAt,
    sourceLocalLayerSerialTerminalInputCutDataAt_regionEdges]
  have hports := sourceLocalLayerSerialTerminalInputCutDataAt_portsInRegion
    corridor hunique (sourceLocalLayerNextOffset offset hnext)
  constructor
  · rintro ⟨hleftColor, hrightColor, hreachable⟩
    exact ⟨hports left, hports right, hleftColor, hrightColor, hreachable⟩
  · rintro ⟨_hleftRegion, _hrightRegion, hleftColor, hrightColor, hreachable⟩
    exact ⟨hleftColor, hrightColor, hreachable⟩

/-- The colouring-parametric uniform finite successor letter decodes exactly
to all five fields of the literal next terminal-aware corridor profile. -/
theorem sourceLocalLayerSerialCellUniformSuccessorLetterForColorAt_outputProfile_eq
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (caps : OrientedFacialPentagonCapPair graphData)
    (coloring :
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.EdgeColoring Color)
    (web : GoertzelV24ClosedWebAtGoodWord.Instance
      caps.toFacialPentagonCapPair.toPentagonCapPair.boundaryData coloring)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (color :
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.edgeSet → Color)
    (hrole : ∀ role, color
      (sourceLocalLayerBoundaryRebaseEdgeAt corridor hunique offset hnext role) ≠
        0) :
    (sourceLocalLayerSerialCellUniformSuccessorLetterForColorAt graphData minimal
      caps coloring web corridor hunique offset hnext color hrole).outputProfile =
      terminalInputBoundedProfileForColorAt corridor hunique
        (sourceLocalLayerNextOffset offset hnext) color
        (successorCrossingNonzeroForColorAt corridor hunique offset hnext color
          hrole) := by
  classical
  simp only [SourceLocalLayerSerialCellUniformSuccessorLetter.outputProfile,
    sourceLocalLayerSerialCellUniformSuccessorLetterForColorAt]
  rw [BoundedCorridorCutProfile.mk.injEq]
  refine ⟨rfl, ?_⟩
  apply heq_of_eq
  rw [CorridorCutProfile.mk.injEq]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · funext crossing
    exact sourceLocalLayerSerialCellUniformSuccessorLetterForColorAt_edgeColor
      graphData minimal caps coloring web corridor hunique offset hnext color
      hrole crossing
  · funext pair left right
    exact sourceLocalLayerSerialCellUniformSuccessorLetterForColorAt_strandConnected
      graphData minimal caps coloring web corridor hunique offset hnext color
      hrole pair left right
  · funext left right
    exact sourceLocalLayerSerialCellUniformSuccessorLetterForColorAt_faceContinues
      graphData minimal caps coloring web corridor hunique offset hnext color
      hrole left right
  · funext fragment port
    exact
      sourceLocalLayerSerialCellUniformSuccessorLetterForColorAt_fragmentContainsPort
        graphData minimal caps coloring web corridor hunique offset hnext color
        hrole fragment port
  · funext fragment
    exact sourceLocalLayerSerialCellUniformSuccessorLetterForColorAt_faceLengthCap
      graphData minimal caps coloring web corridor hunique offset hnext color
      hrole fragment

end

end GoertzelV24ClosedWebLocalLayerSerialCellUniformSuccessorColorParametric

end Mettapedia.GraphTheory.FourColor
