import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalLayerSerialCellUniformSuccessorCoordinates
import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalLayerSerialBoundaryRebaseFiniteOutputDecoder

/-!
# One finite five-field successor letter on the uniform interface

The tracked and facial recurrences now share fixed, source-independent bounds,
and the named successor observations have exact coordinates in those carriers.
This file packages the resulting output as one finite letter.

Crossing colours and the two endpoint colour guards are stored as three named
port colours.  Tracked connectivity is decoded from those guards and the
forty-nine-edge graph-free closure.  Port incidence is decoded from the two
literal dart occurrences of a port and the forty-eight-dart facial closure.
Ambient-face continuation and the capped regional face length remain explicit
finite fields: neither is determined by regional component connectivity alone.

The source constructor below uses the exact cumulative recurrences and the
already-proved finite facial receipt.  It introduces no ambient vertices,
edges, or darts into the letter type.  Realizable initial states and closure
enumeration remain later obligations.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebLocalLayerSerialCellUniformSuccessorLetter

open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAnnularEmbedding.ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAtGoodWord
open GoertzelV24ClosedWebAtGoodWord.Instance
open GoertzelV24ClosedWebAtGoodWord.Instance.LocalLayerFormation
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24ClosedWebLocalLayerSerialCellUniformFaceRecurrence
open GoertzelV24ClosedWebLocalLayerSerialCellUniformSuccessorCoordinates
open GoertzelV24ClosedWebLocalLayerSerialCellUniformTrackedRecurrence
open GoertzelV24ClosedWebLocalLayerSerialBoundaryRebaseTrackedColorParametric
open GoertzelV24BoundaryProfileFiniteState
open GoertzelV24CorridorProfile
open GoertzelV24FaceOrbitIncidence
open GoertzelV24FacialPentagonCap
open GoertzelV24HexSlabConnectivityProfile
open GoertzelV24InterfaceDeletionComponentFactor
open GoertzelV24InterfaceDeletionComponentFactorGraphFree
open GoertzelV24TwoEdgeCutMinimality
open GoertzelV24TwoPentagonCapOpening
open GoertzelV24WindingClassification
open SimpleGraphDartRotation

/-- A finite output letter for one literal Cell followed by its boundary
rebase.  Every dependent coordinate lives below a fixed numerical bound. -/
structure SourceLocalLayerSerialCellUniformSuccessorLetter where
  outputCount : Fin 5
  trackedCode : BoundedInterfaceExteriorFamilyCode 49 TrackedColorPair
  faceCode : BoundedInterfaceExteriorFamilyCode 48 Unit
  portColor : CorridorPort 2 1 → StrandColor
  trackedPortCoordinate :
    CorridorPort 2 1 → Fin trackedCode.vertexCount.val
  faceFragmentCoordinate :
    Fin outputCount.val → Fin faceCode.vertexCount.val
  facePortCoordinate :
    CorridorPort 2 1 → Fin 2 → Fin faceCode.vertexCount.val
  faceContinues : Fin outputCount.val → Fin outputCount.val → Bool
  faceLengthCap : Fin outputCount.val → Fin 6

noncomputable instance :
    DecidableEq SourceLocalLayerSerialCellUniformSuccessorLetter :=
  Classical.decEq _

private abbrev sourceLocalLayerSerialCellUniformSuccessorLetterCode :=
  Σ outputCount : Fin 5,
    Σ trackedCode : BoundedInterfaceExteriorFamilyCode 49 TrackedColorPair,
      Σ faceCode : BoundedInterfaceExteriorFamilyCode 48 Unit,
        (CorridorPort 2 1 → StrandColor) ×
        (CorridorPort 2 1 → Fin trackedCode.vertexCount.val) ×
        (Fin outputCount.val → Fin faceCode.vertexCount.val) ×
        (CorridorPort 2 1 → Fin 2 → Fin faceCode.vertexCount.val) ×
        (Fin outputCount.val → Fin outputCount.val → Bool) ×
        (Fin outputCount.val → Fin 6)

private def sourceLocalLayerSerialCellUniformSuccessorLetterEquiv :
    SourceLocalLayerSerialCellUniformSuccessorLetter ≃
      sourceLocalLayerSerialCellUniformSuccessorLetterCode where
  toFun letter :=
    ⟨letter.outputCount, letter.trackedCode, letter.faceCode,
      letter.portColor, letter.trackedPortCoordinate,
      letter.faceFragmentCoordinate, letter.facePortCoordinate,
      letter.faceContinues, letter.faceLengthCap⟩
  invFun data := by
    rcases data with ⟨outputCount, trackedCode, faceCode, portColor,
      trackedPortCoordinate, faceFragmentCoordinate, facePortCoordinate,
      faceContinues, faceLengthCap⟩
    exact {
      outputCount := outputCount
      trackedCode := trackedCode
      faceCode := faceCode
      portColor := portColor
      trackedPortCoordinate := trackedPortCoordinate
      faceFragmentCoordinate := faceFragmentCoordinate
      facePortCoordinate := facePortCoordinate
      faceContinues := faceContinues
      faceLengthCap := faceLengthCap }
  left_inv letter := by cases letter; rfl
  right_inv data := by
    rcases data with ⟨outputCount, trackedCode, faceCode, portColor,
      trackedPortCoordinate, faceFragmentCoordinate, facePortCoordinate,
      faceContinues, faceLengthCap⟩
    rfl

set_option synthInstance.maxSize 256 in
deriving noncomputable instance Fintype for
  sourceLocalLayerSerialCellUniformSuccessorLetterCode

noncomputable instance :
    Fintype SourceLocalLayerSerialCellUniformSuccessorLetter :=
  Fintype.ofEquiv _ sourceLocalLayerSerialCellUniformSuccessorLetterEquiv.symm

/-- Graph-free tracked-connectivity bit decoded from the port colour guards
and the exact tracked closure. -/
noncomputable def
    SourceLocalLayerSerialCellUniformSuccessorLetter.strandConnected
    (letter : SourceLocalLayerSerialCellUniformSuccessorLetter)
    (pair : TrackedColorPair) (left right : CorridorPort 2 1) : Bool := by
  classical
  exact decide
    (IsTrackedColor (trackedColorPairColors pair).1
        (trackedColorPairColors pair).2 (letter.portColor left).toColor ∧
      IsTrackedColor (trackedColorPairColors pair).1
        (trackedColorPairColors pair).2 (letter.portColor right).toColor ∧
      InterfaceExteriorClosure (letter.trackedCode.code pair)
        (letter.trackedPortCoordinate left)
        (letter.trackedPortCoordinate right))

/-- Graph-free fragment/port incidence decoded from the two literal port
occurrences and the exact facial closure. -/
noncomputable def
    SourceLocalLayerSerialCellUniformSuccessorLetter.fragmentContainsPort
    (letter : SourceLocalLayerSerialCellUniformSuccessorLetter)
    (fragment : Fin letter.outputCount.val) (port : CorridorPort 2 1) : Bool := by
  classical
  exact decide (∃ side : Fin 2,
    InterfaceExteriorClosure (letter.faceCode.code ())
      (letter.facePortCoordinate port side)
      (letter.faceFragmentCoordinate fragment))

/-- Decode all five source-profile coordinates from one uniform finite
successor letter. -/
noncomputable def
    SourceLocalLayerSerialCellUniformSuccessorLetter.outputProfile
    (letter : SourceLocalLayerSerialCellUniformSuccessorLetter) :
    BoundedCorridorCutProfile 2 1 4 where
  faceFragmentCount := letter.outputCount
  profile := {
    edgeColor := fun crossing => letter.portColor (.inl crossing)
    strandConnected := letter.strandConnected
    faceContinues := letter.faceContinues
    fragmentContainsPort := letter.fragmentContainsPort
    faceLengthCap := letter.faceLengthCap }

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance cellUniformSuccessorLetterEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

local instance cellUniformSuccessorLetterOpenedGraphDecidableRel
    (caps : OrientedFacialPentagonCapPair (G := G) graphData) :
    DecidableRel
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.Adj :=
  Classical.decRel _

/-- The exact finite uniform successor letter extracted from one literal
source Cell--rebase step. -/
noncomputable def sourceLocalLayerSerialCellUniformSuccessorLetterAt
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
    (hnext : offset.val + 1 < blockLength - 3) :
    SourceLocalLayerSerialCellUniformSuccessorLetter := by
  let output := sourceLocalLayerSerialTerminalInputBoundedProfileAt corridor
    hunique (sourceLocalLayerNextOffset offset hnext)
  let receipt := sourceLocalLayerBoundaryRebaseFiniteProfileReceiptAt corridor
    hunique offset hnext
  let trackedCode :=
    sourceLocalLayerSerialCellRebaseUniformTrackedBoundedSuccessorCodeAt
      graphData minimal caps coloring web corridor hunique offset hnext coloring
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
theorem sourceLocalLayerSerialCellUniformSuccessorLetterAt_edgeColor
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
    (crossing : Fin 2) :
    (sourceLocalLayerSerialCellUniformSuccessorLetterAt graphData minimal caps
      coloring web corridor hunique offset hnext).portColor (.inl crossing) =
      (sourceLocalLayerSerialTerminalInputBoundedProfileAt corridor hunique
        (sourceLocalLayerNextOffset offset hnext)).profile.edgeColor crossing := by
  exact sourceLocalLayerBoundaryRebaseFiniteProfileReceiptAt_edgeColor corridor
    hunique offset hnext crossing

@[simp]
theorem sourceLocalLayerSerialCellUniformSuccessorLetterAt_faceContinues
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
    (left right : Fin
      (sourceLocalLayerSerialTerminalInputBoundedProfileAt corridor hunique
        (sourceLocalLayerNextOffset offset hnext)).faceFragmentCount.val) :
    (sourceLocalLayerSerialCellUniformSuccessorLetterAt graphData minimal caps
      coloring web corridor hunique offset hnext).faceContinues left right =
      (sourceLocalLayerSerialTerminalInputBoundedProfileAt corridor hunique
        (sourceLocalLayerNextOffset offset hnext)).profile.faceContinues
          left right := by
  exact sourceLocalLayerBoundaryRebaseFiniteProfileReceiptAt_faceContinues
    corridor hunique offset hnext left right

@[simp]
theorem sourceLocalLayerSerialCellUniformSuccessorLetterAt_faceLengthCap
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
    (fragment : Fin
      (sourceLocalLayerSerialTerminalInputBoundedProfileAt corridor hunique
        (sourceLocalLayerNextOffset offset hnext)).faceFragmentCount.val) :
    (sourceLocalLayerSerialCellUniformSuccessorLetterAt graphData minimal caps
      coloring web corridor hunique offset hnext).faceLengthCap fragment =
      (sourceLocalLayerSerialTerminalInputBoundedProfileAt corridor hunique
        (sourceLocalLayerNextOffset offset hnext)).profile.faceLengthCap
          fragment := by
  exact sourceLocalLayerBoundaryRebaseFiniteProfileReceiptAt_faceLengthCap
    corridor hunique offset hnext fragment

@[simp]
theorem sourceLocalLayerSerialCellUniformSuccessorLetterAt_fragmentContainsPort
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
    (fragment : Fin
      (sourceLocalLayerSerialTerminalInputBoundedProfileAt corridor hunique
        (sourceLocalLayerNextOffset offset hnext)).faceFragmentCount.val)
    (port : CorridorPort 2 1) :
    (sourceLocalLayerSerialCellUniformSuccessorLetterAt graphData minimal caps
      coloring web corridor hunique offset hnext).fragmentContainsPort
        fragment port =
      (sourceLocalLayerSerialTerminalInputBoundedProfileAt corridor hunique
        (sourceLocalLayerNextOffset offset hnext)).profile.fragmentContainsPort
          fragment port := by
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
  simpa [sourceFragment, sourceLocalLayerBoundaryRebaseFiniteProfileReceiptAt]
    using congrArg (fun value => value = true) hprofile

@[simp]
theorem sourceLocalLayerSerialCellUniformSuccessorLetterAt_strandConnected
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
    (pair : TrackedColorPair) (left right : CorridorPort 2 1) :
    (sourceLocalLayerSerialCellUniformSuccessorLetterAt graphData minimal caps
      coloring web corridor hunique offset hnext).strandConnected
        pair left right =
      (sourceLocalLayerSerialTerminalInputBoundedProfileAt corridor hunique
        (sourceLocalLayerNextOffset offset hnext)).profile.strandConnected
          pair left right := by
  apply Bool.eq_iff_iff.mpr
  simp only [SourceLocalLayerSerialCellUniformSuccessorLetter.strandConnected,
    decide_eq_true_eq]
  change
    (IsTrackedColor (trackedColorPairColors pair).1
        (trackedColorPairColors pair).2
        (((sourceLocalLayerBoundaryRebaseFiniteProfileReceiptAt corridor hunique
          offset hnext).tracked.roleColor
            (sourceLocalLayerBoundaryRebaseSuccessorPortRole left)).toColor) ∧
      IsTrackedColor (trackedColorPairColors pair).1
        (trackedColorPairColors pair).2
        (((sourceLocalLayerBoundaryRebaseFiniteProfileReceiptAt corridor hunique
          offset hnext).tracked.roleColor
            (sourceLocalLayerBoundaryRebaseSuccessorPortRole right)).toColor) ∧
      InterfaceExteriorClosure
        (sourceLocalLayerSerialCellRebaseUniformTrackedSuccessorRawCodeAt
          graphData caps coloring web corridor hunique offset hnext coloring
          pair)
        (sourceLocalLayerSerialCellRebaseUniformTrackedPortCoordinateAt graphData
          caps coloring web corridor hunique offset hnext left)
        (sourceLocalLayerSerialCellRebaseUniformTrackedPortCoordinateAt graphData
          caps coloring web corridor hunique offset hnext right)) ↔ _
  simp only [sourceLocalLayerBoundaryRebaseFiniteProfileReceiptAt]
  rw [sourceLocalLayerBoundaryRebaseSuccessorTrackedStateAt_roleColor_toColor,
    sourceLocalLayerBoundaryRebaseSuccessorTrackedStateAt_roleColor_toColor]
  rw [sourceLocalLayerBoundaryRebaseEdgeAt_successorPortRole,
    sourceLocalLayerBoundaryRebaseEdgeAt_successorPortRole]
  rw [sourceLocalLayerSerialCellRebaseUniformTrackedClosure_port_iff]
  change _ ↔
    ((sourceLocalLayerBoundaryRebaseSuccessorCutDataAt corridor hunique offset
      hnext).regionalProfile coloring (fun _ => web.tait _)
      ).strandConnected pair left right = true
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

/-- The one uniform finite successor letter decodes exactly to all five fields
of the literal next terminal-aware corridor profile. -/
theorem sourceLocalLayerSerialCellUniformSuccessorLetterAt_outputProfile_eq
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
    (hnext : offset.val + 1 < blockLength - 3) :
    (sourceLocalLayerSerialCellUniformSuccessorLetterAt graphData minimal caps
      coloring web corridor hunique offset hnext).outputProfile =
      sourceLocalLayerSerialTerminalInputBoundedProfileAt corridor hunique
        (sourceLocalLayerNextOffset offset hnext) := by
  classical
  simp only [SourceLocalLayerSerialCellUniformSuccessorLetter.outputProfile,
    sourceLocalLayerSerialCellUniformSuccessorLetterAt]
  rw [BoundedCorridorCutProfile.mk.injEq]
  refine ⟨rfl, ?_⟩
  apply heq_of_eq
  rw [CorridorCutProfile.mk.injEq]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · funext crossing
    exact sourceLocalLayerSerialCellUniformSuccessorLetterAt_edgeColor
      graphData minimal caps coloring web corridor hunique offset hnext crossing
  · funext pair left right
    exact sourceLocalLayerSerialCellUniformSuccessorLetterAt_strandConnected
      graphData minimal caps coloring web corridor hunique offset hnext pair left
      right
  · funext left right
    exact sourceLocalLayerSerialCellUniformSuccessorLetterAt_faceContinues
      graphData minimal caps coloring web corridor hunique offset hnext left right
  · funext fragment port
    exact sourceLocalLayerSerialCellUniformSuccessorLetterAt_fragmentContainsPort
      graphData minimal caps coloring web corridor hunique offset hnext fragment
      port
  · funext fragment
    exact sourceLocalLayerSerialCellUniformSuccessorLetterAt_faceLengthCap
      graphData minimal caps coloring web corridor hunique offset hnext fragment

end

end GoertzelV24ClosedWebLocalLayerSerialCellUniformSuccessorLetter

end Mettapedia.GraphTheory.FourColor
