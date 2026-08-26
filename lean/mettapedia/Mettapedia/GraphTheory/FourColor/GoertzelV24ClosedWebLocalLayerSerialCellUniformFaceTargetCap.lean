import Mathlib.Data.Bool.Basic
import Mathlib.Data.Prod.Lex
import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalLayerSerialCellUniformFaceTargetIncidence
import Mettapedia.GraphTheory.FourColor.GoertzelV24InterfaceExteriorLabelCapFactorForget

/-!
# Cap-six facial data on the rolling successor interface

The literal Cell successor is first observed on its uniform finite facial
carrier.  Forgetting uniform coordinates can merge old strict-exterior
components and can expose forgotten coordinates as new exterior labels.  This
file instantiates the finite weighted contraction with the direction-sensitive
entry decoder for the next rolling interface.

The construction remains parametric in the corridor boundary data.  It does
not enumerate ambient graphs or inspect the cumulative prefix beyond the
bounded uniform successor code.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebLocalLayerSerialCellUniformFaceTargetCap

open GoertzelV24BoundedCarrierGraphFamilyCode
open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAnnularEmbedding.ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAtGoodWord
open GoertzelV24ClosedWebAtGoodWord.Instance
open GoertzelV24ClosedWebAtGoodWord.Instance.LocalLayerFormation
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24ClosedWebLocalLayerSerialCellUniformFaceRecurrence
open GoertzelV24ClosedWebLocalLayerSerialCellUniformFaceTargetCode
open GoertzelV24ClosedWebLocalLayerSerialCellUniformFaceTargetIncidence
open GoertzelV24CorridorProfile
open GoertzelV24FaceOrbitIncidence
open GoertzelV24FacialPentagonCap
open GoertzelV24InterfaceExteriorLabelCapFactor
open GoertzelV24InterfaceExteriorLabelCapFactorForget
open GoertzelV24InterfaceDeletionComponentFactor
open GoertzelV24InterfaceDeletionComponentFactorForget
open GoertzelV24InterfaceDeletionComponentFactorForgetExterior
open GoertzelV24RotationFaceInterfaceExteriorLabelCap
open GoertzelV24TwoEdgeCutMinimality
open GoertzelV24TwoPentagonCapOpening
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance uniformFaceTargetCapEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

/-- Canonical executable order on oriented finite incidences. -/
local instance uniformFaceTargetCapIncidenceLinearOrder {n : Nat} :
    LinearOrder (Fin n × Bool) :=
  LinearOrder.lift' (fun incidence : Fin n × Bool => toLex incidence)
    toLex.injective

local instance uniformFaceTargetCapOpenedGraphDecidableRel
    (caps : OrientedFacialPentagonCapPair (G := G) graphData) :
    DecidableRel
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.Adj :=
  Classical.decRel _

/-- The exact cap-six facial code of the literal successor graph on the
uniform Cell--rebase carrier. -/
noncomputable def sourceLocalLayerSerialCellRebaseUniformFaceSuccessorLabelCapSixCodeAt
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : GoertzelV24ClosedWebAtGoodWord.Instance data coloring}
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3) :
    BoundedInterfaceExteriorLabelCapCode
      (Fin (sourceLocalLayerSerialCellRebaseFaceInteractionCarrierAt corridor
        hunique offset hnext).card)
      (Fin (sourceLocalLayerSerialCellRebaseFaceInteractionCarrierAt corridor
        hunique offset hnext).card × Bool) 6 :=
  exactFaceInterfaceExteriorLabelCapCode web.annular.RS
    (sourceLocalLayerSerialTerminalInputRegionAt corridor hunique
      (sourceLocalLayerNextOffset offset hnext))
    (sourceLocalLayerSerialCellRebaseUniformFaceDartAt corridor hunique offset
      hnext)
    6

/-- Literal target-coordinate activity in the successor regional face graph. -/
noncomputable def sourceLocalLayerSerialCellRebaseUniformFaceTargetPresentAt
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : GoertzelV24ClosedWebAtGoodWord.Instance data coloring}
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3) :
    Fin (sourceLocalLayerSerialFaceTransitionCarrierAt corridor hunique
      (sourceLocalLayerNextOffset offset hnext)).card → Bool :=
  fun slot => decide (
    web.annular.RS.edgeOf
      (((carrierCoordinate
        (sourceLocalLayerSerialFaceTransitionCarrierAt corridor hunique
          (sourceLocalLayerNextOffset offset hnext))).symm slot).1) ∈
      sourceLocalLayerSerialTerminalInputRegionAt corridor hunique
        (sourceLocalLayerNextOffset offset hnext))

/-- Finite cap-six contraction from the uniform successor carrier to the next
rolling facial carrier. -/
noncomputable def sourceLocalLayerSerialCellRebaseUniformFaceTargetLabelCapSixCodeAt
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
    BoundedInterfaceExteriorLabelCapCode
      (Fin (sourceLocalLayerSerialFaceTransitionCarrierAt corridor hunique
        (sourceLocalLayerNextOffset offset hnext)).card)
      (Fin (sourceLocalLayerSerialFaceTransitionCarrierAt corridor hunique
        (sourceLocalLayerNextOffset offset hnext)).card × Bool) 6 :=
  partialContractedInterfaceExteriorLabelCapCode
    (sourceLocalLayerSerialCellRebaseUniformFaceSuccessorLabelCapSixCodeAt
      corridor hunique offset hnext)
    (sourceLocalLayerSerialCellRebaseUniformFaceTargetSourceAt corridor hunique
      offset hnext)
    Prod.fst
    (sourceLocalLayerSerialCellRebaseUniformFaceTargetPresentAt corridor hunique
      offset hnext)
    (sourceLocalLayerSerialCellRebaseUniformFaceTargetEntryAt graphData minimal
      caps coloring web corridor hunique offset hnext)

/-- Every decoded target incidence points to a physically live contraction
atom.  The left branch is a forgotten live uniform dart; the right branch is
an already-live uniform strict-exterior incidence. -/
theorem sourceLocalLayerSerialCellRebaseUniformFaceTargetEntryAt_atomPresent
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
    (incidence : Fin
      (sourceLocalLayerSerialFaceTransitionCarrierAt corridor hunique
        (sourceLocalLayerNextOffset offset hnext)).card × Bool)
    (atom : SourceLocalLayerSerialCellRebaseUniformFaceTargetEntry
      (sourceLocalLayerSerialCellRebaseFaceInteractionCarrierAt corridor
        hunique offset hnext).card)
    (hentry :
      sourceLocalLayerSerialCellRebaseUniformFaceTargetEntryAt graphData minimal
        caps coloring web corridor hunique offset hnext incidence = some atom) :
    exteriorLabelCapContractionAtomPresent
        (sourceLocalLayerSerialCellRebaseUniformFaceSuccessorLabelCapSixCodeAt
          corridor hunique offset hnext)
        (sourceLocalLayerSerialCellRebaseUniformFaceTargetSourceAt corridor
          hunique offset hnext)
        atom = true := by
  classical
  let graph := sourceLocalLayerBoundaryRebaseSuccessorFaceGraphAt corridor
    hunique offset hnext
  let target := sourceLocalLayerSerialFaceTransitionCarrierAt corridor hunique
    (sourceLocalLayerNextOffset offset hnext)
  let uniform := sourceLocalLayerSerialCellRebaseFaceInteractionCarrierAt
    corridor hunique offset hnext
  let targetDartAt := fun slot : Fin target.card =>
    ((carrierCoordinate target).symm slot).1
  let uniformDartAt := sourceLocalLayerSerialCellRebaseUniformFaceDartAt
    corridor hunique offset hnext
  let retain := sourceLocalLayerSerialCellRebaseUniformFaceTargetSourceAt
    corridor hunique offset hnext
  have hpresentTarget : ExteriorIncidencePresent graph targetDartAt Prod.fst
      (faceInterfaceIncidenceVertex web.annular.RS targetDartAt) incidence :=
    (sourceLocalLayerSerialCellRebaseUniformFaceTargetEntryAt_isSome_iff
      graphData minimal caps coloring web corridor hunique offset hnext
        incidence).1 (by simp [hentry])
  cases atom with
  | inl uniformSlot =>
      unfold exteriorLabelCapContractionAtomPresent
      have hleft :=
        sourceLocalLayerSerialCellRebaseUniformFaceTargetEntryAt_left graphData
          minimal caps coloring web corridor hunique offset hnext incidence
            uniformSlot hentry
      rcases hleft with ⟨hvertex, hnotRetained⟩
      simp only [Bool.and_eq_true]
      constructor
      · apply (exactFaceInterfaceExteriorLabelCapCode_interfacePresent_iff
          web.annular.RS
          (sourceLocalLayerSerialTerminalInputRegionAt corridor hunique
            (sourceLocalLayerNextOffset offset hnext))
          uniformDartAt uniformSlot 6).2
        have houtsideRegion : web.annular.RS.edgeOf
              (faceInterfaceIncidenceVertex web.annular.RS targetDartAt
                incidence) ∈
            sourceLocalLayerSerialTerminalInputRegionAt corridor hunique
              (sourceLocalLayerNextOffset offset hnext) :=
          hpresentTarget.2.2.2.2
        simpa [uniformDartAt, targetDartAt] using hvertex.symm ▸ houtsideRegion
      · apply (codeSurvivesPartialRetained_exact_iff graph uniformDartAt
          retain uniformSlot).2
        intro removedSlot hremoved heq
        rw [partialRetainedCoordinateMask_eq_true_iff] at hremoved
        rcases hremoved with ⟨targetSlot, hsource⟩
        have hslot : uniformSlot = removedSlot :=
          (sourceLocalLayerSerialCellRebaseUniformFaceDartAt_injective corridor
            hunique offset hnext) heq
        subst removedSlot
        exact hnotRetained targetSlot hsource
  | inr uniformIncidence =>
      unfold exteriorLabelCapContractionAtomPresent
      have hright :=
        sourceLocalLayerSerialCellRebaseUniformFaceTargetEntryAt_right graphData
          minimal caps coloring web corridor hunique offset hnext incidence
            uniformIncidence hentry
      exact (exactFaceInterfaceExteriorLabelCapCode_incidencePresent_iff
        web.annular.RS
        (sourceLocalLayerSerialTerminalInputRegionAt corridor hunique
          (sourceLocalLayerNextOffset offset hnext))
        uniformDartAt uniformIncidence 6).2 hright.2

/-- The finite decoder marks exactly the literal oriented incidences of the
rolling target exterior. -/
@[simp]
theorem sourceLocalLayerSerialCellRebaseUniformFaceTargetLabelCapSixCodeAt_incidencePresent_iff
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
    (incidence : Fin
      (sourceLocalLayerSerialFaceTransitionCarrierAt corridor hunique
        (sourceLocalLayerNextOffset offset hnext)).card × Bool) :
    (sourceLocalLayerSerialCellRebaseUniformFaceTargetLabelCapSixCodeAt
      graphData minimal caps coloring web corridor hunique offset hnext
      ).incidencePresent incidence = true ↔
      let graph := sourceLocalLayerBoundaryRebaseSuccessorFaceGraphAt corridor
        hunique offset hnext
      let target := sourceLocalLayerSerialFaceTransitionCarrierAt corridor
        hunique (sourceLocalLayerNextOffset offset hnext)
      let targetDartAt := fun slot : Fin target.card =>
        ((carrierCoordinate target).symm slot).1
      ExteriorIncidencePresent graph targetDartAt Prod.fst
        (faceInterfaceIncidenceVertex web.annular.RS targetDartAt)
        incidence := by
  classical
  dsimp only
  let entry := sourceLocalLayerSerialCellRebaseUniformFaceTargetEntryAt
    graphData minimal caps coloring web corridor hunique offset hnext
  change
    exteriorLabelCapContractionEntryPresent
        (sourceLocalLayerSerialCellRebaseUniformFaceSuccessorLabelCapSixCodeAt
          corridor hunique offset hnext)
        (sourceLocalLayerSerialCellRebaseUniformFaceTargetSourceAt corridor
          hunique offset hnext)
        entry incidence = true ↔ _
  rw [exteriorLabelCapContractionEntryPresent_eq_true_iff]
  constructor
  · rintro ⟨atom, hentry, _⟩
    exact
      (sourceLocalLayerSerialCellRebaseUniformFaceTargetEntryAt_isSome_iff
        graphData minimal caps coloring web corridor hunique offset hnext
          incidence).1 (by simp [entry, hentry])
  · intro hpresent
    have hsome :=
      (sourceLocalLayerSerialCellRebaseUniformFaceTargetEntryAt_isSome_iff
        graphData minimal caps coloring web corridor hunique offset hnext
          incidence).2 hpresent
    cases hentry : entry incidence with
    | none => simp [entry, hentry] at hsome
    | some atom =>
        exact ⟨atom, rfl,
          sourceLocalLayerSerialCellRebaseUniformFaceTargetEntryAt_atomPresent
            graphData minimal caps coloring web corridor hunique offset hnext
              incidence atom (by simpa [entry] using hentry)⟩

/-- Target-coordinate activity is the literal successor-region predicate. -/
@[simp]
theorem sourceLocalLayerSerialCellRebaseUniformFaceTargetLabelCapSixCodeAt_interfacePresent_iff
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
    (slot : Fin
      (sourceLocalLayerSerialFaceTransitionCarrierAt corridor hunique
        (sourceLocalLayerNextOffset offset hnext)).card) :
    (sourceLocalLayerSerialCellRebaseUniformFaceTargetLabelCapSixCodeAt
      graphData minimal caps coloring web corridor hunique offset hnext
      ).interfacePresent slot = true ↔
      web.annular.RS.edgeOf
          (((carrierCoordinate
            (sourceLocalLayerSerialFaceTransitionCarrierAt corridor hunique
              (sourceLocalLayerNextOffset offset hnext))).symm slot).1) ∈
        sourceLocalLayerSerialTerminalInputRegionAt corridor hunique
          (sourceLocalLayerNextOffset offset hnext) := by
  simp [sourceLocalLayerSerialCellRebaseUniformFaceTargetLabelCapSixCodeAt,
    partialContractedInterfaceExteriorLabelCapCode,
    sourceLocalLayerSerialCellRebaseUniformFaceTargetPresentAt]

/-- Forgetting labels does not alter the already-verified rolling successor
connectivity row. -/
@[simp]
theorem sourceLocalLayerSerialCellRebaseUniformFaceTargetLabelCapSixCodeAt_connectivity
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
    (sourceLocalLayerSerialCellRebaseUniformFaceTargetLabelCapSixCodeAt
      graphData minimal caps coloring web corridor hunique offset hnext
      ).connectivity =
      sourceLocalLayerSerialCellRebaseUniformFaceTargetRawCodeAt corridor
        hunique offset hnext := by
  unfold sourceLocalLayerSerialCellRebaseUniformFaceTargetLabelCapSixCodeAt
  unfold sourceLocalLayerSerialCellRebaseUniformFaceSuccessorLabelCapSixCodeAt
  change partialContractedInterfaceExteriorCode
      (exactInterfaceExteriorCode
        (sourceLocalLayerBoundaryRebaseSuccessorFaceGraphAt corridor hunique
          offset hnext)
        (sourceLocalLayerSerialCellRebaseUniformFaceDartAt corridor hunique
          offset hnext))
      (sourceLocalLayerSerialCellRebaseUniformFaceTargetSourceAt corridor hunique
        offset hnext) = _
  rw [← sourceLocalLayerSerialCellRebaseUniformFaceSuccessorCodeAt_exact
    corridor hunique offset hnext]
  rfl

end

end GoertzelV24ClosedWebLocalLayerSerialCellUniformFaceTargetCap

end Mettapedia.GraphTheory.FourColor
