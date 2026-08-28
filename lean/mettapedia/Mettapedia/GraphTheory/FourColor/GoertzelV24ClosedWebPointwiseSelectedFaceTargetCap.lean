import Mathlib.Data.Bool.Basic
import Mathlib.Data.Prod.Lex
import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebPointwiseSelectedFaceTargetIncidence
import Mettapedia.GraphTheory.FourColor.GoertzelV24InterfaceExteriorLabelCapFactorForgetExact

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

namespace GoertzelV24ClosedWebPointwiseSelectedFaceTargetCap

open GoertzelV24AnnularInteriorFaceUniqueness
open GoertzelV24BoundedCarrierGraphFamilyCode
open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAnnularEmbedding.ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAtGoodWord
open GoertzelV24ClosedWebAtGoodWord.Formation
open GoertzelV24ClosedWebAtGoodWord.Instance
open GoertzelV24ClosedWebAtGoodWord.Instance.LocalLayerFormation
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24ClosedWebPointwiseSelectedFaceUniformRecurrence
open GoertzelV24ClosedWebPointwiseSelectedFaceTargetCode
open GoertzelV24ClosedWebPointwiseSelectedFaceTargetIncidence
open GoertzelV24CorridorProfile
open GoertzelV24FaceOrbitIncidence
open GoertzelV24FacialPentagonCap
open GoertzelV24InterfaceExteriorLabelCapFactor
open GoertzelV24InterfaceExteriorLabelCapFactorForget
open GoertzelV24InterfaceExteriorLabelCapFactorForgetExact
open GoertzelV24InterfaceDeletionComponentFactor
open GoertzelV24InterfaceDeletionComponentFactorForget
open GoertzelV24InterfaceDeletionComponentFactorForgetExterior
open GoertzelV24RotationFaceInterfaceExteriorLabelCap
open GoertzelV24RotationFaceRegionalDartGraph
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

/-- Every edge from a uniform successor coordinate into its strict exterior
has one of the two canonical facial incidence names. -/
theorem pointwiseSelectedSourceLocalLayerSerialCellRebaseUniformFaceSuccessor_incidenceComplete
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : GoertzelV24ClosedWebAtGoodWord.Instance data coloring}
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      web.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (slot : Fin (pointwiseSelectedSourceLocalLayerSerialCellRebaseFaceInteractionCarrierAt
      web.toFormation corridor hinterior offset hnext).card)
    (outside : web.annular.RS.D)
    (houtside : OutsideInterface
      (pointwiseSelectedSourceLocalLayerSerialCellRebaseUniformFaceDartAt web.toFormation corridor hinterior offset
        hnext) outside)
    (hadj : (pointwiseSelectedSourceLocalLayerBoundaryRebaseSuccessorFaceGraphAt web.toFormation corridor
      hinterior offset hnext).Adj
        (pointwiseSelectedSourceLocalLayerSerialCellRebaseUniformFaceDartAt web.toFormation corridor hinterior
          offset hnext slot) outside) :
    ∃ incidence :
        Fin (pointwiseSelectedSourceLocalLayerSerialCellRebaseFaceInteractionCarrierAt web.toFormation corridor
          hinterior offset hnext).card × Bool,
      incidence.1 = slot ∧
        faceInterfaceIncidenceVertex web.annular.RS
          (pointwiseSelectedSourceLocalLayerSerialCellRebaseUniformFaceDartAt web.toFormation corridor hinterior
            offset hnext) incidence = outside := by
  rcases exists_faceInterfaceIncidence_of_adj_outside web.annular.RS
      (pointwiseSelectedSourceLocalLayerSerialTerminalInputRegionAt web.toFormation corridor hinterior
        (sourceLocalLayerNextOffset offset hnext))
      (pointwiseSelectedSourceLocalLayerSerialCellRebaseUniformFaceDartAt web.toFormation corridor hinterior offset
        hnext) slot outside hadj houtside with
    ⟨direction, hvertex, _hpresent⟩
  exact ⟨(slot, direction), rfl, hvertex⟩

/-- Every supported uniform successor coordinate is marked present by the
exact facial code. -/
theorem pointwiseSelectedSourceLocalLayerSerialCellRebaseUniformFaceSuccessorLabelCapSixCodeAt_interfacePresent_of_mem_support
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : GoertzelV24ClosedWebAtGoodWord.Instance data coloring}
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      web.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (slot : Fin (pointwiseSelectedSourceLocalLayerSerialCellRebaseFaceInteractionCarrierAt
      web.toFormation corridor hinterior offset hnext).card)
    (hsupport : pointwiseSelectedSourceLocalLayerSerialCellRebaseUniformFaceDartAt web.toFormation corridor
      hinterior offset hnext slot ∈
        (pointwiseSelectedSourceLocalLayerBoundaryRebaseSuccessorFaceGraphAt web.toFormation corridor hinterior
          offset hnext).support) :
    (pointwiseSelectedSourceLocalLayerSerialCellRebaseUniformFaceSuccessorLabelCapSixCodeAt
      web.toFormation corridor hinterior offset hnext).interfacePresent slot = true := by
  rw [pointwiseSelectedSourceLocalLayerSerialCellRebaseUniformFaceSuccessorLabelCapSixCodeAt_exact
    web.toFormation corridor hinterior offset hnext]
  apply (exactFaceInterfaceExteriorLabelCapCode_interfacePresent_iff
    web.annular.RS
    (pointwiseSelectedSourceLocalLayerSerialTerminalInputRegionAt web.toFormation corridor hinterior
      (sourceLocalLayerNextOffset offset hnext))
    (pointwiseSelectedSourceLocalLayerSerialCellRebaseUniformFaceDartAt web.toFormation corridor hinterior offset
      hnext) slot 6).2
  rcases hsupport with ⟨other, hadj⟩
  exact (faceRegionalDartGraph_adj web.annular.RS
    (pointwiseSelectedSourceLocalLayerSerialTerminalInputRegionAt web.toFormation corridor hinterior
      (sourceLocalLayerNextOffset offset hnext)) _ _).1 hadj |>.2.2.1

/-- Literal target-coordinate activity in the successor regional face graph. -/
noncomputable def pointwiseSelectedSourceLocalLayerSerialCellRebaseUniformFaceTargetPresentAt
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : GoertzelV24ClosedWebAtGoodWord.Instance data coloring}
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      web.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3) :
    Fin (pointwiseSelectedSourceLocalLayerSerialFaceTransitionCarrierAt web.toFormation corridor hinterior
      (sourceLocalLayerNextOffset offset hnext)).card → Bool :=
  fun slot => decide (
    web.annular.RS.edgeOf
      (((carrierCoordinate
        (pointwiseSelectedSourceLocalLayerSerialFaceTransitionCarrierAt web.toFormation corridor hinterior
          (sourceLocalLayerNextOffset offset hnext))).symm slot).1) ∈
      pointwiseSelectedSourceLocalLayerSerialTerminalInputRegionAt web.toFormation corridor hinterior
        (sourceLocalLayerNextOffset offset hnext))

/-- Finite cap-six contraction from the uniform successor carrier to the next
rolling facial carrier. -/
noncomputable def pointwiseSelectedSourceLocalLayerSerialCellRebaseUniformFaceTargetLabelCapSixCodeAt
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (caps : OrientedFacialPentagonCapPair graphData)
    (coloring :
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.EdgeColoring Color)
    (web : GoertzelV24ClosedWebAtGoodWord.Instance
      caps.toFacialPentagonCapPair.toPentagonCapPair.boundaryData coloring)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      web.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3) :
    BoundedInterfaceExteriorLabelCapCode
      (Fin (pointwiseSelectedSourceLocalLayerSerialFaceTransitionCarrierAt web.toFormation corridor hinterior
        (sourceLocalLayerNextOffset offset hnext)).card)
      (Fin (pointwiseSelectedSourceLocalLayerSerialFaceTransitionCarrierAt web.toFormation corridor hinterior
        (sourceLocalLayerNextOffset offset hnext)).card × Bool) 6 :=
  partialContractedInterfaceExteriorLabelCapCode
    (pointwiseSelectedSourceLocalLayerSerialCellRebaseUniformFaceSuccessorLabelCapSixCodeAt
      web.toFormation corridor hinterior offset hnext)
    (pointwiseSelectedSourceLocalLayerSerialCellRebaseUniformFaceTargetSourceAt web.toFormation corridor hinterior
      offset hnext)
    Prod.fst
    (pointwiseSelectedSourceLocalLayerSerialCellRebaseUniformFaceTargetPresentAt corridor hinterior
      offset hnext)
    (pointwiseSelectedSourceLocalLayerSerialCellRebaseUniformFaceTargetEntryAt graphData minimal
      caps coloring web corridor hinterior offset hnext)

/-- Every decoded target incidence points to a physically live contraction
atom.  The left branch is a forgotten live uniform dart; the right branch is
an already-live uniform strict-exterior incidence. -/
theorem pointwiseSelectedSourceLocalLayerSerialCellRebaseUniformFaceTargetEntryAt_atomPresent
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (caps : OrientedFacialPentagonCapPair graphData)
    (coloring :
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.EdgeColoring Color)
    (web : GoertzelV24ClosedWebAtGoodWord.Instance
      caps.toFacialPentagonCapPair.toPentagonCapPair.boundaryData coloring)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      web.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (incidence : Fin
      (pointwiseSelectedSourceLocalLayerSerialFaceTransitionCarrierAt web.toFormation corridor hinterior
        (sourceLocalLayerNextOffset offset hnext)).card × Bool)
    (atom : SourceLocalLayerSerialCellRebaseUniformFaceTargetEntry
      (pointwiseSelectedSourceLocalLayerSerialCellRebaseFaceInteractionCarrierAt web.toFormation corridor
        hinterior offset hnext).card)
    (hentry :
      pointwiseSelectedSourceLocalLayerSerialCellRebaseUniformFaceTargetEntryAt graphData minimal
        caps coloring web corridor hinterior offset hnext incidence = some atom) :
    exteriorLabelCapContractionAtomPresent
        (pointwiseSelectedSourceLocalLayerSerialCellRebaseUniformFaceSuccessorLabelCapSixCodeAt
          web.toFormation corridor hinterior offset hnext)
        (pointwiseSelectedSourceLocalLayerSerialCellRebaseUniformFaceTargetSourceAt web.toFormation corridor
          hinterior offset hnext)
        atom = true := by
  classical
  let graph := pointwiseSelectedSourceLocalLayerBoundaryRebaseSuccessorFaceGraphAt web.toFormation corridor
    hinterior offset hnext
  let target := pointwiseSelectedSourceLocalLayerSerialFaceTransitionCarrierAt web.toFormation corridor hinterior
    (sourceLocalLayerNextOffset offset hnext)
  let uniform := pointwiseSelectedSourceLocalLayerSerialCellRebaseFaceInteractionCarrierAt
    web.toFormation corridor hinterior offset hnext
  let targetDartAt := fun slot : Fin target.card =>
    ((carrierCoordinate target).symm slot).1
  let uniformDartAt := pointwiseSelectedSourceLocalLayerSerialCellRebaseUniformFaceDartAt
    web.toFormation corridor hinterior offset hnext
  let retain := pointwiseSelectedSourceLocalLayerSerialCellRebaseUniformFaceTargetSourceAt
    web.toFormation corridor hinterior offset hnext
  have hpresentTarget : ExteriorIncidencePresent graph targetDartAt Prod.fst
      (faceInterfaceIncidenceVertex web.annular.RS targetDartAt) incidence :=
    (pointwiseSelectedSourceLocalLayerSerialCellRebaseUniformFaceTargetEntryAt_isSome_iff
      graphData minimal caps coloring web corridor hinterior offset hnext
        incidence).1 (by simp [hentry])
  cases atom with
  | inl uniformSlot =>
      unfold exteriorLabelCapContractionAtomPresent
      have hleft :=
        pointwiseSelectedSourceLocalLayerSerialCellRebaseUniformFaceTargetEntryAt_left graphData
          minimal caps coloring web corridor hinterior offset hnext incidence
            uniformSlot hentry
      rcases hleft with ⟨hvertex, hnotRetained⟩
      simp only [Bool.and_eq_true]
      constructor
      · rw [pointwiseSelectedSourceLocalLayerSerialCellRebaseUniformFaceSuccessorLabelCapSixCodeAt_exact
          web.toFormation corridor hinterior offset hnext]
        apply (exactFaceInterfaceExteriorLabelCapCode_interfacePresent_iff
          web.annular.RS
          (pointwiseSelectedSourceLocalLayerSerialTerminalInputRegionAt web.toFormation corridor hinterior
            (sourceLocalLayerNextOffset offset hnext))
          uniformDartAt uniformSlot 6).2
        have houtsideRegion : web.annular.RS.edgeOf
              (faceInterfaceIncidenceVertex web.annular.RS targetDartAt
                incidence) ∈
            pointwiseSelectedSourceLocalLayerSerialTerminalInputRegionAt web.toFormation corridor hinterior
              (sourceLocalLayerNextOffset offset hnext) :=
          hpresentTarget.2.2.2.2
        simpa [uniformDartAt, targetDartAt] using hvertex.symm ▸ houtsideRegion
      · apply (codeSurvivesPartialRetained_exact_iff graph uniformDartAt
          retain uniformSlot).2
        intro removedSlot hremoved heq
        rw [partialRetainedCoordinateMask_eq_true_iff] at hremoved
        rcases hremoved with ⟨targetSlot, hsource⟩
        have hslot : uniformSlot = removedSlot :=
          (pointwiseSelectedSourceLocalLayerSerialCellRebaseUniformFaceDartAt_injective
            web.toFormation corridor hinterior offset hnext) heq
        subst removedSlot
        exact hnotRetained targetSlot hsource
  | inr uniformIncidence =>
      unfold exteriorLabelCapContractionAtomPresent
      have hright :=
        pointwiseSelectedSourceLocalLayerSerialCellRebaseUniformFaceTargetEntryAt_right graphData
          minimal caps coloring web corridor hinterior offset hnext incidence
            uniformIncidence hentry
      rw [pointwiseSelectedSourceLocalLayerSerialCellRebaseUniformFaceSuccessorLabelCapSixCodeAt_exact
        web.toFormation corridor hinterior offset hnext]
      exact (exactFaceInterfaceExteriorLabelCapCode_incidencePresent_iff
        web.annular.RS
        (pointwiseSelectedSourceLocalLayerSerialTerminalInputRegionAt web.toFormation corridor hinterior
          (sourceLocalLayerNextOffset offset hnext))
        uniformDartAt uniformIncidence 6).2 hright.2

/-- A decoded atom denotes the literal exterior endpoint of its target
incidence. -/
theorem pointwiseSelectedSourceLocalLayerSerialCellRebaseUniformFaceTargetEntryAt_atomVertex
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (caps : OrientedFacialPentagonCapPair graphData)
    (coloring :
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.EdgeColoring Color)
    (web : GoertzelV24ClosedWebAtGoodWord.Instance
      caps.toFacialPentagonCapPair.toPentagonCapPair.boundaryData coloring)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      web.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (incidence : Fin
      (pointwiseSelectedSourceLocalLayerSerialFaceTransitionCarrierAt web.toFormation corridor hinterior
        (sourceLocalLayerNextOffset offset hnext)).card × Bool)
    (atom : SourceLocalLayerSerialCellRebaseUniformFaceTargetEntry
      (pointwiseSelectedSourceLocalLayerSerialCellRebaseFaceInteractionCarrierAt web.toFormation corridor
        hinterior offset hnext).card)
    (hentry :
      pointwiseSelectedSourceLocalLayerSerialCellRebaseUniformFaceTargetEntryAt graphData minimal
        caps coloring web corridor hinterior offset hnext incidence = some atom) :
    let target := pointwiseSelectedSourceLocalLayerSerialFaceTransitionCarrierAt web.toFormation corridor hinterior
      (sourceLocalLayerNextOffset offset hnext)
    let targetDartAt := fun slot : Fin target.card =>
      ((carrierCoordinate target).symm slot).1
    let uniformDartAt := pointwiseSelectedSourceLocalLayerSerialCellRebaseUniformFaceDartAt
      web.toFormation corridor hinterior offset hnext
    exteriorLabelCapContractionAtomVertex uniformDartAt
        (faceInterfaceIncidenceVertex web.annular.RS uniformDartAt) atom =
      faceInterfaceIncidenceVertex web.annular.RS targetDartAt incidence := by
  classical
  dsimp only
  cases atom with
  | inl uniformSlot =>
      exact
        (pointwiseSelectedSourceLocalLayerSerialCellRebaseUniformFaceTargetEntryAt_left graphData
          minimal caps coloring web corridor hinterior offset hnext incidence
            uniformSlot hentry).1
  | inr uniformIncidence =>
      exact
        (pointwiseSelectedSourceLocalLayerSerialCellRebaseUniformFaceTargetEntryAt_right graphData
          minimal caps coloring web corridor hinterior offset hnext incidence
            uniformIncidence hentry).1

/-- The finite decoder marks exactly the literal oriented incidences of the
rolling target exterior. -/
@[simp]
theorem pointwiseSelectedSourceLocalLayerSerialCellRebaseUniformFaceTargetLabelCapSixCodeAt_incidencePresent_iff
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (caps : OrientedFacialPentagonCapPair graphData)
    (coloring :
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.EdgeColoring Color)
    (web : GoertzelV24ClosedWebAtGoodWord.Instance
      caps.toFacialPentagonCapPair.toPentagonCapPair.boundaryData coloring)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      web.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (incidence : Fin
      (pointwiseSelectedSourceLocalLayerSerialFaceTransitionCarrierAt web.toFormation corridor hinterior
        (sourceLocalLayerNextOffset offset hnext)).card × Bool) :
    (pointwiseSelectedSourceLocalLayerSerialCellRebaseUniformFaceTargetLabelCapSixCodeAt
      graphData minimal caps coloring web corridor hinterior offset hnext
      ).incidencePresent incidence = true ↔
      let graph := pointwiseSelectedSourceLocalLayerBoundaryRebaseSuccessorFaceGraphAt web.toFormation corridor
        hinterior offset hnext
      let target := pointwiseSelectedSourceLocalLayerSerialFaceTransitionCarrierAt web.toFormation corridor
        hinterior (sourceLocalLayerNextOffset offset hnext)
      let targetDartAt := fun slot : Fin target.card =>
        ((carrierCoordinate target).symm slot).1
      ExteriorIncidencePresent graph targetDartAt Prod.fst
        (faceInterfaceIncidenceVertex web.annular.RS targetDartAt)
        incidence := by
  classical
  dsimp only
  let entry := pointwiseSelectedSourceLocalLayerSerialCellRebaseUniformFaceTargetEntryAt
    graphData minimal caps coloring web corridor hinterior offset hnext
  change
    exteriorLabelCapContractionEntryPresent
        (pointwiseSelectedSourceLocalLayerSerialCellRebaseUniformFaceSuccessorLabelCapSixCodeAt
          web.toFormation corridor hinterior offset hnext)
        (pointwiseSelectedSourceLocalLayerSerialCellRebaseUniformFaceTargetSourceAt web.toFormation corridor
          hinterior offset hnext)
        entry incidence = true ↔ _
  rw [exteriorLabelCapContractionEntryPresent_eq_true_iff]
  constructor
  · rintro ⟨atom, hentry, _⟩
    exact
      (pointwiseSelectedSourceLocalLayerSerialCellRebaseUniformFaceTargetEntryAt_isSome_iff
        graphData minimal caps coloring web corridor hinterior offset hnext
          incidence).1 (by simp [entry, hentry])
  · intro hpresent
    have hsome :=
      (pointwiseSelectedSourceLocalLayerSerialCellRebaseUniformFaceTargetEntryAt_isSome_iff
        graphData minimal caps coloring web corridor hinterior offset hnext
          incidence).2 hpresent
    cases hentry : entry incidence with
    | none => simp [entry, hentry] at hsome
    | some atom =>
        exact ⟨atom, rfl,
          pointwiseSelectedSourceLocalLayerSerialCellRebaseUniformFaceTargetEntryAt_atomPresent
            graphData minimal caps coloring web corridor hinterior offset hnext
              incidence atom (by simpa [entry] using hentry)⟩

/-- The contracted incidence relation cannot invent an exterior-component
identification: every reported pair is connected in the literal rolling
successor exterior. -/
theorem pointwiseSelectedSourceLocalLayerSerialCellRebaseUniformFaceTargetLabelCapSixCodeAt_incidenceConnected_sound
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (caps : OrientedFacialPentagonCapPair graphData)
    (coloring :
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.EdgeColoring Color)
    (web : GoertzelV24ClosedWebAtGoodWord.Instance
      caps.toFacialPentagonCapPair.toPentagonCapPair.boundaryData coloring)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      web.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (first second : Fin
      (pointwiseSelectedSourceLocalLayerSerialFaceTransitionCarrierAt web.toFormation corridor hinterior
        (sourceLocalLayerNextOffset offset hnext)).card × Bool)
    (hconnected :
      (pointwiseSelectedSourceLocalLayerSerialCellRebaseUniformFaceTargetLabelCapSixCodeAt
        graphData minimal caps coloring web corridor hinterior offset hnext
        ).incidenceConnected first second = true) :
    let graph := pointwiseSelectedSourceLocalLayerBoundaryRebaseSuccessorFaceGraphAt web.toFormation corridor
      hinterior offset hnext
    let target := pointwiseSelectedSourceLocalLayerSerialFaceTransitionCarrierAt web.toFormation corridor hinterior
      (sourceLocalLayerNextOffset offset hnext)
    let targetDartAt := fun slot : Fin target.card =>
      ((carrierCoordinate target).symm slot).1
    ExteriorIncidencePresent graph targetDartAt Prod.fst
        (faceInterfaceIncidenceVertex web.annular.RS targetDartAt) first ∧
      ExteriorIncidencePresent graph targetDartAt Prod.fst
        (faceInterfaceIncidenceVertex web.annular.RS targetDartAt) second ∧
      (exteriorGraph graph targetDartAt).Reachable
        (faceInterfaceIncidenceVertex web.annular.RS targetDartAt first)
        (faceInterfaceIncidenceVertex web.annular.RS targetDartAt second) := by
  classical
  dsimp only
  let graph := pointwiseSelectedSourceLocalLayerBoundaryRebaseSuccessorFaceGraphAt web.toFormation corridor
    hinterior offset hnext
  let target := pointwiseSelectedSourceLocalLayerSerialFaceTransitionCarrierAt web.toFormation corridor hinterior
    (sourceLocalLayerNextOffset offset hnext)
  let uniform := pointwiseSelectedSourceLocalLayerSerialCellRebaseFaceInteractionCarrierAt
    web.toFormation corridor hinterior offset hnext
  let targetDartAt := fun slot : Fin target.card =>
    ((carrierCoordinate target).symm slot).1
  let uniformDartAt := pointwiseSelectedSourceLocalLayerSerialCellRebaseUniformFaceDartAt
    web.toFormation corridor hinterior offset hnext
  let retain := pointwiseSelectedSourceLocalLayerSerialCellRebaseUniformFaceTargetSourceAt
    web.toFormation corridor hinterior offset hnext
  let entry := pointwiseSelectedSourceLocalLayerSerialCellRebaseUniformFaceTargetEntryAt
    graphData minimal caps coloring web corridor hinterior offset hnext
  let code :=
    pointwiseSelectedSourceLocalLayerSerialCellRebaseUniformFaceSuccessorLabelCapSixCodeAt
      web.toFormation corridor hinterior offset hnext
  change (partialContractedInterfaceExteriorLabelCapCode code retain Prod.fst
    (pointwiseSelectedSourceLocalLayerSerialCellRebaseUniformFaceTargetPresentAt corridor hinterior
      offset hnext) entry).incidenceConnected first second = true at hconnected
  have hdata :=
    (partialContractedInterfaceExteriorLabelCapCode_incidenceConnected_iff
      code retain Prod.fst
      (pointwiseSelectedSourceLocalLayerSerialCellRebaseUniformFaceTargetPresentAt corridor
        hinterior offset hnext) entry first second).1 hconnected
  rcases hdata with
    ⟨firstAtom, secondAtom, hfirstEntry, hsecondEntry, _, _, hreach⟩
  have hfirstPresent : ExteriorIncidencePresent graph targetDartAt Prod.fst
      (faceInterfaceIncidenceVertex web.annular.RS targetDartAt) first :=
    (pointwiseSelectedSourceLocalLayerSerialCellRebaseUniformFaceTargetEntryAt_isSome_iff
      graphData minimal caps coloring web corridor hinterior offset hnext first).1
        (by simp [entry, hfirstEntry])
  have hsecondPresent : ExteriorIncidencePresent graph targetDartAt Prod.fst
      (faceInterfaceIncidenceVertex web.annular.RS targetDartAt) second :=
    (pointwiseSelectedSourceLocalLayerSerialCellRebaseUniformFaceTargetEntryAt_isSome_iff
      graphData minimal caps coloring web corridor hinterior offset hnext second).1
        (by simp [entry, hsecondEntry])
  have hsome : ∀ retained slot, retain retained = some slot →
      uniformDartAt slot = targetDartAt retained := by
    intro retained slot hretain
    exact pointwiseSelectedSourceLocalLayerSerialCellRebaseUniformFaceTargetSourceAt_dart_eq
      web.toFormation corridor hinterior offset hnext retained slot hretain
  have hnone : ∀ retained, retain retained = none →
      targetDartAt retained ∉ graph.support := by
    intro retained hretain
    exact
      pointwiseSelectedSourceLocalLayerSerialCellRebaseUniformFaceTargetSourceAt_none_not_mem_support
        graphData minimal caps coloring web corridor hinterior offset hnext
          retained hretain
  have hreachLiteral : (exteriorGraph graph targetDartAt).Reachable
      (exteriorLabelCapContractionAtomVertex uniformDartAt
        (faceInterfaceIncidenceVertex web.annular.RS uniformDartAt) firstAtom)
      (exteriorLabelCapContractionAtomVertex uniformDartAt
      (faceInterfaceIncidenceVertex web.annular.RS uniformDartAt)
          secondAtom) := by
    have hcodeExact : code = exactInterfaceExteriorLabelCapCode graph
        uniformDartAt
        (fun dart => web.annular.RS.edgeOf dart ∈
          pointwiseSelectedSourceLocalLayerSerialTerminalInputRegionAt web.toFormation corridor hinterior
            (sourceLocalLayerNextOffset offset hnext))
        Prod.fst (faceInterfaceIncidenceVertex web.annular.RS uniformDartAt)
        web.annular.RS.edgeOf 6 := by
      exact
        pointwiseSelectedSourceLocalLayerSerialCellRebaseUniformFaceSuccessorLabelCapSixCodeAt_exact
          web.toFormation corridor hinterior offset hnext
    have hconnectivity : code.connectivity =
        exactInterfaceExteriorCode graph uniformDartAt := by
      rw [hcodeExact]
      rfl
    have hincidencePresent : ∀ incidence,
        code.incidencePresent incidence = true ↔
          ExteriorIncidencePresent graph uniformDartAt Prod.fst
            (faceInterfaceIncidenceVertex web.annular.RS uniformDartAt)
            incidence := by
      intro incidence
      rw [hcodeExact]
      exact exactInterfaceExteriorLabelCapCode_incidencePresent_iff graph
        uniformDartAt
        (fun dart => web.annular.RS.edgeOf dart ∈
          pointwiseSelectedSourceLocalLayerSerialTerminalInputRegionAt web.toFormation corridor hinterior
            (sourceLocalLayerNextOffset offset hnext))
        Prod.fst (faceInterfaceIncidenceVertex web.annular.RS uniformDartAt)
          web.annular.RS.edgeOf incidence 6
    have hincidenceConnected : ∀ first second,
        code.incidenceConnected first second = true ↔
          ExteriorIncidencePresent graph uniformDartAt Prod.fst
              (faceInterfaceIncidenceVertex web.annular.RS uniformDartAt)
              first ∧
            ExteriorIncidencePresent graph uniformDartAt Prod.fst
              (faceInterfaceIncidenceVertex web.annular.RS uniformDartAt)
              second ∧
            (exteriorGraph graph uniformDartAt).Reachable
              (faceInterfaceIncidenceVertex web.annular.RS uniformDartAt first)
              (faceInterfaceIncidenceVertex web.annular.RS uniformDartAt
                second) := by
      intro first second
      rw [hcodeExact]
      exact exactInterfaceExteriorLabelCapCode_incidenceConnected_iff graph
        uniformDartAt
        (fun dart => web.annular.RS.edgeOf dart ∈
          pointwiseSelectedSourceLocalLayerSerialTerminalInputRegionAt web.toFormation corridor hinterior
            (sourceLocalLayerNextOffset offset hnext))
        Prod.fst (faceInterfaceIncidenceVertex web.annular.RS uniformDartAt)
          web.annular.RS.edgeOf first second 6
    exact exteriorLabelCapContractionAtomReachable_sound_of_exact
      (N := web.annular.RS.D)
      (Larger := Fin uniform.card) (Retained := Fin target.card)
      (Incidence := Fin uniform.card × Bool) (cap := 6) graph
      uniformDartAt targetDartAt retain hsome hnone Prod.fst
      (faceInterfaceIncidenceVertex web.annular.RS uniformDartAt) code
      hconnectivity hincidencePresent hincidenceConnected firstAtom secondAtom
        hreach
  have hfirstVertex :=
    pointwiseSelectedSourceLocalLayerSerialCellRebaseUniformFaceTargetEntryAt_atomVertex
      graphData minimal caps coloring web corridor hinterior offset hnext first
        firstAtom (by simpa [entry] using hfirstEntry)
  have hsecondVertex :=
    pointwiseSelectedSourceLocalLayerSerialCellRebaseUniformFaceTargetEntryAt_atomVertex
      graphData minimal caps coloring web corridor hinterior offset hnext second
        secondAtom (by simpa [entry] using hsecondEntry)
  exact ⟨hfirstPresent, hsecondPresent, by
    simpa [uniformDartAt, targetDartAt] using
      hfirstVertex ▸ hsecondVertex ▸ hreachLiteral⟩

/-- Every literal rolling-successor exterior connection is found by the finite
contracted incidence relation. -/
theorem pointwiseSelectedSourceLocalLayerSerialCellRebaseUniformFaceTargetLabelCapSixCodeAt_incidenceConnected_complete
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (caps : OrientedFacialPentagonCapPair graphData)
    (coloring :
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.EdgeColoring Color)
    (web : GoertzelV24ClosedWebAtGoodWord.Instance
      caps.toFacialPentagonCapPair.toPentagonCapPair.boundaryData coloring)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      web.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (first second : Fin
      (pointwiseSelectedSourceLocalLayerSerialFaceTransitionCarrierAt web.toFormation corridor hinterior
        (sourceLocalLayerNextOffset offset hnext)).card × Bool)
    (hfirst :
      let graph := pointwiseSelectedSourceLocalLayerBoundaryRebaseSuccessorFaceGraphAt web.toFormation corridor
        hinterior offset hnext
      let target := pointwiseSelectedSourceLocalLayerSerialFaceTransitionCarrierAt web.toFormation corridor
        hinterior (sourceLocalLayerNextOffset offset hnext)
      let targetDartAt := fun slot : Fin target.card =>
        ((carrierCoordinate target).symm slot).1
      ExteriorIncidencePresent graph targetDartAt Prod.fst
        (faceInterfaceIncidenceVertex web.annular.RS targetDartAt) first)
    (hsecond :
      let graph := pointwiseSelectedSourceLocalLayerBoundaryRebaseSuccessorFaceGraphAt web.toFormation corridor
        hinterior offset hnext
      let target := pointwiseSelectedSourceLocalLayerSerialFaceTransitionCarrierAt web.toFormation corridor
        hinterior (sourceLocalLayerNextOffset offset hnext)
      let targetDartAt := fun slot : Fin target.card =>
        ((carrierCoordinate target).symm slot).1
      ExteriorIncidencePresent graph targetDartAt Prod.fst
        (faceInterfaceIncidenceVertex web.annular.RS targetDartAt) second)
    (hreachable :
      let graph := pointwiseSelectedSourceLocalLayerBoundaryRebaseSuccessorFaceGraphAt web.toFormation corridor
        hinterior offset hnext
      let target := pointwiseSelectedSourceLocalLayerSerialFaceTransitionCarrierAt web.toFormation corridor
        hinterior (sourceLocalLayerNextOffset offset hnext)
      let targetDartAt := fun slot : Fin target.card =>
        ((carrierCoordinate target).symm slot).1
      (exteriorGraph graph targetDartAt).Reachable
        (faceInterfaceIncidenceVertex web.annular.RS targetDartAt first)
        (faceInterfaceIncidenceVertex web.annular.RS targetDartAt second)) :
    (pointwiseSelectedSourceLocalLayerSerialCellRebaseUniformFaceTargetLabelCapSixCodeAt
      graphData minimal caps coloring web corridor hinterior offset hnext
      ).incidenceConnected first second = true := by
  classical
  dsimp only at hfirst hsecond hreachable
  let graph := pointwiseSelectedSourceLocalLayerBoundaryRebaseSuccessorFaceGraphAt web.toFormation corridor
    hinterior offset hnext
  let target := pointwiseSelectedSourceLocalLayerSerialFaceTransitionCarrierAt web.toFormation corridor hinterior
    (sourceLocalLayerNextOffset offset hnext)
  let uniform := pointwiseSelectedSourceLocalLayerSerialCellRebaseFaceInteractionCarrierAt
    web.toFormation corridor hinterior offset hnext
  let targetDartAt := fun slot : Fin target.card =>
    ((carrierCoordinate target).symm slot).1
  let uniformDartAt := pointwiseSelectedSourceLocalLayerSerialCellRebaseUniformFaceDartAt
    web.toFormation corridor hinterior offset hnext
  let retain := pointwiseSelectedSourceLocalLayerSerialCellRebaseUniformFaceTargetSourceAt
    web.toFormation corridor hinterior offset hnext
  let entry := pointwiseSelectedSourceLocalLayerSerialCellRebaseUniformFaceTargetEntryAt
    graphData minimal caps coloring web corridor hinterior offset hnext
  let code :=
    pointwiseSelectedSourceLocalLayerSerialCellRebaseUniformFaceSuccessorLabelCapSixCodeAt
      web.toFormation corridor hinterior offset hnext
  have hfirstSome :=
    (pointwiseSelectedSourceLocalLayerSerialCellRebaseUniformFaceTargetEntryAt_isSome_iff
      graphData minimal caps coloring web corridor hinterior offset hnext first).2
        hfirst
  have hsecondSome :=
    (pointwiseSelectedSourceLocalLayerSerialCellRebaseUniformFaceTargetEntryAt_isSome_iff
      graphData minimal caps coloring web corridor hinterior offset hnext second).2
        hsecond
  cases hfirstEntry : entry first with
  | none => simp [entry, hfirstEntry] at hfirstSome
  | some firstAtom =>
      cases hsecondEntry : entry second with
      | none => simp [entry, hsecondEntry] at hsecondSome
      | some secondAtom =>
          have hfirstAtomPresent :=
            pointwiseSelectedSourceLocalLayerSerialCellRebaseUniformFaceTargetEntryAt_atomPresent
              graphData minimal caps coloring web corridor hinterior offset hnext
                first firstAtom (by simpa [entry] using hfirstEntry)
          have hsecondAtomPresent :=
            pointwiseSelectedSourceLocalLayerSerialCellRebaseUniformFaceTargetEntryAt_atomPresent
              graphData minimal caps coloring web corridor hinterior offset hnext
                second secondAtom (by simpa [entry] using hsecondEntry)
          have hfirstAtomPresentCode :
              exteriorLabelCapContractionAtomPresent code retain firstAtom =
                true := by
            simpa [code, retain] using hfirstAtomPresent
          have hsecondAtomPresentCode :
              exteriorLabelCapContractionAtomPresent code retain secondAtom =
                true := by
            simpa [code, retain] using hsecondAtomPresent
          have hfirstVertex :=
            pointwiseSelectedSourceLocalLayerSerialCellRebaseUniformFaceTargetEntryAt_atomVertex
              graphData minimal caps coloring web corridor hinterior offset hnext
                first firstAtom (by simpa [entry] using hfirstEntry)
          have hsecondVertex :=
            pointwiseSelectedSourceLocalLayerSerialCellRebaseUniformFaceTargetEntryAt_atomVertex
              graphData minimal caps coloring web corridor hinterior offset hnext
                second secondAtom (by simpa [entry] using hsecondEntry)
          have hsome : ∀ retained slot, retain retained = some slot →
              uniformDartAt slot = targetDartAt retained := by
            intro retained slot hretain
            exact
              pointwiseSelectedSourceLocalLayerSerialCellRebaseUniformFaceTargetSourceAt_dart_eq
                web.toFormation corridor hinterior offset hnext retained slot hretain
          have hcodeExact : code = exactInterfaceExteriorLabelCapCode graph
              uniformDartAt
              (fun dart => web.annular.RS.edgeOf dart ∈
                pointwiseSelectedSourceLocalLayerSerialTerminalInputRegionAt web.toFormation corridor hinterior
                  (sourceLocalLayerNextOffset offset hnext))
              Prod.fst
              (faceInterfaceIncidenceVertex web.annular.RS uniformDartAt)
              web.annular.RS.edgeOf 6 := by
            exact
              pointwiseSelectedSourceLocalLayerSerialCellRebaseUniformFaceSuccessorLabelCapSixCodeAt_exact
                web.toFormation corridor hinterior offset hnext
          have hconnectivity : code.connectivity =
              exactInterfaceExteriorCode graph uniformDartAt := by
            rw [hcodeExact]
            rfl
          have hinterfacePresent : ∀ slot,
              uniformDartAt slot ∈ graph.support →
                code.interfacePresent slot = true := by
            intro slot hsupport
            exact
              pointwiseSelectedSourceLocalLayerSerialCellRebaseUniformFaceSuccessorLabelCapSixCodeAt_interfacePresent_of_mem_support
                corridor hinterior offset hnext slot hsupport
          have hincidencePresent : ∀ incidence,
              code.incidencePresent incidence = true ↔
                ExteriorIncidencePresent graph uniformDartAt Prod.fst
                  (faceInterfaceIncidenceVertex web.annular.RS uniformDartAt)
                  incidence := by
            intro incidence
            rw [hcodeExact]
            exact exactInterfaceExteriorLabelCapCode_incidencePresent_iff graph
              uniformDartAt
              (fun dart => web.annular.RS.edgeOf dart ∈
                pointwiseSelectedSourceLocalLayerSerialTerminalInputRegionAt web.toFormation corridor hinterior
                  (sourceLocalLayerNextOffset offset hnext))
              Prod.fst
              (faceInterfaceIncidenceVertex web.annular.RS uniformDartAt)
              web.annular.RS.edgeOf incidence 6
          have hincidenceConnected : ∀ first second,
              code.incidenceConnected first second = true ↔
                ExteriorIncidencePresent graph uniformDartAt Prod.fst
                    (faceInterfaceIncidenceVertex web.annular.RS uniformDartAt)
                    first ∧
                  ExteriorIncidencePresent graph uniformDartAt Prod.fst
                    (faceInterfaceIncidenceVertex web.annular.RS uniformDartAt)
                    second ∧
                  (exteriorGraph graph uniformDartAt).Reachable
                    (faceInterfaceIncidenceVertex web.annular.RS uniformDartAt
                      first)
                    (faceInterfaceIncidenceVertex web.annular.RS uniformDartAt
                      second) := by
            intro first second
            rw [hcodeExact]
            exact exactInterfaceExteriorLabelCapCode_incidenceConnected_iff
              graph uniformDartAt
              (fun dart => web.annular.RS.edgeOf dart ∈
                pointwiseSelectedSourceLocalLayerSerialTerminalInputRegionAt web.toFormation corridor hinterior
                  (sourceLocalLayerNextOffset offset hnext))
              Prod.fst
              (faceInterfaceIncidenceVertex web.annular.RS uniformDartAt)
              web.annular.RS.edgeOf first second 6
          have hincidenceComplete : ∀ slot outside,
              OutsideInterface uniformDartAt outside →
                graph.Adj (uniformDartAt slot) outside →
                ∃ incidence : Fin uniform.card × Bool,
                  incidence.1 = slot ∧
                    faceInterfaceIncidenceVertex web.annular.RS uniformDartAt
                      incidence = outside := by
            intro slot outside houtside hadj
            exact
              pointwiseSelectedSourceLocalLayerSerialCellRebaseUniformFaceSuccessor_incidenceComplete
                corridor hinterior offset hnext slot outside houtside hadj
          have hreachAtoms : (exteriorGraph graph targetDartAt).Reachable
              (exteriorLabelCapContractionAtomVertex uniformDartAt
                (faceInterfaceIncidenceVertex web.annular.RS uniformDartAt)
                firstAtom)
              (exteriorLabelCapContractionAtomVertex uniformDartAt
                (faceInterfaceIncidenceVertex web.annular.RS uniformDartAt)
                secondAtom) := by
            simpa [uniformDartAt, targetDartAt] using
              hfirstVertex ▸ hsecondVertex ▸ hreachable
          have hreachAtomsFinite :=
            exteriorLabelCapContractionAtomReachable_complete_of_exact
              (N := web.annular.RS.D) (Larger := Fin uniform.card)
              (Retained := Fin target.card)
              (Incidence := Fin uniform.card × Bool) (cap := 6) graph
              uniformDartAt targetDartAt retain hsome Prod.fst
              (faceInterfaceIncidenceVertex web.annular.RS uniformDartAt) code
              hconnectivity hinterfacePresent hincidencePresent
              hincidenceConnected hincidenceComplete firstAtom secondAtom
              hfirstAtomPresentCode hsecondAtomPresentCode hreachAtoms
          change (partialContractedInterfaceExteriorLabelCapCode code retain
            Prod.fst
            (pointwiseSelectedSourceLocalLayerSerialCellRebaseUniformFaceTargetPresentAt corridor
              hinterior offset hnext) entry).incidenceConnected first second = true
          exact
            (partialContractedInterfaceExteriorLabelCapCode_incidenceConnected_iff
              code retain Prod.fst
              (pointwiseSelectedSourceLocalLayerSerialCellRebaseUniformFaceTargetPresentAt
                corridor hinterior offset hnext) entry first second).2
              ⟨firstAtom, secondAtom, hfirstEntry, hsecondEntry,
                hfirstAtomPresentCode, hsecondAtomPresentCode,
                hreachAtomsFinite⟩

/-- The contracted relation is exactly the literal rolling-successor exterior
component relation. -/
@[simp]
theorem pointwiseSelectedSourceLocalLayerSerialCellRebaseUniformFaceTargetLabelCapSixCodeAt_incidenceConnected_iff
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (caps : OrientedFacialPentagonCapPair graphData)
    (coloring :
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.EdgeColoring Color)
    (web : GoertzelV24ClosedWebAtGoodWord.Instance
      caps.toFacialPentagonCapPair.toPentagonCapPair.boundaryData coloring)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      web.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (first second : Fin
      (pointwiseSelectedSourceLocalLayerSerialFaceTransitionCarrierAt web.toFormation corridor hinterior
        (sourceLocalLayerNextOffset offset hnext)).card × Bool) :
    (pointwiseSelectedSourceLocalLayerSerialCellRebaseUniformFaceTargetLabelCapSixCodeAt
      graphData minimal caps coloring web corridor hinterior offset hnext
      ).incidenceConnected first second = true ↔
      let graph := pointwiseSelectedSourceLocalLayerBoundaryRebaseSuccessorFaceGraphAt web.toFormation corridor
        hinterior offset hnext
      let target := pointwiseSelectedSourceLocalLayerSerialFaceTransitionCarrierAt web.toFormation corridor
        hinterior (sourceLocalLayerNextOffset offset hnext)
      let targetDartAt := fun slot : Fin target.card =>
        ((carrierCoordinate target).symm slot).1
      ExteriorIncidencePresent graph targetDartAt Prod.fst
          (faceInterfaceIncidenceVertex web.annular.RS targetDartAt) first ∧
        ExteriorIncidencePresent graph targetDartAt Prod.fst
          (faceInterfaceIncidenceVertex web.annular.RS targetDartAt) second ∧
        (exteriorGraph graph targetDartAt).Reachable
          (faceInterfaceIncidenceVertex web.annular.RS targetDartAt first)
          (faceInterfaceIncidenceVertex web.annular.RS targetDartAt second) := by
  constructor
  · exact
      pointwiseSelectedSourceLocalLayerSerialCellRebaseUniformFaceTargetLabelCapSixCodeAt_incidenceConnected_sound
        graphData minimal caps coloring web corridor hinterior offset hnext first
          second
  · rintro ⟨hfirst, hsecond, hreachable⟩
    exact
      pointwiseSelectedSourceLocalLayerSerialCellRebaseUniformFaceTargetLabelCapSixCodeAt_incidenceConnected_complete
        graphData minimal caps coloring web corridor hinterior offset hnext first
          second hfirst hsecond hreachable

/-- Target-coordinate activity is the literal successor-region predicate. -/
@[simp]
theorem pointwiseSelectedSourceLocalLayerSerialCellRebaseUniformFaceTargetLabelCapSixCodeAt_interfacePresent_iff
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (caps : OrientedFacialPentagonCapPair graphData)
    (coloring :
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.EdgeColoring Color)
    (web : GoertzelV24ClosedWebAtGoodWord.Instance
      caps.toFacialPentagonCapPair.toPentagonCapPair.boundaryData coloring)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      web.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (slot : Fin
      (pointwiseSelectedSourceLocalLayerSerialFaceTransitionCarrierAt web.toFormation corridor hinterior
        (sourceLocalLayerNextOffset offset hnext)).card) :
    (pointwiseSelectedSourceLocalLayerSerialCellRebaseUniformFaceTargetLabelCapSixCodeAt
      graphData minimal caps coloring web corridor hinterior offset hnext
      ).interfacePresent slot = true ↔
      web.annular.RS.edgeOf
          (((carrierCoordinate
            (pointwiseSelectedSourceLocalLayerSerialFaceTransitionCarrierAt web.toFormation corridor hinterior
              (sourceLocalLayerNextOffset offset hnext))).symm slot).1) ∈
        pointwiseSelectedSourceLocalLayerSerialTerminalInputRegionAt web.toFormation corridor hinterior
          (sourceLocalLayerNextOffset offset hnext) := by
  simp [pointwiseSelectedSourceLocalLayerSerialCellRebaseUniformFaceTargetLabelCapSixCodeAt,
    partialContractedInterfaceExteriorLabelCapCode,
    pointwiseSelectedSourceLocalLayerSerialCellRebaseUniformFaceTargetPresentAt]

/-- Forgetting labels does not alter the already-verified rolling successor
connectivity row. -/
@[simp]
theorem pointwiseSelectedSourceLocalLayerSerialCellRebaseUniformFaceTargetLabelCapSixCodeAt_connectivity
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (caps : OrientedFacialPentagonCapPair graphData)
    (coloring :
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.EdgeColoring Color)
    (web : GoertzelV24ClosedWebAtGoodWord.Instance
      caps.toFacialPentagonCapPair.toPentagonCapPair.boundaryData coloring)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      web.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3) :
    (pointwiseSelectedSourceLocalLayerSerialCellRebaseUniformFaceTargetLabelCapSixCodeAt
      graphData minimal caps coloring web corridor hinterior offset hnext
      ).connectivity =
      pointwiseSelectedSourceLocalLayerSerialCellRebaseUniformFaceTargetRawCodeAt web.toFormation corridor
        hinterior offset hnext := by
  unfold pointwiseSelectedSourceLocalLayerSerialCellRebaseUniformFaceTargetLabelCapSixCodeAt
  rfl

end

end GoertzelV24ClosedWebPointwiseSelectedFaceTargetCap

end Mettapedia.GraphTheory.FourColor
