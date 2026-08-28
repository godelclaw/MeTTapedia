import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebPointwiseSelectedFaceRollingSuccessor
import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebPointwiseSelectedFaceTargetCapExact

/-!
# Exact rolling facial interaction state

The finite facial rebase is exact on the current forty-eight-dart interaction
carrier, and rolling locality supplies finite addresses for every active
incidence of the following carrier.  This file proves that contracting through
those addresses gives all five fields of the canonical following facial state:
connectivity, activity, oriented incidence activity, exterior-component
connectivity, and capped face progress.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebPointwiseSelectedFaceRollingExact

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
open GoertzelV24ClosedWebPointwiseSelectedFaceTargetCap
open GoertzelV24ClosedWebPointwiseSelectedFaceTargetCapExact
open GoertzelV24ClosedWebPointwiseSelectedFacePreRebaseExact
open GoertzelV24ClosedWebLocalLayerSerialRootedInteractionFacePreRebaseState
open GoertzelV24ClosedWebLocalLayerSerialRootedInteractionFaceRollingSuccessor
open GoertzelV24ClosedWebPointwiseSelectedFaceRollingSuccessor
open GoertzelV24ClosedWebPointwiseSelectedFaceSuccessor
open GoertzelV24ClosedWebPointwiseSelectedRootedInteractionState
open GoertzelV24ClosedWebLocalLayerSerialRootedInteractionRollingSuccessor
open GoertzelV24ClosedWebLocalLayerSerialRootedInteractionState
open GoertzelV24CorridorProfile
open GoertzelV24FaceOrbitIncidence
open GoertzelV24FacialPentagonCap
open GoertzelV24InterfaceDeletionComponentFactor
open GoertzelV24InterfaceDeletionComponentFactorForget
open GoertzelV24InterfaceDeletionComponentFactorForgetExterior
open GoertzelV24InterfaceExteriorLabelCapFactor
open GoertzelV24InterfaceExteriorLabelCapFactorForget
open GoertzelV24InterfaceExteriorLabelCapFactorForgetExact
open GoertzelV24InterfaceExteriorLabelCapFactorForgetWeightExact
open GoertzelV24InterfaceExteriorSupportedPortProjection
open GoertzelV24MinimalFacialPentagonCapPairPointwiseSelectedLocalCellCarrier
open GoertzelV24RotationFaceInterfaceExteriorLabelCap
open GoertzelV24RotationFaceRegionalDartCarrier
open GoertzelV24RotationFaceRegionalDartGraph
open GoertzelV24TwoEdgeCutMinimality
open GoertzelV24TwoPentagonCapOpening
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance faceRollingExactIncidenceLinearOrder {n : Nat} :
    LinearOrder (Fin n × Bool) :=
  LinearOrder.lift' (fun incidence : Fin n × Bool => toLex incidence)
    toLex.injective

local instance faceRollingExactOpenedGraphDecidableRel
    (caps : OrientedFacialPentagonCapPair (G := G) graphData) :
    DecidableRel
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.Adj :=
  Classical.decRel _

/-- The selected one-step facial collar stays on annular-interior faces.  A
changed dart lies over one of the four selected rebase edges; its two facial
neighbors remain in the same face orbit. -/
theorem pointwiseSelectedSourceLocalLayerBoundaryRebaseFaceCollarAt_face_internal
    {data : AnnularBoundaryData G 5} (formation : Formation data)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      formation.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (dart : formation.annular.RS.D)
    (hdart : dart ∈
      pointwiseSelectedSourceLocalLayerBoundaryRebaseFaceCollarAt formation
        corridor hinterior offset hnext) :
    dartOrbitFace formation.annular.RS dart ∈
      formation.annular.cellulation.interiorFaces := by
  rw [pointwiseSelectedSourceLocalLayerBoundaryRebaseFaceCollarAt,
    Finset.mem_biUnion] at hdart
  rcases hdart with ⟨changed, hchanged, hdart⟩
  have hchangedInternal : dartOrbitFace formation.annular.RS changed ∈
      formation.annular.cellulation.interiorFaces := by
    apply pointwiseSelectedSourceLocalLayerBoundaryRebaseSwitchAt_incidentFace_internal
      formation corridor hinterior offset hnext
        (formation.annular.RS.edgeOf changed)
        (dartOrbitFace formation.annular.RS changed)
    · exact (mem_dartsOnEdges_iff formation.annular.RS _ changed).1 hchanged
    · exact GoertzelV24FaceDualConnectedness.edgeOf_mem_orbitFaceBoundary_dartOrbitFace
        formation.annular.RS changed
  simp only [Finset.mem_insert, Finset.mem_singleton] at hdart
  rcases hdart with rfl | rfl | rfl
  · exact hchangedInternal
  · rw [dartOrbitFace_phi_eq]
    exact hchangedInternal
  · have hsame := dartOrbitFace_phi_eq formation.annular.RS
      (formation.annular.RS.phi.symm changed)
    have hsame' : dartOrbitFace formation.annular.RS changed =
        dartOrbitFace formation.annular.RS
          (formation.annular.RS.phi.symm changed) := by
      simpa using hsame
    rw [← hsame']
    exact hchangedInternal

/-- Every active dart of the following complete interaction carrier lies on an
annular-interior face.  The transition half uses the exact target theorem; the
collar half is interior by the one-step collar theorem. -/
theorem pointwiseSelectedSourceLocalLayerSerialCellRebaseNextFaceInteractionDartAt_face_internal
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
    (hnextNext :
      (sourceLocalLayerNextOffset offset hnext).val + 1 < blockLength - 3)
    (slot : Fin
      (pointwiseSelectedSourceLocalLayerSerialCellRebaseFaceInteractionCarrierAt web.toFormation corridor hinterior
        (sourceLocalLayerNextOffset offset hnext) hnextNext).card)
    (hactive : web.annular.RS.edgeOf
        (((carrierCoordinate
          (pointwiseSelectedSourceLocalLayerSerialCellRebaseFaceInteractionCarrierAt web.toFormation corridor
            hinterior (sourceLocalLayerNextOffset offset hnext) hnextNext)
          ).symm slot).1) ∈
      pointwiseSelectedSourceLocalLayerSerialTerminalInputRegionAt web.toFormation corridor hinterior
        (sourceLocalLayerNextOffset offset hnext)) :
    dartOrbitFace web.annular.RS
        (((carrierCoordinate
          (pointwiseSelectedSourceLocalLayerSerialCellRebaseFaceInteractionCarrierAt web.toFormation corridor
            hinterior (sourceLocalLayerNextOffset offset hnext) hnextNext)
          ).symm slot).1) ∈
      web.annular.cellulation.interiorFaces := by
  let next := sourceLocalLayerNextOffset offset hnext
  let target := pointwiseSelectedSourceLocalLayerSerialFaceTransitionCarrierAt web.toFormation corridor hinterior
    next
  let interaction :=
    pointwiseSelectedSourceLocalLayerSerialCellRebaseFaceInteractionCarrierAt web.toFormation corridor hinterior
      next hnextNext
  let dart : web.annular.RS.D := ((carrierCoordinate interaction).symm slot).1
  have hdart : dart ∈ interaction :=
    ((carrierCoordinate interaction).symm slot).2
  rcases Finset.mem_union.mp hdart with htarget | hcollar
  · let targetSlot : Fin target.card := carrierCoordinate target ⟨dart, htarget⟩
    have htargetDart :
        ((carrierCoordinate target).symm targetSlot).1 = dart := by
      simp [targetSlot]
    have hinternal :=
      pointwiseSelectedSourceLocalLayerSerialCellRebaseUniformFaceTargetDartAt_face_internal
        graphData minimal caps coloring web corridor hinterior offset hnext
          targetSlot (by simpa [next, target, interaction, dart, htargetDart]
            using hactive)
    simpa [next, target, interaction, dart, htargetDart] using hinternal
  · exact pointwiseSelectedSourceLocalLayerBoundaryRebaseFaceCollarAt_face_internal web.toFormation corridor
      hinterior next hnextNext dart hcollar

/-- Edge labels are injective on the literal target-exterior component named by
a live rolling atom.  Its root lies on an active interior face, exterior
reachability stays on that face, and the certified face boundary is simple. -/
theorem pointwiseSelectedSourceLocalLayerSerialFaceRollingEntryAt_label_injective
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
    (hnextNext :
      (sourceLocalLayerNextOffset offset hnext).val + 1 < blockLength - 3)
    (incidence : Fin
      (pointwiseSelectedSourceLocalLayerSerialCellRebaseFaceInteractionCarrierAt web.toFormation corridor hinterior
        (sourceLocalLayerNextOffset offset hnext) hnextNext).card × Bool)
    (atom : ExteriorLabelCapContractionAtom
      (Fin (pointwiseSelectedSourceLocalLayerSerialCellRebaseFaceInteractionCarrierAt web.toFormation corridor
        hinterior offset hnext).card)
      (Fin (pointwiseSelectedSourceLocalLayerSerialCellRebaseFaceInteractionCarrierAt web.toFormation corridor
        hinterior offset hnext).card × Bool))
    (hentry : pointwiseSelectedSourceLocalLayerSerialFaceRollingEntryAt graphData minimal caps
      coloring web corridor hinterior offset hnext hnextNext incidence =
        some atom) :
    let graph := pointwiseSelectedSourceLocalLayerBoundaryRebaseSuccessorFaceGraphAt web.toFormation corridor
      hinterior offset hnext
    let target := pointwiseSelectedSourceLocalLayerSerialCellRebaseFaceInteractionCarrierAt
      web.toFormation corridor hinterior (sourceLocalLayerNextOffset offset hnext) hnextNext
    let targetDartAt := fun slot : Fin target.card =>
      ((carrierCoordinate target).symm slot).1
    let currentDartAt := pointwiseSelectedSourceLocalLayerSerialCellRebaseUniformFaceDartAt
      web.toFormation corridor hinterior offset hnext
    Set.InjOn web.annular.RS.edgeOf
      {vertex |
        (exteriorGraph graph targetDartAt).Reachable
          (exteriorLabelCapContractionAtomVertex currentDartAt
            (faceInterfaceIncidenceVertex web.annular.RS currentDartAt) atom)
          vertex} := by
  classical
  dsimp only
  let graph := pointwiseSelectedSourceLocalLayerBoundaryRebaseSuccessorFaceGraphAt web.toFormation corridor
    hinterior offset hnext
  let region := pointwiseSelectedSourceLocalLayerSerialTerminalInputRegionAt web.toFormation corridor hinterior
    (sourceLocalLayerNextOffset offset hnext)
  let target := pointwiseSelectedSourceLocalLayerSerialCellRebaseFaceInteractionCarrierAt
    web.toFormation corridor hinterior (sourceLocalLayerNextOffset offset hnext) hnextNext
  let targetDartAt := fun slot : Fin target.card =>
    ((carrierCoordinate target).symm slot).1
  let currentDartAt := pointwiseSelectedSourceLocalLayerSerialCellRebaseUniformFaceDartAt
    web.toFormation corridor hinterior offset hnext
  let atomVertex := exteriorLabelCapContractionAtomVertex currentDartAt
    (faceInterfaceIncidenceVertex web.annular.RS currentDartAt) atom
  have hpresent : ExteriorIncidencePresent graph targetDartAt Prod.fst
      (faceInterfaceIncidenceVertex web.annular.RS targetDartAt) incidence :=
    (pointwiseSelectedSourceLocalLayerSerialFaceRollingEntryAt_isSome_iff graphData minimal caps
      coloring web corridor hinterior offset hnext hnextNext incidence).1
      (by simp [hentry])
  have htargetInternal : dartOrbitFace web.annular.RS
        (targetDartAt incidence.1) ∈
      web.annular.cellulation.interiorFaces := by
    apply pointwiseSelectedSourceLocalLayerSerialCellRebaseNextFaceInteractionDartAt_face_internal
      graphData minimal caps coloring web corridor hinterior offset hnext
        hnextNext incidence.1
    exact hpresent.2.2.2.1
  have htargetRootFace : dartOrbitFace web.annular.RS
        (targetDartAt incidence.1) =
      dartOrbitFace web.annular.RS
        (faceInterfaceIncidenceVertex web.annular.RS targetDartAt incidence) :=
    faceRegionalDartGraph_adj_dartOrbitFace_eq web.annular.RS region hpresent.2
  have hatomVertex : atomVertex =
      faceInterfaceIncidenceVertex web.annular.RS targetDartAt incidence := by
    exact pointwiseSelectedSourceLocalLayerSerialFaceRollingEntryAt_atomVertex graphData minimal
      caps coloring web corridor hinterior offset hnext hnextNext incidence atom
        hentry
  have hatomInternal : dartOrbitFace web.annular.RS atomVertex ∈
      web.annular.cellulation.interiorFaces := by
    rw [hatomVertex, ← htargetRootFace]
    exact htargetInternal
  have hexteriorLe : exteriorGraph graph targetDartAt ≤ graph := by
    intro first second hadj
    exact hadj.1
  intro left hleft right hright hedge
  have hleftFace : dartOrbitFace web.annular.RS atomVertex =
      dartOrbitFace web.annular.RS left :=
    faceRegionalDartGraph_reachable_dartOrbitFace_eq web.annular.RS region
      (hleft.mono hexteriorLe)
  have hrightFace : dartOrbitFace web.annular.RS atomVertex =
      dartOrbitFace web.annular.RS right :=
    faceRegionalDartGraph_reachable_dartOrbitFace_eq web.annular.RS region
      (hright.mono hexteriorLe)
  have hinjective : Set.InjOn web.annular.RS.edgeOf
      (orbitFaceDarts web.annular.RS
        (dartOrbitFace web.annular.RS atomVertex)) := by
    apply Finset.card_image_iff.mp
    exact InteriorFace.boundary_card_eq_darts_card web atomVertex hatomInternal
  exact hinjective
    ((mem_orbitFaceDarts_iff web.annular.RS
      (dartOrbitFace web.annular.RS atomVertex) left).2 hleftFace.symm)
    ((mem_orbitFaceDarts_iff web.annular.RS
      (dartOrbitFace web.annular.RS atomVertex) right).2 hrightFace.symm)
    hedge

/-- The rolling contraction computes exactly the five-field facial code on the
following complete interaction carrier. -/
theorem pointwiseSelectedSourceLocalLayerSerialFaceRollingNextInteractionStateAt_code_eq
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
    (hnextNext :
      (sourceLocalLayerNextOffset offset hnext).val + 1 < blockLength - 3) :
    let hcell :=
      pointwiseSelectedSourceLocalLayerCellRegionAt_card_le_six graphData
        minimal caps coloring web corridor hinterior offset
    let preRebase :=
      pointwiseSelectedSourceLocalLayerSerialFaceInteractionPreRebaseStateAt
        web.toFormation corridor hinterior offset hnext hcell
    let factor := pointwiseSelectedSourceLocalLayerSerialFaceRollingFactorAt graphData minimal
      caps coloring web corridor hinterior offset hnext hnextNext
    let nextInteraction :=
      pointwiseSelectedSourceLocalLayerSerialCellRebaseFaceInteractionCarrierAt web.toFormation corridor hinterior
        (sourceLocalLayerNextOffset offset hnext) hnextNext
    let nextDartAt := fun slot : Fin nextInteraction.card =>
      ((carrierCoordinate nextInteraction).symm slot).1
    (factor.nextInteractionState preRebase (by rfl)).code () =
      exactFaceInterfaceExteriorLabelCapCode web.annular.RS
        (pointwiseSelectedSourceLocalLayerSerialTerminalInputRegionAt web.toFormation corridor hinterior
          (sourceLocalLayerNextOffset offset hnext))
        nextDartAt 6 := by
  classical
  dsimp only
  unfold SourceLocalLayerSerialFaceRollingFactor.nextInteractionState
  dsimp only
  unfold pointwiseSelectedSourceLocalLayerSerialFaceRollingFactorAt
  dsimp only
  rw [pointwiseSelectedSourceLocalLayerSerialFaceRebaseUniformSuccessorAt_eq graphData minimal
    caps coloring web corridor hinterior offset hnext
      (pointwiseSelectedSourceLocalLayerCellRegionAt_card_le_six graphData
        minimal caps coloring web corridor hinterior offset)]
  let graph := pointwiseSelectedSourceLocalLayerBoundaryRebaseSuccessorFaceGraphAt web.toFormation corridor
    hinterior offset hnext
  let current := pointwiseSelectedSourceLocalLayerSerialCellRebaseFaceInteractionCarrierAt
    web.toFormation corridor hinterior offset hnext
  let target := pointwiseSelectedSourceLocalLayerSerialCellRebaseFaceInteractionCarrierAt
    web.toFormation corridor hinterior (sourceLocalLayerNextOffset offset hnext) hnextNext
  let currentDartAt := pointwiseSelectedSourceLocalLayerSerialCellRebaseUniformFaceDartAt
    web.toFormation corridor hinterior offset hnext
  let targetDartAt := fun slot : Fin target.card =>
    ((carrierCoordinate target).symm slot).1
  let retain := finiteCarrierPartialSource current target
  let entry := pointwiseSelectedSourceLocalLayerSerialFaceRollingEntryAt graphData minimal caps
    coloring web corridor hinterior offset hnext hnextNext
  let code :=
    pointwiseSelectedSourceLocalLayerSerialCellRebaseUniformFaceSuccessorLabelCapSixCodeAt
      web.toFormation corridor hinterior offset hnext
  have hcodeExact : code = exactInterfaceExteriorLabelCapCode graph
      currentDartAt
      (fun dart => web.annular.RS.edgeOf dart ∈
        pointwiseSelectedSourceLocalLayerSerialTerminalInputRegionAt web.toFormation corridor hinterior
          (sourceLocalLayerNextOffset offset hnext))
      Prod.fst (faceInterfaceIncidenceVertex web.annular.RS currentDartAt)
      web.annular.RS.edgeOf 6 := by
    exact
      pointwiseSelectedSourceLocalLayerSerialCellRebaseUniformFaceSuccessorLabelCapSixCodeAt_exact
        web.toFormation corridor hinterior offset hnext
  have hconnectivity : code.connectivity =
      exactInterfaceExteriorCode graph currentDartAt := by
    rw [hcodeExact]
    rfl
  have hinterfacePresent : ∀ slot,
      currentDartAt slot ∈ graph.support →
        code.interfacePresent slot = true := by
    intro slot hsupport
    exact
      pointwiseSelectedSourceLocalLayerSerialCellRebaseUniformFaceSuccessorLabelCapSixCodeAt_interfacePresent_of_mem_support
        corridor hinterior offset hnext slot hsupport
  have hincidencePresent : ∀ incidence,
      code.incidencePresent incidence = true ↔
        ExteriorIncidencePresent graph currentDartAt Prod.fst
          (faceInterfaceIncidenceVertex web.annular.RS currentDartAt)
          incidence := by
    intro incidence
    rw [hcodeExact]
    exact exactInterfaceExteriorLabelCapCode_incidencePresent_iff graph
      currentDartAt
      (fun dart => web.annular.RS.edgeOf dart ∈
        pointwiseSelectedSourceLocalLayerSerialTerminalInputRegionAt web.toFormation corridor hinterior
          (sourceLocalLayerNextOffset offset hnext))
      Prod.fst (faceInterfaceIncidenceVertex web.annular.RS currentDartAt)
      web.annular.RS.edgeOf incidence 6
  have hincidenceConnected : ∀ first second,
      code.incidenceConnected first second = true ↔
        ExteriorIncidencePresent graph currentDartAt Prod.fst
            (faceInterfaceIncidenceVertex web.annular.RS currentDartAt) first ∧
          ExteriorIncidencePresent graph currentDartAt Prod.fst
            (faceInterfaceIncidenceVertex web.annular.RS currentDartAt) second ∧
          (exteriorGraph graph currentDartAt).Reachable
            (faceInterfaceIncidenceVertex web.annular.RS currentDartAt first)
            (faceInterfaceIncidenceVertex web.annular.RS currentDartAt
              second) := by
    intro first second
    rw [hcodeExact]
    exact exactInterfaceExteriorLabelCapCode_incidenceConnected_iff graph
      currentDartAt
      (fun dart => web.annular.RS.edgeOf dart ∈
        pointwiseSelectedSourceLocalLayerSerialTerminalInputRegionAt web.toFormation corridor hinterior
          (sourceLocalLayerNextOffset offset hnext))
      Prod.fst (faceInterfaceIncidenceVertex web.annular.RS currentDartAt)
      web.annular.RS.edgeOf first second 6
  have hincidenceComplete : ∀ slot outside,
      OutsideInterface currentDartAt outside →
        graph.Adj (currentDartAt slot) outside →
          ∃ incidence : Fin current.card × Bool,
            incidence.1 = slot ∧
              faceInterfaceIncidenceVertex web.annular.RS currentDartAt
                incidence = outside := by
    intro slot outside houtside hadj
    exact
      pointwiseSelectedSourceLocalLayerSerialCellRebaseUniformFaceSuccessor_incidenceComplete
        corridor hinterior offset hnext slot outside houtside hadj
  have hincidenceCap : ∀ incidence,
      (code.incidenceCap incidence).val =
        min (exteriorIncidenceLabelSupport graph currentDartAt Prod.fst
          (faceInterfaceIncidenceVertex web.annular.RS currentDartAt)
          web.annular.RS.edgeOf incidence).card 6 := by
    intro incidence
    rw [hcodeExact]
    exact exactInterfaceExteriorLabelCapCode_incidenceCap_val graph
      currentDartAt
      (fun dart => web.annular.RS.edgeOf dart ∈
        pointwiseSelectedSourceLocalLayerSerialTerminalInputRegionAt web.toFormation corridor hinterior
          (sourceLocalLayerNextOffset offset hnext))
      Prod.fst (faceInterfaceIncidenceVertex web.annular.RS currentDartAt)
      web.annular.RS.edgeOf incidence 6
  have hsome : ∀ retained slot, retain retained = some slot →
      currentDartAt slot = targetDartAt retained := by
    intro retained slot hretain
    exact
      pointwiseSelectedSourceLocalLayerSerialFaceRollingFactorAt_nextInteractionSource_dart_eq
        graphData minimal caps coloring web corridor hinterior offset hnext
          hnextNext retained slot hretain
  have hnone : ∀ retained, retain retained = none →
      targetDartAt retained ∉ graph.support := by
    intro retained hretain
    exact
      pointwiseSelectedSourceLocalLayerSerialFaceRollingFactorAt_nextInteractionSource_none_not_mem_support
        graphData minimal caps coloring web corridor hinterior offset hnext
          hnextNext retained hretain
  have hcurrentInjective : Function.Injective currentDartAt :=
    pointwiseSelectedSourceLocalLayerSerialCellRebaseUniformFaceDartAt_injective web.toFormation corridor hinterior
      offset hnext
  have htargetInjective : Function.Injective targetDartAt := by
    intro left right heq
    apply (carrierCoordinate target).symm.injective
    exact Subtype.ext heq
  change partialContractedInterfaceExteriorLabelCapCode code retain Prod.fst
      (fun slot => decide (web.annular.RS.edgeOf (targetDartAt slot) ∈
        pointwiseSelectedSourceLocalLayerSerialTerminalInputRegionAt web.toFormation corridor hinterior
          (sourceLocalLayerNextOffset offset hnext))) entry =
    exactInterfaceExteriorLabelCapCode graph targetDartAt
      (fun dart => web.annular.RS.edgeOf dart ∈
        pointwiseSelectedSourceLocalLayerSerialTerminalInputRegionAt web.toFormation corridor hinterior
          (sourceLocalLayerNextOffset offset hnext))
      Prod.fst (faceInterfaceIncidenceVertex web.annular.RS targetDartAt)
      web.annular.RS.edgeOf 6
  apply BoundedInterfaceExteriorLabelCapCode.ext
  · change partialContractedInterfaceExteriorCode code.connectivity retain =
      exactInterfaceExteriorCode graph targetDartAt
    rw [hconnectivity]
    apply boundedInterfaceExteriorCode_ext_iff
    · intro left right
      change partialReindexedVertexEq left right = true ↔
        (exactInterfaceExteriorCode graph targetDartAt).vertexEq left right = true
      rw [partialReindexedVertexEq_eq_true_iff targetDartAt htargetInjective]
      simp [exactInterfaceExteriorCode]
    · intro left right
      change partialReindexedDirectAdj
          (exactInterfaceExteriorCode graph currentDartAt) retain left right =
            true ↔
        (exactInterfaceExteriorCode graph targetDartAt).directAdj left right =
          true
      rw [partialReindexedDirectAdj_exact_iff graph currentDartAt targetDartAt
        retain hsome hnone left right]
      simp [exactInterfaceExteriorCode]
    · intro left right
      change partialReindexedExteriorConnected
          (exactInterfaceExteriorCode graph currentDartAt) retain left right =
            true ↔
        (exactInterfaceExteriorCode graph targetDartAt).exteriorConnected left
          right = true
      rw [partialReindexedExteriorConnected_exact_eq_true_iff graph
        currentDartAt targetDartAt retain hsome hnone left right]
      simp [exactInterfaceExteriorCode]
  · rfl
  · funext incidence
    apply Bool.eq_iff_iff.mpr
    rw [partialContractedInterfaceExteriorLabelCapCode_incidencePresent_iff]
    rw [exactInterfaceExteriorLabelCapCode_incidencePresent_iff graph
      targetDartAt
      (fun dart => web.annular.RS.edgeOf dart ∈
        pointwiseSelectedSourceLocalLayerSerialTerminalInputRegionAt web.toFormation corridor hinterior
          (sourceLocalLayerNextOffset offset hnext))
      Prod.fst (faceInterfaceIncidenceVertex web.annular.RS targetDartAt)
      web.annular.RS.edgeOf incidence 6]
    constructor
    · rintro ⟨atom, hentry, _hatomPresent⟩
      exact
        (pointwiseSelectedSourceLocalLayerSerialFaceRollingEntryAt_isSome_iff graphData minimal
          caps coloring web corridor hinterior offset hnext hnextNext
            incidence).1 (by simp [entry, hentry])
    · intro hpresent
      have hsomeEntry :=
        (pointwiseSelectedSourceLocalLayerSerialFaceRollingEntryAt_isSome_iff graphData minimal
          caps coloring web corridor hinterior offset hnext hnextNext
            incidence).2 hpresent
      rcases Option.isSome_iff_exists.mp hsomeEntry with ⟨atom, hentry⟩
      refine ⟨atom, by simpa [entry] using hentry, ?_⟩
      exact pointwiseSelectedSourceLocalLayerSerialFaceRollingEntryAt_atomPresent graphData
        minimal caps coloring web corridor hinterior offset hnext hnextNext
          incidence atom (by simpa [entry] using hentry)
  · funext first second
    apply Bool.eq_iff_iff.mpr
    rw [partialContractedInterfaceExteriorLabelCapCode_incidenceConnected_iff]
    rw [exactInterfaceExteriorLabelCapCode_incidenceConnected_iff graph
      targetDartAt
      (fun dart => web.annular.RS.edgeOf dart ∈
        pointwiseSelectedSourceLocalLayerSerialTerminalInputRegionAt web.toFormation corridor hinterior
          (sourceLocalLayerNextOffset offset hnext))
      Prod.fst (faceInterfaceIncidenceVertex web.annular.RS targetDartAt)
      web.annular.RS.edgeOf first second 6]
    constructor
    · rintro ⟨firstAtom, secondAtom, hfirstEntry, hsecondEntry,
        hfirstAtomPresent, hsecondAtomPresent, hreach⟩
      have hfirstPresent : ExteriorIncidencePresent graph targetDartAt Prod.fst
          (faceInterfaceIncidenceVertex web.annular.RS targetDartAt) first :=
        (pointwiseSelectedSourceLocalLayerSerialFaceRollingEntryAt_isSome_iff graphData minimal
          caps coloring web corridor hinterior offset hnext hnextNext first).1
          (by simp [entry, hfirstEntry])
      have hsecondPresent : ExteriorIncidencePresent graph targetDartAt Prod.fst
          (faceInterfaceIncidenceVertex web.annular.RS targetDartAt) second :=
        (pointwiseSelectedSourceLocalLayerSerialFaceRollingEntryAt_isSome_iff graphData minimal
          caps coloring web corridor hinterior offset hnext hnextNext second).1
          (by simp [entry, hsecondEntry])
      have hreachLiteral :=
        (exteriorLabelCapContractionAtomReachable_iff_of_exact graph
          currentDartAt targetDartAt retain hsome hnone Prod.fst
          (faceInterfaceIncidenceVertex web.annular.RS currentDartAt) code
          hconnectivity hinterfacePresent hincidencePresent hincidenceConnected
          hincidenceComplete firstAtom secondAtom hfirstAtomPresent
          hsecondAtomPresent).1 hreach
      have hfirstVertex :=
        pointwiseSelectedSourceLocalLayerSerialFaceRollingEntryAt_atomVertex graphData minimal
          caps coloring web corridor hinterior offset hnext hnextNext first
            firstAtom (by simpa [entry] using hfirstEntry)
      have hsecondVertex :=
        pointwiseSelectedSourceLocalLayerSerialFaceRollingEntryAt_atomVertex graphData minimal
          caps coloring web corridor hinterior offset hnext hnextNext second
            secondAtom (by simpa [entry] using hsecondEntry)
      exact ⟨hfirstPresent, hsecondPresent, by
        simpa [currentDartAt, targetDartAt] using
          hfirstVertex ▸ hsecondVertex ▸ hreachLiteral⟩
    · rintro ⟨hfirstPresent, hsecondPresent, hreachLiteral⟩
      have hfirstSome :=
        (pointwiseSelectedSourceLocalLayerSerialFaceRollingEntryAt_isSome_iff graphData minimal
          caps coloring web corridor hinterior offset hnext hnextNext first).2
          hfirstPresent
      have hsecondSome :=
        (pointwiseSelectedSourceLocalLayerSerialFaceRollingEntryAt_isSome_iff graphData minimal
          caps coloring web corridor hinterior offset hnext hnextNext second).2
          hsecondPresent
      rcases Option.isSome_iff_exists.mp hfirstSome with
        ⟨firstAtom, hfirstEntry⟩
      rcases Option.isSome_iff_exists.mp hsecondSome with
        ⟨secondAtom, hsecondEntry⟩
      have hfirstAtomPresent :=
        pointwiseSelectedSourceLocalLayerSerialFaceRollingEntryAt_atomPresent graphData minimal
          caps coloring web corridor hinterior offset hnext hnextNext first
            firstAtom (by simpa [entry] using hfirstEntry)
      have hsecondAtomPresent :=
        pointwiseSelectedSourceLocalLayerSerialFaceRollingEntryAt_atomPresent graphData minimal
          caps coloring web corridor hinterior offset hnext hnextNext second
            secondAtom (by simpa [entry] using hsecondEntry)
      have hfirstVertex :=
        pointwiseSelectedSourceLocalLayerSerialFaceRollingEntryAt_atomVertex graphData minimal
          caps coloring web corridor hinterior offset hnext hnextNext first
            firstAtom (by simpa [entry] using hfirstEntry)
      have hsecondVertex :=
        pointwiseSelectedSourceLocalLayerSerialFaceRollingEntryAt_atomVertex graphData minimal
          caps coloring web corridor hinterior offset hnext hnextNext second
            secondAtom (by simpa [entry] using hsecondEntry)
      have hreachAtoms : (exteriorGraph graph targetDartAt).Reachable
          (exteriorLabelCapContractionAtomVertex currentDartAt
            (faceInterfaceIncidenceVertex web.annular.RS currentDartAt)
            firstAtom)
          (exteriorLabelCapContractionAtomVertex currentDartAt
            (faceInterfaceIncidenceVertex web.annular.RS currentDartAt)
            secondAtom) := by
        simpa [currentDartAt, targetDartAt] using
          hfirstVertex.symm ▸ hsecondVertex.symm ▸ hreachLiteral
      have hreach :=
        (exteriorLabelCapContractionAtomReachable_iff_of_exact graph
          currentDartAt targetDartAt retain hsome hnone Prod.fst
          (faceInterfaceIncidenceVertex web.annular.RS currentDartAt) code
          hconnectivity hinterfacePresent hincidencePresent hincidenceConnected
          hincidenceComplete firstAtom secondAtom hfirstAtomPresent
          hsecondAtomPresent).2 hreachAtoms
      exact ⟨firstAtom, secondAtom, by simpa [entry] using hfirstEntry,
        by simpa [entry] using hsecondEntry, hfirstAtomPresent,
        hsecondAtomPresent, hreach⟩
  · funext incidence
    apply Fin.ext
    rw [exactInterfaceExteriorLabelCapCode_incidenceCap_val graph targetDartAt
      (fun dart => web.annular.RS.edgeOf dart ∈
        pointwiseSelectedSourceLocalLayerSerialTerminalInputRegionAt web.toFormation corridor hinterior
          (sourceLocalLayerNextOffset offset hnext))
      Prod.fst (faceInterfaceIncidenceVertex web.annular.RS targetDartAt)
      web.annular.RS.edgeOf incidence 6]
    cases hentry : entry incidence with
    | none =>
        have hnotPresent : ¬ ExteriorIncidencePresent graph targetDartAt
            Prod.fst (faceInterfaceIncidenceVertex web.annular.RS targetDartAt)
            incidence := by
          intro hpresent
          have hsomeEntry :=
            (pointwiseSelectedSourceLocalLayerSerialFaceRollingEntryAt_isSome_iff graphData
              minimal caps coloring web corridor hinterior offset hnext hnextNext
                incidence).2 hpresent
          simp [entry, hentry] at hsomeEntry
        rw [partialContractedInterfaceExteriorLabelCapCode_incidenceCap_val]
        simp [hentry, exteriorIncidenceLabelSupport, hnotPresent]
    | some atom =>
        have hatomPresent :=
          pointwiseSelectedSourceLocalLayerSerialFaceRollingEntryAt_atomPresent graphData minimal
            caps coloring web corridor hinterior offset hnext hnextNext incidence
              atom (by simpa [entry] using hentry)
        have hlabelInjective : Set.InjOn web.annular.RS.edgeOf
            {vertex |
              (exteriorGraph graph targetDartAt).Reachable
                (exteriorLabelCapContractionAtomVertex currentDartAt
                  (faceInterfaceIncidenceVertex web.annular.RS currentDartAt)
                  atom)
                vertex} := by
          exact pointwiseSelectedSourceLocalLayerSerialFaceRollingEntryAt_label_injective
            graphData minimal caps coloring web corridor hinterior offset hnext
              hnextNext incidence atom (by simpa [entry] using hentry)
        have hcomponent :=
          exteriorLabelCapContractionComponentCap_val_eq_literalLabelSupport
            graph currentDartAt targetDartAt retain hsome hnone Prod.fst
            (faceInterfaceIncidenceVertex web.annular.RS currentDartAt)
            web.annular.RS.edgeOf code hconnectivity hinterfacePresent
            hincidencePresent hincidenceConnected hincidenceComplete
            hincidenceCap atom hatomPresent hcurrentInjective hlabelInjective
        have hpresent : ExteriorIncidencePresent graph targetDartAt Prod.fst
            (faceInterfaceIncidenceVertex web.annular.RS targetDartAt)
            incidence :=
          (pointwiseSelectedSourceLocalLayerSerialFaceRollingEntryAt_isSome_iff graphData
            minimal caps coloring web corridor hinterior offset hnext hnextNext
              incidence).1 (by simp [entry, hentry])
        have hatomVertex :=
          pointwiseSelectedSourceLocalLayerSerialFaceRollingEntryAt_atomVertex graphData minimal
            caps coloring web corridor hinterior offset hnext hnextNext incidence
              atom (by simpa [entry] using hentry)
        have hatomVertex' :
            exteriorLabelCapContractionAtomVertex currentDartAt
                (faceInterfaceIncidenceVertex web.annular.RS currentDartAt)
                atom =
              faceInterfaceIncidenceVertex web.annular.RS targetDartAt
                incidence := by
          simpa [currentDartAt, targetDartAt] using hatomVertex
        have hsupport :
            exteriorLabelCapContractionLiteralLabelSupport graph targetDartAt
                currentDartAt
                (faceInterfaceIncidenceVertex web.annular.RS currentDartAt)
                web.annular.RS.edgeOf atom =
              exteriorIncidenceLabelSupport graph targetDartAt Prod.fst
                (faceInterfaceIncidenceVertex web.annular.RS targetDartAt)
                web.annular.RS.edgeOf incidence := by
          ext value
          simp [exteriorLabelCapContractionLiteralLabelSupport,
            exteriorIncidenceLabelSupport, hpresent, hatomVertex']
        rw [partialContractedInterfaceExteriorLabelCapCode_incidenceCap_val]
        simp only [hentry]
        rw [if_pos hatomPresent]
        exact hcomponent.trans (by rw [hsupport])

/-- The finite rolling facial contraction is the complete following
interaction-exterior field of the canonical rooted state. -/
theorem pointwiseSelectedSourceLocalLayerSerialFaceRollingNextInteractionStateAt_eq
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
    (hnextNext :
      (sourceLocalLayerNextOffset offset hnext).val + 1 < blockLength - 3)
    (color :
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.edgeSet → Color)
    (hcrossing : ∀ step,
      color (pointwiseSelectedSourceLocalLayerLeftCrossingAt web.toFormation
        corridor hinterior (sourceLocalLayerNextOffset offset hnext) step) ≠ 0) :
    let hcell :=
      pointwiseSelectedSourceLocalLayerCellRegionAt_card_le_six graphData
        minimal caps coloring web corridor hinterior offset
    let hcellNext :=
      pointwiseSelectedSourceLocalLayerCellRegionAt_card_le_six graphData
        minimal caps coloring web corridor hinterior
          (sourceLocalLayerNextOffset offset hnext)
    let preRebase :=
      pointwiseSelectedSourceLocalLayerSerialFaceInteractionPreRebaseStateAt
        web.toFormation corridor hinterior offset hnext hcell
    let factor := pointwiseSelectedSourceLocalLayerSerialFaceRollingFactorAt graphData minimal
      caps coloring web corridor hinterior offset hnext hnextNext
    factor.nextInteractionState preRebase (by rfl) =
      (pointwiseSelectedSourceLocalLayerSerialRootedInteractionStateForColorAt
        web corridor hinterior (sourceLocalLayerNextOffset offset hnext)
          hnextNext hcellNext color hcrossing
        ).faceInteractionExterior := by
  dsimp only
  rw [BoundedInterfaceExteriorLabelCapFamilyCode.mk.injEq]
  refine ⟨rfl, ?_⟩
  apply heq_of_eq
  funext family
  rw [pointwiseSelectedSourceLocalLayerSerialFaceRollingNextInteractionStateAt_code_eq
    graphData minimal caps coloring web corridor hinterior offset hnext hnextNext]
  rfl

end

end GoertzelV24ClosedWebPointwiseSelectedFaceRollingExact

end Mettapedia.GraphTheory.FourColor
