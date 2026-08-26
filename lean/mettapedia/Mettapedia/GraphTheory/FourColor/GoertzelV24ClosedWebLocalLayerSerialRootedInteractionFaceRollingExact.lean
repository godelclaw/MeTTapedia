import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalLayerSerialRootedInteractionFaceRollingSuccessor
import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalLayerSerialCellUniformFaceTargetCapExact

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

namespace GoertzelV24ClosedWebLocalLayerSerialRootedInteractionFaceRollingExact

open GoertzelV24BoundedCarrierGraphFamilyCode
open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAnnularEmbedding.ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAtGoodWord
open GoertzelV24ClosedWebAtGoodWord.Instance
open GoertzelV24ClosedWebAtGoodWord.Instance.LocalLayerFormation
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24ClosedWebLocalLayerSerialCellUniformFaceRecurrence
open GoertzelV24ClosedWebLocalLayerSerialCellUniformFaceTargetCap
open GoertzelV24ClosedWebLocalLayerSerialCellUniformFaceTargetCapExact
open GoertzelV24ClosedWebLocalLayerSerialRootedInteractionFacePreRebaseExact
open GoertzelV24ClosedWebLocalLayerSerialRootedInteractionFacePreRebaseState
open GoertzelV24ClosedWebLocalLayerSerialRootedInteractionFaceRollingSuccessor
open GoertzelV24ClosedWebLocalLayerSerialRootedInteractionFaceSuccessor
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
open GoertzelV24RotationFaceInterfaceExteriorLabelCap
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

/-- Every active dart of the following complete interaction carrier lies on an
annular-interior face.  The transition half uses the exact target theorem; the
collar half is interior by the one-step collar theorem. -/
theorem sourceLocalLayerSerialCellRebaseNextFaceInteractionDartAt_face_internal
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
    (hnextNext :
      (sourceLocalLayerNextOffset offset hnext).val + 1 < blockLength - 3)
    (slot : Fin
      (sourceLocalLayerSerialCellRebaseFaceInteractionCarrierAt corridor hunique
        (sourceLocalLayerNextOffset offset hnext) hnextNext).card)
    (hactive : web.annular.RS.edgeOf
        (((carrierCoordinate
          (sourceLocalLayerSerialCellRebaseFaceInteractionCarrierAt corridor
            hunique (sourceLocalLayerNextOffset offset hnext) hnextNext)
          ).symm slot).1) ∈
      sourceLocalLayerSerialTerminalInputRegionAt corridor hunique
        (sourceLocalLayerNextOffset offset hnext)) :
    dartOrbitFace web.annular.RS
        (((carrierCoordinate
          (sourceLocalLayerSerialCellRebaseFaceInteractionCarrierAt corridor
            hunique (sourceLocalLayerNextOffset offset hnext) hnextNext)
          ).symm slot).1) ∈
      web.annular.cellulation.interiorFaces := by
  let next := sourceLocalLayerNextOffset offset hnext
  let target := sourceLocalLayerSerialFaceTransitionCarrierAt corridor hunique
    next
  let interaction :=
    sourceLocalLayerSerialCellRebaseFaceInteractionCarrierAt corridor hunique
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
      sourceLocalLayerSerialCellRebaseUniformFaceTargetDartAt_face_internal
        graphData minimal caps coloring web corridor hunique offset hnext
          targetSlot (by simpa [next, target, interaction, dart, htargetDart]
            using hactive)
    simpa [next, target, interaction, dart, htargetDart] using hinternal
  · exact sourceLocalLayerBoundaryRebaseFaceCollarAt_face_internal corridor
      hunique next hnextNext dart hcollar

/-- Edge labels are injective on the literal target-exterior component named by
a live rolling atom.  Its root lies on an active interior face, exterior
reachability stays on that face, and the certified face boundary is simple. -/
theorem sourceLocalLayerSerialFaceRollingEntryAt_label_injective
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
    (hnextNext :
      (sourceLocalLayerNextOffset offset hnext).val + 1 < blockLength - 3)
    (incidence : Fin
      (sourceLocalLayerSerialCellRebaseFaceInteractionCarrierAt corridor hunique
        (sourceLocalLayerNextOffset offset hnext) hnextNext).card × Bool)
    (atom : ExteriorLabelCapContractionAtom
      (Fin (sourceLocalLayerSerialCellRebaseFaceInteractionCarrierAt corridor
        hunique offset hnext).card)
      (Fin (sourceLocalLayerSerialCellRebaseFaceInteractionCarrierAt corridor
        hunique offset hnext).card × Bool))
    (hentry : sourceLocalLayerSerialFaceRollingEntryAt graphData minimal caps
      coloring web corridor hunique offset hnext hnextNext incidence =
        some atom) :
    let graph := sourceLocalLayerBoundaryRebaseSuccessorFaceGraphAt corridor
      hunique offset hnext
    let target := sourceLocalLayerSerialCellRebaseFaceInteractionCarrierAt
      corridor hunique (sourceLocalLayerNextOffset offset hnext) hnextNext
    let targetDartAt := fun slot : Fin target.card =>
      ((carrierCoordinate target).symm slot).1
    let currentDartAt := sourceLocalLayerSerialCellRebaseUniformFaceDartAt
      corridor hunique offset hnext
    Set.InjOn web.annular.RS.edgeOf
      {vertex |
        (exteriorGraph graph targetDartAt).Reachable
          (exteriorLabelCapContractionAtomVertex currentDartAt
            (faceInterfaceIncidenceVertex web.annular.RS currentDartAt) atom)
          vertex} := by
  classical
  dsimp only
  let graph := sourceLocalLayerBoundaryRebaseSuccessorFaceGraphAt corridor
    hunique offset hnext
  let region := sourceLocalLayerSerialTerminalInputRegionAt corridor hunique
    (sourceLocalLayerNextOffset offset hnext)
  let target := sourceLocalLayerSerialCellRebaseFaceInteractionCarrierAt
    corridor hunique (sourceLocalLayerNextOffset offset hnext) hnextNext
  let targetDartAt := fun slot : Fin target.card =>
    ((carrierCoordinate target).symm slot).1
  let currentDartAt := sourceLocalLayerSerialCellRebaseUniformFaceDartAt
    corridor hunique offset hnext
  let atomVertex := exteriorLabelCapContractionAtomVertex currentDartAt
    (faceInterfaceIncidenceVertex web.annular.RS currentDartAt) atom
  have hpresent : ExteriorIncidencePresent graph targetDartAt Prod.fst
      (faceInterfaceIncidenceVertex web.annular.RS targetDartAt) incidence :=
    (sourceLocalLayerSerialFaceRollingEntryAt_isSome_iff graphData minimal caps
      coloring web corridor hunique offset hnext hnextNext incidence).1
      (by simp [hentry])
  have htargetInternal : dartOrbitFace web.annular.RS
        (targetDartAt incidence.1) ∈
      web.annular.cellulation.interiorFaces := by
    apply sourceLocalLayerSerialCellRebaseNextFaceInteractionDartAt_face_internal
      graphData minimal caps coloring web corridor hunique offset hnext
        hnextNext incidence.1
    exact hpresent.2.2.2.1
  have htargetRootFace : dartOrbitFace web.annular.RS
        (targetDartAt incidence.1) =
      dartOrbitFace web.annular.RS
        (faceInterfaceIncidenceVertex web.annular.RS targetDartAt incidence) :=
    faceRegionalDartGraph_adj_dartOrbitFace_eq web.annular.RS region hpresent.2
  have hatomVertex : atomVertex =
      faceInterfaceIncidenceVertex web.annular.RS targetDartAt incidence := by
    exact sourceLocalLayerSerialFaceRollingEntryAt_atomVertex graphData minimal
      caps coloring web corridor hunique offset hnext hnextNext incidence atom
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
theorem sourceLocalLayerSerialFaceRollingNextInteractionStateAt_code_eq
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
    (hnextNext :
      (sourceLocalLayerNextOffset offset hnext).val + 1 < blockLength - 3) :
    let preRebase := sourceLocalLayerSerialFaceInteractionPreRebaseStateAt
      graphData minimal caps coloring web corridor hunique offset hnext
    let factor := sourceLocalLayerSerialFaceRollingFactorAt graphData minimal
      caps coloring web corridor hunique offset hnext hnextNext
    let nextInteraction :=
      sourceLocalLayerSerialCellRebaseFaceInteractionCarrierAt corridor hunique
        (sourceLocalLayerNextOffset offset hnext) hnextNext
    let nextDartAt := fun slot : Fin nextInteraction.card =>
      ((carrierCoordinate nextInteraction).symm slot).1
    (factor.nextInteractionState preRebase (by rfl)).code () =
      exactFaceInterfaceExteriorLabelCapCode web.annular.RS
        (sourceLocalLayerSerialTerminalInputRegionAt corridor hunique
          (sourceLocalLayerNextOffset offset hnext))
        nextDartAt 6 := by
  classical
  dsimp only
  unfold SourceLocalLayerSerialFaceRollingFactor.nextInteractionState
  dsimp only
  unfold sourceLocalLayerSerialFaceRollingFactorAt
  dsimp only
  rw [sourceLocalLayerSerialFaceRebaseUniformSuccessorAt_eq graphData minimal
    caps coloring web corridor hunique offset hnext]
  let graph := sourceLocalLayerBoundaryRebaseSuccessorFaceGraphAt corridor
    hunique offset hnext
  let current := sourceLocalLayerSerialCellRebaseFaceInteractionCarrierAt
    corridor hunique offset hnext
  let target := sourceLocalLayerSerialCellRebaseFaceInteractionCarrierAt
    corridor hunique (sourceLocalLayerNextOffset offset hnext) hnextNext
  let currentDartAt := sourceLocalLayerSerialCellRebaseUniformFaceDartAt
    corridor hunique offset hnext
  let targetDartAt := fun slot : Fin target.card =>
    ((carrierCoordinate target).symm slot).1
  let retain := finiteCarrierPartialSource current target
  let entry := sourceLocalLayerSerialFaceRollingEntryAt graphData minimal caps
    coloring web corridor hunique offset hnext hnextNext
  let code :=
    sourceLocalLayerSerialCellRebaseUniformFaceSuccessorLabelCapSixCodeAt
      corridor hunique offset hnext
  have hcodeExact : code = exactInterfaceExteriorLabelCapCode graph
      currentDartAt
      (fun dart => web.annular.RS.edgeOf dart ∈
        sourceLocalLayerSerialTerminalInputRegionAt corridor hunique
          (sourceLocalLayerNextOffset offset hnext))
      Prod.fst (faceInterfaceIncidenceVertex web.annular.RS currentDartAt)
      web.annular.RS.edgeOf 6 := by
    exact
      sourceLocalLayerSerialCellRebaseUniformFaceSuccessorLabelCapSixCodeAt_exact
        corridor hunique offset hnext
  have hconnectivity : code.connectivity =
      exactInterfaceExteriorCode graph currentDartAt := by
    rw [hcodeExact]
    rfl
  have hinterfacePresent : ∀ slot,
      currentDartAt slot ∈ graph.support →
        code.interfacePresent slot = true := by
    intro slot hsupport
    exact
      sourceLocalLayerSerialCellRebaseUniformFaceSuccessorLabelCapSixCodeAt_interfacePresent_of_mem_support
        corridor hunique offset hnext slot hsupport
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
        sourceLocalLayerSerialTerminalInputRegionAt corridor hunique
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
        sourceLocalLayerSerialTerminalInputRegionAt corridor hunique
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
      sourceLocalLayerSerialCellRebaseUniformFaceSuccessor_incidenceComplete
        corridor hunique offset hnext slot outside houtside hadj
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
        sourceLocalLayerSerialTerminalInputRegionAt corridor hunique
          (sourceLocalLayerNextOffset offset hnext))
      Prod.fst (faceInterfaceIncidenceVertex web.annular.RS currentDartAt)
      web.annular.RS.edgeOf incidence 6
  have hsome : ∀ retained slot, retain retained = some slot →
      currentDartAt slot = targetDartAt retained := by
    intro retained slot hretain
    exact
      sourceLocalLayerSerialFaceRollingFactorAt_nextInteractionSource_dart_eq
        graphData minimal caps coloring web corridor hunique offset hnext
          hnextNext retained slot hretain
  have hnone : ∀ retained, retain retained = none →
      targetDartAt retained ∉ graph.support := by
    intro retained hretain
    exact
      sourceLocalLayerSerialFaceRollingFactorAt_nextInteractionSource_none_not_mem_support
        graphData minimal caps coloring web corridor hunique offset hnext
          hnextNext retained hretain
  have hcurrentInjective : Function.Injective currentDartAt :=
    sourceLocalLayerSerialCellRebaseUniformFaceDartAt_injective corridor hunique
      offset hnext
  have htargetInjective : Function.Injective targetDartAt := by
    intro left right heq
    apply (carrierCoordinate target).symm.injective
    exact Subtype.ext heq
  change partialContractedInterfaceExteriorLabelCapCode code retain Prod.fst
      (fun slot => decide (web.annular.RS.edgeOf (targetDartAt slot) ∈
        sourceLocalLayerSerialTerminalInputRegionAt corridor hunique
          (sourceLocalLayerNextOffset offset hnext))) entry =
    exactInterfaceExteriorLabelCapCode graph targetDartAt
      (fun dart => web.annular.RS.edgeOf dart ∈
        sourceLocalLayerSerialTerminalInputRegionAt corridor hunique
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
        sourceLocalLayerSerialTerminalInputRegionAt corridor hunique
          (sourceLocalLayerNextOffset offset hnext))
      Prod.fst (faceInterfaceIncidenceVertex web.annular.RS targetDartAt)
      web.annular.RS.edgeOf incidence 6]
    constructor
    · rintro ⟨atom, hentry, _hatomPresent⟩
      exact
        (sourceLocalLayerSerialFaceRollingEntryAt_isSome_iff graphData minimal
          caps coloring web corridor hunique offset hnext hnextNext
            incidence).1 (by simp [entry, hentry])
    · intro hpresent
      have hsomeEntry :=
        (sourceLocalLayerSerialFaceRollingEntryAt_isSome_iff graphData minimal
          caps coloring web corridor hunique offset hnext hnextNext
            incidence).2 hpresent
      rcases Option.isSome_iff_exists.mp hsomeEntry with ⟨atom, hentry⟩
      refine ⟨atom, by simpa [entry] using hentry, ?_⟩
      exact sourceLocalLayerSerialFaceRollingEntryAt_atomPresent graphData
        minimal caps coloring web corridor hunique offset hnext hnextNext
          incidence atom (by simpa [entry] using hentry)
  · funext first second
    apply Bool.eq_iff_iff.mpr
    rw [partialContractedInterfaceExteriorLabelCapCode_incidenceConnected_iff]
    rw [exactInterfaceExteriorLabelCapCode_incidenceConnected_iff graph
      targetDartAt
      (fun dart => web.annular.RS.edgeOf dart ∈
        sourceLocalLayerSerialTerminalInputRegionAt corridor hunique
          (sourceLocalLayerNextOffset offset hnext))
      Prod.fst (faceInterfaceIncidenceVertex web.annular.RS targetDartAt)
      web.annular.RS.edgeOf first second 6]
    constructor
    · rintro ⟨firstAtom, secondAtom, hfirstEntry, hsecondEntry,
        hfirstAtomPresent, hsecondAtomPresent, hreach⟩
      have hfirstPresent : ExteriorIncidencePresent graph targetDartAt Prod.fst
          (faceInterfaceIncidenceVertex web.annular.RS targetDartAt) first :=
        (sourceLocalLayerSerialFaceRollingEntryAt_isSome_iff graphData minimal
          caps coloring web corridor hunique offset hnext hnextNext first).1
          (by simp [entry, hfirstEntry])
      have hsecondPresent : ExteriorIncidencePresent graph targetDartAt Prod.fst
          (faceInterfaceIncidenceVertex web.annular.RS targetDartAt) second :=
        (sourceLocalLayerSerialFaceRollingEntryAt_isSome_iff graphData minimal
          caps coloring web corridor hunique offset hnext hnextNext second).1
          (by simp [entry, hsecondEntry])
      have hreachLiteral :=
        (exteriorLabelCapContractionAtomReachable_iff_of_exact graph
          currentDartAt targetDartAt retain hsome hnone Prod.fst
          (faceInterfaceIncidenceVertex web.annular.RS currentDartAt) code
          hconnectivity hinterfacePresent hincidencePresent hincidenceConnected
          hincidenceComplete firstAtom secondAtom hfirstAtomPresent
          hsecondAtomPresent).1 hreach
      have hfirstVertex :=
        sourceLocalLayerSerialFaceRollingEntryAt_atomVertex graphData minimal
          caps coloring web corridor hunique offset hnext hnextNext first
            firstAtom (by simpa [entry] using hfirstEntry)
      have hsecondVertex :=
        sourceLocalLayerSerialFaceRollingEntryAt_atomVertex graphData minimal
          caps coloring web corridor hunique offset hnext hnextNext second
            secondAtom (by simpa [entry] using hsecondEntry)
      exact ⟨hfirstPresent, hsecondPresent, by
        simpa [currentDartAt, targetDartAt] using
          hfirstVertex ▸ hsecondVertex ▸ hreachLiteral⟩
    · rintro ⟨hfirstPresent, hsecondPresent, hreachLiteral⟩
      have hfirstSome :=
        (sourceLocalLayerSerialFaceRollingEntryAt_isSome_iff graphData minimal
          caps coloring web corridor hunique offset hnext hnextNext first).2
          hfirstPresent
      have hsecondSome :=
        (sourceLocalLayerSerialFaceRollingEntryAt_isSome_iff graphData minimal
          caps coloring web corridor hunique offset hnext hnextNext second).2
          hsecondPresent
      rcases Option.isSome_iff_exists.mp hfirstSome with
        ⟨firstAtom, hfirstEntry⟩
      rcases Option.isSome_iff_exists.mp hsecondSome with
        ⟨secondAtom, hsecondEntry⟩
      have hfirstAtomPresent :=
        sourceLocalLayerSerialFaceRollingEntryAt_atomPresent graphData minimal
          caps coloring web corridor hunique offset hnext hnextNext first
            firstAtom (by simpa [entry] using hfirstEntry)
      have hsecondAtomPresent :=
        sourceLocalLayerSerialFaceRollingEntryAt_atomPresent graphData minimal
          caps coloring web corridor hunique offset hnext hnextNext second
            secondAtom (by simpa [entry] using hsecondEntry)
      have hfirstVertex :=
        sourceLocalLayerSerialFaceRollingEntryAt_atomVertex graphData minimal
          caps coloring web corridor hunique offset hnext hnextNext first
            firstAtom (by simpa [entry] using hfirstEntry)
      have hsecondVertex :=
        sourceLocalLayerSerialFaceRollingEntryAt_atomVertex graphData minimal
          caps coloring web corridor hunique offset hnext hnextNext second
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
        sourceLocalLayerSerialTerminalInputRegionAt corridor hunique
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
            (sourceLocalLayerSerialFaceRollingEntryAt_isSome_iff graphData
              minimal caps coloring web corridor hunique offset hnext hnextNext
                incidence).2 hpresent
          simp [entry, hentry] at hsomeEntry
        rw [partialContractedInterfaceExteriorLabelCapCode_incidenceCap_val]
        simp [hentry, exteriorIncidenceLabelSupport, hnotPresent]
    | some atom =>
        have hatomPresent :=
          sourceLocalLayerSerialFaceRollingEntryAt_atomPresent graphData minimal
            caps coloring web corridor hunique offset hnext hnextNext incidence
              atom (by simpa [entry] using hentry)
        have hlabelInjective : Set.InjOn web.annular.RS.edgeOf
            {vertex |
              (exteriorGraph graph targetDartAt).Reachable
                (exteriorLabelCapContractionAtomVertex currentDartAt
                  (faceInterfaceIncidenceVertex web.annular.RS currentDartAt)
                  atom)
                vertex} := by
          exact sourceLocalLayerSerialFaceRollingEntryAt_label_injective
            graphData minimal caps coloring web corridor hunique offset hnext
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
          (sourceLocalLayerSerialFaceRollingEntryAt_isSome_iff graphData
            minimal caps coloring web corridor hunique offset hnext hnextNext
              incidence).1 (by simp [entry, hentry])
        have hatomVertex :=
          sourceLocalLayerSerialFaceRollingEntryAt_atomVertex graphData minimal
            caps coloring web corridor hunique offset hnext hnextNext incidence
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
theorem sourceLocalLayerSerialFaceRollingNextInteractionStateAt_eq
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
    (hnextNext :
      (sourceLocalLayerNextOffset offset hnext).val + 1 < blockLength - 3)
    (color :
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.edgeSet → Color)
    (hcrossing : ∀ step,
      color ((sourceLocalLayerSerialTerminalInputCutDataAt corridor hunique
        (sourceLocalLayerNextOffset offset hnext)).crossingEdge step) ≠ 0) :
    let preRebase := sourceLocalLayerSerialFaceInteractionPreRebaseStateAt
      graphData minimal caps coloring web corridor hunique offset hnext
    let factor := sourceLocalLayerSerialFaceRollingFactorAt graphData minimal
      caps coloring web corridor hunique offset hnext hnextNext
    factor.nextInteractionState preRebase (by rfl) =
      (sourceLocalLayerSerialRootedInteractionStateForColorAt graphData minimal
        caps coloring web corridor hunique
          (sourceLocalLayerNextOffset offset hnext) hnextNext color hcrossing
        ).faceInteractionExterior := by
  dsimp only
  rw [BoundedInterfaceExteriorLabelCapFamilyCode.mk.injEq]
  refine ⟨rfl, ?_⟩
  apply heq_of_eq
  funext family
  rw [sourceLocalLayerSerialFaceRollingNextInteractionStateAt_code_eq
    graphData minimal caps coloring web corridor hunique offset hnext hnextNext]
  rfl

end

end GoertzelV24ClosedWebLocalLayerSerialRootedInteractionFaceRollingExact

end Mettapedia.GraphTheory.FourColor
