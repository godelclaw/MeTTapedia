import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalLayerSerialCellUniformFaceTargetCapExact
import Mettapedia.GraphTheory.FourColor.GoertzelV24InterfaceExteriorLabelCapFullComponent
import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalLayerSerialCellFaceFiniteOutputCap

/-!
# Decode the rolling successor's full facial component caps

The cap-six target factor stores strict-exterior component weights.  Forgetting
its whole rolling interface turns represented darts and old exterior
components into one finite atom graph.  Its component total, capped once more
at five, is exactly the component-progress field of the next cumulative face
state.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebLocalLayerSerialCellUniformFaceTargetComponentCap

open GoertzelV24BoundedCarrierGraphFamilyCode
open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAnnularEmbedding.ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAtGoodWord
open GoertzelV24ClosedWebAtGoodWord.Instance
open GoertzelV24ClosedWebAtGoodWord.Instance.LocalLayerFormation
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24ClosedWebLocalLayerSerialCellFaceFiniteOutputCap
open GoertzelV24ClosedWebLocalLayerSerialCellUniformFaceTargetCap
open GoertzelV24ClosedWebLocalLayerSerialCellUniformFaceTargetCapExact
open GoertzelV24FaceOrbitIncidence
open GoertzelV24FacialPentagonCap
open GoertzelV24InterfaceDeletionComponentFactor
open GoertzelV24InterfaceExteriorLabelCapFactor
open GoertzelV24InterfaceExteriorLabelCapFullComponent
open GoertzelV24MinimalFacialPentagonCapPairLocalCellCarrier
open GoertzelV24RotationFaceInterfaceExteriorLabelCap
open GoertzelV24RotationFaceRegionalDartGraph
open GoertzelV24TwoEdgeCutMinimality
open GoertzelV24TwoPentagonCapOpening
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance uniformFaceTargetComponentCapEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

local instance uniformFaceTargetComponentCapIncidenceLinearOrder {n : Nat} :
    LinearOrder (Fin n × Bool) :=
  LinearOrder.lift' (fun incidence : Fin n × Bool ↦ toLex incidence)
    toLex.injective

local instance uniformFaceTargetComponentCapOpenedGraphDecidableRel
    {graphData : Data G}
    (caps : OrientedFacialPentagonCapPair (G := G) graphData) :
    DecidableRel
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.Adj :=
  Classical.decRel _

/-- Fully finite cap-at-five component query on one coordinate of the rolling
target.  An absent coordinate denotes cap zero. -/
noncomputable def sourceLocalLayerSerialCellRebaseUniformFaceTargetComponentCapAt
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
    let target := sourceLocalLayerSerialFaceTransitionCarrierAt corridor hunique
      (sourceLocalLayerNextOffset offset hnext)
    Fin target.card → Fin 6 := by
  dsimp only
  let code :=
    sourceLocalLayerSerialCellRebaseUniformFaceTargetLabelCapSixCodeAt
      graphData minimal caps coloring web corridor hunique offset hnext
  exact fun slot =>
    if code.interfacePresent slot then
      ⟨min (interfaceExteriorLabelCapFullComponent code Prod.fst slot).val 5,
        Nat.lt_succ_of_le (Nat.min_le_right _ _)⟩
    else
      0

/-- The finite target component query is the literal cap at five of the
distinct primal edges in the successor regional face component. -/
theorem sourceLocalLayerSerialCellRebaseUniformFaceTargetComponentCapAt_exact
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
    let target := sourceLocalLayerSerialFaceTransitionCarrierAt corridor hunique
      (sourceLocalLayerNextOffset offset hnext)
    let targetDartAt := fun slot : Fin target.card =>
      ((carrierCoordinate target).symm slot).1
    sourceLocalLayerSerialCellRebaseUniformFaceTargetComponentCapAt graphData
        minimal caps coloring web corridor hunique offset hnext slot =
      ⟨min (sourceLocalLayerBoundaryRebaseFaceComponentEdges web.annular.RS
          (sourceLocalLayerSerialTerminalInputRegionAt corridor hunique
            (sourceLocalLayerNextOffset offset hnext))
          (targetDartAt slot)).card 5,
        Nat.lt_succ_of_le (Nat.min_le_right _ _)⟩ := by
  classical
  dsimp only
  let next := sourceLocalLayerNextOffset offset hnext
  let region := sourceLocalLayerSerialTerminalInputRegionAt corridor hunique next
  let graph := faceRegionalDartGraph web.annular.RS region
  let target := sourceLocalLayerSerialFaceTransitionCarrierAt corridor hunique
    next
  let targetDartAt := fun slot : Fin target.card =>
    ((carrierCoordinate target).symm slot).1
  let code :=
    sourceLocalLayerSerialCellRebaseUniformFaceTargetLabelCapSixCodeAt
      graphData minimal caps coloring web corridor hunique offset hnext
  change (if code.interfacePresent slot then
      (⟨min (interfaceExteriorLabelCapFullComponent code Prod.fst slot).val 5,
        Nat.lt_succ_of_le (Nat.min_le_right _ _)⟩ : Fin 6)
    else (0 : Fin 6)) =
      ⟨min (sourceLocalLayerBoundaryRebaseFaceComponentEdges web.annular.RS
          region (targetDartAt slot)).card 5,
        Nat.lt_succ_of_le (Nat.min_le_right _ _)⟩
  by_cases hpresent : web.annular.RS.edgeOf (targetDartAt slot) ∈ region
  · have hcodePresent : code.interfacePresent slot = true := by
      unfold code
      rw [sourceLocalLayerSerialCellRebaseUniformFaceTargetLabelCapSixCodeAt_exact]
      exact (exactFaceInterfaceExteriorLabelCapCode_interfacePresent_iff
        web.annular.RS region targetDartAt slot 6).2 hpresent
    simp only [hcodePresent, if_true]
    have htargetInternal : dartOrbitFace web.annular.RS (targetDartAt slot) ∈
        web.annular.cellulation.interiorFaces := by
      exact
        sourceLocalLayerSerialCellRebaseUniformFaceTargetDartAt_face_internal
          graphData minimal caps coloring web corridor hunique offset hnext slot
            hpresent
    have hlabelInjective : Set.InjOn web.annular.RS.edgeOf
        {vertex | graph.Reachable (targetDartAt slot) vertex} := by
      intro left hleft right hright hedge
      have hleftFace : dartOrbitFace web.annular.RS (targetDartAt slot) =
          dartOrbitFace web.annular.RS left :=
        faceRegionalDartGraph_reachable_dartOrbitFace_eq web.annular.RS region
          hleft
      have hrightFace : dartOrbitFace web.annular.RS (targetDartAt slot) =
          dartOrbitFace web.annular.RS right :=
        faceRegionalDartGraph_reachable_dartOrbitFace_eq web.annular.RS region
          hright
      have hinjective : Set.InjOn web.annular.RS.edgeOf
          (orbitFaceDarts web.annular.RS
            (dartOrbitFace web.annular.RS (targetDartAt slot))) := by
        apply Finset.card_image_iff.mp
        exact InteriorFace.boundary_card_eq_darts_card web (targetDartAt slot)
          htargetInternal
      exact hinjective
        ((mem_orbitFaceDarts_iff web.annular.RS
          (dartOrbitFace web.annular.RS (targetDartAt slot)) left).2
            hleftFace.symm)
        ((mem_orbitFaceDarts_iff web.annular.RS
          (dartOrbitFace web.annular.RS (targetDartAt slot)) right).2
            hrightFace.symm)
        hedge
    have hfull :
        (interfaceExteriorLabelCapFullComponent
          (exactFaceInterfaceExteriorLabelCapCode web.annular.RS region
            targetDartAt 6) Prod.fst slot).val =
          min (fullComponentLabelSupport graph targetDartAt
            web.annular.RS.edgeOf slot).card 6 := by
      unfold exactFaceInterfaceExteriorLabelCapCode
      apply interfaceExteriorLabelCapFullComponent_exact
      · intro targetSlot hsupport
        rcases hsupport with ⟨other, hadj⟩
        exact (faceRegionalDartGraph_adj web.annular.RS region _ _).1
          hadj |>.2.2.1
      · intro targetSlot outside houtside hadj
        rcases exists_faceInterfaceIncidence_of_adj_outside web.annular.RS
            region targetDartAt targetSlot outside hadj houtside with
          ⟨direction, hvertex, _⟩
        exact ⟨(targetSlot, direction), rfl, hvertex⟩
      · exact hpresent
      · intro left right heq
        apply (carrierCoordinate target).symm.injective
        exact Subtype.ext heq
      · exact hlabelInjective
    have hsupport : fullComponentLabelSupport graph targetDartAt
          web.annular.RS.edgeOf slot =
        sourceLocalLayerBoundaryRebaseFaceComponentEdges web.annular.RS region
          (targetDartAt slot) := by
      letI : DecidablePred (graph.Reachable (targetDartAt slot)) :=
        Classical.decPred _
      ext edge
      rw [mem_sourceLocalLayerBoundaryRebaseFaceComponentEdges_iff]
      constructor
      · intro hedge
        rw [fullComponentLabelSupport] at hedge
        rcases Finset.mem_image.mp hedge with ⟨dart, hdart, hedgeOf⟩
        rw [Finset.mem_filter] at hdart
        have hedgeRegion : web.annular.RS.edgeOf dart ∈ region := by
          by_cases heq : dart = targetDartAt slot
          · simpa [heq] using hpresent
          · have hsupport : dart ∈ graph.support :=
              SimpleGraph.mem_support_of_reachable heq hdart.2.symm
            rw [SimpleGraph.mem_support] at hsupport
            rcases hsupport with ⟨neighbor, hadj⟩
            exact (faceRegionalDartGraph_adj web.annular.RS region _ _).1
              (by simpa [graph] using hadj) |>.2.2.1
        exact ⟨hedgeOf ▸ hedgeRegion,
          ⟨⟨dart, web.annular.RS.mem_dartsOn.2 hedgeOf⟩, hdart.2⟩⟩
      · rintro ⟨hedgeRegion, dart, hreachable⟩
        rw [fullComponentLabelSupport]
        apply Finset.mem_image.mpr
        exact ⟨dart.1, by
          rw [Finset.mem_filter]
          exact ⟨Finset.mem_univ _, by simpa [graph] using hreachable⟩,
          web.annular.RS.mem_dartsOn.1 dart.2⟩
    unfold code
    rw [sourceLocalLayerSerialCellRebaseUniformFaceTargetLabelCapSixCodeAt_exact]
    apply Fin.ext
    simp only
    rw [hfull, hsupport]
    omega
  · have hcodePresent : code.interfacePresent slot = false := by
      apply Bool.eq_false_iff.mpr
      intro htrue
      have :=
        (sourceLocalLayerSerialCellRebaseUniformFaceTargetLabelCapSixCodeAt_interfacePresent_iff
          graphData minimal caps coloring web corridor hunique offset hnext
            slot).1 htrue
      exact hpresent this
    simp [hcodePresent]
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro edge hedge
    rw [mem_sourceLocalLayerBoundaryRebaseFaceComponentEdges_iff] at hedge
    rcases hedge with ⟨hedgeRegion, dart, hreachable⟩
    by_cases heq : dart.1 = targetDartAt slot
    · have hedgeOf : web.annular.RS.edgeOf dart.1 = edge :=
        web.annular.RS.mem_dartsOn.1 dart.2
      rw [← hedgeOf, heq] at hedgeRegion
      exact hpresent hedgeRegion
    · have hsupport : targetDartAt slot ∈ graph.support :=
        SimpleGraph.mem_support_of_reachable (Ne.symm heq) hreachable
      rw [SimpleGraph.mem_support] at hsupport
      rcases hsupport with ⟨neighbor, hadj⟩
      exact hpresent ((faceRegionalDartGraph_adj web.annular.RS region _ _).1
        (by simpa [graph] using hadj) |>.2.2.1)

end

end GoertzelV24ClosedWebLocalLayerSerialCellUniformFaceTargetComponentCap

end Mettapedia.GraphTheory.FourColor
