import Mettapedia.GraphTheory.FourColor.Compositional.CarrierSaturationCyclicCut
import Mettapedia.GraphTheory.FourColor.GoertzelV24ConnectedVertexSideEdgeShore

/-!
# Coherent rooted saturation of nested carrier prefixes

Component-saturated carrier prefixes remain monotone with the sweep cut.
Using one common exterior root therefore preserves nesting under rooted cut
saturation.  The first carrier edge added between two distinct cuts witnesses
strictness of the resulting incident-edge shores.
-/

namespace Mettapedia.GraphTheory.FourColor.Compositional

namespace CarrierSaturationRootedNesting

open CarrierSaturationBoundaryDecomposition
open CarrierSaturationConnected
open CarrierSaturationCyclicCut
open GoertzelV24ConnectedVertexSideEdgeShore
open GoertzelV24CyclicThreeCutConnectedSides
open GoertzelV24OrderedMeshResidualSiteFacialBond
open GoertzelV24OrderedMeshResidualSiteMatching
open GoertzelV24ResidualReturnCycleOrder
open GoertzelV24ResidualReturnPairing
open GoertzelV24ResidualReturnSectorNoncrossing
open MatchingParity
open Mettapedia.GraphTheory
open PathPrefixBoundary
open ResidualReturnComponentSaturation
open RootedCutSaturation
open SimpleGraph

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Component-saturated carrier prefixes are monotone in their cut
coordinate. -/
theorem carrierPrefixReturnSaturation_mono
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (site : ProperAlternatingSiteWitness G sigma first second)
    {firstCut secondCut : CyclePosition sigma site}
    (horder : firstCut ≤ secondCut) :
    ∀ vertex,
      carrierPrefixReturnSaturation hG sigma hSigma site firstCut vertex →
        carrierPrefixReturnSaturation hG sigma hSigma site secondCut vertex := by
  apply pairingBoundarySaturation_mono
  intro position hposition
  exact hposition.trans_le horder

/-- The suffix component for a later saturated cut lies inside the suffix
component of every earlier saturated cut. -/
theorem carrierPrefixExteriorComponent_mono
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (site : ProperAlternatingSiteWitness G sigma first second)
    {firstCut secondCut : CyclePosition sigma site}
    (horder : firstCut ≤ secondCut) :
    ∀ vertex,
      carrierPrefixExteriorComponent hG sigma hSigma site secondCut vertex →
        carrierPrefixExteriorComponent hG sigma hSigma site firstCut vertex := by
  intro vertex hvertex
  let firstComplement := fun point =>
    ¬carrierPrefixReturnSaturation hG sigma hSigma site firstCut point
  let secondComplement := fun point =>
    ¬carrierPrefixReturnSaturation hG sigma hSigma site secondCut point
  have hcomplementMono : ∀ point, secondComplement point →
      firstComplement point := by
    intro point hnotSecond hfirst
    exact hnotSecond
      (carrierPrefixReturnSaturation_mono hG sigma hSigma site horder point
        hfirst)
  have hsecondOutsideFirst : firstComplement
      (cycleVertexOrder sigma site secondCut).1 := by
    change ¬carrierPrefixReturnSaturation hG sigma hSigma site firstCut
      (cycleVertexOrder sigma site secondCut).1
    rw [cycleVertex_mem_carrierPrefixReturnSaturation_iff]
    exact not_lt_of_ge horder
  rcases hvertex with ⟨hvertexOutsideSecond, hsecondToVertex⟩
  have hsecondToVertexFirst :
      (G.induce firstComplement).Reachable
        ⟨(cycleVertexOrder sigma site secondCut).1, hsecondOutsideFirst⟩
        ⟨vertex, hcomplementMono vertex hvertexOutsideSecond⟩ := by
    let inclusion := G.induceHomOfLE hcomplementMono
    have hmapped := hsecondToVertex.map inclusion.toHom
    convert hmapped using 1 <;> apply Subtype.ext <;> rfl
  rcases cycleVertex_mem_carrierPrefixExteriorComponent hG sigma hSigma site
      firstCut secondCut horder with ⟨_secondOutside, hfirstToSecond⟩
  refine ⟨hcomplementMono vertex hvertexOutsideSecond, ?_⟩
  exact hfirstToSecond.trans hsecondToVertexFirst

/-- If a common exterior root lies beyond an anchor cut, every carrier
coordinate between an earlier cut and that anchor is in the complement
component rooted at the common root. -/
theorem cycleVertex_mem_commonRootExteriorComponent
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (site : ProperAlternatingSiteWitness G sigma first second)
    {cut coordinate anchor : CyclePosition sigma site}
    (hcutCoordinate : cut ≤ coordinate) (hcoordinateAnchor : coordinate ≤ anchor)
    (outsideRoot : V)
    (hrootAnchor : carrierPrefixExteriorComponent hG sigma hSigma site anchor
      outsideRoot) :
    inducedReachableSide G
      (fun vertex =>
        ¬carrierPrefixReturnSaturation hG sigma hSigma site cut vertex)
      outsideRoot
      (carrierPrefixExteriorComponent_mono hG sigma hSigma site
        (hcutCoordinate.trans hcoordinateAnchor) outsideRoot hrootAnchor).choose
      (cycleVertexOrder sigma site coordinate).1 := by
  have hrootCut := carrierPrefixExteriorComponent_mono hG sigma hSigma site
    (hcutCoordinate.trans hcoordinateAnchor) outsideRoot hrootAnchor
  have hcoordinateCut := cycleVertex_mem_carrierPrefixExteriorComponent
    hG sigma hSigma site cut coordinate hcutCoordinate
  rcases hrootCut with ⟨hrootOutside, hcutToRoot⟩
  rcases hcoordinateCut with ⟨hcoordinateOutside, hcutToCoordinate⟩
  refine ⟨hcoordinateOutside, ?_⟩
  exact hcutToRoot.symm.trans hcutToCoordinate

/-- Rooted closure sides of two distinct saturated carrier prefixes have
strictly nested incident-edge shores. -/
theorem incidentEdgeShore_carrierClosureSide_ssubset
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (site : ProperAlternatingSiteWitness G sigma first second)
    {firstCut secondCut anchor : CyclePosition sigma site}
    (hfirstSecond : firstCut < secondCut)
    (hsecondAnchor : secondCut ≤ anchor)
    (outsideRoot : V)
    (hrootAnchor : carrierPrefixExteriorComponent hG sigma hSigma site anchor
      outsideRoot) :
    incidentEdgeShore G
        (closureSide (G := G)
          (carrierPrefixReturnSaturation hG sigma hSigma site firstCut)
          outsideRoot
          (carrierPrefixExteriorComponent_mono hG sigma hSigma site
            hfirstSecond.le outsideRoot
            (carrierPrefixExteriorComponent_mono hG sigma hSigma site
              hsecondAnchor outsideRoot hrootAnchor)).choose) ⊂
      incidentEdgeShore G
        (closureSide (G := G)
          (carrierPrefixReturnSaturation hG sigma hSigma site secondCut)
          outsideRoot
          (carrierPrefixExteriorComponent_mono hG sigma hSigma site
            hsecondAnchor outsideRoot hrootAnchor).choose) := by
  let hrootSecond := carrierPrefixExteriorComponent_mono hG sigma hSigma site
    hsecondAnchor outsideRoot hrootAnchor
  let hrootFirst := carrierPrefixExteriorComponent_mono hG sigma hSigma site
    (hfirstSecond.le.trans hsecondAnchor) outsideRoot hrootAnchor
  let firstSide := carrierPrefixReturnSaturation hG sigma hSigma site firstCut
  let secondSide := carrierPrefixReturnSaturation hG sigma hSigma site secondCut
  let firstClosure := closureSide (G := G) firstSide outsideRoot
    hrootFirst.choose
  let secondClosure := closureSide (G := G) secondSide outsideRoot
    hrootSecond.choose
  have hsideMono : ∀ vertex, firstSide vertex → secondSide vertex := by
    exact carrierPrefixReturnSaturation_mono hG sigma hSigma site
      hfirstSecond.le
  have hclosureMono : ∀ vertex, firstClosure vertex →
      secondClosure vertex := by
    intro vertex hvertex
    apply closureSide_mono (G := G) hsideMono outsideRoot hrootSecond.choose
      vertex
    simpa only [firstClosure, firstSide, hrootFirst] using hvertex
  have hshoreMono : incidentEdgeShore G firstClosure ⊆
      incidentEdgeShore G secondClosure :=
    incidentEdgeShore_mono hclosureMono
  apply (Finset.ssubset_iff_of_subset hshoreMono).2
  let next : CyclePosition sigma site := ⟨firstCut.val + 1, by
    have hlt := Fin.mk_lt_mk.mp hfirstSecond
    have := secondCut.isLt
    omega⟩
  have hnextPositive : 0 < (carrierPrefixPathCut site next).val := by
    simp only [carrierPrefixPathCut_val, next]
    omega
  let edge := forwardPathEdge site.cycle.tail
    (carrierPrefixPathCut site next) hnextPositive
  have hnextSecond : next ≤ secondCut := by
    apply Fin.mk_le_mk.mpr
    exact hfirstSecond
  have hfirstNext : firstCut ≤ next := by
    apply Fin.mk_le_mk.mpr
    omega
  have hfirstVertex : site.cycle.tail.getVert
      ((carrierPrefixPathCut site next).val - 1) =
        (cycleVertexOrder sigma site firstCut).1 := by
    have hvalue : (carrierPrefixPathCut site next).val - 1 =
        firstCut.val := by
      simp only [carrierPrefixPathCut_val, next]
      omega
    rw [hvalue]
    change site.cycle.tail.getVert (carrierPrefixPathCut site firstCut) =
      (cycleVertexOrder sigma site firstCut).1
    rw [← cycleVertexOrder_carrierCyclePositionOfPathCoordinate]
    rw [carrierCyclePositionOfPathCut]
  have hnextVertex : site.cycle.tail.getVert
      (carrierPrefixPathCut site next) =
        (cycleVertexOrder sigma site next).1 := by
    rw [← cycleVertexOrder_carrierCyclePositionOfPathCoordinate]
    rw [carrierCyclePositionOfPathCut]
  refine ⟨edge, ?_, ?_⟩
  · apply (mem_incidentEdgeShore_iff secondClosure edge).2
    refine ⟨(cycleVertexOrder sigma site firstCut).1, ?_, ?_⟩
    · change (cycleVertexOrder sigma site firstCut).1 ∈
        s(site.cycle.tail.getVert
            ((carrierPrefixPathCut site next).val - 1),
          site.cycle.tail.getVert (carrierPrefixPathCut site next))
      rw [hfirstVertex, hnextVertex]
      simp
    · apply side_subset_closureSide
      exact cycleVertex_mem_carrierPrefixReturnSaturation hG sigma hSigma site
        secondCut firstCut hfirstSecond
  · intro hedge
    rcases (mem_incidentEdgeShore_iff firstClosure edge).1 hedge with
      ⟨vertex, hvertexEdge, hvertexClosure⟩
    have hcases : vertex = (cycleVertexOrder sigma site firstCut).1 ∨
        vertex = (cycleVertexOrder sigma site next).1 := by
      have : vertex = site.cycle.tail.getVert
            ((carrierPrefixPathCut site next).val - 1) ∨
          vertex = site.cycle.tail.getVert
            (carrierPrefixPathCut site next) := by
        simpa [edge, forwardPathEdge] using hvertexEdge
      simpa only [hfirstVertex, hnextVertex] using this
    rcases hcases with rfl | rfl
    · apply hvertexClosure
      exact cycleVertex_mem_commonRootExteriorComponent hG sigma hSigma site
        firstCut.le_refl hfirstSecond.le outsideRoot hrootSecond
    · apply hvertexClosure
      exact cycleVertex_mem_commonRootExteriorComponent hG sigma hSigma site
        hfirstNext hnextSecond outsideRoot hrootSecond

end

end CarrierSaturationRootedNesting

end Mettapedia.GraphTheory.FourColor.Compositional
