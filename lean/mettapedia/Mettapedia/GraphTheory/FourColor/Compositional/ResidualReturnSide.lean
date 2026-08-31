import Mettapedia.GraphTheory.Embedding.FaceCutGauge
import Mettapedia.GraphTheory.FourColor.Compositional.ResidualReturnNoncrossing

/-!
# Rooted sides of residual returns

A facial bond names one shore by a finite set of faces, but exchanging that
set with its complement describes the same cut.  This module turns the bond
into an exact binary face cut and normalizes its labels at a chosen root face.
The resulting coordinate is independent of the arbitrary choice of shore.

This is the comparison surface needed before residual-return data at distinct
mesh sites can be synchronized: local Boolean names are replaced by values in
one rooted ambient face coordinate system.
-/

namespace Mettapedia.GraphTheory.FourColor.Compositional.ResidualReturnSide

open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24OrderedMeshResidualSiteFacialBond
open GoertzelV24ResidualReturnCycleOrder
open GoertzelV24ResidualReturnPairing
open GoertzelV24ResidualReturnShore
open GoertzelV24TwoEdgeCutMinimality
open MatchingParity
open Mettapedia.GraphTheory.Embedding
open Mettapedia.GraphTheory.FourColor.Compositional.ResidualReturnNoncrossing
open SimpleGraph
open SimpleGraphDartRotation

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

/-- The exact binary face cut represented by a residual site's facial bond. -/
def facialBondCut
    (rotation : Data G) (sigma : Pairing V) {first second : V}
    (bond : ProperAlternatingSiteFacialBondWitness rotation sigma first second) :
    ExactFaceCut rotation.toRotationSystem
      (fun edge : G.edgeSet => edge.1 ∈ bond.site.cycle.edges) F2 :=
  ExactFaceCut.ofFinset bond.faces fun dart =>
    bond.cycle_separates_faces dart

/-- The facial orbit immediately adjacent to the third dart at one cyclic
return position. -/
def returnFace
    (rotation : Data G)
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (bond : ProperAlternatingSiteFacialBondWitness rotation sigma first second)
    (position : CyclePosition sigma bond.site) :
    OrbitFace rotation.toRotationSystem :=
  dartOrbitFace rotation.toRotationSystem
    (siteThirdDart hG sigma hSigma bond.site
      (cycleVertexOrder sigma bond.site position))

/-- The side of one residual-return endpoint in the face coordinate system
whose chosen root face has value zero. -/
def basedReturnSide
    (rotation : Data G)
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (root : OrbitFace rotation.toRotationSystem)
    (bond : ProperAlternatingSiteFacialBondWitness rotation sigma first second)
    (position : CyclePosition sigma bond.site) : F2 :=
  (facialBondCut rotation sigma bond).basedLabel root
    (returnFace rotation hG sigma hSigma bond position)

/-- Equality of rooted side coordinates is exactly equality of the historical
local Boolean shore labels. -/
theorem basedReturnSide_eq_iff_orderedReturnShore_eq
    (rotation : Data G)
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (root : OrbitFace rotation.toRotationSystem)
    (bond : ProperAlternatingSiteFacialBondWitness rotation sigma first second)
    (left right : CyclePosition sigma bond.site) :
    basedReturnSide rotation hG sigma hSigma root bond left =
        basedReturnSide rotation hG sigma hSigma root bond right ↔
      orderedReturnShore rotation hG sigma hSigma bond left =
        orderedReturnShore rotation hG sigma hSigma bond right := by
  simp only [basedReturnSide, ExactFaceCut.basedLabel]
  rw [sub_left_inj]
  unfold facialBondCut returnFace orderedReturnShore
  by_cases hleft : dartOrbitFace rotation.toRotationSystem
      (siteThirdDart hG sigma hSigma bond.site
        (cycleVertexOrder sigma bond.site left)) ∈ bond.faces <;>
    by_cases hright : dartOrbitFace rotation.toRotationSystem
      (siteThirdDart hG sigma hSigma bond.site
        (cycleVertexOrder sigma bond.site right)) ∈ bond.faces <;>
    simp [ExactFaceCut.ofFinset, hleft, hright]

/-- Both endpoints of one physical residual return have the same rooted side
coordinate. -/
theorem basedReturnSide_partner
    (rotation : Data G)
    (hcubic : rotation.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic rotation.toRotationSystem)
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (root : OrbitFace rotation.toRotationSystem)
    (bond : ProperAlternatingSiteFacialBondWitness rotation sigma first second)
    (position : CyclePosition sigma bond.site) :
    basedReturnSide rotation hG sigma hSigma root bond position =
      basedReturnSide rotation hG sigma hSigma root bond
        ((orderedSiteReturnPairing hG sigma hSigma bond.site).partner
          position) := by
  apply (basedReturnSide_eq_iff_orderedReturnShore_eq
    rotation hG sigma hSigma root bond _ _).2
  exact orderedReturnShore_partner rotation hcubic hrotation hG sigma hSigma
    bond position

/-- On a connected two-sided map, every exact binary cut supported on the
same residual cycle gives the same rooted face coordinate as the facial-bond
construction. -/
theorem facialBondCut_basedLabel_eq
    (rotation : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    (sigma : Pairing V) {first second : V}
    (bond : ProperAlternatingSiteFacialBondWitness rotation sigma first second)
    (other : ExactFaceCut rotation.toRotationSystem
      (fun edge : G.edgeSet => edge.1 ∈ bond.site.cycle.edges) F2)
    (root face : OrbitFace rotation.toRotationSystem) :
    (facialBondCut rotation sigma bond).basedLabel root face =
      other.basedLabel root face := by
  apply ExactFaceCut.basedLabel_eq minimal.facesTwoSided
  exact orbitFaceInteriorDual_connected rotation.toRotationSystem
    minimal.spherical.cubic minimal.primalConnected
      minimal.vertexRotationCyclic

/-- The noncrossing theorem can be consumed entirely in the rooted ambient
face coordinate system. -/
theorem not_crosses_of_basedReturnSide_eq
    (rotation : Data G)
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) {first second : V}
    (receipt : TwoSectorReturnReceipt rotation hG sigma first second)
    (root : OrbitFace rotation.toRotationSystem)
    (left right : OrderedReturnChord
      (orderedSiteReturnPairing hG sigma receipt.base.sigma_supported
        receipt.base.bond.site))
    (hside : basedReturnSide rotation hG sigma
        receipt.base.sigma_supported root receipt.base.bond left.left =
      basedReturnSide rotation hG sigma
        receipt.base.sigma_supported root receipt.base.bond right.left) :
    ¬left.Crosses right := by
  apply receipt.sameShore_noncrossing left right
  exact (basedReturnSide_eq_iff_orderedReturnShore_eq
    rotation hG sigma receipt.base.sigma_supported root receipt.base.bond
      left.left right.left).1 hside

end

end Mettapedia.GraphTheory.FourColor.Compositional.ResidualReturnSide
