import Mettapedia.Combinatorics.Matching.CircuitPartition
import Mettapedia.GraphTheory.FourColor.Compositional.ResidualReturnParity

/-!
# Circuit parity at one residual matching exchange

At a proper alternating site, the residual graph before the matching exchange
uses the site's `tau` edges on the alternating cycle; after the exchange it uses
the original `sigma` edges.  Both states use the same off-cycle return paths.

This file expresses those two circuit partitions in the common cyclic boundary
coordinate.  Their circuit parity is computed from exactly two ingredients:
the parity-labelled physical return pairing and the unit-length local matching.
It does not yet identify the finite orbits with ambient residual connected
components; that is the next geometric bridge.
-/

namespace Mettapedia.GraphTheory.FourColor.Compositional

namespace ResidualCircuitParity

open GoertzelV24OrderedMeshResidualSiteMatching
open GoertzelV24ResidualReturnCycleOrder
open GoertzelV24ResidualReturnPairing
open MatchingParity
open ResidualReturnParity
open SimpleGraph

attribute [-instance]
  GoertzelV24RetainedVertexRotationSplice.retainedVertexFintype
  GoertzelV24SeamFaceArcPartition.hitPointFintype

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Restrict the original matching to the alternating carrier. -/
def siteSigmaPairing
    (sigma : Pairing V) {first second : V}
    (site : ProperAlternatingSiteWitness G sigma first second) :
    Pairing (BoundaryVertex site.carrier) :=
  sigma.subtype (fun vertex => vertex ∈ site.carrier) site.sigma_closed

/-- Restrict the incoming matching to the alternating carrier. -/
def siteTauPairing
    (sigma : Pairing V) {first second : V}
    (site : ProperAlternatingSiteWitness G sigma first second) :
    Pairing (BoundaryVertex site.carrier) :=
  site.tau.subtype (fun vertex => vertex ∈ site.carrier) site.tau_closed

/-- The original matching on the carrier, transported to cyclic positions. -/
def orderedSiteSigmaPairing
    (sigma : Pairing V) {first second : V}
    (site : ProperAlternatingSiteWitness G sigma first second) :
    Pairing (CyclePosition sigma site) :=
  pairingCongr (cycleVertexOrder sigma site) (siteSigmaPairing sigma site)

/-- The incoming matching on the carrier, transported to cyclic positions. -/
def orderedSiteTauPairing
    (sigma : Pairing V) {first second : V}
    (site : ProperAlternatingSiteWitness G sigma first second) :
    Pairing (CyclePosition sigma site) :=
  pairingCongr (cycleVertexOrder sigma site) (siteTauPairing sigma site)

@[simp]
theorem cycleVertexOrder_orderedSiteSigmaPairing_partner
    (sigma : Pairing V) {first second : V}
    (site : ProperAlternatingSiteWitness G sigma first second)
    (position : CyclePosition sigma site) :
    cycleVertexOrder sigma site
        ((orderedSiteSigmaPairing sigma site).partner position) =
      (siteSigmaPairing sigma site).partner
        (cycleVertexOrder sigma site position) := by
  simp [orderedSiteSigmaPairing, pairingCongr]

@[simp]
theorem cycleVertexOrder_orderedSiteTauPairing_partner
    (sigma : Pairing V) {first second : V}
    (site : ProperAlternatingSiteWitness G sigma first second)
    (position : CyclePosition sigma site) :
    cycleVertexOrder sigma site
        ((orderedSiteTauPairing sigma site).partner position) =
      (siteTauPairing sigma site).partner
        (cycleVertexOrder sigma site position) := by
  simp [orderedSiteTauPairing, pairingCongr]

/-- Parity of the old residual circuit through a cyclic position.  Old
residual circuits use `tau` edges on the operated alternating cycle. -/
def oldCircuitParity
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (site : ProperAlternatingSiteWitness G sigma first second)
    (root : CyclePosition sigma site) : ZMod 2 :=
  CircuitPartition.circuitParity
    (orderedSiteReturnParityPairing hG sigma hSigma site)
    (orderedSiteTauPairing sigma site) root

/-- Parity of the new residual circuit through a cyclic position.  New
residual circuits use `sigma` edges on the operated alternating cycle. -/
def newCircuitParity
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (site : ProperAlternatingSiteWitness G sigma first second)
    (root : CyclePosition sigma site) : ZMod 2 :=
  CircuitPartition.circuitParity
    (orderedSiteReturnParityPairing hG sigma hSigma site)
    (orderedSiteSigmaPairing sigma site) root

/-- The old circuit parity is the sum of physical return-path parities plus
one for every local `tau` edge traversed by its oriented orbit. -/
theorem oldCircuitParity_eq_path_sum
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (site : ProperAlternatingSiteWitness G sigma first second)
    (root : CyclePosition sigma site) :
    oldCircuitParity hG sigma hSigma site root =
      (∑ position :
          {position // position ∈ CircuitPartition.orientedOrbit
            (orderedSiteReturnParityPairing hG sigma hSigma site).toPairing
            (orderedSiteTauPairing sigma site) root},
        ((GoertzelV24ResidualReturnArc.orderedReturnPath
          hG sigma hSigma site position).length : ZMod 2)) +
      (CircuitPartition.orientedOrbit
        (orderedSiteReturnParityPairing hG sigma hSigma site).toPairing
        (orderedSiteTauPairing sigma site) root).card := by
  rw [oldCircuitParity, CircuitPartition.circuitParity_eq]
  congr 1
  unfold CircuitPartition.orientedLabelSum
  refine Fintype.sum_congr _ _ ?_
  intro position
  exact orderedSiteReturnParityPairing_label
    hG sigma hSigma site position

/-- The new circuit has the identical path-sum formula with the local
`sigma` pairing in place of `tau`. -/
theorem newCircuitParity_eq_path_sum
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (site : ProperAlternatingSiteWitness G sigma first second)
    (root : CyclePosition sigma site) :
    newCircuitParity hG sigma hSigma site root =
      (∑ position :
          {position // position ∈ CircuitPartition.orientedOrbit
            (orderedSiteReturnParityPairing hG sigma hSigma site).toPairing
            (orderedSiteSigmaPairing sigma site) root},
        ((GoertzelV24ResidualReturnArc.orderedReturnPath
          hG sigma hSigma site position).length : ZMod 2)) +
      (CircuitPartition.orientedOrbit
        (orderedSiteReturnParityPairing hG sigma hSigma site).toPairing
        (orderedSiteSigmaPairing sigma site) root).card := by
  rw [newCircuitParity, CircuitPartition.circuitParity_eq]
  congr 1
  unfold CircuitPartition.orientedLabelSum
  refine Fintype.sum_congr _ _ ?_
  intro position
  exact orderedSiteReturnParityPairing_label
    hG sigma hSigma site position

/-- Old circuit parity is independent of the orientation selected by a
return-path endpoint. -/
theorem oldCircuitParity_return_partner
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (site : ProperAlternatingSiteWitness G sigma first second)
    (root : CyclePosition sigma site) :
    oldCircuitParity hG sigma hSigma site
        ((orderedSiteReturnParityPairing hG sigma hSigma site).partner root) =
      oldCircuitParity hG sigma hSigma site root :=
  CircuitPartition.circuitParity_partner
    (orderedSiteReturnParityPairing hG sigma hSigma site)
    (orderedSiteTauPairing sigma site) root

/-- New circuit parity has the same orientation independence. -/
theorem newCircuitParity_return_partner
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (site : ProperAlternatingSiteWitness G sigma first second)
    (root : CyclePosition sigma site) :
    newCircuitParity hG sigma hSigma site
        ((orderedSiteReturnParityPairing hG sigma hSigma site).partner root) =
      newCircuitParity hG sigma hSigma site root :=
  CircuitPartition.circuitParity_partner
    (orderedSiteReturnParityPairing hG sigma hSigma site)
    (orderedSiteSigmaPairing sigma site) root

end

end ResidualCircuitParity

end Mettapedia.GraphTheory.FourColor.Compositional
