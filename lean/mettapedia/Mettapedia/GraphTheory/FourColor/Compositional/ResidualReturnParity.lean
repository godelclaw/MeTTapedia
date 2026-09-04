import Mettapedia.Combinatorics.Matching.Labeled
import Mettapedia.GraphTheory.FourColor.GoertzelV24ResidualReturnArc

/-!
# Length and parity labels on residual return pairings

The residual return pairing records which two vertices of an alternating site
are joined through the unchanged residual material.  For residual oddness, the
endpoint pairing alone is insufficient: one must also remember the parity of
the path between each paired pair of endpoints.

This file adds that missing datum without changing the physical construction.
Each return edge is labelled by the graph distance between its endpoints in
the common residual graph.  Mapping the label modulo two gives the finite
parity interface used by circuit-partition calculations.
-/

namespace Mettapedia.GraphTheory.FourColor.Compositional

namespace ResidualReturnParity

open GoertzelV24OrderedMeshResidualSiteMatching
open GoertzelV24ResidualReturnCycleOrder
open GoertzelV24ResidualReturnPairing
open GoertzelV24ResidualReturnArc
open MatchingParity
open SimpleGraph

attribute [-instance]
  GoertzelV24RetainedVertexRotationSplice.retainedVertexFintype
  GoertzelV24SeamFaceArcPartition.hitPointFintype

noncomputable section

universe u w

variable {W : Type w} [Fintype W] [DecidableEq W]
  {H : SimpleGraph W} [DecidableRel H.Adj]

/-- The endpoint pairing of a finite degree-`1/2` graph, labelled by the exact
distance through its component. -/
def boundaryReturnDistancePairing
    (boundary : Finset W)
    (hdegree : ∀ vertex : W,
      H.degree vertex = if vertex ∈ boundary then 1 else 2) :
    LabeledPairing (BoundaryVertex boundary) Nat where
  toPairing := boundaryReturnPairing (H := H) boundary hdegree
  label start := H.dist start.1
    ((boundaryReturnPairing (H := H) boundary hdegree).partner start).1
  label_partner start := by
    let pairing := boundaryReturnPairing (H := H) boundary hdegree
    change H.dist (pairing.partner start).1
        (pairing.partner (pairing.partner start)).1 =
      H.dist start.1 (pairing.partner start).1
    calc
      H.dist (pairing.partner start).1
          (pairing.partner (pairing.partner start)).1 =
          H.dist (pairing.partner start).1 start.1 := by
            rw [pairing.partner_partner]
      _ = H.dist start.1 (pairing.partner start).1 := SimpleGraph.dist_comm

@[simp]
theorem boundaryReturnDistancePairing_toPairing
    (boundary : Finset W)
    (hdegree : ∀ vertex : W,
      H.degree vertex = if vertex ∈ boundary then 1 else 2) :
    (boundaryReturnDistancePairing boundary hdegree).toPairing =
      boundaryReturnPairing (H := H) boundary hdegree :=
  rfl

/-- Forget exact return length but retain its parity. -/
def boundaryReturnParityPairing
    (boundary : Finset W)
    (hdegree : ∀ vertex : W,
      H.degree vertex = if vertex ∈ boundary then 1 else 2) :
    LabeledPairing.ParityPairing (BoundaryVertex boundary) :=
  LabeledPairing.mapLabel (A := Nat) (B := ZMod 2)
    (fun length : Nat => (length : ZMod 2))
    (boundaryReturnDistancePairing boundary hdegree)

variable {V : Type u} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

/-- The physical return pairing of one alternating site, labelled by exact
distance through the common residual graph. -/
def siteReturnDistancePairing
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (site : ProperAlternatingSiteWitness G sigma first second) :
    LabeledPairing (BoundaryVertex site.carrier) Nat :=
  boundaryReturnDistancePairing (H := commonResidualGraph G sigma site)
    site.carrier (degree_commonResidualGraph hG sigma hSigma site)

@[simp]
theorem siteReturnDistancePairing_toPairing
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (site : ProperAlternatingSiteWitness G sigma first second) :
    (siteReturnDistancePairing hG sigma hSigma site).toPairing =
      siteReturnPairing hG sigma hSigma site :=
  by
    simp [siteReturnDistancePairing, boundaryReturnDistancePairing,
      siteReturnPairing]

/-- The finite parity-labelled return interface in physical coordinates. -/
def siteReturnParityPairing
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (site : ProperAlternatingSiteWitness G sigma first second) :
    LabeledPairing.ParityPairing (BoundaryVertex site.carrier) :=
  LabeledPairing.mapLabel (A := Nat) (B := ZMod 2)
    (fun length : Nat => (length : ZMod 2))
    (siteReturnDistancePairing hG sigma hSigma site)

/-- The same distance-labelled return interface in the cyclic coordinates of
the operated alternating cycle. -/
def orderedSiteReturnDistancePairing
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (site : ProperAlternatingSiteWitness G sigma first second) :
    LabeledPairing (CyclePosition sigma site) Nat :=
  (siteReturnDistancePairing hG sigma hSigma site).reindex
    (cycleVertexOrder sigma site)

@[simp]
theorem orderedSiteReturnDistancePairing_partner
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (site : ProperAlternatingSiteWitness G sigma first second)
    (position : CyclePosition sigma site) :
    (orderedSiteReturnDistancePairing hG sigma hSigma site).toPairing.partner
        position =
      (orderedSiteReturnPairing hG sigma hSigma site).partner position :=
  by
    simp [orderedSiteReturnDistancePairing, orderedSiteReturnPairing,
      pairingCongr, siteReturnDistancePairing, boundaryReturnDistancePairing,
      siteReturnPairing, LabeledPairing.reindex]

/-- The label in cyclic coordinates is the exact length of the canonical
physical return path. -/
theorem orderedSiteReturnDistancePairing_label
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (site : ProperAlternatingSiteWitness G sigma first second)
    (position : CyclePosition sigma site) :
    (orderedSiteReturnDistancePairing hG sigma hSigma site).label position =
      (orderedReturnPath hG sigma hSigma site position).length := by
  rw [orderedReturnPath_length_eq_dist]
  simp [orderedSiteReturnDistancePairing, siteReturnDistancePairing,
    boundaryReturnDistancePairing, LabeledPairing.reindex,
    siteReturnPairing, cycleVertexOrder_orderedSiteReturnPairing_partner]

/-- The finite parity-labelled return interface in cyclic coordinates. -/
def orderedSiteReturnParityPairing
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (site : ProperAlternatingSiteWitness G sigma first second) :
    LabeledPairing.ParityPairing (CyclePosition sigma site) :=
  LabeledPairing.mapLabel (A := Nat) (B := ZMod 2)
    (fun length : Nat => (length : ZMod 2))
    (orderedSiteReturnDistancePairing hG sigma hSigma site)

end

end ResidualReturnParity

end Mettapedia.GraphTheory.FourColor.Compositional
