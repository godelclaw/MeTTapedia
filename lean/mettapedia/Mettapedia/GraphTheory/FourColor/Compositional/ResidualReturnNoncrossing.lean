import Mettapedia.GraphTheory.FourColor.GoertzelV24ResidualReturnSectorNoncrossing

/-!
# Noncrossing residual-return receipts

This file exposes the route-specific residual-return geometry through a small
consumer-facing interface.  A receipt retains the physical formation and shore
data at one alternating site and records the proved consequence needed by the
two-dimensional compositional descent: returns on the same facial shore do not
cross in cyclic order.

The implementation currently delegates to the historical `GoertzelV24` modules.
Downstream compositional arguments can depend on this semantic interface without
depending on the construction history of the local separator proof.
-/

namespace Mettapedia.GraphTheory.FourColor.Compositional.ResidualReturnNoncrossing

open GoertzelV24OrderedInjectiveMeshWidthFactorization
open GoertzelV24OrderedMeshGlobalSites
open GoertzelV24ResidualDefectDescent
open GoertzelV24ResidualReturnCycleOrder
open GoertzelV24ResidualReturnPairing
open GoertzelV24ResidualReturnSectorNoncrossing
open GoertzelV24ResidualReturnShore
open GoertzelV24TwoEdgeCutMinimality
open MatchingParity
open SimpleGraph
open SimpleGraphDartRotation

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

/-- The complete local receipt needed by the two-sector compositional argument.

The `base` field contains the physical facial formation, the canonical return
pairing, reachability through unchanged material, and preservation of facial
shore.  The additional field is the geometric conclusion: two canonical
returns with the same shore label cannot interleave in cyclic order. -/
structure TwoSectorReturnReceipt
    (rotation : Data G) (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (first second : V) where
  base : FacialFormationReturnShoreReceipt rotation hG sigma first second
  sameShore_noncrossing :
    ∀ left right : OrderedReturnChord
        (orderedSiteReturnPairing hG sigma base.sigma_supported base.bond.site),
      orderedReturnShore rotation hG sigma base.sigma_supported base.bond
          left.left =
        orderedReturnShore rotation hG sigma base.sigma_supported base.bond
          right.left →
      ¬left.Crosses right

/-- Upgrade a physical return/shore receipt to the two-sector interface in a
graph-backed least counterexample. -/
def TwoSectorReturnReceipt.ofReturnShoreReceipt
    (rotation : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) {first second : V}
    (receipt : FacialFormationReturnShoreReceipt rotation hG sigma first second) :
    TwoSectorReturnReceipt rotation hG sigma first second where
  base := receipt
  sameShore_noncrossing := by
    intro left right hshore
    exact not_crosses_of_orderedReturnShore_eq_of_minimal
      rotation minimal hG sigma receipt.sigma_supported receipt.bond
        left right hshore

/-- A single residual-defect minimizer supplies a two-sector noncrossing
receipt at every noncentral step of an ordered mesh.  Thus the local geometric
theorem is available in the same global quantifier shape as the pre-existing
formation and return-pairing data. -/
theorem exists_twoSectorReturnReceipt_at_every_globalMeshStep
    {a b : Nat}
    (rotation : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    (ordered : OrderedInjectiveMesh
      (GoertzelV24RotationMultigraphAdapter.toMultigraph
        rotation.toRotationSystem) a b) :
    ∃ hG : HasCubicIncidentEdgeTriples G,
      ∃ sigma : Pairing V,
        sigma.SupportedBy G ∧
        2 ≤ residualDefect G sigma ∧
        ∀ step : GlobalMeshStep rotation ordered,
          sigma.partner (globalFirstVertex rotation ordered step) =
              globalSecondVertex rotation ordered step ∨
            Nonempty (TwoSectorReturnReceipt rotation hG sigma
              (globalFirstVertex rotation ordered step)
              (globalSecondVertex rotation ordered step)) := by
  obtain ⟨hG, sigma, hSigma, hodd, hsites⟩ :=
    exists_exchangeRigid_with_facialFormation_returnPairing_and_shore_at_every_globalMeshStep
      rotation minimal ordered
  refine ⟨hG, sigma, hSigma, hodd, ?_⟩
  intro step
  rcases hsites step with hcentral | hreceipt
  · exact Or.inl hcentral
  · rcases hreceipt with ⟨receipt⟩
    exact Or.inr ⟨TwoSectorReturnReceipt.ofReturnShoreReceipt
      rotation minimal hG sigma receipt⟩

end

end Mettapedia.GraphTheory.FourColor.Compositional.ResidualReturnNoncrossing
