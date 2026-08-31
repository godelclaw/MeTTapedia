import Mettapedia.GraphTheory.FourColor.Compositional.MeshJunctionAlternatingGeometry
import Mettapedia.GraphTheory.FourColor.Compositional.ResidualReturnSweepCyclicCut
import Mettapedia.GraphTheory.FourColor.Compositional.ResidualReturnCarrierSweep

/-!
# Residual-return sweep alternatives across an ordered mesh

This module lifts the single-site geometric sweep alternative into the global
mesh quantifiers already supplied by the residual-defect minimizer.  At every
noncentral mesh step, one proof-carrying receipt now exposes the same exact
alternatives: a uniformly bounded cyclic cut, a long ambient return, a long
carrier interval, or two materially spaced equal phased sweep states.

The construction is pointwise.  It deliberately does not claim that cuts or
repeated states chosen at neighbouring sites are mutually compatible; that is
the remaining mesh-synchronization problem.
-/

namespace Mettapedia.GraphTheory.FourColor.Compositional.MeshResidualReturnSweep

open GoertzelV24NoncrossingSweepLifo
open GoertzelV24OrderedInjectiveMeshWidthFactorization
open GoertzelV24OrderedMeshGlobalSites
open GoertzelV24ResidualDefectDescent
open GoertzelV24ResidualReturnCycleOrder
open GoertzelV24RotationMultigraphAdapter
open GoertzelV24TwoEdgeCutMinimality
open MatchingParity
open MeshJunctionAlternatingGeometry
open ResidualReturnSweep
open ResidualReturnCarrierSweep
open ResidualReturnSweepCyclicCut
open ResidualSiteGeometry
open SimpleGraph
open SimpleGraphDartRotation

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]
  {a b : Nat}

/-- A provenanced two-sector return receipt, upgraded with the geometric
length alternative at every requested separator bound and material spacing. -/
structure GeometricSweepReceipt
    (rotation : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    (ordered : OrderedInjectiveMesh
      (toMultigraph rotation.toRotationSystem) a b)
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V)
    (step : GlobalMeshStep rotation ordered) where
  base : ProvenancedTwoSectorReturnReceipt
    rotation minimal ordered hG sigma step
  alternative : ∀ componentBound spacing : Nat,
    2 * (spacing + 1) * (1 + 1) ^ 2 <
        base.base.base.bond.site.cycle.tail.support.length →
      HasCyclicEdgeCutOfSizeAtMost G (6 * componentBound) ∨
        HasNestedAmbientReturnSupportLargerThan rotation hG sigma
          base.base.base.sigma_supported base.base.base.bond componentBound ∨
        HasNestedCarrierIntervalSupportLargerThan rotation hG sigma
          base.base.base.sigma_supported base.base.base.bond componentBound ∨
        ∃ firstPosition secondPosition :
            CyclePosition sigma base.base.base.bond.site,
          firstPosition < secondPosition ∧
            spacing + 1 ≤ secondPosition.val - firstPosition.val ∧
            (phasedResidualReturnSweepData rotation minimal hG sigma
                base.base.base.sigma_supported base.base.base.bond spacing).rawState
                firstPosition =
              (phasedResidualReturnSweepData rotation minimal hG sigma
                base.base.base.sigma_supported base.base.base.bond spacing).rawState
                secondPosition

/-- The local cyclic-cut theorem upgrades any provenanced two-sector receipt
without changing its site, pairing, colouring provenance, or facial bond. -/
def GeometricSweepReceipt.ofTwoSector
    (rotation : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    (ordered : OrderedInjectiveMesh
      (toMultigraph rotation.toRotationSystem) a b)
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V)
    (step : GlobalMeshStep rotation ordered)
  (receipt : ProvenancedTwoSectorReturnReceipt
      rotation minimal ordered hG sigma step) :
    GeometricSweepReceipt rotation minimal ordered hG sigma step where
  base := receipt
  alternative := fun componentBound spacing hmany =>
    hasCyclicEdgeCutOfSizeAtMost_or_longAmbientReturn_or_longCarrierInterval_or_spaced
      rotation minimal hG sigma receipt.base.base.sigma_supported
        receipt.base.base.bond componentBound spacing hmany

/-- Every geometric mesh receipt inherits the carrier-compressed alternative:
the long carrier horn becomes a deeper local stack or a local repeated phased
state, leaving only the long ambient-return horn geometrically uncompressed. -/
theorem carrierCompressedAlternative_of_geometricSweepReceipt
    (rotation : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    (ordered : OrderedInjectiveMesh
      (toMultigraph rotation.toRotationSystem) a b)
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V)
    (step : GlobalMeshStep rotation ordered)
    (receipt : GeometricSweepReceipt rotation minimal ordered hG sigma step)
    (depth spacing : Nat)
    (hmany : 2 * (spacing + 1) * (1 + 1) ^ 2 <
      receipt.base.base.base.bond.site.cycle.tail.support.length) :
    CarrierCompressedGeometricAlternative rotation minimal hG sigma
      receipt.base.base.base.sigma_supported receipt.base.base.base.bond
        depth spacing :=
  hasCarrierCompressedGeometricAlternative rotation minimal hG sigma
    receipt.base.base.base.sigma_supported receipt.base.base.base.bond
      depth spacing hmany

/-- One common residual-defect minimizer supplies the geometric sweep
alternative at every noncentral step of an ordered mesh. -/
theorem exists_geometricSweepReceipt_at_every_globalMeshStep
    (rotation : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    (ordered : OrderedInjectiveMesh
      (toMultigraph rotation.toRotationSystem) a b) :
    ∃ hG : HasCubicIncidentEdgeTriples G,
      ∃ sigma : Pairing V,
        sigma.SupportedBy G ∧
        2 ≤ residualDefect G sigma ∧
        ∀ step : GlobalMeshStep rotation ordered,
          sigma.partner (globalFirstVertex rotation ordered step) =
              globalSecondVertex rotation ordered step ∨
            Nonempty (GeometricSweepReceipt
              rotation minimal ordered hG sigma step) := by
  obtain ⟨hG, sigma, hSigma, hdefect, hsites⟩ :=
    exists_provenancedTwoSectorReturnReceipt_at_every_globalMeshStep
      rotation minimal ordered
  refine ⟨hG, sigma, hSigma, hdefect, ?_⟩
  intro step
  rcases hsites step with hcentral | hreceipt
  · exact Or.inl hcentral
  · rcases hreceipt with ⟨receipt⟩
    exact Or.inr ⟨GeometricSweepReceipt.ofTwoSector
      rotation minimal ordered hG sigma step receipt⟩

/-- At every internal row junction, at least one of the two incident arms
carries the complete geometric sweep alternative.  The choice of arm remains
local to the junction; no cross-junction coherence is asserted. -/
theorem exists_minimizer_with_geometricSweep_at_every_internal_row_junction
    (rotation : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    (ordered : OrderedInjectiveMesh
      (toMultigraph rotation.toRotationSystem) a (b + 2)) :
    ∃ hG : HasCubicIncidentEdgeTriples G,
      ∃ sigma : Pairing V,
        sigma.SupportedBy G ∧
        2 ≤ residualDefect G sigma ∧
        ∀ (row : Fin a) (column : Fin b),
          Nonempty (GeometricSweepReceipt rotation minimal ordered hG sigma
            (incomingGlobalStep rotation ordered row column)) ∨
          Nonempty (GeometricSweepReceipt rotation minimal ordered hG sigma
            (outgoingGlobalStep rotation ordered row column)) := by
  obtain ⟨hG, sigma, hSigma, hdefect, hsites⟩ :=
    exists_geometricSweepReceipt_at_every_globalMeshStep
      rotation minimal ordered
  refine ⟨hG, sigma, hSigma, hdefect, ?_⟩
  intro row column
  rcases hsites (incomingGlobalStep rotation ordered row column) with
      hIncomingCentral | hIncomingSweep
  · rcases hsites (outgoingGlobalStep rotation ordered row column) with
        hOutgoingCentral | hOutgoingSweep
    · exact False.elim
        (not_both_arms_central rotation ordered sigma row column
          ⟨hIncomingCentral, hOutgoingCentral⟩)
    · exact Or.inr hOutgoingSweep
  · exact Or.inl hIncomingSweep

end

end Mettapedia.GraphTheory.FourColor.Compositional.MeshResidualReturnSweep
