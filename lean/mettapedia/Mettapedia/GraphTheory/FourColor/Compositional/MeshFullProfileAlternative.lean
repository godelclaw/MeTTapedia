import Mettapedia.GraphTheory.FourColor.Compositional.FullProfileGeometricAlternative
import Mettapedia.GraphTheory.FourColor.Compositional.MeshResidualReturnSweep

/-!
# Complete-profile residual alternatives across an ordered mesh

This module lifts complete-profile ambient compression through the existing
mesh provenance.  It does not reselect a colouring, matching, site, or return
pairing.  Every noncentral global step keeps its original geometric receipt
and gains the stronger single-site alternative in which the shallow ambient
repeat has already been eliminated.
-/

namespace Mettapedia.GraphTheory.FourColor.Compositional

namespace MeshFullProfileAlternative

open FullProfileGeometricAlternative
open GoertzelV24OrderedInjectiveMeshWidthFactorization
open GoertzelV24OrderedMeshGlobalSites
open GoertzelV24ResidualDefectDescent
open GoertzelV24RotationMultigraphAdapter
open GoertzelV24TwoEdgeCutMinimality
open MatchingParity
open MeshJunctionAlternatingGeometry
open MeshResidualReturnSweep
open SimpleGraph
open SimpleGraphDartRotation

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]
  {a b : Nat}

/-- A provenanced mesh-step receipt whose ambient shallow branch has already
been eliminated by complete Count profiles. -/
structure FullProfileSweepReceipt
    (rotation : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    (ordered : OrderedInjectiveMesh
      (toMultigraph rotation.toRotationSystem) a b)
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V)
    (step : GlobalMeshStep rotation ordered) where
  base : GeometricSweepReceipt rotation minimal ordered hG sigma step
  alternative : ∀ depth spacing : Nat,
    2 * (spacing + 1) * (1 + 1) ^ 2 <
        base.base.base.base.bond.site.cycle.tail.support.length →
      FullProfileStrictFamilyAlternative rotation minimal hG sigma
        base.base.base.base.sigma_supported base.base.base.base.bond
        depth spacing

/-- Upgrade a geometric receipt without changing any of its witnesses. -/
def FullProfileSweepReceipt.ofGeometric
    (rotation : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    (ordered : OrderedInjectiveMesh
      (toMultigraph rotation.toRotationSystem) a b)
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V)
    (step : GlobalMeshStep rotation ordered)
    (receipt : GeometricSweepReceipt rotation minimal ordered hG sigma step) :
    FullProfileSweepReceipt rotation minimal ordered hG sigma step where
  base := receipt
  alternative := fun depth spacing hmany =>
    hasFullProfileStrictFamilyAlternative rotation minimal hG sigma
      receipt.base.base.base.sigma_supported receipt.base.base.base.bond
      depth spacing hmany

/-- One common residual-defect minimizer supplies the complete-profile
alternative at every noncentral global mesh step. -/
theorem exists_fullProfileSweepReceipt_at_every_globalMeshStep
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
            Nonempty (FullProfileSweepReceipt
              rotation minimal ordered hG sigma step) := by
  obtain ⟨hG, sigma, hSigma, hdefect, hsteps⟩ :=
    exists_geometricSweepReceipt_at_every_globalMeshStep rotation minimal ordered
  refine ⟨hG, sigma, hSigma, hdefect, ?_⟩
  intro step
  rcases hsteps step with hcentral | hreceipt
  · exact Or.inl hcentral
  · rcases hreceipt with ⟨receipt⟩
    exact Or.inr ⟨FullProfileSweepReceipt.ofGeometric rotation minimal ordered
        hG sigma step receipt⟩

/-- At every internal row junction, at least one incident arm carries the
complete-profile alternative.  The arm choice remains local. -/
theorem exists_minimizer_with_fullProfileSweep_at_every_internal_row_junction
    (rotation : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    (ordered : OrderedInjectiveMesh
      (toMultigraph rotation.toRotationSystem) a (b + 2)) :
    ∃ hG : HasCubicIncidentEdgeTriples G,
      ∃ sigma : Pairing V,
        sigma.SupportedBy G ∧
        2 ≤ residualDefect G sigma ∧
        ∀ (row : Fin a) (column : Fin b),
          Nonempty (FullProfileSweepReceipt rotation minimal ordered hG sigma
            (incomingGlobalStep rotation ordered row column)) ∨
          Nonempty (FullProfileSweepReceipt rotation minimal ordered hG sigma
            (outgoingGlobalStep rotation ordered row column)) := by
  obtain ⟨hG, sigma, hSigma, hdefect, hsteps⟩ :=
    exists_fullProfileSweepReceipt_at_every_globalMeshStep rotation minimal
      ordered
  refine ⟨hG, sigma, hSigma, hdefect, ?_⟩
  intro row column
  rcases hsteps (incomingGlobalStep rotation ordered row column) with
      hIncomingCentral | hIncomingSweep
  · rcases hsteps (outgoingGlobalStep rotation ordered row column) with
        hOutgoingCentral | hOutgoingSweep
    · exact False.elim
        (not_both_arms_central rotation ordered sigma row column
          ⟨hIncomingCentral, hOutgoingCentral⟩)
    · exact Or.inr hOutgoingSweep
  · exact Or.inl hIncomingSweep

end

end MeshFullProfileAlternative

end Mettapedia.GraphTheory.FourColor.Compositional
