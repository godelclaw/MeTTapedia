import Mettapedia.GraphTheory.FourColor.Compositional.ResidualCircuitDefectFormula
import Mettapedia.GraphTheory.FourColor.Compositional.ResidualSiteProvenance

/-!
# Finite residual-circuit monotonicity across an ordered mesh

The exchange-rigid matching selected from a graph-backed least counterexample
is common to every site of an ordered mesh.  At a site where it does not use
the prescribed central edge, the physical provenance construction supplies a
proper alternating carrier.  The exact circuit-defect formula then turns
global exchange-rigidity into a finite local constraint: the number of odd
circuit classes cannot decrease.

This is a consumer-facing bridge for the high-width argument.  It constructs
the matching and the physical site receipt from the least counterexample; it
does not assume cross-site compatibility or a strict decrease.
-/

namespace Mettapedia.GraphTheory.FourColor.Compositional

namespace ResidualMeshCircuitMonotonicity

open GoertzelV24AlternatingMatchingComponent
open GoertzelV24OrderedInjectiveMeshWidthFactorization
open GoertzelV24OrderedMeshGlobalSites
open GoertzelV24OrderedMeshResidualSiteMatching
open GoertzelV24ResidualDefectDescent
open GoertzelV24ResidualOddness
open GoertzelV24RotationMultigraphAdapter
open GoertzelV24TwoEdgeCutMinimality
open MatchingParity
open ResidualCircuitDefectFormula
open ResidualSiteProvenance
open SimpleGraph
open SimpleGraphDartRotation

attribute [-instance]
  GoertzelV24RetainedVertexRotationSplice.retainedVertexFintype
  GoertzelV24SeamFaceArcPartition.hitPointFintype

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]
  {a b : Nat}

/-- The cubic incident-edge witness canonically obtained from a graph-backed
least counterexample. -/
def minimalCounterexampleIncidentTriples
    (rotation : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation) :
    HasCubicIncidentEdgeTriples G :=
  hasCubicIncidentEdgeTriples_of_incidentEdgeFinset_card_eq_three
    (incidentEdgeFinset_card_eq_three rotation minimal)

/-- One physical residual-defect minimizer works across the whole ordered
mesh.  At every noncentral site its old odd circuit-class count is at most its
new count. -/
theorem exists_pairing_with_oddCircuitMonotonicity_at_every_globalMeshStep
    (rotation : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    (ordered : OrderedInjectiveMesh
      (toMultigraph rotation.toRotationSystem) a b) :
    ∃ sigma : Pairing V,
      ∃ hSigma : sigma.SupportedBy G,
      2 ≤ residualDefect G sigma ∧
      ∀ step : GlobalMeshStep rotation ordered,
        sigma.partner (globalFirstVertex rotation ordered step) =
            globalSecondVertex rotation ordered step ∨
          ∃ receipt : ProvenancedAlternatingSiteReceipt
              rotation minimal ordered sigma step,
            (oldOddCircuitClasses
                (minimalCounterexampleIncidentTriples rotation minimal)
                sigma hSigma receipt.site).ncard ≤
              (newOddCircuitClasses
                (minimalCounterexampleIncidentTriples rotation minimal)
                sigma hSigma receipt.site).ncard := by
  obtain ⟨sigma, hSigma, hodd, hsites⟩ :=
    exists_exchangeRigid_with_provenanced_alternatingSite_at_every_globalMeshStep
      rotation minimal ordered
  refine ⟨sigma, hSigma, hodd, ?_⟩
  intro step
  rcases hsites step with hcentral | hsite
  · exact Or.inl hcentral
  · right
    let receipt := Classical.choice hsite
    refine ⟨receipt, ?_⟩
    exact oldOddCircuitClasses_ncard_le_new
      (minimalCounterexampleIncidentTriples rotation minimal)
      sigma hSigma receipt.site

end

end ResidualMeshCircuitMonotonicity

end Mettapedia.GraphTheory.FourColor.Compositional
