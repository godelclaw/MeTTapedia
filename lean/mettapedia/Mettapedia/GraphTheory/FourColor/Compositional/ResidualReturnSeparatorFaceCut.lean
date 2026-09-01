import Mettapedia.GraphTheory.Embedding.FaceCut
import Mettapedia.GraphTheory.FourColor.Compositional.ResidualReturnComplementaryCycle
import Mettapedia.GraphTheory.FourColor.GoertzelV24TwoEdgeCutMinimality

/-!
# Exact face cuts of residual-return separators

Every physical residual return in a graph-backed minimal counterexample closes
with its carrier interval to a simple cycle.  Connected spherical-map duality
therefore supplies an exact binary face cut supported on precisely that
separator.
-/

namespace Mettapedia.GraphTheory.FourColor.Compositional

namespace ResidualReturnSeparatorFaceCut

open GoertzelV24FaceBoundaryLinearAlgebra
open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24OrderedMeshResidualSiteMatching
open GoertzelV24ResidualReturnCycleOrder
open GoertzelV24ResidualReturnSectorNoncrossing
open GoertzelV24TwoEdgeCutMinimality
open GoertzelV24WalkCycleParity
open MatchingParity
open Mettapedia.GraphTheory.Embedding
open ResidualReturnComplementaryCycle
open SimpleGraph
open SimpleGraphDartRotation

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

/-- The canonical exact face cut carried by a physical residual-return
separator.  Nondegeneracy is automatic in a simple graph. -/
theorem exists_exactFaceCut_orderedReturnSeparator
    (rotation : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (site : ProperAlternatingSiteWitness G sigma first second)
    (chord : OrderedReturnChord
      (orderedSiteReturnPairing hG sigma hSigma site)) :
    let separator := orderedReturnSeparator hG sigma hSigma site chord
    ∃ cut : ExactFaceCut rotation.toRotationSystem
        (fun edge : G.edgeSet => edge.1 ∈ separator.edges) F2,
      orbitFaceBoundaryLinearMap rotation.toRotationSystem cut.label =
        walkEdgeParity separator := by
  dsimp only
  let separator := orderedReturnSeparator hG sigma hSigma site chord
  have hseparator : separator.IsCycle := by
    simpa only [separator] using orderedReturnSeparator_isCycle_automatic
      hG sigma hSigma site chord
  have hconnected : G.Connected := by
    rw [←
      GoertzelV24SimpleGraphFaceDualConnectedness.rotationPrimalGraph_toRotationSystem_eq
        G rotation]
    exact minimal.primalConnected
  have hdual := orbitFaceInteriorDual_connected rotation.toRotationSystem
    minimal.spherical.cubic minimal.primalConnected
      minimal.vertexRotationCyclic
  exact exists_exactFaceCut_of_closedTrail rotation minimal.facesTwoSided
    hdual hconnected minimal.spherical separator hseparator.isTrail

end

end ResidualReturnSeparatorFaceCut

end Mettapedia.GraphTheory.FourColor.Compositional
