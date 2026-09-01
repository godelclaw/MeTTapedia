import Mettapedia.GraphTheory.Embedding.CubicPathCycleAttachment
import Mettapedia.GraphTheory.FourColor.Compositional.ResidualReturnPathAttachment
import Mettapedia.GraphTheory.FourColor.Compositional.ResidualReturnSeparatorFaceCut

/-!
# Face sides of residual-return separator exits

At an internal vertex of a physical residual return, an attachment exterior
to the return path either reaches the complementary carrier arc or leaves the
entire displayed separator.  In the latter case the exact face cut of the
separator and the local cubic rotation determine the attachment's vertex
side.

This is the semantic form of the route's sector-exit datum.  It retains the
actual separator, exact face cut, and rotation turn rather than replacing
them by a route-specific Boolean label.
-/

namespace Mettapedia.GraphTheory.FourColor.Compositional

namespace ResidualReturnSeparatorExitSide

open CubicPathAttachment
open CubicPathRotation
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
open ResidualReturnPathAttachment
open ResidualReturnSeparatorFaceCut
open SimpleGraph
open SimpleGraphDartRotation

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

/-- An exterior third edge on a residual return has one of two exact
geometric meanings.  It either reaches the complementary carrier arc, or an
exact face cut of the whole return separator reads its off-cycle side from
the local rotation turn. -/
theorem exists_exactFaceCut_with_attachment_exit_side
    (rotation : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (site : ProperAlternatingSiteWitness G sigma first second)
    (chord : OrderedReturnChord
      (orderedSiteReturnPairing hG sigma hSigma site))
    (position : AmbientReturnInternalPosition hG sigma hSigma site chord)
    (hexternal : IsExternalAttachment
      (orderedChordAmbientPath_isPath hG sigma hSigma site chord)
      (regularOfDegreeThree_of_cubicIncidentTriples hG) position) :
    let separator := orderedReturnSeparator hG sigma hSigma site chord
    ∃ cut : ExactFaceCut rotation.toRotationSystem
        (fun edge : G.edgeSet => edge.1 ∈ separator.edges) F2,
      orbitFaceBoundaryLinearMap rotation.toRotationSystem cut.label =
          walkEdgeParity separator ∧
        (ambientReturnAttachmentNeighbor hG sigma hSigma site chord position ∈
            site.carrier ∨
          ((ambientReturnAttachmentTurn rotation hG sigma hSigma site chord
                  position = .backwardToAttachment ∧
              ∀ selected : F2,
                cut.filledCycleSide rotation separator selected
                    (ambientReturnAttachmentNeighbor
                      hG sigma hSigma site chord position) ↔
                  cut.label (dartOrbitFace rotation.toRotationSystem
                    (forwardDart position)) = selected) ∨
            (ambientReturnAttachmentTurn rotation hG sigma hSigma site chord
                  position = .forwardToAttachment ∧
              ∀ selected : F2,
                cut.filledCycleSide rotation separator selected
                    (ambientReturnAttachmentNeighbor
                      hG sigma hSigma site chord position) ↔
                  cut.label (dartOrbitFace rotation.toRotationSystem
                    (backwardDart position)) = selected))) := by
  dsimp only
  let separator := orderedReturnSeparator hG sigma hSigma site chord
  rcases exists_exactFaceCut_orderedReturnSeparator rotation minimal hG sigma
      hSigma site chord with
    ⟨cut, hboundary⟩
  refine ⟨cut, hboundary, ?_⟩
  rcases ambientReturnExternalAttachment_reachesCarrier_or_leavesSeparator
      hG sigma hSigma site chord position hexternal with hcarrier | hexit
  · exact Or.inl hcarrier
  · right
    let closure := ambientReturnPathCycleClosureAutomatic
      hG sigma hSigma site chord
    have hcycleExterior : IsCycleExteriorAttachment closure
        (orderedChordAmbientPath_isPath hG sigma hSigma site chord)
        (regularOfDegreeThree_of_cubicIncidentTriples hG) position := by
      change ambientReturnAttachmentNeighbor hG sigma hSigma site chord position ∉
        separator.support
      exact hexit
    rcases attachmentTurn_cases rotation
        (orderedChordAmbientPath_isPath hG sigma hSigma site chord)
        (regularOfDegreeThree_of_cubicIncidentTriples hG) position with
      hbackward | hforward
    · left
      refine ⟨?_, ?_⟩
      · exact hbackward
      · intro selected
        simpa only [separator, closure,
          ambientReturnAttachmentNeighbor,
          ambientReturnPathCycleClosureAutomatic,
          ambientReturnPathCycleClosureOfNontrivial,
          orderedReturnSeparator] using
          (filledCycleSide_attachmentNeighbor_iff_forwardDart_of_backwardTurn
            rotation minimal.vertexRotationCyclic closure
            (orderedChordAmbientPath_isPath hG sigma hSigma site chord)
            (regularOfDegreeThree_of_cubicIncidentTriples hG) position cut
            selected hcycleExterior hbackward)
    · right
      refine ⟨?_, ?_⟩
      · exact hforward
      · intro selected
        simpa only [separator, closure,
          ambientReturnAttachmentNeighbor,
          ambientReturnPathCycleClosureAutomatic,
          ambientReturnPathCycleClosureOfNontrivial,
          orderedReturnSeparator] using
          (filledCycleSide_attachmentNeighbor_iff_backwardDart_of_forwardTurn
            rotation minimal.vertexRotationCyclic closure
            (orderedChordAmbientPath_isPath hG sigma hSigma site chord)
            (regularOfDegreeThree_of_cubicIncidentTriples hG) position cut
            selected hcycleExterior hforward)

end

end ResidualReturnSeparatorExitSide

end Mettapedia.GraphTheory.FourColor.Compositional
