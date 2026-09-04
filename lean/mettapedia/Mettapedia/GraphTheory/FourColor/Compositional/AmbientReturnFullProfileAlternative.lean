import Mettapedia.GraphTheory.FourColor.Compositional.AmbientReturnConnectedCutProfileBound
import Mettapedia.GraphTheory.FourColor.Compositional.PathChordStrictFamily

/-!
# The long ambient-return alternative from complete cut profiles

A sufficiently long ambient residual-return path cannot remain both locally
shallow and internally attached.  In the shallow case, its central prefixes
give more connected cyclic cuts than there are complete phased boundary
profiles, contradicting vertex minimality.  What remains is an external
attachment or a strictly nested family of original path chords.
-/

namespace Mettapedia.GraphTheory.FourColor.Compositional

namespace AmbientReturnFullProfileAlternative

open AmbientReturnAttachmentSweep
open AmbientReturnCentralCutFamily
open AmbientReturnConnectedCutProfileBound
open CubicPathAttachment
open CubicPathChordDiagram
open CubicPathRotation
open GoertzelV24NoncrossingSweepLifo
open GoertzelV24OrderedMeshResidualSiteMatching
open GoertzelV24ResidualReturnCycleOrder
open GoertzelV24ResidualReturnSectorNoncrossing
open GoertzelV24TwoEdgeCutMinimality
open MatchingParity
open Mettapedia.GraphTheory
open PathChordStrictFamily
open ResidualReturnPathAttachment
open SimpleGraph
open SimpleGraphDartRotation

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Exact path-support threshold after paying for the two endpoint margins
and one more central cut than the complete profile carrier contains. -/
def fullProfileAmbientThreshold (depth : Nat) : Nat :=
  6 + (connectedCutProfileStateCount (physicalSweepBound depth) +
    2 * physicalSweepBound depth)

/-- A path beyond the complete-profile threshold has an exterior attachment
or contains `depth + 1` strictly nested original internal chords. -/
theorem exists_externalAttachment_or_strictlyNestedChordFamily
    (rotation : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {firstVertex secondVertex : V}
    (site : ProperAlternatingSiteWitness G sigma firstVertex secondVertex)
    (returnChord : OrderedReturnChord
      (orderedSiteReturnPairing hG sigma hSigma site))
    (depth : Nat)
    (hmany : fullProfileAmbientThreshold depth <
      (orderedChordAmbientPath hG sigma hSigma site returnChord).support.toFinset.card) :
    (∃ position : InternalPosition
        (orderedChordAmbientPath hG sigma hSigma site returnChord),
      IsExternalAttachment
        (orderedChordAmbientPath_isPath hG sigma hSigma site returnChord)
        (regularOfDegreeThree_of_cubicIncidentTriples hG) position) ∨
      ∃ closure : PathCycleClosure
          (orderedChordAmbientPath hG sigma hSigma site returnChord),
        ∃ turn : AttachmentTurn,
          HasStrictlyNestedChordFamily
            (turnChords rotation hG sigma hSigma site returnChord turn)
            (depth + 1) := by
  have hlong : 6 +
        (connectedCutProfileStateCount (physicalSweepBound depth) +
          2 * physicalSweepBound depth) <
      (orderedChordAmbientPath hG sigma hSigma site returnChord).support.toFinset.card := by
    simpa only [fullProfileAmbientThreshold] using hmany
  rcases exists_external_or_deep_or_shallowCentralCutFamily rotation minimal hG
      sigma hSigma site returnChord depth
      (connectedCutProfileStateCount (physicalSweepBound depth)) hlong with
    hexternal | ⟨closure, halternative⟩
  · exact Or.inl hexternal
  · rcases halternative with hdeep | hshallow
    · right
      rcases hdeep with ⟨familyIndex, cut, _hcut, hdepth⟩
      refine ⟨closure, indexedAttachmentTurn familyIndex, ?_⟩
      have hdepth' : depth <
          ((turnMatching rotation minimal hG sigma hSigma site returnChord
            closure (indexedAttachmentTurn familyIndex)).stackAt cut).length := by
        simpa only [ambientReturnAttachmentSweepData] using hdepth
      have hlength : depth + 1 ≤
          ((turnMatching rotation minimal hG sigma hSigma site returnChord
            closure (indexedAttachmentTurn familyIndex)).stackAt cut).length := by
        omega
      exact hasStrictlyNestedChordFamily_of_stackAt_length_le
        (turnChords rotation hG sigma hSigma site returnChord
          (indexedAttachmentTurn familyIndex))
        (pairwiseEndpointDisjoint_turnChords rotation hG sigma hSigma site
          returnChord (indexedAttachmentTurn familyIndex))
        (pairwiseNoncrossing_turnChords rotation minimal hG sigma hSigma site
          returnChord closure (indexedAttachmentTurn familyIndex))
        (fun _ => ()) cut (depth + 1) hlength
    · rcases hshallow with ⟨receipt⟩
      exfalso
      have hupper :=
        ShallowCentralCutFamilyReceipt.card_le_profileStateCount rotation minimal
          hG sigma hSigma site returnChord closure depth
          (connectedCutProfileStateCount (physicalSweepBound depth)) receipt
      exact (Nat.not_lt_of_ge hupper) receipt.many

end

end AmbientReturnFullProfileAlternative

end Mettapedia.GraphTheory.FourColor.Compositional
