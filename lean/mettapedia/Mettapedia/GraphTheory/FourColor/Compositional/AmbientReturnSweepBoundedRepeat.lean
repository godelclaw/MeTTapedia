import Mettapedia.GraphTheory.FourColor.Compositional.AmbientReturnSweepInterface
import Mettapedia.GraphTheory.FourColor.Compositional.AmbientReturnSweepWidth
import Mettapedia.GraphTheory.FourColor.Compositional.RestrictedNoncrossingSweepBounded

/-!
# Bounded physical interfaces from shallow ambient-return sweeps

The shallow repeated-state branch retains more than an ordered open-wire
equivalence.  Negation of the deep-stack branch bounds both physical prefix
cuts, because the two sweep stacks count precisely the open internal chords.
This file packages that resource bound without claiming that the raw sweep
state is already the full colouring-and-face profile required for splicing.
-/

namespace Mettapedia.GraphTheory.FourColor.Compositional

namespace AmbientReturnSweepBoundedRepeat

open AmbientReturnAttachmentSweep
open AmbientReturnSweepInterface
open AmbientReturnSweepWidth
open CubicPathAttachment
open CubicPathChordDiagram
open GoertzelV24CubicSmallBoundaryCycle
open GoertzelV24NoncrossingSweepLifo
open GoertzelV24OrderedMeshResidualSiteMatching
open GoertzelV24ResidualReturnCycleOrder
open GoertzelV24ResidualReturnSectorNoncrossing
open GoertzelV24TwoEdgeCutMinimality
open MatchingParity
open Mettapedia.GraphTheory
open PathPrefixBoundary
open ResidualReturnPathAttachment
open SimpleGraph
open SimpleGraphDartRotation
open scoped BigOperators

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

/-- A repeated ambient interface together with the shallow bounds and the
no-external-attachment fact which turn its stacks into physical cut bounds. -/
structure BoundedSpacedAmbientReturnInterfaceReceipt
    (rotation : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {firstVertex secondVertex : V}
    (site : ProperAlternatingSiteWitness G sigma firstVertex secondVertex)
    (returnChord : OrderedReturnChord
      (orderedSiteReturnPairing hG sigma hSigma site))
    (closure : PathCycleClosure
      (orderedChordAmbientPath hG sigma hSigma site returnChord))
    (depth spacing : Nat) where
  interfaceReceipt : SpacedAmbientReturnInterfaceReceipt rotation minimal hG
    sigma hSigma site returnChord closure spacing
  noExternal : ∀ position : InternalPosition
      (orderedChordAmbientPath hG sigma hSigma site returnChord),
    ¬IsExternalAttachment
      (orderedChordAmbientPath_isPath hG sigma hSigma site returnChord)
      (regularOfDegreeThree_of_cubicIncidentTriples hG) position
  firstStackBound : ∀ family,
    (((ambientReturnAttachmentSweepData rotation minimal hG sigma hSigma site
      returnChord closure).family family).stackAt
        interfaceReceipt.firstCut).length ≤ depth
  secondStackBound : ∀ family,
    (((ambientReturnAttachmentSweepData rotation minimal hG sigma hSigma site
      returnChord closure).family family).stackAt
        interfaceReceipt.secondCut).length ≤ depth

/-- Every eligible ambient sweep coordinate is positive. -/
theorem positive_of_mem_eligibleAmbientReturnSweepPositions
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {firstVertex secondVertex : V}
    (site : ProperAlternatingSiteWitness G sigma firstVertex secondVertex)
    (returnChord : OrderedReturnChord
      (orderedSiteReturnPairing hG sigma hSigma site))
    (cut : Fin
      ((orderedChordAmbientPath hG sigma hSigma site returnChord).length + 1))
    (hcut : cut ∈ eligibleAmbientReturnSweepPositions hG sigma hSigma site
      returnChord) :
    0 < cut.val := by
  change cut ∈ internalNonendpointCoordinates
    (orderedChordAmbientPath_isPath hG sigma hSigma site returnChord)
    (regularOfDegreeThree_of_cubicIncidentTriples hG) at hcut
  rw [internalNonendpointCoordinates] at hcut
  rcases Finset.mem_image.mp hcut with
    ⟨position, _hposition, hcoordinate⟩
  rw [← hcoordinate]
  exact Nat.pos_of_ne_zero position.index_ne_zero

/-- The first physical prefix cut of a bounded receipt has uniformly bounded
width. -/
theorem BoundedSpacedAmbientReturnInterfaceReceipt.firstBoundaryWidth
    (rotation : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {firstVertex secondVertex : V}
    (site : ProperAlternatingSiteWitness G sigma firstVertex secondVertex)
    (returnChord : OrderedReturnChord
      (orderedSiteReturnPairing hG sigma hSigma site))
    (closure : PathCycleClosure
      (orderedChordAmbientPath hG sigma hSigma site returnChord))
    (depth spacing : Nat)
    (receipt : BoundedSpacedAmbientReturnInterfaceReceipt rotation minimal hG
      sigma hSigma site returnChord closure depth spacing) :
    (crossingEdgeFinset G
      (pathPrefixSide
        (orderedChordAmbientPath hG sigma hSigma site returnChord)
        receipt.interfaceReceipt.firstCut)).card ≤ 7 + 2 * depth := by
  have hcut := positive_of_mem_eligibleAmbientReturnSweepPositions hG sigma
    hSigma site returnChord receipt.interfaceReceipt.firstCut
      receipt.interfaceReceipt.firstEligible
  have hphysical := card_ambientReturnPrefixBoundary_le_stack_lengths rotation
    minimal hG sigma hSigma site returnChord closure receipt.noExternal
      receipt.interfaceReceipt.firstCut hcut
  have hback :
      ((turnMatching rotation minimal hG sigma hSigma site returnChord closure
        .backwardToAttachment).stackAt
          receipt.interfaceReceipt.firstCut).length ≤ depth := by
    simpa [ambientReturnAttachmentSweepData, indexedAttachmentTurn] using
      receipt.firstStackBound (0 : Fin 2)
  have hforward :
      ((turnMatching rotation minimal hG sigma hSigma site returnChord closure
        .forwardToAttachment).stackAt
          receipt.interfaceReceipt.firstCut).length ≤ depth := by
    simpa [ambientReturnAttachmentSweepData, indexedAttachmentTurn] using
      receipt.firstStackBound (1 : Fin 2)
  omega

/-- The second physical prefix cut obeys the same width bound. -/
theorem BoundedSpacedAmbientReturnInterfaceReceipt.secondBoundaryWidth
    (rotation : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {firstVertex secondVertex : V}
    (site : ProperAlternatingSiteWitness G sigma firstVertex secondVertex)
    (returnChord : OrderedReturnChord
      (orderedSiteReturnPairing hG sigma hSigma site))
    (closure : PathCycleClosure
      (orderedChordAmbientPath hG sigma hSigma site returnChord))
    (depth spacing : Nat)
    (receipt : BoundedSpacedAmbientReturnInterfaceReceipt rotation minimal hG
      sigma hSigma site returnChord closure depth spacing) :
    (crossingEdgeFinset G
      (pathPrefixSide
        (orderedChordAmbientPath hG sigma hSigma site returnChord)
        receipt.interfaceReceipt.secondCut)).card ≤ 7 + 2 * depth := by
  have hcut := positive_of_mem_eligibleAmbientReturnSweepPositions hG sigma
    hSigma site returnChord receipt.interfaceReceipt.secondCut
      receipt.interfaceReceipt.secondEligible
  have hphysical := card_ambientReturnPrefixBoundary_le_stack_lengths rotation
    minimal hG sigma hSigma site returnChord closure receipt.noExternal
      receipt.interfaceReceipt.secondCut hcut
  have hback :
      ((turnMatching rotation minimal hG sigma hSigma site returnChord closure
        .backwardToAttachment).stackAt
          receipt.interfaceReceipt.secondCut).length ≤ depth := by
    simpa [ambientReturnAttachmentSweepData, indexedAttachmentTurn] using
      receipt.secondStackBound (0 : Fin 2)
  have hforward :
      ((turnMatching rotation minimal hG sigma hSigma site returnChord closure
        .forwardToAttachment).stackAt
          receipt.interfaceReceipt.secondCut).length ≤ depth := by
    simpa [ambientReturnAttachmentSweepData, indexedAttachmentTurn] using
      receipt.secondStackBound (1 : Fin 2)
  omega

/-- Long ambient returns yield an external escape, a genuinely deep physical
chord family, or a materially spaced repeated ordered interface whose two
actual prefix cuts have width at most `7 + 2 * depth`. -/
theorem exists_externalAttachment_or_deepTurnStack_or_boundedSweepRepeat
    (rotation : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {firstVertex secondVertex : V}
    (site : ProperAlternatingSiteWitness G sigma firstVertex secondVertex)
    (returnChord : OrderedReturnChord
      (orderedSiteReturnPairing hG sigma hSigma site))
    (depth spacing : Nat)
    (hmany : ambientReturnShallowStateCount depth spacing <
      (orderedChordAmbientPath hG sigma hSigma site returnChord).support.toFinset.card) :
    (∃ position : InternalPosition
        (orderedChordAmbientPath hG sigma hSigma site returnChord),
      IsExternalAttachment
        (orderedChordAmbientPath_isPath hG sigma hSigma site returnChord)
        (regularOfDegreeThree_of_cubicIncidentTriples hG) position) ∨
      ∃ closure : PathCycleClosure
          (orderedChordAmbientPath hG sigma hSigma site returnChord),
        (∃ family cut,
          cut ∈ eligibleAmbientReturnSweepPositions hG sigma hSigma site
            returnChord ∧
          depth <
            (((ambientReturnAttachmentSweepData rotation minimal hG sigma hSigma
              site returnChord closure).family family).stackAt cut).length) ∨
        Nonempty (BoundedSpacedAmbientReturnInterfaceReceipt rotation minimal
          hG sigma hSigma site returnChord closure depth spacing) := by
  let path := orderedChordAmbientPath hG sigma hSigma site returnChord
  let hpath := orderedChordAmbientPath_isPath hG sigma hSigma site returnChord
  let hregular := regularOfDegreeThree_of_cubicIncidentTriples hG
  by_cases hexternal : ∃ position : InternalPosition path,
      IsExternalAttachment hpath hregular position
  · exact Or.inl hexternal
  · right
    push Not at hexternal
    have hpathLong : 1 < path.length := by
      have hsupport : path.support.toFinset.card = path.length + 1 := by
        rw [List.toFinset_card_of_nodup hpath.support_nodup,
          path.length_support]
      have hmanyPath : ambientReturnShallowStateCount depth spacing <
          path.support.toFinset.card := by
        simpa only [path] using hmany
      have hlarge : 6 < path.support.toFinset.card := by
        have hbudgetLarge : 6 < ambientReturnShallowStateCount depth spacing := by
          simp [ambientReturnShallowStateCount]
        exact lt_trans hbudgetLarge hmanyPath
      rw [hsupport] at hlarge
      omega
    let closure := ambientReturnPathCycleClosureOfLongPath
      hG sigma hSigma site returnChord hpathLong
    refine ⟨closure, ?_⟩
    let positions := eligibleAmbientReturnSweepPositions hG sigma hSigma site
      returnChord
    let data := ambientReturnAttachmentSweepData rotation minimal hG sigma hSigma
      site returnChord closure
    have hlower : path.support.toFinset.card - 6 ≤ positions.card := by
      simpa only [path, positions] using
        support_card_sub_six_le_eligibleAmbientReturnSweepPositions_card
          hG sigma hSigma site returnChord
    have hstateCount :
        (spacing + 1) * (depth + 1) ^ 2 < positions.card := by
      have hsupport : 6 + (spacing + 1) * (depth + 1) ^ 2 <
          path.support.toFinset.card := by
        simpa only [ambientReturnShallowStateCount, path] using hmany
      omega
    have hmanyStates :
        Fintype.card Unit * (spacing + 1) *
            (∑ d : Fin (depth + 1), Fintype.card Unit ^ (d : Nat)) ^ 2 <
          positions.card := by
      simpa using hstateCount
    rcases
        _root_.Mettapedia.GraphTheory.FourColor.Compositional.RestrictedNoncrossingSweepBounded.SweepData.exists_deep_family_on_or_spaced_eq_rawState_with_bounds
            data depth spacing positions hmanyStates with
      hdeep |
        ⟨first, second, hfirst, hsecond, horder, hspacing, heq,
          hfirstBound, hsecondBound⟩
    · exact Or.inl (by simpa only [data, positions] using hdeep)
    · right
      have hfirstEndpoint : IsInternalChordEndpoint path first := by
        apply isInternalChordEndpoint_of_mem_internalNonendpointCoordinates
          hpath hregular hexternal
        simpa only [positions, eligibleAmbientReturnSweepPositions, path, hpath,
          hregular] using hfirst
      have hsecondEndpoint : IsInternalChordEndpoint path second := by
        apply isInternalChordEndpoint_of_mem_internalNonendpointCoordinates
          hpath hregular hexternal
        simpa only [positions, eligibleAmbientReturnSweepPositions, path, hpath,
          hregular] using hsecond
      refine ⟨⟨⟨first, second, ?_, ?_, horder, hspacing, ?_, ?_, ?_⟩,
        ?_, ?_, ?_⟩⟩
      · simpa only [positions] using hfirst
      · simpa only [positions] using hsecond
      · simpa only [path] using hfirstEndpoint
      · simpa only [path] using hsecondEndpoint
      · simpa only [data] using heq
      · simpa only [path, hpath, hregular] using hexternal
      · simpa only [data] using hfirstBound
      · simpa only [data] using hsecondBound

end

end AmbientReturnSweepBoundedRepeat

end Mettapedia.GraphTheory.FourColor.Compositional
