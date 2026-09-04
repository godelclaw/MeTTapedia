import Mettapedia.GraphTheory.FourColor.Compositional.ResidualReturnPairingChordRole
import Mettapedia.GraphTheory.FourColor.Compositional.AmbientReturnSweepWidth

/-!
# Innermost-chord drainage on a residual return

An innermost chord of the full internal-chord diagram has a simple local
sector property: every other chord entering its open interval must cross it.
The exact face-cut theorem for residual returns then forces that chord to use
the opposite local rotation turn.  The selected chord is also a literal edge
of the reference pairing.

This is the residual-return analogue of the combinatorial core of the
source's sector-drainage argument.  It does not construct the source's named
annular holes, a global Tait colouring, or a hole-free sector.
-/

namespace Mettapedia.GraphTheory.FourColor.Compositional

namespace ResidualReturnInnermostChordDrainage

open AmbientReturnAttachmentSweep
open AmbientReturnSweepWidth
open CubicPathAttachment
open CubicPathChordDiagram
open GoertzelV24OrderedMeshResidualSiteMatching
open GoertzelV24ResidualExchange
open GoertzelV24ResidualReturnCycleOrder
open GoertzelV24ResidualReturnSectorNoncrossing
open GoertzelV24TwoEdgeCutMinimality
open MatchingParity
open Mettapedia.GraphTheory
open PathPrefixBoundary
open ResidualReturnAttachmentMatching
open ResidualReturnPathAttachment
open ResidualReturnSeparatorExitSide
open SimpleGraph
open SimpleGraphDartRotation

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

/-- The source-facing local information carried by an innermost residual
return chord.  Any distinct internal chord entering its interval drains to
the other local rotation turn. -/
structure InnermostChordDrainage
    (rotation : Data G)
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (site : ProperAlternatingSiteWitness G sigma first second)
    (returnChord : OrderedReturnChord
      (orderedSiteReturnPairing hG sigma hSigma site)) where
  chord : OrderedPathChord
    ((orderedChordAmbientPath hG sigma hSigma site returnChord).length + 1)
  chord_mem : chord ∈ internalChords
    (orderedChordAmbientPath hG sigma hSigma site returnChord)
  innermost : InnermostIn chord (internalChords
    (orderedChordAmbientPath hG sigma hSigma site returnChord))
  pairingEdge : (pairingGraph sigma).Adj
    ((orderedChordAmbientPath hG sigma hSigma site returnChord).getVert
      chord.left)
    ((orderedChordAmbientPath hG sigma hSigma site returnChord).getVert
      chord.right)
  touching_chords_drain : ∀ other,
    other ∈ internalChords
      (orderedChordAmbientPath hG sigma hSigma site returnChord) →
    other ≠ chord →
    other.HasEndpointInside chord →
    internalChordTurn rotation hG sigma hSigma site returnChord other ≠
      internalChordTurn rotation hG sigma hSigma site returnChord chord

/-- Every nonempty internal-chord diagram on an ambient residual return has
an innermost chord with the drainage property. -/
theorem exists_innermostChordDrainage
    (rotation : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (site : ProperAlternatingSiteWitness G sigma first second)
    (returnChord : OrderedReturnChord
      (orderedSiteReturnPairing hG sigma hSigma site))
    (closure : PathCycleClosure
      (orderedChordAmbientPath hG sigma hSigma site returnChord))
    (hnonempty : (internalChords
      (orderedChordAmbientPath hG sigma hSigma site returnChord)).Nonempty) :
    Nonempty (InnermostChordDrainage rotation hG sigma hSigma site
      returnChord) := by
  let path := orderedChordAmbientPath hG sigma hSigma site returnChord
  have hpath := orderedChordAmbientPath_isPath hG sigma hSigma site returnChord
  have hregular := regularOfDegreeThree_of_cubicIncidentTriples hG
  obtain ⟨selected, hselected, hinnermost⟩ :=
    exists_innermost_orderedPathChord hnonempty
  have hselectedInternal : IsInternalChord selected :=
    mem_internalChords_iff.mp hselected
  refine ⟨{
    chord := selected
    chord_mem := hselected
    innermost := hinnermost
    pairingEdge := ?_
    touching_chords_drain := ?_ }⟩
  · exact internalChord_partner_leftVertex_eq_rightVertex
      hG sigma hSigma site returnChord selected hselectedInternal
  · intro other hother hne htouches
    have hotherInternal : IsInternalChord other :=
      mem_internalChords_iff.mp hother
    have hdisjoint : PairwiseEndpointDisjoint (internalChords path) :=
      pairwiseEndpointDisjoint_internalChords hpath hregular
    have hcrosses : other.Crosses selected :=
      OrderedPathChord.crosses_of_hasEndpointInside_of_innermost hdisjoint
        hinnermost hselected hother hne htouches
    have hturnNe := attachmentTurn_ne_of_crosses_internalChords
      rotation minimal hG sigma hSigma site returnChord closure
        other selected hotherInternal hselectedInternal hcrosses
    simpa only [internalChordTurn_of_isInternalChord rotation hG sigma hSigma
      site returnChord other hotherInternal,
      internalChordTurn_of_isInternalChord rotation hG sigma hSigma site
        returnChord selected hselectedInternal] using hturnNe

/-- Every non-endpoint-exception position in the open interval cut off by an
innermost chord either leaves the ambient return path or is incident to an
internal chord of the opposite turn. -/
theorem external_or_oppositeTurnChord_of_inside
    (rotation : Data G)
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (site : ProperAlternatingSiteWitness G sigma first second)
    (returnChord : OrderedReturnChord
      (orderedSiteReturnPairing hG sigma hSigma site))
    (drainage : InnermostChordDrainage rotation hG sigma hSigma site
      returnChord)
    (position : AmbientReturnInternalPosition hG sigma hSigma site
      returnChord)
    (hinside : drainage.chord.left < position.coordinate ∧
      position.coordinate < drainage.chord.right)
    (hnotEndpoint : ¬IsEndpointAttachment
      (orderedChordAmbientPath_isPath hG sigma hSigma site returnChord)
      (regularOfDegreeThree_of_cubicIncidentTriples hG) position) :
    IsExternalAttachment
        (orderedChordAmbientPath_isPath hG sigma hSigma site returnChord)
        (regularOfDegreeThree_of_cubicIncidentTriples hG) position ∨
      ∃ other,
        other ∈ internalChords
          (orderedChordAmbientPath hG sigma hSigma site returnChord) ∧
        (position.coordinate = other.left ∨
          position.coordinate = other.right) ∧
        internalChordTurn rotation hG sigma hSigma site returnChord other ≠
          internalChordTurn rotation hG sigma hSigma site returnChord
            drainage.chord := by
  let path := orderedChordAmbientPath hG sigma hSigma site returnChord
  let hpath := orderedChordAmbientPath_isPath hG sigma hSigma site returnChord
  let hregular := regularOfDegreeThree_of_cubicIncidentTriples hG
  rcases external_or_endpoint_or_mem_internalChord hpath hregular position with
    hexternal | hendpoint | ⟨other, hother, hincident⟩
  · exact Or.inl hexternal
  · exact False.elim (hnotEndpoint hendpoint)
  · right
    have hne : other ≠ drainage.chord := by
      intro heq
      subst other
      rcases hincident with hleft | hright
      · have := hinside.1
        rw [hleft] at this
        exact (lt_irrefl _ this)
      · have := hinside.2
        rw [hright] at this
        exact (lt_irrefl _ this)
    have htouches : other.HasEndpointInside drainage.chord := by
      rcases hincident with hleft | hright
      · left
        simpa only [← hleft] using hinside
      · right
        simpa only [← hright] using hinside
    exact ⟨other, hother, hincident,
      drainage.touching_chords_drain other hother hne htouches⟩

/-- Sweep coordinates have already discarded the endpoint-return exceptions.
Consequently, every eligible coordinate inside an innermost chord either has
an external attachment or belongs to an opposite-turn internal chord. -/
theorem external_or_oppositeTurnChord_of_eligible_inside
    (rotation : Data G)
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (site : ProperAlternatingSiteWitness G sigma first second)
    (returnChord : OrderedReturnChord
      (orderedSiteReturnPairing hG sigma hSigma site))
    (drainage : InnermostChordDrainage rotation hG sigma hSigma site
      returnChord)
    (coordinate : Fin
      ((orderedChordAmbientPath hG sigma hSigma site returnChord).length + 1))
    (heligible : coordinate ∈ eligibleAmbientReturnSweepPositions hG sigma
      hSigma site returnChord)
    (hinside : drainage.chord.left < coordinate ∧
      coordinate < drainage.chord.right) :
    (∃ position : AmbientReturnInternalPosition hG sigma hSigma site
        returnChord,
      position.coordinate = coordinate ∧
        IsExternalAttachment
          (orderedChordAmbientPath_isPath hG sigma hSigma site returnChord)
          (regularOfDegreeThree_of_cubicIncidentTriples hG) position) ∨
      ∃ other,
        other ∈ internalChords
          (orderedChordAmbientPath hG sigma hSigma site returnChord) ∧
        (coordinate = other.left ∨ coordinate = other.right) ∧
        internalChordTurn rotation hG sigma hSigma site returnChord other ≠
          internalChordTurn rotation hG sigma hSigma site returnChord
            drainage.chord := by
  rcases Finset.mem_image.mp heligible with
    ⟨position, hposition, hcoordinate⟩
  have hnotEndpoint : ¬IsEndpointAttachment
      (orderedChordAmbientPath_isPath hG sigma hSigma site returnChord)
      (regularOfDegreeThree_of_cubicIncidentTriples hG) position := by
    intro hendpoint
    exact (Finset.mem_sdiff.mp hposition).2
      ((mem_endpointAttachmentPositions_iff
        (orderedChordAmbientPath_isPath hG sigma hSigma site returnChord)
        (regularOfDegreeThree_of_cubicIncidentTriples hG) position).mpr
          hendpoint)
  have hinsidePosition : drainage.chord.left < position.coordinate ∧
      position.coordinate < drainage.chord.right := by
    simpa only [hcoordinate] using hinside
  rcases external_or_oppositeTurnChord_of_inside rotation hG sigma hSigma site
      returnChord drainage position hinsidePosition hnotEndpoint with
    hexternal | ⟨other, hother, hincident, hturn⟩
  · exact Or.inl ⟨position, hcoordinate, hexternal⟩
  · exact Or.inr ⟨other, hother, by
      simpa only [← hcoordinate] using hincident, hturn⟩

/-- Uniform source-facing drainage alternative.  Either one eligible point
inside the selected chord supplies a proof-carrying separator exit, or every
eligible point in that interval is incident to an opposite-turn chord. -/
theorem exists_exitSideReceipt_or_all_eligible_inside_drain
    (rotation : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (site : ProperAlternatingSiteWitness G sigma first second)
    (returnChord : OrderedReturnChord
      (orderedSiteReturnPairing hG sigma hSigma site))
    (drainage : InnermostChordDrainage rotation hG sigma hSigma site
      returnChord) :
    Nonempty (AttachmentExitSideReceipt rotation hG sigma hSigma site
        returnChord) ∨
      ∀ coordinate : Fin
          ((orderedChordAmbientPath hG sigma hSigma site returnChord).length + 1),
        coordinate ∈ eligibleAmbientReturnSweepPositions hG sigma hSigma site
            returnChord →
        drainage.chord.left < coordinate →
        coordinate < drainage.chord.right →
        ∃ other,
          other ∈ internalChords
            (orderedChordAmbientPath hG sigma hSigma site returnChord) ∧
          (coordinate = other.left ∨ coordinate = other.right) ∧
          internalChordTurn rotation hG sigma hSigma site returnChord other ≠
            internalChordTurn rotation hG sigma hSigma site returnChord
              drainage.chord := by
  by_cases hexit : ∃ position : AmbientReturnInternalPosition hG sigma hSigma
      site returnChord,
      position.coordinate ∈ eligibleAmbientReturnSweepPositions hG sigma
        hSigma site returnChord ∧
      drainage.chord.left < position.coordinate ∧
      position.coordinate < drainage.chord.right ∧
      IsExternalAttachment
        (orderedChordAmbientPath_isPath hG sigma hSigma site returnChord)
        (regularOfDegreeThree_of_cubicIncidentTriples hG) position
  · rcases hexit with ⟨position, _heligible, _hleft, _hright, hexternal⟩
    exact Or.inl <| nonempty_attachmentExitSideReceipt_of_external rotation
      minimal hG sigma hSigma site returnChord position hexternal
  · right
    intro coordinate heligible hleft hright
    rcases external_or_oppositeTurnChord_of_eligible_inside rotation hG sigma
        hSigma site returnChord drainage coordinate heligible ⟨hleft, hright⟩ with
      ⟨position, hcoordinate, hexternal⟩ |
        ⟨other, hother, hincident, hturn⟩
    · exact False.elim <| hexit ⟨position, by
        simpa only [hcoordinate] using heligible, by
        simpa only [hcoordinate] using hleft, by
        simpa only [hcoordinate] using hright, hexternal⟩
    · exact ⟨other, hother, hincident, hturn⟩

/-- Eligible sweep coordinates strictly inside the selected innermost chord. -/
def eligibleCoordinatesInside
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (site : ProperAlternatingSiteWitness G sigma first second)
    (returnChord : OrderedReturnChord
      (orderedSiteReturnPairing hG sigma hSigma site))
    (rotation : Data G)
    (drainage : InnermostChordDrainage rotation hG sigma hSigma site
      returnChord) :
    Finset (Fin
      ((orderedChordAmbientPath hG sigma hSigma site returnChord).length + 1)) :=
  (eligibleAmbientReturnSweepPositions hG sigma hSigma site returnChord).filter
    fun coordinate =>
      drainage.chord.left < coordinate ∧ coordinate < drainage.chord.right

/-- Internal chords open at either endpoint of the selected chord. -/
def openChordsAtEnds
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (site : ProperAlternatingSiteWitness G sigma first second)
    (returnChord : OrderedReturnChord
      (orderedSiteReturnPairing hG sigma hSigma site))
    (rotation : Data G)
    (drainage : InnermostChordDrainage rotation hG sigma hSigma site
      returnChord) :
    Finset (OrderedPathChord
      ((orderedChordAmbientPath hG sigma hSigma site returnChord).length + 1)) :=
  openInternalChords
      (orderedChordAmbientPath hG sigma hSigma site returnChord)
      drainage.chord.left ∪
    openInternalChords
      (orderedChordAmbientPath hG sigma hSigma site returnChord)
      drainage.chord.right

/-- If the innermost interval has no separator-exit receipt, each eligible
coordinate in it is an endpoint of a chord open at one of the interval's two
ends. -/
theorem eligibleCoordinatesInside_subset_chordEndpoints_openChordsAtEnds
    (rotation : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (site : ProperAlternatingSiteWitness G sigma first second)
    (returnChord : OrderedReturnChord
      (orderedSiteReturnPairing hG sigma hSigma site))
    (drainage : InnermostChordDrainage rotation hG sigma hSigma site
      returnChord)
    (hnoExit : ¬Nonempty (AttachmentExitSideReceipt rotation hG sigma hSigma
      site returnChord)) :
    eligibleCoordinatesInside hG sigma hSigma site returnChord rotation
        drainage ⊆
      orderedPathChordEndpoints
        (openChordsAtEnds hG sigma hSigma site returnChord rotation
          drainage) := by
  intro coordinate hcoordinate
  have heligible := (Finset.mem_filter.mp hcoordinate).1
  have hinside := (Finset.mem_filter.mp hcoordinate).2
  rcases exists_exitSideReceipt_or_all_eligible_inside_drain rotation minimal
      hG sigma hSigma site returnChord drainage with hexit | hdrain
  · exact False.elim (hnoExit hexit)
  · rcases hdrain coordinate heligible hinside.1 hinside.2 with
      ⟨other, hother, hincident, _hturn⟩
    have hne : other ≠ drainage.chord := by
      intro heq
      subst other
      rcases hincident with hleft | hright
      · have := hinside.1
        rw [hleft] at this
        exact (lt_irrefl _ this)
      · have := hinside.2
        rw [hright] at this
        exact (lt_irrefl _ this)
    have htouches : other.HasEndpointInside drainage.chord := by
      rcases hincident with hleft | hright
      · left
        simpa only [← hleft] using hinside
      · right
        simpa only [← hright] using hinside
    have hcrosses : other.Crosses drainage.chord :=
      OrderedPathChord.crosses_of_hasEndpointInside_of_innermost
        (pairwiseEndpointDisjoint_internalChords
          (orderedChordAmbientPath_isPath hG sigma hSigma site returnChord)
          (regularOfDegreeThree_of_cubicIncidentTriples hG))
        drainage.innermost drainage.chord_mem hother hne htouches
    have hopen := other.open_at_left_or_right_of_crosses hcrosses
    apply mem_orderedPathChordEndpoints_iff.mpr
    refine ⟨other, ?_, hincident⟩
    unfold openChordsAtEnds
    rw [Finset.mem_union]
    rcases hopen with hopen | hopen
    · exact Or.inl (Finset.mem_filter.mpr ⟨hother, hopen⟩)
    · exact Or.inr (Finset.mem_filter.mpr ⟨hother, hopen⟩)

/-- Endpoint counting turns the uniform drainage statement into a finite
bound by the number of chords open at the selected interval's ends. -/
theorem card_eligibleCoordinatesInside_le_two_mul_openChordsAtEnds
    (rotation : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (site : ProperAlternatingSiteWitness G sigma first second)
    (returnChord : OrderedReturnChord
      (orderedSiteReturnPairing hG sigma hSigma site))
    (drainage : InnermostChordDrainage rotation hG sigma hSigma site
      returnChord)
    (hnoExit : ¬Nonempty (AttachmentExitSideReceipt rotation hG sigma hSigma
      site returnChord)) :
    (eligibleCoordinatesInside hG sigma hSigma site returnChord rotation
      drainage).card ≤
        2 * (openChordsAtEnds hG sigma hSigma site returnChord rotation
          drainage).card := by
  exact (Finset.card_le_card
    (eligibleCoordinatesInside_subset_chordEndpoints_openChordsAtEnds rotation
      minimal hG sigma hSigma site returnChord drainage hnoExit)).trans
    (card_orderedPathChordEndpoints_le_two_mul _)

/-- If all four turn-stack depths at the endpoints of the selected chord are
at most `depth`, its sweep-eligible interior contains at most `8 * depth`
coordinates unless a separator-exit receipt exists. -/
theorem card_eligibleCoordinatesInside_le_eight_mul_of_stackBounds
    (rotation : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (site : ProperAlternatingSiteWitness G sigma first second)
    (returnChord : OrderedReturnChord
      (orderedSiteReturnPairing hG sigma hSigma site))
    (closure : PathCycleClosure
      (orderedChordAmbientPath hG sigma hSigma site returnChord))
    (drainage : InnermostChordDrainage rotation hG sigma hSigma site
      returnChord)
    (depth : Nat)
    (hnoExit : ¬Nonempty (AttachmentExitSideReceipt rotation hG sigma hSigma
      site returnChord))
    (hstack : ∀ turn : CubicPathRotation.AttachmentTurn,
      ((turnMatching rotation minimal hG sigma hSigma site returnChord closure
          turn).stackAt drainage.chord.left).length ≤ depth ∧
      ((turnMatching rotation minimal hG sigma hSigma site returnChord closure
          turn).stackAt drainage.chord.right).length ≤ depth) :
    (eligibleCoordinatesInside hG sigma hSigma site returnChord rotation
      drainage).card ≤ 8 * depth := by
  have hcovered :=
    card_eligibleCoordinatesInside_le_two_mul_openChordsAtEnds rotation minimal
      hG sigma hSigma site returnChord drainage hnoExit
  have hopen :
      (openChordsAtEnds hG sigma hSigma site returnChord rotation
        drainage).card ≤
        (openInternalChords
          (orderedChordAmbientPath hG sigma hSigma site returnChord)
          drainage.chord.left).card +
        (openInternalChords
          (orderedChordAmbientPath hG sigma hSigma site returnChord)
          drainage.chord.right).card := by
    exact Finset.card_union_le _ _
  have hleft := card_openInternalChords_eq_stack_lengths rotation minimal hG
    sigma hSigma site returnChord closure drainage.chord.left
  have hright := card_openInternalChords_eq_stack_lengths rotation minimal hG
    sigma hSigma site returnChord closure drainage.chord.right
  have hbackward :=
    hstack CubicPathRotation.AttachmentTurn.backwardToAttachment
  have hforward :=
    hstack CubicPathRotation.AttachmentTurn.forwardToAttachment
  unfold openChordsAtEnds at hcovered hopen
  omega

/-- In the no-exit branch, shallow endpoint stacks bound the actual span of
the selected innermost chord.  The additive five is one interval endpoint
plus the at-most-four path-endpoint attachment exceptions. -/
theorem innermostChord_span_le_eight_mul_depth_add_five_of_stackBounds
    (rotation : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (site : ProperAlternatingSiteWitness G sigma first second)
    (returnChord : OrderedReturnChord
      (orderedSiteReturnPairing hG sigma hSigma site))
    (closure : PathCycleClosure
      (orderedChordAmbientPath hG sigma hSigma site returnChord))
    (drainage : InnermostChordDrainage rotation hG sigma hSigma site
      returnChord)
    (depth : Nat)
    (hnoExit : ¬Nonempty (AttachmentExitSideReceipt rotation hG sigma hSigma
      site returnChord))
    (hstack : ∀ turn : CubicPathRotation.AttachmentTurn,
      ((turnMatching rotation minimal hG sigma hSigma site returnChord closure
          turn).stackAt drainage.chord.left).length ≤ depth ∧
      ((turnMatching rotation minimal hG sigma hSigma site returnChord closure
          turn).stackAt drainage.chord.right).length ≤ depth) :
    drainage.chord.right.val - drainage.chord.left.val ≤ 8 * depth + 5 := by
  have hchord : IsInternalChord drainage.chord :=
    mem_internalChords_iff.mp drainage.chord_mem
  have hspan :=
    Mettapedia.GraphTheory.CubicPathChordDiagram.OrderedPathChord.span_le_card_internalNonendpointCoordinates_inside_add_five
      (orderedChordAmbientPath_isPath hG sigma hSigma site returnChord)
      (regularOfDegreeThree_of_cubicIncidentTriples hG) drainage.chord hchord
  have hbound :=
    card_eligibleCoordinatesInside_le_eight_mul_of_stackBounds rotation minimal
      hG sigma hSigma site returnChord closure drainage depth hnoExit hstack
  change drainage.chord.right.val - drainage.chord.left.val ≤
    (eligibleCoordinatesInside hG sigma hSigma site returnChord rotation
      drainage).card + 5 at hspan
  omega

/-- Consumer-facing quantitative drainage dichotomy: bounded endpoint stacks
give either an exact separator-exit receipt or an `8 * depth + 5` span bound
for the selected innermost chord. -/
theorem exitReceipt_or_innermostChord_span_le_eight_mul_depth_add_five
    (rotation : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (site : ProperAlternatingSiteWitness G sigma first second)
    (returnChord : OrderedReturnChord
      (orderedSiteReturnPairing hG sigma hSigma site))
    (closure : PathCycleClosure
      (orderedChordAmbientPath hG sigma hSigma site returnChord))
    (drainage : InnermostChordDrainage rotation hG sigma hSigma site
      returnChord)
    (depth : Nat)
    (hstack : ∀ turn : CubicPathRotation.AttachmentTurn,
      ((turnMatching rotation minimal hG sigma hSigma site returnChord closure
          turn).stackAt drainage.chord.left).length ≤ depth ∧
      ((turnMatching rotation minimal hG sigma hSigma site returnChord closure
          turn).stackAt drainage.chord.right).length ≤ depth) :
    Nonempty (AttachmentExitSideReceipt rotation hG sigma hSigma site
        returnChord) ∨
      drainage.chord.right.val - drainage.chord.left.val ≤ 8 * depth + 5 := by
  by_cases hexit : Nonempty (AttachmentExitSideReceipt rotation hG sigma
      hSigma site returnChord)
  · exact Or.inl hexit
  · exact Or.inr <|
      innermostChord_span_le_eight_mul_depth_add_five_of_stackBounds rotation
        minimal hG sigma hSigma site returnChord closure drainage depth hexit
        hstack

end

end ResidualReturnInnermostChordDrainage

end Mettapedia.GraphTheory.FourColor.Compositional
