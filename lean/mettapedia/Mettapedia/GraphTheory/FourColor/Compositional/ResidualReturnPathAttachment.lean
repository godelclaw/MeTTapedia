import Mettapedia.GraphTheory.CubicPathChord
import Mettapedia.GraphTheory.CubicPathCycleAttachment
import Mettapedia.GraphTheory.FourColor.CubicPathRotation
import Mettapedia.GraphTheory.FourColor.Compositional.ResidualReturnSweepCyclicCut

/-!
# Third-edge attachments along ambient residual returns

The ambient witness of an ordered residual-return chord is a simple path in
the underlying cubic graph.  This file specializes the generic cubic-path
attachment calculus to that witness.  Every strict internal return position
therefore carries one canonical third edge, classified as either a chord back
to a nonconsecutive return position or an attachment leaving the return path.

No planar side or noncrossing conclusion is asserted here.
-/

namespace Mettapedia.GraphTheory.FourColor.Compositional.ResidualReturnPathAttachment

open CubicPathAttachment
open CubicPathRotation
open GoertzelV24OrderedMeshResidualSiteMatching
open GoertzelV24OrderedMeshResidualSiteFacialBond
open GoertzelV24ResidualReturnCycleOrder
open GoertzelV24ResidualReturnSectorNoncrossing
open MatchingParity
open ResidualReturnComplementaryCycle
open ResidualReturnSweepCyclicCut
open SimpleGraph

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

/-- The route's explicit incident-edge triples imply Mathlib's standard
3-regularity predicate. -/
theorem regularOfDegreeThree_of_cubicIncidentTriples
    (hG : HasCubicIncidentEdgeTriples G) : G.IsRegularOfDegree 3 :=
  fun vertex => by
    rw [← incidentEdgeFinset_card_eq_degree]
    exact incidentEdgeFinset_card_eq_three_of_hasCubicIncidentEdgeTriples hG vertex

/-- Strict internal coordinates of the ambient path witnessing one ordered
residual-return chord. -/
abbrev AmbientReturnInternalPosition
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (site : ProperAlternatingSiteWitness G sigma first second)
    (chord : OrderedReturnChord
      (orderedSiteReturnPairing hG sigma hSigma site)) :=
  InternalPosition (orderedChordAmbientPath hG sigma hSigma site chord)

/-- The ambient return is one arc of its literal simple separator cycle and
the reverse operated-cycle interval is the other.  Either arc may supply the
nontriviality needed by the cycle constructor. -/
def ambientReturnPathCycleClosureOfNontrivial
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (site : ProperAlternatingSiteWitness G sigma first second)
    (chord : OrderedReturnChord
      (orderedSiteReturnPairing hG sigma hSigma site))
    (hnontrivial :
      1 < (orderedChordAmbientPath hG sigma hSigma site chord).length ∨
        1 < chord.right.val - chord.left.val) :
    PathCycleClosure
      (orderedChordAmbientPath hG sigma hSigma site chord) where
  complement := (residualCycleInterval sigma site chord).reverse
  path_not_nil :=
    orderedChordAmbientPath_not_nil hG sigma hSigma site chord
  complement_not_nil := by
    rw [SimpleGraph.Walk.not_nil_iff_lt_length,
      SimpleGraph.Walk.length_reverse,
      residualCycleInterval_length sigma site chord]
    exact Nat.sub_pos_of_lt chord.left_lt_right
  cycle_isCycle := by
    simpa [orderedReturnSeparator] using
      orderedReturnSeparator_isCycle_of_nontrivial
        hG sigma hSigma site chord hnontrivial

/-- Carrier-interval form of the ambient return closure. -/
def ambientReturnPathCycleClosure
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (site : ProperAlternatingSiteWitness G sigma first second)
    (chord : OrderedReturnChord
      (orderedSiteReturnPairing hG sigma hSigma site))
    (hlong : 1 < chord.right.val - chord.left.val) :
    PathCycleClosure
      (orderedChordAmbientPath hG sigma hSigma site chord) :=
  ambientReturnPathCycleClosureOfNontrivial
    hG sigma hSigma site chord (Or.inr hlong)

/-- Long-ambient-path form of the same closure.  This is the form consumed by
the ambient attachment sweep when the paired carrier coordinates happen to
be adjacent. -/
def ambientReturnPathCycleClosureOfLongPath
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (site : ProperAlternatingSiteWitness G sigma first second)
    (chord : OrderedReturnChord
      (orderedSiteReturnPairing hG sigma hSigma site))
    (hlong : 1 <
      (orderedChordAmbientPath hG sigma hSigma site chord).length) :
    PathCycleClosure
      (orderedChordAmbientPath hG sigma hSigma site chord) :=
  ambientReturnPathCycleClosureOfNontrivial
    hG sigma hSigma site chord (Or.inl hlong)

/-- The canonical path-cycle closure of a physical residual return.  In a
simple graph the ambient return and the carrier interval cannot both be one
edge, so no length side condition is required. -/
def ambientReturnPathCycleClosureAutomatic
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (site : ProperAlternatingSiteWitness G sigma first second)
    (chord : OrderedReturnChord
      (orderedSiteReturnPairing hG sigma hSigma site)) :
    PathCycleClosure
      (orderedChordAmbientPath hG sigma hSigma site chord) :=
  ambientReturnPathCycleClosureOfNontrivial hG sigma hSigma site chord <| by
    rcases orderedReturnSeparator_length_alternative
        hG sigma hSigma site chord with hambient | hcarrier
    · exact Or.inl hambient
    · exact Or.inr <| by
        simpa only [residualCycleInterval_length] using hcarrier

/-- The unique neighbour reached by the third edge at an internal ambient
return position. -/
def ambientReturnAttachmentNeighbor
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (site : ProperAlternatingSiteWitness G sigma first second)
    (chord : OrderedReturnChord
      (orderedSiteReturnPairing hG sigma hSigma site))
    (position : AmbientReturnInternalPosition hG sigma hSigma site chord) : V :=
  attachmentNeighbor
    (orderedChordAmbientPath_isPath hG sigma hSigma site chord)
    (regularOfDegreeThree_of_cubicIncidentTriples hG) position

/-- The canonical third edge at an internal ambient return position. -/
def ambientReturnAttachmentEdge
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (site : ProperAlternatingSiteWitness G sigma first second)
    (chord : OrderedReturnChord
      (orderedSiteReturnPairing hG sigma hSigma site))
    (position : AmbientReturnInternalPosition hG sigma hSigma site chord) :
    G.edgeSet :=
  attachmentEdge
    (orderedChordAmbientPath_isPath hG sigma hSigma site chord)
    (regularOfDegreeThree_of_cubicIncidentTriples hG) position

/-- Which oriented path dart is immediately followed by the unique attachment
dart in the ambient vertex rotation. -/
def ambientReturnAttachmentTurn
    (rotation : SimpleGraphDartRotation.Data G)
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (site : ProperAlternatingSiteWitness G sigma first second)
    (chord : OrderedReturnChord
      (orderedSiteReturnPairing hG sigma hSigma site))
    (position : AmbientReturnInternalPosition hG sigma hSigma site chord) :
    AttachmentTurn :=
  attachmentTurn rotation
    (orderedChordAmbientPath_isPath hG sigma hSigma site chord)
    (regularOfDegreeThree_of_cubicIncidentTriples hG) position

/-- The exact three-dart rotation cycle selected by an ambient return's
attachment turn.  This is local rotation syntax only; planar noncrossing is a
separate theorem. -/
theorem ambientReturnAttachmentTurn_rotationCycle
    (rotation : SimpleGraphDartRotation.Data G)
    (hcyclic : rotation.IsVertexwiseCyclic)
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (site : ProperAlternatingSiteWitness G sigma first second)
    (chord : OrderedReturnChord
      (orderedSiteReturnPairing hG sigma hSigma site))
    (position : AmbientReturnInternalPosition hG sigma hSigma site chord) :
    let hpath := orderedChordAmbientPath_isPath hG sigma hSigma site chord
    let hregular := regularOfDegreeThree_of_cubicIncidentTriples hG
    (ambientReturnAttachmentTurn rotation hG sigma hSigma site chord position =
          .backwardToAttachment ∧
        rotation.vertexRotation (backwardDart position) =
          attachmentDart hpath hregular position ∧
        rotation.vertexRotation (attachmentDart hpath hregular position) =
          forwardDart position ∧
        rotation.vertexRotation (forwardDart position) = backwardDart position) ∨
      (ambientReturnAttachmentTurn rotation hG sigma hSigma site chord position =
          .forwardToAttachment ∧
        rotation.vertexRotation (backwardDart position) = forwardDart position ∧
        rotation.vertexRotation (forwardDart position) =
          attachmentDart hpath hregular position ∧
        rotation.vertexRotation (attachmentDart hpath hregular position) =
          backwardDart position) := by
  dsimp only
  let hpath := orderedChordAmbientPath_isPath hG sigma hSigma site chord
  let hregular := regularOfDegreeThree_of_cubicIncidentTriples hG
  rcases attachmentTurn_cases rotation hpath hregular position with
    hbackward | hforward
  · left
    exact ⟨hbackward,
      rotationCycle_of_attachmentTurn_eq_backwardToAttachment
        rotation hcyclic hpath hregular position hbackward⟩
  · right
    exact ⟨hforward,
      rotationCycle_of_attachmentTurn_eq_forwardToAttachment
        rotation hcyclic hpath hregular position hforward⟩

/-- At every internal position of an ambient residual return, the third edge
is either a nonconsecutive chord of that return or an external attachment. -/
theorem ambientReturnChordAttachment_or_externalAttachment
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (site : ProperAlternatingSiteWitness G sigma first second)
    (chord : OrderedReturnChord
      (orderedSiteReturnPairing hG sigma hSigma site))
    (position : AmbientReturnInternalPosition hG sigma hSigma site chord) :
    Nonempty
        (ChordAttachment
          (orderedChordAmbientPath_isPath hG sigma hSigma site chord)
          (regularOfDegreeThree_of_cubicIncidentTriples hG) position) ∨
      IsExternalAttachment
        (orderedChordAmbientPath_isPath hG sigma hSigma site chord)
        (regularOfDegreeThree_of_cubicIncidentTriples hG) position :=
  chordAttachment_or_externalAttachment
    (orderedChordAmbientPath_isPath hG sigma hSigma site chord)
    (regularOfDegreeThree_of_cubicIncidentTriples hG) position

/-- An attachment that leaves an ambient residual-return path either reaches
the complementary carrier arc or genuinely leaves the whole displayed return
separator.  This is the semantic refinement of the raw "external to the
path" horn used by the attachment sweep. -/
theorem ambientReturnExternalAttachment_reachesCarrier_or_leavesSeparator
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
    ambientReturnAttachmentNeighbor hG sigma hSigma site chord position ∈
        site.carrier ∨
      ambientReturnAttachmentNeighbor hG sigma hSigma site chord position ∉
        (orderedReturnSeparator hG sigma hSigma site chord).support := by
  by_cases hcarrierArc :
      ambientReturnAttachmentNeighbor hG sigma hSigma site chord position ∈
        (residualCycleInterval sigma site chord).support
  · exact Or.inl <|
      mem_carrier_of_mem_residualCycleInterval_support
        sigma site chord hcarrierArc
  · right
    unfold orderedReturnSeparator
    rw [SimpleGraph.Walk.mem_support_append_iff]
    push Not
    constructor
    · exact hexternal
    · simpa only [SimpleGraph.Walk.support_reverse, List.mem_reverse] using
        hcarrierArc

/-- A third edge that returns to the same ambient residual path determines
the simple chord boundary cut off by that edge. -/
def ambientReturnChordBoundary
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (site : ProperAlternatingSiteWitness G sigma first second)
    (chord : OrderedReturnChord
      (orderedSiteReturnPairing hG sigma hSigma site))
    (position : AmbientReturnInternalPosition hG sigma hSigma site chord)
    (attachment : ChordAttachment
      (orderedChordAmbientPath_isPath hG sigma hSigma site chord)
      (regularOfDegreeThree_of_cubicIncidentTriples hG) position) :
    SamePathChordBoundary G :=
  attachment.boundary
    (orderedChordAmbientPath_isPath hG sigma hSigma site chord)
    (regularOfDegreeThree_of_cubicIncidentTriples hG) position

/-- The boundary supplied by a returning third edge is a simple cycle. -/
theorem ambientReturnChordBoundary_cycleWalk_isCycle
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (site : ProperAlternatingSiteWitness G sigma first second)
    (chord : OrderedReturnChord
      (orderedSiteReturnPairing hG sigma hSigma site))
    (position : AmbientReturnInternalPosition hG sigma hSigma site chord)
    (attachment : ChordAttachment
      (orderedChordAmbientPath_isPath hG sigma hSigma site chord)
      (regularOfDegreeThree_of_cubicIncidentTriples hG) position) :
    (ambientReturnChordBoundary hG sigma hSigma site chord position
      attachment).cycleWalk.IsCycle :=
  SamePathChordBoundary.cycleWalk_isCycle _

/-- A nested same-shore return whose inner ambient path contains more than
`bound` strict internal positions. -/
def HasNestedAmbientReturnInternalPositionsMoreThan
    (rotation : SimpleGraphDartRotation.Data G)
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (bond : ProperAlternatingSiteFacialBondWitness rotation sigma first second)
    (bound : Nat) : Prop :=
  ∃ outer inner : OrderedReturnChord
      (orderedSiteReturnPairing hG sigma hSigma bond.site),
    orderedReturnShore rotation hG sigma hSigma bond outer.left =
        orderedReturnShore rotation hG sigma hSigma bond inner.left ∧
      outer.left < inner.left ∧ inner.right < outer.right ∧
      bound < Fintype.card
        (AmbientReturnInternalPosition hG sigma hSigma bond.site inner)

/-- A long ambient-return support yields many internal third-edge attachment
positions, losing only the two endpoints. -/
theorem hasNestedAmbientReturnInternalPositionsMoreThan_of_support
    (rotation : SimpleGraphDartRotation.Data G)
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (bond : ProperAlternatingSiteFacialBondWitness rotation sigma first second)
    (bound : Nat)
    (hlong :
      HasNestedAmbientReturnSupportLargerThan rotation hG sigma hSigma bond
        (bound + 2)) :
    HasNestedAmbientReturnInternalPositionsMoreThan
      rotation hG sigma hSigma bond bound := by
  rcases hlong with ⟨outer, inner, hshore, hleft, hright, hcard⟩
  refine ⟨outer, inner, hshore, hleft, hright, ?_⟩
  exact lt_card_internalPosition_of_add_two_lt_support_toFinset_card
    (orderedChordAmbientPath_isPath hG sigma hSigma bond.site inner) hcard

end

end Mettapedia.GraphTheory.FourColor.Compositional.ResidualReturnPathAttachment
