import Mettapedia.GraphTheory.CubicPathAttachment
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
open GoertzelV24OrderedMeshResidualSiteMatching
open GoertzelV24OrderedMeshResidualSiteFacialBond
open GoertzelV24ResidualReturnCycleOrder
open GoertzelV24ResidualReturnSectorNoncrossing
open MatchingParity
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
