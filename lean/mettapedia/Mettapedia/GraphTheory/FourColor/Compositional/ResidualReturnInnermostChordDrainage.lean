import Mettapedia.GraphTheory.FourColor.Compositional.ResidualReturnPairingChordRole

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
open CubicPathChordDiagram
open GoertzelV24OrderedMeshResidualSiteMatching
open GoertzelV24ResidualExchange
open GoertzelV24ResidualReturnCycleOrder
open GoertzelV24ResidualReturnSectorNoncrossing
open GoertzelV24TwoEdgeCutMinimality
open MatchingParity
open ResidualReturnAttachmentMatching
open ResidualReturnPathAttachment
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

end

end ResidualReturnInnermostChordDrainage

end Mettapedia.GraphTheory.FourColor.Compositional
