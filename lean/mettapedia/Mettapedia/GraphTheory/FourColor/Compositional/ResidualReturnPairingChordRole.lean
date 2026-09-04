import Mettapedia.GraphTheory.FourColor.Compositional.AmbientReturnAttachmentSweep
import Mettapedia.GraphTheory.FourColor.Compositional.ResidualReturnAttachmentMatching

/-!
# Pairing-chord role on residual returns

The path of an ambient residual return runs entirely outside the reference
pairing.  By contrast, every internal chord selected by either local turn
stack is an edge of that pairing.  Thus the two-stack sweep has the local
closed-web role required by the compositional source: path material and
reference-pairing chords are not merely abstract coordinates, but actual
disjoint edge classes in the ambient cubic graph.

This file makes only that local identification.  It does not assert that the
whole graph carries a Tait colouring or that the residual return is an
annular closed web.
-/

namespace Mettapedia.GraphTheory.FourColor.Compositional

namespace ResidualReturnPairingChordRole

open AmbientReturnAttachmentSweep
open CubicPathChordDiagram
open GoertzelV24OrderedMeshResidualSiteMatching
open GoertzelV24ResidualExchange
open GoertzelV24ResidualReturnCycleOrder
open GoertzelV24ResidualReturnSectorNoncrossing
open MatchingParity
open ResidualReturnAttachmentMatching
open ResidualReturnPathAttachment
open SimpleGraph
open SimpleGraphDartRotation

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

/-- An edge traversed by the ambient return path is not an edge of the
reference-pairing graph. -/
theorem ambientReturnPathEdge_not_pairingGraph
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (site : ProperAlternatingSiteWitness G sigma first second)
    (returnChord : OrderedReturnChord
      (orderedSiteReturnPairing hG sigma hSigma site))
    {left right : V}
    (hadj : (orderedChordAmbientPath hG sigma hSigma site returnChord).toSubgraph.Adj
      left right) :
    ¬(pairingGraph sigma).Adj left right := by
  simpa only [pairingGraph_adj] using
    ambientReturnPathEdge_partner_ne hG sigma hSigma site returnChord hadj

/-- Every internal chord in a fixed turn stack is a reference-pairing edge
at its ordered left endpoint. -/
theorem turnChord_partner_leftVertex_eq_rightVertex
    (rotation : Data G)
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (site : ProperAlternatingSiteWitness G sigma first second)
    (returnChord : OrderedReturnChord
      (orderedSiteReturnPairing hG sigma hSigma site))
    (turn : CubicPathRotation.AttachmentTurn)
    (chord : OrderedPathChord
      ((orderedChordAmbientPath hG sigma hSigma site returnChord).length + 1))
    (hmem : chord ∈
      turnChords rotation hG sigma hSigma site returnChord turn) :
    sigma.partner
        ((orderedChordAmbientPath hG sigma hSigma site returnChord).getVert
          chord.left) =
      (orderedChordAmbientPath hG sigma hSigma site returnChord).getVert
        chord.right := by
  exact internalChord_partner_leftVertex_eq_rightVertex
    hG sigma hSigma site returnChord chord
      ((mem_turnChords_iff rotation hG sigma hSigma site returnChord turn chord).mp
        hmem).1

/-- Equivalently, every internal chord in either turn stack is literally an
edge of the reference-pairing graph. -/
theorem turnChord_pairingGraph_adj
    (rotation : Data G)
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (site : ProperAlternatingSiteWitness G sigma first second)
    (returnChord : OrderedReturnChord
      (orderedSiteReturnPairing hG sigma hSigma site))
    (turn : CubicPathRotation.AttachmentTurn)
    (chord : OrderedPathChord
      ((orderedChordAmbientPath hG sigma hSigma site returnChord).length + 1))
    (hmem : chord ∈
      turnChords rotation hG sigma hSigma site returnChord turn) :
    (pairingGraph sigma).Adj
      ((orderedChordAmbientPath hG sigma hSigma site returnChord).getVert
        chord.left)
      ((orderedChordAmbientPath hG sigma hSigma site returnChord).getVert
        chord.right) := by
  exact turnChord_partner_leftVertex_eq_rightVertex rotation hG sigma hSigma
    site returnChord turn chord hmem

end

end ResidualReturnPairingChordRole

end Mettapedia.GraphTheory.FourColor.Compositional
