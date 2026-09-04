import Mettapedia.GraphTheory.FourColor.Compositional.CarrierSaturationCyclicCut
import Mettapedia.GraphTheory.FourColor.CyclicCutConnectedShore

/-!
# A long carrier yields an attachment, a strict family, or a connected cut

Choose a cut in the middle of a sufficiently long alternating carrier.  The
boundary-depth alternative either exposes a physical attachment, supplies a
strict family of connected return cuts, or bounds the saturated carrier-prefix
boundary.  In the last case the two carrier margins exceed the cubic-tree
budget, so the saturated prefix is itself a connected cyclic cut.
-/

namespace Mettapedia.GraphTheory.FourColor.Compositional

namespace CarrierConnectedCutAlternative

open CarrierBoundaryDeepAlternative
open CarrierSaturationBoundaryDecomposition
open CarrierSaturationCyclicCut
open GoertzelV24ConnectedShoreLiteralNode
open GoertzelV24OrderedMeshResidualSiteFacialBond
open GoertzelV24ResidualReturnCycleOrder
open GoertzelV24ResidualReturnPairing
open GoertzelV24ResidualReturnSectorNoncrossing
open GoertzelV24SimpleGraphFaceDualConnectedness
open GoertzelV24TwoEdgeCutMinimality
open MatchingParity
open ResidualReturnSeparatorExitSide
open ResidualReturnStrictFamily
open SimpleGraph
open SimpleGraphDartRotation

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

/-- The uniform width obtained when neither return stack is deep. -/
def connectedCarrierCutBound (length : Nat) : Nat := 2 * length + 6

/-- At a carrier cut with two large margins, the bounded-boundary branch of
the depth alternative is already a connected cyclic cut. -/
theorem attachment_or_strictFamily_or_connectedAtWidth
    (rotation : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (bond : ProperAlternatingSiteFacialBondWitness rotation sigma first second)
    (length : Nat)
    (cut : CyclePosition sigma bond.site) (hcut : 0 < cut.val)
    (hprefixLarge : connectedCarrierCutBound length < cut.val + 2)
    (hsuffixLarge : connectedCarrierCutBound length <
      (Fintype.card (CyclePosition sigma bond.site) - cut.val) + 2) :
    (∃ chord : OrderedReturnChord
        (orderedSiteReturnPairing hG sigma hSigma bond.site),
      Nonempty (AttachmentExitSideReceipt rotation hG sigma hSigma
        bond.site chord)) ∨
      HasStrictlyNestedConnectedReturnCutFamily G length ∨
      Nonempty (CyclicEdgeCutRealization.ConnectedAtWidth G
        (connectedCarrierCutBound length)) := by
  rcases attachment_or_strictFamily_or_card_ambientExitDart_le
      rotation minimal hG sigma hSigma bond length cut with
    hreceipt | hfamily | hboundary
  · exact Or.inl hreceipt
  · exact Or.inr (Or.inl hfamily)
  · right
    right
    have hconnected : G.Connected := by
      rw [← rotationPrimalGraph_toRotationSystem_eq G rotation]
      exact minimal.primalConnected
    exact exists_connectedAtWidth_carrierPrefix hconnected hG sigma hSigma
      bond.site cut hcut (connectedCarrierCutBound length) hboundary
      hprefixLarge hsuffixLarge

/-- A carrier longer than twice the bounded-cut budget has a canonical middle
cut to which the preceding alternative applies. -/
theorem attachment_or_strictFamily_or_connectedAtWidth_of_longCarrier
    (rotation : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (bond : ProperAlternatingSiteFacialBondWitness rotation sigma first second)
    (length : Nat)
    (hcarrierLarge : 2 * connectedCarrierCutBound length <
      bond.site.cycle.tail.support.length) :
    (∃ chord : OrderedReturnChord
        (orderedSiteReturnPairing hG sigma hSigma bond.site),
      Nonempty (AttachmentExitSideReceipt rotation hG sigma hSigma
        bond.site chord)) ∨
      HasStrictlyNestedConnectedReturnCutFamily G length ∨
      Nonempty (CyclicEdgeCutRealization.ConnectedAtWidth G
        (connectedCarrierCutBound length)) := by
  let bound := connectedCarrierCutBound length
  have hboundPositive : 0 < bound := by
    simp only [bound, connectedCarrierCutBound]
    omega
  let cut : CyclePosition sigma bond.site :=
    ⟨bound + 1, by
      omega⟩
  have hcut : 0 < cut.val := by
    simp only [cut]
    omega
  have hprefixLarge : bound < cut.val + 2 := by
    simp only [cut]
    omega
  have hsuffixLarge : bound <
      (Fintype.card (CyclePosition sigma bond.site) - cut.val) + 2 := by
    have hcard : Fintype.card (CyclePosition sigma bond.site) =
        bond.site.cycle.tail.support.length := by simp
    rw [hcard]
    simp only [cut]
    omega
  simpa only [bound] using
    attachment_or_strictFamily_or_connectedAtWidth rotation minimal hG sigma
      hSigma bond length cut hcut hprefixLarge hsuffixLarge

/-- Consumer-facing version: the bounded branch already carries the literal
connected shore node used by exact-state replacement. -/
theorem attachment_or_strictFamily_or_connectedShoreNode_of_longCarrier
    (rotation : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (bond : ProperAlternatingSiteFacialBondWitness rotation sigma first second)
    (length : Nat)
    (hcarrierLarge : 2 * connectedCarrierCutBound length <
      bond.site.cycle.tail.support.length) :
    (∃ chord : OrderedReturnChord
        (orderedSiteReturnPairing hG sigma hSigma bond.site),
      Nonempty (AttachmentExitSideReceipt rotation hG sigma hSigma
        bond.site chord)) ∨
      HasStrictlyNestedConnectedReturnCutFamily G length ∨
      Nonempty (ConnectedShoreNode (G := G)
        (connectedCarrierCutBound length) (connectedCarrierCutBound length)) := by
  rcases attachment_or_strictFamily_or_connectedAtWidth_of_longCarrier
      rotation minimal hG sigma hSigma bond length hcarrierLarge with
    hreceipt | hfamily | hcut
  · exact Or.inl hreceipt
  · exact Or.inr (Or.inl hfamily)
  · right
    right
    rcases hcut with ⟨cut⟩
    exact ⟨cut.toConnectedShoreNode rotation minimal⟩

end

end CarrierConnectedCutAlternative

end Mettapedia.GraphTheory.FourColor.Compositional
