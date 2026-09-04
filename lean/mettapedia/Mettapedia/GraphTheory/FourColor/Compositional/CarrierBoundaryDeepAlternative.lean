import Mettapedia.GraphTheory.FourColor.Compositional.OffCarrierReferenceAttachment
import Mettapedia.GraphTheory.FourColor.Compositional.ResidualReturnStrictFamily

/-!
# A uniform carrier-prefix boundary or a strict return-cut family

The boundary of a component-saturated carrier prefix is controlled by the
two residual-return stacks, up to four carrier-local exits.  A stack deeper
than `length + 1` already supplies a strict family of `length` connected
cyclic cuts.  Combining the two facts gives an ambient-independent
alternative: a physical attachment receipt, a strict cut family, or a
boundary of size at most `2 * length + 6`.

The final branch is deliberately stated only as a bound on actual exit
darts.  Turning the saturated prefix into a connected cyclic cut is a
separate geometric step.
-/

namespace Mettapedia.GraphTheory.FourColor.Compositional

namespace CarrierBoundaryDeepAlternative

open CarrierSaturationBoundaryDecomposition
open GoertzelV24OrderedMeshResidualSiteFacialBond
open GoertzelV24ResidualReturnCycleOrder
open GoertzelV24ResidualReturnPairing
open GoertzelV24ResidualReturnSectorNoncrossing
open GoertzelV24TwoEdgeCutMinimality
open MatchingParity
open OffCarrierReferenceAttachment
open ResidualReturnSeparatorExitSide
open ResidualReturnStrictFamily
open ResidualReturnSweep
open SimpleGraph
open SimpleGraphDartRotation

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

/-- At one saturated carrier-prefix cut, either an off-carrier reference exit
has already become a physical separator attachment, one of the two return
stacks supplies the requested strict connected-cut family, or the entire
ambient exit boundary has the uniform bound `2 * length + 6`. -/
theorem attachment_or_strictFamily_or_card_ambientExitDart_le
    (rotation : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (bond : ProperAlternatingSiteFacialBondWitness rotation sigma first second)
    (length : Nat)
    (cut : CyclePosition sigma bond.site) :
    (∃ chord : OrderedReturnChord
        (orderedSiteReturnPairing hG sigma hSigma bond.site),
      Nonempty (AttachmentExitSideReceipt rotation hG sigma hSigma
        bond.site chord)) ∨
      HasStrictlyNestedConnectedReturnCutFamily G length ∨
      Nat.card (AmbientExitDart hG sigma hSigma bond.site cut) ≤
        2 * length + 6 := by
  rcases attachmentReceipt_or_card_ambientExitDart_le_stacks_add_four
      rotation minimal hG sigma hSigma bond cut with hreceipt | hboundary
  · exact Or.inl hreceipt
  · by_cases hleft : length + 1 <
        ((returnShoreMatching rotation minimal hG sigma hSigma bond false).stackAt
          cut).length
    · exact Or.inr (Or.inl
        (hasStrictlyNestedConnectedReturnCutFamily_of_deep_stack
          rotation minimal hG sigma hSigma bond length
            ⟨0, cut, hleft⟩))
    · by_cases hright : length + 1 <
          ((returnShoreMatching rotation minimal hG sigma hSigma bond true).stackAt
            cut).length
      · exact Or.inr (Or.inl
          (hasStrictlyNestedConnectedReturnCutFamily_of_deep_stack
            rotation minimal hG sigma hSigma bond length
              ⟨1, cut, hright⟩))
      · right
        right
        omega

end

end CarrierBoundaryDeepAlternative

end Mettapedia.GraphTheory.FourColor.Compositional
