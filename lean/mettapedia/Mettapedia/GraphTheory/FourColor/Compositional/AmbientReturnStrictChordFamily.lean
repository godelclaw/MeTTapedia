import Mettapedia.GraphTheory.FourColor.Compositional.AmbientReturnAttachmentCompression
import Mettapedia.GraphTheory.FourColor.Compositional.AmbientReturnSweepInterface
import Mettapedia.GraphTheory.FourColor.Compositional.PathChordStrictFamily

/-!
# Physical chord families inside long ambient residual returns

The ambient-attachment compression theorem records a deep LIFO stack using
anonymous `Unit` labels.  This file crosses the representation boundary back
to the actual graph: every arc in that stack comes from an internal chord of
the ambient residual-return path, and a deep same-turn stack therefore gives
an indexed strictly nested family of those original chords.

External separator exits and materially spaced repeated sweep states remain
explicit alternatives.  No repeated state is treated as a colour-preserving
splice interface here.
-/

namespace Mettapedia.GraphTheory.FourColor.Compositional

namespace AmbientReturnStrictChordFamily

open AmbientReturnAttachmentCompression
open AmbientReturnAttachmentSweep
open AmbientReturnSweepInterface
open CubicPathChordDiagram
open CubicPathRotation
open GoertzelV24OrderedMeshResidualSiteFacialBond
open GoertzelV24ResidualReturnCycleOrder
open GoertzelV24ResidualReturnSectorNoncrossing
open GoertzelV24TwoEdgeCutMinimality
open MatchingParity
open Mettapedia.GraphTheory
open PathChordStrictFamily
open ResidualReturnPathAttachment
open ResidualReturnSeparatorExitSide
open SimpleGraph
open SimpleGraphDartRotation

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

/-- The ambient-attachment alternative after replacing its deep stack by a
strict family of original internal path chords. -/
def HasRealizedNestedAmbientAttachmentAlternative
    (rotation : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (bond : ProperAlternatingSiteFacialBondWitness rotation sigma first second)
    (length spacing : Nat) : Prop :=
  ∃ outer inner : OrderedReturnChord
      (orderedSiteReturnPairing hG sigma hSigma bond.site),
    orderedReturnShore rotation hG sigma hSigma bond outer.left =
        orderedReturnShore rotation hG sigma hSigma bond inner.left ∧
      outer.left < inner.left ∧ inner.right < outer.right ∧
      (Nonempty
          (AttachmentExitSideReceipt rotation hG sigma hSigma bond.site inner) ∨
        ∃ closure : PathCycleClosure
            (orderedChordAmbientPath hG sigma hSigma bond.site inner),
          (∃ turn : AttachmentTurn,
              HasStrictlyNestedChordFamily
                (turnChords rotation hG sigma hSigma bond.site inner turn)
                length) ∨
            Nonempty (SpacedAmbientReturnInterfaceReceipt rotation minimal hG
              sigma hSigma bond.site inner closure spacing))

/-- Realize the deep-stack branch of the compressed ambient-attachment
alternative as original graph chords. -/
theorem realized_of_nestedAmbientAttachmentSweepAlternative
    (rotation : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (bond : ProperAlternatingSiteFacialBondWitness rotation sigma first second)
    (length spacing : Nat)
    (alternative : HasNestedAmbientAttachmentSweepAlternative rotation minimal
      hG sigma hSigma bond (length + 1) spacing) :
    HasRealizedNestedAmbientAttachmentAlternative rotation minimal hG sigma
      hSigma bond length spacing := by
  rcases alternative with
    ⟨outer, inner, hshore, hleft, hright, hexit | hsweep⟩
  · exact ⟨outer, inner, hshore, hleft, hright, Or.inl hexit⟩
  · rcases hsweep with ⟨closure, hdeep | hrepeat⟩
    · rcases hdeep with ⟨familyIndex, cut, _heligible, hdepth⟩
      refine ⟨outer, inner, hshore, hleft, hright, Or.inr
        ⟨closure, Or.inl ⟨indexedAttachmentTurn familyIndex, ?_⟩⟩⟩
      have hlength : length ≤
          (((ambientReturnAttachmentSweepData rotation minimal hG sigma hSigma
            bond.site inner closure).family familyIndex).stackAt cut).length := by
        omega
      have hlength' : length ≤
          ((turnMatching rotation minimal hG sigma hSigma bond.site inner
            closure (indexedAttachmentTurn familyIndex)).stackAt cut).length := by
        simpa only [ambientReturnAttachmentSweepData] using hlength
      exact hasStrictlyNestedChordFamily_of_stackAt_length_le
        (turnChords rotation hG sigma hSigma bond.site inner
          (indexedAttachmentTurn familyIndex))
        (pairwiseEndpointDisjoint_turnChords rotation hG sigma hSigma bond.site
          inner (indexedAttachmentTurn familyIndex))
        (pairwiseNoncrossing_turnChords rotation minimal hG sigma hSigma
          bond.site inner closure (indexedAttachmentTurn familyIndex))
        (fun _ => ()) cut length hlength'
    · rcases hrepeat with
        ⟨firstCut, secondCut, hfirstEligible, hsecondEligible, hordered,
          hseparated, hfirstEndpoint, hsecondEndpoint, heq⟩
      exact ⟨outer, inner, hshore, hleft, hright,
        Or.inr ⟨closure, Or.inr
          (nonempty_spacedAmbientReturnInterfaceReceipt rotation minimal hG
            sigma hSigma bond.site inner closure spacing firstCut secondCut
            hfirstEligible hsecondEligible hordered hseparated hfirstEndpoint
            hsecondEndpoint heq)⟩⟩

end

end AmbientReturnStrictChordFamily

end Mettapedia.GraphTheory.FourColor.Compositional
