import Mettapedia.GraphTheory.FourColor.Compositional.AmbientReturnAttachmentCompression
import Mettapedia.GraphTheory.FourColor.Compositional.AmbientReturnSweepBoundedRepeat
import Mettapedia.GraphTheory.FourColor.Compositional.PathChordStrictFamily

/-!
# The long ambient-return alternative with bounded physical repeat cuts

This is the resource-preserving form of ambient-return compression.  A long
nested ambient return yields an actual separator exit, a strict nested family
of original graph chords, or a repeated ordered interface whose two prefix
edge boundaries have the uniform bound certified in
`AmbientReturnSweepBoundedRepeat`.
-/

namespace Mettapedia.GraphTheory.FourColor.Compositional

namespace AmbientReturnBoundedAlternative

open AmbientReturnAttachmentCompression
open AmbientReturnAttachmentSweep
open AmbientReturnSweepBoundedRepeat
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
open ResidualReturnSweepCyclicCut
open SimpleGraph
open SimpleGraphDartRotation

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

/-- The fully physical, resource-preserving alternatives supplied by one long
nested ambient return. -/
def HasBoundedRealizedNestedAmbientAttachmentAlternative
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
            Nonempty
              (BoundedSpacedAmbientReturnInterfaceReceipt rotation minimal hG
                sigma hSigma bond.site inner closure length spacing))

/-- Replace the graph-dependent long-ambient horn by physical separator,
strict-chord, or uniformly bounded repeated-interface data. -/
theorem hasBoundedRealizedNestedAmbientAttachmentAlternative
    (rotation : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (bond : ProperAlternatingSiteFacialBondWitness rotation sigma first second)
    (length spacing : Nat)
    (hlong : HasNestedAmbientReturnSupportLargerThan rotation hG sigma hSigma bond
      (ambientReturnShallowStateCount length spacing)) :
    HasBoundedRealizedNestedAmbientAttachmentAlternative rotation minimal hG
      sigma hSigma bond length spacing := by
  rcases hlong with ⟨outer, inner, hshore, hleft, hright, hcard⟩
  refine ⟨outer, inner, hshore, hleft, hright, ?_⟩
  rcases
      exists_externalAttachment_or_deepTurnStack_or_boundedSweepRepeat
        rotation minimal hG sigma hSigma bond.site inner length spacing hcard with
    ⟨position, hexternal⟩ | ⟨closure, hdeep | hrepeat⟩
  · exact Or.inl
      (nonempty_attachmentExitSideReceipt_of_external rotation minimal hG sigma
        hSigma bond.site inner position hexternal)
  · rcases hdeep with ⟨familyIndex, cut, _heligible, hdepth⟩
    refine Or.inr ⟨closure, Or.inl
      ⟨indexedAttachmentTurn familyIndex, ?_⟩⟩
    have hlength : length ≤
        ((turnMatching rotation minimal hG sigma hSigma bond.site inner closure
          (indexedAttachmentTurn familyIndex)).stackAt cut).length := by
      simpa only [ambientReturnAttachmentSweepData] using Nat.le_of_lt hdepth
    exact hasStrictlyNestedChordFamily_of_stackAt_length_le
      (turnChords rotation hG sigma hSigma bond.site inner
        (indexedAttachmentTurn familyIndex))
      (pairwiseEndpointDisjoint_turnChords rotation hG sigma hSigma bond.site
        inner (indexedAttachmentTurn familyIndex))
      (pairwiseNoncrossing_turnChords rotation minimal hG sigma hSigma bond.site
        inner closure (indexedAttachmentTurn familyIndex))
      (fun _ => ()) cut length hlength
  · exact Or.inr ⟨closure, Or.inr hrepeat⟩

end

end AmbientReturnBoundedAlternative

end Mettapedia.GraphTheory.FourColor.Compositional
