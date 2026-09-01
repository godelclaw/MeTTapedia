import Mettapedia.GraphTheory.FourColor.Compositional.AmbientReturnAttachmentSweep
import Mettapedia.GraphTheory.FourColor.Compositional.ResidualReturnCarrierSweep
import Mettapedia.GraphTheory.FourColor.Compositional.ResidualReturnSeparatorExitSide

/-!
# Compressing both coordinates of a physical residual return

The componentwise separator alternative has two potentially long coordinates:
the alternating-carrier interval and the ambient return path.  The carrier
coordinate already has a residual-return LIFO sweep.  The ambient coordinate
now has a second, independent two-stack sweep formed by its cubic third-edge
attachments.

This file combines those constructions.  A raw long-ambient-path horn is
replaced by an explicit external attachment, a deep same-turn chord nest, or a
materially spaced repeated phased attachment state.  Thus no geometrically
long coordinate remains as an unstructured alternative.
-/

namespace Mettapedia.GraphTheory.FourColor.Compositional.AmbientReturnAttachmentCompression

open AmbientReturnAttachmentSweep
open CubicPathAttachment
open CubicPathChordDiagram
open GoertzelV24NoncrossingSweepLifo
open GoertzelV24OrderedMeshResidualSiteFacialBond
open GoertzelV24OrderedMeshResidualSiteMatching
open GoertzelV24ResidualReturnCycleOrder
open GoertzelV24ResidualReturnSectorNoncrossing
open GoertzelV24TwoEdgeCutMinimality
open MatchingParity
open ResidualReturnCarrierSweep
open ResidualReturnPathAttachment
open ResidualReturnSeparatorExitSide
open ResidualReturnSweepCyclicCut
open SimpleGraph
open SimpleGraphDartRotation

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

/-- One nested ambient return together with its fully structured attachment
outcome. -/
def HasNestedAmbientAttachmentSweepAlternative
    (rotation : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (bond : ProperAlternatingSiteFacialBondWitness rotation sigma first second)
    (depth spacing : Nat) : Prop :=
  ∃ outer inner : OrderedReturnChord
      (orderedSiteReturnPairing hG sigma hSigma bond.site),
    orderedReturnShore rotation hG sigma hSigma bond outer.left =
        orderedReturnShore rotation hG sigma hSigma bond inner.left ∧
      outer.left < inner.left ∧ inner.right < outer.right ∧
      (Nonempty
          (AttachmentExitSideReceipt rotation hG sigma hSigma bond.site inner) ∨
        ∃ closure : PathCycleClosure
            (orderedChordAmbientPath hG sigma hSigma bond.site inner),
          (∃ family cut,
            cut ∈ eligibleAmbientReturnSweepPositions hG sigma hSigma
              bond.site inner ∧
            depth <
              (((ambientReturnAttachmentSweepData rotation minimal hG sigma
                hSigma bond.site inner closure).family family).stackAt cut).length) ∨
          ∃ firstCut secondCut : Fin
              ((orderedChordAmbientPath hG sigma hSigma bond.site inner).length + 1),
            firstCut ∈ eligibleAmbientReturnSweepPositions hG sigma hSigma
              bond.site inner ∧
            secondCut ∈ eligibleAmbientReturnSweepPositions hG sigma hSigma
              bond.site inner ∧
            firstCut < secondCut ∧
            spacing + 1 ≤ secondCut.val - firstCut.val ∧
            IsInternalChordEndpoint
              (orderedChordAmbientPath hG sigma hSigma bond.site inner) firstCut ∧
            IsInternalChordEndpoint
              (orderedChordAmbientPath hG sigma hSigma bond.site inner) secondCut ∧
            ((PhasedNoncrossingSweep.SweepData.withPositionPhase
                (ambientReturnAttachmentSweepData rotation minimal hG sigma
                  hSigma bond.site inner closure) spacing).rawState firstCut =
              (PhasedNoncrossingSweep.SweepData.withPositionPhase
                (ambientReturnAttachmentSweepData rotation minimal hG sigma
                  hSigma bond.site inner closure) spacing).rawState secondCut))

/-- A long nested ambient return is therefore never terminal: it supplies the
structured attachment alternative above. -/
theorem hasNestedAmbientAttachmentSweepAlternative
    (rotation : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (bond : ProperAlternatingSiteFacialBondWitness rotation sigma first second)
    (depth spacing : Nat)
    (hlong : HasNestedAmbientReturnSupportLargerThan rotation hG sigma hSigma bond
      (ambientReturnShallowStateCount depth spacing)) :
    HasNestedAmbientAttachmentSweepAlternative rotation minimal hG sigma hSigma
      bond depth spacing := by
  rcases hlong with ⟨outer, inner, hshore, hleft, hright, hcard⟩
  refine ⟨outer, inner, hshore, hleft, hright, ?_⟩
  rcases exists_externalAttachment_or_deepTurnStack_or_spacedSweepRepeat
      rotation minimal hG sigma hSigma bond.site inner depth spacing hcard with
    ⟨position, hexternal⟩ | hsweep
  · exact Or.inl
      (nonempty_attachmentExitSideReceipt_of_external rotation minimal hG sigma
        hSigma bond.site inner position hexternal)
  · exact Or.inr hsweep

/-- One common component bound large enough for both the carrier and ambient
two-stack state spaces. -/
def fullyCompressedComponentBound (depth spacing : Nat) : Nat :=
  max (residualReturnShallowStateCount depth spacing)
    (ambientReturnShallowStateCount depth spacing)

/-- The componentwise geometric alternative after both long-coordinate horns
have been replaced by their finite sweeps. -/
def FullyCompressedGeometricAlternative
    (rotation : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (bond : ProperAlternatingSiteFacialBondWitness rotation sigma first second)
    (depth spacing : Nat) : Prop :=
  HasCyclicEdgeCutOfSizeAtMost G
      (6 * fullyCompressedComponentBound depth spacing) ∨
    HasNestedAmbientAttachmentSweepAlternative rotation minimal hG sigma hSigma
      bond depth spacing ∨
    HasNestedCarrierDeepReturnStack rotation minimal hG sigma hSigma bond depth ∨
    HasNestedCarrierSpacedSweepRepeat rotation minimal hG sigma hSigma bond spacing ∨
    HasSpacedResidualReturnSweepRepeat rotation minimal hG sigma hSigma bond spacing

/-- **Both-coordinate compression theorem.**  At one residual site, the
componentwise separator alternative has no raw long-path branch left: a
bounded cyclic cut, a structured ambient attachment sweep, a deep carrier
stack, or a materially spaced repeated state must occur. -/
theorem hasFullyCompressedGeometricAlternative
    (rotation : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (bond : ProperAlternatingSiteFacialBondWitness rotation sigma first second)
    (depth spacing : Nat)
    (hmany : 2 * (spacing + 1) * (1 + 1) ^ 2 <
      bond.site.cycle.tail.support.length) :
    FullyCompressedGeometricAlternative rotation minimal hG sigma hSigma bond
      depth spacing := by
  let bound := fullyCompressedComponentBound depth spacing
  rcases
      hasCyclicEdgeCutOfSizeAtMost_or_longAmbientReturn_or_longCarrierInterval_or_spaced
        rotation minimal hG sigma hSigma bond bound spacing hmany with
    hcut | hambient | hcarrier | hrepeated
  · exact Or.inl hcut
  · right
    left
    apply hasNestedAmbientAttachmentSweepAlternative rotation minimal hG sigma
      hSigma bond depth spacing
    rcases hambient with ⟨outer, inner, hshore, hleft, hright, hcard⟩
    refine ⟨outer, inner, hshore, hleft, hright, ?_⟩
    exact lt_of_le_of_lt
      (Nat.le_max_right
        (residualReturnShallowStateCount depth spacing)
        (ambientReturnShallowStateCount depth spacing)) hcard
  · right
    right
    rcases hcarrier with ⟨outer, inner, hshore, hleft, hright, hcard⟩
    have hcarrier' : HasNestedCarrierIntervalSupportLargerThan rotation hG sigma
        hSigma bond (residualReturnShallowStateCount depth spacing) :=
      ⟨outer, inner, hshore, hleft, hright,
        lt_of_le_of_lt
          (Nat.le_max_left
            (residualReturnShallowStateCount depth spacing)
            (ambientReturnShallowStateCount depth spacing)) hcard⟩
    rcases hasNestedCarrierDeepReturnStack_or_spacedSweepRepeat
        rotation minimal hG sigma hSigma bond depth spacing hcarrier' with
      hdeep | hrepeat
    · exact Or.inl hdeep
    · exact Or.inr (Or.inl hrepeat)
  · exact Or.inr (Or.inr (Or.inr (Or.inr hrepeated)))

end

end Mettapedia.GraphTheory.FourColor.Compositional.AmbientReturnAttachmentCompression
