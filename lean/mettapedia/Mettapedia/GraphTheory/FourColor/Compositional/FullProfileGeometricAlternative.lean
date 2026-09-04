import Mettapedia.GraphTheory.FourColor.Compositional.AmbientReturnFullProfileAlternative
import Mettapedia.GraphTheory.FourColor.Compositional.ExactStateGeometricAlternative
import Mettapedia.GraphTheory.FourColor.Compositional.ResidualReturnCarrierSweep
import Mettapedia.GraphTheory.FourColor.Compositional.ResidualReturnStrictFamily

/-!
# Single-site geometry after complete-profile ambient compression

The componentwise residual-return alternative has two potentially long
coordinates.  The carrier coordinate keeps its existing LIFO compression.
For the ambient coordinate, complete Count profiles now eliminate the
shallow repeated-state branch entirely.  Its only remaining outcomes are a
proof-carrying exit or a prescribed strict family of original path chords.
-/

namespace Mettapedia.GraphTheory.FourColor.Compositional

namespace FullProfileGeometricAlternative

open AmbientReturnFullProfileAlternative
open CubicPathChordDiagram
open CubicPathRotation
open CyclicEdgeCutRealization
open ExactStateGeometricAlternative
open GoertzelV24ConnectedShoreLiteralNode
open GoertzelV24OrderedMeshResidualSiteFacialBond
open GoertzelV24ResidualReturnCycleOrder
open GoertzelV24ResidualReturnSectorNoncrossing
open GoertzelV24TwoEdgeCutMinimality
open MatchingParity
open PathChordStrictFamily
open ResidualReturnCarrierSweep
open ResidualReturnPathAttachment
open ResidualReturnSeparatorExitSide
open ResidualReturnStrictFamily
open ResidualReturnSweepCyclicCut
open SimpleGraph
open SimpleGraphDartRotation

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

/-- One bound large enough for carrier LIFO compression and complete-profile
compression of the ambient return path. -/
def fullProfileComponentBound (depth spacing : Nat) : Nat :=
  max (residualReturnShallowStateCount depth spacing)
    (fullProfileAmbientThreshold depth)

/-- The ambient coordinate after the shallow branch has been removed. -/
def HasProfileCompressedNestedAmbientAlternative
    (rotation : Data G)
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (bond : ProperAlternatingSiteFacialBondWitness rotation sigma first second)
    (depth : Nat) : Prop :=
  ∃ outer inner : OrderedReturnChord
      (orderedSiteReturnPairing hG sigma hSigma bond.site),
    orderedReturnShore rotation hG sigma hSigma bond outer.left =
        orderedReturnShore rotation hG sigma hSigma bond inner.left ∧
      outer.left < inner.left ∧ inner.right < outer.right ∧
      (Nonempty
          (AttachmentExitSideReceipt rotation hG sigma hSigma bond.site inner) ∨
        ∃ closure : PathCycleClosure
            (orderedChordAmbientPath hG sigma hSigma bond.site inner),
          ∃ turn : AttachmentTurn,
            HasStrictlyNestedChordFamily
              (AmbientReturnAttachmentSweep.turnChords rotation hG sigma hSigma
                bond.site inner turn) (depth + 1))

/-- The full single-site alternative after semantic compression of the
ambient shallow branch. -/
def FullProfileSingleSiteAlternative
    (rotation : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (bond : ProperAlternatingSiteFacialBondWitness rotation sigma first second)
    (depth spacing : Nat) : Prop :=
  Nonempty
      (ConnectedShoreNode (G := G)
        (6 * fullProfileComponentBound depth spacing)
        (6 * fullProfileComponentBound depth spacing)) ∨
    HasProfileCompressedNestedAmbientAlternative rotation hG sigma
      hSigma bond depth ∨
    HasNestedCarrierDeepReturnStack rotation minimal hG sigma hSigma bond depth ∨
    HasNestedCarrierSpacedSweepRepeat rotation minimal hG sigma hSigma bond
      spacing ∨
    HasSpacedResidualReturnSweepRepeat rotation minimal hG sigma hSigma bond
      spacing

/-- A sufficiently long residual site has a bounded connected Count state,
an ambient exit or strict chord family, a deep carrier stack, or one of the
two explicitly retained carrier repeated-state receipts. -/
theorem hasFullProfileGeometricAlternative
    (rotation : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (bond : ProperAlternatingSiteFacialBondWitness rotation sigma first second)
    (depth spacing : Nat)
    (hmany : 2 * (spacing + 1) * (1 + 1) ^ 2 <
      bond.site.cycle.tail.support.length) :
    FullProfileSingleSiteAlternative rotation minimal hG sigma hSigma bond
      depth spacing := by
  let bound := fullProfileComponentBound depth spacing
  rcases
      hasCyclicEdgeCutOfSizeAtMost_or_longAmbientReturn_or_longCarrierInterval_or_spaced
        rotation minimal hG sigma hSigma bond bound spacing hmany with
    hcut | hambient | hcarrier | hrepeated
  · exact Or.inl
      (exists_connectedShoreNode_of_hasCyclicEdgeCutOfSizeAtMost
        rotation minimal (6 * bound) hcut)
  · right
    left
    rcases hambient with ⟨outer, inner, hshore, hleft, hright, hcard⟩
    refine ⟨outer, inner, hshore, hleft, hright, ?_⟩
    have hlong : fullProfileAmbientThreshold depth <
        (orderedChordAmbientPath hG sigma hSigma bond.site inner).support.toFinset.card :=
      lt_of_le_of_lt
        (Nat.le_max_right (residualReturnShallowStateCount depth spacing)
          (fullProfileAmbientThreshold depth)) hcard
    rcases exists_externalAttachment_or_strictlyNestedChordFamily rotation
        minimal hG sigma hSigma bond.site inner depth hlong with
      ⟨position, hexternal⟩ | ⟨closure, turn, hfamily⟩
    · exact Or.inl
        (nonempty_attachmentExitSideReceipt_of_external rotation minimal hG
          sigma hSigma bond.site inner position hexternal)
    · exact Or.inr ⟨closure, turn, hfamily⟩
  · right
    right
    have hcarrier' : HasNestedCarrierIntervalSupportLargerThan rotation hG sigma
        hSigma bond (residualReturnShallowStateCount depth spacing) := by
      rcases hcarrier with ⟨outer, inner, hshore, hleft, hright, hcard⟩
      exact ⟨outer, inner, hshore, hleft, hright,
        lt_of_le_of_lt
          (Nat.le_max_left (residualReturnShallowStateCount depth spacing)
            (fullProfileAmbientThreshold depth)) hcard⟩
    rcases hasNestedCarrierDeepReturnStack_or_spacedSweepRepeat rotation minimal
        hG sigma hSigma bond depth spacing hcarrier' with hdeep | hrepeat
    · exact Or.inl hdeep
    · exact Or.inr (Or.inl hrepeat)
  · exact Or.inr (Or.inr (Or.inr (Or.inr hrepeated)))

/-- The complete-profile alternative with the carrier deep-stack branch
realized as a strict family of connected literal cut shores.  The ambient
branch intentionally remains an exit-or-same-turn-chord-family statement:
turning that chord family into a bounded interface requires the additional
closed-web sector hypotheses from the source route. -/
def FullProfileStrictFamilyAlternative
    (rotation : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (bond : ProperAlternatingSiteFacialBondWitness rotation sigma first second)
    (length spacing : Nat) : Prop :=
  Nonempty
      (ConnectedShoreNode (G := G)
        (6 * fullProfileComponentBound (length + 1) spacing)
        (6 * fullProfileComponentBound (length + 1) spacing)) ∨
    HasProfileCompressedNestedAmbientAlternative rotation hG sigma
      hSigma bond (length + 1) ∨
    HasStrictlyNestedConnectedReturnCutFamily G length ∨
    HasNestedCarrierSpacedSweepRepeat rotation minimal hG sigma hSigma bond
      spacing ∨
    HasSpacedResidualReturnSweepRepeat rotation minimal hG sigma hSigma bond
      spacing

/-- Replace the carrier deep-stack outcome by the literal connected-cut
family extracted from the same unchanged physical return data. -/
theorem strictFamily_of_fullProfile
    (rotation : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (bond : ProperAlternatingSiteFacialBondWitness rotation sigma first second)
    (length spacing : Nat)
    (alternative : FullProfileSingleSiteAlternative rotation minimal hG sigma
      hSigma bond (length + 1) spacing) :
    FullProfileStrictFamilyAlternative rotation minimal hG sigma hSigma bond
      length spacing := by
  rcases alternative with
    hstate | hambient | hdeep | hcarrierRepeat | hreturnRepeat
  · exact Or.inl hstate
  · exact Or.inr (Or.inl hambient)
  · exact Or.inr (Or.inr (Or.inl
      (hasStrictlyNestedConnectedReturnCutFamily_of_nestedCarrierDeepReturnStack
        rotation minimal hG sigma hSigma bond length hdeep)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl hcarrierRepeat)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr hreturnRepeat)))

/-- A sufficiently long residual site therefore exposes only literal
connected cuts, an ambient separator exit or same-turn chord family, or one
of the two retained repeated-state receipts. -/
theorem hasFullProfileStrictFamilyAlternative
    (rotation : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (bond : ProperAlternatingSiteFacialBondWitness rotation sigma first second)
    (length spacing : Nat)
    (hmany : 2 * (spacing + 1) * (1 + 1) ^ 2 <
      bond.site.cycle.tail.support.length) :
    FullProfileStrictFamilyAlternative rotation minimal hG sigma hSigma bond
      length spacing :=
  strictFamily_of_fullProfile rotation minimal hG sigma hSigma bond length
    spacing
    (hasFullProfileGeometricAlternative rotation minimal hG sigma hSigma bond
      (length + 1) spacing hmany)

end

end FullProfileGeometricAlternative

end Mettapedia.GraphTheory.FourColor.Compositional
