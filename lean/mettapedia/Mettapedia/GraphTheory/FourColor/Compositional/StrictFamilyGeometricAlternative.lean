import Mettapedia.GraphTheory.FourColor.Compositional.ExactStateGeometricAlternative
import Mettapedia.GraphTheory.FourColor.Compositional.ResidualReturnStrictFamily
import Mettapedia.GraphTheory.FourColor.Compositional.AmbientReturnStrictChordFamily
import Mettapedia.GraphTheory.FourColor.Compositional.ResidualReturnSweepInterface

/-!
# Compressed return sweeps with the deep horn realized as a strict family

The two-coordinate compression theorem has five outcomes.  Its bounded-cut
outcome already carries a connected exact state, while its deep carrier-stack
outcome now carries an arbitrarily long strictly nested family of connected
cut shores.  This file composes those results without weakening or hiding the
three remaining attachment/repetition outcomes.

The common width of the strict family is finite but may still depend on the
ambient graph.  Uniform quantitative control remains a separate high-width
obligation.
-/

namespace Mettapedia.GraphTheory.FourColor.Compositional

namespace StrictFamilyGeometricAlternative

open AmbientReturnAttachmentCompression
open AmbientReturnStrictChordFamily
open ExactStateGeometricAlternative
open GoertzelV24ConnectedShoreLiteralNode
open GoertzelV24OrderedMeshResidualSiteFacialBond
open GoertzelV24TwoEdgeCutMinimality
open MatchingParity
open ResidualReturnCarrierSweep
open ResidualReturnStrictFamily
open ResidualReturnSweepInterface
open SimpleGraph
open SimpleGraphDartRotation

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

/-- The fully compressed single-site alternative after realizing a deep
carrier stack as a strict connected-cut family of the requested length. -/
def FullyCompressedStrictFamilyAlternative
    (rotation : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (bond : ProperAlternatingSiteFacialBondWitness rotation sigma first second)
    (length spacing : Nat) : Prop :=
  Nonempty
      (ConnectedShoreNode (G := G)
        (6 * fullyCompressedComponentBound (length + 1) spacing)
        (6 * fullyCompressedComponentBound (length + 1) spacing)) ∨
    HasNestedAmbientAttachmentSweepAlternative rotation minimal hG sigma hSigma
      bond (length + 1) spacing ∨
    HasStrictlyNestedConnectedReturnCutFamily G length ∨
    HasNestedCarrierSpacedSweepRepeat rotation minimal hG sigma hSigma bond
      spacing ∨
    HasSpacedResidualReturnSweepRepeat rotation minimal hG sigma hSigma bond
      spacing

/-- Replace the carrier-deep branch of an exact-state compressed alternative
by the strict connected-cut family extracted from it. -/
theorem strictFamilyAlternative_of_exactState
    (rotation : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (bond : ProperAlternatingSiteFacialBondWitness rotation sigma first second)
    (length spacing : Nat)
    (alternative : FullyCompressedExactStateAlternative rotation minimal hG
      sigma hSigma bond (length + 1) spacing) :
    FullyCompressedStrictFamilyAlternative rotation minimal hG sigma hSigma
      bond length spacing := by
  rcases alternative with
    hstate | hambient | hdeep | hcarrierRepeat | hreturnRepeat
  · exact Or.inl hstate
  · exact Or.inr (Or.inl hambient)
  · exact Or.inr (Or.inr (Or.inl
      (hasStrictlyNestedConnectedReturnCutFamily_of_nestedCarrierDeepReturnStack
        rotation minimal hG sigma hSigma bond length hdeep)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl hcarrierRepeat)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr hreturnRepeat)))

/-- **Strict-family both-coordinate compression.**  At a sufficiently long
residual site, either a bounded connected exact state already exists, an
arbitrarily requested finite strict connected-cut family exists, or one of
the three explicitly retained attachment/repetition alternatives occurs. -/
theorem hasFullyCompressedStrictFamilyAlternative
    (rotation : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (bond : ProperAlternatingSiteFacialBondWitness rotation sigma first second)
    (length spacing : Nat)
    (hmany : 2 * (spacing + 1) * (1 + 1) ^ 2 <
      bond.site.cycle.tail.support.length) :
    FullyCompressedStrictFamilyAlternative rotation minimal hG sigma hSigma
      bond length spacing :=
  strictFamilyAlternative_of_exactState rotation minimal hG sigma hSigma bond
    length spacing
    (hasFullyCompressedExactStateAlternative rotation minimal hG sigma hSigma
      bond (length + 1) spacing hmany)

/-- The same alternative after the ambient deep-stack subcase has also been
lifted from anonymous stack labels to a strict family of original graph
chords. -/
def FullyRealizedStrictFamilyAlternative
    (rotation : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (bond : ProperAlternatingSiteFacialBondWitness rotation sigma first second)
    (length spacing : Nat) : Prop :=
  Nonempty
      (ConnectedShoreNode (G := G)
        (6 * fullyCompressedComponentBound (length + 1) spacing)
        (6 * fullyCompressedComponentBound (length + 1) spacing)) ∨
    HasRealizedNestedAmbientAttachmentAlternative rotation minimal hG sigma
      hSigma bond length spacing ∨
    HasStrictlyNestedConnectedReturnCutFamily G length ∨
    HasNestedCarrierSpacedSweepRepeat rotation minimal hG sigma hSigma bond
      spacing ∨
    HasSpacedResidualReturnSweepRepeat rotation minimal hG sigma hSigma bond
      spacing

/-- Realize both deep-stack branches of the compressed alternative: carrier
stacks become strict connected-cut families and ambient stacks become strict
families of original path chords. -/
theorem fullyRealized_of_compressedStrictFamily
    (rotation : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (bond : ProperAlternatingSiteFacialBondWitness rotation sigma first second)
    (length spacing : Nat)
    (alternative : FullyCompressedStrictFamilyAlternative rotation minimal hG
      sigma hSigma bond length spacing) :
    FullyRealizedStrictFamilyAlternative rotation minimal hG sigma hSigma bond
      length spacing := by
  rcases alternative with
    hstate | hambient | hfamily | hcarrierRepeat | hreturnRepeat
  · exact Or.inl hstate
  · exact Or.inr (Or.inl
      (realized_of_nestedAmbientAttachmentSweepAlternative rotation minimal hG
        sigma hSigma bond length spacing hambient))
  · exact Or.inr (Or.inr (Or.inl hfamily))
  · exact Or.inr (Or.inr (Or.inr (Or.inl hcarrierRepeat)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr hreturnRepeat)))

/-- **Fully realized qualitative compression.**  Every deep stack in either
coordinate is now returned as a family of original graph objects.  The only
remaining nonphysical data are the two explicitly named repeated sweep-state
horns. -/
theorem hasFullyRealizedStrictFamilyAlternative
    (rotation : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (bond : ProperAlternatingSiteFacialBondWitness rotation sigma first second)
    (length spacing : Nat)
    (hmany : 2 * (spacing + 1) * (1 + 1) ^ 2 <
      bond.site.cycle.tail.support.length) :
    FullyRealizedStrictFamilyAlternative rotation minimal hG sigma hSigma bond
      length spacing :=
  fullyRealized_of_compressedStrictFamily rotation minimal hG sigma hSigma bond
    length spacing
    (hasFullyCompressedStrictFamilyAlternative rotation minimal hG sigma
      hSigma bond length spacing hmany)

/-- The fully realized alternative with both residual-return repetition horns
packaged as ordered open-wire interface receipts. -/
def FullyWiredStrictFamilyAlternative
    (rotation : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (bond : ProperAlternatingSiteFacialBondWitness rotation sigma first second)
    (length spacing : Nat) : Prop :=
  Nonempty
      (ConnectedShoreNode (G := G)
        (6 * fullyCompressedComponentBound (length + 1) spacing)
        (6 * fullyCompressedComponentBound (length + 1) spacing)) ∨
    HasRealizedNestedAmbientAttachmentAlternative rotation minimal hG sigma
      hSigma bond length spacing ∨
    HasStrictlyNestedConnectedReturnCutFamily G length ∨
    Nonempty (CarrierSpacedResidualReturnInterfaceReceipt rotation minimal hG
      sigma hSigma bond spacing) ∨
    Nonempty (SpacedResidualReturnInterfaceReceipt rotation minimal hG sigma
      hSigma bond spacing)

/-- Add the canonical ordered open-wire equivalences to both residual-return
repetition branches. -/
theorem wired_of_fullyRealizedStrictFamily
    (rotation : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (bond : ProperAlternatingSiteFacialBondWitness rotation sigma first second)
    (length spacing : Nat)
    (alternative : FullyRealizedStrictFamilyAlternative rotation minimal hG
      sigma hSigma bond length spacing) :
    FullyWiredStrictFamilyAlternative rotation minimal hG sigma hSigma bond
      length spacing := by
  rcases alternative with
    hstate | hambient | hfamily | hcarrierRepeat | hreturnRepeat
  · exact Or.inl hstate
  · exact Or.inr (Or.inl hambient)
  · exact Or.inr (Or.inr (Or.inl hfamily))
  · exact Or.inr (Or.inr (Or.inr (Or.inl
      (nonempty_carrierSpacedResidualReturnInterfaceReceipt_of_repeat
        rotation minimal hG sigma hSigma bond spacing hcarrierRepeat))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr
      (nonempty_spacedResidualReturnInterfaceReceipt_of_repeat
        rotation minimal hG sigma hSigma bond spacing hreturnRepeat))))

/-- **Wired qualitative compression.**  Deep states are original graph
families, and repeated residual-return states carry canonical equivalences of
their ordered open-wire interfaces.  Colour/Count agreement across those
equivalences is intentionally not asserted. -/
theorem hasFullyWiredStrictFamilyAlternative
    (rotation : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (bond : ProperAlternatingSiteFacialBondWitness rotation sigma first second)
    (length spacing : Nat)
    (hmany : 2 * (spacing + 1) * (1 + 1) ^ 2 <
      bond.site.cycle.tail.support.length) :
    FullyWiredStrictFamilyAlternative rotation minimal hG sigma hSigma bond
      length spacing :=
  wired_of_fullyRealizedStrictFamily rotation minimal hG sigma hSigma bond
    length spacing
    (hasFullyRealizedStrictFamilyAlternative rotation minimal hG sigma hSigma
      bond length spacing hmany)

end

end StrictFamilyGeometricAlternative

end Mettapedia.GraphTheory.FourColor.Compositional
