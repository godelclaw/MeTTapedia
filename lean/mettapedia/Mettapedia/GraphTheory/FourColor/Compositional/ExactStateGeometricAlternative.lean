import Mettapedia.GraphTheory.FourColor.CyclicCutConnectedShore
import Mettapedia.GraphTheory.FourColor.Compositional.AmbientReturnAttachmentCompression

/-!
# Exact-state form of the compressed residual-return alternative

The geometric compression theorem exposes a bounded cyclic-cut horn.  The
physical replacement theorem does not consume a bare cut: it consumes a
connected shore together with its literal finite boundary state.

Width-preserving cut saturation closes that representation gap.  In a
graph-backed least counterexample, the bounded-cut horn canonically supplies
a `ConnectedShoreNode` at the same bound.  All other geometric horns are
preserved unchanged.  Thus this file strengthens the *value returned* by the
existing alternative without changing or reproving its geometry.
-/

namespace Mettapedia.GraphTheory.FourColor.Compositional

namespace ExactStateGeometricAlternative

open AmbientReturnAttachmentCompression
open CyclicEdgeCutRealization
open GoertzelV24ConnectedShoreLiteralNode
open GoertzelV24OrderedMeshResidualSiteFacialBond
open GoertzelV24TwoEdgeCutMinimality
open MatchingParity
open ResidualReturnCarrierSweep
open ResidualReturnSeparatorExitSide
open ResidualReturnSweepCyclicCut
open SimpleGraph
open SimpleGraphDartRotation

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

local instance finiteGraphLocallyFinite : G.LocallyFinite := fun vertex =>
  @Subtype.fintype V (Membership.mem (G.neighborSet vertex))
    (inferInstance : DecidablePred (Membership.mem (G.neighborSet vertex)))
    inferInstance

/-- The both-coordinate geometric alternative with its cyclic-cut horn
upgraded to the exact connected shore state consumed by physical
replacement. -/
def FullyCompressedExactStateAlternative
    (rotation : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (bond : ProperAlternatingSiteFacialBondWitness rotation sigma first second)
    (depth spacing : Nat) : Prop :=
  Nonempty
      (ConnectedShoreNode (G := G)
        (6 * fullyCompressedComponentBound depth spacing)
        (6 * fullyCompressedComponentBound depth spacing)) ∨
    HasNestedAmbientAttachmentSweepAlternative rotation minimal hG sigma hSigma
      bond depth spacing ∨
    HasNestedCarrierDeepReturnStack rotation minimal hG sigma hSigma bond depth ∨
    HasNestedCarrierSpacedSweepRepeat rotation minimal hG sigma hSigma bond spacing ∨
    HasSpacedResidualReturnSweepRepeat rotation minimal hG sigma hSigma bond spacing

/-- Replace the bare bounded-cut horn of an already proved compressed
alternative by its saturated connected shore node. -/
theorem exactStateAlternative_of_fullyCompressed
    (rotation : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (bond : ProperAlternatingSiteFacialBondWitness rotation sigma first second)
    (depth spacing : Nat)
    (alternative : FullyCompressedGeometricAlternative rotation minimal hG sigma
      hSigma bond depth spacing) :
    FullyCompressedExactStateAlternative rotation minimal hG sigma hSigma bond
      depth spacing := by
  rcases alternative with hcut | hambient | hdeep | hcarrierRepeat | hreturnRepeat
  · exact Or.inl
      (exists_connectedShoreNode_of_hasCyclicEdgeCutOfSizeAtMost
        rotation minimal (6 * fullyCompressedComponentBound depth spacing) hcut)
  · exact Or.inr (Or.inl hambient)
  · exact Or.inr (Or.inr (Or.inl hdeep))
  · exact Or.inr (Or.inr (Or.inr (Or.inl hcarrierRepeat)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr hreturnRepeat)))

/-- **Exact-state both-coordinate compression.**  A sufficiently long
residual site yields either an actual bounded-width connected shore state or
one of the four already structured attachment/stack/repetition horns. -/
theorem hasFullyCompressedExactStateAlternative
    (rotation : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (bond : ProperAlternatingSiteFacialBondWitness rotation sigma first second)
    (depth spacing : Nat)
    (hmany : 2 * (spacing + 1) * (1 + 1) ^ 2 <
      bond.site.cycle.tail.support.length) :
    FullyCompressedExactStateAlternative rotation minimal hG sigma hSigma bond
      depth spacing :=
  exactStateAlternative_of_fullyCompressed rotation minimal hG sigma hSigma bond
    depth spacing
    (hasFullyCompressedGeometricAlternative rotation minimal hG sigma hSigma bond
      depth spacing hmany)

end

end ExactStateGeometricAlternative

end Mettapedia.GraphTheory.FourColor.Compositional
