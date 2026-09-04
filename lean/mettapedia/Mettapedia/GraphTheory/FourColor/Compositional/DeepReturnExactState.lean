import Mettapedia.GraphTheory.FourColor.Compositional.ExactStateGeometricAlternative

/-!
# Exact connected states from deep residual-return stacks

A deep carrier stack is not merely a combinatorial alternative.  At depth
two it contains two strictly nested physical return chords.  Their inner
separator and the complementary cycle give a concrete cyclic edge cut.
Width-preserving saturation then turns that particular cut into connected
complementary shores, retaining the subcut relation to the physical
separator.

The resulting bound is still the size of the chosen separator times the
cubic degree.  Thus this module discharges the *realization* of the deep
horn, while deliberately leaving uniform control of that bound to the global
high-width argument.
-/

namespace Mettapedia.GraphTheory.FourColor.Compositional

namespace DeepReturnExactState

open CyclePushOffCut
open CyclicEdgeCutRealization
open ExactStateGeometricAlternative
open GoertzelV24ConnectedShoreLiteralNode
open GoertzelV24FaceDualConnectedness
open GoertzelV24OrderedMeshResidualSiteFacialBond
open GoertzelV24ResidualReturnCycleOrder
open GoertzelV24ResidualReturnSectorNoncrossing
open GoertzelV24TwoEdgeCutMinimality
open MatchingParity
open Mettapedia.GraphTheory.Embedding
open ResidualReturnCarrierSweep
open ResidualReturnCyclicCut
open ResidualReturnSweep
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

/-- A degree-controlled return cut together with a connected cyclic subcut
at the same explicit separator bound.  The final subset field remembers that
the connected cut was obtained by tightening the physical push-off cut. -/
def HasSaturatedDegreeControlledCyclicReturnCut
    (rotation : Data G)
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (bond : ProperAlternatingSiteFacialBondWitness rotation sigma first second) :
    Prop :=
  ∃ outer inner : OrderedReturnChord
      (orderedSiteReturnPairing hG sigma hSigma bond.site),
    orderedReturnShore rotation hG sigma hSigma bond outer.left =
        orderedReturnShore rotation hG sigma hSigma bond inner.left ∧
      outer.left < inner.left ∧ inner.right < outer.right ∧
      (let separator :=
        orderedReturnSeparator hG sigma hSigma bond.site inner
       ∃ faceCut : ExactFaceCut rotation.toRotationSystem
            (fun edge : G.edgeSet ↦ edge.1 ∈ separator.edges) F2,
         ∃ selected : F2,
           ∃ _rawRealization : CyclicEdgeCutRealization G
               (CyclePushOffCut.edges rotation separator faceCut selected),
             (CyclePushOffCut.edges rotation separator faceCut selected).card ≤
                 separator.support.toFinset.card * 3 ∧
               ∃ connected : ConnectedAtWidth G
                   (separator.support.toFinset.card * 3),
                 connected.edgeCut ⊆
                   CyclePushOffCut.edges rotation separator faceCut selected)

/-- Saturate the concrete cyclic cut carried by a degree-controlled return
receipt, preserving its physical push-off support as provenance. -/
theorem saturated_of_degreeControlled
    (rotation : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (bond : ProperAlternatingSiteFacialBondWitness rotation sigma first second)
    (hcut : HasDegreeControlledCyclicReturnCut rotation hG sigma hSigma bond) :
    HasSaturatedDegreeControlledCyclicReturnCut rotation hG sigma hSigma bond := by
  rcases hcut with ⟨outer, inner, hshore, hleft, hright, hcut⟩
  refine ⟨outer, inner, hshore, hleft, hright, ?_⟩
  dsimp only at hcut ⊢
  rcases hcut with ⟨faceCut, selected, realization, hcard⟩
  refine ⟨faceCut, selected, realization, hcard, ?_⟩
  have hconnected : G.Connected := by
    rw [←
      GoertzelV24SimpleGraphFaceDualConnectedness.rotationPrimalGraph_toRotationSystem_eq
        G rotation]
    exact minimal.primalConnected
  exact realization.exists_connectedAtWidth_subcut hconnected
    _ hcard

/-- A carrier-local deep stack of depth at least two already yields a
provenanced connected cyclic subcut. -/
theorem saturated_of_nestedCarrierDeepReturnStack
    (rotation : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (bond : ProperAlternatingSiteFacialBondWitness rotation sigma first second)
    (depth : Nat) (hdepth : 1 ≤ depth)
    (hdeep : HasNestedCarrierDeepReturnStack rotation minimal hG sigma hSigma
      bond depth) :
    HasSaturatedDegreeControlledCyclicReturnCut rotation hG sigma hSigma bond := by
  rcases hdeep with
    ⟨_outer, _inner, _hshore, _hleft, _hright,
      shore, cut, _hposition, hstack⟩
  apply saturated_of_degreeControlled rotation minimal hG sigma hSigma bond
  apply hasDegreeControlledCyclicReturnCut_of_deep_return_shore
    rotation minimal hG sigma hSigma bond
  exact ⟨shore, cut, lt_of_le_of_lt hdepth hstack⟩

/-- Forgetting the separator provenance exposes the exact connected shore
node carried by a saturated degree-controlled return cut. -/
theorem exists_connectedShoreNode_of_saturated
    (rotation : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (bond : ProperAlternatingSiteFacialBondWitness rotation sigma first second)
    (hcut : HasSaturatedDegreeControlledCyclicReturnCut rotation hG sigma
      hSigma bond) :
    ∃ bound : Nat,
      Nonempty (ConnectedShoreNode (G := G) bound bound) := by
  rcases hcut with
    ⟨_outer, inner, _hshore, _hleft, _hright,
      faceCut, selected, _rawRealization, _hcard, connected, _hsubset⟩
  let bound :=
    (orderedReturnSeparator hG sigma hSigma bond.site inner).support.toFinset.card * 3
  exact ⟨bound, ⟨connected.toConnectedShoreNode rotation minimal⟩⟩

/-- The fully compressed alternative with its carrier-deep horn replaced by
a concrete, saturated cyclic-cut receipt. -/
def FullyRealizedExactStateAlternative
    (rotation : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (bond : ProperAlternatingSiteFacialBondWitness rotation sigma first second)
    (depth spacing : Nat) : Prop :=
  Nonempty
      (ConnectedShoreNode (G := G)
        (6 * AmbientReturnAttachmentCompression.fullyCompressedComponentBound
          depth spacing)
        (6 * AmbientReturnAttachmentCompression.fullyCompressedComponentBound
          depth spacing)) ∨
    AmbientReturnAttachmentCompression.HasNestedAmbientAttachmentSweepAlternative
      rotation minimal hG sigma hSigma bond depth spacing ∨
    HasSaturatedDegreeControlledCyclicReturnCut rotation hG sigma hSigma bond ∨
    HasNestedCarrierSpacedSweepRepeat rotation minimal hG sigma hSigma bond spacing ∨
    HasSpacedResidualReturnSweepRepeat rotation minimal hG sigma hSigma bond spacing

/-- Realize the carrier-deep horn of an exact-state compressed alternative.
Only the mathematically necessary condition `1 ≤ depth` is added: a cyclic
annulus needs two nested return chords. -/
theorem realized_of_exactStateAlternative
    (rotation : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (bond : ProperAlternatingSiteFacialBondWitness rotation sigma first second)
    (depth spacing : Nat) (hdepth : 1 ≤ depth)
    (alternative : FullyCompressedExactStateAlternative rotation minimal hG
      sigma hSigma bond depth spacing) :
    FullyRealizedExactStateAlternative rotation minimal hG sigma hSigma bond
      depth spacing := by
  rcases alternative with
    hstate | hambient | hdeep | hcarrierRepeat | hreturnRepeat
  · exact Or.inl hstate
  · exact Or.inr (Or.inl hambient)
  · exact Or.inr (Or.inr (Or.inl
      (saturated_of_nestedCarrierDeepReturnStack rotation minimal hG sigma
        hSigma bond depth hdepth hdeep)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl hcarrierRepeat)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr hreturnRepeat)))

/-- Consumer theorem from the original geometric hypotheses directly to the
alternative with a physically realized carrier-deep branch. -/
theorem hasFullyRealizedExactStateAlternative
    (rotation : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (bond : ProperAlternatingSiteFacialBondWitness rotation sigma first second)
    (depth spacing : Nat) (hdepth : 1 ≤ depth)
    (hmany : 2 * (spacing + 1) * (1 + 1) ^ 2 <
      bond.site.cycle.tail.support.length) :
    FullyRealizedExactStateAlternative rotation minimal hG sigma hSigma bond
      depth spacing :=
  realized_of_exactStateAlternative rotation minimal hG sigma hSigma bond
    depth spacing hdepth
    (hasFullyCompressedExactStateAlternative rotation minimal hG sigma hSigma
      bond depth spacing hmany)

end

end DeepReturnExactState

end Mettapedia.GraphTheory.FourColor.Compositional
