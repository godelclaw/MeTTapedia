import Mettapedia.GraphTheory.FourColor.Compositional.ResidualReturnStrictNesting
import Mettapedia.GraphTheory.FourColor.CyclicCutConnectedShore
import Mettapedia.GraphTheory.FourColor.GoertzelV24MajorityShoreStateDescent

/-!
# Long strict connected-cut families from residual-return stacks

A nested physical return family is converted into a coherent family of
connected cut shores.  One outer return supplies a common exterior root and
one innermost return supplies a common orientation guard.  Every intervening
return is pushed off and saturated independently, then all resulting receipts
are widened to one finite common bound.

The theorem deliberately exposes that common bound rather than claiming it is
uniform in the ambient graph.  Bounding it independently is the remaining
high-width obligation; the present file closes the family-coherence and
strictness part of M1.
-/

namespace Mettapedia.GraphTheory.FourColor.Compositional

namespace ResidualReturnStrictFamily

open GoertzelV24ConnectedVertexSideEdgeShore
open GoertzelV24ConnectedShoreLiteralNode
open GoertzelV24MajorityShoreStateDescent
open GoertzelV24OrderedMeshResidualSiteFacialBond
open GoertzelV24ResidualReturnCycleOrder
open GoertzelV24ResidualReturnSectorNoncrossing
open GoertzelV24TwoEdgeCutMinimality
open MatchingParity
open ResidualReturnNestedCuts
open ResidualReturnNestedFamily
open ResidualReturnStrictNesting
open RootedCutSaturation
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

/-- A finite family of connected cuts at one width whose literal incident-edge
shores are strictly decreasing in the displayed order. -/
def HasStrictlyNestedConnectedReturnCutFamily
    (G : SimpleGraph V) [DecidableRel G.Adj] (length : Nat) : Prop :=
  ∃ bound : Nat,
    ∃ cuts : Fin length → CyclicEdgeCutRealization.ConnectedAtWidth G bound,
      ∀ i j, i < j →
        incidentEdgeShore G (cuts j).realization.side ⊂
          incidentEdgeShore G (cuts i).realization.side

/-- A family of `length + 2` nested physical returns yields `length`
strictly nested connected cut shores.  The first and last returns are kept as
the common exterior-root and orientation guards. -/
theorem hasStrictlyNestedConnectedReturnCutFamily_of_returnFamily
    (rotation : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (bond : ProperAlternatingSiteFacialBondWitness rotation sigma first second)
    (length : Nat)
    (family : StrictlyNestedReturnFamily rotation hG sigma hSigma bond
      (length + 2)) :
    HasStrictlyNestedConnectedReturnCutFamily G length := by
  classical
  rcases family with ⟨shore, chord, hshore, hnested⟩
  let outerIndex : Fin (length + 2) := ⟨0, by omega⟩
  let targetIndex (i : Fin length) : Fin (length + 2) :=
    ⟨i.val + 1, by omega⟩
  let guardIndex : Fin (length + 2) := ⟨length + 1, by omega⟩
  have houterTarget (i : Fin length) :=
    hnested outerIndex (targetIndex i) (by
      apply Fin.mk_lt_mk.mpr
      omega)
  have htargetGuard (i : Fin length) :=
    hnested (targetIndex i) guardIndex (by
      apply Fin.mk_lt_mk.mpr
      omega)
  have hexists (i : Fin length) :=
    nestedConnectedReturnCutConstruction rotation minimal hG sigma hSigma bond
      (chord outerIndex) (chord (targetIndex i)) (chord guardIndex)
      (houterTarget i).1 (htargetGuard i).1 (htargetGuard i).2
      (houterTarget i).2
      ((hshore outerIndex).trans (hshore (targetIndex i)).symm)
      ((hshore (targetIndex i)).trans (hshore guardIndex).symm)
  choose localBound targetFaceCut guardFaceCut targetSelected guardSelected
    targetConnected guardConnected certificate using hexists
  let commonWidth := ∑ i : Fin length, localBound i
  have hlocalBound (i : Fin length) : localBound i ≤ commonWidth := by
    unfold commonWidth
    exact Finset.single_le_sum (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ i)
  let cuts (i : Fin length) := (targetConnected i).widen (hlocalBound i)
  refine ⟨commonWidth, cuts, ?_⟩
  intro i j hij
  have houterI := houterTarget i
  have hijNested := hnested (targetIndex i) (targetIndex j) (by
    apply Fin.mk_lt_mk.mpr
    omega)
  have hjGuard := htargetGuard j
  have hshoreOuterI :
      orderedReturnShore rotation hG sigma hSigma bond
          (chord outerIndex).left =
        orderedReturnShore rotation hG sigma hSigma bond
          (chord (targetIndex i)).left :=
    (hshore outerIndex).trans (hshore (targetIndex i)).symm
  have hshoreIJ :
      orderedReturnShore rotation hG sigma hSigma bond
          (chord (targetIndex i)).left =
        orderedReturnShore rotation hG sigma hSigma bond
          (chord (targetIndex j)).left :=
    (hshore (targetIndex i)).trans (hshore (targetIndex j)).symm
  have hshoreJGuard :
      orderedReturnShore rotation hG sigma hSigma bond
          (chord (targetIndex j)).left =
        orderedReturnShore rotation hG sigma hSigma bond
          (chord guardIndex).left :=
    (hshore (targetIndex j)).trans (hshore guardIndex).symm
  have hclosuresNested := closureSide_subset_of_nested_return_separators
    rotation minimal hG sigma hSigma bond (chord outerIndex)
      (chord (targetIndex i)) (chord (targetIndex j))
      houterI.1 hijNested.1 hijNested.2 houterI.2
      hshoreOuterI hshoreIJ (targetFaceCut i) (targetSelected i)
      (targetFaceCut j) (targetSelected j) (certificate i).outsideMiddle
      (certificate i).rootOutsideMiddle
      (certificate j).rootOutsideMiddle
  have hstrictClosure :=
    incidentEdgeShore_deepClosure_ssubset_shallowClosure
      rotation minimal hG sigma hSigma bond (chord outerIndex)
        (chord (targetIndex i)) (chord (targetIndex j)) (chord guardIndex)
        houterI.1 hijNested.1 hjGuard.1 hjGuard.2 hijNested.2 houterI.2
        hshoreOuterI hshoreIJ hshoreJGuard
        (targetFaceCut i) (targetSelected i)
        (targetFaceCut j) (targetSelected j)
        (certificate j).outsideMiddle
        (certificate i).rootOutsideMiddle
        (certificate j).rootOutsideMiddle hclosuresNested
  have hiSide : (cuts i).realization.side =
      closureSide (G := G)
        ((targetFaceCut i).filledCycleSide rotation
          (orderedReturnSeparator hG sigma hSigma bond.site
            (chord (targetIndex i))) (targetSelected i))
        (cycleVertexOrder sigma bond.site (chord outerIndex).left).1
        (certificate i).rootOutsideMiddle := by
    funext vertex
    exact propext ((certificate i).middleSide vertex)
  have hjSide : (cuts j).realization.side =
      closureSide (G := G)
        ((targetFaceCut j).filledCycleSide rotation
          (orderedReturnSeparator hG sigma hSigma bond.site
            (chord (targetIndex j))) (targetSelected j))
        (cycleVertexOrder sigma bond.site (chord outerIndex).left).1
        (certificate j).rootOutsideMiddle := by
    funext vertex
    exact propext ((certificate j).middleSide vertex)
  simpa only [hiSide, hjSide] using hstrictClosure

/-- A stack deeper than `length + 1` therefore yields a coherent strict
connected-cut family of length `length`. -/
theorem hasStrictlyNestedConnectedReturnCutFamily_of_deep_stack
    (rotation : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (bond : ProperAlternatingSiteFacialBondWitness rotation sigma first second)
    (length : Nat)
    (hdeep : ∃ shore cut,
      length + 1 <
        (((ResidualReturnSweep.residualReturnSweepData rotation minimal hG
          sigma hSigma bond).family shore).stackAt cut).length) :
    HasStrictlyNestedConnectedReturnCutFamily G length :=
  hasStrictlyNestedConnectedReturnCutFamily_of_returnFamily
    rotation minimal hG sigma hSigma bond length
      (strictlyNestedReturnFamily_of_deep_stack
        rotation minimal hG sigma hSigma bond (length + 1) hdeep)

/-- The connected-cut family feeds the existing literal-shore pigeonhole
theorem directly.  The returned width is the finite common bound produced by
the family construction. -/
theorem exists_width_with_length_le_stateCount_of_deep_stack
    (rotation : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (bond : ProperAlternatingSiteFacialBondWitness rotation sigma first second)
    (length : Nat)
    (hdeep : ∃ shore cut,
      length + 1 <
        (((ResidualReturnSweep.residualReturnSweepData rotation minimal hG
          sigma hSigma bond).family shore).stackAt cut).length) :
    ∃ bound : Nat,
      length ≤ (6 * bound + 1) *
        (∑ j : Fin (bound + 1),
          Nat.factorial (j : Nat) * 2 ^ (3 ^ (j : Nat))) := by
  rcases hasStrictlyNestedConnectedReturnCutFamily_of_deep_stack
      rotation minimal hG sigma hSigma bond length hdeep with
    ⟨bound, cuts, hstrict⟩
  let nodes : Fin length → LiteralShoreNode rotation bound bound := fun i =>
    ((cuts i).toConnectedShoreNode rotation minimal).toLiteral rotation minimal
  refine ⟨bound, length_le_of_literalShoreChain rotation minimal
    bound bound length nodes ?_⟩
  intro i j hij
  simpa only [nodes, ConnectedShoreNode.toLiteral_shore,
    CyclicEdgeCutRealization.ConnectedAtWidth.toConnectedShoreNode_shore] using
      hstrict i j hij

end

end ResidualReturnStrictFamily

end Mettapedia.GraphTheory.FourColor.Compositional
