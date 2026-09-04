import Mettapedia.GraphTheory.FourColor.Compositional.ResidualReturnNestedFamily

/-!
# Nested connected cut shores from residual-return triples

Three strictly nested physical returns determine two cycle separators.  The
outer complementary return cycle fixes one common exterior root.  Each
separator is pushed to an exact primal edge cut and saturated relative to
that root.  Exact face-side nesting then proves that the inner connected
shore is contained in the middle connected shore.

The two cuts use one common width bound.  This is the literal nested-cut
object consumed by the cumulative-state pigeonhole and physical replacement
theorems; neither the cuts nor their nesting are assumed.
-/

namespace Mettapedia.GraphTheory.FourColor.Compositional

namespace ResidualReturnNestedCuts

open CyclePushOffCut
open GoertzelV24CyclicThreeCutConnectedSides
open GoertzelV24FaceDualConnectedness
open GoertzelV24OrderedMeshResidualSiteFacialBond
open GoertzelV24ResidualReturnCycleOrder
open GoertzelV24ResidualReturnSectorNoncrossing
open GoertzelV24TwoEdgeCutMinimality
open MatchingParity
open Mettapedia.GraphTheory.Embedding
open ResidualReturnComplementaryCycle
open ResidualReturnNestedFamily
open ResidualReturnSeparatorFaceCut
open ResidualReturnSeparatorNesting
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

/-- Two connected cyclic-cut shores at one width, with the inner shore
pointwise contained in the outer shore. -/
def HasNestedConnectedReturnCuts (G : SimpleGraph V) [DecidableRel G.Adj] :
    Prop :=
  ∃ bound : Nat,
    ∃ middle inner : CyclicEdgeCutRealization.ConnectedAtWidth G bound,
      ∀ vertex, inner.realization.side vertex →
        middle.realization.side vertex

/-- A physical strictly nested return triple constructs two nested connected
cut shores at one explicit common width.  The common exterior root is the
base point of the outer complementary return cycle. -/
theorem hasNestedConnectedReturnCuts_of_strictlyNestedReturnTriple
    (rotation : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (bond : ProperAlternatingSiteFacialBondWitness rotation sigma first second)
    (triple : StrictlyNestedReturnTriple rotation hG sigma hSigma bond) :
    HasNestedConnectedReturnCuts G := by
  rcases triple with
    ⟨shore, outer, middle, inner, houterShore, hmiddleShore, hinnerShore,
      houterMiddleLeft, hmiddleInnerLeft, hinnerMiddleRight,
      hmiddleOuterRight⟩
  have hshoreOuterMiddle :
      orderedReturnShore rotation hG sigma hSigma bond outer.left =
        orderedReturnShore rotation hG sigma hSigma bond middle.left := by
    exact houterShore.trans hmiddleShore.symm
  have hshoreMiddleInner :
      orderedReturnShore rotation hG sigma hSigma bond middle.left =
        orderedReturnShore rotation hG sigma hSigma bond inner.left := by
    exact hmiddleShore.trans hinnerShore.symm
  let middleSeparator :=
    orderedReturnSeparator hG sigma hSigma bond.site middle
  let innerSeparator :=
    orderedReturnSeparator hG sigma hSigma bond.site inner
  let outsideCycle :=
    complementaryReturnCycle hG sigma hSigma bond.site outer
  let outsideRoot := (cycleVertexOrder sigma bond.site outer.left).1
  let middleBound := middleSeparator.support.toFinset.card * 3
  let innerBound := innerSeparator.support.toFinset.card * 3
  let bound := max middleBound innerBound
  have hmiddleCycle : middleSeparator.IsCycle := by
    simpa only [middleSeparator] using
      orderedReturnSeparator_isCycle_automatic
        hG sigma hSigma bond.site middle
  have hinnerCycle : innerSeparator.IsCycle := by
    simpa only [innerSeparator] using
      orderedReturnSeparator_isCycle_automatic
        hG sigma hSigma bond.site inner
  have houtsideCycle : outsideCycle.IsCycle := by
    simpa only [outsideCycle] using
      complementaryReturnCycle_isCycle hG sigma hSigma bond.site outer
        (complementaryReturnCycle_length_alternative
          hG sigma hSigma bond.site outer)
  have houterInnerLeft : outer.left < inner.left :=
    houterMiddleLeft.trans hmiddleInnerLeft
  have hinnerOuterRight : inner.right < outer.right :=
    hinnerMiddleRight.trans hmiddleOuterRight
  have hdisjointMiddle :
      outsideCycle.support.Disjoint middleSeparator.support := by
    simpa only [outsideCycle, middleSeparator] using
      complementaryReturnCycle_support_disjoint_orderedReturnSeparator
        hG sigma hSigma bond.site outer middle
          houterMiddleLeft hmiddleOuterRight
  have hdisjointInner :
      outsideCycle.support.Disjoint innerSeparator.support := by
    simpa only [outsideCycle, innerSeparator] using
      complementaryReturnCycle_support_disjoint_orderedReturnSeparator
        hG sigma hSigma bond.site outer inner
          houterInnerLeft hinnerOuterRight
  rcases exists_exactFaceCut_orderedReturnSeparator rotation minimal hG sigma
      hSigma bond.site middle with ⟨middleFaceCut, _hmiddleBoundary⟩
  rcases exists_exactFaceCut_orderedReturnSeparator rotation minimal hG sigma
      hSigma bond.site inner with ⟨innerFaceCut, _hinnerBoundary⟩
  rcases exists_selected_with_specific_complement_cycle
      rotation minimal.vertexRotationCyclic middleSeparator middleFaceCut
        outsideCycle houtsideCycle hdisjointMiddle with
    ⟨middleSelected, houtsideMiddle⟩
  rcases exists_selected_with_specific_complement_cycle
      rotation minimal.vertexRotationCyclic innerSeparator innerFaceCut
        outsideCycle houtsideCycle hdisjointInner with
    ⟨innerSelected, houtsideInner⟩
  have hmiddleComplement : HasCycleOnSide G (fun vertex =>
      ¬middleFaceCut.filledCycleSide rotation middleSeparator
        middleSelected vertex) :=
    ⟨_, houtsideMiddle _ outsideCycle.start_mem_support,
      outsideCycle, houtsideCycle, houtsideMiddle⟩
  have hinnerComplement : HasCycleOnSide G (fun vertex =>
      ¬innerFaceCut.filledCycleSide rotation innerSeparator
        innerSelected vertex) :=
    ⟨_, houtsideInner _ outsideCycle.start_mem_support,
      outsideCycle, houtsideCycle, houtsideInner⟩
  let middleRaw := cyclicEdgeCutRealization_of_complement_cycle
    rotation middleSeparator hmiddleCycle middleFaceCut middleSelected
      hmiddleComplement
  let innerRaw := cyclicEdgeCutRealization_of_complement_cycle
    rotation innerSeparator hinnerCycle innerFaceCut innerSelected
      hinnerComplement
  have hmiddleWidth0 :
      (CyclePushOffCut.edges rotation middleSeparator middleFaceCut
        middleSelected).card ≤ middleBound := by
    apply card_edges_le_support_mul_degreeBound
      rotation minimal.vertexRotationCyclic middleSeparator middleFaceCut
        middleSelected 3
    intro vertex _hvertex
    exact (incidentEdgeFinset_card_eq_three_of_hasCubicIncidentEdgeTriples
      hG vertex).le
  have hinnerWidth0 :
      (CyclePushOffCut.edges rotation innerSeparator innerFaceCut
        innerSelected).card ≤ innerBound := by
    apply card_edges_le_support_mul_degreeBound
      rotation minimal.vertexRotationCyclic innerSeparator innerFaceCut
        innerSelected 3
    intro vertex _hvertex
    exact (incidentEdgeFinset_card_eq_three_of_hasCubicIncidentEdgeTriples
      hG vertex).le
  have hmiddleWidth :
      (CyclePushOffCut.edges rotation middleSeparator middleFaceCut
        middleSelected).card ≤ bound :=
    hmiddleWidth0.trans (Nat.le_max_left _ _)
  have hinnerWidth :
      (CyclePushOffCut.edges rotation innerSeparator innerFaceCut
        innerSelected).card ≤ bound :=
    hinnerWidth0.trans (Nat.le_max_right _ _)
  have hconnected : G.Connected := by
    rw [←
      GoertzelV24SimpleGraphFaceDualConnectedness.rotationPrimalGraph_toRotationSystem_eq
        G rotation]
    exact minimal.primalConnected
  have hmiddleRawConnected : (G.induce middleRaw.side).Connected := by
    exact induce_filledCycleSide_connected rotation hconnected
      minimal.vertexRotationCyclic middleSeparator hmiddleCycle
        middleFaceCut middleSelected
  have hinnerRawConnected : (G.induce innerRaw.side).Connected := by
    exact induce_filledCycleSide_connected rotation hconnected
      minimal.vertexRotationCyclic innerSeparator hinnerCycle
        innerFaceCut innerSelected
  have hrootMiddle : ¬middleRaw.side outsideRoot :=
    houtsideMiddle _ outsideCycle.start_mem_support
  have hrootInner : ¬innerRaw.side outsideRoot :=
    houtsideInner _ outsideCycle.start_mem_support
  rcases RootedCutSaturation.exists_connectedAtWidth
      hconnected middleRaw hmiddleRawConnected outsideRoot hrootMiddle
      outsideCycle houtsideCycle houtsideMiddle bound hmiddleWidth with
    ⟨middleConnected, _hmiddleEdgeCut, hmiddleSide⟩
  rcases RootedCutSaturation.exists_connectedAtWidth
      hconnected innerRaw hinnerRawConnected outsideRoot hrootInner
      outsideCycle houtsideCycle houtsideInner bound hinnerWidth with
    ⟨innerConnected, _hinnerEdgeCut, hinnerSide⟩
  have hinnerSupportMiddleFilled : ∀ vertex,
      vertex ∈ innerSeparator.support →
        middleFaceCut.filledCycleSide rotation middleSeparator
          middleSelected vertex := by
    simpa only [middleSeparator, innerSeparator] using
      orderedReturnSeparator_support_subset_filledCycleSide_of_triple_nested
        rotation minimal hG sigma hSigma bond outer middle inner
          houterMiddleLeft hmiddleInnerLeft hinnerMiddleRight
          hmiddleOuterRight hshoreOuterMiddle hshoreMiddleInner
          middleFaceCut middleSelected houtsideMiddle
  have hinnerSupportMiddleClosure : ∀ vertex,
      vertex ∈ innerSeparator.support →
        closureSide (G := G) middleRaw.side outsideRoot
          hrootMiddle vertex := by
    intro vertex hvertex
    apply side_subset_closureSide middleRaw.side outsideRoot
      hrootMiddle vertex
    exact hinnerSupportMiddleFilled vertex hvertex
  have hrootMiddleClosure :
      ¬closureSide (G := G) middleRaw.side outsideRoot
        hrootMiddle outsideRoot := by
    intro hclosure
    apply hclosure
    exact inducedReachableSide_root
      (fun vertex => ¬middleRaw.side vertex) outsideRoot hrootMiddle
  have hmiddleClosureComplementConnected :
      (G.induce (fun vertex =>
        ¬closureSide (G := G) middleRaw.side outsideRoot
          hrootMiddle vertex)).Connected :=
    induce_complement_closureSide_connected middleRaw.side
      outsideRoot hrootMiddle
  have hclosuresNested : ∀ vertex,
      closureSide (G := G) innerRaw.side outsideRoot hrootInner vertex →
        closureSide (G := G) middleRaw.side outsideRoot
          hrootMiddle vertex := by
    apply closureSide_filledCycleSide_subset_of_cycle_support_subset
      rotation minimal.vertexRotationCyclic innerSeparator innerFaceCut
        innerSelected
        (closureSide (G := G) middleRaw.side outsideRoot hrootMiddle)
        hmiddleClosureComplementConnected outsideRoot hrootInner
        hrootMiddleClosure
    exact hinnerSupportMiddleClosure
  refine ⟨bound, middleConnected, innerConnected, ?_⟩
  intro vertex hinner
  apply (hmiddleSide vertex).2
  apply hclosuresNested vertex
  exact (hinnerSide vertex).1 hinner

/-- The depth-two horn of the carrier-local sweep therefore constructs a
literal nested pair of connected cut shores. -/
theorem hasNestedConnectedReturnCuts_of_nestedCarrierDeepReturnStack
    (rotation : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (bond : ProperAlternatingSiteFacialBondWitness rotation sigma first second)
    (hdeep : ResidualReturnCarrierSweep.HasNestedCarrierDeepReturnStack
      rotation minimal hG sigma hSigma bond 2) :
    HasNestedConnectedReturnCuts G :=
  hasNestedConnectedReturnCuts_of_strictlyNestedReturnTriple
    rotation minimal hG sigma hSigma bond
      (strictlyNestedReturnTriple_of_nestedCarrierDeepReturnStack
        rotation minimal hG sigma hSigma bond hdeep)

end

end ResidualReturnNestedCuts

end Mettapedia.GraphTheory.FourColor.Compositional
