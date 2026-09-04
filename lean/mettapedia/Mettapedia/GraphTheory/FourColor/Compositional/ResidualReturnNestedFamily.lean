import Mettapedia.GraphTheory.FourColor.Compositional.ResidualReturnCarrierSweep
import Mettapedia.GraphTheory.FourColor.Compositional.ResidualReturnSeparatorNesting

/-!
# Physical return triples extracted from a deep residual stack

The LIFO sweep records residual returns as ordered labelled arcs.  Separator
geometry, however, is stated for the original chords of the physical return
pairing.  This file closes that representation seam: every selected sweep arc
is realized by a physical chord on the selected shore, with exactly the same
two endpoints.

Consequently a residual stack of depth at least three supplies three literal
same-shore return chords in strict nesting order.  These are the direct input
to the separator-side nesting theorem; no abstract family of cuts is assumed.
-/

namespace Mettapedia.GraphTheory.FourColor.Compositional

namespace ResidualReturnNestedFamily

open GoertzelV24NoncrossingSweepLifo
open GoertzelV24OrderedMeshResidualSiteFacialBond
open GoertzelV24ResidualReturnCycleOrder
open GoertzelV24TwoEdgeCutMinimality
open MatchingParity
open NoncrossingPairingSweep
open ResidualReturnCarrierSweep
open ResidualReturnSweep
open SimpleGraph
open SimpleGraphDartRotation

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Three physical residual returns on one facial shore, strictly nested in
the linear display of the carrier cycle. -/
def StrictlyNestedReturnTriple
    (rotation : Data G)
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (bond : ProperAlternatingSiteFacialBondWitness rotation sigma first second) :
    Prop :=
  ∃ (shore : Bool)
      (outer middle inner : OrderedReturnChord
        (orderedSiteReturnPairing hG sigma hSigma bond.site)),
    orderedReturnShore rotation hG sigma hSigma bond outer.left = shore ∧
      orderedReturnShore rotation hG sigma hSigma bond middle.left = shore ∧
      orderedReturnShore rotation hG sigma hSigma bond inner.left = shore ∧
      outer.left < middle.left ∧ middle.left < inner.left ∧
      inner.right < middle.right ∧ middle.right < outer.right

/-- Every arc retained by one shore matching comes from a literal physical
return chord on that shore, with exactly the displayed arc endpoints. -/
theorem exists_physical_chord_of_mem_returnShoreMatching_arcs
    (rotation : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (bond : ProperAlternatingSiteFacialBondWitness rotation sigma first second)
    (shore : Bool)
    (arc : LabeledArc Unit bond.site.cycle.tail.support.length)
    (harc : arc ∈
      (returnShoreMatching rotation minimal hG sigma hSigma bond shore).arcs) :
    ∃ chord : OrderedReturnChord
        (orderedSiteReturnPairing hG sigma hSigma bond.site),
      orderedReturnShore rotation hG sigma hSigma bond chord.left = shore ∧
        chord.left = arc.left ∧ chord.right = arc.right := by
  let selected : CyclePosition sigma bond.site → Prop :=
    OnReturnShore rotation hG sigma hSigma bond shore
  letI : DecidablePred selected := fun position => by
    dsimp [selected, OnReturnShore]
    infer_instance
  have hcanonical : arc ∈ canonicalArcList
      (orderedSiteReturnPairing hG sigma hSigma bond.site)
      selected (fun _ => ()) := by
    simpa [returnShoreMatching, noncrossingMatchingOfPairing, selected] using harc
  rcases exists_canonical_position_of_mem_canonicalArcList
      (orderedSiteReturnPairing hG sigma hSigma bond.site)
      selected (fun _ => ()) arc hcanonical with
    ⟨position, hposition, hselected, harcEq⟩
  let chord := orderedReturnChord
    (orderedSiteReturnPairing hG sigma hSigma bond.site) position
  refine ⟨chord, ?_, ?_, ?_⟩
  · simpa [chord, selected, OnReturnShore, orderedReturnChord,
      min_eq_left hposition.le] using hselected
  · have := congrArg LabeledArc.left harcEq
    simpa [chord, chordArc] using this
  · have := congrArg LabeledArc.right harcEq
    simpa [chord, chordArc] using this

/-- A residual-return stack deeper than two is not merely an abstract list:
it contains three literal physical return chords on one shore, in strict
nesting order. -/
theorem strictlyNestedReturnTriple_of_deep_stack
    (rotation : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (bond : ProperAlternatingSiteFacialBondWitness rotation sigma first second)
    (hdeep : ∃ shore cut,
      2 < (((residualReturnSweepData rotation minimal hG sigma hSigma bond).family
        shore).stackAt cut).length) :
    StrictlyNestedReturnTriple rotation hG sigma hSigma bond := by
  rcases exists_long_strictlyNested_return_family_of_deep
      rotation minimal hG sigma hSigma bond 2 hdeep with
    ⟨shoreIndex, cut, hlength, hpairwise⟩
  let shore := returnShoreIndex shoreIndex
  let matching :=
    returnShoreMatching rotation minimal hG sigma hSigma bond shore
  let arcs := matching.openArcs cut
  change 2 < arcs.length at hlength
  change arcs.Pairwise (fun outer inner =>
    outer.left < inner.left ∧ inner.right < outer.right) at hpairwise
  have hzero : 0 < arcs.length := by omega
  have hone : 1 < arcs.length := by omega
  have htwo : 2 < arcs.length := hlength
  let zero : Fin arcs.length := ⟨0, hzero⟩
  let one : Fin arcs.length := ⟨1, hone⟩
  let two : Fin arcs.length := ⟨2, htwo⟩
  let outerArc := arcs.get zero
  let middleArc := arcs.get one
  let innerArc := arcs.get two
  have hzeroOne : zero < one := by simp [zero, one]
  have honeTwo : one < two := by simp [one, two]
  have houterMiddle := hpairwise.rel_get_of_lt hzeroOne
  have hmiddleInner := hpairwise.rel_get_of_lt honeTwo
  have houterOpen : outerArc ∈ matching.openArcs cut := by
    simpa [arcs, outerArc] using List.get_mem arcs zero
  have hmiddleOpen : middleArc ∈ matching.openArcs cut := by
    simpa [arcs, middleArc] using List.get_mem arcs one
  have hinnerOpen : innerArc ∈ matching.openArcs cut := by
    simpa [arcs, innerArc] using List.get_mem arcs two
  have houterArc : outerArc ∈ matching.arcs := by
    exact List.mem_of_mem_filter houterOpen
  have hmiddleArc : middleArc ∈ matching.arcs := by
    exact List.mem_of_mem_filter hmiddleOpen
  have hinnerArc : innerArc ∈ matching.arcs := by
    exact List.mem_of_mem_filter hinnerOpen
  rcases exists_physical_chord_of_mem_returnShoreMatching_arcs
      rotation minimal hG sigma hSigma bond shore outerArc houterArc with
    ⟨outer, houterShore, houterLeft, houterRight⟩
  rcases exists_physical_chord_of_mem_returnShoreMatching_arcs
      rotation minimal hG sigma hSigma bond shore middleArc hmiddleArc with
    ⟨middle, hmiddleShore, hmiddleLeft, hmiddleRight⟩
  rcases exists_physical_chord_of_mem_returnShoreMatching_arcs
      rotation minimal hG sigma hSigma bond shore innerArc hinnerArc with
    ⟨inner, hinnerShore, hinnerLeft, hinnerRight⟩
  refine ⟨shore, outer, middle, inner,
    houterShore, hmiddleShore, hinnerShore, ?_, ?_, ?_, ?_⟩
  · simpa only [houterLeft, hmiddleLeft] using houterMiddle.1
  · simpa only [hmiddleLeft, hinnerLeft] using hmiddleInner.1
  · simpa only [hmiddleRight, hinnerRight] using hmiddleInner.2
  · simpa only [houterRight, hmiddleRight] using houterMiddle.2

/-- The deep horn of the carrier-local geometric alternative at depth two
therefore supplies the literal nested return triple consumed by separator
geometry. -/
theorem strictlyNestedReturnTriple_of_nestedCarrierDeepReturnStack
    (rotation : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (bond : ProperAlternatingSiteFacialBondWitness rotation sigma first second)
    (hdeep : HasNestedCarrierDeepReturnStack
      rotation minimal hG sigma hSigma bond 2) :
    StrictlyNestedReturnTriple rotation hG sigma hSigma bond := by
  rcases hdeep with ⟨_outer, _inner, _hshore, _hleft, _hright,
    shore, cut, _hcut, hdepth⟩
  exact strictlyNestedReturnTriple_of_deep_stack
    rotation minimal hG sigma hSigma bond ⟨shore, cut, hdepth⟩

end

end ResidualReturnNestedFamily

end Mettapedia.GraphTheory.FourColor.Compositional
