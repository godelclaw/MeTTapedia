import Mettapedia.GraphTheory.FourColor.Compositional.ResidualReturnSweep
import Mettapedia.GraphTheory.FourColor.Compositional.ResidualReturnCyclicCut

/-!
# Cyclic cuts realized from residual-return sweeps

The LIFO sweep stores a residual return as a small labelled endpoint record.
The separator geometry, by contrast, is stated for the physical chord of the
return pairing.  This file identifies those two representations and transfers
the cyclic-cut theorem to nested records in a sweep stack.

No new planarity premise is introduced: every sweep record is traced back to
the canonical endpoint from which `returnShoreMatching` constructed it.
-/

namespace Mettapedia.GraphTheory.FourColor.Compositional.ResidualReturnSweepCyclicCut

open CyclePushOffCut
open GoertzelV24FaceDualConnectedness
open GoertzelV24NoncrossingSweepLifo
open GoertzelV24OrderedMeshResidualSiteFacialBond
open GoertzelV24ResidualReturnCycleOrder
open GoertzelV24ResidualReturnSectorNoncrossing
open GoertzelV24TwoEdgeCutMinimality
open MatchingParity
open Mettapedia.GraphTheory.Embedding
open NoncrossingPairingSweep
open ResidualReturnCyclicCut
open ResidualReturnSweep
open SimpleGraph
open SimpleGraphDartRotation

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Every open record in a residual-return shore sweep is the endpoint record
of an actual canonical return chord on that shore. -/
theorem exists_physical_chord_of_mem_openArcs
    (rotation : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (bond : ProperAlternatingSiteFacialBondWitness rotation sigma first second)
    (shore : Fin 2) (cut : CyclePosition sigma bond.site)
    (arc : LabeledArc Unit bond.site.cycle.tail.support.length)
    (harc : arc ∈
      (returnShoreMatching rotation minimal hG sigma hSigma bond
        (returnShoreIndex shore)).openArcs cut) :
    ∃ chord : OrderedReturnChord
        (orderedSiteReturnPairing hG sigma hSigma bond.site),
      chord.left = arc.left ∧ chord.right = arc.right ∧
        orderedReturnShore rotation hG sigma hSigma bond chord.left =
          returnShoreIndex shore := by
  letI : DecidablePred
      (OnReturnShore rotation hG sigma hSigma bond (returnShoreIndex shore)) :=
    fun position => by
      unfold OnReturnShore
      infer_instance
  have harcs : arc ∈
      (returnShoreMatching rotation minimal hG sigma hSigma bond
        (returnShoreIndex shore)).arcs :=
    (List.mem_filter.1 harc).1
  change arc ∈ canonicalArcList
    (orderedSiteReturnPairing hG sigma hSigma bond.site)
    (OnReturnShore rotation hG sigma hSigma bond (returnShoreIndex shore))
    (fun _ => ()) at harcs
  rcases exists_canonical_position_of_mem_canonicalArcList
      (orderedSiteReturnPairing hG sigma hSigma bond.site)
      (OnReturnShore rotation hG sigma hSigma bond (returnShoreIndex shore))
      (fun _ => ()) arc harcs with
    ⟨position, hposition, hshore, harcEq⟩
  refine ⟨orderedReturnChord
      (orderedSiteReturnPairing hG sigma hSigma bond.site) position, ?_, ?_, ?_⟩
  · rw [← harcEq]
    simp only [chordArc_left_of_lt _ _ _ hposition]
    simp [orderedReturnChord, min_eq_left hposition.le]
  · rw [← harcEq]
    simp only [chordArc_right_of_lt _ _ _ hposition]
    simp [orderedReturnChord, max_eq_right hposition.le]
  · simpa [OnReturnShore, orderedReturnChord,
      min_eq_left hposition.le] using hshore

/-- A residual site has a degree-controlled cyclic return cut when two
physical returns on one facial shore are strictly nested and the inner
return's separator can be pushed to a cyclic edge cut.  The cut size is
controlled by three times the separator support; this is not a uniform-width
bound because the physical return path may itself be arbitrarily long. -/
def HasDegreeControlledCyclicReturnCut
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
            (fun edge : G.edgeSet => edge.1 ∈ separator.edges) F2,
         ∃ selected : F2,
           ∃ _realization : CyclicEdgeCutRealization G
               (CyclePushOffCut.edges rotation separator faceCut selected),
             (CyclePushOffCut.edges rotation separator faceCut selected).card ≤
               separator.support.toFinset.card * 3)

/-- The remaining non-uniform horn: a strictly nested pair on one return
shore whose inner physical separator has support larger than `bound`. -/
def HasNestedReturnSeparatorLargerThan
    (rotation : Data G)
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (bond : ProperAlternatingSiteFacialBondWitness rotation sigma first second)
    (bound : Nat) : Prop :=
  ∃ outer inner : OrderedReturnChord
      (orderedSiteReturnPairing hG sigma hSigma bond.site),
    orderedReturnShore rotation hG sigma hSigma bond outer.left =
        orderedReturnShore rotation hG sigma hSigma bond inner.left ∧
      outer.left < inner.left ∧ inner.right < outer.right ∧
      bound < (orderedReturnSeparator hG sigma hSigma bond.site inner).support.toFinset.card

/-- Two strictly nested records in one residual-return sweep stack are
realized by two strictly nested physical returns and therefore determine the
degree-controlled cyclic edge cut furnished by the separator geometry. -/
theorem hasDegreeControlledCyclicReturnCut_of_nested_openArcs
    (rotation : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (bond : ProperAlternatingSiteFacialBondWitness rotation sigma first second)
    (shore : Fin 2) (sweepCut : CyclePosition sigma bond.site)
    (outer inner : LabeledArc Unit bond.site.cycle.tail.support.length)
    (houter : outer ∈
      (returnShoreMatching rotation minimal hG sigma hSigma bond
        (returnShoreIndex shore)).openArcs sweepCut)
    (hinner : inner ∈
      (returnShoreMatching rotation minimal hG sigma hSigma bond
        (returnShoreIndex shore)).openArcs sweepCut)
    (hleft : outer.left < inner.left)
    (hright : inner.right < outer.right) :
    HasDegreeControlledCyclicReturnCut rotation hG sigma hSigma bond := by
  rcases exists_physical_chord_of_mem_openArcs rotation minimal hG sigma
      hSigma bond shore sweepCut outer houter with
    ⟨outerChord, houterLeft, houterRight, houterShore⟩
  rcases exists_physical_chord_of_mem_openArcs rotation minimal hG sigma
      hSigma bond shore sweepCut inner hinner with
    ⟨innerChord, hinnerLeft, hinnerRight, hinnerShore⟩
  refine ⟨outerChord, innerChord, houterShore.trans hinnerShore.symm,
    ?_, ?_, ?_⟩
  · simpa only [houterLeft, hinnerLeft] using hleft
  · simpa only [hinnerRight, houterRight] using hright
  apply exists_bounded_cyclicEdgeCut_of_strictly_nested_returns
    rotation minimal hG sigma hSigma bond.site outerChord innerChord
  · simpa only [houterLeft, hinnerLeft] using hleft
  · simpa only [hinnerRight, houterRight] using hright

/-- The deep horn of the physical residual-return sweep has direct geometric
content: stack depth at least two already supplies a degree-controlled cyclic
return cut. -/
theorem hasDegreeControlledCyclicReturnCut_of_deep_return_shore
    (rotation : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (bond : ProperAlternatingSiteFacialBondWitness rotation sigma first second)
    (hdeep : ∃ shore cut,
      1 < (((residualReturnSweepData rotation minimal hG sigma hSigma bond).family
        shore).stackAt cut).length) :
    HasDegreeControlledCyclicReturnCut rotation hG sigma hSigma bond := by
  rcases exists_long_strictlyNested_return_family_of_deep rotation minimal hG
      sigma hSigma bond 1 hdeep with ⟨shore, cut, hlength, hnested⟩
  let arcs := (returnShoreMatching rotation minimal hG sigma hSigma bond
    (returnShoreIndex shore)).openArcs cut
  have hzero : 0 < arcs.length := by
    change 0 <
      ((returnShoreMatching rotation minimal hG sigma hSigma bond
        (returnShoreIndex shore)).openArcs cut).length
    omega
  have hone : 1 < arcs.length := by
    simpa only [arcs] using hlength
  let outer := arcs.get ⟨0, hzero⟩
  let inner := arcs.get ⟨1, hone⟩
  have hpair : outer.left < inner.left ∧ inner.right < outer.right := by
    apply hnested.rel_get_of_lt
    change (0 : Nat) < 1
    omega
  apply hasDegreeControlledCyclicReturnCut_of_nested_openArcs rotation minimal hG sigma
    hSigma bond shore cut outer inner
  · exact arcs.get_mem ⟨0, hzero⟩
  · exact arcs.get_mem ⟨1, hone⟩
  · exact hpair.1
  · exact hpair.2

/-- **Geometric residual-return sweep alternative.**  A sufficiently long
alternating carrier has either a degree-controlled cyclic return cut or two
materially spaced positions with the same phased two-shore sweep record.  This
removes the abstract "deep stack" outcome from the consumer-facing dichotomy
without claiming a uniform interface width. -/
theorem hasDegreeControlledCyclicReturnCut_or_spaced_eq_rawState
    (rotation : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (bond : ProperAlternatingSiteFacialBondWitness rotation sigma first second)
    (spacing : Nat)
    (hmany :
      2 * (spacing + 1) * (1 + 1) ^ 2 <
        bond.site.cycle.tail.support.length) :
    HasDegreeControlledCyclicReturnCut rotation hG sigma hSigma bond ∨
      ∃ firstPosition secondPosition : CyclePosition sigma bond.site,
        firstPosition < secondPosition ∧
          spacing + 1 ≤ secondPosition.val - firstPosition.val ∧
          (phasedResidualReturnSweepData rotation minimal hG sigma hSigma bond
              spacing).rawState firstPosition =
            (phasedResidualReturnSweepData rotation minimal hG sigma hSigma bond
              spacing).rawState secondPosition := by
  rcases exists_deep_return_shore_or_spaced_eq_rawState rotation minimal hG
      sigma hSigma bond 1 spacing hmany with hdeep | hspaced
  · exact Or.inl (hasDegreeControlledCyclicReturnCut_of_deep_return_shore
      rotation minimal hG sigma hSigma bond hdeep)
  · exact Or.inr hspaced

/-- **Uniform-width / long-return / repeated-state trichotomy.**  Supplying a
candidate separator bound turns the degree-controlled cut horn into an actual
uniform-width cut unless the chosen physical return separator is longer than
that bound.  This exposes, rather than hides, the extra compression theorem
needed by the global mesh descent. -/
theorem hasCyclicEdgeCutOfSizeAtMost_or_longReturnSeparator_or_spaced_eq_rawState
    (rotation : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (bond : ProperAlternatingSiteFacialBondWitness rotation sigma first second)
    (separatorBound spacing : Nat)
    (hmany :
      2 * (spacing + 1) * (1 + 1) ^ 2 <
        bond.site.cycle.tail.support.length) :
    HasCyclicEdgeCutOfSizeAtMost G (3 * separatorBound) ∨
      HasNestedReturnSeparatorLargerThan rotation hG sigma hSigma bond
        separatorBound ∨
      ∃ firstPosition secondPosition : CyclePosition sigma bond.site,
        firstPosition < secondPosition ∧
          spacing + 1 ≤ secondPosition.val - firstPosition.val ∧
          (phasedResidualReturnSweepData rotation minimal hG sigma hSigma bond
              spacing).rawState firstPosition =
            (phasedResidualReturnSweepData rotation minimal hG sigma hSigma bond
              spacing).rawState secondPosition := by
  rcases hasDegreeControlledCyclicReturnCut_or_spaced_eq_rawState
      rotation minimal hG sigma hSigma bond spacing hmany with hcut | hrepeated
  · rcases hcut with
      ⟨outer, inner, hshore, hleft, hright, faceCut, selected,
        realization, hcard⟩
    by_cases hshort :
        (orderedReturnSeparator hG sigma hSigma bond.site inner).support.toFinset.card ≤
          separatorBound
    · left
      apply realization.hasCyclicEdgeCutOfSizeAtMost
      omega
    · exact Or.inr (Or.inl
        ⟨outer, inner, hshore, hleft, hright, Nat.lt_of_not_ge hshort⟩)
  · exact Or.inr (Or.inr hrepeated)

end

end Mettapedia.GraphTheory.FourColor.Compositional.ResidualReturnSweepCyclicCut
