import Mettapedia.GraphTheory.FourColor.Compositional.NoncrossingPairingSweep
import Mettapedia.GraphTheory.FourColor.GoertzelV24ResidualReturnSectorNoncrossing

/-!
# LIFO sweeps of physical residual returns

The residual return pairing around a proper alternating cycle has two facial
shores.  Exact planar separation says that two return chords on the same shore
cannot cross.  This file turns the two shore classes into literal ordered
noncrossing matchings and feeds them to the finite LIFO sweep theorem.

Thus a long alternating carrier has a precise length--depth alternative:
either one shore contains a deeply nested return family, or two boundary
positions have the same shore letter and the same two return stacks.  This is
the synchronization datum required by the compositional route; no reducible
configuration or catalogue is involved.
-/

namespace Mettapedia.GraphTheory.FourColor.Compositional.ResidualReturnSweep

open GoertzelV24NoncrossingSweepLifo
open GoertzelV24ResidualReturnCycleOrder
open GoertzelV24ResidualReturnSectorNoncrossing
open GoertzelV24OrderedMeshResidualSiteFacialBond
open GoertzelV24TwoEdgeCutMinimality
open MatchingParity
open NoncrossingPairingSweep
open SimpleGraph
open SimpleGraphDartRotation

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

/-- The predicate selecting canonical residual chords on one facial shore. -/
def OnReturnShore
    (rotation : Data G)
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (bond : ProperAlternatingSiteFacialBondWitness rotation sigma first second)
    (shore : Bool) (position : CyclePosition sigma bond.site) : Prop :=
  orderedReturnShore rotation hG sigma hSigma bond position = shore

/-- The physical residual chords on one facial shore, sorted by their first
cyclic coordinate. -/
def returnShoreMatching
    (rotation : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (bond : ProperAlternatingSiteFacialBondWitness rotation sigma first second)
    (shore : Bool) :
    NoncrossingMatching Unit bond.site.cycle.tail.support.length :=
  by
    letI : DecidablePred
        (OnReturnShore rotation hG sigma hSigma bond shore) :=
      fun position => by
        unfold OnReturnShore
        infer_instance
    exact noncrossingMatchingOfPairing
      (orderedSiteReturnPairing hG sigma hSigma bond.site)
      (OnReturnShore rotation hG sigma hSigma bond shore)
      (fun _ => ()) (by
        intro left right hleft hright
        exact not_crosses_of_orderedReturnShore_eq_of_minimal
          rotation minimal hG sigma hSigma bond left right
            (hleft.trans hright.symm))

/-- The two Boolean shores are indexed by the two-element finite type used by
the generic simultaneous-sweep state. -/
def returnShoreIndex (index : Fin 2) : Bool :=
  decide (index = 1)

@[simp] theorem returnShoreIndex_zero : returnShoreIndex 0 = false := by
  decide

@[simp] theorem returnShoreIndex_one : returnShoreIndex 1 = true := by
  decide

/-- The complete two-shore residual sweep around one alternating carrier. -/
def residualReturnSweepData
    (rotation : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (bond : ProperAlternatingSiteFacialBondWitness rotation sigma first second) :
    SweepData Bool Unit 2 bond.site.cycle.tail.support.length where
  letter := orderedReturnShore rotation hG sigma hSigma bond
  family index := returnShoreMatching rotation minimal hG sigma hSigma bond
    (returnShoreIndex index)

/-- On either shore, the canonical residual-return list is genuinely
noncrossing. -/
theorem returnShoreMatching_pairwise_noncrossing
    (rotation : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (bond : ProperAlternatingSiteFacialBondWitness rotation sigma first second)
    (shore : Bool) :
    (returnShoreMatching rotation minimal hG sigma hSigma bond shore).arcs.Pairwise
      fun earlier later =>
        ¬(earlier.left < later.left ∧ later.left < earlier.right ∧
          earlier.right < later.right) :=
  (returnShoreMatching rotation minimal hG sigma hSigma bond shore).noncrossing

/-- **Physical residual-return length--depth alternative.**  More cyclic
positions than the two bounded Unit-stack states force either nesting deeper
than `depth` on one facial shore or two distinct positions with identical
literal two-shore sweep records. -/
theorem exists_deep_return_shore_or_distinct_eq_rawState
    (rotation : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (bond : ProperAlternatingSiteFacialBondWitness rotation sigma first second)
    (depth : Nat)
    (hmany :
      2 * (depth + 1) ^ 2 < bond.site.cycle.tail.support.length) :
    (∃ shore cut,
        depth < (((residualReturnSweepData rotation minimal hG sigma hSigma bond).family
          shore).stackAt cut).length) ∨
      ∃ firstPosition secondPosition : CyclePosition sigma bond.site,
        firstPosition ≠ secondPosition ∧
          (residualReturnSweepData rotation minimal hG sigma hSigma bond).rawState
              firstPosition =
            (residualReturnSweepData rotation minimal hG sigma hSigma bond).rawState
              secondPosition := by
  apply SweepData.exists_deep_family_or_distinct_eq_rawState
    (data := residualReturnSweepData rotation minimal hG sigma hSigma bond)
    depth
  simpa using hmany

end

end Mettapedia.GraphTheory.FourColor.Compositional.ResidualReturnSweep
