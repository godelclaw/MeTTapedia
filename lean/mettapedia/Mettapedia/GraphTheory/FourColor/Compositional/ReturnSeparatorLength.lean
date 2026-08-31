import Mettapedia.GraphTheory.FourColor.GoertzelV24ResidualReturnSectorNoncrossing

/-!
# Length decomposition for return separators

A physical return separator is the union of two geometrically different
paths: the return through the ambient graph and the interval along the carrier
cycle.  Its support can therefore be large for two different reasons.  This
file records that elementary decomposition before either case is compressed.

The statements are generic walk combinatorics followed by the semantic return
separator specialization.  No planarity or colouring hypothesis is used.
-/

namespace Mettapedia.GraphTheory.FourColor.Compositional.ReturnSeparatorLength

open GoertzelV24OrderedMeshResidualSiteMatching
open GoertzelV24ResidualReturnCycleOrder
open GoertzelV24ResidualReturnSectorNoncrossing
open MatchingParity
open SimpleGraph

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

/-- The distinct vertices of an appended walk are contained in the union of
the distinct vertices of its two pieces. -/
theorem support_toFinset_card_append_le {start middle finish : V}
    (first : G.Walk start middle) (second : G.Walk middle finish) :
    (first.append second).support.toFinset.card ≤
      first.support.toFinset.card + second.support.toFinset.card := by
  calc
    (first.append second).support.toFinset.card =
        (first.support.toFinset ∪ second.support.tail.toFinset).card := by
      rw [SimpleGraph.Walk.support_append, List.toFinset_append]
    _ ≤ first.support.toFinset.card + second.support.tail.toFinset.card :=
      Finset.card_union_le _ _
    _ ≤ first.support.toFinset.card + second.support.toFinset.card := by
      apply Nat.add_le_add_left
      apply Finset.card_le_card
      intro vertex hvertex
      simp only [List.mem_toFinset] at hvertex ⊢
      exact List.mem_of_mem_tail hvertex

/-- The support of a return separator is bounded by the supports of its
ambient return and carrier interval. -/
theorem orderedReturnSeparator_support_toFinset_card_le
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (site : ProperAlternatingSiteWitness G sigma first second)
    (chord : OrderedReturnChord
      (orderedSiteReturnPairing hG sigma hSigma site)) :
    (orderedReturnSeparator hG sigma hSigma site chord).support.toFinset.card ≤
      (orderedChordAmbientPath hG sigma hSigma site chord).support.toFinset.card +
        (residualCycleInterval sigma site chord).support.toFinset.card := by
  unfold orderedReturnSeparator
  calc
    ((orderedChordAmbientPath hG sigma hSigma site chord).append
        (residualCycleInterval sigma site chord).reverse).support.toFinset.card ≤
        (orderedChordAmbientPath hG sigma hSigma site chord).support.toFinset.card +
          (residualCycleInterval sigma site chord).reverse.support.toFinset.card :=
      support_toFinset_card_append_le _ _
    _ = (orderedChordAmbientPath hG sigma hSigma site chord).support.toFinset.card +
          (residualCycleInterval sigma site chord).support.toFinset.card := by
      simp only [SimpleGraph.Walk.support_reverse, List.toFinset_reverse]

/-- The carrier piece is a simple path, so its number of distinct vertices is
exactly its coordinate span plus one. -/
theorem residualCycleInterval_support_toFinset_card
    (sigma : Pairing V) {first second : V}
    (site : ProperAlternatingSiteWitness G sigma first second)
    {pairing : Pairing (CyclePosition sigma site)}
    (chord : OrderedReturnChord pairing) :
    (residualCycleInterval sigma site chord).support.toFinset.card =
      chord.right.val - chord.left.val + 1 := by
  rw [List.toFinset_card_of_nodup
    (residualCycleInterval_isPath sigma site chord).support_nodup]
  rw [(residualCycleInterval sigma site chord).length_support,
    residualCycleInterval_length sigma site chord]

/-- If a return separator has more than twice `bound` distinct vertices, then
either its ambient return or its carrier interval has more than `bound`
distinct vertices. -/
theorem long_ambientReturn_or_long_carrierInterval
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (site : ProperAlternatingSiteWitness G sigma first second)
    (chord : OrderedReturnChord
      (orderedSiteReturnPairing hG sigma hSigma site))
    (bound : Nat)
    (hlong : 2 * bound <
      (orderedReturnSeparator hG sigma hSigma site chord).support.toFinset.card) :
    bound <
        (orderedChordAmbientPath hG sigma hSigma site chord).support.toFinset.card ∨
      bound <
        (residualCycleInterval sigma site chord).support.toFinset.card := by
  by_contra hshort
  rw [not_or] at hshort
  have hambient :
      (orderedChordAmbientPath hG sigma hSigma site chord).support.toFinset.card ≤
        bound := Nat.le_of_not_gt hshort.1
  have hcarrier :
      (residualCycleInterval sigma site chord).support.toFinset.card ≤ bound :=
    Nat.le_of_not_gt hshort.2
  have hseparator :=
    orderedReturnSeparator_support_toFinset_card_le
      hG sigma hSigma site chord
  omega

end

end Mettapedia.GraphTheory.FourColor.Compositional.ReturnSeparatorLength
