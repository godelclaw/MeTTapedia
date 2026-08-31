import Mettapedia.GraphTheory.FourColor.GoertzelV24NoncrossingSweepLifo
import Mettapedia.GraphTheory.FourColor.GoertzelV24ResidualReturnCycleOrder
import Mathlib.Data.Finset.Sort

/-!
# Ordered sweeps of noncrossing pairings

A fixed-point-free involution on `Fin n` determines canonical chords by
retaining the smaller endpoint of each pair.  If a selected family of those
chords is noncrossing, sorting the retained endpoints produces the literal
ordered-arc representation consumed by the finite LIFO sweep theorem.

This module contains no planar-map assumptions.  It is the structural bridge
between a pairing stated as an involution and a sweep stated as an ordered
list of arcs.
-/

namespace Mettapedia.GraphTheory.FourColor.Compositional.NoncrossingPairingSweep

open GoertzelV24NoncrossingSweepLifo
open GoertzelV24ResidualReturnCycleOrder
open MatchingParity

universe u

/-- The arcs open across one cut of a noncrossing matching are strictly
nested in their left-endpoint order. -/
theorem openArcs_pairwise_strictlyNested {K : Type u} {n : Nat}
    (matching : NoncrossingMatching K n) (cut : Fin n) :
    (matching.openArcs cut).Pairwise fun outer inner =>
      outer.left < inner.left ∧ inner.right < outer.right := by
  have hleft : (matching.openArcs cut).Pairwise fun outer inner =>
      outer.left < inner.left :=
    matching.leftOrdered.filter _
  have hright : (matching.openArcs cut).Pairwise fun outer inner =>
      inner.right < outer.right :=
    matching.openArcs_pairwise_right_decreasing cut
  rw [List.pairwise_iff_get]
  intro first second hfirstSecond
  exact ⟨hleft.rel_get_of_lt hfirstSecond,
    hright.rel_get_of_lt hfirstSecond⟩

/-- Stack depth is exactly the number of arcs open across the cut. -/
theorem stackAt_length_eq_openArcs_length {K : Type u} {n : Nat}
    (matching : NoncrossingMatching K n) (cut : Fin n) :
    (matching.stackAt cut).length = (matching.openArcs cut).length := by
  simp [NoncrossingMatching.stackAt]

/-- The smaller endpoints of the selected chords of a pairing. -/
def canonicalLeftEndpoints {n : Nat} (pairing : Pairing (Fin n))
    (selected : Fin n → Prop) [DecidablePred selected] : Finset (Fin n) :=
  Finset.univ.filter fun position =>
    position < pairing.partner position ∧ selected position

/-- The labelled canonical chord named by one endpoint. -/
def chordArc {K : Type u} {n : Nat} (pairing : Pairing (Fin n))
    (label : Fin n → K) (position : Fin n) : LabeledArc K n where
  left := (orderedReturnChord pairing position).left
  right := (orderedReturnChord pairing position).right
  label := label position

@[simp]
theorem chordArc_left_of_lt {K : Type u} {n : Nat}
    (pairing : Pairing (Fin n)) (label : Fin n → K) (position : Fin n)
    (hlt : position < pairing.partner position) :
    (chordArc pairing label position).left = position := by
  simp [chordArc, orderedReturnChord, min_eq_left hlt.le]

@[simp]
theorem chordArc_right_of_lt {K : Type u} {n : Nat}
    (pairing : Pairing (Fin n)) (label : Fin n → K) (position : Fin n)
    (hlt : position < pairing.partner position) :
    (chordArc pairing label position).right = pairing.partner position := by
  simp [chordArc, orderedReturnChord, max_eq_right hlt.le]

/-- The selected canonical chords, ordered by increasing left endpoint. -/
def canonicalArcList {K : Type u} {n : Nat} (pairing : Pairing (Fin n))
    (selected : Fin n → Prop) [DecidablePred selected]
    (label : Fin n → K) : List (LabeledArc K n) :=
  ((canonicalLeftEndpoints pairing selected).sort.map
    (chordArc pairing label))

private theorem canonical_position_data {n : Nat}
    (pairing : Pairing (Fin n)) (selected : Fin n → Prop)
    [DecidablePred selected]
    (position : Fin (canonicalLeftEndpoints pairing selected).sort.length) :
    let value := (canonicalLeftEndpoints pairing selected).sort.get position
    value < pairing.partner value ∧ selected value := by
  dsimp only
  have hmem :
      (canonicalLeftEndpoints pairing selected).sort.get position ∈
        canonicalLeftEndpoints pairing selected :=
    (Finset.mem_sort (· ≤ ·)).1 (List.get_mem _ position)
  exact (Finset.mem_filter.1 hmem).2

/-- Build the ordered LIFO input associated with any selected noncrossing
subfamily of a pairing.  The hypothesis is stated on canonical chords, so it
is independent of the enumeration chosen by this construction. -/
def noncrossingMatchingOfPairing {K : Type u} {n : Nat}
    (pairing : Pairing (Fin n))
    (selected : Fin n → Prop) [DecidablePred selected]
    (label : Fin n → K)
    (hnoncrossing : ∀ first second : OrderedReturnChord pairing,
      selected first.left → selected second.left → ¬ first.Crosses second) :
    NoncrossingMatching K n where
  arcs := canonicalArcList pairing selected label
  proper := by
    intro arc harc
    rcases List.mem_map.1 harc with ⟨position, _hposition, rfl⟩
    exact (orderedReturnChord pairing position).left_lt_right
  leftOrdered := by
    rw [canonicalArcList, List.pairwise_map, List.pairwise_iff_get]
    intro first second hfirstSecond
    let positions := (canonicalLeftEndpoints pairing selected).sort
    have hordered : positions.Pairwise (· < ·) :=
      by simpa [positions] using
        (Finset.sortedLT_sort (canonicalLeftEndpoints pairing selected)).pairwise
    have hlt := hordered.rel_get_of_lt hfirstSecond
    have hfirst := canonical_position_data pairing selected first
    have hsecond := canonical_position_data pairing selected second
    simpa only [chordArc_left_of_lt pairing label _ hfirst.1,
      chordArc_left_of_lt pairing label _ hsecond.1] using hlt
  endpointDisjoint := by
    rw [canonicalArcList, List.pairwise_map, List.pairwise_iff_get]
    intro first second hfirstSecond
    let positions := (canonicalLeftEndpoints pairing selected).sort
    let left := positions.get first
    let right := positions.get second
    have hordered : positions.Pairwise (· < ·) :=
      by simpa [positions] using
        (Finset.sortedLT_sort (canonicalLeftEndpoints pairing selected)).pairwise
    have hlr : left < right := hordered.rel_get_of_lt hfirstSecond
    have hleft := canonical_position_data pairing selected first
    have hright := canonical_position_data pairing selected second
    change left < pairing.partner left ∧ selected left at hleft
    change right < pairing.partner right ∧ selected right at hright
    have hleftNeRight : left ≠ right := ne_of_lt hlr
    have hleftNePartnerRight : left ≠ pairing.partner right := by
      intro heq
      have hpartner : pairing.partner left = right := by
        rw [heq, pairing.partner_partner]
      have hleftOrder := hleft.1
      have hrightOrder := hright.1
      rw [hpartner] at hleftOrder
      rw [← heq] at hrightOrder
      omega
    have hpartnerLeftNeRight : pairing.partner left ≠ right := by
      intro heq
      have hpartner : pairing.partner right = left := by
        rw [← heq, pairing.partner_partner]
      have hleftOrder := hleft.1
      have hrightOrder := hright.1
      rw [heq] at hleftOrder
      rw [hpartner] at hrightOrder
      omega
    have hpartnersNe : pairing.partner left ≠ pairing.partner right := by
      intro heq
      exact hleftNeRight (by
        rw [← pairing.partner_partner left,
          ← pairing.partner_partner right, heq])
    change
      (chordArc pairing label left).left ≠
          (chordArc pairing label right).left ∧
        (chordArc pairing label left).left ≠
          (chordArc pairing label right).right ∧
        (chordArc pairing label left).right ≠
          (chordArc pairing label right).left ∧
        (chordArc pairing label left).right ≠
          (chordArc pairing label right).right
    simpa only [chordArc_left_of_lt pairing label _ hleft.1,
        chordArc_left_of_lt pairing label _ hright.1,
        chordArc_right_of_lt pairing label _ hleft.1,
        chordArc_right_of_lt pairing label _ hright.1] using
        ⟨hleftNeRight, hleftNePartnerRight,
          hpartnerLeftNeRight, hpartnersNe⟩
  noncrossing := by
    rw [canonicalArcList, List.pairwise_map, List.pairwise_iff_get]
    intro first second hfirstSecond
    let positions := (canonicalLeftEndpoints pairing selected).sort
    let left := positions.get first
    let right := positions.get second
    have hordered : positions.Pairwise (· < ·) :=
      by simpa [positions] using
        (Finset.sortedLT_sort (canonicalLeftEndpoints pairing selected)).pairwise
    have hlr : left < right := hordered.rel_get_of_lt hfirstSecond
    have hleft := canonical_position_data pairing selected first
    have hright := canonical_position_data pairing selected second
    change left < pairing.partner left ∧ selected left at hleft
    change right < pairing.partner right ∧ selected right at hright
    intro hcrossing
    apply hnoncrossing (orderedReturnChord pairing left)
      (orderedReturnChord pairing right)
    · simpa [orderedReturnChord, min_eq_left hleft.1.le] using hleft.2
    · simpa [orderedReturnChord, min_eq_left hright.1.le] using hright.2
    · left
      change
        (chordArc pairing label left).left <
            (chordArc pairing label right).left ∧
          (chordArc pairing label right).left <
            (chordArc pairing label left).right ∧
          (chordArc pairing label left).right <
            (chordArc pairing label right).right at hcrossing
      simp only [chordArc_left_of_lt pairing label _ hleft.1,
        chordArc_left_of_lt pairing label _ hright.1,
        chordArc_right_of_lt pairing label _ hleft.1,
        chordArc_right_of_lt pairing label _ hright.1] at hcrossing
      simpa only [orderedReturnChord, min_eq_left hleft.1.le,
        min_eq_left hright.1.le, max_eq_right hleft.1.le,
        max_eq_right hright.1.le] using hcrossing

end Mettapedia.GraphTheory.FourColor.Compositional.NoncrossingPairingSweep
