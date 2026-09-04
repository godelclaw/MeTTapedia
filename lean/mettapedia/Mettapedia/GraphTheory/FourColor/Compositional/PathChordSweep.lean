import Mettapedia.GraphTheory.PathChord
import Mettapedia.GraphTheory.FourColor.GoertzelV24NoncrossingSweepLifo
import Mathlib.Data.Finset.Sort

/-!
# LIFO sweeps of finite path-chord diagrams

This file is the representation bridge from the intrinsic finite chord
diagram on a linearly ordered path to the ordered list of labelled arcs used
by the noncrossing LIFO sweep.

The input hypotheses say exactly that distinct chords do not share endpoints
and do not cross.  Sorting the chords lexicographically therefore sorts them
strictly by their left endpoints.  No graph, embedding, colouring, or
four-colour-specific hypothesis occurs in the construction.
-/

namespace Mettapedia.GraphTheory.FourColor.Compositional.PathChordSweep

open Mettapedia.GraphTheory
open GoertzelV24NoncrossingSweepLifo

universe u

private instance orderedPathChordLinearOrder (length : Nat) :
    LinearOrder (OrderedPathChord length) :=
  LinearOrder.lift'
    (fun chord => toLex (chord.left, chord.right)) (by
      intro first second heq
      have hpairs : (first.left, first.right) =
          (second.left, second.right) := by
        simpa using congrArg ofLex heq
      cases first
      cases second
      simp_all)

/-- Regard one ordered path chord as a labelled sweep arc. -/
def chordArc {K : Type u} {length : Nat}
    (label : OrderedPathChord length → K)
    (chord : OrderedPathChord length) : LabeledArc K length where
  left := chord.left
  right := chord.right
  label := label chord

/-- The arcs of a finite chord diagram, sorted lexicographically by their
endpoint coordinates.  Endpoint disjointness later makes this strict
left-endpoint order. -/
def orderedArcList {K : Type u} {length : Nat}
    (chords : Finset (OrderedPathChord length))
    (label : OrderedPathChord length → K) : List (LabeledArc K length) :=
  chords.sort.map (chordArc label)

/-- Every sweep arc remembers the path chord from which it came. -/
theorem exists_chord_of_mem_orderedArcList
    {K : Type u} {length : Nat}
    (chords : Finset (OrderedPathChord length))
    (label : OrderedPathChord length → K)
    (arc : LabeledArc K length)
    (harc : arc ∈ orderedArcList chords label) :
    ∃ chord ∈ chords, chordArc label chord = arc := by
  rcases List.mem_map.1 harc with ⟨chord, hchord, rfl⟩
  exact ⟨chord, (Finset.mem_sort (· ≤ ·)).1 hchord, rfl⟩

private theorem left_lt_of_sorted_lt_of_left_ne
    {length : Nat} {first second : OrderedPathChord length}
    (hsorted : first < second) (hne : first.left ≠ second.left) :
    first.left < second.left := by
  change toLex (first.left, first.right) <
    toLex (second.left, second.right) at hsorted
  have hle := (Prod.Lex.toLex_lt_toLex'.1 hsorted).1
  exact lt_of_le_of_ne hle hne

/-- A finite endpoint-disjoint noncrossing chord diagram supplies the literal
ordered matching consumed by the LIFO sweep.  Labels are arbitrary and do not
participate in the geometric hypotheses. -/
def noncrossingMatchingOfChordDiagram
    {K : Type u} {length : Nat}
    (chords : Finset (OrderedPathChord length))
    (hdisjoint : PairwiseEndpointDisjoint chords)
    (hnoncrossing : PairwiseNoncrossing chords)
    (label : OrderedPathChord length → K) :
    NoncrossingMatching K length where
  arcs := orderedArcList chords label
  proper := by
    intro arc harc
    rcases exists_chord_of_mem_orderedArcList chords label arc harc with
      ⟨chord, _hchord, rfl⟩
    exact chord.left_lt_right
  leftOrdered := by
    rw [orderedArcList, List.pairwise_map, List.pairwise_iff_get]
    intro first second hfirstSecond
    have hsorted := Finset.sortedLT_sort chords hfirstSecond
    have hfirstMem : chords.sort.get first ∈ chords :=
      (Finset.mem_sort (· ≤ ·)).1 (List.get_mem _ first)
    have hsecondMem : chords.sort.get second ∈ chords :=
      (Finset.mem_sort (· ≤ ·)).1 (List.get_mem _ second)
    have hne : chords.sort.get first ≠ chords.sort.get second :=
      ne_of_lt hsorted
    have hleftNe :=
      (hdisjoint _ hfirstMem _ hsecondMem hne).1
    simpa [chordArc] using
      left_lt_of_sorted_lt_of_left_ne hsorted hleftNe
  endpointDisjoint := by
    rw [orderedArcList, List.pairwise_map, List.pairwise_iff_get]
    intro first second hfirstSecond
    have hsorted := Finset.sortedLT_sort chords hfirstSecond
    have hfirstMem : chords.sort.get first ∈ chords :=
      (Finset.mem_sort (· ≤ ·)).1 (List.get_mem _ first)
    have hsecondMem : chords.sort.get second ∈ chords :=
      (Finset.mem_sort (· ≤ ·)).1 (List.get_mem _ second)
    simpa [chordArc] using
      hdisjoint _ hfirstMem _ hsecondMem (ne_of_lt hsorted)
  noncrossing := by
    rw [orderedArcList, List.pairwise_map, List.pairwise_iff_get]
    intro first second hfirstSecond
    have hsorted := Finset.sortedLT_sort chords hfirstSecond
    have hfirstMem : chords.sort.get first ∈ chords :=
      (Finset.mem_sort (· ≤ ·)).1 (List.get_mem _ first)
    have hsecondMem : chords.sort.get second ∈ chords :=
      (Finset.mem_sort (· ≤ ·)).1 (List.get_mem _ second)
    have hne : chords.sort.get first ≠ chords.sort.get second :=
      ne_of_lt hsorted
    have hleft := left_lt_of_sorted_lt_of_left_ne hsorted
      (hdisjoint _ hfirstMem _ hsecondMem hne).1
    intro hcrossing
    apply hnoncrossing _ hfirstMem _ hsecondMem hne
    left
    exact ⟨hleft, hcrossing.2.1, hcrossing.2.2⟩

/-- The LIFO stack has one entry for each physical chord crossing the sweep
cut.  This is the cardinality seam between the finite sweep representation
and the underlying chord diagram; labels do not affect it. -/
theorem stackAt_length_noncrossingMatchingOfChordDiagram
    {K : Type u} {length : Nat}
    (chords : Finset (OrderedPathChord length))
    (hdisjoint : PairwiseEndpointDisjoint chords)
    (hnoncrossing : PairwiseNoncrossing chords)
    (label : OrderedPathChord length → K)
    (cut : Fin length) :
    ((noncrossingMatchingOfChordDiagram chords hdisjoint hnoncrossing label).stackAt
        cut).length =
      (chords.filter fun chord => chord.left < cut ∧ cut ≤ chord.right).card := by
  simp only [GoertzelV24NoncrossingSweepLifo.NoncrossingMatching.stackAt,
    GoertzelV24NoncrossingSweepLifo.NoncrossingMatching.openArcs,
    noncrossingMatchingOfChordDiagram, List.length_map, List.length_reverse,
    orderedArcList, List.filter_map]
  have hnodup :
      (List.filter
        ((fun arc => decide (arc.left < cut ∧ cut ≤ arc.right)) ∘
          chordArc label)
        (chords.sort (fun first second => first ≤ second))).Nodup := by
    apply List.Nodup.filter
    simp
  rw [← List.toFinset_card_of_nodup hnodup]
  simp [chordArc]

end Mettapedia.GraphTheory.FourColor.Compositional.PathChordSweep
