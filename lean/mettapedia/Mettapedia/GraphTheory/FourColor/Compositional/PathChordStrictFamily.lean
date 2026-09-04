import Mettapedia.GraphTheory.FourColor.Compositional.NoncrossingPairingSweep
import Mettapedia.GraphTheory.FourColor.Compositional.PathChordSweep

/-!
# Strict chord families extracted from noncrossing LIFO stacks

This is the representation bridge from a deep stack of anonymous sweep
labels back to the original path chords.  The stack depth counts arcs open at
one cut.  Those arcs are strictly nested, and every arc in the generated
matching remembers the unique ordered chord from which it came.

The result is graph-free and independent of four-colour semantics.
-/

namespace Mettapedia.GraphTheory.FourColor.Compositional

namespace PathChordStrictFamily

open GoertzelV24NoncrossingSweepLifo
open Mettapedia.GraphTheory
open NoncrossingPairingSweep
open PathChordSweep

universe u

/-- An indexed family of original path chords, all selected from one finite
diagram and strictly nested in the displayed order. -/
def HasStrictlyNestedChordFamily {n : Nat}
    (chords : Finset (OrderedPathChord n)) (length : Nat) : Prop :=
  ∃ family : Fin length → OrderedPathChord n,
    (∀ i, family i ∈ chords) ∧
      ∀ i j, i < j → (family j).NestedIn (family i)

/-- A stack with at least `length` open arcs in the matching generated from a
finite chord diagram contains `length` original chords in strict nesting
order. -/
theorem hasStrictlyNestedChordFamily_of_stackAt_length_le
    {K : Type u} {n : Nat}
    (chords : Finset (OrderedPathChord n))
    (hdisjoint : PairwiseEndpointDisjoint chords)
    (hnoncrossing : PairwiseNoncrossing chords)
    (label : OrderedPathChord n → K)
    (cut : Fin n) (length : Nat)
    (hdepth : length ≤
      ((noncrossingMatchingOfChordDiagram chords hdisjoint hnoncrossing label
        ).stackAt cut).length) :
    HasStrictlyNestedChordFamily chords length := by
  classical
  let matching :=
    noncrossingMatchingOfChordDiagram chords hdisjoint hnoncrossing label
  let opened := matching.openArcs cut
  have hopened : length ≤ opened.length := by
    simpa only [matching, opened,
      stackAt_length_eq_openArcs_length] using hdepth
  let arcIndex (i : Fin length) : Fin opened.length :=
    ⟨i.val, lt_of_lt_of_le i.isLt hopened⟩
  have harcMem (i : Fin length) : opened.get (arcIndex i) ∈ matching.arcs := by
    exact (List.mem_filter.mp (opened.get_mem (arcIndex i))).1
  have hsource (i : Fin length) :
      ∃ chord ∈ chords,
        PathChordSweep.chordArc label chord = opened.get (arcIndex i) := by
    exact exists_chord_of_mem_orderedArcList chords label
      (opened.get (arcIndex i)) (by
        simpa only [matching, noncrossingMatchingOfChordDiagram] using
          harcMem i)
  choose family hfamilyMem hfamilyArc using hsource
  refine ⟨family, hfamilyMem, ?_⟩
  intro i j hij
  have hindex : arcIndex i < arcIndex j := by
    apply Fin.mk_lt_mk.mpr
    exact hij
  have hnested :=
    (openArcs_pairwise_strictlyNested matching cut).rel_get_of_lt hindex
  unfold OrderedPathChord.NestedIn
  have hleftI : (family i).left = (opened.get (arcIndex i)).left :=
    congrArg (fun arc : LabeledArc K n => arc.left) (hfamilyArc i)
  have hleftJ : (family j).left = (opened.get (arcIndex j)).left :=
    congrArg (fun arc : LabeledArc K n => arc.left) (hfamilyArc j)
  have hrightI : (family i).right = (opened.get (arcIndex i)).right :=
    congrArg (fun arc : LabeledArc K n => arc.right) (hfamilyArc i)
  have hrightJ : (family j).right = (opened.get (arcIndex j)).right :=
    congrArg (fun arc : LabeledArc K n => arc.right) (hfamilyArc j)
  rw [hleftI, hleftJ, hrightI, hrightJ]
  exact hnested

/-- Strict inequality in the usual deep-stack orientation is the convenient
consumer form of the extraction theorem. -/
theorem hasStrictlyNestedChordFamily_of_lt_stackAt_length
    {K : Type u} {n : Nat}
    (chords : Finset (OrderedPathChord n))
    (hdisjoint : PairwiseEndpointDisjoint chords)
    (hnoncrossing : PairwiseNoncrossing chords)
    (label : OrderedPathChord n → K)
    (cut : Fin n) (length : Nat)
    (hdepth : length - 1 <
      ((noncrossingMatchingOfChordDiagram chords hdisjoint hnoncrossing label
        ).stackAt cut).length) :
    HasStrictlyNestedChordFamily chords length := by
  apply hasStrictlyNestedChordFamily_of_stackAt_length_le
    chords hdisjoint hnoncrossing label cut length
  omega

end PathChordStrictFamily

end Mettapedia.GraphTheory.FourColor.Compositional
