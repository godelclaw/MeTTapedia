import Mettapedia.GraphTheory.PathChord

/-!
# Laminar families of ordered path chords

This file develops graph-free structure for nested chord intervals.  It is
independent of embeddings, colourings, and the four-colour development.

The `rainbowChordFamily` is the basic sharpness example: for every depth it
is an endpoint-disjoint, pairwise noncrossing laminar family of exactly that
cardinality.  Thus noncrossing, even within a single labelled sector, does
not by itself bound nesting depth.  Any such bound must use additional
geometric information.
-/

namespace Mettapedia.GraphTheory

/-! ## Laminar and fibrewise-noncrossing families -/

/-- A finite chord family is laminar when every distinct pair of endpoint
intervals is strictly nested in one direction. -/
def PairwiseLaminar {length : Nat}
    (chords : Finset (OrderedPathChord length)) : Prop :=
  ∀ first ∈ chords, ∀ second ∈ chords, first ≠ second →
    first.NestedIn second ∨ second.NestedIn first

/-- Chords carrying the same label do not cross.  The Boolean case is the
abstract combinatorial content of a two-sector noncrossing assignment. -/
def FiberwiseNoncrossing {length : Nat} {Label : Type*}
    (chords : Finset (OrderedPathChord length))
    (label : OrderedPathChord length → Label) : Prop :=
  ∀ first ∈ chords, ∀ second ∈ chords, first ≠ second →
    label first = label second → ¬ first.Crosses second

theorem fiberwiseNoncrossing_of_pairwiseNoncrossing
    {length : Nat} {Label : Type*}
    {chords : Finset (OrderedPathChord length)}
    (hnoncrossing : PairwiseNoncrossing chords)
    (label : OrderedPathChord length → Label) :
    FiberwiseNoncrossing chords label := by
  intro first hfirst second hsecond hne _
  exact hnoncrossing first hfirst second hsecond hne

theorem OrderedPathChord.not_crosses_of_nestedIn
    {length : Nat} {inner outer : OrderedPathChord length}
    (hnested : inner.NestedIn outer) : ¬ inner.Crosses outer := by
  unfold OrderedPathChord.NestedIn at hnested
  unfold OrderedPathChord.Crosses
  omega

/-! ## Rainbow families -/

/-- The `index`th chord of the depth-`depth` rainbow.  Increasing indices
move the left endpoint rightwards and the right endpoint leftwards. -/
def rainbowChord (depth : Nat) (index : Fin depth) :
    OrderedPathChord (2 * depth + 1) where
  left := ⟨index, by omega⟩
  right := ⟨2 * depth - index, by omega⟩
  left_lt_right := by
    change index.val < 2 * depth - index.val
    apply Nat.lt_sub_of_add_lt
    omega

theorem rainbowChord_injective (depth : Nat) :
    Function.Injective (rainbowChord depth) := by
  intro first second heq
  have hleft := congrArg (fun chord => chord.left.val) heq
  exact Fin.ext hleft

/-- All chords in the depth-`depth` rainbow. -/
def rainbowChordFamily (depth : Nat) :
    Finset (OrderedPathChord (2 * depth + 1)) :=
  Finset.univ.image (rainbowChord depth)

@[simp] theorem mem_rainbowChordFamily_iff
    {depth : Nat} {chord : OrderedPathChord (2 * depth + 1)} :
    chord ∈ rainbowChordFamily depth ↔
      ∃ index : Fin depth, rainbowChord depth index = chord := by
  simp [rainbowChordFamily]

@[simp] theorem card_rainbowChordFamily (depth : Nat) :
    (rainbowChordFamily depth).card = depth := by
  rw [rainbowChordFamily, Finset.card_image_of_injective _
    (rainbowChord_injective depth)]
  simp

theorem rainbowChord_nestedIn_of_lt
    {depth : Nat} {inner outer : Fin depth}
    (hlt : outer < inner) :
    (rainbowChord depth inner).NestedIn (rainbowChord depth outer) := by
  unfold rainbowChord OrderedPathChord.NestedIn
  simp only
  constructor
  · exact hlt
  · exact Nat.sub_lt_sub_left (by omega) hlt

theorem rainbowChordFamily_pairwiseLaminar (depth : Nat) :
    PairwiseLaminar (rainbowChordFamily depth) := by
  intro first hfirst second hsecond hne
  rw [mem_rainbowChordFamily_iff] at hfirst hsecond
  rcases hfirst with ⟨firstIndex, rfl⟩
  rcases hsecond with ⟨secondIndex, rfl⟩
  have hindexNe : firstIndex ≠ secondIndex := by
    intro heq
    exact hne (congrArg (rainbowChord depth) heq)
  rcases lt_or_gt_of_ne hindexNe with hlt | hgt
  · exact Or.inr (rainbowChord_nestedIn_of_lt hlt)
  · exact Or.inl (rainbowChord_nestedIn_of_lt hgt)

theorem rainbowChordFamily_pairwiseNoncrossing (depth : Nat) :
    PairwiseNoncrossing (rainbowChordFamily depth) := by
  intro first hfirst second hsecond hne
  rcases rainbowChordFamily_pairwiseLaminar depth
      first hfirst second hsecond hne with hnested | hnested
  · exact OrderedPathChord.not_crosses_of_nestedIn hnested
  · intro hcross
    exact OrderedPathChord.not_crosses_of_nestedIn hnested (by
      unfold OrderedPathChord.Crosses at hcross ⊢
      tauto)

theorem rainbowChordFamily_pairwiseEndpointDisjoint (depth : Nat) :
    PairwiseEndpointDisjoint (rainbowChordFamily depth) := by
  intro first hfirst second hsecond hne
  rw [mem_rainbowChordFamily_iff] at hfirst hsecond
  rcases hfirst with ⟨firstIndex, rfl⟩
  rcases hsecond with ⟨secondIndex, rfl⟩
  have hindexNe : firstIndex.val ≠ secondIndex.val := by
    intro heq
    exact hne (congrArg (rainbowChord depth) (Fin.ext heq))
  unfold rainbowChord
  simp only
  constructor
  · exact Fin.ne_of_val_ne hindexNe
  constructor
  · intro heq
    have hval := congrArg Fin.val heq
    change firstIndex.val = 2 * depth - secondIndex.val at hval
    have hrightLower : depth ≤ 2 * depth - secondIndex.val := by
      apply Nat.le_sub_of_add_le
      omega
    omega
  constructor
  · intro heq
    have hval := congrArg Fin.val heq
    change 2 * depth - firstIndex.val = secondIndex.val at hval
    have hrightLower : depth ≤ 2 * depth - firstIndex.val := by
      apply Nat.le_sub_of_add_le
      omega
    omega
  · intro heq
    have hval := congrArg Fin.val heq
    change 2 * depth - firstIndex.val =
      2 * depth - secondIndex.val at hval
    rcases lt_or_gt_of_ne hindexNe with hlt | hgt
    · have hstrict : 2 * depth - secondIndex.val <
          2 * depth - firstIndex.val :=
        Nat.sub_lt_sub_left (by omega) hlt
      omega
    · have hstrict : 2 * depth - firstIndex.val <
          2 * depth - secondIndex.val :=
        Nat.sub_lt_sub_left (by omega) hgt
      omega

/-- Arbitrarily deep endpoint-disjoint noncrossing families exist even when
every chord receives the same sector label. -/
theorem exists_constant_sector_noncrossing_family (depth : Nat) :
    ∃ (length : Nat) (chords : Finset (OrderedPathChord length))
        (sector : OrderedPathChord length → Bool),
      chords.card = depth ∧
      PairwiseEndpointDisjoint chords ∧
      PairwiseLaminar chords ∧
      FiberwiseNoncrossing chords sector ∧
      ∀ chord ∈ chords, sector chord = false := by
  refine ⟨2 * depth + 1, rainbowChordFamily depth, fun _ => false,
    card_rainbowChordFamily depth,
    rainbowChordFamily_pairwiseEndpointDisjoint depth,
    rainbowChordFamily_pairwiseLaminar depth, ?_, ?_⟩
  · exact fiberwiseNoncrossing_of_pairwiseNoncrossing
      (rainbowChordFamily_pairwiseNoncrossing depth) _
  · simp

/-- Endpoint disjointness, laminarity, and fibrewise noncrossing impose no
uniform bound on the number of chords.  In particular, a bounded-local-
complexity conclusion needs information beyond these three interval-order
properties. -/
theorem no_uniform_cardinality_bound_of_laminar_fiberwiseNoncrossing :
    ¬ ∃ bound : Nat,
      ∀ (length : Nat) (chords : Finset (OrderedPathChord length))
        (sector : OrderedPathChord length → Bool),
        PairwiseEndpointDisjoint chords →
        PairwiseLaminar chords →
        FiberwiseNoncrossing chords sector →
        chords.card ≤ bound := by
  rintro ⟨bound, hbound⟩
  obtain ⟨length, chords, sector, hcard, hdisjoint, hlaminar,
      hnoncrossing, _hconstant⟩ :=
    exists_constant_sector_noncrossing_family (bound + 1)
  have hle := hbound length chords sector hdisjoint hlaminar hnoncrossing
  omega

end Mettapedia.GraphTheory
