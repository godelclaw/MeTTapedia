import Mettapedia.Algebra.SupportTensor
import Mathlib.Data.List.Sort

/-!
Ranking sparse entries need not materialize names or repack scalar scores.
Increasing support coordinates preserve the input-position tie order. After
ranking, an arbitrary injective catalog renaming can carry the rank bonuses.

The bonus operation is arbitrary: in particular, this law does not remove
an initial rounded addition or assume an IEEE arithmetic identity. Scores
are ordered values; rejecting nonfinite native scores is a separate gate.
These are operation correspondence laws, not verification of a native sort.
-/

set_option autoImplicit false

namespace Mettapedia.Algorithms.Retrieval.RankedCoordinateProjection

open Mettapedia.Algebra.SupportTensor

variable {I J K S R : Type*}

/-- Descending score, then ascending original coordinate. -/
def before [LinearOrder I] [LinearOrder S] (left right : I × S) : Bool :=
  decide (right.2 < left.2 ∨ (left.2 = right.2 ∧ left.1 ≤ right.1))

def rename (coordinate : I → J) (row : I × S) : J × S :=
  (coordinate row.1, row.2)

theorem before_rename [LinearOrder I] [LinearOrder J] [LinearOrder S]
    (coordinate : I → J) (increasing : StrictMono coordinate) (left right : I × S) :
    before (rename coordinate left) (rename coordinate right) = before left right := by
  simp only [before, rename, increasing.le_iff_le]

/-- Sorting compressed row positions and sorting their increasing support
coordinates give exactly the same ranked occurrence sequence. -/
theorem sort_rename [LinearOrder I] [LinearOrder J] [LinearOrder S]
    (coordinate : I → J) (increasing : StrictMono coordinate) (rows : List (I × S)) :
    (rows.map (rename coordinate)).mergeSort before =
      (rows.mergeSort before).map (rename coordinate) := by
  symm
  apply List.map_mergeSort
  intro left _ right _
  exact (before_rename coordinate increasing left right).symm

/-- Each ranked occurrence receives its positional bonus, without reducing
or reassociating the caller's scalar operation. -/
def rankedBonuses [LinearOrder I] [LinearOrder S]
    (bonus : Nat → R) (rows : List (I × S)) : List (I × R) :=
  (rows.mergeSort before).zipIdx.map fun entry => (entry.1.1, bonus entry.2)

theorem rankedBonuses_rename [LinearOrder I] [LinearOrder J] [LinearOrder S]
    (coordinate : I → J) (increasing : StrictMono coordinate)
    (bonus : Nat → R) (rows : List (I × S)) :
    rankedBonuses bonus (rows.map (rename coordinate)) =
      (rankedBonuses bonus rows).map (rename coordinate) := by
  simp only [rankedBonuses, sort_rename coordinate increasing, List.zipIdx_map,
    List.map_map, Function.comp_def, rename]
  rfl

/-- Catalog coordinates need not have ranking order. Renaming after ranking
retains every bonus and its target, including stored zero bonuses. -/
theorem catalog_projection [LinearOrder I] [LinearOrder J] [LinearOrder S]
    (support : I → J) (increasing : StrictMono support) (catalog : J → K)
    (bonus : Nat → R) (rows : List (I × S)) :
    (rankedBonuses bonus (rows.map (rename support))).map (rename catalog) =
      (rankedBonuses bonus rows).map (rename (catalog ∘ support)) := by
  rw [rankedBonuses_rename support increasing]
  simp only [List.map_map, Function.comp_def, rename]
  rfl

/-- The list law also preserves the support-aware tensor observation; no
implicit filling or dropping of zeros is involved. -/
theorem catalog_lookup [LinearOrder I] [LinearOrder J] [LinearOrder S] [DecidableEq K]
    (support : I → J) (increasing : StrictMono support) (catalog : J → K)
    (bonus : Nat → R) (rows : List (I × S)) :
    lookupFirst ((rankedBonuses bonus (rows.map (rename support))).map (rename catalog)) =
      lookupFirst ((rankedBonuses bonus rows).map (rename (catalog ∘ support))) := by
  rw [catalog_projection support increasing]

theorem rankedBonuses_coordinates [LinearOrder I] [LinearOrder S]
    (bonus : Nat → R) (rows : List (I × S)) :
    (rankedBonuses bonus rows).map Prod.fst = (rows.mergeSort before).map Prod.fst := by
  calc
    _ = ((rows.mergeSort before).zipIdx.map Prod.fst).map Prod.fst := by
      simp only [rankedBonuses, List.map_map, Function.comp_def]
    _ = _ := by rw [List.zipIdx_map_fst]

/-- Unique source identities and an injective catalog map justify constructing
a duplicate-rejecting sparse tensor from the projected bonuses. -/
theorem catalog_coordinates_unique [LinearOrder I] [LinearOrder S]
    (catalog : I → K) (injective : Function.Injective catalog)
    (bonus : Nat → R) (rows : List (I × S)) (unique : (rows.map Prod.fst).Nodup) :
    (((rankedBonuses bonus rows).map (rename catalog)).map Prod.fst).Nodup := by
  have sortedUnique := ((List.mergeSort_perm rows before).map Prod.fst).nodup_iff.mpr unique
  have rankedUnique : ((rankedBonuses bonus rows).map Prod.fst).Nodup := by
    rw [rankedBonuses_coordinates]
    exact sortedUnique
  simpa only [List.map_map, Function.comp_def, rename] using rankedUnique.map injective

/-- A bounded catalog ordinal is the low digit of an occurrence-order key.
This keeps first-query encounter order ahead of catalog order in score ties. -/
def occurrenceKey (width first ordinal : Nat) : Nat := first * width + ordinal

private theorem occurrenceKey_earlier {width left right low high : Nat}
    (earlier : left < right) (bounded : low < width) :
    occurrenceKey width left low < occurrenceKey width right high := by
  calc
    left * width + low < left * width + width := Nat.add_lt_add_left bounded _
    _ = (left + 1) * width := by rw [Nat.add_mul, Nat.one_mul]
    _ ≤ right * width := Nat.mul_le_mul_right width (by omega)
    _ ≤ right * width + high := Nat.le_add_right _ _

theorem occurrenceKey_order {width left right low high : Nat}
    (leftBound : low < width) (rightBound : high < width) :
    occurrenceKey width left low < occurrenceKey width right high ↔
      left < right ∨ (left = right ∧ low < high) := by
  constructor
  · intro beforeKey
    rcases lt_trichotomy left right with earlier | same | later
    · exact Or.inl earlier
    · subst right
      exact Or.inr ⟨rfl, Nat.lt_of_add_lt_add_left beforeKey⟩
    · exact False.elim (Nat.lt_asymm beforeKey (occurrenceKey_earlier later rightBound))
  · rintro (earlier | ⟨same, lowBefore⟩)
    · exact occurrenceKey_earlier earlier leftBound
    · subst right
      exact Nat.add_lt_add_left lowBefore _

/-- The original catalog ordinal is recovered without a name lookup. -/
theorem occurrenceKey_decode {width ordinal : Nat} (first : Nat)
    (bounded : ordinal < width) : occurrenceKey width first ordinal % width = ordinal := by
  simp [occurrenceKey, Nat.add_mod, Nat.mod_eq_of_lt bounded]

theorem occurrenceKey_unique {width first next ordinal other : Nat}
    (bounded : ordinal < width) (otherBounded : other < width)
    (same : occurrenceKey width first ordinal = occurrenceKey width next other) :
    first = next ∧ ordinal = other := by
  have lows : ordinal = other := by
    simpa only [occurrenceKey_decode first bounded, occurrenceKey_decode next otherBounded]
      using congrArg (· % width) same
  have noEarlier : ¬ first < next := by
    intro earlier
    have impossible := occurrenceKey_earlier (high := other) earlier bounded
    rw [same] at impossible
    exact Nat.lt_irrefl _ impossible
  have noLater : ¬ next < first := by
    intro later
    have impossible := occurrenceKey_earlier (high := ordinal) later otherBounded
    rw [same] at impossible
    exact Nat.lt_irrefl _ impossible
  exact ⟨by omega, lows⟩

example : rankedBonuses (fun rank => rank + 10)
    ([(0, 4), (2, 8), (4, 8)] : List (Nat × Nat)) = [(2, 10), (4, 11), (0, 12)] := by
  simp [rankedBonuses, List.mergeSort, before, List.zipIdx]

/-- Reversing support coordinates changes equal-score ties, so arbitrary
renaming cannot be moved across ranking. -/
example :
    (rankedBonuses id ([(0, 1), (1, 1)] : List (Nat × Nat))).map (rename (1 - ·)) ≠
      rankedBonuses id (([(0, 1), (1, 1)] : List (Nat × Nat)).map (rename (1 - ·))) := by
  simp [rankedBonuses, List.mergeSort, before, List.zipIdx, rename]

example : occurrenceKey 4 0 3 < occurrenceKey 4 1 0 := by decide

/-- Without a bounded low digit the coordinate can alias the next query. -/
example : occurrenceKey 4 0 4 = occurrenceKey 4 1 0 := by decide

example :
    (((rankedBonuses id ([(0, 1), (1, 1)] : List (Nat × Nat))).map
      (rename (fun _ => 0))).map Prod.fst).Nodup = False := by
  simp [rankedBonuses, List.mergeSort, before, List.zipIdx, rename]

#print axioms sort_rename
#print axioms rankedBonuses_rename
#print axioms catalog_projection
#print axioms catalog_lookup
#print axioms catalog_coordinates_unique
#print axioms occurrenceKey_order
#print axioms occurrenceKey_decode
#print axioms occurrenceKey_unique

end Mettapedia.Algorithms.Retrieval.RankedCoordinateProjection
