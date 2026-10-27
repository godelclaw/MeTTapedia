import Std

/-!
# Captured maxima over ordered native records

A retained maximum and the absence of keys above it form a sufficient read
scope. Earlier rows need not be captured. An empty range needs the whole
absence observation; a point read at a retained maximum alone is insufficient.

The executable witness is replayed through the actual MeTTa maximum query and
scoped store commits. Key decoding/iterator coverage, native memory and
filesystem behavior remain implementation obligations. The integer embedding
below models its arithmetic, not the C byte serializer.
-/

namespace Mettapedia.Machines.NativeStoreMaximum

abbrev Records (α : Type) := Int → Option α

def IsMaximum {α : Type} (rows : Records α) (maximum : Int) : Prop :=
  rows maximum ≠ none ∧ ∀ key, maximum < key → rows key = none

theorem maximum_preserved_by_suffix_reads {α : Type}
    (before after : Records α) (maximum : Int)
    (original : IsMaximum before maximum)
    (same : ∀ key, maximum ≤ key → before key = after key) :
    IsMaximum after maximum := by
  constructor
  · intro missing
    exact original.1 ((same maximum (Int.le_refl maximum)).trans missing)
  · intro key later
    calc
      after key = before key := (same key (by omega)).symm
      _ = none := original.2 key later

theorem empty_preserved_by_complete_absence_reads {α : Type}
    (before after : Records α) (empty : ∀ key, before key = none)
    (same : ∀ key, before key = after key) : ∀ key, after key = none := by
  intro key
  exact (same key).symm.trans (empty key)

def replace {α : Type} (rows : Records α) (changed : Int) (value : Option α) : Records α :=
  fun key => if key = changed then value else rows key

theorem replacement_below_maximum_preserves_suffix {α : Type}
    (rows : Records α) (maximum changed : Int) (value : Option α)
    (earlier : changed < maximum) :
    ∀ key, maximum ≤ key → rows key = replace rows changed value key := by
  intro key lower
  have different : key ≠ changed := by omega
  simp [replace, different]

def bias : Int := 9223372036854775808
def orderedInteger (value : Int) : Int := value + bias
def decodeInteger (value : Int) : Int := value - bias

theorem signed_key_round_trip (value : Int) :
    decodeInteger (orderedInteger value) = value := by
  simp [decodeInteger, orderedInteger]

theorem signed_key_order (left right : Int) :
    orderedInteger left < orderedInteger right ↔ left < right := by
  simp [orderedInteger]

theorem signed_key_fits_exactly_in_unsigned64 (value : Int) :
    (0 ≤ orderedInteger value ∧ orderedInteger value < 18446744073709551616) ↔
      (-9223372036854775808 ≤ value ∧ value ≤ 9223372036854775807) := by
  simp only [orderedInteger, bias]
  omega

def before : Records Nat := fun key =>
  if key = 9 then some 0 else if key = 1 then some 1 else none
def below : Records Nat := replace before 1 (some 2)
def above : Records Nat := replace before 10 (some 2)

theorem original_maximum : IsMaximum before 9 := by
  constructor
  · simp [before]
  · intro key later
    have nine : key ≠ 9 := by omega
    have one : key ≠ 1 := by omega
    simp [before, nine, one]

theorem lower_mutation_keeps_the_maximum : IsMaximum below 9 :=
  maximum_preserved_by_suffix_reads before below 9 original_maximum
    (replacement_below_maximum_preserves_suffix before 9 1 (some 2) (by decide))

theorem point_only_reads_miss_a_new_maximum : before 9 = above 9 ∧ ¬ IsMaximum above 9 := by
  constructor
  · simp [above, replace]
  · intro alleged
    have missing := alleged.2 10 (by decide)
    simp [above, replace] at missing

def validation (includeAbsence : Bool) (after : Records Nat) : String :=
  let observed := if includeAbsence then [9, 10] else [9]
  if observed.all (fun key => before key == after key) then "accepted" else "conflict"

theorem finite_witness :
    validation true below = "accepted" ∧ validation true above = "conflict" ∧
    validation false above = "accepted" := by decide

def trace : String :=
  s!"MAXIMUM_SCOPE_TRACE 9 {validation true below} {validation true above} {validation false above}"

end Mettapedia.Machines.NativeStoreMaximum

#eval IO.println Mettapedia.Machines.NativeStoreMaximum.trace
