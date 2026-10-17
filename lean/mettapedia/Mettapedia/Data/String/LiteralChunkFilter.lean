import Mathlib.Data.List.Infix

/-!
# Literal occurrences across chunk seams

The input units here are already decoded and case-normalized. An occurrence
lies entirely within the prior chunk, or survives in one pattern-length suffix
of that chunk followed by the new chunk. Cropping that suffix cannot suppress
a crossing occurrence. This is a search-filter law, not native UTF-8 decoding,
byte cropping, case normalization, or matcher adequacy.
-/

set_option autoImplicit false

namespace Mettapedia.Data.String.LiteralChunkFilter

universe u
variable {α : Type u}

def OccursAt (needle input : List α) (position : Nat) : Prop :=
  (input.drop position).take needle.length = needle

def Occurs (needle input : List α) : Prop := ∃ position, OccursAt needle input position

theorem occurrence_after_drop (needle input : List α) (position cut : Nat)
    (earlier : cut ≤ position) :
    OccursAt needle (input.drop cut) (position - cut) ↔ OccursAt needle input position := by
  simp only [OccursAt, List.drop_drop]
  have same : cut + (position - cut) = position := by omega
  rw [same]

theorem occurrence_before_seam (needle first second : List α) (position : Nat)
    (before : position + needle.length ≤ first.length)
    (occurrence : OccursAt needle (first ++ second) position) :
    OccursAt needle first position := by
  have positionBound : position ≤ first.length := by omega
  have takeBound : needle.length ≤ (first.drop position).length := by
    rw [List.length_drop]
    omega
  simpa only [OccursAt, List.drop_append_of_le_length positionBound,
    List.take_append_of_le_length takeBound] using occurrence

theorem crossing_survives_suffix (needle first second : List α) (position : Nat)
    (crossing : first.length < position + needle.length)
    (occurrence : OccursAt needle (first ++ second) position) :
    OccursAt needle (first.drop (first.length - needle.length) ++ second)
      (position - (first.length - needle.length)) := by
  have earlier : first.length - needle.length ≤ position := by omega
  have suffixBound : first.length - needle.length ≤ first.length := Nat.sub_le _ _
  rw [← List.drop_append_of_le_length suffixBound]
  exact (occurrence_after_drop needle (first ++ second) position
    (first.length - needle.length) earlier).mpr occurrence

theorem seam_filter_complete (needle first second : List α)
    (occurrence : Occurs needle (first ++ second)) :
    Occurs needle first ∨ Occurs needle (first.drop (first.length - needle.length) ++ second) := by
  obtain ⟨position, found⟩ := occurrence
  by_cases before : position + needle.length ≤ first.length
  · exact Or.inl ⟨position, occurrence_before_seam needle first second position before found⟩
  · have crossing : first.length < position + needle.length := by omega
    exact Or.inr ⟨_, crossing_survives_suffix needle first second position crossing found⟩

example : OccursAt ['b', 'c'] (['a', 'b'] ++ ['c', 'd']) 1 := by simp [OccursAt]
example : OccursAt ['b', 'c'] ((['a', 'b'].drop 0) ++ ['c', 'd']) 1 := by simp [OccursAt]
example : ¬ Occurs ['b', 'c'] ['c', 'd'] := by
  rintro ⟨position, found⟩
  cases position with
  | zero => simp [OccursAt] at found
  | succ position =>
      cases position with
      | zero => simp [OccursAt] at found
      | succ position => simp [OccursAt, List.drop] at found

end Mettapedia.Data.String.LiteralChunkFilter
