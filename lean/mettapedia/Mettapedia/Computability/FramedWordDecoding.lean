import Mettapedia.Computability.WordTemplateMachine

/-!
# Independent decoding of complete framed words

The existing indexed-template frame has a delimiter outside the cell alphabet.
The decoder retains empty fields and duplicate occurrences and refuses an
unterminated final field. It operates on the emitted word, without access to
the values from which that word was generated.
-/
set_option autoImplicit false

namespace Mettapedia.Computability.WordTemplateMachine.Indexed

variable {Cell : Type}

def decodeScan : List (Option Cell) → List Cell → List (List Cell) → Option (List (List Cell))
  | [], [], complete => some complete.reverse
  | [], _ :: _, _ => none
  | none :: rest, current, complete => decodeScan rest [] (current.reverse :: complete)
  | some cell :: rest, current, complete => decodeScan rest (cell :: current) complete

def decodeFrames (word : List (Option Cell)) : Option (List (List Cell)) :=
  decodeScan word [] []

theorem decodeScan_field (word current : List Cell)
    (rest : List (Option Cell)) (complete : List (List Cell)) :
    decodeScan (word.map some ++ none :: rest) current complete =
      decodeScan rest [] ((current.reverse ++ word) :: complete) := by
  induction word generalizing current with
  | nil => simp [decodeScan]
  | cons cell word ih =>
      simpa [decodeScan, List.reverse_cons, List.append_assoc] using ih (cell :: current)

theorem decodeScan_frame (words complete : List (List Cell)) :
    decodeScan (frame words) [] complete = some (complete.reverse ++ words) := by
  induction words generalizing complete with
  | nil => simp [frame, decodeScan]
  | cons word rest ih =>
      simp only [frame, List.flatMap_cons, List.append_assoc, List.cons_append,
        List.nil_append] at *
      rw [decodeScan_field]
      simpa [List.reverse_cons, List.append_assoc] using ih (word :: complete)

/-- Inverse of the original physical framing, including every empty field. -/
theorem decodeFrames_frame (words : List (List Cell)) :
    decodeFrames (frame words) = some words := by
  simpa [decodeFrames] using decodeScan_frame words []

theorem frame_injective : Function.Injective (frame (Γ := Cell)) := by
  intro first second same
  have decoded := congrArg decodeFrames same
  simpa only [decodeFrames_frame, Option.some.injEq] using decoded

/-- Successful decoding accounts for every physical input cell, including the
delimiters; it cannot accept an unconsumed suffix. -/
theorem decodeScan_sound (word : List (Option Cell)) (current : List Cell)
    (complete : List (List Cell)) {fields : List (List Cell)}
    (decoded : decodeScan word current complete = some fields) :
    frame fields = frame complete.reverse ++ current.reverse.map some ++ word := by
  induction word generalizing current complete with
  | nil =>
      cases current with
      | nil =>
          simp only [decodeScan, Option.some.injEq] at decoded
          subst fields
          simp
      | cons cell rest => simp [decodeScan] at decoded
  | cons cell rest ih =>
      cases cell with
      | none =>
          have result := ih [] (current.reverse :: complete) decoded
          simpa [List.reverse_cons, frame, List.flatMap_append, List.append_assoc]
            using result
      | some cell =>
          have result := ih (cell :: current) complete decoded
          simpa [List.reverse_cons, List.map_append, List.append_assoc] using result

theorem decodeFrames_eq_some_iff (word : List (Option Cell)) (fields : List (List Cell)) :
    decodeFrames word = some fields ↔ word = frame fields := by
  constructor
  · intro decoded
    have result := decodeScan_sound word [] [] decoded
    simpa [frame] using result.symm
  · rintro rfl
    exact decodeFrames_frame fields

namespace DecodingControls

theorem empty_vector : decodeFrames ([] : List (Option Cell)) = some [] := rfl

theorem empty_field : decodeFrames ([none] : List (Option Cell)) = some [[]] := rfl

theorem empty_field_is_not_empty_vector :
    decodeFrames ([none] : List (Option Cell)) ≠ decodeFrames [] := by
  simp [decodeFrames, decodeScan]

theorem unterminated_field (cell : Cell) : decodeFrames [some cell] = none := rfl

theorem mixed_fields (cell : Cell) :
    decodeFrames [none, some cell, none, none, some cell, none] =
      some [[], [cell], [], [cell]] := rfl

end DecodingControls
end Mettapedia.Computability.WordTemplateMachine.Indexed
