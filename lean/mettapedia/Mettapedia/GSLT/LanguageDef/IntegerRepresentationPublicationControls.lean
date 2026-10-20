import Mettapedia.GSLT.LanguageDef.IntegerRepresentationPublication
import Mettapedia.GSLT.LanguageDef.IntegerRepresentationRetainedCallControls

/-! # Publication, subsequent dispatch and unsafe narrowing controls -/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.IntegerRepresentationExternalCall.Retained.Publication.Controls

open ArithmeticExternalCallPilot

def provider : Provider Int String := fun operation left right => .ok (operation.fn left right)

theorem provider_sound : SuccessfulSound id provider := by
  intro operation left right result _ returned
  cases returned
  rfl

def narrowStored : Narrow Retained.Controls.decode where
  attempt stored := integerNarrow.attempt stored.value
  correct stored word accepted := integerNarrow.correct stored.value word accepted

def checks : List (String × Bool) := [
  ("large cancellation publishes a word",
    add integerNarrow id provider (.inr (2^128)) (.inr (-(2^128) + 7)) == .ok (.inl 7)),
  ("positive overflow remains storage",
    add integerNarrow id provider (.inl (Int64.ofInt (2^63 - 1))) (.inl 1) == .ok (.inr (2^63))),
  ("negative overflow remains storage",
    add integerNarrow id provider (.inl (Int64.ofInt (-(2^63)))) (.inl (-1)) == .ok (.inr (-(2^63) - 1))),
  ("minimum signed word is admitted", publish integerNarrow (.inr (-(2^63))) == .inl (Int64.ofInt (-(2^63)))),
  ("maximum signed word is admitted", publish integerNarrow (.inr (2^63 - 1)) == .inl (Int64.ofInt (2^63 - 1))),
  ("declined narrowing retains storage", publish integerNarrow (.inr (2^100)) == .inr (2^100)),
  ("wrapped zero is refused", integerNarrow.attempt (2^64) == none),
  ("sequence uses the narrowed intermediate",
    addMany integerNarrow id provider (.inr (2^128)) [.inr (-(2^128) + 7), .inl 3] == .ok (.inl 10)),
  ("successful publication can release provenance",
    addMany narrowStored Retained.Controls.encode Retained.Controls.limited
      (.inr ⟨7, 3⟩) [.inl 1, .inl 1] == .ok (.inl 9)),
  ("retaining the same provenance can exhaust the provider",
    Retained.addMany Retained.Controls.encode Retained.Controls.limited
      (.inr ⟨7, 3⟩) [.inl 1, .inl 1] == .error "resource-exhausted"),
  ("publication does not hide a failed call",
    add narrowStored Retained.Controls.encode Retained.Controls.limited
      (.inr ⟨7, 4⟩) (.inl 1) == .error "resource-exhausted")]

theorem all_checks : checks.all (·.2) = true := by decide +kernel

/-- A narrowing function that simply truncates fails the guarded-transfer
law; the wrapped result would change an actual integer observation. -/
theorem unchecked_truncation_not_sound :
    ¬ (∀ value : Int, (Int64.ofInt value).toInt = value) := by
  intro sound
  have different : (Int64.ofInt (2^64)).toInt ≠ (2^64 : Int) := by decide +kernel
  exact different (sound (2^64))

theorem cancellation_sequence_meaning :
    resultInteger id (Sum.inl (10 : Int64) : Value Int) = (2^128 : Int) + (-(2^128) + 7 + 3) := by
  have returned : addMany integerNarrow id provider (.inr (2^128))
      [.inr (-(2^128) + 7), .inl 3] = .ok (.inl 10) := by decide +kernel
  have meaning := addMany_sound integerNarrow id (fun _ => rfl)
    provider provider_sound _ _ _ returned
  exact meaning

end Mettapedia.GSLT.LanguageDef.IntegerRepresentationExternalCall.Retained.Publication.Controls
