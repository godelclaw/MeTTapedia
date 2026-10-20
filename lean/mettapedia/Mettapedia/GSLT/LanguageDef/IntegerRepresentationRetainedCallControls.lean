import Mettapedia.GSLT.LanguageDef.IntegerRepresentationRetainedCall

/-! # Retained operands, promotion and resource-failure controls -/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.IntegerRepresentationExternalCall.Retained.Controls

open ArithmeticExternalCallPilot

/-- The generation distinguishes reusing a stored operand from re-encoding
its integer. It models provenance, not a claim about an actual allocator. -/
structure Stored where
  value : Int
  generation : Nat
  deriving DecidableEq, Repr

def encode (value : Int) : Stored := ⟨value, 0⟩
def decode (value : Stored) : Int := value.value

theorem roundtrip : Function.LeftInverse decode encode := fun _ => rfl

def provider : Provider Stored String := fun operation left right =>
  .ok ⟨operation.fn left.value right.value, max left.generation right.generation + 1⟩

theorem provider_sound : SuccessfulSound decode provider := by
  intro operation left right result _ returned
  cases returned
  rfl

def limited : Provider Stored String := fun operation left right =>
  if left.generation < 4 && right.generation < 4 then provider operation left right
  else .error "resource-exhausted"

theorem limited_sound : SuccessfulSound decode limited := by
  intro operation left right result defined returned
  unfold limited at returned
  split at returned
  · exact provider_sound operation left right result defined returned
  · cases returned

def checks : List (String × Bool) := [
  ("small words stay words", add encode provider (.inl 2) (.inl 3) == .ok (.inl 5)),
  ("signed overflow promotes", add encode provider (.inl (Int64.ofInt (2^63 - 1))) (.inl 1) ==
    .ok (.inr ⟨2^63, 1⟩)),
  ("stored operands retain generations", add encode provider (.inr ⟨8, 7⟩) (.inr ⟨9, 12⟩) ==
    .ok (.inr ⟨17, 13⟩)),
  ("mixed operands promote only the word", add encode provider (.inr ⟨2^128, 7⟩) (.inl 1) ==
    .ok (.inr ⟨2^128 + 1, 8⟩)),
  ("chain reuses stored results", addMany encode provider (.inr ⟨2^128, 7⟩)
    [.inr ⟨1, 12⟩, .inr ⟨2, 4⟩] == .ok (.inr ⟨2^128 + 3, 14⟩)),
  ("chain does not reset provenance", addMany encode provider (.inr ⟨2^128, 7⟩)
    [.inr ⟨1, 12⟩, .inr ⟨2, 4⟩] != .ok (.inr ⟨2^128 + 3, 1⟩)),
  ("fresh fallback available", add encode limited (.inr (encode 7)) (.inr (encode 1)) ==
    .ok (.inr ⟨8, 1⟩)),
  ("retained fallback can fail", add encode limited (.inr ⟨7, 4⟩) (.inr (encode 1)) ==
    .error "resource-exhausted"),
  ("failure stops the sequence", addMany encode limited (.inr ⟨7, 4⟩) [.inl 1, .inl 2] ==
    .error "resource-exhausted")]

theorem all_checks : checks.all (·.2) = true := by decide +kernel

/-- Availability on freshly encoded values does not imply availability on
the retained values of the same mathematical integers. -/
theorem fresh_available_retained_refused :
    (∀ left right : Int, ∃ value, limited .add (encode left) (encode right) = .ok value) ∧
    (∀ value, limited .add ⟨7, 4⟩ (encode 1) ≠ .ok value) := by
  constructor
  · intro left right
    exact ⟨⟨left + right, 1⟩, rfl⟩
  · intro value
    simp [limited]

theorem large_sequence_meaning :
    resultInteger decode (.inr (⟨2^128 + 3, 14⟩ : Stored)) = 2^128 + 3 := by
  have returned : addMany encode provider (.inr ⟨2^128, 7⟩)
      [.inr ⟨1, 12⟩, .inr ⟨2, 4⟩] = .ok (.inr ⟨2^128 + 3, 14⟩) := by decide +kernel
  exact addMany_sound encode decode roundtrip provider provider_sound _ _ _ returned

end Mettapedia.GSLT.LanguageDef.IntegerRepresentationExternalCall.Retained.Controls
