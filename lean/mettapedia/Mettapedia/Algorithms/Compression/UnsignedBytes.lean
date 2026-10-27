import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Tactic

/-!
# Canonical unsigned byte fields

Zero is the empty vector. Other values are their minimal big-endian base-256
digits. The machine-integer profile accepts exactly the nonnegative signed
64-bit range; it never obtains integer identities through floating conversion.
The generic definitions use naturals for bytes and check their byte range.
-/

namespace Mettapedia.Algorithms.Compression.UnsignedBytes

def encode (value : Nat) : List Nat := (Nat.digits 256 value).reverse

def decode (bytes : List Nat) : Option Nat :=
  if ∀ byte ∈ bytes, byte < 256 then
    let value := Nat.ofDigits 256 bytes.reverse
    if encode value = bytes then some value else none
  else none

theorem encode_bytes (value : Nat) : ∀ byte ∈ encode value, byte < 256 := by
  intro byte member
  exact Nat.digits_lt_base (by decide) (by simpa [encode] using member)

theorem value_encode (value : Nat) : Nat.ofDigits 256 (encode value).reverse = value := by
  simp [encode, Nat.ofDigits_digits]

theorem decode_encode (value : Nat) : decode (encode value) = some value := by
  unfold decode
  rw [if_pos (encode_bytes value)]
  simp [value_encode]

theorem decode_sound {bytes : List Nat} {value : Nat} (found : decode bytes = some value) :
    encode value = bytes ∧ ∀ byte ∈ bytes, byte < 256 := by
  unfold decode at found
  split at found
  · rename_i valid
    dsimp only at found
    split at found
    · rename_i canonical
      cases Option.some.inj found
      exact ⟨canonical, valid⟩
    · cases found
  · cases found

theorem encode_injective : Function.Injective encode := by
  intro left right equal
  have values := congrArg (fun bytes => Nat.ofDigits 256 bytes.reverse) equal
  simpa [value_encode] using values

def machineLimit : Nat := 2 ^ 63

def decodeMachine (bytes : List Nat) : Option Nat := do
  let value ← decode bytes
  if value < machineLimit then some value else none

theorem decodeMachine_encode (value : Nat) :
    decodeMachine (encode value) = if value < machineLimit then some value else none := by
  simp [decodeMachine, decode_encode]

theorem decodeMachine_sound {bytes : List Nat} {value : Nat}
    (found : decodeMachine bytes = some value) :
    encode value = bytes ∧ value < machineLimit := by
  unfold decodeMachine at found
  cases decoded : decode bytes with
  | none => simp [decoded] at found
  | some result =>
      simp [decoded] at found
      obtain ⟨bounded, rfl⟩ := found
      exact ⟨(decode_sound decoded).1, bounded⟩

example : decode [] = some 0 := by decide
example : decode [0] = none := by decide
example : decode [0, 1] = none := by decide
example : decode [1, 0] = some 256 := by decide
example : decode [256] = none := by decide

end Mettapedia.Algorithms.Compression.UnsignedBytes
