import Mettapedia.Languages.MeTTa.OSLFCore.Atom

/-!
# Finite policy indices as MeTTa data

Small policy wires repeatedly need natural numbers and bounded table indices.
This module supplies one structural encoding in the existing MeTTa `Atom`
carrier.  Decoding a bounded index checks the submitted bound; it does not
silently truncate an out-of-range number.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.Bridges.GSLT.FinitePolicyAtomWire

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)

def encodeNat : Nat → Atom
  | 0 => .symbol "policy-nat-zero-v1"
  | n + 1 => .expression [.symbol "policy-nat-succ-v1", encodeNat n]

def decodeNat : Atom → Option Nat
  | .symbol "policy-nat-zero-v1" => some 0
  | .expression [.symbol "policy-nat-succ-v1", predecessor] =>
      (decodeNat predecessor).map Nat.succ
  | _ => none

@[simp] theorem decodeNat_encodeNat (value : Nat) :
    decodeNat (encodeNat value) = some value := by
  induction value with
  | zero => rfl
  | succ value ih => simp [encodeNat, decodeNat, ih]

def encodeFin {bound : Nat} (index : Fin bound) : Atom := encodeNat index.val

def decodeFin (bound : Nat) (atom : Atom) : Option (Fin bound) := do
  let value ← decodeNat atom
  if within : value < bound then some ⟨value, within⟩ else none

@[simp] theorem decodeFin_encodeFin {bound : Nat} (index : Fin bound) :
    decodeFin bound (encodeFin index) = some index := by
  simp [decodeFin, encodeFin, index.isLt]

theorem encodeNat_injective : Function.Injective encodeNat := by
  intro first second equal
  have decoded := congrArg decodeNat equal
  simpa only [decodeNat_encodeNat, Option.some.injEq] using decoded

theorem encodeFin_injective {bound : Nat} :
    Function.Injective (encodeFin : Fin bound → Atom) := by
  intro first second equal
  have decoded := congrArg (decodeFin bound) equal
  simpa only [decodeFin_encodeFin, Option.some.injEq] using decoded

/-- The boundary check is substantive: an encoded natural at or above the
submitted table length is not accepted as an index. -/
theorem out_of_range_refused {bound value : Nat} (outside : bound ≤ value) :
    decodeFin bound (encodeNat value) = none := by
  simp [decodeFin, Nat.not_lt.mpr outside]

/-- Malformed atoms are not interpreted as the zero index. -/
theorem malformed_index_refused (bound : Nat) :
    decodeFin bound (.symbol "policy-nat-succ-v1") = none := by
  rfl

#print axioms decodeNat_encodeNat
#print axioms decodeFin_encodeFin
#print axioms encodeNat_injective
#print axioms encodeFin_injective
#print axioms out_of_range_refused
#print axioms malformed_index_refused

end Mettapedia.Languages.MeTTa.Bridges.GSLT.FinitePolicyAtomWire
