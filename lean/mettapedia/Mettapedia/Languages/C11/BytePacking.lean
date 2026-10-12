import Mettapedia.Languages.C11.ByteStorageData

/-!
# Constructed byte-order representation of finite words

A byte is a character-width bit vector. The executable encoder extracts
successive radix digits; the decoder combines them. Both byte orders have
general inverse laws at every byte width and object extent. Checked encoding
rejects words that do not fit, and checked decoding retains the exact extent.
An independent digit judgment characterizes the encoded bytes in both
directions. This layer does not interpret signed values or classify padding,
effective types or trap representations.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.C11.BytePacking

open ByteStorageData

inductive Order where
  | little
  | big
  deriving DecidableEq, Repr

def radix (profile : Profile) : Nat := 2 ^ profile.charBits

theorem radix_positive (profile : Profile) : 0 < radix profile := Nat.two_pow_pos _

def encodeLittle (profile : Profile) : Nat → Nat → List (Byte profile)
  | 0, _ => []
  | count + 1, value => BitVec.ofNat profile.charBits value ::
      encodeLittle profile count (value / radix profile)

def decodeLittle (profile : Profile) : List (Byte profile) → Nat
  | [] => 0
  | head :: tail => head.toNat + radix profile * decodeLittle profile tail

inductive Digits (profile : Profile) : List (Byte profile) → Nat → Prop where
  | nil : Digits profile [] 0
  | cons (head : Byte profile) (tail : List (Byte profile)) (rest : Nat)
      (digits : Digits profile tail rest) :
      Digits profile (head :: tail) (head.toNat + radix profile * rest)

theorem decodeLittle_digits (profile : Profile) (bytes : List (Byte profile)) :
    Digits profile bytes (decodeLittle profile bytes) := by
  induction bytes with
  | nil => exact .nil
  | cons head tail ih => exact .cons head tail _ ih

theorem digits_decodeLittle (profile : Profile) (bytes : List (Byte profile)) (value : Nat)
    (digits : Digits profile bytes value) : decodeLittle profile bytes = value := by
  induction digits with
  | nil => rfl
  | cons head tail rest digits ih => simp only [decodeLittle, ih]

theorem digits_iff (profile : Profile) (bytes : List (Byte profile)) (value : Nat) :
    Digits profile bytes value ↔ decodeLittle profile bytes = value := by
  constructor
  · exact digits_decodeLittle profile bytes value
  · intro equal
    rw [← equal]
    exact decodeLittle_digits profile bytes

theorem encodeLittle_length (profile : Profile) (count value : Nat) :
    (encodeLittle profile count value).length = count := by
  induction count generalizing value with
  | zero => rfl
  | succ count ih => simp only [encodeLittle, List.length_cons, ih]

theorem decodeLittle_bound (profile : Profile) (bytes : List (Byte profile)) :
    decodeLittle profile bytes < radix profile ^ bytes.length := by
  induction bytes with
  | nil => simp [decodeLittle]
  | cons head tail ih =>
      have digitBound : head.toNat < radix profile := head.isLt
      have restBound := Nat.mul_le_mul_left (radix profile) (Nat.succ_le_of_lt ih)
      simp only [decodeLittle, List.length_cons, pow_succ]
      nlinarith

theorem decodeLittle_encode (profile : Profile) (count value : Nat)
    (fits : value < radix profile ^ count) :
    decodeLittle profile (encodeLittle profile count value) = value := by
  induction count generalizing value with
  | zero =>
      simp only [pow_zero] at fits
      have zero : value = 0 := by omega
      simp [zero, encodeLittle, decodeLittle]
  | succ count ih =>
      have quotient : value / radix profile < radix profile ^ count :=
        (Nat.div_lt_iff_lt_mul (radix_positive profile)).mpr (by simpa only [pow_succ] using fits)
      simp only [encodeLittle, decodeLittle, BitVec.toNat_ofNat, ih _ quotient]
      exact Nat.mod_add_div value (radix profile)

theorem encodeLittle_decode (profile : Profile) (bytes : List (Byte profile)) :
    encodeLittle profile bytes.length (decodeLittle profile bytes) = bytes := by
  induction bytes with
  | nil => rfl
  | cons head tail ih =>
      have digitBound : head.toNat < radix profile := head.isLt
      have remainder : (head.toNat + radix profile * decodeLittle profile tail) % radix profile = head.toNat := by
        simp [Nat.add_mod, Nat.mod_eq_of_lt digitBound]
      have quotient : (head.toNat + radix profile * decodeLittle profile tail) / radix profile =
          decodeLittle profile tail := by
        rw [Nat.add_mul_div_left _ _ (radix_positive profile), Nat.div_eq_of_lt digitBound]
        simp
      simp only [List.length_cons, decodeLittle, encodeLittle, quotient, ih]
      congr 1
      apply BitVec.eq_of_toNat_eq
      exact remainder

def orient {α : Type} (order : Order) (bytes : List α) : List α := match order with
  | .little => bytes
  | .big => bytes.reverse

theorem orient_length {α : Type} (order : Order) (bytes : List α) :
    (orient order bytes).length = bytes.length := by cases order <;> simp [orient]

theorem orient_involutive {α : Type} (order : Order) (bytes : List α) :
    orient order (orient order bytes) = bytes := by cases order <;> simp [orient]

def encode (profile : Profile) (order : Order) (count value : Nat) : Option (List (Byte profile)) :=
  if value < radix profile ^ count then some (orient order (encodeLittle profile count value)) else none

def decode (profile : Profile) (order : Order) (count : Nat) (bytes : List (Byte profile)) : Option Nat :=
  if bytes.length = count then some (decodeLittle profile (orient order bytes)) else none

def Representation (profile : Profile) (order : Order) (count value : Nat)
    (bytes : List (Byte profile)) : Prop :=
  bytes.length = count ∧ Digits profile (orient order bytes) value

theorem encode_sound (profile : Profile) (order : Order) (count value : Nat)
    (bytes : List (Byte profile)) (encoded : encode profile order count value = some bytes) :
    Representation profile order count value bytes := by
  by_cases fits : value < radix profile ^ count
  · simp only [encode, fits, ↓reduceIte, Option.some.injEq] at encoded
    subst bytes
    refine ⟨?_, ?_⟩
    · rw [orient_length, encodeLittle_length]
    · rw [orient_involutive, digits_iff, decodeLittle_encode profile count value fits]
  · simp [encode, fits] at encoded

theorem encode_complete (profile : Profile) (order : Order) (count value : Nat)
    (bytes : List (Byte profile)) (represented : Representation profile order count value bytes) :
    encode profile order count value = some bytes := by
  obtain ⟨extent, digits⟩ := represented
  have decoded := digits_decodeLittle profile (orient order bytes) value digits
  have bound := decodeLittle_bound profile (orient order bytes)
  rw [orient_length, extent, decoded] at bound
  have encoded := encodeLittle_decode profile (orient order bytes)
  rw [orient_length, extent, decoded] at encoded
  simp only [encode, bound, ↓reduceIte]
  rw [encoded, orient_involutive]

theorem encode_iff (profile : Profile) (order : Order) (count value : Nat) (bytes : List (Byte profile)) :
    encode profile order count value = some bytes ↔ Representation profile order count value bytes :=
  ⟨encode_sound profile order count value bytes, encode_complete profile order count value bytes⟩

theorem decode_iff (profile : Profile) (order : Order) (count value : Nat) (bytes : List (Byte profile)) :
    decode profile order count bytes = some value ↔ Representation profile order count value bytes := by
  simp only [decode, Representation, digits_iff]
  by_cases extent : bytes.length = count <;> simp [extent]

theorem decode_encode (profile : Profile) (order : Order) (count value : Nat) (bytes : List (Byte profile))
    (encoded : encode profile order count value = some bytes) : decode profile order count bytes = some value :=
  (decode_iff profile order count value bytes).mpr (encode_sound profile order count value bytes encoded)

theorem encode_decode (profile : Profile) (order : Order) (count value : Nat) (bytes : List (Byte profile))
    (decoded : decode profile order count bytes = some value) : encode profile order count value = some bytes :=
  encode_complete profile order count value bytes ((decode_iff profile order count value bytes).mp decoded)

theorem opposite_order_observes_reverse (profile : Profile) (count : Nat) (bytes : List (Byte profile)) :
    decode profile .big count bytes = decode profile .little count bytes.reverse := by
  simp [decode, orient]

end Mettapedia.Languages.C11.BytePacking
