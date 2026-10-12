import Mettapedia.Languages.C11.IntegerBits

/-!
# Integer object bytes under an explicit layout and padding policy

This constructed profile places value/sign bits in the low finite-word
positions and padding above them. Bytes follow the selected byte order.
Padding is either ignored or required to be zero; the latter profile makes
nonzero padding a trap. The ordinary writer generates zero padding and a
positive zero, so it cannot manufacture a trap from a valid value.

The reader is proved equivalent to independent byte-digit, padding and
integer-bit judgments. The general store/read law covers every valid integer
value, precision, character width, sufficient positive object size and byte
order in the declared profile. Invalid byte extent is distinguished from a
valid-width trap. This is representation interpretation; lvalue access,
indeterminate bytes, effective types, alignment and volatile effects remain
in the memory/source layer. Other bit-position and padding policies need
their own implementation profiles.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.C11.IntegerObject

open ByteStorageData

inductive Padding where
  | ignored
  | zero
  deriving DecidableEq, Repr

inductive Padding.Allows : Padding → Nat → Prop where
  | ignored (bits : Nat) : Padding.Allows .ignored bits
  | zero : Padding.Allows .zero 0

instance (policy : Padding) (bits : Nat) : Decidable (policy.Allows bits) := by
  cases policy with
  | ignored => exact .isTrue (.ignored bits)
  | zero =>
      by_cases zero : bits = 0
      · subst bits; exact .isTrue .zero
      · exact .isFalse (fun allowed => by cases allowed; exact zero rfl)

theorem Padding.zero_allowed (policy : Padding) : policy.Allows 0 := by
  cases policy with
  | ignored => exact .ignored 0
  | zero => exact .zero

structure Profile where
  characters : ByteStorageData.Profile
  integer : IntegerFormat
  byteCount : Nat
  positiveExtent : 0 < byteCount
  fits : IntegerBits.width integer ≤ characters.charBits * byteCount
  order : BytePacking.Order
  negativeZero : IntegerBits.NegativeZero
  padding : Padding

inductive Outcome where
  | integer (result : IntegerBits.Outcome)
  | paddingTrap
  deriving DecidableEq, Repr

def valueModulus (profile : Profile) : Nat := 2 ^ IntegerBits.width profile.integer

theorem valueModulus_positive (profile : Profile) : 0 < valueModulus profile := Nat.two_pow_pos _

def readObject (profile : Profile) (bytes : List (Byte profile.characters)) : Option Outcome := do
  let word ← BytePacking.decode profile.characters profile.order profile.byteCount bytes
  if profile.padding.Allows (word / valueModulus profile) then
    let result ← IntegerBits.read profile.integer profile.negativeZero (word % valueModulus profile)
    some (.integer result)
  else some .paddingTrap

inductive Reading (profile : Profile) : List (Byte profile.characters) → Outcome → Prop where
  | integer (bytes : List (Byte profile.characters)) (word : Nat) (result : IntegerBits.Outcome)
      (represented : BytePacking.Representation profile.characters profile.order profile.byteCount word bytes)
      (padding : profile.padding.Allows (word / valueModulus profile))
      (integer : IntegerBits.Reading profile.integer profile.negativeZero (word % valueModulus profile) result) :
      Reading profile bytes (.integer result)
  | paddingTrap (bytes : List (Byte profile.characters)) (word : Nat)
      (represented : BytePacking.Representation profile.characters profile.order profile.byteCount word bytes)
      (padding : ¬ profile.padding.Allows (word / valueModulus profile)) :
      Reading profile bytes .paddingTrap

theorem readObject_sound (profile : Profile) (bytes : List (Byte profile.characters)) (outcome : Outcome)
    (computed : readObject profile bytes = some outcome) : Reading profile bytes outcome := by
  cases decoded : BytePacking.decode profile.characters profile.order profile.byteCount bytes with
  | none => simp [readObject, decoded] at computed
  | some word =>
      have represented := (BytePacking.decode_iff profile.characters profile.order profile.byteCount word bytes).mp decoded
      by_cases padding : profile.padding.Allows (word / valueModulus profile)
      · cases integer : IntegerBits.read profile.integer profile.negativeZero (word % valueModulus profile) with
        | none => simp [readObject, decoded, padding, integer] at computed
        | some result =>
            simp [readObject, decoded, padding, integer] at computed
            subst outcome
            exact .integer bytes word result represented padding
              (IntegerBits.read_sound profile.integer profile.negativeZero _ result integer)
      · simp [readObject, decoded, padding] at computed
        subst outcome
        exact .paddingTrap bytes word represented padding

theorem readObject_complete (profile : Profile) (bytes : List (Byte profile.characters)) (outcome : Outcome)
    (reading : Reading profile bytes outcome) : readObject profile bytes = some outcome := by
  cases reading with
  | integer word result represented padding integer =>
      have decoded := (BytePacking.decode_iff profile.characters profile.order profile.byteCount word bytes).mpr represented
      have computed := IntegerBits.read_complete profile.integer profile.negativeZero _ result integer
      simp [readObject, decoded, padding, computed]
  | paddingTrap word represented padding =>
      have decoded := (BytePacking.decode_iff profile.characters profile.order profile.byteCount word bytes).mpr represented
      simp [readObject, decoded, padding]

theorem readObject_iff (profile : Profile) (bytes : List (Byte profile.characters)) (outcome : Outcome) :
    readObject profile bytes = some outcome ↔ Reading profile bytes outcome :=
  ⟨readObject_sound profile bytes outcome, readObject_complete profile bytes outcome⟩

theorem readObject_value_in_range (profile : Profile) (bytes : List (Byte profile.characters))
    (integer : Int) (negativeZero : Bool)
    (computed : readObject profile bytes = some (.integer (.value integer negativeZero))) :
    profile.integer.Represents integer := by
  have reading := readObject_sound profile bytes _ computed
  cases reading with
  | integer word result represented padding reading =>
      exact IntegerBits.Reading.value_in_range profile.integer profile.negativeZero _ _ reading integer negativeZero rfl

theorem readObject_extent (profile : Profile) (bytes : List (Byte profile.characters)) (outcome : Outcome)
    (computed : readObject profile bytes = some outcome) : bytes.length = profile.byteCount := by
  have reading := readObject_sound profile bytes outcome computed
  cases reading with
  | integer word result represented padding integer => exact represented.1
  | paddingTrap word represented padding => exact represented.1

theorem canonicalWord_fits (profile : Profile) (integer : Int) (valid : profile.integer.Represents integer) :
    IntegerBits.canonicalWord profile.integer integer < BytePacking.radix profile.characters ^ profile.byteCount := by
  have bounded := IntegerBits.canonicalWord_bound profile.integer integer valid
  change IntegerBits.canonicalWord profile.integer integer < valueModulus profile at bounded
  have enough := Nat.pow_le_pow_right (by decide : 0 < 2) profile.fits
  have extent : BytePacking.radix profile.characters ^ profile.byteCount = 2 ^ (profile.characters.charBits * profile.byteCount) := by
    simp [BytePacking.radix, pow_mul]
  rw [extent]
  exact Nat.lt_of_lt_of_le bounded enough

def storeObject (profile : Profile) (integer : Int) : List (Byte profile.characters) :=
  BytePacking.orient profile.order
    (BytePacking.encodeLittle profile.characters profile.byteCount (IntegerBits.canonicalWord profile.integer integer))

theorem storeObject_extent (profile : Profile) (integer : Int) :
    (storeObject profile integer).length = profile.byteCount := by
  rw [storeObject, BytePacking.orient_length, BytePacking.encodeLittle_length]

theorem storeObject_representation (profile : Profile) (integer : Int) (valid : profile.integer.Represents integer) :
    BytePacking.Representation profile.characters profile.order profile.byteCount
      (IntegerBits.canonicalWord profile.integer integer) (storeObject profile integer) := by
  apply BytePacking.encode_sound profile.characters profile.order profile.byteCount _ _
  simp only [BytePacking.encode, canonicalWord_fits profile integer valid, ↓reduceIte, storeObject]

theorem storeObject_reading (profile : Profile) (integer : Int) (valid : profile.integer.Represents integer) :
    Reading profile (storeObject profile integer) (.integer (.value integer false)) := by
  have bounded := IntegerBits.canonicalWord_bound profile.integer integer valid
  change IntegerBits.canonicalWord profile.integer integer < valueModulus profile at bounded
  have padding : profile.padding.Allows (IntegerBits.canonicalWord profile.integer integer / valueModulus profile) := by
    rw [Nat.div_eq_of_lt bounded]
    exact profile.padding.zero_allowed
  apply Reading.integer _ _ _ (storeObject_representation profile integer valid) padding
  rw [Nat.mod_eq_of_lt bounded]
  exact IntegerBits.canonicalWord_reading profile.integer profile.negativeZero integer valid

theorem readObject_storeObject (profile : Profile) (integer : Int) (valid : profile.integer.Represents integer) :
    readObject profile (storeObject profile integer) = some (.integer (.value integer false)) :=
  readObject_complete profile _ _ (storeObject_reading profile integer valid)

theorem storeObject_injective (profile : Profile) (left right : Int)
    (leftValid : profile.integer.Represents left) (rightValid : profile.integer.Represents right)
    (same : storeObject profile left = storeObject profile right) : left = right := by
  have observation := congrArg (readObject profile) same
  rw [readObject_storeObject profile left leftValid, readObject_storeObject profile right rightValid] at observation
  cases observation
  rfl

end Mettapedia.Languages.C11.IntegerObject
