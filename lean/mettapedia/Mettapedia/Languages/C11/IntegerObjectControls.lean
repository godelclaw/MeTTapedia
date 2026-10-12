import Mettapedia.Languages.C11.IntegerMemory
import Mettapedia.Languages.C11.ObjectControls

/-!
# Integer representation and byte-memory controls

The controls distinguish value conversion from a representation view,
negative from positive zero, invalid extent from a trap representation,
padding policy from value bits, and raw copying from initialized-value
access. The alternative signed formats are semantic profiles; native probes
use the declared two's-complement host profile.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.C11.IntegerObjectControls

open ByteStorageData
open ObjectControls
open Mettapedia.Machines.CMemory

def unsignedCharacter : IntegerObject.Profile :=
  ⟨byte8, .unsigned 8 (by decide), 1, by decide, by decide, .little, .normal, .ignored⟩
def signedCharacter (representation : SignedRepresentation) (zero : IntegerBits.NegativeZero) :
    IntegerObject.Profile :=
  ⟨byte8, .signed 7 (by decide) representation, 1, by decide, by change 8 ≤ 8; decide, .little, zero, .ignored⟩
def int16 (order : BytePacking.Order) : IntegerObject.Profile :=
  ⟨byte8, .signed 15 (by decide) (.twosComplement true), 2, by decide, by decide, order, .normal, .ignored⟩
def int32 (order : BytePacking.Order) : IntegerObject.Profile :=
  ⟨byte8, .signed 31 (by decide) (.twosComplement true), 4, by decide, by decide, order, .normal, .ignored⟩
def uint32 : IntegerObject.Profile :=
  ⟨byte8, .unsigned 32 (by decide), 4, by decide, by decide, .little, .normal, .ignored⟩
def paddedInt (padding : IntegerObject.Padding) : IntegerObject.Profile :=
  ⟨byte8, .signed 15 (by decide) (.twosComplement true), 4, by decide, by decide, .little, .normal, padding⟩
def wideCharacter : IntegerObject.Profile :=
  ⟨byte16, .unsigned 16 (by decide), 1, by decide, by decide, .little, .normal, .ignored⟩

def bytes (values : List Nat) : List (Byte byte8) := values.map b

theorem little_word_has_low_byte_first :
    BytePacking.encode byte8 .little 2 4660 = some (bytes [52, 18]) := by decide
theorem big_word_has_high_byte_first :
    BytePacking.encode byte8 .big 2 4660 = some (bytes [18, 52]) := by decide
theorem wrong_order_changes_value :
    BytePacking.decode byte8 .big 2 (bytes [52, 18]) = some 13330 := by decide
theorem word_overflow_refused : BytePacking.encode byte8 .little 2 65536 = none := by decide
theorem wrong_word_extent_refused : BytePacking.decode byte8 .little 2 (bytes [52]) = none := by decide
theorem empty_word_cannot_encode_nonzero : BytePacking.encode byte8 .big 0 1 = none := rfl

theorem twos_complement_character_reads_minimum :
    IntegerObject.readObject (signedCharacter (.twosComplement true) .normal) (bytes [128]) =
      some (.integer (.value (-128) false)) := by decide
theorem exceptional_minimum_is_a_trap :
    IntegerObject.readObject (signedCharacter (.twosComplement false) .normal) (bytes [128]) =
      some (.integer (.trap .minimum)) := by decide
theorem sign_magnitude_negative_zero_retained :
    IntegerObject.readObject (signedCharacter .signMagnitude .normal) (bytes [128]) =
      some (.integer (.value 0 true)) := by decide
theorem sign_magnitude_negative_zero_can_trap :
    IntegerObject.readObject (signedCharacter .signMagnitude .trap) (bytes [128]) =
      some (.integer (.trap .negativeZero)) := by decide
theorem ones_complement_negative_zero_retained :
    IntegerObject.readObject (signedCharacter .onesComplement .normal) (bytes [255]) =
      some (.integer (.value 0 true)) := by decide
theorem ones_complement_negative_zero_can_trap :
    IntegerObject.readObject (signedCharacter .onesComplement .trap) (bytes [255]) =
      some (.integer (.trap .negativeZero)) := by decide
theorem positive_zero_is_not_negative_zero :
    IntegerObject.readObject (signedCharacter .signMagnitude .normal) (bytes [0]) =
      some (.integer (.value 0 false)) := by decide
theorem ordinary_zero_store_chooses_positive_zero :
    IntegerObject.storeObject (signedCharacter .onesComplement .normal) 0 = bytes [0] := rfl
theorem integer_format_preserves_minimum_policy :
    IntegerBits.read (.signed 7 (by decide) (.twosComplement false)) .normal 128 ≠
      some (.value (-128) false) := by decide
theorem over_width_encoding_is_invalid_data :
    IntegerBits.read (.signed 7 (by decide) .signMagnitude) .normal 256 = none := by decide

theorem all_ones_has_three_integer_interpretations :
    IntegerObject.readObject (signedCharacter .signMagnitude .normal) (bytes [255]) =
      some (.integer (.value (-127) false)) ∧
    IntegerObject.readObject (signedCharacter .onesComplement .normal) (bytes [255]) =
      some (.integer (.value 0 true)) ∧
    IntegerObject.readObject (signedCharacter (.twosComplement true) .normal) (bytes [255]) =
      some (.integer (.value (-1) false)) := by decide
theorem sign_magnitude_minus_one_has_sign_and_magnitude :
    IntegerObject.storeObject (signedCharacter .signMagnitude .normal) (-1) = bytes [129] := rfl
theorem ones_complement_minus_one_complements_bits :
    IntegerObject.storeObject (signedCharacter .onesComplement .normal) (-1) = bytes [254] := rfl
theorem twos_complement_minus_one_has_all_bits_set :
    IntegerObject.storeObject (signedCharacter (.twosComplement true) .normal) (-1) = bytes [255] := rfl
theorem unsigned_view_is_not_an_integer_conversion :
    IntegerObject.readObject unsignedCharacter
      (IntegerObject.storeObject (signedCharacter .onesComplement .normal) (-1)) =
      some (.integer (.value 254 false)) ∧
    convertInteger intervalReductionPolicy (-1) (.integer unsignedCharacter.integer) = .value 255 := by decide

theorem signed_short_minimum_little_bytes :
    IntegerObject.storeObject (int16 .little) (-32768) = bytes [0, 128] := rfl
theorem signed_short_minimum_big_bytes :
    IntegerObject.storeObject (int16 .big) (-32768) = bytes [128, 0] := rfl
theorem signed_int_negative_bytes :
    IntegerObject.storeObject (int32 .little) (-17) = bytes [239, 255, 255, 255] := rfl
theorem signed_int_positive_byte_order :
    IntegerObject.storeObject (int32 .big) 305419896 = bytes [18, 52, 86, 120] := rfl
theorem signed_int_wrong_byte_order_changes_value :
    IntegerObject.readObject (int32 .big) (bytes [239, 255, 255, 255]) =
      some (.integer (.value (-268435457) false)) := by decide
theorem invalid_object_extent_is_not_a_trap :
    IntegerObject.readObject (int32 .little) (bytes [128]) = none := by decide

theorem ignored_padding_preserves_value :
    IntegerObject.readObject (paddedInt .ignored) (bytes [17, 0, 99, 88]) =
      some (.integer (.value 17 false)) := by decide
theorem checked_padding_classifies_a_trap :
    IntegerObject.readObject (paddedInt .zero) (bytes [17, 0, 99, 88]) = some .paddingTrap := by decide
theorem padding_and_value_are_separate :
    IntegerObject.readObject (paddedInt .zero) (bytes [17, 0, 0, 0]) =
      some (.integer (.value 17 false)) := by decide
theorem ordinary_store_does_not_manufacture_padding_trap :
    IntegerObject.readObject (paddedInt .zero) (IntegerObject.storeObject (paddedInt .zero) (-17)) =
      some (.integer (.value (-17) false)) := IntegerObject.readObject_storeObject _ _ (by decide)
theorem wide_character_preserves_sixteen_bits :
    IntegerObject.readObject wideCharacter [BitVec.ofNat 16 511] = some (.integer (.value 511 false)) := by decide

def emptyStorage : ByteRanges.Storage.State (Byte byte8) := [(7, ⟨true, List.replicate 8 (some (b 0))⟩)]
def minusSeventeen : IntegerValue (int32 .little).integer := ⟨-17, by decide⟩
def saved : ByteRanges.Storage.State (Byte byte8) := ExecutableStorage.put emptyStorage 7
  ⟨true, [239, 255, 255, 255, 0, 0, 0, 0].map (fun n => some (b n))⟩

theorem initialized_writer_changes_object_bytes :
    IntegerMemory.storeInteger (int32 .little) emptyStorage ⟨7, 0⟩ minusSeventeen = some saved := rfl
theorem initialized_reader_recovers_signed_value :
    IntegerMemory.readInteger (int32 .little) saved ⟨7, 0⟩ = some (.integer (.value (-17) false)) :=
  IntegerMemory.read_after_store _ _ _ _ _ initialized_writer_changes_object_bytes
theorem unsigned_byte_view_retains_corresponding_bits :
    IntegerMemory.readInteger uint32 saved ⟨7, 0⟩ = some (.integer (.value 4294967279 false)) := by decide
theorem crossing_object_write_refused :
    IntegerMemory.storeInteger (int32 .little) emptyStorage ⟨7, 6⟩ minusSeventeen = none := by decide
theorem crossing_object_read_refused :
    IntegerMemory.readInteger (int32 .little) saved ⟨7, 6⟩ = none := by decide
theorem indeterminate_bytes_do_not_yield_initialized_value :
    IntegerMemory.readInteger (int32 .little) [(7, ⟨true, [none, some (b 0), some (b 0), some (b 0)]⟩)] ⟨7, 0⟩ = none := by decide
theorem dead_object_has_no_initialized_read :
    IntegerMemory.readInteger (int32 .little) [(7, ⟨false, (bytes [1, 0, 0, 0]).map some⟩)] ⟨7, 0⟩ = none := by decide
theorem raw_trap_bytes_remain_observable :
    ByteRanges.readBytes [(7, ⟨true, [some (b 128)]⟩)] ⟨⟨7, 0⟩, 1⟩ = some [some (b 128)] ∧
    IntegerMemory.readInteger (signedCharacter .signMagnitude .trap) [(7, ⟨true, [some (b 128)]⟩)] ⟨7, 0⟩ =
      some (.integer (.trap .negativeZero)) := by decide

end Mettapedia.Languages.C11.IntegerObjectControls
