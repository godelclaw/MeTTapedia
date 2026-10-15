import Mettapedia.Languages.C11.IntegerMemoryProfiles
import Mettapedia.Languages.C11.IntegerAssignment

/-!
# Mixed integer layout and assignment controls

The controls use one byte allocation with distinct character, short, int,
long and Boolean objects. They retain complete memory after stores, separate
assignment conversion from representation aliases, and reject type/extent,
qualifier, lifetime and alignment violations. Character stores preserve
effective-type information; non-character stores can establish it.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.C11.IntegerMemoryControls

open AccessTypes ObjectAccessMemory IntegerMemoryModel

def model : Model := IntegerMemoryProfiles.memoryModel .lp64 .little
def characterType : IntegerType IntegerExtension := .signed (.standard .char)
def unsignedCharacterType : IntegerType IntegerExtension := .unsigned (.standard .char)
def shortType : IntegerType IntegerExtension := .signed (.standard .short)
def longType : IntegerType IntegerExtension := .signed (.standard .long)

def view (type : IntegerType IntegerExtension) : AccessTypes.View := ⟨.scalar (.integer type), {}⟩
def location (type : IntegerType IntegerExtension) (offset count : Nat) : Lvalue :=
  ⟨⟨⟨7, offset⟩, count⟩, view type⟩
def character : Lvalue := location characterType 0 1
def short : Lvalue := location shortType 2 2
def integer : Lvalue := location .int 4 4
def long : Lvalue := location longType 8 8
def boolean : Lvalue := location .boolean 16 1

def catalog : Catalog :=
  [(character.object, declaredRecord character.view 1),
    (short.object, declaredRecord short.view 2),
    (integer.object, declaredRecord integer.view 4),
    (long.object, declaredRecord long.view 8),
    (boolean.object, declaredRecord boolean.view 1)]

def byte (value : Nat) : ByteStorageData.Byte model.characters := BitVec.ofNat 8 value
def zero : Option (ByteStorageData.Byte model.characters) := some (byte 0)
def initial : State model.characters := ⟨[(7, ⟨true, List.replicate 32 zero⟩)], catalog⟩

def minusSeven : IntegerScalar.Value model.parameters := ⟨characterType, ⟨-7, by decide⟩⟩
def minusOne : IntegerScalar.Value model.parameters := ⟨characterType, ⟨-1, by decide⟩⟩
def minusShort : IntegerScalar.Value model.parameters := ⟨shortType, ⟨-1234, by decide⟩⟩
def seventeen : IntegerScalar.Value model.parameters := ⟨.int, ⟨17, by decide⟩⟩
def two : IntegerScalar.Value model.parameters := ⟨.int, ⟨2, by decide⟩⟩
def twoFiftyFive : IntegerScalar.Value model.parameters := ⟨.int, ⟨255, by decide⟩⟩
def largeLong : IntegerScalar.Value model.parameters := ⟨longType, ⟨4294967296, by decide⟩⟩
def trueBoolean : IntegerScalar.Value model.parameters := ⟨.boolean, ⟨1, by decide⟩⟩
def unsignedCharacter : IntegerScalar.Value model.parameters := ⟨unsignedCharacterType, ⟨249, by decide⟩⟩

def afterCharacter : State model.characters :=
  ⟨(7, ⟨true, some (byte 249) :: List.replicate 31 zero⟩) :: initial.storage,
    (character.object, declaredRecord character.view 1) :: catalog⟩

def afterCharacterMinusOne : State model.characters :=
  ⟨(7, ⟨true, some (byte 255) :: List.replicate 31 zero⟩) :: initial.storage,
    (character.object, declaredRecord character.view 1) :: catalog⟩

def mixed : Option (State model.characters) := do
  let saved ← IntegerMemoryModel.store model initial character minusSeven
  let saved ← IntegerMemoryModel.store model saved short minusShort
  let saved ← IntegerMemoryModel.store model saved integer seventeen
  let saved ← IntegerMemoryModel.store model saved long largeLong
  IntegerMemoryModel.store model saved boolean trueBoolean

def mixedReads : Option (List (Loaded model)) := do
  let saved ← mixed
  let first ← IntegerMemoryModel.load model saved character
  let second ← IntegerMemoryModel.load model saved short
  let third ← IntegerMemoryModel.load model saved integer
  let fourth ← IntegerMemoryModel.load model saved long
  let fifth ← IntegerMemoryModel.load model saved boolean
  some [first, second, third, fourth, fifth]

theorem all_objects_use_one_character_memory :
    ((model.layout characterType).representation.characters,
      (model.layout shortType).representation.characters,
      (model.layout .int).representation.characters,
      (model.layout longType).representation.characters) =
    (model.characters, model.characters, model.characters, model.characters) := rfl

theorem distinct_object_extents :
    ((model.layout characterType).representation.byteCount,
      (model.layout shortType).representation.byteCount,
      (model.layout .int).representation.byteCount,
      (model.layout longType).representation.byteCount) = (1, 2, 4, 8) := rfl

theorem character_store_retains_complete_state :
    IntegerMemoryModel.store model initial character minusSeven = some afterCharacter := by cbv

theorem character_store_readback : IntegerMemoryModel.load model afterCharacter character =
    some (.value minusSeven false) := by cbv

theorem character_alias_reads_representation :
    IntegerMemoryModel.load model afterCharacter (character.cast (view unsignedCharacterType)) =
      some (.value unsignedCharacter false) := by cbv

theorem character_write_keeps_adjacent_byte : ByteRanges.readBytes afterCharacter.storage ⟨⟨7, 0⟩, 2⟩ =
    some [some (byte 249), zero] := by cbv

theorem mixed_width_stores_and_reads : mixedReads = some [
    .value minusSeven false, .value minusShort false, .value seventeen false,
    .value largeLong false, .value trueBoolean false] := by cbv

theorem assignment_converts_before_store :
    IntegerAssignment.assign model intervalReductionPolicy initial character twoFiftyFive =
      some (.stored minusOne, afterCharacterMinusOne) := by cbv

theorem conversion_signal_keeps_every_memory_field :
    IntegerAssignment.assign model (signalingPolicy 9) initial character twoFiftyFive =
      some (.conversionSignal 9, initial) := by cbv

theorem boolean_assignment_uses_truth :
    (IntegerAssignment.assign model intervalReductionPolicy initial boolean two).map (fun result => result.1) =
      some (.stored trueBoolean) := by cbv

theorem stored_boolean_is_canonical :
    (IntegerAssignment.assign model intervalReductionPolicy initial boolean two).bind (fun result =>
      ByteRanges.readBytes result.2.storage ⟨⟨7, 16⟩, 1⟩) = some [some (byte 1)] := by cbv

theorem unconverted_store_is_refused : IntegerMemoryModel.store model initial character seventeen = none := by cbv

theorem declared_character_store_keeps_declared_type :
    ObjectStores.selectPermission (declaredRecord character.view 1).info character.view.type =
      some (character.view.type, (declaredRecord character.view 1).info) := by cbv

theorem allocated_character_store_does_not_establish_type :
    ObjectStores.selectPermission {} (view unsignedCharacterType).type = some ((view unsignedCharacterType).type, {}) := by cbv

theorem character_access_type_differs_from_retained_type :
    ObjectStores.selectPermission ⟨none, some integer.view.type⟩ (view unsignedCharacterType).type =
      some ((view unsignedCharacterType).type, ⟨none, some integer.view.type⟩) := by cbv

theorem non_character_store_establishes_type : ObjectStores.selectPermission {} short.view.type =
    some (short.view.type, ⟨none, some short.view.type⟩) := by cbv

theorem wrong_extent_refuses_before_writing :
    IntegerMemoryModel.store model initial (integer.cast (view longType)) largeLong = none := by cbv

theorem missing_catalog_refuses_store :
    IntegerMemoryModel.store model ⟨initial.storage, []⟩ character minusSeven = none := by cbv

theorem readonly_object_cannot_be_modified_through_unqualified_view :
    IntegerMemoryModel.store model
      ⟨initial.storage, (character.object, declaredRecord ⟨character.view.type, {const := true}⟩ 1) :: catalog⟩
      character minusSeven = none := by cbv

theorem volatile_write_requires_interaction : IntegerMemoryModel.store model initial
    (character.cast ⟨character.view.type, {volatile := true}⟩) minusSeven = none := by cbv

theorem ended_lifetime_refuses_store :
    IntegerMemoryModel.store model ⟨[(7, ⟨false, List.replicate 32 zero⟩)], catalog⟩ character minusSeven = none := by cbv

theorem misalignment_refuses_store :
    IntegerMemoryModel.store model
      ⟨initial.storage, ((location shortType 1 2).object, declaredRecord short.view 2) :: catalog⟩
      (location shortType 1 2) minusShort = none := by cbv

theorem invalid_boolean_padding_has_a_distinct_trap :
    IntegerMemoryModel.load model
      ⟨[(7, ⟨true, List.replicate 16 zero ++ some (byte 2) :: List.replicate 15 zero⟩)], catalog⟩ boolean =
        some (.paddingTrap .boolean) := by cbv

theorem character_store_has_independent_writing :
    IntegerMemoryModel.Writing model (represent initial) (represent afterCharacter) character minusSeven :=
  IntegerMemoryModel.store_sound _ _ _ _ _ character_store_retains_complete_state

theorem assignment_has_independent_conversion_and_writing :
    IntegerAssignment.Assigning model intervalReductionPolicy (represent initial) character twoFiftyFive
      (.stored minusOne) (represent afterCharacterMinusOne) :=
  IntegerAssignment.assign_sound _ _ _ _ _ _ _ assignment_converts_before_store

end Mettapedia.Languages.C11.IntegerMemoryControls
