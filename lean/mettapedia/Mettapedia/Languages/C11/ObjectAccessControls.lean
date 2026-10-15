import Mettapedia.Languages.C11.ScopedLvalues
import Mettapedia.Languages.C11.IntegerObjectControls
import Mettapedia.Languages.C11.CestaObjectAccess

/-!
# Object type, alias, qualifier and scoped-access controls

Positive controls retain signed/unsigned aliases, nested member permissions,
allocated-object type establishment and exact memory after scoped stores.
Negative controls reject unrelated types, false aggregate character aliases,
readonly writes, volatile pure accesses, misalignment and ended lifetimes.
These controls supplement the general lookup and memory correspondence laws.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.C11.ObjectAccessControls

open AccessTypes ObjectAccessMemory IntegerObjectControls
open ByteStorageData ObjectControls
open Mettapedia.Machines.CMemory

def signedType : IntegerType IntegerExtension := .signed (.standard .int)
def unsignedType : IntegerType IntegerExtension := .unsigned (.standard .int)
def intType : ObjectType := .scalar (.integer signedType)
def uintType : ObjectType := .scalar (.integer unsignedType)
def floatType : ObjectType := .scalar (.real .float)
def charType : ObjectType := .scalar .plainCharacter
def ucharType : ObjectType := .scalar (.integer (.unsigned (.standard .char)))

theorem signed_unsigned_alias_allowed : permits uintType intType = true := by rfl
theorem unsigned_signed_alias_allowed : permits intType uintType = true := by rfl
theorem same_integer_allowed : permits intType intType = true := by rfl
theorem floating_alias_rejected : permits floatType intType = false := by decide +kernel
theorem plain_character_may_observe_integer : permits charType intType = true := by decide +kernel
theorem unsigned_character_may_observe_integer : permits ucharType intType = true := by decide +kernel
theorem character_type_is_distinct : compatible charType ucharType = false := by rfl
theorem boolean_is_not_unsigned_counterpart :
    permits (.scalar (.integer .boolean)) uintType = false := by decide +kernel
theorem real_and_complex_are_distinct :
    compatible floatType (.scalar (.complex .float)) = false := by rfl
theorem pointer_referents_retained :
    permits (.scalar (.pointer 17)) (.scalar (.pointer 18)) = false := by decide +kernel
theorem same_pointer_referent_allowed :
    permits (.scalar (.pointer 17)) (.scalar (.pointer 17)) = true := by rfl

def enumA : ObjectType := .scalar (.enumeration 10 (.signed (.standard .int)))
def enumB : ObjectType := .scalar (.enumeration 11 (.signed (.standard .int)))
theorem enum_integer_compatible : compatible enumA intType = true := by rfl
theorem integer_other_enum_compatible : compatible intType enumB = true := by rfl
theorem compatibility_not_closed_transitively : compatible enumA enumB = false := by rfl
theorem equal_enum_width_does_not_remove_identity : permits enumA enumB = false := by decide +kernel

def nestedAggregate : ObjectType := .aggregate .structure 1
  [floatType, .aggregate .union 2 [uintType, charType]]
theorem nested_corresponding_member_allowed : permits nestedAggregate intType = true := by decide +kernel
theorem character_member_is_not_universal_alias :
    permits (.aggregate .structure 3 [charType]) intType = false := by decide +kernel
theorem array_member_relation_allowed : permits (.array uintType 3) intType = true := by decide +kernel
theorem unrelated_array_rejected : permits (.array floatType 3) intType = false := by decide +kernel
theorem complete_array_extent_retained : compatible (.array intType 3) (.array intType 4) = false := by rfl
theorem struct_and_union_identities_distinct :
    compatible (.aggregate .structure 1 [intType]) (.aggregate .union 1 [intType]) = false := by rfl
theorem qualification_does_not_change_alias_permission :
    (⟨uintType, {const := true, volatile := true}⟩ : AccessTypes.View).permits intType = true := by rfl

def declaredInt : EffectiveTypes.Info := ⟨some intType, none⟩
def retainedInt : EffectiveTypes.Info := ⟨none, some intType⟩
theorem declared_read_type_retained :
    EffectiveTypes.admitRead declaredInt uintType = some intType := by rfl
theorem retained_read_type_retained :
    EffectiveTypes.admitRead retainedInt uintType = some intType := by rfl
theorem wrong_declared_read_rejected : EffectiveTypes.admitRead declaredInt floatType = none := by decide +kernel
theorem wrong_retained_read_rejected : EffectiveTypes.admitRead retainedInt floatType = none := by decide +kernel
theorem fresh_read_uses_access_type :
    EffectiveTypes.admitRead {} floatType = some floatType := by rfl
theorem declared_store_cannot_retype : EffectiveTypes.admitStore declaredInt floatType = none := by decide +kernel
theorem allocated_store_can_retype :
    EffectiveTypes.admitStore retainedInt floatType = some (floatType, ⟨none, some floatType⟩) := by rfl
theorem character_store_not_laundered_into_type_establishment :
    EffectiveTypes.admitStore retainedInt charType = none := by rfl
theorem whole_copy_retains_source_type :
    (EffectiveTypes.copyType declaredInt {}).retained = some intType := rfl
theorem whole_copy_preserves_declared_target :
    (EffectiveTypes.copyType ⟨some floatType, none⟩ declaredInt).declared = some intType := rfl

def intLayout : Layout := ⟨integerValueProfile .lp64, signedType, int32 .little, rfl⟩
def uintLayout : Layout := ⟨integerValueProfile .lp64, unsignedType, uint32, rfl⟩
def object : Identity := ⟨⟨7, 0⟩, 4⟩
def secondObject : Identity := ⟨⟨7, 4⟩, 4⟩
def intView : AccessTypes.View := ⟨intType, {}⟩
def uintView : AccessTypes.View := ⟨uintType, {}⟩
def location : Lvalue := ⟨object, intView⟩
def otherLocation : Lvalue := ⟨secondObject, intView⟩
def unsignedLocation : Lvalue := location.cast uintView
def readonlyRecord : ObjectAccessMemory.Record := declaredRecord ⟨intType, {const := true}⟩ 4
def integerRecord : ObjectAccessMemory.Record := declaredRecord intView 4
def state : State byte8 := ⟨emptyStorage, [(object, integerRecord), (secondObject, integerRecord)]⟩
def readonlyState : State byte8 := ⟨emptyStorage, [(object, readonlyRecord)]⟩
def allocatedState : State byte8 := ⟨emptyStorage, [(object, allocatedRecord 4)]⟩

theorem initialized_object_read : ObjectAccessMemory.read intLayout state location =
    some (.integer (.value 0 false)) := by rfl
theorem unsigned_view_reads_same_initial_bytes : ObjectAccessMemory.read uintLayout state unsignedLocation =
    some (.integer (.value 0 false)) := by rfl
theorem wrong_source_integer_type_rejected : ObjectAccessMemory.read intLayout state unsignedLocation = none := by rfl
theorem readonly_object_can_be_read : ObjectAccessMemory.read intLayout readonlyState location =
    some (.integer (.value 0 false)) := by rfl
theorem cast_away_const_does_not_authorize_write :
    ObjectAccessMemory.store intLayout readonlyState location minusSeventeen = none := by rfl
theorem const_access_view_rejects_store :
    ObjectAccessMemory.store intLayout state (location.cast ⟨intType, {const := true}⟩) minusSeventeen = none := by rfl
theorem volatile_access_requires_interaction :
    ObjectAccessMemory.read intLayout state (location.cast ⟨intType, {volatile := true}⟩) = none := by rfl
theorem volatile_object_requires_interaction :
    ObjectAccessMemory.read intLayout ⟨emptyStorage, [(object, declaredRecord ⟨intType, {volatile := true}⟩ 4)]⟩
      location = none := by rfl
theorem zero_alignment_rejected :
    ObjectAccessMemory.read intLayout ⟨emptyStorage, [(object, declaredRecord intView 0)]⟩ location = none := by rfl
theorem misaligned_object_rejected :
    ObjectAccessMemory.read intLayout ⟨emptyStorage, [(⟨⟨7, 1⟩, 4⟩, integerRecord)]⟩
      ⟨⟨⟨7, 1⟩, 4⟩, intView⟩ = none := by rfl
theorem wrong_extent_rejected :
    ObjectAccessMemory.read intLayout ⟨emptyStorage, [(⟨⟨7, 0⟩, 2⟩, integerRecord)]⟩
      ⟨⟨⟨7, 0⟩, 2⟩, intView⟩ = none := by rfl
theorem ended_lifetime_rejects_retained_view :
    ObjectAccessMemory.read intLayout ⟨[(7, ⟨false, List.replicate 8 (some (b 0))⟩)], [(object, integerRecord)]⟩
      location = none := by rfl
theorem absent_object_metadata_rejected : ObjectAccessMemory.read intLayout ⟨emptyStorage, []⟩ location = none := by rfl

def afterStore : State byte8 :=
  ⟨saved, (object, integerRecord) :: state.catalog⟩

theorem store_saves_complete_state : ObjectAccessMemory.store intLayout state location minusSeventeen =
    some afterStore := by rfl
theorem stored_signed_value_retained : ObjectAccessMemory.read intLayout afterStore location =
    some (.integer (.value (-17) false)) := by rfl
theorem alias_reads_representation_not_conversion : ObjectAccessMemory.read uintLayout afterStore unsignedLocation =
    some (.integer (.value 4294967279 false)) := by rfl
theorem disjoint_object_value_retained : ObjectAccessMemory.read intLayout afterStore otherLocation =
    some (.integer (.value 0 false)) := by rfl
theorem aliases_retain_conflict_identity :
    Sequencing.conflicts location.writeEvent unsignedLocation.readEvent = true := by rfl
theorem distinct_objects_do_not_conflict :
    Sequencing.conflicts location.writeEvent otherLocation.readEvent = false := by rfl

def environment : ScopedLvalues.Environment := [[("x", location), ("alias", unsignedLocation)], [("x", otherLocation)]]
theorem nearest_scope_selected : ScopedLvalues.lookup environment "x" = some location := by rfl
theorem alias_binding_retained : ScopedLvalues.lookup environment "alias" = some unsignedLocation := by rfl
theorem absent_binding_rejected : ScopedLvalues.lookup environment "missing" = none := by rfl
theorem empty_frames_are_skipped : ScopedLvalues.lookup [[], [], [("x", location)]] "x" = some location := by rfl
theorem first_binding_in_frame_selected :
    ScopedLvalues.lookup [[("x", location), ("x", otherLocation)]] "x" = some location := by rfl
theorem scoped_read_observes_saved_memory : ScopedLvalues.read intLayout afterStore environment "x" =
    some (.integer (.value (-17) false)) := by rfl
theorem scoped_alias_observes_saved_memory : ScopedLvalues.read uintLayout afterStore environment "alias" =
    some (.integer (.value 4294967279 false)) := by rfl
theorem scoped_store_updates_selected_object : ScopedLvalues.store intLayout state environment "x" minusSeventeen =
    some afterStore := by rfl

theorem source_identifier_retained :
    CestaObjectAccess.identifierName (.node "Var" [.text "x"]) = some "x" := by rfl
theorem wrong_identifier_constructor_rejected :
    CestaObjectAccess.identifierName (.node "IntConst" [.text "17"]) = none := by rfl
theorem erased_identifier_rejected :
    CestaObjectAccess.identifierName (.node "Var" []) = none := by rfl
theorem extra_identifier_child_rejected :
    CestaObjectAccess.identifierName (.node "Var" [.text "x", .text "alias"]) = none := by rfl
theorem nested_expression_is_not_identifier_token :
    CestaObjectAccess.identifierName (.node "Var" [.node "Var" [.text "x"]]) = none := by rfl

end Mettapedia.Languages.C11.ObjectAccessControls
