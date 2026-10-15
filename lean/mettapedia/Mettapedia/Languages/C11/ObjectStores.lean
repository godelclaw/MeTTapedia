import Mettapedia.Languages.C11.ObjectAccessMemory

/-!
# Whole-object stores with character effective-type preservation

An ordinary non-character store uses the existing type-establishing rule.
A character store retains the object's effective-type information and uses
the character access permission. The executable permission selector agrees
with these independently constructed rules. Typed whole-object integer
stores join this permission to the existing bounds, lifetime, qualifier,
alignment and owned byte-writing judgments.

Character accesses to portions of larger objects require a constructed
subobject/byte-region adapter. This module supplies complete admitted object
stores, not that adapter, native effect authority or volatile interaction.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.C11.ObjectStores

open AccessTypes ObjectAccessMemory
open Mettapedia.Machines.CMemory
open Mettapedia.GSLT.SeparationAlgebra
open scoped Mettapedia.GSLT.SeparationAlgebra

inductive Permission (info : EffectiveTypes.Info) (view : ObjectType) : ObjectType → EffectiveTypes.Info → Prop where
  | ordinary (type : ObjectType) (after : EffectiveTypes.Info)
      (permitted : EffectiveTypes.StorePermission info view type after) : Permission info view type after
  | declaredCharacter (type : ObjectType) (declared : info.declared = some type)
      (isCharacter : AccessTypes.character view = true) : Permission info view type info
  | allocatedCharacter (untyped : info.declared = none) (isCharacter : AccessTypes.character view = true) :
      Permission info view view info

def selectPermission (info : EffectiveTypes.Info) (view : ObjectType) : Option (ObjectType × EffectiveTypes.Info) :=
  if AccessTypes.character view then some ((info.declared).getD view, info)
  else EffectiveTypes.admitStore info view

theorem ordinary_non_character {info : EffectiveTypes.Info} {view type : ObjectType} {after : EffectiveTypes.Info}
    (permitted : EffectiveTypes.StorePermission info view type after) : AccessTypes.character view = false := by
  cases permitted <;> assumption

theorem selectPermission_sound (info : EffectiveTypes.Info) (view type : ObjectType) (after : EffectiveTypes.Info)
    (accepted : selectPermission info view = some (type, after)) : Permission info view type after := by
  cases character : AccessTypes.character view with
  | false =>
      simp only [selectPermission, character, Bool.false_eq_true, ↓reduceIte] at accepted
      exact .ordinary type after (EffectiveTypes.admitStore_sound _ _ _ _ accepted)
  | true =>
      cases declared : info.declared with
      | none =>
          simp only [selectPermission, character, ↓reduceIte, declared, Option.getD_none, Option.some.injEq, Prod.mk.injEq] at accepted
          obtain ⟨rfl, rfl⟩ := accepted
          exact .allocatedCharacter declared character
      | some actual =>
          simp only [selectPermission, character, ↓reduceIte, declared, Option.getD_some, Option.some.injEq, Prod.mk.injEq] at accepted
          obtain ⟨rfl, rfl⟩ := accepted
          exact .declaredCharacter actual declared character

theorem selectPermission_complete (info : EffectiveTypes.Info) (view type : ObjectType) (after : EffectiveTypes.Info)
    (permitted : Permission info view type after) : selectPermission info view = some (type, after) := by
  cases permitted
  case ordinary =>
    rename_i permission
    simp only [selectPermission, ordinary_non_character permission, Bool.false_eq_true, ↓reduceIte,
      EffectiveTypes.admitStore_complete _ _ _ _ permission]
  case declaredCharacter =>
    rename_i declared isCharacter
    simp [selectPermission, isCharacter, declared]
  case allocatedCharacter =>
    rename_i untyped isCharacter
    simp [selectPermission, isCharacter, untyped]

theorem selectPermission_iff (info : EffectiveTypes.Info) (view type : ObjectType) (after : EffectiveTypes.Info) :
    selectPermission info view = some (type, after) ↔ Permission info view type after :=
  ⟨selectPermission_sound info view type after, selectPermission_complete info view type after⟩

theorem declared_preserved {info after : EffectiveTypes.Info} {view type : ObjectType}
    (permitted : Permission info view type after) : after.declared = info.declared := by
  cases permitted
  case ordinary =>
    rename_i permission
    exact EffectiveTypes.store_preserves_declared permission
  all_goals rfl

theorem character_retains_type {info after : EffectiveTypes.Info} {view type : ObjectType}
    (permitted : Permission info view type after) (isCharacter : AccessTypes.character view = true) : after = info := by
  cases permitted
  case ordinary =>
    rename_i permission
    have impossible := ordinary_non_character permission
    rw [isCharacter] at impossible
    cases impossible
  all_goals rfl

theorem readable_after_store {info after : EffectiveTypes.Info} {view type : ObjectType}
    (permitted : Permission info view type after) : ∃ readType, EffectiveTypes.ReadPermission after view readType := by
  cases permitted
  case ordinary =>
    rename_i permission
    exact ⟨_, EffectiveTypes.store_read_permission permission⟩
  case declaredCharacter =>
    exact ⟨_, EffectiveTypes.readingType_sound _ _, .character (by assumption)⟩
  case allocatedCharacter =>
    rename_i isCharacter
    exact ⟨_, EffectiveTypes.readingType_sound _ _, .character isCharacter⟩

def store (layout : Layout) (before : State layout.representation.characters) (location : Lvalue)
    (value : IntegerValue layout.representation.integer) : Option (State layout.representation.characters) := do
  let record ← before.catalog.lookup location.object
  if PureView layout record location ∧ Writable record location then
    let typed ← selectPermission record.info location.view.type
    let storage ← IntegerMemory.storeInteger layout.representation before.storage location.object.address value
    some ⟨storage, (location.object, {record with info := typed.2}) :: before.catalog⟩
  else none

def Writing (layout : Layout) (before after : SemanticState layout.representation.characters)
    (location : Lvalue) (value : IntegerValue layout.representation.integer) : Prop :=
  ∃ record type info, before.catalog.lookup location.object = some record ∧
    PureView layout record location ∧ Writable record location ∧ Permission record.info location.view.type type info ∧
    IntegerMemory.Writing layout.representation before.memory after.memory location.object.address value ∧
    after.catalog = (location.object, {record with info := info}) :: before.catalog

theorem store_sound (layout : Layout) (before after : State layout.representation.characters) (location : Lvalue)
    (value : IntegerValue layout.representation.integer) (executed : store layout before location value = some after) :
    Writing layout (represent before) (represent after) location value := by
  cases found : before.catalog.lookup location.object with
  | none => simp [store, found] at executed
  | some record =>
      by_cases valid : PureView layout record location ∧ Writable record location
      · cases admitted : selectPermission record.info location.view.type with
        | none => simp [store, found, valid, admitted] at executed
        | some typed =>
            cases written : IntegerMemory.storeInteger layout.representation before.storage location.object.address value with
            | none => simp [store, found, written] at executed
            | some storage =>
                simp [store, found, valid, admitted, written] at executed
                subst after
                exact ⟨record, typed.1, typed.2, found, valid.1, valid.2,
                  selectPermission_sound _ _ _ _ admitted, IntegerMemory.storeInteger_sound _ _ _ _ _ written, rfl⟩
      · simp [store, found, valid] at executed

theorem store_complete (layout : Layout) (before : State layout.representation.characters)
    (after : SemanticState layout.representation.characters) (location : Lvalue)
    (value : IntegerValue layout.representation.integer) (writing : Writing layout (represent before) after location value) :
    ∃ saved, store layout before location value = some saved ∧ represent saved = after := by
  obtain ⟨record, type, info, found, pure, writable, permission, writing, catalog⟩ := writing
  change before.catalog.lookup location.object = some record at found
  obtain ⟨storage, written, memory⟩ := IntegerMemory.storeInteger_complete _ _ _ _ _ writing
  have admitted := selectPermission_complete _ _ _ _ permission
  refine ⟨⟨storage, (location.object, {record with info := info}) :: before.catalog⟩, ?_, ?_⟩
  · simp only [store, found, pure, writable, and_self, ↓reduceIte, admitted, written, bind, Option.bind_some]
  · cases after
    simp_all only [represent]

theorem read_after_store (layout : Layout) (before after : State layout.representation.characters)
    (location : Lvalue) (value : IntegerValue layout.representation.integer)
    (executed : store layout before location value = some after) :
    ObjectAccessMemory.read layout after location = some (.integer (.value value.value false)) := by
  cases found : before.catalog.lookup location.object with
  | none => simp [store, found] at executed
  | some record =>
      by_cases valid : PureView layout record location ∧ Writable record location
      · cases admitted : selectPermission record.info location.view.type with
        | none => simp [store, found, valid, admitted] at executed
        | some typed =>
            cases written : IntegerMemory.storeInteger layout.representation before.storage location.object.address value with
            | none => simp [store, found, written] at executed
            | some storage =>
                simp [store, found, valid, admitted, written] at executed
                subst after
                have permission := selectPermission_sound _ _ _ _ admitted
                obtain ⟨readType, allowedRead⟩ := readable_after_store permission
                have readable := (EffectiveTypes.admitRead_iff _ _ _).mpr allowedRead
                have result := IntegerMemory.read_after_store _ _ _ _ _ written
                have pure : PureView layout {record with info := typed.2} location := valid.1
                simp [ObjectAccessMemory.read, List.lookup, pure, readable, result]
      · simp [store, found, valid] at executed

theorem Writing.frame (layout : Layout) (before after : SemanticState layout.representation.characters)
    (frame : Heap (Excl (Option (ByteStorageData.Byte layout.representation.characters))))
    (location : Lvalue) (value : IntegerValue layout.representation.integer)
    (writing : Writing layout before after location value) (separate : before.memory ## frame) :
    Writing layout ⟨before.memory + frame, before.catalog⟩ ⟨after.memory + frame, after.catalog⟩ location value ∧
      after.memory ## frame := by
  obtain ⟨record, type, info, found, pure, writable, permission, written, catalog⟩ := writing
  obtain ⟨framed, retained⟩ := IntegerMemory.Writing.frame _ _ _ _ _ _ written separate
  exact ⟨⟨record, type, info, found, pure, writable, permission, framed, catalog⟩, retained⟩

end Mettapedia.Languages.C11.ObjectStores
