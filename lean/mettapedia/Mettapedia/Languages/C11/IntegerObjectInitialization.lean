import Mettapedia.Languages.C11.IntegerObjectConstruction

/-!
# Contents of constructed integer declarations

All-zero byte initialization is shown to denote the ordinary integer zero
for every admitted integer format, character width, byte order and padding
policy. The proof joins the independently specified heap read, byte packing,
bit interpretation, declared type and alignment rules.

Indeterminate construction retains owned byte markers but produces no
initialized scalar value through this reader. This is a representation
boundary, not a classification of every C11 indeterminate expression as
undefined behavior. Executing explicit source initializers, volatile reads
and character reads needs the corresponding source/access rules.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.C11.IntegerObjectInitialization

open IntegerObjectConstruction ByteRanges ByteStorageData ObjectAccessMemory

theorem canonicalWord_zero (format : IntegerFormat) : IntegerBits.canonicalWord format 0 = 0 := by
  cases format <;> simp [IntegerBits.canonicalWord]

theorem encodeLittle_zero (characters : ByteStorageData.Profile) (count : Nat) :
    BytePacking.encodeLittle characters count 0 = List.replicate count (BitVec.ofNat characters.charBits 0) := by
  induction count with
  | zero => rfl
  | succ count ih => simp only [BytePacking.encodeLittle, Nat.zero_div, ih, List.replicate_succ]

theorem orient_zero (characters : ByteStorageData.Profile) (order : BytePacking.Order) (count : Nat) :
    BytePacking.orient order (List.replicate count (BitVec.ofNat characters.charBits 0)) =
      List.replicate count (BitVec.ofNat characters.charBits 0) := by
  cases order <;> simp [BytePacking.orient]

theorem storeObject_zero (profile : IntegerObject.Profile) :
    IntegerObject.storeObject profile 0 = List.replicate profile.byteCount (BitVec.ofNat profile.characters.charBits 0) := by
  rw [IntegerObject.storeObject, canonicalWord_zero, encodeLittle_zero, orient_zero]

theorem zero_bytes_reading (profile : IntegerObject.Profile) :
    IntegerObject.Reading profile (List.replicate profile.byteCount (BitVec.ofNat profile.characters.charBits 0))
      (.integer (.value 0 false)) := by
  rw [← storeObject_zero]
  exact IntegerObject.readObject_sound _ _ _
    (IntegerObject.readObject_storeObject profile 0 profile.integer.zero_representable)

theorem initialized_zero (characters : ByteStorageData.Profile) (count : Nat) :
    IntegerMemory.initialized (List.replicate count (some (BitVec.ofNat characters.charBits 0))) =
      some (List.replicate count (BitVec.ofNat characters.charBits 0)) := by
  rw [← List.map_replicate (f := some)]
  exact IntegerMemory.initialized_some _

theorem indeterminate_refused {Byte : Type} (count : Nat) (positive : 0 < count) :
    IntegerMemory.initialized (List.replicate count (none : Option Byte)) = none := by
  cases count with
  | zero => omega
  | succ count => rfl

theorem element_read_permission (declaration : Declaration) (element : ObjectLayout.Layout)
    (identity : Mettapedia.Machines.CMemory.BlockId) (index : Fin declaration.shape.count) :
    EffectiveTypes.ReadPermission (elementRecord declaration element).info
      (elementLocation declaration element identity index).view.type (.scalar (.integer declaration.integer)) := by
  exact ⟨.declared _ rfl, .direct (.inl (.refl _))⟩

theorem constructed_zero_reading (model : IntegerMemoryModel.Model) (memory : ObjectAccessMemory.State model.characters)
    (arrays : ArrayPointers.Catalog) (declaration : Declaration) (element : ObjectLayout.Layout)
    (identity : Mettapedia.Machines.CMemory.BlockId) (result : Constructed model)
    (executed : construct model memory arrays declaration element identity .zero = some result)
    (index : Fin declaration.shape.count) :
    ObjectAccessMemory.Reading (model.layout declaration.integer) (ObjectAccessMemory.represent result.memory)
      (elementLocation declaration element identity index) (.integer (.value 0 false)) := by
  have formed := (construct_sound _ _ _ _ _ _ _ _ executed).1
  change element.bytes = (model.objects declaration.integer).byteCount at formed
  refine ⟨elementRecord declaration element, .scalar (.integer declaration.integer),
    construct_records_element _ _ _ _ _ _ _ _ executed index,
    element_pure _ _ _ _ formed index, element_read_permission _ _ _ _, ?_⟩
  refine ⟨List.replicate element.bytes (BitVec.ofNat model.characters.charBits 0), ?_, ?_⟩
  · have read := readBytes_sound result.memory.storage _ _
      (constructed_raw_element _ _ _ _ _ _ _ _ executed index)
    change ReadRange (heap result.memory.storage)
      ⟨(elementLocation declaration element identity index).object.address, (model.objects declaration.integer).byteCount⟩
      ((List.replicate element.bytes (BitVec.ofNat model.characters.charBits 0)).map some)
    rw [← formed]
    simpa only [elementLocation, InitialContents.byte, List.map_replicate] using read
  · rw [formed]
    exact zero_bytes_reading (model.layout declaration.integer).representation

theorem constructed_zero_read (model : IntegerMemoryModel.Model) (memory : ObjectAccessMemory.State model.characters)
    (arrays : ArrayPointers.Catalog) (declaration : Declaration) (element : ObjectLayout.Layout)
    (identity : Mettapedia.Machines.CMemory.BlockId) (result : Constructed model)
    (executed : construct model memory arrays declaration element identity .zero = some result)
    (index : Fin declaration.shape.count) :
    ObjectAccessMemory.read (model.layout declaration.integer) result.memory
      (elementLocation declaration element identity index) = some (.integer (.value 0 false)) :=
  ObjectAccessMemory.read_complete _ _ _ _ (constructed_zero_reading _ _ _ _ _ _ _ executed index)

theorem constructed_indeterminate_integer_refused (model : IntegerMemoryModel.Model)
    (memory : ObjectAccessMemory.State model.characters) (arrays : ArrayPointers.Catalog)
    (declaration : Declaration) (element : ObjectLayout.Layout)
    (identity : Mettapedia.Machines.CMemory.BlockId) (result : Constructed model)
    (executed : construct model memory arrays declaration element identity .indeterminate = some result)
    (index : Fin declaration.shape.count) :
    IntegerMemory.readInteger (model.layout declaration.integer).representation result.memory.storage
      (elementLocation declaration element identity index).object.address = none := by
  have formed := (construct_sound _ _ _ _ _ _ _ _ executed).1
  have raw := constructed_raw_element _ _ _ _ _ _ _ _ executed index
  have positive : 0 < element.bytes := element.positive
  have unknown := @indeterminate_refused (Byte model.characters) element.bytes positive
  change element.bytes = (model.objects declaration.integer).byteCount at formed
  change readBytes result.memory.storage
    ⟨(elementLocation declaration element identity index).object.address, element.bytes⟩ =
      some (List.replicate element.bytes none) at raw
  change (readBytes result.memory.storage
    ⟨(elementLocation declaration element identity index).object.address, (model.objects declaration.integer).byteCount⟩).bind _ = none
  rw [← formed, raw]
  simp only [Option.bind_some, unknown]
  rfl

theorem constructed_indeterminate_read_refused (model : IntegerMemoryModel.Model)
    (memory : ObjectAccessMemory.State model.characters) (arrays : ArrayPointers.Catalog)
    (declaration : Declaration) (element : ObjectLayout.Layout)
    (identity : Mettapedia.Machines.CMemory.BlockId) (result : Constructed model)
    (executed : construct model memory arrays declaration element identity .indeterminate = some result)
    (index : Fin declaration.shape.count) :
    ObjectAccessMemory.read (model.layout declaration.integer) result.memory
      (elementLocation declaration element identity index) = none := by
  have integer := constructed_indeterminate_integer_refused _ _ _ _ _ _ _ executed index
  unfold ObjectAccessMemory.read
  cases result.memory.catalog.lookup (elementLocation declaration element identity index).object with
  | none => rfl
  | some record =>
      dsimp only [bind, Option.bind_some]
      split
      · cases EffectiveTypes.admitRead record.info (elementLocation declaration element identity index).view.type <;>
          simp only [Option.bind_none, Option.bind_some, integer]
      · rfl

end Mettapedia.Languages.C11.IntegerObjectInitialization
