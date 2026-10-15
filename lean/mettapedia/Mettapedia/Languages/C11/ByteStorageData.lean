import Mettapedia.Languages.C11.ObjectStep

/-!
# Checked numeric data for finite byte storage

The byte profile names CHAR_BIT and enforces the C11 minimum. Finite data
retain every allocation record, including shadowed and dead records, every
indeterminate marker, and the array catalog. Byte payloads outside the
profile's unsigned-character range are rejected instead of truncated.
Both codec inverse laws are proved for bytes, blocks, storage and states.

This constructs a finite representation and its ownership heap; it does not
authenticate execution history, source declarations, physical addresses or
external publication authority. The data are Lean records and lists. A
Cesta/GSLT or MeTTa term codec requires its own constructed syntax adapter.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.C11.ByteStorageData

open Mettapedia.Machines.CMemory

structure Profile where
  charBits : Nat
  minimum : 8 ≤ charBits
  deriving DecidableEq, Repr

abbrev Byte (profile : Profile) := BitVec profile.charBits

def encodeByte {profile : Profile} (byte : Byte profile) : Nat := byte.toNat

def decodeByte (profile : Profile) (data : Nat) : Option (Byte profile) :=
  if inside : data < 2 ^ profile.charBits then some (BitVec.ofNatLT data inside) else none

@[simp]
theorem decodeByte_encode (profile : Profile) (byte : Byte profile) :
    decodeByte profile (encodeByte byte) = some byte := by
  unfold decodeByte encodeByte
  rw [dif_pos byte.isLt]
  exact congrArg some (BitVec.eq_of_toNat_eq rfl)

theorem encodeByte_decode (profile : Profile) (data : Nat) (byte : Byte profile)
    (decoded : decodeByte profile data = some byte) : encodeByte byte = data := by
  unfold decodeByte at decoded
  split at decoded
  · cases decoded
    rfl
  · cases decoded

def encodeContent {profile : Profile} (content : Option (Byte profile)) : Option Nat := content.map encodeByte

def decodeContent (profile : Profile) : Option Nat → Option (Option (Byte profile))
  | none => some none
  | some data => (decodeByte profile data).map some

@[simp]
theorem decodeContent_encode (profile : Profile) (content : Option (Byte profile)) :
    decodeContent profile (encodeContent content) = some content := by
  cases content <;> simp [encodeContent, decodeContent]

theorem encodeContent_decode (profile : Profile) (data : Option Nat) (content : Option (Byte profile))
    (decoded : decodeContent profile data = some content) : encodeContent content = data := by
  cases data with
  | none => cases decoded; rfl
  | some data =>
      cases actual : decodeByte profile data with
      | none => simp [decodeContent, actual] at decoded
      | some byte =>
          simp only [decodeContent, actual, Option.map_some] at decoded
          cases decoded
          exact congrArg some (encodeByte_decode profile data byte actual)

def encodeContents {profile : Profile} (contents : List (Option (Byte profile))) : List (Option Nat) :=
  contents.map encodeContent

def decodeContents (profile : Profile) : List (Option Nat) → Option (List (Option (Byte profile)))
  | [] => some []
  | head :: tail => do
      let content ← decodeContent profile head
      let rest ← decodeContents profile tail
      some (content :: rest)

@[simp]
theorem decodeContents_encode (profile : Profile) (contents : List (Option (Byte profile))) :
    decodeContents profile (encodeContents contents) = some contents := by
  induction contents with
  | nil => rfl
  | cons head tail ih =>
      change decodeContents profile (encodeContent head :: encodeContents tail) = some (head :: tail)
      simp only [decodeContents, decodeContent_encode, ih, bind, Option.bind_some]

theorem encodeContents_decode (profile : Profile) (data : List (Option Nat))
    (contents : List (Option (Byte profile))) (decoded : decodeContents profile data = some contents) :
    encodeContents contents = data := by
  induction data generalizing contents with
  | nil => cases decoded; rfl
  | cons head tail ih =>
      cases first : decodeContent profile head with
      | none => simp [decodeContents, first] at decoded
      | some content =>
          cases rest : decodeContents profile tail with
          | none => simp [decodeContents, first, rest] at decoded
          | some remaining =>
              simp only [decodeContents, first, rest, bind, Option.bind_some] at decoded
              cases decoded
              simp only [encodeContents, List.map_cons]
              rw [encodeContent_decode profile head content first]
              exact congrArg (head :: ·) (ih remaining rest)

structure BlockData where
  live : Bool
  contents : List (Option Nat)
  deriving DecidableEq, Repr

def encodeBlock {profile : Profile} (block : ExecutableStorage.Block (Byte profile)) : BlockData :=
  ⟨block.live, encodeContents block.cells⟩

def decodeBlock (profile : Profile) (data : BlockData) : Option (ExecutableStorage.Block (Byte profile)) :=
  (decodeContents profile data.contents).map fun cells => ⟨data.live, cells⟩

@[simp]
theorem decodeBlock_encode (profile : Profile) (block : ExecutableStorage.Block (Byte profile)) :
    decodeBlock profile (encodeBlock block) = some block := by
  cases block
  simp [decodeBlock, encodeBlock]

theorem encodeBlock_decode (profile : Profile) (data : BlockData) (block : ExecutableStorage.Block (Byte profile))
    (decoded : decodeBlock profile data = some block) : encodeBlock block = data := by
  cases contents : decodeContents profile data.contents with
  | none => simp [decodeBlock, contents] at decoded
  | some cells =>
      simp only [decodeBlock, contents, Option.map_some] at decoded
      cases decoded
      have equal := encodeContents_decode profile data.contents cells contents
      cases data
      simp only [encodeBlock, equal]

abbrev StorageData := List (BlockId × BlockData)

def encodeStorage {profile : Profile} (storage : ByteRanges.Storage.State (Byte profile)) : StorageData :=
  storage.map fun entry => (entry.1, encodeBlock entry.2)

def decodeStorage (profile : Profile) : StorageData → Option (ByteRanges.Storage.State (Byte profile))
  | [] => some []
  | (identity, data) :: tail => do
      let block ← decodeBlock profile data
      let rest ← decodeStorage profile tail
      some ((identity, block) :: rest)

@[simp]
theorem decodeStorage_encode (profile : Profile) (storage : ByteRanges.Storage.State (Byte profile)) :
    decodeStorage profile (encodeStorage storage) = some storage := by
  induction storage with
  | nil => rfl
  | cons entry tail ih =>
      rcases entry with ⟨identity, block⟩
      change decodeStorage profile ((identity, encodeBlock block) :: encodeStorage tail) =
        some ((identity, block) :: tail)
      simp only [decodeStorage, decodeBlock_encode, ih, bind, Option.bind_some]

theorem encodeStorage_decode (profile : Profile) (data : StorageData)
    (storage : ByteRanges.Storage.State (Byte profile)) (decoded : decodeStorage profile data = some storage) :
    encodeStorage storage = data := by
  induction data generalizing storage with
  | nil => cases decoded; rfl
  | cons entry tail ih =>
      rcases entry with ⟨identity, data⟩
      cases first : decodeBlock profile data with
      | none => simp [decodeStorage, first] at decoded
      | some block =>
          cases rest : decodeStorage profile tail with
          | none => simp [decodeStorage, first, rest] at decoded
          | some remaining =>
              simp only [decodeStorage, first, rest, bind, Option.bind_some] at decoded
              cases decoded
              simp only [encodeStorage, List.map_cons]
              rw [encodeBlock_decode profile data block first]
              exact congrArg ((identity, data) :: ·) (ih remaining rest)

structure StateData where
  storage : StorageData
  catalog : ArrayPointers.Catalog
  deriving DecidableEq, Repr

def encodeState {profile : Profile} (state : ObjectStep.State (Byte profile)) : StateData :=
  ⟨encodeStorage state.storage, state.catalog⟩

def decodeState (profile : Profile) (data : StateData) : Option (ObjectStep.State (Byte profile)) :=
  (decodeStorage profile data.storage).map fun storage => ⟨storage, data.catalog⟩

@[simp]
theorem decodeState_encode (profile : Profile) (state : ObjectStep.State (Byte profile)) :
    decodeState profile (encodeState state) = some state := by
  cases state
  simp [encodeState, decodeState]

theorem encodeState_decode (profile : Profile) (data : StateData) (state : ObjectStep.State (Byte profile))
    (decoded : decodeState profile data = some state) : encodeState state = data := by
  cases actual : decodeStorage profile data.storage with
  | none => simp [decodeState, actual] at decoded
  | some storage =>
      simp only [decodeState, actual, Option.map_some] at decoded
      cases decoded
      have equal := encodeStorage_decode profile data.storage storage actual
      cases data
      simp only [encodeState, equal]

theorem encodeState_injective (profile : Profile) : Function.Injective (@encodeState profile) := by
  intro first second equal
  have decoded := congrArg (decodeState profile) equal
  rw [decodeState_encode, decodeState_encode] at decoded
  exact Option.some.inj decoded

end Mettapedia.Languages.C11.ByteStorageData
