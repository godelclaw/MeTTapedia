import Mettapedia.Languages.C11.ObjectLayout
import Mettapedia.GSLT.Distinction.ProductiveBlocks

/-!
# Executable byte/object operations and their retained step state

This interface joins raw representation access, allocation retirement and
array-relative pointer operations. Every defined executable result has an
independent resource-heap transition. Conversely, every such transition
from a represented state has a constructed executable result under an
allocator choice, with exactly the represented heap and catalog endpoint.
Heap correspondence is extensional: persistent finite storage may retain
shadowed records that the heap lookup does not observe.

Allocation and retirement are storage-kernel operations. C library malloc,
free and realloc still need size/alignment, duration and effective-type
contracts. The catalog must be constructed by the source/type layer; a
region descriptor does not authenticate a C declaration or publication.
Whole C expression/statement control and native refinement are not claimed.

The driver saves the complete finite state after one response. Its events
are semantic receipts, not authority to commit host effects. Step charges
count kernel requests; separate accounts count byte reads and writes.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.C11.ObjectStep

open Mettapedia.Machines.CMemory
open Mettapedia.GSLT.SeparationAlgebra
open Mettapedia.GSLT.Distinction.ProductiveBlocks
open ByteRanges

structure State (Byte : Type) where
  storage : Storage.State Byte
  catalog : ArrayPointers.Catalog
  deriving DecidableEq, Repr

structure SemanticState (Byte : Type) where
  memory : Heap (Excl (Option Byte))
  catalog : ArrayPointers.Catalog

def represent {Byte : Type} (state : State Byte) : SemanticState Byte :=
  ⟨ByteRanges.heap state.storage, state.catalog⟩

inductive Request (Byte : Type) where
  | readRepresentation (range : Range)
  | writeRepresentation (address : Address) (contents : List (Option Byte))
  | copyRepresentation (source : Range) (target : Address)
  | allocate (bytes : Nat)
  | retire (address : Option Ptr)
  | advancePointer (pointer : ArrayPointers.Pointer) (distance : Int)
  | subtractPointers (left right : ArrayPointers.Pointer)
  | elementView (pointer : ArrayPointers.Pointer)
  deriving DecidableEq, Repr

inductive Response (Byte : Type) where
  | representation (contents : List (Option Byte))
  | updated
  | allocation (address : Option Ptr)
  | pointer (pointer : ArrayPointers.Pointer)
  | difference (value : Int)
  | element (range : Range)
  deriving DecidableEq, Repr

variable {Byte : Type}

/-- Independent transitions are built from heap, ownership and index
judgments, not from the executable step's returned value. -/
inductive Reduction (profile : ArrayPointers.DifferenceProfile) :
    SemanticState Byte → Request Byte → Response Byte → SemanticState Byte → Prop where
  | read (before : SemanticState Byte) (range : Range) (contents : List (Option Byte))
      (observed : ReadRange before.memory range contents) :
      Reduction profile before (.readRepresentation range) (.representation contents) before
  | write (before : SemanticState Byte) (address : Address) (contents : List (Option Byte))
      (after : Heap (Excl (Option Byte))) (written : WriteRange before.memory address contents after) :
      Reduction profile before (.writeRepresentation address contents) .updated ⟨after, before.catalog⟩
  | copy (before : SemanticState Byte) (source : Range) (target : Address)
      (after : Heap (Excl (Option Byte))) (copied : CopyRange before.memory source target after) :
      Reduction profile before (.copyRepresentation source target) .updated ⟨after, before.catalog⟩
  | allocate (before : SemanticState Byte) (bytes : Nat) (address : Option Ptr)
      (after : Heap (Excl (Option Byte))) (allocated : AllocStep bytes before.memory address after) :
      Reduction profile before (.allocate bytes) (.allocation address) ⟨after, before.catalog⟩
  | retire (before : SemanticState Byte) (address : Option Ptr) (after : Heap (Excl (Option Byte)))
      (owned : (act (L := Excl (Option Byte)) (.free address)).Safe before.memory)
      (retired : (act (L := Excl (Option Byte)) (.free address)).Step before.memory () after) :
      Reduction profile before (.retire address) .updated ⟨after, before.catalog⟩
  | advance (before : SemanticState Byte) (pointer result : ArrayPointers.Pointer) (distance : Int)
      (computed : ArrayPointers.Addition before.memory before.catalog pointer distance result) :
      Reduction profile before (.advancePointer pointer distance) (.pointer result) before
  | difference (before : SemanticState Byte) (left right : ArrayPointers.Pointer) (value : Int)
      (computed : ArrayPointers.Subtraction profile before.memory before.catalog left right value) :
      Reduction profile before (.subtractPointers left right) (.difference value) before
  | element (before : SemanticState Byte) (pointer : ArrayPointers.Pointer) (range : Range)
      (view : ArrayPointers.ElementRange before.memory before.catalog pointer range) :
      Reduction profile before (.elementView pointer) (.element range) before

def execute (profile : ArrayPointers.DifferenceProfile) (choice : ExecutableStorage.AllocationChoice)
    (state : State Byte) : Request Byte → Option (Response Byte × State Byte)
  | .readRepresentation range => do
      let contents ← readBytes state.storage range
      some (.representation contents, state)
  | .writeRepresentation address contents => do
      let storage ← writeBytes state.storage address contents
      some (.updated, { state with storage })
  | .copyRepresentation source target => do
      let storage ← copyBytes state.storage source target
      some (.updated, { state with storage })
  | .allocate bytes => do
      let (address, storage) ← ExecutableStorage.allocate state.storage bytes choice
      some (.allocation address, { state with storage })
  | .retire address => do
      let storage ← ExecutableStorage.free state.storage address
      some (.updated, { state with storage })
  | .advancePointer pointer distance => do
      let result ← ArrayPointers.add state.storage state.catalog pointer distance
      some (.pointer result, state)
  | .subtractPointers left right => do
      let value ← ArrayPointers.subtract profile state.storage state.catalog left right
      some (.difference value, state)
  | .elementView pointer => do
      let range ← ArrayPointers.elementRange state.storage state.catalog pointer
      some (.element range, state)

theorem execute_sound (profile : ArrayPointers.DifferenceProfile)
    (choice : ExecutableStorage.AllocationChoice) (before after : State Byte)
    (request : Request Byte) (response : Response Byte)
    (executed : execute profile choice before request = some (response, after)) :
    Reduction profile (represent before) request response (represent after) := by
  cases request with
  | readRepresentation range =>
      cases observed : readBytes before.storage range with
      | none => simp [execute, observed] at executed
      | some contents =>
          simp [execute, observed] at executed
          obtain ⟨rfl, rfl⟩ := executed
          exact .read _ range contents (readBytes_sound before.storage range contents observed)
  | writeRepresentation address contents =>
      cases written : writeBytes before.storage address contents with
      | none => simp [execute, written] at executed
      | some storage =>
          simp [execute, written] at executed
          obtain ⟨rfl, rfl⟩ := executed
          exact .write _ address contents _ (writeBytes_sound before.storage storage address contents written)
  | copyRepresentation source target =>
      cases copied : copyBytes before.storage source target with
      | none => simp [execute, copied] at executed
      | some storage =>
          simp [execute, copied] at executed
          obtain ⟨rfl, rfl⟩ := executed
          exact .copy _ source target _ (copyBytes_sound before.storage storage source target copied)
  | allocate bytes =>
      cases allocated : ExecutableStorage.allocate before.storage bytes choice with
      | none => simp [execute, allocated] at executed
      | some result =>
          rcases result with ⟨address, storage⟩
          simp [execute, allocated] at executed
          obtain ⟨rfl, rfl⟩ := executed
          exact .allocate _ bytes address _
            (ExecutableStorage.allocate_sound before.storage storage bytes choice address allocated)
  | retire address =>
      cases retired : ExecutableStorage.free before.storage address with
      | none => simp [execute, retired] at executed
      | some storage =>
          simp [execute, retired] at executed
          obtain ⟨rfl, rfl⟩ := executed
          have correct := ExecutableStorage.free_sound before.storage storage address retired
          exact .retire _ address _ correct.1 correct.2
  | advancePointer pointer distance =>
      cases computed : ArrayPointers.add before.storage before.catalog pointer distance with
      | none => simp [execute, computed] at executed
      | some result =>
          simp [execute, computed] at executed
          obtain ⟨rfl, rfl⟩ := executed
          exact .advance _ pointer result distance
            (ArrayPointers.add_sound before.storage before.catalog pointer distance result computed)
  | subtractPointers left right =>
      cases computed : ArrayPointers.subtract profile before.storage before.catalog left right with
      | none => simp [execute, computed] at executed
      | some value =>
          simp [execute, computed] at executed
          obtain ⟨rfl, rfl⟩ := executed
          exact .difference _ left right value
            (ArrayPointers.subtract_sound profile before.storage before.catalog left right value computed)
  | elementView pointer =>
      cases viewed : ArrayPointers.elementRange before.storage before.catalog pointer with
      | none => simp [execute, viewed] at executed
      | some range =>
          simp [execute, viewed] at executed
          obtain ⟨rfl, rfl⟩ := executed
          exact .element _ pointer range ((ArrayPointers.elementRange_iff _ _ _ _).mp viewed)

theorem execute_complete (profile : ArrayPointers.DifferenceProfile) (before : State Byte)
    (request : Request Byte) (response : Response Byte) (after : SemanticState Byte)
    (reduced : Reduction profile (represent before) request response after) :
    ∃ choice saved, execute profile choice before request = some (response, saved) ∧ represent saved = after := by
  cases reduced with
  | read range contents observed =>
      exact ⟨.failure, before, by simp [execute, readBytes_complete before.storage range contents observed], rfl⟩
  | write address contents after written =>
      obtain ⟨storage, computed, final⟩ := writeBytes_complete before.storage address contents after written
      exact ⟨.failure, { before with storage }, by simp [execute, computed], by simp only [represent, final]⟩
  | copy source target after copied =>
      obtain ⟨storage, computed, final⟩ := copyBytes_complete before.storage source target after copied
      exact ⟨.failure, { before with storage }, by simp [execute, computed], by simp only [represent, final]⟩
  | allocate bytes address after allocated =>
      obtain ⟨choice, storage, computed, final⟩ :=
        ExecutableStorage.allocate_complete before.storage bytes address after allocated
      exact ⟨choice, { before with storage }, by simp [execute, computed], by simp only [represent, final]⟩
  | retire address after owned retired =>
      obtain ⟨storage, computed, final⟩ := ExecutableStorage.free_complete before.storage address after owned retired
      exact ⟨.failure, { before with storage }, by simp [execute, computed], by simp only [represent, final]⟩
  | advance pointer result distance computed =>
      exact ⟨.failure, before, by simp [execute,
        ArrayPointers.add_complete before.storage before.catalog pointer distance result computed], rfl⟩
  | difference left right value computed =>
      exact ⟨.failure, before, by simp [execute,
        ArrayPointers.subtract_complete profile before.storage before.catalog left right value computed], rfl⟩
  | element pointer range viewed =>
      exact ⟨.failure, before, by simp [execute,
        (ArrayPointers.elementRange_iff before.storage before.catalog pointer range).mpr viewed], rfl⟩

theorem execute_iff (profile : ArrayPointers.DifferenceProfile) (before : State Byte)
    (request : Request Byte) (response : Response Byte) (after : SemanticState Byte) :
    (∃ choice saved, execute profile choice before request = some (response, saved) ∧ represent saved = after) ↔
      Reduction profile (represent before) request response after := by
  constructor
  · rintro ⟨choice, saved, computed, rfl⟩
    exact execute_sound profile choice before saved request response computed
  · exact execute_complete profile before request response after

structure Input (Byte : Type) where
  state : State Byte
  request : Request Byte
  choice : ExecutableStorage.AllocationChoice
  deriving DecidableEq, Repr

structure Receipt (Byte : Type) where
  input : Input Byte
  response : Response Byte
  after : State Byte
  deriving DecidableEq, Repr

inductive Configuration (Byte : Type) where
  | pending (input : Input Byte)
  | completed (response : Response Byte) (saved : State Byte)
  | refused (saved : Input Byte)
  deriving DecidableEq, Repr

inductive Verdict (Byte : Type) where
  | returned (response : Response Byte) (saved : State Byte)
  | refused (saved : Input Byte)
  deriving DecidableEq, Repr

def machine (profile : ArrayPointers.DifferenceProfile) :
    Machine (Configuration Byte) (Receipt Byte) (Verdict Byte) Empty where
  step
    | .pending input =>
        match execute profile input.choice input.state input.request with
        | some (response, saved) => some (.publish [⟨input, response, saved⟩] (.completed response saved))
        | none => some (.finish (.refused input))
    | .completed response saved => some (.finish (.returned response saved))
    | .refused input => some (.finish (.refused input))

/-- Count attempted kernel requests, including a refused request. -/
def requestCharge : Configuration Byte → Nat
  | .pending _ => 1
  | _ => 0

def Request.bytesRead : Request Byte → Nat
  | .readRepresentation range | .copyRepresentation range _ => range.extent
  | _ => 0

def Request.bytesWritten : Request Byte → Nat
  | .writeRepresentation _ contents => contents.length
  | .copyRepresentation range _ => range.extent
  | _ => 0

def byteReadCharge (profile : ArrayPointers.DifferenceProfile) : Configuration Byte → Nat
  | .pending input =>
      if (execute profile input.choice input.state input.request).isSome then input.request.bytesRead else 0
  | _ => 0

def byteWriteCharge (profile : ArrayPointers.DifferenceProfile) : Configuration Byte → Nat
  | .pending input =>
      if (execute profile input.choice input.state input.request).isSome then input.request.bytesWritten else 0
  | _ => 0

theorem accepted_residual (profile : ArrayPointers.DifferenceProfile) (input : Input Byte)
    (response : Response Byte) (saved : State Byte)
    (computed : execute profile input.choice input.state input.request = some (response, saved)) :
    (machine profile).run 1 (.pending input) =
      ([⟨input, response, saved⟩], .exhausted (.completed response saved)) := by
  simp [Machine.run, machine, computed]

theorem completed_no_receipts (profile : ArrayPointers.DifferenceProfile) (fuel : Nat)
    (response : Response Byte) (saved : State Byte) :
    ((machine profile).run fuel (.completed response saved)).1 = [] := by
  cases fuel <;> rfl

theorem accepted_receipt_valid (profile : ArrayPointers.DifferenceProfile) (input : Input Byte)
    (response : Response Byte) (saved : State Byte)
    (computed : execute profile input.choice input.state input.request = some (response, saved)) :
    Reduction profile (represent input.state) input.request response (represent saved) :=
  execute_sound profile input.choice input.state saved input.request response computed

theorem resume_after_prefix (profile : ArrayPointers.DifferenceProfile) (first second : Nat)
    (initial saved : Configuration Byte) (events : List (Receipt Byte))
    (paused : (machine profile).run first initial = (events, .exhausted saved)) :
    (machine profile).run (first + second) initial =
      (events ++ ((machine profile).run second saved).1, ((machine profile).run second saved).2) :=
  (machine profile).established_and_pending first second initial saved events paused

def productive (profile : ArrayPointers.DifferenceProfile) : (machine profile (Byte := Byte)).Productive where
  rank _ := 0
  moves configuration := by
    cases configuration with
    | pending input => cases computed : execute profile input.choice input.state input.request <;> simp [machine, computed]
    | completed response saved => simp [machine]
    | refused input => simp [machine]
  silent_decreases := by
    intro configuration next silent
    cases configuration <;> simp [machine] at silent
    split at silent <;> simp at silent

end Mettapedia.Languages.C11.ObjectStep
