import Mettapedia.Languages.C11.IntegerObjectConstruction

/-!
# Finite declaration reservations over constructed owned memory

A sequence constructs every requested integer object's storage, type
records, array descriptor and root view. It keeps declaration order and
all intermediate ownership endpoints. Source non-VLA block entry can
reserve the sequence with indeterminate contents while keeping the returned
views separate from identifier visibility and initializer execution.

The allocator choices and layouts are explicit and checked at every object.
The independent rule composes heap creation judgments rather than trusting
the returned list of lvalues. General correspondence covers arbitrary finite
sequences, not a bounded number of declarations.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.C11.IntegerObjectSequences

open IntegerObjectConstruction ObjectAccessMemory
open Mettapedia.Machines.CMemory
open Mettapedia.GSLT.SeparationAlgebra
open scoped Mettapedia.GSLT.SeparationAlgebra

structure Request where
  declaration : Declaration
  element : ObjectLayout.Layout
  identity : BlockId
  contents : InitialContents

structure Prepared (model : IntegerMemoryModel.Model) where
  memory : ObjectAccessMemory.State model.characters
  arrays : ArrayPointers.Catalog
  locations : List Lvalue
  deriving DecidableEq, Repr

def construct (model : IntegerMemoryModel.Model) (memory : ObjectAccessMemory.State model.characters)
    (arrays : ArrayPointers.Catalog) : List Request → Option (Prepared model)
  | [] => some ⟨memory, arrays, []⟩
  | request :: rest => do
      let object ← IntegerObjectConstruction.construct model memory arrays request.declaration
        request.element request.identity request.contents
      let following ← construct model object.memory object.arrays rest
      some ⟨following.memory, following.arrays, object.location :: following.locations⟩

inductive CreationSequence (model : IntegerMemoryModel.Model) :
    ObjectAccessMemory.SemanticState model.characters → ArrayPointers.Catalog → List Request →
      ObjectAccessMemory.SemanticState model.characters → ArrayPointers.Catalog → List Lvalue → Prop where
  | empty (memory : ObjectAccessMemory.SemanticState model.characters) (arrays : ArrayPointers.Catalog) :
      CreationSequence model memory arrays [] memory arrays []
  | cons (before middle after : ObjectAccessMemory.SemanticState model.characters)
      (arrays middleArrays afterArrays : ArrayPointers.Catalog) (request : Request) (rest : List Request)
      (location : Lvalue) (locations : List Lvalue)
      (created : Creation model before arrays request.declaration request.element request.identity request.contents
        middle middleArrays location)
      (following : CreationSequence model middle middleArrays rest after afterArrays locations) :
      CreationSequence model before arrays (request :: rest) after afterArrays (location :: locations)

theorem construct_sound (model : IntegerMemoryModel.Model) (memory : ObjectAccessMemory.State model.characters)
    (arrays : ArrayPointers.Catalog) (requests : List Request) (result : Prepared model)
    (executed : construct model memory arrays requests = some result) :
    CreationSequence model (ObjectAccessMemory.represent memory) arrays requests
      (ObjectAccessMemory.represent result.memory) result.arrays result.locations := by
  induction requests generalizing memory arrays result with
  | nil => simp only [construct, Option.some.injEq] at executed; subst result; exact .empty _ _
  | cons request rest ih =>
      simp only [construct, bind, Option.bind_eq_some_iff, Option.some.injEq] at executed
      obtain ⟨object, created, following, remainder, rfl⟩ := executed
      exact .cons _ _ _ _ _ _ _ _ _ _
        (IntegerObjectConstruction.construct_sound _ _ _ _ _ _ _ _ created) (ih _ _ _ remainder)

theorem construct_complete (model : IntegerMemoryModel.Model) (memory : ObjectAccessMemory.State model.characters)
    (arrays : ArrayPointers.Catalog) (requests : List Request) (after : ObjectAccessMemory.SemanticState model.characters)
    (nextArrays : ArrayPointers.Catalog) (locations : List Lvalue)
    (creation : CreationSequence model (ObjectAccessMemory.represent memory) arrays requests after nextArrays locations) :
    ∃ result, construct model memory arrays requests = some result ∧
      ObjectAccessMemory.represent result.memory = after ∧ result.arrays = nextArrays ∧ result.locations = locations := by
  generalize present : ObjectAccessMemory.represent memory = before at creation
  induction creation generalizing memory with
  | empty before arrays => exact ⟨⟨memory, arrays, []⟩, rfl, present, rfl, rfl⟩
  | cons before middle after arrays middleArrays afterArrays request rest location locations created following ih =>
      rw [← present] at created
      obtain ⟨object, objectCreated, middleEqual, arraysEqual, locationEqual⟩ :=
        IntegerObjectConstruction.construct_complete _ _ _ _ _ _ _ _ _ _ created
      obtain ⟨following, computed, finalMemory, finalArrays, finalLocations⟩ := ih object.memory middleEqual
      refine ⟨⟨following.memory, following.arrays, object.location :: following.locations⟩, ?_,
        finalMemory, finalArrays, ?_⟩
      · simp only [construct, objectCreated, bind, Option.bind_some, arraysEqual, computed]
      · rw [locationEqual, finalLocations]

theorem CreationSequence.locations (model : IntegerMemoryModel.Model)
    (before after : ObjectAccessMemory.SemanticState model.characters) (arrays nextArrays : ArrayPointers.Catalog)
    (requests : List Request) (locations : List Lvalue)
    (creation : CreationSequence model before arrays requests after nextArrays locations) :
    locations = requests.map (fun request => root request.declaration request.element request.identity) := by
  induction creation with
  | empty => rfl
  | cons before middle after arrays middleArrays afterArrays request rest location locations created following ih =>
      rw [List.map_cons, created.2.2.2.2.2.2, ih]

theorem CreationSequence.other (model : IntegerMemoryModel.Model)
    (before after : ObjectAccessMemory.SemanticState model.characters) (arrays nextArrays : ArrayPointers.Catalog)
    (requests : List Request) (locations : List Lvalue)
    (creation : CreationSequence model before arrays requests after nextArrays locations)
    (identity : BlockId) (outside : identity ∉ requests.map Request.identity) : after.memory identity = before.memory identity := by
  induction creation with
  | empty => rfl
  | cons before middle after arrays middleArrays afterArrays request rest location locations created following ih =>
      have different : identity ≠ request.identity := by
        intro same
        exact outside (List.mem_cons.mpr (.inl same))
      have notFollowing : identity ∉ rest.map Request.identity := fun member => outside (List.mem_cons_of_mem _ member)
      exact (ih notFollowing).trans (created.2.2.2.1.2.2.2 identity different)

theorem CreationSequence.formed (model : IntegerMemoryModel.Model)
    (before after : ObjectAccessMemory.SemanticState model.characters) (arrays nextArrays : ArrayPointers.Catalog)
    (requests : List Request) (locations : List Lvalue)
    (creation : CreationSequence model before arrays requests after nextArrays locations)
    (request : Request) (member : request ∈ requests) : Formation model request.declaration request.element := by
  induction creation with
  | empty => cases member
  | cons before middle after arrays middleArrays afterArrays first rest location locations created following ih =>
      rcases List.mem_cons.mp member with same | followingMember
      · subst request; exact created.1
      · exact ih followingMember

end Mettapedia.Languages.C11.IntegerObjectSequences
