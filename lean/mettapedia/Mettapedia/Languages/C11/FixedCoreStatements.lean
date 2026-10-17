import Mettapedia.Languages.C11.FixedCore

/-!
# The fixed C core: statements, lifetimes, calls, allocation and interaction

Core statements sequence their effects explicitly. A block reserves each
declared object when its declaration is reached at block entry and retires every
owned lifetime on every exit: falling through, `break`, `continue` and `return`.
A call evaluates its arguments, which are pure, and starts an activation whose
parameters are new objects initialized by assignment conversion; the caller
waits for the returned value. An external call suspends the machine with a
request and resumes when a reply is delivered. `allocate` and `release` create
and retire dynamic objects; releasing anything else is undefined behavior.

Two choices are left open by C11 and stay open here: the identity of every new
object, and whether an allocation succeeds. The executable step receives them as
an explicit `Choice`; the independent judgment allows every admissible choice.
Object layouts are the selected ABI's, supplied as a parameter.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.C11.FixedCore

open IntegerMemoryModel ObjectAccessMemory
open Mettapedia.Machines.CMemory (BlockId)

/-! ## Syntax -/

/-- A declaration at the head of a block. -/
inductive Declaration (model : Model) where
  | object (declaration : IntegerObjectConstruction.Declaration) (initializer : Option (Expression model))
  | pointer (name : String) (initializer : Option (Expression model))

inductive Statement (model : Model) where
  | skip
  | assign (place : Place model) (value : Expression model)
  | setPointer (name : String) (value : Expression model)
  | call (result : Option String) (function : String) (arguments : List (Expression model))
  | external (result : Option String) (service : String) (arguments : List (Expression model))
  | allocate (name : String) (type : IntegerType IntegerExtension) (count : Expression model)
  | release (pointer : Expression model)
  | sequence (first second : Statement model)
  | block (declarations : List (Declaration model)) (body : Statement model)
  | conditional (condition : Expression model) (yes no : Statement model)
  | whileLoop (condition : Expression model) (body : Statement model)
  | breakLoop
  | continueLoop
  | returnValue (value : Option (Expression model))

inductive Parameter where
  | integer (name : String) (type : IntegerType IntegerExtension)
  | pointer (name : String)
  deriving DecidableEq, Repr

def Parameter.name : Parameter → String
  | .integer name _ => name
  | .pointer name => name

/-- Whether an argument value has the parameter's kind. -/
def Parameter.accepts {model : Model} : Parameter → Value model → Bool
  | .integer _ _, .integer _ => true
  | .integer _ _, _ => false
  | .pointer _, _ => true

def Declaration.name {model : Model} : Declaration model → String
  | .object declaration _ => declaration.name
  | .pointer name _ => name

structure Function (model : Model) where
  parameters : List Parameter
  body : Statement model

abbrev Program (model : Model) := List (String × Function model)

/-! ## Configurations -/

inductive Flow where
  | normal
  | broken
  | continued
  deriving DecidableEq, Repr

inductive Control (model : Model) where
  | execute (statement : Statement model)
  | declaring (declarations : List (Declaration model)) (body : Statement model)
  | binding (pending : List (Parameter × Value model)) (body : Statement model)
  | flow (flow : Flow)
  | returning (value : Option (Value model))
  | awaiting (result : Option String)

inductive Continuation (model : Model) where
  | stop
  | sequence (next : Statement model) (outer : Continuation model)
  | loop (condition : Expression model) (body : Statement model) (outer : Continuation model)
  | scope (outer : Continuation model)

structure Activation (model : Model) where
  scopes : List (Scope model)
  control : Control model
  continuation : Continuation model

inductive Status (model : Model) where
  | running
  | waiting (service : String) (arguments : List (Value model))
  | finished (value : Option (Value model))
  | faulted (fault : Fault model)

/-- A configuration over a memory carrier. The executable machine uses the
finite byte storage; the independent judgment uses its heap representation. -/
structure Configuration (model : Model) (Memory : Type) where
  memory : Memory
  arrays : ArrayPointers.Catalog
  heap : List BlockId
  stack : List (Activation model)
  status : Status model

abbrev Executable (model : Model) := Configuration model (State model.characters)
abbrev Semantic (model : Model) := Configuration model (SemanticState model.characters)

def Configuration.represent {model : Model} (configuration : Executable model) : Semantic model :=
  { configuration with memory := ObjectAccessMemory.represent configuration.memory }

/-- The open choices of one step: the identity of a new object and whether a
dynamic allocation succeeds. -/
structure Choice where
  identity : BlockId
  allocationSucceeds : Bool := true
  deriving DecidableEq, Repr

variable {model : Model}

/-! ## Scope operations -/

def Scope.declares (scope : Scope model) (name : String) : Bool :=
  (scope.objects.bindings.lookup name).isSome || (scope.pointers.lookup name).isSome

/-- Bind an object in the innermost scope. -/
def Scope.bindObject (scope : Scope model) (name : String) (location : Lvalue) (identity : BlockId) :
    Scope model :=
  { scope with objects := ⟨(name, location) :: scope.objects.bindings, identity :: scope.objects.allocations⟩ }

def Scope.bindPointer (scope : Scope model) (name : String) (value : Option (Value model)) : Scope model :=
  { scope with pointers := (name, value) :: scope.pointers }

/-- Update the innermost scope declaring a pointer variable. -/
def setPointerIn (name : String) (value : Value model) : List (Scope model) → Option (List (Scope model))
  | [] => none
  | scope :: rest =>
      match scope.objects.bindings.lookup name with
      | some _ => none
      | none =>
          match scope.pointers.lookup name with
          | some _ =>
              some ({ scope with pointers := (name, some value) :: scope.pointers.filter (·.1 ≠ name) } :: rest)
          | none => (setPointerIn name value rest).map (scope :: ·)

/-- Pointer variables hold pointers. -/
def pointerValue : Value model → Bool
  | .address _ | .null => true
  | .integer _ => false

/-- Every argument value, or the first fault. -/
def argumentValues : List (Result model) → Except (Fault model) (List (Value model))
  | [] => .ok []
  | .fault fault :: _ => .error fault
  | .value value :: rest => (argumentValues rest).map (value :: ·)

/-- Pair parameters with argument values, checking kinds. -/
def bindParameters : List Parameter → List (Value model) → Option (List (Parameter × Value model))
  | [], [] => some []
  | .integer name type :: parameters, .integer scalar :: values =>
      (bindParameters parameters values).map ((.integer name type, .integer scalar) :: ·)
  | .pointer name :: parameters, value :: values =>
      if pointerValue value then (bindParameters parameters values).map ((.pointer name, value) :: ·) else none
  | _, _ => none

def scalarDeclaration (name : String) (type : IntegerType IntegerExtension) : IntegerObjectConstruction.Declaration :=
  ⟨name, type, .scalar⟩

/-- The outcome of an effect on the memory: the new memory or a fault. -/
inductive Effect (model : Model) (Memory : Type) where
  | done (memory : Memory)
  | fault (fault : Fault model)

def Effect.represent : Effect model (State model.characters) → Effect model (SemanticState model.characters)
  | .done memory => .done (ObjectAccessMemory.represent memory)
  | .fault reason => .fault reason

/-! ## Memory effects and their independent outcomes -/

section Effects

variable (model : Model) (policy : SignedConversionPolicy)

/-- Assignment conversion into a located element, then a typed store. -/
def storeElement (memory : State model.characters) (arrays : ArrayPointers.Catalog) (target : Address)
    (value : IntegerScalar.Value model.parameters) : Effect model (State model.characters) :=
  match ArrayPointers.elementRange memory.storage arrays target.pointer with
  | none => .fault (.access target)
  | some range =>
      match IntegerAssignment.assign model policy memory (elementLvalue target range) value with
      | none => .fault (.access target)
      | some (.stored _, saved) => .done saved
      | some (.conversionSignal identifier, _) => .fault (.signal identifier)

inductive StoresElement (memory : SemanticState model.characters) (arrays : ArrayPointers.Catalog)
    (target : Address) (value : IntegerScalar.Value model.parameters) :
    Effect model (SemanticState model.characters) → Prop where
  | missing (absent : ¬∃ range, ArrayPointers.ElementRange memory.memory arrays target.pointer range) :
      StoresElement memory arrays target value (.fault (.access target))
  | refused (range : ByteRanges.Range)
      (inside : ArrayPointers.ElementRange memory.memory arrays target.pointer range)
      (undefined : ¬∃ observed after, IntegerAssignment.Assigning model policy memory
        (elementLvalue target range) value observed after) :
      StoresElement memory arrays target value (.fault (.access target))
  | stored (range : ByteRanges.Range) (converted : IntegerScalar.Value model.parameters)
      (after : SemanticState model.characters)
      (inside : ArrayPointers.ElementRange memory.memory arrays target.pointer range)
      (assigned : IntegerAssignment.Assigning model policy memory (elementLvalue target range) value
        (.stored converted) after) :
      StoresElement memory arrays target value (.done after)
  | signal (range : ByteRanges.Range) (identifier : Nat) (after : SemanticState model.characters)
      (inside : ArrayPointers.ElementRange memory.memory arrays target.pointer range)
      (assigned : IntegerAssignment.Assigning model policy memory (elementLvalue target range) value
        (.conversionSignal identifier) after) :
      StoresElement memory arrays target value (.fault (.signal identifier))

theorem storeElement_sound (memory : State model.characters) (arrays : ArrayPointers.Catalog) (target : Address)
    (value : IntegerScalar.Value model.parameters) :
    StoresElement model policy (ObjectAccessMemory.represent memory) arrays target value
      (storeElement model policy memory arrays target value).represent := by
  cases ranged : ArrayPointers.elementRange memory.storage arrays target.pointer with
  | none =>
      simp only [storeElement, ranged, Effect.represent]
      refine .missing ?_
      rintro ⟨range, inside⟩
      rw [(ArrayPointers.elementRange_iff _ _ _ _).mpr inside] at ranged
      cases ranged
  | some range =>
      have inside : ArrayPointers.ElementRange (ObjectAccessMemory.represent memory).memory arrays
          target.pointer range := (ArrayPointers.elementRange_iff _ _ _ _).mp ranged
      cases assigned : IntegerAssignment.assign model policy memory (elementLvalue target range) value with
      | none =>
          simp only [storeElement, ranged, assigned, Effect.represent]
          refine .refused range inside ?_
          rintro ⟨observed, after, assigning⟩
          obtain ⟨saved, computed, _⟩ := IntegerAssignment.assign_complete _ _ _ _ _ _ _ assigning
          rw [computed] at assigned
          cases assigned
      | some pair =>
          obtain ⟨observed, saved⟩ := pair
          have assigning := IntegerAssignment.assign_sound _ _ _ _ _ _ _ assigned
          cases observed with
          | stored converted =>
              simp only [storeElement, ranged, assigned, Effect.represent]
              exact .stored range converted _ inside assigning
          | conversionSignal identifier =>
              simp only [storeElement, ranged, assigned, Effect.represent]
              exact .signal range identifier _ inside assigning

theorem storeElement_complete (memory : State model.characters) (arrays : ArrayPointers.Catalog) (target : Address)
    (value : IntegerScalar.Value model.parameters) (effect : Effect model (SemanticState model.characters))
    (storing : StoresElement model policy (ObjectAccessMemory.represent memory) arrays target value effect) :
    (storeElement model policy memory arrays target value).represent = effect := by
  cases storing with
  | missing absent =>
      cases ranged : ArrayPointers.elementRange memory.storage arrays target.pointer with
      | none => simp only [storeElement, ranged, Effect.represent]
      | some range => exact absurd ⟨range, (ArrayPointers.elementRange_iff _ _ _ _).mp ranged⟩ absent
  | refused range inside undefined =>
      have ranged := (ArrayPointers.elementRange_iff memory.storage arrays target.pointer range).mpr inside
      cases assigned : IntegerAssignment.assign model policy memory (elementLvalue target range) value with
      | none => simp only [storeElement, ranged, assigned, Effect.represent]
      | some pair =>
          obtain ⟨observed, saved⟩ := pair
          exact absurd ⟨observed, _, IntegerAssignment.assign_sound _ _ _ _ _ _ _ assigned⟩ undefined
  | stored range converted after inside assigning =>
      have ranged := (ArrayPointers.elementRange_iff memory.storage arrays target.pointer range).mpr inside
      obtain ⟨saved, computed, represented⟩ := IntegerAssignment.assign_complete _ _ _ _ _ _ _ assigning
      simp only [storeElement, ranged, computed, Effect.represent, represented]
  | signal range identifier after inside assigning =>
      have ranged := (ArrayPointers.elementRange_iff memory.storage arrays target.pointer range).mpr inside
      obtain ⟨saved, computed, _⟩ := IntegerAssignment.assign_complete _ _ _ _ _ _ _ assigning
      simp only [storeElement, ranged, computed, Effect.represent]

/-- Reserve a new object in the innermost scope and bind its name there. Its
contents are indeterminate until an initializer or assignment stores a value. -/
def declareObject (memory : State model.characters) (arrays : ArrayPointers.Catalog)
    (scopes : List (Scope model)) (declaration : IntegerObjectConstruction.Declaration)
    (element : ObjectLayout.Layout) (identity : BlockId) :
    Option (State model.characters × ArrayPointers.Catalog × List (Scope model)) :=
  match scopes with
  | [] => none
  | head :: rest =>
      (IntegerObjectConstruction.construct model memory arrays declaration element identity .indeterminate).map
        fun result => (result.memory, result.arrays, head.bindObject declaration.name result.location identity :: rest)

inductive DeclaresObject (memory : SemanticState model.characters) (arrays : ArrayPointers.Catalog)
    (scopes : List (Scope model)) (declaration : IntegerObjectConstruction.Declaration)
    (element : ObjectLayout.Layout) (identity : BlockId) :
    SemanticState model.characters → ArrayPointers.Catalog → List (Scope model) → Prop where
  | declared (head : Scope model) (rest : List (Scope model)) (after : SemanticState model.characters)
      (nextArrays : ArrayPointers.Catalog) (location : Lvalue) (split : scopes = head :: rest)
      (creation : IntegerObjectConstruction.Creation model memory arrays declaration element identity
        .indeterminate after nextArrays location) :
      DeclaresObject memory arrays scopes declaration element identity after nextArrays
        (head.bindObject declaration.name location identity :: rest)

theorem declareObject_sound (memory : State model.characters) (arrays : ArrayPointers.Catalog)
    (scopes : List (Scope model)) (declaration : IntegerObjectConstruction.Declaration)
    (element : ObjectLayout.Layout) (identity : BlockId)
    (after : State model.characters) (nextArrays : ArrayPointers.Catalog) (nextScopes : List (Scope model))
    (executed : declareObject model memory arrays scopes declaration element identity =
      some (after, nextArrays, nextScopes)) :
    DeclaresObject model (ObjectAccessMemory.represent memory) arrays scopes declaration element identity
      (ObjectAccessMemory.represent after) nextArrays nextScopes := by
  cases scopes with
  | nil => simp [declareObject] at executed
  | cons head rest =>
      simp only [declareObject, Option.map_eq_some_iff, Prod.mk.injEq] at executed
      obtain ⟨result, constructed, rfl, rfl, rfl⟩ := executed
      exact .declared head rest _ _ _ rfl
        (IntegerObjectConstruction.construct_sound _ _ _ _ _ _ _ _ constructed)

theorem declareObject_complete (memory : State model.characters) (arrays : ArrayPointers.Catalog)
    (scopes : List (Scope model)) (declaration : IntegerObjectConstruction.Declaration)
    (element : ObjectLayout.Layout) (identity : BlockId)
    (after : SemanticState model.characters) (nextArrays : ArrayPointers.Catalog) (nextScopes : List (Scope model))
    (declared : DeclaresObject model (ObjectAccessMemory.represent memory) arrays scopes declaration element identity
      after nextArrays nextScopes) :
    ∃ saved, declareObject model memory arrays scopes declaration element identity =
      some (saved, nextArrays, nextScopes) ∧ ObjectAccessMemory.represent saved = after := by
  cases declared with
  | declared head rest after nextArrays location split creation =>
      subst split
      obtain ⟨result, constructed, memoryEq, arraysEq, locationEq⟩ :=
        IntegerObjectConstruction.construct_complete _ _ _ _ _ _ _ _ _ _ creation
      refine ⟨result.memory, ?_, memoryEq⟩
      simp [declareObject, constructed, arraysEq, locationEq]

/-- Retire every lifetime owned by the innermost scope and drop the scope. -/
def leaveScope (memory : State model.characters) (scopes : List (Scope model)) :
    Option (State model.characters × List (Scope model)) :=
  match scopes with
  | [] => none
  | head :: rest =>
      (AutomaticObjectScopes.releaseStorage memory.storage head.objects.allocations).map
        fun storage => (⟨storage, memory.catalog⟩, rest)

inductive LeavesScope (memory : SemanticState model.characters) (scopes : List (Scope model)) :
    SemanticState model.characters → List (Scope model) → Prop where
  | left (head : Scope model) (rest : List (Scope model)) (after : Mettapedia.Machines.CMemory.Heap
        (Mettapedia.GSLT.SeparationAlgebra.Excl (Option (ByteStorageData.Byte model.characters))))
      (split : scopes = head :: rest)
      (release : AutomaticObjectScopes.Release memory.memory head.objects.allocations after) :
      LeavesScope memory scopes ⟨after, memory.catalog⟩ rest

theorem leaveScope_sound (memory : State model.characters) (scopes : List (Scope model))
    (after : State model.characters) (rest : List (Scope model))
    (executed : leaveScope model memory scopes = some (after, rest)) :
    LeavesScope model (ObjectAccessMemory.represent memory) scopes (ObjectAccessMemory.represent after) rest := by
  cases scopes with
  | nil => simp [leaveScope] at executed
  | cons head tail =>
      simp only [leaveScope, Option.map_eq_some_iff, Prod.mk.injEq] at executed
      obtain ⟨storage, released, rfl, rfl⟩ := executed
      exact .left head tail _ rfl (AutomaticObjectScopes.releaseStorage_sound _ _ _ released)

theorem leaveScope_complete (memory : State model.characters) (scopes : List (Scope model))
    (after : SemanticState model.characters) (rest : List (Scope model))
    (left : LeavesScope model (ObjectAccessMemory.represent memory) scopes after rest) :
    ∃ saved, leaveScope model memory scopes = some (saved, rest) ∧ ObjectAccessMemory.represent saved = after := by
  cases left with
  | left head rest after split release =>
      subst split
      obtain ⟨storage, released, heap⟩ := AutomaticObjectScopes.releaseStorage_complete _ _ _ release
      exact ⟨⟨storage, memory.catalog⟩, by simp [leaveScope, released], by
        simp [ObjectAccessMemory.represent, heap]⟩

/-- Deliver a returned or replied value to the name the caller is waiting with. -/
def deliver (memory : State model.characters) (arrays : ArrayPointers.Catalog) (scopes : List (Scope model))
    (result : Option String) (value : Option (Value model)) :
    Effect model (State model.characters × List (Scope model)) :=
  match result, value with
  | none, _ => .done (memory, scopes)
  | some _, none => .fault .missingReturn
  | some name, some delivered =>
      match resolve scopes name with
      | some (.object location) =>
          match rootAddress location, delivered with
          | some target, .integer scalar =>
              match storeElement model policy memory arrays target scalar with
              | .done saved => .done (saved, scopes)
              | .fault reason => .fault reason
          | _, _ => .fault .constraint
      | some (.pointer _) =>
          if pointerValue delivered then
            match setPointerIn name delivered scopes with
            | some updated => .done (memory, updated)
            | none => .fault .constraint
          else .fault .constraint
      | none => .fault .constraint

end Effects

/-! ## The executable step -/

section Step

variable (model : Model) (policy : SignedConversionPolicy) (abi : IntegerType IntegerExtension → ObjectLayout.Layout)
  (program : Program model)

/-- Continue with a new top activation. -/
def Configuration.continueWith (configuration : Executable model) (top : Activation model)
    (callers : List (Activation model)) : Option (Executable model) :=
  some { configuration with stack := top :: callers }

def Configuration.fail (configuration : Executable model) (reason : Fault model) : Option (Executable model) :=
  some { configuration with status := .faulted reason }

/-- One step of the top activation of a running configuration. `none` means the
configuration is malformed or the choice is not admissible. -/
def advance (choice : Choice) (configuration : Executable model) (top : Activation model)
    (callers : List (Activation model)) : Option (Executable model) :=
  let memory := configuration.memory
  let arrays := configuration.arrays
  let scopes := top.scopes
  let evaluateHere := evaluate model policy memory arrays scopes
  match top.control with
  | .execute statement =>
      match statement with
      | .skip => configuration.continueWith model { top with control := .flow .normal } callers
      | .assign place value =>
          match locate model policy memory arrays scopes place, evaluateHere value with
          | .error reason, _ => configuration.fail model reason
          | .ok _, .fault reason => configuration.fail model reason
          | .ok target, .value (.integer scalar) =>
              match storeElement model policy memory arrays target scalar with
              | .done saved => some { configuration with
                  memory := saved,
                  stack := { top with control := .flow .normal } :: callers }
              | .fault reason => configuration.fail model reason
          | .ok _, .value _ => configuration.fail model .constraint
      | .setPointer name value =>
          match evaluateHere value with
          | .fault reason => configuration.fail model reason
          | .value delivered =>
              if pointerValue delivered then
                match setPointerIn name delivered scopes with
                | some updated => configuration.continueWith model
                    { top with scopes := updated, control := .flow .normal } callers
                | none => configuration.fail model .constraint
              else configuration.fail model .constraint
      | .call result function arguments =>
          match argumentValues (arguments.map evaluateHere) with
          | .error reason => configuration.fail model reason
          | .ok values =>
              match program.lookup function with
              | none => configuration.fail model .constraint
              | some definition =>
                  match bindParameters definition.parameters values with
                  | none => configuration.fail model .constraint
                  | some pending => some { configuration with stack :=
                      ⟨[{}], .binding pending definition.body, .scope .stop⟩ ::
                        { top with control := .awaiting result } :: callers }
      | .external result service arguments =>
          match argumentValues (arguments.map evaluateHere) with
          | .error reason => configuration.fail model reason
          | .ok values => some { configuration with
              status := .waiting service values,
              stack := { top with control := .awaiting result } :: callers }
      | .allocate name type count =>
          match evaluateHere count with
          | .fault reason => configuration.fail model reason
          | .value (.integer amount) =>
              if admitted : 0 < amount.integer.value.toNat ∧ choice.allocationSucceeds = true then
                match IntegerObjectConstruction.construct model memory arrays
                    ⟨name, type, .array amount.integer.value.toNat admitted.1⟩ (abi type) choice.identity
                    .indeterminate with
                | none => none
                | some created =>
                    match setPointerIn name (.address ⟨type, ⟨choice.identity, 0⟩⟩) scopes with
                    | some updated => some { configuration with
                        memory := created.memory,
                        arrays := created.arrays, heap := choice.identity :: configuration.heap,
                        stack := { top with scopes := updated, control := .flow .normal } :: callers }
                    | none => configuration.fail model .constraint
              else
                match setPointerIn name .null scopes with
                | some updated => configuration.continueWith model
                    { top with scopes := updated, control := .flow .normal } callers
                | none => configuration.fail model .constraint
          | .value _ => configuration.fail model .constraint
      | .release pointer =>
          match evaluateHere pointer with
          | .fault reason => configuration.fail model reason
          | .value .null => configuration.continueWith model { top with control := .flow .normal } callers
          | .value (.address target) =>
              if target.pointer.index = 0 ∧ target.pointer.object ∈ configuration.heap then
                match AutomaticObjectScopes.retireStorage memory.storage target.pointer.object with
                | some storage => some { configuration with
                    memory := ⟨storage, memory.catalog⟩,
                    heap := configuration.heap.erase target.pointer.object,
                    stack := { top with control := .flow .normal } :: callers }
                | none => configuration.fail model .invalidRelease
              else configuration.fail model .invalidRelease
          | .value (.integer _) => configuration.fail model .constraint
      | .sequence first second => configuration.continueWith model
          { top with control := .execute first, continuation := .sequence second top.continuation } callers
      | .block declarations body => configuration.continueWith model
          { top with
            scopes := {} :: scopes, control := .declaring declarations body,
            continuation := .scope top.continuation } callers
      | .conditional condition yes no =>
          match evaluateHere condition with
          | .fault reason => configuration.fail model reason
          | .value (.integer test) => configuration.continueWith model
              { top with control := .execute (if IntegerScalar.truth test then yes else no) } callers
          | .value _ => configuration.fail model .constraint
      | .whileLoop condition body =>
          match evaluateHere condition with
          | .fault reason => configuration.fail model reason
          | .value (.integer test) =>
              if IntegerScalar.truth test then configuration.continueWith model
                { top with
                  control := .execute body,
                  continuation := .loop condition body top.continuation } callers
              else configuration.continueWith model { top with control := .flow .normal } callers
          | .value _ => configuration.fail model .constraint
      | .breakLoop => configuration.continueWith model { top with control := .flow .broken } callers
      | .continueLoop => configuration.continueWith model { top with control := .flow .continued } callers
      | .returnValue none => configuration.continueWith model { top with control := .returning none } callers
      | .returnValue (some value) =>
          match evaluateHere value with
          | .fault reason => configuration.fail model reason
          | .value returned => configuration.continueWith model
              { top with control := .returning (some returned) } callers
  | .declaring [] body => configuration.continueWith model { top with control := .execute body } callers
  | .declaring (.object declaration initializer :: rest) body =>
      match scopes with
      | [] => none
      | head :: _ =>
          if head.declares declaration.name then configuration.fail model .constraint
          else
            match declareObject model memory arrays scopes declaration (abi declaration.integer) choice.identity with
            | none => none
            | some (saved, nextArrays, nextScopes) =>
                match initializer with
                | none => some { configuration with
                    memory := saved, arrays := nextArrays,
                    stack := { top with scopes := nextScopes, control := .declaring rest body } :: callers }
                | some value =>
                    match declaration.shape with
                    | .array _ _ => configuration.fail model .constraint
                    | .scalar =>
                        match evaluate model policy saved nextArrays nextScopes value with
                        | .fault reason => configuration.fail model reason
                        | .value (.integer scalar) =>
                            match storeElement model policy saved nextArrays
                                ⟨declaration.integer, ⟨choice.identity, 0⟩⟩ scalar with
                            | .done stored => some { configuration with
                                memory := stored, arrays := nextArrays,
                                stack := { top with scopes := nextScopes, control := .declaring rest body } ::
                                  callers }
                            | .fault reason => configuration.fail model reason
                        | .value _ => configuration.fail model .constraint
  | .declaring (.pointer name initializer :: rest) body =>
      match scopes with
      | [] => none
      | head :: tail =>
          if head.declares name then configuration.fail model .constraint
          else
            match initializer with
            | none => configuration.continueWith model
                { top with scopes := head.bindPointer name none :: tail, control := .declaring rest body } callers
            | some value =>
                match evaluate model policy memory arrays (head.bindPointer name none :: tail) value with
                | .fault reason => configuration.fail model reason
                | .value delivered =>
                    if pointerValue delivered then configuration.continueWith model
                      { top with
                        scopes := head.bindPointer name (some delivered) :: tail,
                        control := .declaring rest body } callers
                    else configuration.fail model .constraint
  | .binding [] body => configuration.continueWith model { top with control := .execute body } callers
  | .binding ((.integer name type, .integer scalar) :: rest) body =>
      match scopes with
      | [] => none
      | head :: _ =>
          if head.declares name then configuration.fail model .constraint
          else
            match declareObject model memory arrays scopes (scalarDeclaration name type) (abi type) choice.identity with
            | none => none
            | some (saved, nextArrays, nextScopes) =>
                match storeElement model policy saved nextArrays ⟨type, ⟨choice.identity, 0⟩⟩ scalar with
                | .done stored => some { configuration with
                    memory := stored, arrays := nextArrays,
                    stack := { top with scopes := nextScopes, control := .binding rest body } :: callers }
                | .fault reason => configuration.fail model reason
  | .binding ((.pointer name, delivered) :: rest) body =>
      match scopes with
      | [] => none
      | head :: tail =>
          if head.declares name then configuration.fail model .constraint
          else configuration.continueWith model
            { top with scopes := head.bindPointer name (some delivered) :: tail, control := .binding rest body } callers
  | .binding ((.integer _ _, _) :: _) _ => configuration.fail model .constraint
  | .flow flow =>
      match top.continuation, flow with
      | .stop, .normal => configuration.continueWith model { top with control := .returning none } callers
      | .stop, .broken | .stop, .continued => configuration.fail model .constraint
      | .sequence next outer, .normal => configuration.continueWith model
          { top with control := .execute next, continuation := outer } callers
      | .sequence _ outer, .broken | .sequence _ outer, .continued =>
          configuration.continueWith model { top with continuation := outer } callers
      | .loop _ _ outer, .broken => configuration.continueWith model
          { top with control := .flow .normal, continuation := outer } callers
      | .loop condition body outer, .normal | .loop condition body outer, .continued =>
          configuration.continueWith model
            { top with control := .execute (.whileLoop condition body), continuation := outer } callers
      | .scope outer, _ =>
          match leaveScope model memory scopes with
          | none => none
          | some (saved, rest) => some { configuration with
              memory := saved,
              stack := { top with scopes := rest, continuation := outer } :: callers }
  | .returning value =>
      match top.continuation with
      | .scope outer =>
          match leaveScope model memory scopes with
          | none => none
          | some (saved, rest) => some { configuration with
              memory := saved,
              stack := { top with scopes := rest, continuation := outer } :: callers }
      | .sequence _ outer => configuration.continueWith model { top with continuation := outer } callers
      | .loop _ _ outer => configuration.continueWith model { top with continuation := outer } callers
      | .stop =>
          match callers with
          | [] => some { configuration with status := .finished value }
          | caller :: rest =>
              match caller.control with
              | .awaiting result =>
                  match deliver model policy memory arrays caller.scopes result value with
                  | .done (saved, updated) => some { configuration with
                      memory := saved,
                      stack := { caller with scopes := updated, control := .flow .normal } :: rest }
                  | .fault reason => configuration.fail model reason
              | _ => none
  | .awaiting _ => none

def step (choice : Choice) (configuration : Executable model) : Option (Executable model) :=
  match configuration.status, configuration.stack with
  | .running, top :: callers => advance model policy abi program choice configuration top callers
  | _, _ => none

/-- Deliver an external reply to the waiting activation. -/
def reply (value : Value model) (configuration : Executable model) : Option (Executable model) :=
  match configuration.status, configuration.stack with
  | .waiting _ _, caller :: rest =>
      match caller.control with
      | .awaiting result =>
          match deliver model policy configuration.memory configuration.arrays caller.scopes result (some value) with
          | .done (saved, updated) => some { configuration with
              memory := saved, status := .running,
              stack := { caller with scopes := updated, control := .flow .normal } :: rest }
          | .fault reason => some { configuration with status := .faulted reason }
      | _ => none
  | _, _ => none

/-- Start a program: call `main` with no arguments. -/
def start (main : String) (memory : State model.characters) (arrays : ArrayPointers.Catalog) :
    Option (Executable model) := do
  let definition ← program.lookup main
  let pending ← bindParameters (model := model) definition.parameters []
  some ⟨memory, arrays, [], [⟨[{}], .binding pending definition.body, .scope .stop⟩], .running⟩

end Step

/-! ## The independent step -/

section Independent

variable (model : Model) (policy : SignedConversionPolicy) (abi : IntegerType IntegerExtension → ObjectLayout.Layout)
  (program : Program model)

/-- The independent outcome of delivering a value to a waiting caller. -/
inductive Delivers (memory : SemanticState model.characters) (arrays : ArrayPointers.Catalog)
    (scopes : List (Scope model)) :
    Option String → Option (Value model) → Effect model (SemanticState model.characters × List (Scope model)) →
      Prop where
  | discard (value : Option (Value model)) : Delivers memory arrays scopes none value (.done (memory, scopes))
  | missing (name : String) : Delivers memory arrays scopes (some name) none (.fault .missingReturn)
  | object (name : String) (location : Lvalue) (target : Address) (scalar : IntegerScalar.Value model.parameters)
      (after : SemanticState model.characters) (resolved : Resolves name scopes (.object location))
      (typed : rootAddress location = some target)
      (storing : StoresElement model policy memory arrays target scalar (.done after)) :
      Delivers memory arrays scopes (some name) (some (.integer scalar)) (.done (after, scopes))
  | objectFault (name : String) (location : Lvalue) (target : Address) (scalar : IntegerScalar.Value model.parameters)
      (reason : Fault model) (resolved : Resolves name scopes (.object location))
      (typed : rootAddress location = some target)
      (storing : StoresElement model policy memory arrays target scalar (.fault reason)) :
      Delivers memory arrays scopes (some name) (some (.integer scalar)) (.fault reason)
  | objectKind (name : String) (location : Lvalue) (value : Value model) (resolved : Resolves name scopes (.object location))
      (mismatch : ∀ target scalar, rootAddress location = some target → value ≠ .integer scalar) :
      Delivers memory arrays scopes (some name) (some value) (.fault .constraint)
  | pointer (name : String) (old : Option (Value model)) (value : Value model) (updated : List (Scope model))
      (resolved : Resolves name scopes (.pointer old)) (kind : pointerValue value = true)
      (set : setPointerIn name value scopes = some updated) :
      Delivers memory arrays scopes (some name) (some value) (.done (memory, updated))
  | pointerMissing (name : String) (old : Option (Value model)) (value : Value model)
      (resolved : Resolves name scopes (.pointer old)) (kind : pointerValue value = true)
      (set : setPointerIn name value scopes = none) :
      Delivers memory arrays scopes (some name) (some value) (.fault .constraint)
  | pointerKind (name : String) (old : Option (Value model)) (value : Value model)
      (resolved : Resolves name scopes (.pointer old)) (kind : pointerValue value = false) :
      Delivers memory arrays scopes (some name) (some value) (.fault .constraint)
  | unbound (name : String) (value : Value model) (absent : Unbound name scopes) :
      Delivers memory arrays scopes (some name) (some value) (.fault .constraint)

/-- One independent step of a running configuration. Each premise is a
memory, scope or expression judgment; the open choices (new identities and
allocation success) are free in the rules. -/
inductive Step : Semantic model → Semantic model → Prop where
  | skip (c : Semantic model) (top : Activation model) (callers : List (Activation model))
      (running : c.status = .running) (stack : c.stack = top :: callers) (control : top.control = .execute .skip) :
      Step c { c with stack := { top with control := .flow .normal } :: callers }
  | assignPlaceFault (c : Semantic model) (top : Activation model) (callers : List (Activation model))
      (place : Place model) (value : Expression model) (reason : Fault model)
      (running : c.status = .running) (stack : c.stack = top :: callers)
      (control : top.control = .execute (.assign place value))
      (located : Locates model policy c.memory c.arrays top.scopes place (.error reason)) :
      Step c { c with status := .faulted reason }
  | assignValueFault (c : Semantic model) (top : Activation model) (callers : List (Activation model))
      (place : Place model) (value : Expression model) (target : Address) (reason : Fault model)
      (running : c.status = .running) (stack : c.stack = top :: callers)
      (control : top.control = .execute (.assign place value))
      (located : Locates model policy c.memory c.arrays top.scopes place (.ok target))
      (evaluated : Evaluates model policy c.memory c.arrays top.scopes value (.fault reason)) :
      Step c { c with status := .faulted reason }
  | assign (c : Semantic model) (top : Activation model) (callers : List (Activation model))
      (place : Place model) (value : Expression model) (target : Address)
      (scalar : IntegerScalar.Value model.parameters) (after : SemanticState model.characters)
      (running : c.status = .running) (stack : c.stack = top :: callers)
      (control : top.control = .execute (.assign place value))
      (located : Locates model policy c.memory c.arrays top.scopes place (.ok target))
      (evaluated : Evaluates model policy c.memory c.arrays top.scopes value (.value (.integer scalar)))
      (storing : StoresElement model policy c.memory c.arrays target scalar (.done after)) :
      Step c { c with memory := after, stack := { top with control := .flow .normal } :: callers }
  | assignStoreFault (c : Semantic model) (top : Activation model) (callers : List (Activation model))
      (place : Place model) (value : Expression model) (target : Address)
      (scalar : IntegerScalar.Value model.parameters) (reason : Fault model)
      (running : c.status = .running) (stack : c.stack = top :: callers)
      (control : top.control = .execute (.assign place value))
      (located : Locates model policy c.memory c.arrays top.scopes place (.ok target))
      (evaluated : Evaluates model policy c.memory c.arrays top.scopes value (.value (.integer scalar)))
      (storing : StoresElement model policy c.memory c.arrays target scalar (.fault reason)) :
      Step c { c with status := .faulted reason }
  | assignKind (c : Semantic model) (top : Activation model) (callers : List (Activation model))
      (place : Place model) (value : Expression model) (target : Address) (delivered : Value model)
      (running : c.status = .running) (stack : c.stack = top :: callers)
      (control : top.control = .execute (.assign place value))
      (located : Locates model policy c.memory c.arrays top.scopes place (.ok target))
      (evaluated : Evaluates model policy c.memory c.arrays top.scopes value (.value delivered))
      (kind : pointerValue delivered = true) :
      Step c { c with status := .faulted .constraint }
  | setPointerFault (c : Semantic model) (top : Activation model) (callers : List (Activation model))
      (name : String) (value : Expression model) (reason : Fault model)
      (running : c.status = .running) (stack : c.stack = top :: callers)
      (control : top.control = .execute (.setPointer name value))
      (evaluated : Evaluates model policy c.memory c.arrays top.scopes value (.fault reason)) :
      Step c { c with status := .faulted reason }
  | setPointer (c : Semantic model) (top : Activation model) (callers : List (Activation model))
      (name : String) (value : Expression model) (delivered : Value model) (updated : List (Scope model))
      (running : c.status = .running) (stack : c.stack = top :: callers)
      (control : top.control = .execute (.setPointer name value))
      (evaluated : Evaluates model policy c.memory c.arrays top.scopes value (.value delivered))
      (kind : pointerValue delivered = true) (set : setPointerIn name delivered top.scopes = some updated) :
      Step c { c with stack := { top with scopes := updated, control := .flow .normal } :: callers }
  | setPointerMissing (c : Semantic model) (top : Activation model) (callers : List (Activation model))
      (name : String) (value : Expression model) (delivered : Value model)
      (running : c.status = .running) (stack : c.stack = top :: callers)
      (control : top.control = .execute (.setPointer name value))
      (evaluated : Evaluates model policy c.memory c.arrays top.scopes value (.value delivered))
      (kind : pointerValue delivered = true) (set : setPointerIn name delivered top.scopes = none) :
      Step c { c with status := .faulted .constraint }
  | setPointerKind (c : Semantic model) (top : Activation model) (callers : List (Activation model))
      (name : String) (value : Expression model) (delivered : Value model)
      (running : c.status = .running) (stack : c.stack = top :: callers)
      (control : top.control = .execute (.setPointer name value))
      (evaluated : Evaluates model policy c.memory c.arrays top.scopes value (.value delivered))
      (kind : pointerValue delivered = false) :
      Step c { c with status := .faulted .constraint }
  | callFault (c : Semantic model) (top : Activation model) (callers : List (Activation model))
      (result : Option String) (function : String) (arguments : List (Expression model))
      (results : List (Result model)) (reason : Fault model)
      (running : c.status = .running) (stack : c.stack = top :: callers)
      (control : top.control = .execute (.call result function arguments))
      (evaluated : List.Forall₂ (Evaluates model policy c.memory c.arrays top.scopes) arguments results)
      (bad : argumentValues results = .error reason) :
      Step c { c with status := .faulted reason }
  | callUnknown (c : Semantic model) (top : Activation model) (callers : List (Activation model))
      (result : Option String) (function : String) (arguments : List (Expression model))
      (results : List (Result model)) (values : List (Value model))
      (running : c.status = .running) (stack : c.stack = top :: callers)
      (control : top.control = .execute (.call result function arguments))
      (evaluated : List.Forall₂ (Evaluates model policy c.memory c.arrays top.scopes) arguments results)
      (good : argumentValues results = .ok values) (unknown : program.lookup function = none) :
      Step c { c with status := .faulted .constraint }
  | callArity (c : Semantic model) (top : Activation model) (callers : List (Activation model))
      (result : Option String) (function : String) (arguments : List (Expression model))
      (results : List (Result model)) (values : List (Value model)) (definition : Function model)
      (running : c.status = .running) (stack : c.stack = top :: callers)
      (control : top.control = .execute (.call result function arguments))
      (evaluated : List.Forall₂ (Evaluates model policy c.memory c.arrays top.scopes) arguments results)
      (good : argumentValues results = .ok values) (known : program.lookup function = some definition)
      (mismatch : bindParameters definition.parameters values = none) :
      Step c { c with status := .faulted .constraint }
  | call (c : Semantic model) (top : Activation model) (callers : List (Activation model))
      (result : Option String) (function : String) (arguments : List (Expression model))
      (results : List (Result model)) (values : List (Value model)) (definition : Function model)
      (pending : List (Parameter × Value model))
      (running : c.status = .running) (stack : c.stack = top :: callers)
      (control : top.control = .execute (.call result function arguments))
      (evaluated : List.Forall₂ (Evaluates model policy c.memory c.arrays top.scopes) arguments results)
      (good : argumentValues results = .ok values) (known : program.lookup function = some definition)
      (bound : bindParameters definition.parameters values = some pending) :
      Step c { c with stack := ⟨[{}], .binding pending definition.body, .scope .stop⟩ ::
        { top with control := .awaiting result } :: callers }
  | externalFault (c : Semantic model) (top : Activation model) (callers : List (Activation model))
      (result : Option String) (service : String) (arguments : List (Expression model))
      (results : List (Result model)) (reason : Fault model)
      (running : c.status = .running) (stack : c.stack = top :: callers)
      (control : top.control = .execute (.external result service arguments))
      (evaluated : List.Forall₂ (Evaluates model policy c.memory c.arrays top.scopes) arguments results)
      (bad : argumentValues results = .error reason) :
      Step c { c with status := .faulted reason }
  | external (c : Semantic model) (top : Activation model) (callers : List (Activation model))
      (result : Option String) (service : String) (arguments : List (Expression model))
      (results : List (Result model)) (values : List (Value model))
      (running : c.status = .running) (stack : c.stack = top :: callers)
      (control : top.control = .execute (.external result service arguments))
      (evaluated : List.Forall₂ (Evaluates model policy c.memory c.arrays top.scopes) arguments results)
      (good : argumentValues results = .ok values) :
      Step c { c with status := .waiting service values, stack := { top with control := .awaiting result } :: callers }
  | allocateFault (c : Semantic model) (top : Activation model) (callers : List (Activation model))
      (name : String) (type : IntegerType IntegerExtension) (count : Expression model) (reason : Fault model)
      (running : c.status = .running) (stack : c.stack = top :: callers)
      (control : top.control = .execute (.allocate name type count))
      (evaluated : Evaluates model policy c.memory c.arrays top.scopes count (.fault reason)) :
      Step c { c with status := .faulted reason }
  | allocate (c : Semantic model) (top : Activation model) (callers : List (Activation model))
      (name : String) (type : IntegerType IntegerExtension) (count : Expression model)
      (amount : IntegerScalar.Value model.parameters) (positive : 0 < amount.integer.value.toNat)
      (identity : BlockId) (after : SemanticState model.characters) (nextArrays : ArrayPointers.Catalog)
      (location : Lvalue) (updated : List (Scope model))
      (running : c.status = .running) (stack : c.stack = top :: callers)
      (control : top.control = .execute (.allocate name type count))
      (evaluated : Evaluates model policy c.memory c.arrays top.scopes count (.value (.integer amount)))
      (creation : IntegerObjectConstruction.Creation model c.memory c.arrays
        ⟨name, type, .array amount.integer.value.toNat positive⟩ (abi type) identity .indeterminate
        after nextArrays location)
      (set : setPointerIn name (.address ⟨type, ⟨identity, 0⟩⟩) top.scopes = some updated) :
      Step c { c with
        memory := after, arrays := nextArrays, heap := identity :: c.heap,
        stack := { top with scopes := updated, control := .flow .normal } :: callers }
  | allocateUnbound (c : Semantic model) (top : Activation model) (callers : List (Activation model))
      (name : String) (type : IntegerType IntegerExtension) (count : Expression model)
      (amount : IntegerScalar.Value model.parameters) (positive : 0 < amount.integer.value.toNat)
      (identity : BlockId) (after : SemanticState model.characters) (nextArrays : ArrayPointers.Catalog)
      (location : Lvalue)
      (running : c.status = .running) (stack : c.stack = top :: callers)
      (control : top.control = .execute (.allocate name type count))
      (evaluated : Evaluates model policy c.memory c.arrays top.scopes count (.value (.integer amount)))
      (creation : IntegerObjectConstruction.Creation model c.memory c.arrays
        ⟨name, type, .array amount.integer.value.toNat positive⟩ (abi type) identity .indeterminate
        after nextArrays location)
      (set : setPointerIn name (.address ⟨type, ⟨identity, 0⟩⟩) top.scopes = none) :
      Step c { c with status := .faulted .constraint }
  | allocateNull (c : Semantic model) (top : Activation model) (callers : List (Activation model))
      (name : String) (type : IntegerType IntegerExtension) (count : Expression model)
      (amount : IntegerScalar.Value model.parameters) (updated : List (Scope model))
      (running : c.status = .running) (stack : c.stack = top :: callers)
      (control : top.control = .execute (.allocate name type count))
      (evaluated : Evaluates model policy c.memory c.arrays top.scopes count (.value (.integer amount)))
      (set : setPointerIn name .null top.scopes = some updated) :
      Step c { c with stack := { top with scopes := updated, control := .flow .normal } :: callers }
  | allocateNullUnbound (c : Semantic model) (top : Activation model) (callers : List (Activation model))
      (name : String) (type : IntegerType IntegerExtension) (count : Expression model)
      (amount : IntegerScalar.Value model.parameters)
      (running : c.status = .running) (stack : c.stack = top :: callers)
      (control : top.control = .execute (.allocate name type count))
      (evaluated : Evaluates model policy c.memory c.arrays top.scopes count (.value (.integer amount)))
      (set : setPointerIn name .null top.scopes = none) :
      Step c { c with status := .faulted .constraint }
  | allocateKind (c : Semantic model) (top : Activation model) (callers : List (Activation model))
      (name : String) (type : IntegerType IntegerExtension) (count : Expression model) (delivered : Value model)
      (running : c.status = .running) (stack : c.stack = top :: callers)
      (control : top.control = .execute (.allocate name type count))
      (evaluated : Evaluates model policy c.memory c.arrays top.scopes count (.value delivered))
      (kind : pointerValue delivered = true) :
      Step c { c with status := .faulted .constraint }
  | releaseFault (c : Semantic model) (top : Activation model) (callers : List (Activation model))
      (pointer : Expression model) (reason : Fault model)
      (running : c.status = .running) (stack : c.stack = top :: callers)
      (control : top.control = .execute (.release pointer))
      (evaluated : Evaluates model policy c.memory c.arrays top.scopes pointer (.fault reason)) :
      Step c { c with status := .faulted reason }
  | releaseNull (c : Semantic model) (top : Activation model) (callers : List (Activation model))
      (pointer : Expression model)
      (running : c.status = .running) (stack : c.stack = top :: callers)
      (control : top.control = .execute (.release pointer))
      (evaluated : Evaluates model policy c.memory c.arrays top.scopes pointer (.value .null)) :
      Step c { c with stack := { top with control := .flow .normal } :: callers }
  | release (c : Semantic model) (top : Activation model) (callers : List (Activation model))
      (pointer : Expression model) (target : Address)
      (after : Mettapedia.Machines.CMemory.Heap
        (Mettapedia.GSLT.SeparationAlgebra.Excl (Option (ByteStorageData.Byte model.characters))))
      (running : c.status = .running) (stack : c.stack = top :: callers)
      (control : top.control = .execute (.release pointer))
      (evaluated : Evaluates model policy c.memory c.arrays top.scopes pointer (.value (.address target)))
      (start : target.pointer.index = 0) (dynamic : target.pointer.object ∈ c.heap)
      (retired : AutomaticObjectScopes.Retirement c.memory.memory target.pointer.object after) :
      Step c { c with
        memory := ⟨after, c.memory.catalog⟩, heap := c.heap.erase target.pointer.object,
        stack := { top with control := .flow .normal } :: callers }
  | releaseRefused (c : Semantic model) (top : Activation model) (callers : List (Activation model))
      (pointer : Expression model) (target : Address)
      (running : c.status = .running) (stack : c.stack = top :: callers)
      (control : top.control = .execute (.release pointer))
      (evaluated : Evaluates model policy c.memory c.arrays top.scopes pointer (.value (.address target)))
      (start : target.pointer.index = 0) (dynamic : target.pointer.object ∈ c.heap)
      (refused : ¬∃ after, AutomaticObjectScopes.Retirement c.memory.memory target.pointer.object after) :
      Step c { c with status := .faulted .invalidRelease }
  | releaseInvalid (c : Semantic model) (top : Activation model) (callers : List (Activation model))
      (pointer : Expression model) (target : Address)
      (running : c.status = .running) (stack : c.stack = top :: callers)
      (control : top.control = .execute (.release pointer))
      (evaluated : Evaluates model policy c.memory c.arrays top.scopes pointer (.value (.address target)))
      (invalid : ¬(target.pointer.index = 0 ∧ target.pointer.object ∈ c.heap)) :
      Step c { c with status := .faulted .invalidRelease }
  | releaseKind (c : Semantic model) (top : Activation model) (callers : List (Activation model))
      (pointer : Expression model) (scalar : IntegerScalar.Value model.parameters)
      (running : c.status = .running) (stack : c.stack = top :: callers)
      (control : top.control = .execute (.release pointer))
      (evaluated : Evaluates model policy c.memory c.arrays top.scopes pointer (.value (.integer scalar))) :
      Step c { c with status := .faulted .constraint }
  | sequence (c : Semantic model) (top : Activation model) (callers : List (Activation model))
      (first second : Statement model)
      (running : c.status = .running) (stack : c.stack = top :: callers)
      (control : top.control = .execute (.sequence first second)) :
      Step c { c with stack := { top with
        control := .execute first,
        continuation := .sequence second top.continuation } :: callers }
  | block (c : Semantic model) (top : Activation model) (callers : List (Activation model))
      (declarations : List (Declaration model)) (body : Statement model)
      (running : c.status = .running) (stack : c.stack = top :: callers)
      (control : top.control = .execute (.block declarations body)) :
      Step c { c with stack := { top with
        scopes := {} :: top.scopes, control := .declaring declarations body,
        continuation := .scope top.continuation } :: callers }
  | conditionalFault (c : Semantic model) (top : Activation model) (callers : List (Activation model))
      (condition : Expression model) (yes no : Statement model) (reason : Fault model)
      (running : c.status = .running) (stack : c.stack = top :: callers)
      (control : top.control = .execute (.conditional condition yes no))
      (evaluated : Evaluates model policy c.memory c.arrays top.scopes condition (.fault reason)) :
      Step c { c with status := .faulted reason }
  | conditional (c : Semantic model) (top : Activation model) (callers : List (Activation model))
      (condition : Expression model) (yes no : Statement model) (test : IntegerScalar.Value model.parameters)
      (running : c.status = .running) (stack : c.stack = top :: callers)
      (control : top.control = .execute (.conditional condition yes no))
      (evaluated : Evaluates model policy c.memory c.arrays top.scopes condition (.value (.integer test))) :
      Step c { c with stack := { top with control := .execute (if IntegerScalar.truth test then yes else no) } ::
        callers }
  | conditionalKind (c : Semantic model) (top : Activation model) (callers : List (Activation model))
      (condition : Expression model) (yes no : Statement model) (delivered : Value model)
      (running : c.status = .running) (stack : c.stack = top :: callers)
      (control : top.control = .execute (.conditional condition yes no))
      (evaluated : Evaluates model policy c.memory c.arrays top.scopes condition (.value delivered))
      (kind : pointerValue delivered = true) :
      Step c { c with status := .faulted .constraint }
  | whileFault (c : Semantic model) (top : Activation model) (callers : List (Activation model))
      (condition : Expression model) (body : Statement model) (reason : Fault model)
      (running : c.status = .running) (stack : c.stack = top :: callers)
      (control : top.control = .execute (.whileLoop condition body))
      (evaluated : Evaluates model policy c.memory c.arrays top.scopes condition (.fault reason)) :
      Step c { c with status := .faulted reason }
  | whileTrue (c : Semantic model) (top : Activation model) (callers : List (Activation model))
      (condition : Expression model) (body : Statement model) (test : IntegerScalar.Value model.parameters)
      (running : c.status = .running) (stack : c.stack = top :: callers)
      (control : top.control = .execute (.whileLoop condition body))
      (evaluated : Evaluates model policy c.memory c.arrays top.scopes condition (.value (.integer test)))
      (holds : IntegerScalar.truth test = true) :
      Step c { c with stack := { top with
        control := .execute body,
        continuation := .loop condition body top.continuation } :: callers }
  | whileFalse (c : Semantic model) (top : Activation model) (callers : List (Activation model))
      (condition : Expression model) (body : Statement model) (test : IntegerScalar.Value model.parameters)
      (running : c.status = .running) (stack : c.stack = top :: callers)
      (control : top.control = .execute (.whileLoop condition body))
      (evaluated : Evaluates model policy c.memory c.arrays top.scopes condition (.value (.integer test)))
      (fails : IntegerScalar.truth test = false) :
      Step c { c with stack := { top with control := .flow .normal } :: callers }
  | whileKind (c : Semantic model) (top : Activation model) (callers : List (Activation model))
      (condition : Expression model) (body : Statement model) (delivered : Value model)
      (running : c.status = .running) (stack : c.stack = top :: callers)
      (control : top.control = .execute (.whileLoop condition body))
      (evaluated : Evaluates model policy c.memory c.arrays top.scopes condition (.value delivered))
      (kind : pointerValue delivered = true) :
      Step c { c with status := .faulted .constraint }
  | breakLoop (c : Semantic model) (top : Activation model) (callers : List (Activation model))
      (running : c.status = .running) (stack : c.stack = top :: callers)
      (control : top.control = .execute .breakLoop) :
      Step c { c with stack := { top with control := .flow .broken } :: callers }
  | continueLoop (c : Semantic model) (top : Activation model) (callers : List (Activation model))
      (running : c.status = .running) (stack : c.stack = top :: callers)
      (control : top.control = .execute .continueLoop) :
      Step c { c with stack := { top with control := .flow .continued } :: callers }
  | returnNone (c : Semantic model) (top : Activation model) (callers : List (Activation model))
      (running : c.status = .running) (stack : c.stack = top :: callers)
      (control : top.control = .execute (.returnValue none)) :
      Step c { c with stack := { top with control := .returning none } :: callers }
  | returnFault (c : Semantic model) (top : Activation model) (callers : List (Activation model))
      (value : Expression model) (reason : Fault model)
      (running : c.status = .running) (stack : c.stack = top :: callers)
      (control : top.control = .execute (.returnValue (some value)))
      (evaluated : Evaluates model policy c.memory c.arrays top.scopes value (.fault reason)) :
      Step c { c with status := .faulted reason }
  | returnValue (c : Semantic model) (top : Activation model) (callers : List (Activation model))
      (value : Expression model) (returned : Value model)
      (running : c.status = .running) (stack : c.stack = top :: callers)
      (control : top.control = .execute (.returnValue (some value)))
      (evaluated : Evaluates model policy c.memory c.arrays top.scopes value (.value returned)) :
      Step c { c with stack := { top with control := .returning (some returned) } :: callers }
  | declaringDone (c : Semantic model) (top : Activation model) (callers : List (Activation model))
      (body : Statement model)
      (running : c.status = .running) (stack : c.stack = top :: callers)
      (control : top.control = .declaring [] body) :
      Step c { c with stack := { top with control := .execute body } :: callers }
  | declaringRedeclared (c : Semantic model) (top : Activation model) (callers : List (Activation model))
      (declaration : Declaration model) (rest : List (Declaration model)) (body : Statement model)
      (head : Scope model) (tail : List (Scope model)) (name : String)
      (running : c.status = .running) (stack : c.stack = top :: callers)
      (control : top.control = .declaring (declaration :: rest) body) (scopes : top.scopes = head :: tail)
      (named : declaration.name = name)
      (redeclared : head.declares name = true) :
      Step c { c with status := .faulted .constraint }
  | declaringObject (c : Semantic model) (top : Activation model) (callers : List (Activation model))
      (declaration : IntegerObjectConstruction.Declaration) (rest : List (Declaration model)) (body : Statement model)
      (head : Scope model) (tail : List (Scope model)) (identity : BlockId)
      (after : SemanticState model.characters) (nextArrays : ArrayPointers.Catalog) (nextScopes : List (Scope model))
      (running : c.status = .running) (stack : c.stack = top :: callers)
      (control : top.control = .declaring (.object declaration none :: rest) body) (scopes : top.scopes = head :: tail)
      (fresh : head.declares declaration.name = false)
      (declared : DeclaresObject model c.memory c.arrays top.scopes declaration (abi declaration.integer) identity
        after nextArrays nextScopes) :
      Step c { c with
        memory := after, arrays := nextArrays,
        stack := { top with scopes := nextScopes, control := .declaring rest body } :: callers }
  | declaringArrayInitializer (c : Semantic model) (top : Activation model) (callers : List (Activation model))
      (declaration : IntegerObjectConstruction.Declaration) (value : Expression model)
      (rest : List (Declaration model)) (body : Statement model)
      (head : Scope model) (tail : List (Scope model)) (identity : BlockId)
      (after : SemanticState model.characters) (nextArrays : ArrayPointers.Catalog) (nextScopes : List (Scope model))
      (count : Nat) (positive : 0 < count)
      (running : c.status = .running) (stack : c.stack = top :: callers)
      (control : top.control = .declaring (.object declaration (some value) :: rest) body)
      (scopes : top.scopes = head :: tail) (fresh : head.declares declaration.name = false)
      (declared : DeclaresObject model c.memory c.arrays top.scopes declaration (abi declaration.integer) identity
        after nextArrays nextScopes)
      (array : declaration.shape = .array count positive) :
      Step c { c with status := .faulted .constraint }
  | declaringInitializerFault (c : Semantic model) (top : Activation model) (callers : List (Activation model))
      (declaration : IntegerObjectConstruction.Declaration) (value : Expression model)
      (rest : List (Declaration model)) (body : Statement model)
      (head : Scope model) (tail : List (Scope model)) (identity : BlockId)
      (after : SemanticState model.characters) (nextArrays : ArrayPointers.Catalog) (nextScopes : List (Scope model))
      (reason : Fault model)
      (running : c.status = .running) (stack : c.stack = top :: callers)
      (control : top.control = .declaring (.object declaration (some value) :: rest) body)
      (scopes : top.scopes = head :: tail) (fresh : head.declares declaration.name = false)
      (declared : DeclaresObject model c.memory c.arrays top.scopes declaration (abi declaration.integer) identity
        after nextArrays nextScopes)
      (scalar : declaration.shape = .scalar)
      (evaluated : Evaluates model policy after nextArrays nextScopes value (.fault reason)) :
      Step c { c with status := .faulted reason }
  | declaringInitialized (c : Semantic model) (top : Activation model) (callers : List (Activation model))
      (declaration : IntegerObjectConstruction.Declaration) (value : Expression model)
      (rest : List (Declaration model)) (body : Statement model)
      (head : Scope model) (tail : List (Scope model)) (identity : BlockId)
      (after : SemanticState model.characters) (nextArrays : ArrayPointers.Catalog) (nextScopes : List (Scope model))
      (initial : IntegerScalar.Value model.parameters) (stored : SemanticState model.characters)
      (running : c.status = .running) (stack : c.stack = top :: callers)
      (control : top.control = .declaring (.object declaration (some value) :: rest) body)
      (scopes : top.scopes = head :: tail) (fresh : head.declares declaration.name = false)
      (declared : DeclaresObject model c.memory c.arrays top.scopes declaration (abi declaration.integer) identity
        after nextArrays nextScopes)
      (scalar : declaration.shape = .scalar)
      (evaluated : Evaluates model policy after nextArrays nextScopes value (.value (.integer initial)))
      (storing : StoresElement model policy after nextArrays ⟨declaration.integer, ⟨identity, 0⟩⟩ initial
        (.done stored)) :
      Step c { c with
        memory := stored, arrays := nextArrays,
        stack := { top with scopes := nextScopes, control := .declaring rest body } :: callers }
  | declaringInitializerStoreFault (c : Semantic model) (top : Activation model) (callers : List (Activation model))
      (declaration : IntegerObjectConstruction.Declaration) (value : Expression model)
      (rest : List (Declaration model)) (body : Statement model)
      (head : Scope model) (tail : List (Scope model)) (identity : BlockId)
      (after : SemanticState model.characters) (nextArrays : ArrayPointers.Catalog) (nextScopes : List (Scope model))
      (initial : IntegerScalar.Value model.parameters) (reason : Fault model)
      (running : c.status = .running) (stack : c.stack = top :: callers)
      (control : top.control = .declaring (.object declaration (some value) :: rest) body)
      (scopes : top.scopes = head :: tail) (fresh : head.declares declaration.name = false)
      (declared : DeclaresObject model c.memory c.arrays top.scopes declaration (abi declaration.integer) identity
        after nextArrays nextScopes)
      (scalar : declaration.shape = .scalar)
      (evaluated : Evaluates model policy after nextArrays nextScopes value (.value (.integer initial)))
      (storing : StoresElement model policy after nextArrays ⟨declaration.integer, ⟨identity, 0⟩⟩ initial
        (.fault reason)) :
      Step c { c with status := .faulted reason }
  | declaringInitializerKind (c : Semantic model) (top : Activation model) (callers : List (Activation model))
      (declaration : IntegerObjectConstruction.Declaration) (value : Expression model)
      (rest : List (Declaration model)) (body : Statement model)
      (head : Scope model) (tail : List (Scope model)) (identity : BlockId)
      (after : SemanticState model.characters) (nextArrays : ArrayPointers.Catalog) (nextScopes : List (Scope model))
      (delivered : Value model)
      (running : c.status = .running) (stack : c.stack = top :: callers)
      (control : top.control = .declaring (.object declaration (some value) :: rest) body)
      (scopes : top.scopes = head :: tail) (fresh : head.declares declaration.name = false)
      (declared : DeclaresObject model c.memory c.arrays top.scopes declaration (abi declaration.integer) identity
        after nextArrays nextScopes)
      (scalar : declaration.shape = .scalar)
      (evaluated : Evaluates model policy after nextArrays nextScopes value (.value delivered))
      (kind : pointerValue delivered = true) :
      Step c { c with status := .faulted .constraint }
  | declaringPointer (c : Semantic model) (top : Activation model) (callers : List (Activation model))
      (name : String) (rest : List (Declaration model)) (body : Statement model)
      (head : Scope model) (tail : List (Scope model))
      (running : c.status = .running) (stack : c.stack = top :: callers)
      (control : top.control = .declaring (.pointer name none :: rest) body) (scopes : top.scopes = head :: tail)
      (fresh : head.declares name = false) :
      Step c { c with stack := { top with
        scopes := head.bindPointer name none :: tail,
        control := .declaring rest body } :: callers }
  | declaringPointerFault (c : Semantic model) (top : Activation model) (callers : List (Activation model))
      (name : String) (value : Expression model) (rest : List (Declaration model)) (body : Statement model)
      (head : Scope model) (tail : List (Scope model)) (reason : Fault model)
      (running : c.status = .running) (stack : c.stack = top :: callers)
      (control : top.control = .declaring (.pointer name (some value) :: rest) body)
      (scopes : top.scopes = head :: tail) (fresh : head.declares name = false)
      (evaluated : Evaluates model policy c.memory c.arrays (head.bindPointer name none :: tail) value
        (.fault reason)) :
      Step c { c with status := .faulted reason }
  | declaringPointerInitialized (c : Semantic model) (top : Activation model) (callers : List (Activation model))
      (name : String) (value : Expression model) (rest : List (Declaration model)) (body : Statement model)
      (head : Scope model) (tail : List (Scope model)) (delivered : Value model)
      (running : c.status = .running) (stack : c.stack = top :: callers)
      (control : top.control = .declaring (.pointer name (some value) :: rest) body)
      (scopes : top.scopes = head :: tail) (fresh : head.declares name = false)
      (evaluated : Evaluates model policy c.memory c.arrays (head.bindPointer name none :: tail) value
        (.value delivered))
      (kind : pointerValue delivered = true) :
      Step c { c with stack := { top with
        scopes := head.bindPointer name (some delivered) :: tail,
        control := .declaring rest body } :: callers }
  | declaringPointerKind (c : Semantic model) (top : Activation model) (callers : List (Activation model))
      (name : String) (value : Expression model) (rest : List (Declaration model)) (body : Statement model)
      (head : Scope model) (tail : List (Scope model)) (delivered : Value model)
      (running : c.status = .running) (stack : c.stack = top :: callers)
      (control : top.control = .declaring (.pointer name (some value) :: rest) body)
      (scopes : top.scopes = head :: tail) (fresh : head.declares name = false)
      (evaluated : Evaluates model policy c.memory c.arrays (head.bindPointer name none :: tail) value
        (.value delivered))
      (kind : pointerValue delivered = false) :
      Step c { c with status := .faulted .constraint }
  | bindingDone (c : Semantic model) (top : Activation model) (callers : List (Activation model))
      (body : Statement model)
      (running : c.status = .running) (stack : c.stack = top :: callers)
      (control : top.control = .binding [] body) :
      Step c { c with stack := { top with control := .execute body } :: callers }
  | bindingRedeclared (c : Semantic model) (top : Activation model) (callers : List (Activation model))
      (parameter : Parameter) (delivered : Value model) (rest : List (Parameter × Value model))
      (body : Statement model) (head : Scope model) (tail : List (Scope model)) (name : String)
      (running : c.status = .running) (stack : c.stack = top :: callers)
      (control : top.control = .binding ((parameter, delivered) :: rest) body) (scopes : top.scopes = head :: tail)
      (named : parameter.name = name) (kinds : parameter.accepts delivered = true)
      (redeclared : head.declares name = true) :
      Step c { c with status := .faulted .constraint }
  | bindingInteger (c : Semantic model) (top : Activation model) (callers : List (Activation model))
      (name : String) (type : IntegerType IntegerExtension) (scalar : IntegerScalar.Value model.parameters)
      (rest : List (Parameter × Value model)) (body : Statement model)
      (head : Scope model) (tail : List (Scope model)) (identity : BlockId)
      (after : SemanticState model.characters) (nextArrays : ArrayPointers.Catalog) (nextScopes : List (Scope model))
      (stored : SemanticState model.characters)
      (running : c.status = .running) (stack : c.stack = top :: callers)
      (control : top.control = .binding ((.integer name type, .integer scalar) :: rest) body)
      (scopes : top.scopes = head :: tail) (fresh : head.declares name = false)
      (declared : DeclaresObject model c.memory c.arrays top.scopes (scalarDeclaration name type) (abi type) identity
        after nextArrays nextScopes)
      (storing : StoresElement model policy after nextArrays ⟨type, ⟨identity, 0⟩⟩ scalar (.done stored)) :
      Step c { c with
        memory := stored, arrays := nextArrays,
        stack := { top with scopes := nextScopes, control := .binding rest body } :: callers }
  | bindingIntegerFault (c : Semantic model) (top : Activation model) (callers : List (Activation model))
      (name : String) (type : IntegerType IntegerExtension) (scalar : IntegerScalar.Value model.parameters)
      (rest : List (Parameter × Value model)) (body : Statement model)
      (head : Scope model) (tail : List (Scope model)) (identity : BlockId)
      (after : SemanticState model.characters) (nextArrays : ArrayPointers.Catalog) (nextScopes : List (Scope model))
      (reason : Fault model)
      (running : c.status = .running) (stack : c.stack = top :: callers)
      (control : top.control = .binding ((.integer name type, .integer scalar) :: rest) body)
      (scopes : top.scopes = head :: tail) (fresh : head.declares name = false)
      (declared : DeclaresObject model c.memory c.arrays top.scopes (scalarDeclaration name type) (abi type) identity
        after nextArrays nextScopes)
      (storing : StoresElement model policy after nextArrays ⟨type, ⟨identity, 0⟩⟩ scalar (.fault reason)) :
      Step c { c with status := .faulted reason }
  | bindingPointer (c : Semantic model) (top : Activation model) (callers : List (Activation model))
      (name : String) (delivered : Value model) (rest : List (Parameter × Value model)) (body : Statement model)
      (head : Scope model) (tail : List (Scope model))
      (running : c.status = .running) (stack : c.stack = top :: callers)
      (control : top.control = .binding ((.pointer name, delivered) :: rest) body)
      (scopes : top.scopes = head :: tail) (fresh : head.declares name = false) :
      Step c { c with stack := { top with
        scopes := head.bindPointer name (some delivered) :: tail,
        control := .binding rest body } :: callers }
  | bindingMismatch (c : Semantic model) (top : Activation model) (callers : List (Activation model))
      (name : String) (type : IntegerType IntegerExtension) (delivered : Value model)
      (rest : List (Parameter × Value model)) (body : Statement model)
      (running : c.status = .running) (stack : c.stack = top :: callers)
      (control : top.control = .binding ((.integer name type, delivered) :: rest) body)
      (kind : pointerValue delivered = true) :
      Step c { c with status := .faulted .constraint }
  | fallsOff (c : Semantic model) (top : Activation model) (callers : List (Activation model))
      (running : c.status = .running) (stack : c.stack = top :: callers)
      (control : top.control = .flow .normal) (continuation : top.continuation = .stop) :
      Step c { c with stack := { top with control := .returning none } :: callers }
  | strayJump (c : Semantic model) (top : Activation model) (callers : List (Activation model)) (flow : Flow)
      (running : c.status = .running) (stack : c.stack = top :: callers)
      (control : top.control = .flow flow) (abrupt : flow ≠ .normal) (continuation : top.continuation = .stop) :
      Step c { c with status := .faulted .constraint }
  | next (c : Semantic model) (top : Activation model) (callers : List (Activation model))
      (statement : Statement model) (outer : Continuation model)
      (running : c.status = .running) (stack : c.stack = top :: callers)
      (control : top.control = .flow .normal) (continuation : top.continuation = .sequence statement outer) :
      Step c { c with stack := { top with control := .execute statement, continuation := outer } :: callers }
  | skipNext (c : Semantic model) (top : Activation model) (callers : List (Activation model)) (flow : Flow)
      (statement : Statement model) (outer : Continuation model)
      (running : c.status = .running) (stack : c.stack = top :: callers)
      (control : top.control = .flow flow) (abrupt : flow ≠ .normal)
      (continuation : top.continuation = .sequence statement outer) :
      Step c { c with stack := { top with continuation := outer } :: callers }
  | exitLoop (c : Semantic model) (top : Activation model) (callers : List (Activation model))
      (condition : Expression model) (body : Statement model) (outer : Continuation model)
      (running : c.status = .running) (stack : c.stack = top :: callers)
      (control : top.control = .flow .broken) (continuation : top.continuation = .loop condition body outer) :
      Step c { c with stack := { top with control := .flow .normal, continuation := outer } :: callers }
  | iterate (c : Semantic model) (top : Activation model) (callers : List (Activation model)) (flow : Flow)
      (condition : Expression model) (body : Statement model) (outer : Continuation model)
      (running : c.status = .running) (stack : c.stack = top :: callers)
      (control : top.control = .flow flow) (again : flow ≠ .broken)
      (continuation : top.continuation = .loop condition body outer) :
      Step c { c with stack := { top with
        control := .execute (.whileLoop condition body),
        continuation := outer } :: callers }
  | leave (c : Semantic model) (top : Activation model) (callers : List (Activation model)) (flow : Flow)
      (outer : Continuation model) (after : SemanticState model.characters) (rest : List (Scope model))
      (running : c.status = .running) (stack : c.stack = top :: callers)
      (control : top.control = .flow flow) (continuation : top.continuation = .scope outer)
      (left : LeavesScope model c.memory top.scopes after rest) :
      Step c { c with memory := after, stack := { top with scopes := rest, continuation := outer } :: callers }
  | returnLeave (c : Semantic model) (top : Activation model) (callers : List (Activation model))
      (value : Option (Value model)) (outer : Continuation model) (after : SemanticState model.characters)
      (rest : List (Scope model))
      (running : c.status = .running) (stack : c.stack = top :: callers)
      (control : top.control = .returning value) (continuation : top.continuation = .scope outer)
      (left : LeavesScope model c.memory top.scopes after rest) :
      Step c { c with memory := after, stack := { top with scopes := rest, continuation := outer } :: callers }
  | returnSkip (c : Semantic model) (top : Activation model) (callers : List (Activation model))
      (value : Option (Value model)) (statement : Statement model) (outer : Continuation model)
      (running : c.status = .running) (stack : c.stack = top :: callers)
      (control : top.control = .returning value) (continuation : top.continuation = .sequence statement outer) :
      Step c { c with stack := { top with continuation := outer } :: callers }
  | returnExitLoop (c : Semantic model) (top : Activation model) (callers : List (Activation model))
      (value : Option (Value model)) (condition : Expression model) (body : Statement model)
      (outer : Continuation model)
      (running : c.status = .running) (stack : c.stack = top :: callers)
      (control : top.control = .returning value) (continuation : top.continuation = .loop condition body outer) :
      Step c { c with stack := { top with continuation := outer } :: callers }
  | finish (c : Semantic model) (top : Activation model) (value : Option (Value model))
      (running : c.status = .running) (stack : c.stack = [top])
      (control : top.control = .returning value) (continuation : top.continuation = .stop) :
      Step c { c with status := .finished value }
  | deliver (c : Semantic model) (top caller : Activation model) (rest : List (Activation model))
      (value : Option (Value model)) (result : Option String)
      (after : SemanticState model.characters) (updated : List (Scope model))
      (running : c.status = .running) (stack : c.stack = top :: caller :: rest)
      (control : top.control = .returning value) (continuation : top.continuation = .stop)
      (waiting : caller.control = .awaiting result)
      (delivered : Delivers model policy c.memory c.arrays caller.scopes result value (.done (after, updated))) :
      Step c { c with memory := after, stack := { caller with scopes := updated, control := .flow .normal } :: rest }
  | deliverFault (c : Semantic model) (top caller : Activation model) (rest : List (Activation model))
      (value : Option (Value model)) (result : Option String) (reason : Fault model)
      (running : c.status = .running) (stack : c.stack = top :: caller :: rest)
      (control : top.control = .returning value) (continuation : top.continuation = .stop)
      (waiting : caller.control = .awaiting result)
      (delivered : Delivers model policy c.memory c.arrays caller.scopes result value (.fault reason)) :
      Step c { c with status := .faulted reason }

end Independent

/-! ## Soundness of the executable step -/

section Soundness

variable (model : Model) (policy : SignedConversionPolicy) (abi : IntegerType IntegerExtension → ObjectLayout.Layout)
  (program : Program model)

theorem argumentValues_sound (memory : State model.characters) (arrays : ArrayPointers.Catalog)
    (scopes : List (Scope model)) (arguments : List (Expression model)) :
    List.Forall₂ (Evaluates model policy (ObjectAccessMemory.represent memory) arrays scopes) arguments
      (arguments.map (evaluate model policy memory arrays scopes)) := by
  induction arguments with
  | nil => exact .nil
  | cons argument rest ih => exact .cons (evaluate_sound model policy memory arrays scopes argument) ih

theorem deliver_sound (memory : State model.characters) (arrays : ArrayPointers.Catalog)
    (scopes : List (Scope model)) (result : Option String) (value : Option (Value model)) :
    Delivers model policy (ObjectAccessMemory.represent memory) arrays scopes result value
      (match deliver model policy memory arrays scopes result value with
        | .done (saved, updated) => .done (ObjectAccessMemory.represent saved, updated)
        | .fault reason => .fault reason) := by
  cases result with
  | none => exact .discard value
  | some name =>
      cases value with
      | none => exact .missing name
      | some delivered =>
          cases found : resolve scopes name with
          | none =>
              simp only [deliver, found]
              exact .unbound name delivered ((resolve_none_iff scopes name).mp found)
          | some entity =>
              have resolved := resolve_sound scopes name entity found
              cases entity with
              | object location =>
                  cases typed : rootAddress location with
                  | none =>
                      simp only [deliver, found, typed]
                      exact .objectKind name location delivered resolved
                        (by intro target scalar same; rw [typed] at same; cases same)
                  | some target =>
                      cases delivered with
                      | integer scalar =>
                          have storing := storeElement_sound model policy memory arrays target scalar
                          cases stored : storeElement model policy memory arrays target scalar with
                          | done saved =>
                              simp only [deliver, found, typed, stored]
                              rw [stored] at storing
                              exact .object name location target scalar _ resolved typed storing
                          | fault reason =>
                              simp only [deliver, found, typed, stored]
                              rw [stored] at storing
                              exact .objectFault name location target scalar reason resolved typed storing
                      | address pointer =>
                          simp only [deliver, found, typed]
                          exact .objectKind name location _ resolved (by intro _ _ _ same; cases same)
                      | null =>
                          simp only [deliver, found, typed]
                          exact .objectKind name location _ resolved (by intro _ _ _ same; cases same)
              | pointer old =>
                  by_cases kind : pointerValue delivered = true
                  · cases set : setPointerIn name delivered scopes with
                    | some updated =>
                        simp only [deliver, found, kind, set, if_true]
                        exact .pointer name old delivered updated resolved kind set
                    | none =>
                        simp only [deliver, found, kind, set, if_true]
                        exact .pointerMissing name old delivered resolved kind set
                  · have unkind : pointerValue delivered = false := by simpa using kind
                    simp only [deliver, found, unkind]
                    exact .pointerKind name old delivered resolved unkind

theorem advance_sound_execute (choice : Choice) (c : Executable model) (top : Activation model)
    (callers : List (Activation model)) (statement : Statement model) (next : Executable model)
    (running : c.status = .running) (stack : c.stack = top :: callers)
    (control : top.control = .execute statement)
    (stepped : advance model policy abi program choice c top callers = some next) :
    Step model policy abi program c.represent next.represent := by
  have memoryEq : c.represent.memory = ObjectAccessMemory.represent c.memory := rfl
  have arraysEq : c.represent.arrays = c.arrays := rfl
  have heapEq : c.represent.heap = c.heap := rfl
  have runningR : c.represent.status = .running := running
  have stackR : c.represent.stack = top :: callers := stack
  rcases top with ⟨scopes, topControl, continuation⟩
  simp only at control
  subst control
  cases statement with
  | skip =>
      simp only [advance, Configuration.continueWith, Option.some.injEq] at stepped
      subst stepped
      exact .skip _ _ _ runningR stackR rfl
  | assign place value =>
      have located := locate_sound model policy c.memory c.arrays scopes place
      have evaluated := evaluate_sound model policy c.memory c.arrays scopes value
      cases found : locate model policy c.memory c.arrays scopes place with
      | error reason =>
          simp only [advance, found, Configuration.fail, Option.some.injEq] at stepped
          subst stepped
          rw [found] at located
          exact .assignPlaceFault _ _ _ place value reason runningR stackR rfl located
      | ok target =>
          rw [found] at located
          cases result : evaluate model policy c.memory c.arrays scopes value with
          | fault reason =>
              simp only [advance, found, result, Configuration.fail, Option.some.injEq] at stepped
              subst stepped
              rw [result] at evaluated
              exact .assignValueFault _ _ _ place value target reason runningR stackR rfl located evaluated
          | value delivered =>
              rw [result] at evaluated
              cases delivered with
              | integer scalar =>
                  have storing := storeElement_sound model policy c.memory c.arrays target scalar
                  cases stored : storeElement model policy c.memory c.arrays target scalar with
                  | done saved =>
                      simp only [advance, found, result, stored, Option.some.injEq] at stepped
                      subst stepped
                      rw [stored] at storing
                      exact .assign _ _ _ place value target scalar _ runningR stackR rfl located evaluated storing
                  | fault reason =>
                      simp only [advance, found, result, stored, Configuration.fail, Option.some.injEq] at stepped
                      subst stepped
                      rw [stored] at storing
                      exact .assignStoreFault _ _ _ place value target scalar reason runningR stackR rfl
                        located evaluated storing
              | address pointer =>
                  simp only [advance, found, result, Configuration.fail, Option.some.injEq] at stepped
                  subst stepped
                  exact .assignKind _ _ _ place value target _ runningR stackR rfl located evaluated rfl
              | null =>
                  simp only [advance, found, result, Configuration.fail, Option.some.injEq] at stepped
                  subst stepped
                  exact .assignKind _ _ _ place value target _ runningR stackR rfl located evaluated rfl
  | setPointer name value =>
      have evaluated := evaluate_sound model policy c.memory c.arrays scopes value
      cases result : evaluate model policy c.memory c.arrays scopes value with
      | fault reason =>
          simp only [advance, result, Configuration.fail, Option.some.injEq] at stepped
          subst stepped
          rw [result] at evaluated
          exact .setPointerFault _ _ _ name value reason runningR stackR rfl evaluated
      | value delivered =>
          rw [result] at evaluated
          by_cases kind : pointerValue delivered = true
          · cases set : setPointerIn name delivered scopes with
            | some updated =>
                simp only [advance, result, kind, set, if_true, Configuration.continueWith,
                  Option.some.injEq] at stepped
                subst stepped
                exact .setPointer _ _ _ name value delivered updated runningR stackR rfl evaluated kind set
            | none =>
                simp only [advance, result, kind, set, if_true, Configuration.fail, Option.some.injEq] at stepped
                subst stepped
                exact .setPointerMissing _ _ _ name value delivered runningR stackR rfl evaluated kind set
          · have unkind : pointerValue delivered = false := by simpa using kind
            simp only [advance, result, unkind, Bool.false_eq_true, if_false, Configuration.fail,
              Option.some.injEq] at stepped
            subst stepped
            exact .setPointerKind _ _ _ name value delivered runningR stackR rfl evaluated unkind
  | call result function arguments =>
      have evaluated := argumentValues_sound model policy c.memory c.arrays scopes arguments
      cases values : argumentValues (arguments.map (evaluate model policy c.memory c.arrays scopes)) with
      | error reason =>
          simp only [advance, values, Configuration.fail, Option.some.injEq] at stepped
          subst stepped
          exact .callFault _ _ _ result function arguments _ reason runningR stackR rfl evaluated values
      | ok delivered =>
          cases known : program.lookup function with
          | none =>
              simp only [advance, values, known, Configuration.fail, Option.some.injEq] at stepped
              subst stepped
              exact .callUnknown _ _ _ result function arguments _ delivered runningR stackR rfl evaluated values known
          | some definition =>
              cases bound : bindParameters definition.parameters delivered with
              | none =>
                  simp only [advance, values, known, bound, Configuration.fail, Option.some.injEq] at stepped
                  subst stepped
                  exact .callArity _ _ _ result function arguments _ delivered definition runningR stackR rfl
                    evaluated values known bound
              | some pending =>
                  simp only [advance, values, known, bound, Option.some.injEq] at stepped
                  subst stepped
                  exact .call _ _ _ result function arguments _ delivered definition pending runningR stackR rfl
                    evaluated values known bound
  | external result service arguments =>
      have evaluated := argumentValues_sound model policy c.memory c.arrays scopes arguments
      cases values : argumentValues (arguments.map (evaluate model policy c.memory c.arrays scopes)) with
      | error reason =>
          simp only [advance, values, Configuration.fail, Option.some.injEq] at stepped
          subst stepped
          exact .externalFault _ _ _ result service arguments _ reason runningR stackR rfl evaluated values
      | ok delivered =>
          simp only [advance, values, Option.some.injEq] at stepped
          subst stepped
          exact .external _ _ _ result service arguments _ delivered runningR stackR rfl evaluated values
  | allocate name type count =>
      have evaluated := evaluate_sound model policy c.memory c.arrays scopes count
      cases result : evaluate model policy c.memory c.arrays scopes count with
      | fault reason =>
          simp only [advance, result, Configuration.fail, Option.some.injEq] at stepped
          subst stepped
          rw [result] at evaluated
          exact .allocateFault _ _ _ name type count reason runningR stackR rfl evaluated
      | value delivered =>
          rw [result] at evaluated
          cases delivered with
          | integer amount =>
              by_cases admitted : 0 < amount.integer.value.toNat ∧ choice.allocationSucceeds = true
              · cases created : IntegerObjectConstruction.construct model c.memory c.arrays
                    ⟨name, type, .array amount.integer.value.toNat admitted.1⟩ (abi type) choice.identity
                    .indeterminate with
                | none =>
                    simp only [advance, result, admitted, created] at stepped
                    cases stepped
                | some made =>
                    have creation := IntegerObjectConstruction.construct_sound _ _ _ _ _ _ _ _ created
                    cases set : setPointerIn name (.address ⟨type, ⟨choice.identity, 0⟩⟩) scopes with
                    | some updated =>
                        simp only [advance, result, admitted, created, set, and_self, dite_true,
                          Option.some.injEq] at stepped
                        subst stepped
                        exact .allocate _ _ _ name type count amount admitted.1 choice.identity _ _ _ updated
                          runningR stackR rfl evaluated creation set
                    | none =>
                        simp only [advance, result, admitted, created, set, and_self, dite_true,
                          Configuration.fail, Option.some.injEq] at stepped
                        subst stepped
                        exact .allocateUnbound _ _ _ name type count amount admitted.1 choice.identity _ _ _
                          runningR stackR rfl evaluated creation set
              · cases set : setPointerIn name .null scopes with
                | some updated =>
                    simp only [advance, result, admitted, set, dite_false, Configuration.continueWith,
                      Option.some.injEq] at stepped
                    subst stepped
                    exact .allocateNull _ _ _ name type count amount updated runningR stackR rfl evaluated set
                | none =>
                    simp only [advance, result, admitted, set, dite_false, Configuration.fail,
                      Option.some.injEq] at stepped
                    subst stepped
                    exact .allocateNullUnbound _ _ _ name type count amount runningR stackR rfl evaluated set
          | address pointer =>
              simp only [advance, result, Configuration.fail, Option.some.injEq] at stepped
              subst stepped
              exact .allocateKind _ _ _ name type count _ runningR stackR rfl evaluated rfl
          | null =>
              simp only [advance, result, Configuration.fail, Option.some.injEq] at stepped
              subst stepped
              exact .allocateKind _ _ _ name type count _ runningR stackR rfl evaluated rfl
  | release pointer =>
      have evaluated := evaluate_sound model policy c.memory c.arrays scopes pointer
      cases result : evaluate model policy c.memory c.arrays scopes pointer with
      | fault reason =>
          simp only [advance, result, Configuration.fail, Option.some.injEq] at stepped
          subst stepped
          rw [result] at evaluated
          exact .releaseFault _ _ _ pointer reason runningR stackR rfl evaluated
      | value delivered =>
          rw [result] at evaluated
          cases delivered with
          | null =>
              simp only [advance, result, Configuration.continueWith, Option.some.injEq] at stepped
              subst stepped
              exact .releaseNull _ _ _ pointer runningR stackR rfl evaluated
          | integer scalar =>
              simp only [advance, result, Configuration.fail, Option.some.injEq] at stepped
              subst stepped
              exact .releaseKind _ _ _ pointer scalar runningR stackR rfl evaluated
          | address target =>
              by_cases valid : target.pointer.index = 0 ∧ target.pointer.object ∈ c.heap
              · cases retired : AutomaticObjectScopes.retireStorage c.memory.storage target.pointer.object with
                | some storage =>
                    simp only [advance, result, valid, retired, and_self, if_true, Option.some.injEq] at stepped
                    subst stepped
                    exact .release _ _ _ pointer target _ runningR stackR rfl evaluated valid.1 valid.2
                      (AutomaticObjectScopes.retireStorage_sound _ _ _ retired)
                | none =>
                    simp only [advance, result, valid, retired, and_self, if_true, Configuration.fail,
                      Option.some.injEq] at stepped
                    subst stepped
                    refine .releaseRefused _ _ _ pointer target runningR stackR rfl evaluated valid.1 valid.2 ?_
                    rintro ⟨after, retirement⟩
                    obtain ⟨saved, computed, _⟩ := AutomaticObjectScopes.retireStorage_complete _ _ _ retirement
                    rw [computed] at retired
                    cases retired
              · simp only [advance, result, valid, if_false, Configuration.fail, Option.some.injEq] at stepped
                subst stepped
                exact .releaseInvalid _ _ _ pointer target runningR stackR rfl evaluated valid
  | sequence first second =>
      simp only [advance, Configuration.continueWith, Option.some.injEq] at stepped
      subst stepped
      exact .sequence _ _ _ first second runningR stackR rfl
  | block declarations body =>
      simp only [advance, Configuration.continueWith, Option.some.injEq] at stepped
      subst stepped
      exact .block _ _ _ declarations body runningR stackR rfl
  | conditional condition yes no =>
      have evaluated := evaluate_sound model policy c.memory c.arrays scopes condition
      cases result : evaluate model policy c.memory c.arrays scopes condition with
      | fault reason =>
          simp only [advance, result, Configuration.fail, Option.some.injEq] at stepped
          subst stepped
          rw [result] at evaluated
          exact .conditionalFault _ _ _ condition yes no reason runningR stackR rfl evaluated
      | value delivered =>
          rw [result] at evaluated
          cases delivered with
          | integer test =>
              simp only [advance, result, Configuration.continueWith, Option.some.injEq] at stepped
              subst stepped
              exact .conditional _ _ _ condition yes no test runningR stackR rfl evaluated
          | address pointer =>
              simp only [advance, result, Configuration.fail, Option.some.injEq] at stepped
              subst stepped
              exact .conditionalKind _ _ _ condition yes no _ runningR stackR rfl evaluated rfl
          | null =>
              simp only [advance, result, Configuration.fail, Option.some.injEq] at stepped
              subst stepped
              exact .conditionalKind _ _ _ condition yes no _ runningR stackR rfl evaluated rfl
  | whileLoop condition body =>
      have evaluated := evaluate_sound model policy c.memory c.arrays scopes condition
      cases result : evaluate model policy c.memory c.arrays scopes condition with
      | fault reason =>
          simp only [advance, result, Configuration.fail, Option.some.injEq] at stepped
          subst stepped
          rw [result] at evaluated
          exact .whileFault _ _ _ condition body reason runningR stackR rfl evaluated
      | value delivered =>
          rw [result] at evaluated
          cases delivered with
          | integer test =>
              cases holds : IntegerScalar.truth test with
              | true =>
                  simp only [advance, result, holds, if_true, Configuration.continueWith,
                    Option.some.injEq] at stepped
                  subst stepped
                  exact .whileTrue _ _ _ condition body test runningR stackR rfl evaluated holds
              | false =>
                  simp only [advance, result, holds, Bool.false_eq_true, if_false, Configuration.continueWith,
                    Option.some.injEq] at stepped
                  subst stepped
                  exact .whileFalse _ _ _ condition body test runningR stackR rfl evaluated holds
          | address pointer =>
              simp only [advance, result, Configuration.fail, Option.some.injEq] at stepped
              subst stepped
              exact .whileKind _ _ _ condition body _ runningR stackR rfl evaluated rfl
          | null =>
              simp only [advance, result, Configuration.fail, Option.some.injEq] at stepped
              subst stepped
              exact .whileKind _ _ _ condition body _ runningR stackR rfl evaluated rfl
  | breakLoop =>
      simp only [advance, Configuration.continueWith, Option.some.injEq] at stepped
      subst stepped
      exact .breakLoop _ _ _ runningR stackR rfl
  | continueLoop =>
      simp only [advance, Configuration.continueWith, Option.some.injEq] at stepped
      subst stepped
      exact .continueLoop _ _ _ runningR stackR rfl
  | returnValue value =>
      cases value with
      | none =>
          simp only [advance, Configuration.continueWith, Option.some.injEq] at stepped
          subst stepped
          exact .returnNone _ _ _ runningR stackR rfl
      | some value =>
          have evaluated := evaluate_sound model policy c.memory c.arrays scopes value
          cases result : evaluate model policy c.memory c.arrays scopes value with
          | fault reason =>
              simp only [advance, result, Configuration.fail, Option.some.injEq] at stepped
              subst stepped
              rw [result] at evaluated
              exact .returnFault _ _ _ value reason runningR stackR rfl evaluated
          | value returned =>
              simp only [advance, result, Configuration.continueWith, Option.some.injEq] at stepped
              subst stepped
              rw [result] at evaluated
              exact .returnValue _ _ _ value returned runningR stackR rfl evaluated

theorem advance_sound (choice : Choice) (c : Executable model) (top : Activation model)
    (callers : List (Activation model)) (next : Executable model)
    (running : c.status = .running) (stack : c.stack = top :: callers)
    (stepped : advance model policy abi program choice c top callers = some next) :
    Step model policy abi program c.represent next.represent := by
  have runningR : c.represent.status = .running := running
  have stackR : c.represent.stack = top :: callers := stack
  rcases top with ⟨scopes, control, continuation⟩
  cases control with
  | execute statement =>
      exact advance_sound_execute model policy abi program choice c _ callers statement next running stack rfl stepped
  | declaring declarations body =>
      cases declarations with
      | nil =>
          simp only [advance, Configuration.continueWith, Option.some.injEq] at stepped
          subst stepped
          exact .declaringDone _ _ _ body runningR stackR rfl
      | cons declaration rest =>
          cases scopes with
          | nil => cases declaration <;> simp [advance] at stepped
          | cons head tail =>
              by_cases redeclared : head.declares declaration.name = true
              · cases declaration with
                | object object initializer =>
                    simp only [Declaration.name] at redeclared
                    simp only [advance, redeclared, if_true, Configuration.fail, Option.some.injEq] at stepped
                    subst stepped
                    exact .declaringRedeclared _ _ _ (.object object initializer) rest body head tail object.name
                      runningR stackR rfl rfl rfl redeclared
                | pointer name initializer =>
                    simp only [Declaration.name] at redeclared
                    simp only [advance, redeclared, if_true, Configuration.fail, Option.some.injEq] at stepped
                    subst stepped
                    exact .declaringRedeclared _ _ _ (.pointer name initializer) rest body head tail name
                      runningR stackR rfl rfl rfl redeclared
              · have fresh : head.declares declaration.name = false := by simpa using redeclared
                cases declaration with
                | object object initializer =>
                    simp only [Declaration.name] at fresh
                    cases declared : declareObject model c.memory c.arrays (head :: tail) object
                        (abi object.integer) choice.identity with
                    | none =>
                        simp only [advance, fresh, declared, Bool.false_eq_true, if_false] at stepped
                        cases stepped
                    | some triple =>
                        obtain ⟨saved, nextArrays, nextScopes⟩ := triple
                        have declaration := declareObject_sound model c.memory c.arrays (head :: tail) object
                          (abi object.integer) choice.identity saved nextArrays nextScopes declared
                        cases initializer with
                        | none =>
                            simp only [advance, fresh, declared, Bool.false_eq_true, if_false,
                              Option.some.injEq] at stepped
                            subst stepped
                            exact .declaringObject _ _ _ object rest body head tail choice.identity _ nextArrays
                              nextScopes runningR stackR rfl rfl fresh declaration
                        | some value =>
                            cases shape : object.shape with
                            | array count positive =>
                                simp only [advance, fresh, declared, shape, Bool.false_eq_true, if_false,
                                  Configuration.fail, Option.some.injEq] at stepped
                                subst stepped
                                exact .declaringArrayInitializer _ _ _ object value rest body head tail choice.identity
                                  _ nextArrays nextScopes count positive runningR stackR rfl rfl fresh declaration shape
                            | scalar =>
                                have evaluated := evaluate_sound model policy saved nextArrays nextScopes value
                                cases result : evaluate model policy saved nextArrays nextScopes value with
                                | fault reason =>
                                    simp only [advance, fresh, declared, shape, result, Bool.false_eq_true, if_false,
                                      Configuration.fail, Option.some.injEq] at stepped
                                    subst stepped
                                    rw [result] at evaluated
                                    exact .declaringInitializerFault _ _ _ object value rest body head tail
                                      choice.identity _ nextArrays nextScopes reason runningR stackR rfl rfl fresh
                                      declaration shape evaluated
                                | value delivered =>
                                    rw [result] at evaluated
                                    cases delivered with
                                    | integer initial =>
                                        have storing := storeElement_sound model policy saved nextArrays
                                          ⟨object.integer, ⟨choice.identity, 0⟩⟩ initial
                                        cases stored : storeElement model policy saved nextArrays
                                            ⟨object.integer, ⟨choice.identity, 0⟩⟩ initial with
                                        | done storedMemory =>
                                            simp only [advance, fresh, declared, shape, result, stored,
                                              Bool.false_eq_true, if_false, Option.some.injEq] at stepped
                                            subst stepped
                                            rw [stored] at storing
                                            exact .declaringInitialized _ _ _ object value rest body head tail
                                              choice.identity _ nextArrays nextScopes initial _ runningR stackR rfl rfl
                                              fresh declaration shape evaluated storing
                                        | fault reason =>
                                            simp only [advance, fresh, declared, shape, result, stored,
                                              Bool.false_eq_true, if_false, Configuration.fail,
                                              Option.some.injEq] at stepped
                                            subst stepped
                                            rw [stored] at storing
                                            exact .declaringInitializerStoreFault _ _ _ object value rest body head
                                              tail choice.identity _ nextArrays nextScopes initial reason runningR
                                              stackR rfl rfl fresh declaration shape evaluated storing
                                    | address pointer =>
                                        simp only [advance, fresh, declared, shape, result, Bool.false_eq_true,
                                          if_false, Configuration.fail, Option.some.injEq] at stepped
                                        subst stepped
                                        exact .declaringInitializerKind _ _ _ object value rest body head tail
                                          choice.identity _ nextArrays nextScopes _ runningR stackR rfl rfl fresh
                                          declaration shape evaluated rfl
                                    | null =>
                                        simp only [advance, fresh, declared, shape, result, Bool.false_eq_true,
                                          if_false, Configuration.fail, Option.some.injEq] at stepped
                                        subst stepped
                                        exact .declaringInitializerKind _ _ _ object value rest body head tail
                                          choice.identity _ nextArrays nextScopes _ runningR stackR rfl rfl fresh
                                          declaration shape evaluated rfl
                | pointer name initializer =>
                    simp only [Declaration.name] at fresh
                    cases initializer with
                    | none =>
                        simp only [advance, fresh, Bool.false_eq_true, if_false, Configuration.continueWith,
                          Option.some.injEq] at stepped
                        subst stepped
                        exact .declaringPointer _ _ _ name rest body head tail runningR stackR rfl rfl fresh
                    | some value =>
                        have evaluated := evaluate_sound model policy c.memory c.arrays
                          (head.bindPointer name none :: tail) value
                        cases result : evaluate model policy c.memory c.arrays (head.bindPointer name none :: tail)
                            value with
                        | fault reason =>
                            simp only [advance, fresh, result, Bool.false_eq_true, if_false, Configuration.fail,
                              Option.some.injEq] at stepped
                            subst stepped
                            rw [result] at evaluated
                            exact .declaringPointerFault _ _ _ name value rest body head tail reason runningR stackR
                              rfl rfl fresh evaluated
                        | value delivered =>
                            rw [result] at evaluated
                            by_cases kind : pointerValue delivered = true
                            · simp only [advance, fresh, result, kind, Bool.false_eq_true, if_false, if_true,
                                Configuration.continueWith, Option.some.injEq] at stepped
                              subst stepped
                              exact .declaringPointerInitialized _ _ _ name value rest body head tail delivered
                                runningR stackR rfl rfl fresh evaluated kind
                            · have unkind : pointerValue delivered = false := by simpa using kind
                              simp only [advance, fresh, result, unkind, Bool.false_eq_true, if_false,
                                Configuration.fail, Option.some.injEq] at stepped
                              subst stepped
                              exact .declaringPointerKind _ _ _ name value rest body head tail delivered
                                runningR stackR rfl rfl fresh evaluated unkind
  | binding pending body =>
      cases pending with
      | nil =>
          simp only [advance, Configuration.continueWith, Option.some.injEq] at stepped
          subst stepped
          exact .bindingDone _ _ _ body runningR stackR rfl
      | cons first rest =>
          obtain ⟨parameter, delivered⟩ := first
          cases parameter with
          | integer name type =>
              cases delivered with
              | integer scalar =>
                  cases scopes with
                  | nil => simp [advance] at stepped
                  | cons head tail =>
                      by_cases redeclared : head.declares name = true
                      · simp only [advance, redeclared, if_true, Configuration.fail, Option.some.injEq] at stepped
                        subst stepped
                        exact .bindingRedeclared _ _ _ (.integer name type) (.integer scalar) rest body head tail name
                          runningR stackR rfl rfl rfl rfl redeclared
                      · have fresh : head.declares name = false := by simpa using redeclared
                        cases declared : declareObject model c.memory c.arrays (head :: tail)
                            (scalarDeclaration name type) (abi type) choice.identity with
                        | none =>
                            simp only [advance, fresh, declared, Bool.false_eq_true, if_false] at stepped
                            cases stepped
                        | some triple =>
                            obtain ⟨saved, nextArrays, nextScopes⟩ := triple
                            have declaration := declareObject_sound model c.memory c.arrays (head :: tail)
                              (scalarDeclaration name type) (abi type) choice.identity saved nextArrays nextScopes
                              declared
                            have storing := storeElement_sound model policy saved nextArrays
                              ⟨type, ⟨choice.identity, 0⟩⟩ scalar
                            cases stored : storeElement model policy saved nextArrays
                                ⟨type, ⟨choice.identity, 0⟩⟩ scalar with
                            | done storedMemory =>
                                simp only [advance, fresh, declared, stored, Bool.false_eq_true, if_false,
                                  Option.some.injEq] at stepped
                                subst stepped
                                rw [stored] at storing
                                exact .bindingInteger _ _ _ name type scalar rest body head tail choice.identity _
                                  nextArrays nextScopes _ runningR stackR rfl rfl fresh declaration storing
                            | fault reason =>
                                simp only [advance, fresh, declared, stored, Bool.false_eq_true, if_false,
                                  Configuration.fail, Option.some.injEq] at stepped
                                subst stepped
                                rw [stored] at storing
                                exact .bindingIntegerFault _ _ _ name type scalar rest body head tail choice.identity _
                                  nextArrays nextScopes reason runningR stackR rfl rfl fresh declaration storing
              | address pointer =>
                  simp only [advance, Configuration.fail, Option.some.injEq] at stepped
                  subst stepped
                  exact .bindingMismatch _ _ _ name type _ rest body runningR stackR rfl rfl
              | null =>
                  simp only [advance, Configuration.fail, Option.some.injEq] at stepped
                  subst stepped
                  exact .bindingMismatch _ _ _ name type _ rest body runningR stackR rfl rfl
          | pointer name =>
              cases scopes with
              | nil => simp [advance] at stepped
              | cons head tail =>
                  by_cases redeclared : head.declares name = true
                  · simp only [advance, redeclared, if_true, Configuration.fail, Option.some.injEq] at stepped
                    subst stepped
                    exact .bindingRedeclared _ _ _ (.pointer name) delivered rest body head tail name
                      runningR stackR rfl rfl rfl rfl redeclared
                  · have fresh : head.declares name = false := by simpa using redeclared
                    simp only [advance, fresh, Bool.false_eq_true, if_false, Configuration.continueWith,
                      Option.some.injEq] at stepped
                    subst stepped
                    exact .bindingPointer _ _ _ name delivered rest body head tail runningR stackR rfl rfl fresh
  | flow flow =>
      cases continuation with
      | stop =>
          cases flow with
          | normal =>
              simp only [advance, Configuration.continueWith, Option.some.injEq] at stepped
              subst stepped
              exact .fallsOff _ _ _ runningR stackR rfl rfl
          | broken =>
              simp only [advance, Configuration.fail, Option.some.injEq] at stepped
              subst stepped
              exact .strayJump _ _ _ .broken runningR stackR rfl (by decide) rfl
          | continued =>
              simp only [advance, Configuration.fail, Option.some.injEq] at stepped
              subst stepped
              exact .strayJump _ _ _ .continued runningR stackR rfl (by decide) rfl
      | sequence statement outer =>
          cases flow with
          | normal =>
              simp only [advance, Configuration.continueWith, Option.some.injEq] at stepped
              subst stepped
              exact .next _ _ _ statement outer runningR stackR rfl rfl
          | broken =>
              simp only [advance, Configuration.continueWith, Option.some.injEq] at stepped
              subst stepped
              exact .skipNext _ _ _ .broken statement outer runningR stackR rfl (by decide) rfl
          | continued =>
              simp only [advance, Configuration.continueWith, Option.some.injEq] at stepped
              subst stepped
              exact .skipNext _ _ _ .continued statement outer runningR stackR rfl (by decide) rfl
      | loop condition body outer =>
          cases flow with
          | broken =>
              simp only [advance, Configuration.continueWith, Option.some.injEq] at stepped
              subst stepped
              exact .exitLoop _ _ _ condition body outer runningR stackR rfl rfl
          | normal =>
              simp only [advance, Configuration.continueWith, Option.some.injEq] at stepped
              subst stepped
              exact .iterate _ _ _ .normal condition body outer runningR stackR rfl (by decide) rfl
          | continued =>
              simp only [advance, Configuration.continueWith, Option.some.injEq] at stepped
              subst stepped
              exact .iterate _ _ _ .continued condition body outer runningR stackR rfl (by decide) rfl
      | scope outer =>
          cases left : leaveScope model c.memory scopes with
          | none =>
              simp only [advance, left] at stepped
              cases flow <;> cases stepped
          | some pair =>
              obtain ⟨saved, rest⟩ := pair
              have leaving := leaveScope_sound model c.memory scopes saved rest left
              cases flow <;>
                (simp only [advance, left, Option.some.injEq] at stepped
                 subst stepped
                 exact .leave _ _ _ _ outer _ rest runningR stackR rfl rfl leaving)
  | returning value =>
      cases continuation with
      | scope outer =>
          cases left : leaveScope model c.memory scopes with
          | none =>
              simp only [advance, left] at stepped
              cases stepped
          | some pair =>
              obtain ⟨saved, rest⟩ := pair
              have leaving := leaveScope_sound model c.memory scopes saved rest left
              simp only [advance, left, Option.some.injEq] at stepped
              subst stepped
              exact .returnLeave _ _ _ value outer _ rest runningR stackR rfl rfl leaving
      | sequence statement outer =>
          simp only [advance, Configuration.continueWith, Option.some.injEq] at stepped
          subst stepped
          exact .returnSkip _ _ _ value statement outer runningR stackR rfl rfl
      | loop condition body outer =>
          simp only [advance, Configuration.continueWith, Option.some.injEq] at stepped
          subst stepped
          exact .returnExitLoop _ _ _ value condition body outer runningR stackR rfl rfl
      | stop =>
          cases callers with
          | nil =>
              simp only [advance, Option.some.injEq] at stepped
              subst stepped
              exact .finish _ _ value runningR stackR rfl rfl
          | cons caller rest =>
              rcases caller with ⟨callerScopes, callerControl, callerContinuation⟩
              cases callerControl with
              | awaiting result =>
                  have delivering := deliver_sound model policy c.memory c.arrays callerScopes result value
                  cases delivered : deliver model policy c.memory c.arrays callerScopes result value with
                  | done pair =>
                      obtain ⟨saved, updated⟩ := pair
                      simp only [advance, delivered, Option.some.injEq] at stepped
                      subst stepped
                      rw [delivered] at delivering
                      exact .deliver _ _ _ rest value result _ updated runningR stackR rfl rfl rfl delivering
                  | fault reason =>
                      simp only [advance, delivered, Configuration.fail, Option.some.injEq] at stepped
                      subst stepped
                      rw [delivered] at delivering
                      exact .deliverFault _ _ _ rest value result reason runningR stackR rfl rfl rfl delivering
              | execute _ | declaring _ _ | binding _ _ | flow _ | returning _ =>
                  simp [advance] at stepped
  | awaiting result => simp [advance] at stepped

/-- **Soundness**: every executable step, under any choice, is an independent step. -/
theorem step_sound (choice : Choice) (c next : Executable model)
    (stepped : step model policy abi program choice c = some next) :
    Step model policy abi program c.represent next.represent := by
  rcases c with ⟨memory, arrays, heap, stack, status⟩
  cases status with
  | running =>
      cases stack with
      | nil => simp [step] at stepped
      | cons top callers =>
          exact advance_sound model policy abi program choice _ top callers next rfl rfl stepped
  | waiting _ _ => simp [step] at stepped
  | finished _ => simp [step] at stepped
  | faulted _ => simp [step] at stepped

end Soundness

/-! ## Completeness of the executable step -/

section Completeness

variable (model : Model) (policy : SignedConversionPolicy) (abi : IntegerType IntegerExtension → ObjectLayout.Layout)
  (program : Program model)

theorem Effect.represent_done {memory : State model.characters} {arrays : ArrayPointers.Catalog} {target : Address}
    {value : IntegerScalar.Value model.parameters} {after : SemanticState model.characters}
    (computed : (storeElement model policy memory arrays target value).represent = .done after) :
    ∃ saved, storeElement model policy memory arrays target value = .done saved ∧
      ObjectAccessMemory.represent saved = after := by
  cases stored : storeElement model policy memory arrays target value with
  | done saved =>
      rw [stored] at computed
      cases computed
      exact ⟨saved, rfl, rfl⟩
  | fault reason => rw [stored] at computed; cases computed

theorem Effect.represent_fault {memory : State model.characters} {arrays : ArrayPointers.Catalog} {target : Address}
    {value : IntegerScalar.Value model.parameters} {reason : Fault model}
    (computed : (storeElement model policy memory arrays target value).represent = .fault reason) :
    storeElement model policy memory arrays target value = .fault reason := by
  cases stored : storeElement model policy memory arrays target value with
  | done saved => rw [stored] at computed; cases computed
  | fault other => rw [stored] at computed; cases computed; rfl

theorem argumentValues_complete (memory : State model.characters) (arrays : ArrayPointers.Catalog)
    (scopes : List (Scope model)) {arguments : List (Expression model)} {results : List (Result model)}
    (evaluated : List.Forall₂ (Evaluates model policy (ObjectAccessMemory.represent memory) arrays scopes)
      arguments results) :
    arguments.map (evaluate model policy memory arrays scopes) = results := by
  induction evaluated with
  | nil => rfl
  | cons head _ ih => simp [evaluate_complete model policy memory arrays scopes head, ih]

theorem deliver_complete (memory : State model.characters) (arrays : ArrayPointers.Catalog)
    (scopes : List (Scope model)) (result : Option String) (value : Option (Value model))
    (effect : Effect model (SemanticState model.characters × List (Scope model)))
    (delivering : Delivers model policy (ObjectAccessMemory.represent memory) arrays scopes result value effect) :
    (match deliver model policy memory arrays scopes result value with
      | .done (saved, updated) => Effect.done (ObjectAccessMemory.represent saved, updated)
      | .fault reason => .fault reason) = effect := by
  have sound := deliver_sound model policy memory arrays scopes result value
  -- The independent outcome is unique, so it equals the sound one.
  cases delivering with
  | discard value => rfl
  | missing name => rfl
  | object name location target scalar after resolved typed storing =>
      have computed := storeElement_complete model policy memory arrays target scalar _ storing
      obtain ⟨saved, stored, represented⟩ := Effect.represent_done model policy computed
      simp [deliver, resolve_complete _ _ _ resolved, typed, stored, represented]
  | objectFault name location target scalar reason resolved typed storing =>
      have computed := storeElement_complete model policy memory arrays target scalar _ storing
      have stored := Effect.represent_fault model policy computed
      simp [deliver, resolve_complete _ _ _ resolved, typed, stored]
  | objectKind name location delivered resolved mismatch =>
      cases typed : rootAddress location with
      | none => simp [deliver, resolve_complete _ _ _ resolved, typed]
      | some target =>
          cases delivered with
          | integer scalar => exact absurd rfl (mismatch target scalar typed)
          | address _ => simp [deliver, resolve_complete _ _ _ resolved, typed]
          | null => simp [deliver, resolve_complete _ _ _ resolved, typed]
  | pointer name old delivered updated resolved kind set =>
      simp [deliver, resolve_complete _ _ _ resolved, kind, set]
  | pointerMissing name old delivered resolved kind set =>
      simp [deliver, resolve_complete _ _ _ resolved, kind, set]
  | pointerKind name old delivered resolved kind =>
      simp [deliver, resolve_complete _ _ _ resolved, kind]
  | unbound name delivered absent =>
      simp [deliver, (resolve_none_iff scopes name).mpr absent]

theorem step_eq_advance (choice : Choice) (c : Executable model) (top : Activation model)
    (callers : List (Activation model)) (running : c.status = .running) (stack : c.stack = top :: callers) :
    step model policy abi program choice c = advance model policy abi program choice c top callers := by
  simp [step, running, stack]

/-- **Completeness**: every independent step is the executable step under some
choice of new identities and allocation success. -/
theorem step_complete (c : Executable model) (target : Semantic model)
    (stepping : Step model policy abi program c.represent target) :
    ∃ choice next, step model policy abi program choice c = some next ∧ next.represent = target := by
  rcases c with ⟨memory, arrays, heap, frames, status⟩
  cases stepping with
  | skip top callers running stack control =>
      refine ⟨⟨0, true⟩, { (⟨memory, arrays, heap, frames, status⟩ : Executable model) with
          stack := { top with control := .flow .normal } :: callers }, ?_, ?_⟩
      · rw [step_eq_advance model policy abi program _ _ top callers running stack]
        rcases top with ⟨scopes, control', continuation⟩
        simp only at control; subst control
        rfl
      · rfl
  | assignPlaceFault top callers place value reason running stack control located =>
      refine ⟨⟨0, true⟩, { (⟨memory, arrays, heap, frames, status⟩ : Executable model) with
          status := .faulted reason }, ?_, ?_⟩
      · rw [step_eq_advance model policy abi program _ _ top callers running stack]
        rcases top with ⟨scopes, control', continuation⟩
        simp only at control; subst control
        simp only [advance, locate_complete model policy memory arrays scopes located, Configuration.fail]
      · rfl
  | assignValueFault top callers place value target reason running stack control located evaluated =>
      refine ⟨⟨0, true⟩, { (⟨memory, arrays, heap, frames, status⟩ : Executable model) with
          status := .faulted reason }, ?_, ?_⟩
      · rw [step_eq_advance model policy abi program _ _ top callers running stack]
        rcases top with ⟨scopes, control', continuation⟩
        simp only at control; subst control
        simp only [advance, locate_complete model policy memory arrays scopes located,
          evaluate_complete model policy memory arrays scopes evaluated, Configuration.fail]
      · rfl
  | assign top callers place value target scalar after running stack control located evaluated storing =>
      obtain ⟨saved, stored, represented⟩ := Effect.represent_done model policy
        (storeElement_complete model policy memory arrays target scalar _ storing)
      refine ⟨⟨0, true⟩, { (⟨memory, arrays, heap, frames, status⟩ : Executable model) with
          memory := saved,
          stack := { top with control := .flow .normal } :: callers }, ?_, ?_⟩
      · rw [step_eq_advance model policy abi program _ _ top callers running stack]
        rcases top with ⟨scopes, control', continuation⟩
        simp only at control; subst control
        simp only [advance, locate_complete model policy memory arrays scopes located,
          evaluate_complete model policy memory arrays scopes evaluated, stored]
      · simp [Configuration.represent, represented]
  | assignStoreFault top callers place value target scalar reason running stack control located evaluated storing =>
      have stored := Effect.represent_fault model policy
        (storeElement_complete model policy memory arrays target scalar _ storing)
      refine ⟨⟨0, true⟩, { (⟨memory, arrays, heap, frames, status⟩ : Executable model) with
          status := .faulted reason }, ?_, ?_⟩
      · rw [step_eq_advance model policy abi program _ _ top callers running stack]
        rcases top with ⟨scopes, control', continuation⟩
        simp only at control; subst control
        simp only [advance, locate_complete model policy memory arrays scopes located,
          evaluate_complete model policy memory arrays scopes evaluated, stored, Configuration.fail]
      · rfl
  | assignKind top callers place value target delivered running stack control located evaluated kind =>
      refine ⟨⟨0, true⟩, { (⟨memory, arrays, heap, frames, status⟩ : Executable model) with
          status := .faulted .constraint }, ?_, ?_⟩
      · rw [step_eq_advance model policy abi program _ _ top callers running stack]
        rcases top with ⟨scopes, control', continuation⟩
        simp only at control; subst control
        cases delivered with
        | integer _ => cases kind
        | address _ =>
          simp only [advance, locate_complete model policy memory arrays scopes located,
            evaluate_complete model policy memory arrays scopes evaluated, Configuration.fail]
        | null =>
          simp only [advance, locate_complete model policy memory arrays scopes located,
            evaluate_complete model policy memory arrays scopes evaluated, Configuration.fail]
      · rfl
  | setPointerFault top callers name value reason running stack control evaluated =>
      refine ⟨⟨0, true⟩, { (⟨memory, arrays, heap, frames, status⟩ : Executable model) with
          status := .faulted reason }, ?_, ?_⟩
      · rw [step_eq_advance model policy abi program _ _ top callers running stack]
        rcases top with ⟨scopes, control', continuation⟩
        simp only at control; subst control
        simp only [advance, evaluate_complete model policy memory arrays scopes evaluated, Configuration.fail]
      · rfl
  | setPointer top callers name value delivered updated running stack control evaluated kind set =>
      refine ⟨⟨0, true⟩, { (⟨memory, arrays, heap, frames, status⟩ : Executable model) with
          stack := { top with scopes := updated, control := .flow .normal } :: callers }, ?_, ?_⟩
      · rw [step_eq_advance model policy abi program _ _ top callers running stack]
        rcases top with ⟨scopes, control', continuation⟩
        simp only at control; subst control
        simp only [advance, evaluate_complete model policy memory arrays scopes evaluated, kind, if_true, set,
          Configuration.continueWith]
      · rfl
  | setPointerMissing top callers name value delivered running stack control evaluated kind set =>
      refine ⟨⟨0, true⟩, { (⟨memory, arrays, heap, frames, status⟩ : Executable model) with
          status := .faulted .constraint }, ?_, ?_⟩
      · rw [step_eq_advance model policy abi program _ _ top callers running stack]
        rcases top with ⟨scopes, control', continuation⟩
        simp only at control; subst control
        simp only [advance, evaluate_complete model policy memory arrays scopes evaluated, kind, if_true, set,
          Configuration.fail]
      · rfl
  | setPointerKind top callers name value delivered running stack control evaluated kind =>
      refine ⟨⟨0, true⟩, { (⟨memory, arrays, heap, frames, status⟩ : Executable model) with
          status := .faulted .constraint }, ?_, ?_⟩
      · rw [step_eq_advance model policy abi program _ _ top callers running stack]
        rcases top with ⟨scopes, control', continuation⟩
        simp only at control; subst control
        simp only [advance, evaluate_complete model policy memory arrays scopes evaluated, kind,
          Bool.false_eq_true, if_false, Configuration.fail]
      · rfl
  | callFault top callers result function arguments results reason running stack control evaluated bad =>
      refine ⟨⟨0, true⟩, { (⟨memory, arrays, heap, frames, status⟩ : Executable model) with
          status := .faulted reason }, ?_, ?_⟩
      · rw [step_eq_advance model policy abi program _ _ top callers running stack]
        rcases top with ⟨scopes, control', continuation⟩
        simp only at control; subst control
        simp only [advance, argumentValues_complete model policy memory arrays scopes evaluated, bad,
          Configuration.fail]
      · rfl
  | callUnknown top callers result function arguments results values running stack control evaluated good unknown =>
      refine ⟨⟨0, true⟩, { (⟨memory, arrays, heap, frames, status⟩ : Executable model) with
          status := .faulted .constraint }, ?_, ?_⟩
      · rw [step_eq_advance model policy abi program _ _ top callers running stack]
        rcases top with ⟨scopes, control', continuation⟩
        simp only at control; subst control
        simp only [advance, argumentValues_complete model policy memory arrays scopes evaluated, good, unknown,
          Configuration.fail]
      · rfl
  | callArity top callers result function arguments results values definition running stack control evaluated
      good known mismatch =>
      refine ⟨⟨0, true⟩, { (⟨memory, arrays, heap, frames, status⟩ : Executable model) with
          status := .faulted .constraint }, ?_, ?_⟩
      · rw [step_eq_advance model policy abi program _ _ top callers running stack]
        rcases top with ⟨scopes, control', continuation⟩
        simp only at control; subst control
        simp only [advance, argumentValues_complete model policy memory arrays scopes evaluated, good, known,
          mismatch, Configuration.fail]
      · rfl
  | call top callers result function arguments results values definition pending running stack control evaluated
      good known bound =>
      refine ⟨⟨0, true⟩, { (⟨memory, arrays, heap, frames, status⟩ : Executable model) with
          stack := ⟨[{}], .binding pending definition.body, .scope .stop⟩ :: { top with control := .awaiting result } :: callers }, ?_, ?_⟩
      · rw [step_eq_advance model policy abi program _ _ top callers running stack]
        rcases top with ⟨scopes, control', continuation⟩
        simp only at control; subst control
        simp only [advance, argumentValues_complete model policy memory arrays scopes evaluated, good, known, bound]
      · rfl
  | externalFault top callers result service arguments results reason running stack control evaluated bad =>
      refine ⟨⟨0, true⟩, { (⟨memory, arrays, heap, frames, status⟩ : Executable model) with
          status := .faulted reason }, ?_, ?_⟩
      · rw [step_eq_advance model policy abi program _ _ top callers running stack]
        rcases top with ⟨scopes, control', continuation⟩
        simp only at control; subst control
        simp only [advance, argumentValues_complete model policy memory arrays scopes evaluated, bad,
          Configuration.fail]
      · rfl
  | external top callers result service arguments results values running stack control evaluated good =>
      refine ⟨⟨0, true⟩, { (⟨memory, arrays, heap, frames, status⟩ : Executable model) with
          status := .waiting service values,
          stack := { top with control := .awaiting result } :: callers }, ?_, ?_⟩
      · rw [step_eq_advance model policy abi program _ _ top callers running stack]
        rcases top with ⟨scopes, control', continuation⟩
        simp only at control; subst control
        simp only [advance, argumentValues_complete model policy memory arrays scopes evaluated, good]
      · rfl
  | allocateFault top callers name type count reason running stack control evaluated =>
      refine ⟨⟨0, true⟩, { (⟨memory, arrays, heap, frames, status⟩ : Executable model) with
          status := .faulted reason }, ?_, ?_⟩
      · rw [step_eq_advance model policy abi program _ _ top callers running stack]
        rcases top with ⟨scopes, control', continuation⟩
        simp only at control; subst control
        simp only [advance, evaluate_complete model policy memory arrays scopes evaluated, Configuration.fail]
      · rfl
  | allocate top callers name type count amount positive identity after nextArrays location updated
      running stack control evaluated creation set =>
      obtain ⟨made, constructed, memoryEq, arraysEq, _⟩ :=
        IntegerObjectConstruction.construct_complete _ _ _ _ _ _ _ _ _ _ creation
      refine ⟨⟨identity, true⟩, { (⟨memory, arrays, heap, frames, status⟩ : Executable model) with
          memory := made.memory,
          arrays := made.arrays,
          heap := identity :: heap,
          stack := { top with scopes := updated, control := .flow .normal } :: callers }, ?_, ?_⟩
      · rw [step_eq_advance model policy abi program _ _ top callers running stack]
        rcases top with ⟨scopes, control', continuation⟩
        simp only at control; subst control
        have admitted : 0 < amount.integer.value.toNat ∧ (⟨identity, true⟩ : Choice).allocationSucceeds = true :=
          ⟨positive, rfl⟩
        dsimp only [Configuration.represent] at constructed
        simp only [advance, evaluate_complete model policy memory arrays scopes evaluated, admitted, and_self, dite_true, constructed, set]
      · simp [Configuration.represent, memoryEq, arraysEq]
  | allocateUnbound top callers name type count amount positive identity after nextArrays location
      running stack control evaluated creation set =>
      obtain ⟨made, constructed, memoryEq, arraysEq, _⟩ :=
        IntegerObjectConstruction.construct_complete _ _ _ _ _ _ _ _ _ _ creation
      refine ⟨⟨identity, true⟩, { (⟨memory, arrays, heap, frames, status⟩ : Executable model) with
          status := .faulted .constraint }, ?_, ?_⟩
      · rw [step_eq_advance model policy abi program _ _ top callers running stack]
        rcases top with ⟨scopes, control', continuation⟩
        simp only at control; subst control
        have admitted : 0 < amount.integer.value.toNat ∧ (⟨identity, true⟩ : Choice).allocationSucceeds = true :=
          ⟨positive, rfl⟩
        dsimp only [Configuration.represent] at constructed
        simp only [advance, evaluate_complete model policy memory arrays scopes evaluated, admitted, and_self, dite_true, constructed, set,
          Configuration.fail]
      · rfl
  | allocateNull top callers name type count amount updated running stack control evaluated set =>
      refine ⟨⟨0, false⟩, { (⟨memory, arrays, heap, frames, status⟩ : Executable model) with
          stack := { top with scopes := updated, control := .flow .normal } :: callers }, ?_, ?_⟩
      · rw [step_eq_advance model policy abi program _ _ top callers running stack]
        rcases top with ⟨scopes, control', continuation⟩
        simp only at control; subst control
        have refused : ¬(0 < amount.integer.value.toNat ∧ (⟨0, false⟩ : Choice).allocationSucceeds = true) := by
          simp
        simp only [advance, evaluate_complete model policy memory arrays scopes evaluated, refused, dite_false, set,
          Configuration.continueWith]
      · rfl
  | allocateNullUnbound top callers name type count amount running stack control evaluated set =>
      refine ⟨⟨0, false⟩, { (⟨memory, arrays, heap, frames, status⟩ : Executable model) with
          status := .faulted .constraint }, ?_, ?_⟩
      · rw [step_eq_advance model policy abi program _ _ top callers running stack]
        rcases top with ⟨scopes, control', continuation⟩
        simp only at control; subst control
        have refused : ¬(0 < amount.integer.value.toNat ∧ (⟨0, false⟩ : Choice).allocationSucceeds = true) := by
          simp
        simp only [advance, evaluate_complete model policy memory arrays scopes evaluated, refused, dite_false, set,
          Configuration.fail]
      · rfl
  | allocateKind top callers name type count delivered running stack control evaluated kind =>
      refine ⟨⟨0, true⟩, { (⟨memory, arrays, heap, frames, status⟩ : Executable model) with
          status := .faulted .constraint }, ?_, ?_⟩
      · rw [step_eq_advance model policy abi program _ _ top callers running stack]
        rcases top with ⟨scopes, control', continuation⟩
        simp only at control; subst control
        cases delivered with
        | integer _ => cases kind
        | address _ => simp only [advance, evaluate_complete model policy memory arrays scopes evaluated, Configuration.fail]
        | null => simp only [advance, evaluate_complete model policy memory arrays scopes evaluated, Configuration.fail]
      · rfl
  | releaseFault top callers pointer reason running stack control evaluated =>
      refine ⟨⟨0, true⟩, { (⟨memory, arrays, heap, frames, status⟩ : Executable model) with
          status := .faulted reason }, ?_, ?_⟩
      · rw [step_eq_advance model policy abi program _ _ top callers running stack]
        rcases top with ⟨scopes, control', continuation⟩
        simp only at control; subst control
        simp only [advance, evaluate_complete model policy memory arrays scopes evaluated, Configuration.fail]
      · rfl
  | releaseNull top callers pointer running stack control evaluated =>
      refine ⟨⟨0, true⟩, { (⟨memory, arrays, heap, frames, status⟩ : Executable model) with
          stack := { top with control := .flow .normal } :: callers }, ?_, ?_⟩
      · rw [step_eq_advance model policy abi program _ _ top callers running stack]
        rcases top with ⟨scopes, control', continuation⟩
        simp only at control; subst control
        simp only [advance, evaluate_complete model policy memory arrays scopes evaluated, Configuration.continueWith]
      · rfl
  | release top callers pointer target after running stack control evaluated start dynamic retired =>
      obtain ⟨storage, freed, heapEq⟩ := AutomaticObjectScopes.retireStorage_complete _ _ _ retired
      refine ⟨⟨0, true⟩, { (⟨memory, arrays, heap, frames, status⟩ : Executable model) with
          memory := ⟨storage, memory.catalog⟩,
          heap := heap.erase target.pointer.object,
          stack := { top with control := .flow .normal } :: callers }, ?_, ?_⟩
      · rw [step_eq_advance model policy abi program _ _ top callers running stack]
        rcases top with ⟨scopes, control', continuation⟩
        simp only at control; subst control
        have valid : target.pointer.index = 0 ∧ target.pointer.object ∈ heap := ⟨start, dynamic⟩
        simp only [advance, evaluate_complete model policy memory arrays scopes evaluated, valid, and_self, if_true, freed]
      · simp [Configuration.represent, ObjectAccessMemory.represent, heapEq]
  | releaseRefused top callers pointer target running stack control evaluated start dynamic refused =>
      refine ⟨⟨0, true⟩, { (⟨memory, arrays, heap, frames, status⟩ : Executable model) with
          status := .faulted .invalidRelease }, ?_, ?_⟩
      · rw [step_eq_advance model policy abi program _ _ top callers running stack]
        rcases top with ⟨scopes, control', continuation⟩
        simp only at control; subst control
        have valid : target.pointer.index = 0 ∧ target.pointer.object ∈ heap := ⟨start, dynamic⟩
        cases freed : AutomaticObjectScopes.retireStorage memory.storage target.pointer.object with
        | some storage => exact absurd ⟨_, AutomaticObjectScopes.retireStorage_sound _ _ _ freed⟩ refused
        | none => simp only [advance, evaluate_complete model policy memory arrays scopes evaluated, valid, and_self, if_true, freed,
            Configuration.fail]
      · rfl
  | releaseInvalid top callers pointer target running stack control evaluated invalid =>
      refine ⟨⟨0, true⟩, { (⟨memory, arrays, heap, frames, status⟩ : Executable model) with
          status := .faulted .invalidRelease }, ?_, ?_⟩
      · rw [step_eq_advance model policy abi program _ _ top callers running stack]
        rcases top with ⟨scopes, control', continuation⟩
        simp only at control; subst control
        have invalid' : ¬(target.pointer.index = 0 ∧ target.pointer.object ∈ heap) := invalid
        simp only [advance, evaluate_complete model policy memory arrays scopes evaluated, invalid', if_false, Configuration.fail]
      · rfl
  | releaseKind top callers pointer scalar running stack control evaluated =>
      refine ⟨⟨0, true⟩, { (⟨memory, arrays, heap, frames, status⟩ : Executable model) with
          status := .faulted .constraint }, ?_, ?_⟩
      · rw [step_eq_advance model policy abi program _ _ top callers running stack]
        rcases top with ⟨scopes, control', continuation⟩
        simp only at control; subst control
        simp only [advance, evaluate_complete model policy memory arrays scopes evaluated, Configuration.fail]
      · rfl
  | sequence top callers first second running stack control =>
      refine ⟨⟨0, true⟩, { (⟨memory, arrays, heap, frames, status⟩ : Executable model) with
          stack := { top with control := .execute first, continuation := .sequence second top.continuation } :: callers }, ?_, ?_⟩
      · rw [step_eq_advance model policy abi program _ _ top callers running stack]
        rcases top with ⟨scopes, control', continuation⟩
        simp only at control; subst control
        rfl
      · rfl
  | block top callers declarations body running stack control =>
      refine ⟨⟨0, true⟩, { (⟨memory, arrays, heap, frames, status⟩ : Executable model) with
          stack := { top with scopes := {} :: top.scopes, control := .declaring declarations body, continuation := .scope top.continuation } :: callers }, ?_, ?_⟩
      · rw [step_eq_advance model policy abi program _ _ top callers running stack]
        rcases top with ⟨scopes, control', continuation⟩
        simp only at control; subst control
        rfl
      · rfl
  | conditionalFault top callers condition yes no reason running stack control evaluated =>
      refine ⟨⟨0, true⟩, { (⟨memory, arrays, heap, frames, status⟩ : Executable model) with
          status := .faulted reason }, ?_, ?_⟩
      · rw [step_eq_advance model policy abi program _ _ top callers running stack]
        rcases top with ⟨scopes, control', continuation⟩
        simp only at control; subst control
        simp only [advance, evaluate_complete model policy memory arrays scopes evaluated, Configuration.fail]
      · rfl
  | conditional top callers condition yes no test running stack control evaluated =>
      refine ⟨⟨0, true⟩, { (⟨memory, arrays, heap, frames, status⟩ : Executable model) with
          stack := { top with control := .execute (if IntegerScalar.truth test then yes else no) } :: callers }, ?_, ?_⟩
      · rw [step_eq_advance model policy abi program _ _ top callers running stack]
        rcases top with ⟨scopes, control', continuation⟩
        simp only at control; subst control
        simp only [advance, evaluate_complete model policy memory arrays scopes evaluated, Configuration.continueWith]
      · rfl
  | conditionalKind top callers condition yes no delivered running stack control evaluated kind =>
      refine ⟨⟨0, true⟩, { (⟨memory, arrays, heap, frames, status⟩ : Executable model) with
          status := .faulted .constraint }, ?_, ?_⟩
      · rw [step_eq_advance model policy abi program _ _ top callers running stack]
        rcases top with ⟨scopes, control', continuation⟩
        simp only at control; subst control
        cases delivered with
        | integer _ => cases kind
        | address _ => simp only [advance, evaluate_complete model policy memory arrays scopes evaluated, Configuration.fail]
        | null => simp only [advance, evaluate_complete model policy memory arrays scopes evaluated, Configuration.fail]
      · rfl
  | whileFault top callers condition body reason running stack control evaluated =>
      refine ⟨⟨0, true⟩, { (⟨memory, arrays, heap, frames, status⟩ : Executable model) with
          status := .faulted reason }, ?_, ?_⟩
      · rw [step_eq_advance model policy abi program _ _ top callers running stack]
        rcases top with ⟨scopes, control', continuation⟩
        simp only at control; subst control
        simp only [advance, evaluate_complete model policy memory arrays scopes evaluated, Configuration.fail]
      · rfl
  | whileTrue top callers condition body test running stack control evaluated holds =>
      refine ⟨⟨0, true⟩, { (⟨memory, arrays, heap, frames, status⟩ : Executable model) with
          stack := { top with control := .execute body, continuation := .loop condition body top.continuation } :: callers }, ?_, ?_⟩
      · rw [step_eq_advance model policy abi program _ _ top callers running stack]
        rcases top with ⟨scopes, control', continuation⟩
        simp only at control; subst control
        simp only [advance, evaluate_complete model policy memory arrays scopes evaluated, holds, if_true,
          Configuration.continueWith]
      · rfl
  | whileFalse top callers condition body test running stack control evaluated fails =>
      refine ⟨⟨0, true⟩, { (⟨memory, arrays, heap, frames, status⟩ : Executable model) with
          stack := { top with control := .flow .normal } :: callers }, ?_, ?_⟩
      · rw [step_eq_advance model policy abi program _ _ top callers running stack]
        rcases top with ⟨scopes, control', continuation⟩
        simp only at control; subst control
        simp only [advance, evaluate_complete model policy memory arrays scopes evaluated, fails, Bool.false_eq_true,
          if_false, Configuration.continueWith]
      · rfl
  | whileKind top callers condition body delivered running stack control evaluated kind =>
      refine ⟨⟨0, true⟩, { (⟨memory, arrays, heap, frames, status⟩ : Executable model) with
          status := .faulted .constraint }, ?_, ?_⟩
      · rw [step_eq_advance model policy abi program _ _ top callers running stack]
        rcases top with ⟨scopes, control', continuation⟩
        simp only at control; subst control
        cases delivered with
        | integer _ => cases kind
        | address _ => simp only [advance, evaluate_complete model policy memory arrays scopes evaluated, Configuration.fail]
        | null => simp only [advance, evaluate_complete model policy memory arrays scopes evaluated, Configuration.fail]
      · rfl
  | breakLoop top callers running stack control =>
      refine ⟨⟨0, true⟩, { (⟨memory, arrays, heap, frames, status⟩ : Executable model) with
          stack := { top with control := .flow .broken } :: callers }, ?_, ?_⟩
      · rw [step_eq_advance model policy abi program _ _ top callers running stack]
        rcases top with ⟨scopes, control', continuation⟩
        simp only at control; subst control
        rfl
      · rfl
  | continueLoop top callers running stack control =>
      refine ⟨⟨0, true⟩, { (⟨memory, arrays, heap, frames, status⟩ : Executable model) with
          stack := { top with control := .flow .continued } :: callers }, ?_, ?_⟩
      · rw [step_eq_advance model policy abi program _ _ top callers running stack]
        rcases top with ⟨scopes, control', continuation⟩
        simp only at control; subst control
        rfl
      · rfl
  | returnNone top callers running stack control =>
      refine ⟨⟨0, true⟩, { (⟨memory, arrays, heap, frames, status⟩ : Executable model) with
          stack := { top with control := .returning none } :: callers }, ?_, ?_⟩
      · rw [step_eq_advance model policy abi program _ _ top callers running stack]
        rcases top with ⟨scopes, control', continuation⟩
        simp only at control; subst control
        rfl
      · rfl
  | returnFault top callers value reason running stack control evaluated =>
      refine ⟨⟨0, true⟩, { (⟨memory, arrays, heap, frames, status⟩ : Executable model) with
          status := .faulted reason }, ?_, ?_⟩
      · rw [step_eq_advance model policy abi program _ _ top callers running stack]
        rcases top with ⟨scopes, control', continuation⟩
        simp only at control; subst control
        simp only [advance, evaluate_complete model policy memory arrays scopes evaluated, Configuration.fail]
      · rfl
  | returnValue top callers value returned running stack control evaluated =>
      refine ⟨⟨0, true⟩, { (⟨memory, arrays, heap, frames, status⟩ : Executable model) with
          stack := { top with control := .returning (some returned) } :: callers }, ?_, ?_⟩
      · rw [step_eq_advance model policy abi program _ _ top callers running stack]
        rcases top with ⟨scopes, control', continuation⟩
        simp only at control; subst control
        simp only [advance, evaluate_complete model policy memory arrays scopes evaluated, Configuration.continueWith]
      · rfl
  | declaringDone top callers body running stack control =>
      refine ⟨⟨0, true⟩, { (⟨memory, arrays, heap, frames, status⟩ : Executable model) with
          stack := { top with control := .execute body } :: callers }, ?_, ?_⟩
      · rw [step_eq_advance model policy abi program _ _ top callers running stack]
        rcases top with ⟨scopes, control', continuation⟩
        simp only at control; subst control
        rfl
      · rfl
  | declaringRedeclared top callers declaration rest body head tail name running stack control scopes named redeclared =>
      refine ⟨⟨0, true⟩, { (⟨memory, arrays, heap, frames, status⟩ : Executable model) with
          status := .faulted .constraint }, ?_, ?_⟩
      · rw [step_eq_advance model policy abi program _ _ top callers running stack]
        rcases top with ⟨topScopes, control', continuation⟩
        simp only at control scopes; subst control; subst scopes
        subst named
        cases declaration with
        | object object initializer =>
          simp only [Declaration.name] at redeclared
          simp only [advance, redeclared, if_true, Configuration.fail]
        | pointer pointerName initializer =>
          simp only [Declaration.name] at redeclared
          simp only [advance, redeclared, if_true, Configuration.fail]
      · rfl
  | declaringObject top callers declaration rest body head tail identity after nextArrays nextScopes running stack
      control scopes fresh declared =>
      obtain ⟨saved, declaredExec, representedDecl⟩ :=
        declareObject_complete model memory arrays _ _ _ _ _ _ _ declared
      refine ⟨⟨identity, true⟩, { (⟨memory, arrays, heap, frames, status⟩ : Executable model) with
          memory := saved,
          arrays := nextArrays,
          stack := { top with scopes := nextScopes, control := .declaring rest body } :: callers }, ?_, ?_⟩
      · rw [step_eq_advance model policy abi program _ _ top callers running stack]
        rcases top with ⟨topScopes, control', continuation⟩
        simp only at control scopes; subst control; subst scopes
        simp only [advance, fresh, Bool.false_eq_true, if_false, declaredExec]
      · simp [Configuration.represent, representedDecl]
  | declaringArrayInitializer top callers declaration value rest body head tail identity after nextArrays nextScopes count
      positive running stack control scopes fresh declared array =>
      obtain ⟨saved, declaredExec, representedDecl⟩ :=
        declareObject_complete model memory arrays _ _ _ _ _ _ _ declared
      refine ⟨⟨identity, true⟩, { (⟨memory, arrays, heap, frames, status⟩ : Executable model) with
          status := .faulted .constraint }, ?_, ?_⟩
      · rw [step_eq_advance model policy abi program _ _ top callers running stack]
        rcases top with ⟨topScopes, control', continuation⟩
        simp only at control scopes; subst control; subst scopes
        simp only [advance, fresh, Bool.false_eq_true, if_false, declaredExec, array, Configuration.fail]
      · rfl
  | declaringInitializerFault top callers declaration value rest body head tail identity after nextArrays nextScopes reason
      running stack control scopes fresh declared scalar evaluated =>
      obtain ⟨saved, declaredExec, representedDecl⟩ :=
        declareObject_complete model memory arrays _ _ _ _ _ _ _ declared
      refine ⟨⟨identity, true⟩, { (⟨memory, arrays, heap, frames, status⟩ : Executable model) with
          status := .faulted reason }, ?_, ?_⟩
      · rw [step_eq_advance model policy abi program _ _ top callers running stack]
        rcases top with ⟨topScopes, control', continuation⟩
        simp only at control scopes; subst control; subst scopes
        rw [← representedDecl] at evaluated
        simp only [advance, fresh, Bool.false_eq_true, if_false, declaredExec, scalar,
          evaluate_complete model policy saved nextArrays nextScopes evaluated, Configuration.fail]
      · rfl
  | declaringInitialized top callers declaration value rest body head tail identity after nextArrays nextScopes initial
      stored running stack control scopes fresh declared scalar evaluated storing =>
      obtain ⟨saved, declaredExec, representedDecl⟩ :=
        declareObject_complete model memory arrays _ _ _ _ _ _ _ declared
      rw [← representedDecl] at evaluated storing
      obtain ⟨storedMemory, storedExec, representedStore⟩ := Effect.represent_done model policy
        (storeElement_complete model policy saved nextArrays _ initial _ storing)
      refine ⟨⟨identity, true⟩, { (⟨memory, arrays, heap, frames, status⟩ : Executable model) with
          memory := storedMemory,
          arrays := nextArrays,
          stack := { top with scopes := nextScopes, control := .declaring rest body } :: callers }, ?_, ?_⟩
      · rw [step_eq_advance model policy abi program _ _ top callers running stack]
        rcases top with ⟨topScopes, control', continuation⟩
        simp only at control scopes; subst control; subst scopes
        simp only [advance, fresh, Bool.false_eq_true, if_false, declaredExec, scalar,
          evaluate_complete model policy saved nextArrays nextScopes evaluated, storedExec]
      · simp [Configuration.represent, representedStore]
  | declaringInitializerStoreFault top callers declaration value rest body head tail identity after nextArrays nextScopes
      initial reason running stack control scopes fresh declared scalar evaluated storing =>
      obtain ⟨saved, declaredExec, representedDecl⟩ :=
        declareObject_complete model memory arrays _ _ _ _ _ _ _ declared
      rw [← representedDecl] at evaluated storing
      have storedExec := Effect.represent_fault model policy
        (storeElement_complete model policy saved nextArrays _ initial _ storing)
      refine ⟨⟨identity, true⟩, { (⟨memory, arrays, heap, frames, status⟩ : Executable model) with
          status := .faulted reason }, ?_, ?_⟩
      · rw [step_eq_advance model policy abi program _ _ top callers running stack]
        rcases top with ⟨topScopes, control', continuation⟩
        simp only at control scopes; subst control; subst scopes
        simp only [advance, fresh, Bool.false_eq_true, if_false, declaredExec, scalar,
          evaluate_complete model policy saved nextArrays nextScopes evaluated, storedExec, Configuration.fail]
      · rfl
  | declaringInitializerKind top callers declaration value rest body head tail identity after nextArrays nextScopes
      delivered running stack control scopes fresh declared scalar evaluated kind =>
      obtain ⟨saved, declaredExec, representedDecl⟩ :=
        declareObject_complete model memory arrays _ _ _ _ _ _ _ declared
      refine ⟨⟨identity, true⟩, { (⟨memory, arrays, heap, frames, status⟩ : Executable model) with
          status := .faulted .constraint }, ?_, ?_⟩
      · rw [step_eq_advance model policy abi program _ _ top callers running stack]
        rcases top with ⟨topScopes, control', continuation⟩
        simp only at control scopes; subst control; subst scopes
        rw [← representedDecl] at evaluated
        cases delivered with
        | integer _ => cases kind
        | address _ =>
          simp only [advance, fresh, Bool.false_eq_true, if_false, declaredExec, scalar,
            evaluate_complete model policy saved nextArrays nextScopes evaluated, Configuration.fail]
        | null =>
          simp only [advance, fresh, Bool.false_eq_true, if_false, declaredExec, scalar,
            evaluate_complete model policy saved nextArrays nextScopes evaluated, Configuration.fail]
      · rfl
  | declaringPointer top callers name rest body head tail running stack control scopes fresh =>
      refine ⟨⟨0, true⟩, { (⟨memory, arrays, heap, frames, status⟩ : Executable model) with
          stack := { top with scopes := head.bindPointer name none :: tail, control := .declaring rest body } :: callers }, ?_, ?_⟩
      · rw [step_eq_advance model policy abi program _ _ top callers running stack]
        rcases top with ⟨topScopes, control', continuation⟩
        simp only at control scopes; subst control; subst scopes
        simp only [advance, fresh, Bool.false_eq_true, if_false, Configuration.continueWith]
      · rfl
  | declaringPointerFault top callers name value rest body head tail reason running stack control scopes fresh evaluated =>
      refine ⟨⟨0, true⟩, { (⟨memory, arrays, heap, frames, status⟩ : Executable model) with
          status := .faulted reason }, ?_, ?_⟩
      · rw [step_eq_advance model policy abi program _ _ top callers running stack]
        rcases top with ⟨topScopes, control', continuation⟩
        simp only at control scopes; subst control; subst scopes
        simp only [advance, fresh, Bool.false_eq_true, if_false,
          evaluate_complete model policy memory arrays (head.bindPointer name none :: tail) evaluated, Configuration.fail]
      · rfl
  | declaringPointerInitialized top callers name value rest body head tail delivered running stack control scopes fresh
      evaluated kind =>
      refine ⟨⟨0, true⟩, { (⟨memory, arrays, heap, frames, status⟩ : Executable model) with
          stack := { top with scopes := head.bindPointer name (some delivered) :: tail, control := .declaring rest body } :: callers }, ?_, ?_⟩
      · rw [step_eq_advance model policy abi program _ _ top callers running stack]
        rcases top with ⟨topScopes, control', continuation⟩
        simp only at control scopes; subst control; subst scopes
        simp only [advance, fresh, Bool.false_eq_true, if_false,
          evaluate_complete model policy memory arrays (head.bindPointer name none :: tail) evaluated, kind, if_true, Configuration.continueWith]
      · rfl
  | declaringPointerKind top callers name value rest body head tail delivered running stack control scopes fresh
      evaluated kind =>
      refine ⟨⟨0, true⟩, { (⟨memory, arrays, heap, frames, status⟩ : Executable model) with
          status := .faulted .constraint }, ?_, ?_⟩
      · rw [step_eq_advance model policy abi program _ _ top callers running stack]
        rcases top with ⟨topScopes, control', continuation⟩
        simp only at control scopes; subst control; subst scopes
        simp only [advance, fresh, Bool.false_eq_true, if_false,
          evaluate_complete model policy memory arrays (head.bindPointer name none :: tail) evaluated, kind, Configuration.fail]
      · rfl
  | bindingDone top callers body running stack control =>
      refine ⟨⟨0, true⟩, { (⟨memory, arrays, heap, frames, status⟩ : Executable model) with
          stack := { top with control := .execute body } :: callers }, ?_, ?_⟩
      · rw [step_eq_advance model policy abi program _ _ top callers running stack]
        rcases top with ⟨scopes, control', continuation⟩
        simp only at control; subst control
        rfl
      · rfl
  | bindingRedeclared top callers parameter delivered rest body head tail name running stack control scopes named
      kinds redeclared =>
      refine ⟨⟨0, true⟩, { (⟨memory, arrays, heap, frames, status⟩ : Executable model) with
          status := .faulted .constraint }, ?_, ?_⟩
      · rw [step_eq_advance model policy abi program _ _ top callers running stack]
        rcases top with ⟨topScopes, control', continuation⟩
        simp only at control scopes; subst control; subst scopes
        subst named
        cases parameter with
        | integer integerName type =>
          cases delivered with
          | integer scalar =>
            simp only [Parameter.name] at redeclared
            simp only [advance, redeclared, if_true, Configuration.fail]
          | address _ => cases kinds
          | null => cases kinds
        | pointer pointerName =>
          simp only [Parameter.name] at redeclared
          simp only [advance, redeclared, if_true, Configuration.fail]
      · rfl
  | bindingInteger top callers name type scalar rest body head tail identity after nextArrays nextScopes stored
      running stack control scopes fresh declared storing =>
      obtain ⟨saved, declaredExec, representedDecl⟩ :=
        declareObject_complete model memory arrays _ _ _ _ _ _ _ declared
      rw [← representedDecl] at storing
      obtain ⟨storedMemory, storedExec, representedStore⟩ := Effect.represent_done model policy
        (storeElement_complete model policy saved nextArrays _ scalar _ storing)
      refine ⟨⟨identity, true⟩, { (⟨memory, arrays, heap, frames, status⟩ : Executable model) with
          memory := storedMemory,
          arrays := nextArrays,
          stack := { top with scopes := nextScopes, control := .binding rest body } :: callers }, ?_, ?_⟩
      · rw [step_eq_advance model policy abi program _ _ top callers running stack]
        rcases top with ⟨topScopes, control', continuation⟩
        simp only at control scopes; subst control; subst scopes
        simp only [advance, fresh, Bool.false_eq_true, if_false, declaredExec, storedExec]
      · simp [Configuration.represent, representedStore]
  | bindingIntegerFault top callers name type scalar rest body head tail identity after nextArrays nextScopes reason
      running stack control scopes fresh declared storing =>
      obtain ⟨saved, declaredExec, representedDecl⟩ :=
        declareObject_complete model memory arrays _ _ _ _ _ _ _ declared
      rw [← representedDecl] at storing
      have storedExec := Effect.represent_fault model policy
        (storeElement_complete model policy saved nextArrays _ scalar _ storing)
      refine ⟨⟨identity, true⟩, { (⟨memory, arrays, heap, frames, status⟩ : Executable model) with
          status := .faulted reason }, ?_, ?_⟩
      · rw [step_eq_advance model policy abi program _ _ top callers running stack]
        rcases top with ⟨topScopes, control', continuation⟩
        simp only at control scopes; subst control; subst scopes
        simp only [advance, fresh, Bool.false_eq_true, if_false, declaredExec, storedExec, Configuration.fail]
      · rfl
  | bindingPointer top callers name delivered rest body head tail running stack control scopes fresh =>
      refine ⟨⟨0, true⟩, { (⟨memory, arrays, heap, frames, status⟩ : Executable model) with
          stack := { top with scopes := head.bindPointer name (some delivered) :: tail, control := .binding rest body } :: callers }, ?_, ?_⟩
      · rw [step_eq_advance model policy abi program _ _ top callers running stack]
        rcases top with ⟨topScopes, control', continuation⟩
        simp only at control scopes; subst control; subst scopes
        simp only [advance, fresh, Bool.false_eq_true, if_false, Configuration.continueWith]
      · rfl
  | bindingMismatch top callers name type delivered rest body running stack control kind =>
      refine ⟨⟨0, true⟩, { (⟨memory, arrays, heap, frames, status⟩ : Executable model) with
          status := .faulted .constraint }, ?_, ?_⟩
      · rw [step_eq_advance model policy abi program _ _ top callers running stack]
        rcases top with ⟨scopes, control', continuation⟩
        simp only at control; subst control
        cases delivered with
        | integer _ => cases kind
        | address _ => rfl
        | null => rfl
      · rfl
  | fallsOff top callers running stack control continuation =>
      refine ⟨⟨0, true⟩, { (⟨memory, arrays, heap, frames, status⟩ : Executable model) with
          stack := { top with control := .returning none } :: callers }, ?_, ?_⟩
      · rw [step_eq_advance model policy abi program _ _ top callers running stack]
        rcases top with ⟨topScopes, control', topContinuation⟩
        simp only at control continuation; subst control; subst continuation
        rfl
      · rfl
  | strayJump top callers flow running stack control abrupt continuation =>
      refine ⟨⟨0, true⟩, { (⟨memory, arrays, heap, frames, status⟩ : Executable model) with
          status := .faulted .constraint }, ?_, ?_⟩
      · rw [step_eq_advance model policy abi program _ _ top callers running stack]
        rcases top with ⟨topScopes, control', topContinuation⟩
        simp only at control continuation; subst control; subst continuation
        cases flow with
        | normal => exact absurd rfl abrupt
        | broken => rfl
        | continued => rfl
      · rfl
  | next top callers statement outer running stack control continuation =>
      refine ⟨⟨0, true⟩, { (⟨memory, arrays, heap, frames, status⟩ : Executable model) with
          stack := { top with control := .execute statement, continuation := outer } :: callers }, ?_, ?_⟩
      · rw [step_eq_advance model policy abi program _ _ top callers running stack]
        rcases top with ⟨topScopes, control', topContinuation⟩
        simp only at control continuation; subst control; subst continuation
        rfl
      · rfl
  | skipNext top callers flow statement outer running stack control abrupt continuation =>
      refine ⟨⟨0, true⟩, { (⟨memory, arrays, heap, frames, status⟩ : Executable model) with
          stack := { top with continuation := outer } :: callers }, ?_, ?_⟩
      · rw [step_eq_advance model policy abi program _ _ top callers running stack]
        rcases top with ⟨topScopes, control', topContinuation⟩
        simp only at control continuation; subst control; subst continuation
        cases flow with
        | normal => exact absurd rfl abrupt
        | broken => rfl
        | continued => rfl
      · rfl
  | exitLoop top callers condition body outer running stack control continuation =>
      refine ⟨⟨0, true⟩, { (⟨memory, arrays, heap, frames, status⟩ : Executable model) with
          stack := { top with control := .flow .normal, continuation := outer } :: callers }, ?_, ?_⟩
      · rw [step_eq_advance model policy abi program _ _ top callers running stack]
        rcases top with ⟨topScopes, control', topContinuation⟩
        simp only at control continuation; subst control; subst continuation
        rfl
      · rfl
  | iterate top callers flow condition body outer running stack control again continuation =>
      refine ⟨⟨0, true⟩, { (⟨memory, arrays, heap, frames, status⟩ : Executable model) with
          stack := { top with control := .execute (.whileLoop condition body), continuation := outer } :: callers }, ?_, ?_⟩
      · rw [step_eq_advance model policy abi program _ _ top callers running stack]
        rcases top with ⟨topScopes, control', topContinuation⟩
        simp only at control continuation; subst control; subst continuation
        cases flow with
        | broken => exact absurd rfl again
        | normal => rfl
        | continued => rfl
      · rfl
  | leave top callers flow outer after rest running stack control continuation left =>
      obtain ⟨saved, leftExec, representedLeave⟩ :=
        leaveScope_complete model memory top.scopes after rest left
      refine ⟨⟨0, true⟩, { (⟨memory, arrays, heap, frames, status⟩ : Executable model) with
          memory := saved,
          stack := { top with scopes := rest, continuation := outer } :: callers }, ?_, ?_⟩
      · rw [step_eq_advance model policy abi program _ _ top callers running stack]
        rcases top with ⟨topScopes, control', topContinuation⟩
        simp only at control continuation; subst control; subst continuation
        cases flow <;> simp only [advance, leftExec]
      · simp [Configuration.represent, representedLeave]
  | returnLeave top callers value outer after rest running stack control continuation left =>
      obtain ⟨saved, leftExec, representedLeave⟩ :=
        leaveScope_complete model memory top.scopes after rest left
      refine ⟨⟨0, true⟩, { (⟨memory, arrays, heap, frames, status⟩ : Executable model) with
          memory := saved,
          stack := { top with scopes := rest, continuation := outer } :: callers }, ?_, ?_⟩
      · rw [step_eq_advance model policy abi program _ _ top callers running stack]
        rcases top with ⟨topScopes, control', topContinuation⟩
        simp only at control continuation; subst control; subst continuation
        simp only [advance, leftExec]
      · simp [Configuration.represent, representedLeave]
  | returnSkip top callers value statement outer running stack control continuation =>
      refine ⟨⟨0, true⟩, { (⟨memory, arrays, heap, frames, status⟩ : Executable model) with
          stack := { top with continuation := outer } :: callers }, ?_, ?_⟩
      · rw [step_eq_advance model policy abi program _ _ top callers running stack]
        rcases top with ⟨topScopes, control', topContinuation⟩
        simp only at control continuation; subst control; subst continuation
        rfl
      · rfl
  | returnExitLoop top callers value condition body outer running stack control continuation =>
      refine ⟨⟨0, true⟩, { (⟨memory, arrays, heap, frames, status⟩ : Executable model) with
          stack := { top with continuation := outer } :: callers }, ?_, ?_⟩
      · rw [step_eq_advance model policy abi program _ _ top callers running stack]
        rcases top with ⟨topScopes, control', topContinuation⟩
        simp only at control continuation; subst control; subst continuation
        rfl
      · rfl

  | finish top value running stack control continuation =>
      refine ⟨⟨0, true⟩, { (⟨memory, arrays, heap, frames, status⟩ : Executable model) with
          status := .finished value }, ?_, rfl⟩
      rw [step_eq_advance model policy abi program _ _ top [] running stack]
      rcases top with ⟨topScopes, control', topContinuation⟩
      simp only at control continuation; subst control; subst continuation
      rfl
  | deliver top caller rest value result after updated running stack control continuation waiting delivered =>
      have computed := deliver_complete model policy memory arrays caller.scopes result value _ delivered
      cases delivering : deliver model policy memory arrays caller.scopes result value with
      | fault reason => rw [delivering] at computed; cases computed
      | done pair =>
          obtain ⟨saved, updated'⟩ := pair
          rw [delivering] at computed
          simp only [Effect.done.injEq, Prod.mk.injEq] at computed
          obtain ⟨representedDeliver, rfl⟩ := computed
          refine ⟨⟨0, true⟩, { (⟨memory, arrays, heap, frames, status⟩ : Executable model) with
              memory := saved,
              stack := { caller with scopes := updated', control := .flow .normal } :: rest }, ?_, ?_⟩
          · rw [step_eq_advance model policy abi program _ _ top (caller :: rest) running stack]
            rcases top with ⟨topScopes, control', topContinuation⟩
            rcases caller with ⟨callerScopes, callerControl, callerContinuation⟩
            simp only at control continuation waiting delivering
            subst control; subst continuation; subst waiting
            simp only [advance, delivering]
          · simp [Configuration.represent, representedDeliver]
  | deliverFault top caller rest value result reason running stack control continuation waiting delivered =>
      have computed := deliver_complete model policy memory arrays caller.scopes result value _ delivered
      cases delivering : deliver model policy memory arrays caller.scopes result value with
      | done pair => rw [delivering] at computed; cases computed
      | fault other =>
          rw [delivering] at computed
          obtain rfl : reason = other := by injection computed with same; exact same.symm
          refine ⟨⟨0, true⟩, { (⟨memory, arrays, heap, frames, status⟩ : Executable model) with
              status := .faulted reason }, ?_, rfl⟩
          rw [step_eq_advance model policy abi program _ _ top (caller :: rest) running stack]
          rcases top with ⟨topScopes, control', topContinuation⟩
          rcases caller with ⟨callerScopes, callerControl, callerContinuation⟩
          simp only at control continuation waiting delivering
          subst control; subst continuation; subst waiting
          simp only [advance, delivering, Configuration.fail]

/-- **The executable step is the independent step**, up to the open choices. -/
theorem step_iff (c : Executable model) (target : Semantic model) :
    (∃ choice next, step model policy abi program choice c = some next ∧ next.represent = target) ↔
      Step model policy abi program c.represent target :=
  ⟨fun ⟨choice, next, stepped, represented⟩ =>
      represented ▸ step_sound model policy abi program choice c next stepped,
    step_complete model policy abi program c target⟩

end Completeness

/-! ## The common event machine -/

section Machine

variable (model : Model) (policy : SignedConversionPolicy) (abi : IntegerType IntegerExtension → ObjectLayout.Layout)
  (program : Program model)

/-- Observations of the core machine: each step is a computational occurrence
with its actual source and destination configurations; a fault is reported with
its reason. -/
inductive Event (model : Model) where
  | occurrence (before after : Executable model)
  | fault (reason : Fault model)

/-- An external request carries the service and the argument values. -/
structure Request (model : Model) where
  service : String
  arguments : List (Value model)

/-- The canonical choice: the next identity above every identity in use, and a
successful allocation. -/
def canonicalChoice (configuration : Executable model) : Choice :=
  ⟨IntegerObjectConstruction.freshIdentity configuration.memory configuration.arrays, true⟩

open Mettapedia.GSLT.Distinction.ProductiveBlocks in
/-- The fixed core as a common event machine. External calls suspend with the
complete waiting configuration; `reply` resumes it. -/
def machine : Machine (Executable model) (Event model) (Option (Value model)) (Request model) where
  step configuration :=
    match configuration.status with
    | .running =>
        (step model policy abi program (canonicalChoice model configuration) configuration).map fun next =>
          .publish [.occurrence configuration next] next
    | .waiting service arguments => some (.call ⟨service, arguments⟩ configuration)
    | .finished value => some (.finish value)
    | .faulted reason => some (.fail [.fault reason])

open Mettapedia.GSLT.Distinction.ProductiveBlocks in
/-- Every published occurrence of the machine is an independent step. -/
theorem machine_occurrence_sound (configuration next : Executable model)
    (events : List (Event model))
    (stepped : (machine model policy abi program).step configuration = some (.publish events next)) :
    Step model policy abi program configuration.represent next.represent := by
  unfold machine at stepped
  cases running : configuration.status with
  | running =>
      simp only [running, Option.map_eq_some_iff] at stepped
      obtain ⟨computed, executed, published⟩ := stepped
      cases published
      exact step_sound model policy abi program _ configuration next executed
  | waiting service arguments => simp [running] at stepped
  | finished value => simp [running] at stepped
  | faulted reason => simp [running] at stepped

open Mettapedia.GSLT.Distinction.ProductiveBlocks in
/-- Budget slicing resumes the retained configuration exactly. -/
theorem machine_run_add (first second : Nat) (configuration : Executable model) :
    (machine model policy abi program).run (first + second) configuration =
      (machine model policy abi program).continueRun second
        ((machine model policy abi program).run first configuration) :=
  (machine model policy abi program).run_add first second configuration

end Machine

end Mettapedia.Languages.C11.FixedCore
