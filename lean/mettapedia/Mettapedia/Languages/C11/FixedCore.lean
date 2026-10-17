import Mettapedia.Languages.C11.AutomaticObjectScopes
import Mettapedia.Languages.C11.IntegerOperators
import Mettapedia.Languages.C11.IntegerAssignment

/-!
# The fixed C core: names, pure expressions and places

The fixed core is a source language over the existing semantic modules. Integer
values, conversions, arithmetic and comparisons are the typed integer operations;
objects live in the byte memory with effective types; declared objects and their
lifetimes come from the automatic scope frames; pointers are array-relative
positions checked against live allocations. This module adds names: a place is
resolved through the lexical scopes of the current function activation, and a
pure expression is evaluated against the memory without changing it.

Core expressions have no side effects. Their evaluation order is therefore not
observable, and the evaluator is a function. Side effects inside expressions,
with C11's unsequenced-evaluation semantics, are the subject of the located
expression module; core statements sequence their effects explicitly.

Every refused memory or pointer operation of a well-formed core program is a
C11 undefined behavior: an access to a dead, out-of-bounds, misaligned or
indeterminate object, an effective-type violation, a trap representation, or a
pointer formed outside its array. Arithmetic overflow and division by zero are
undefined; an out-of-range signed conversion raises the implementation-defined
signal of the selected policy. Unbound names and operands of the wrong kind are
constraint violations of the program, not runtime behavior.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.C11.FixedCore

open IntegerMemoryModel ObjectAccessMemory

/-! ## Values, places and expressions -/

/-- A pointer to an integer element: the element type and the array-relative
position. A scalar object is an array of one element. -/
structure Address where
  type : IntegerType IntegerExtension
  pointer : ArrayPointers.Pointer
  deriving DecidableEq, Repr

inductive Value (model : Model) where
  | integer (scalar : IntegerScalar.Value model.parameters)
  | address (target : Address)
  | null
  deriving DecidableEq, Repr

/-- Why a core evaluation has no defined value. -/
inductive Fault (model : Model) where
  /-- Signed overflow or division by zero (undefined behavior). -/
  | arithmetic (type : IntegerType IntegerExtension) (reason : ArithmeticFault)
  /-- An implementation-defined signal raised by an out-of-range conversion. -/
  | signal (identifier : Nat)
  /-- A trap representation was read (undefined behavior). -/
  | trap (type : IntegerType IntegerExtension) (reason : IntegerBits.Trap)
  /-- A padding trap representation was read (undefined behavior). -/
  | paddingTrap (type : IntegerType IntegerExtension)
  /-- The access has no defined meaning in the memory model (undefined behavior). -/
  | access (target : Address)
  /-- Pointer arithmetic or dereference outside a live array, or of a null pointer
  (undefined behavior). -/
  | pointer
  /-- A read of a pointer variable that holds no value (undefined behavior). -/
  | indeterminatePointer (name : String)
  /-- Releasing a pointer that does not start a live dynamic object (undefined
  behavior; includes a second release). -/
  | invalidRelease
  /-- The caller uses the value of a call whose function fell off its end
  (undefined behavior, C11 6.9.1p12). -/
  | missingReturn
  /-- An unbound name or an operand of the wrong kind: the program violates a
  constraint; this is not a runtime behavior. -/
  | constraint
  /-- The host failed to answer a request to the named service. This is an
  interaction outcome, not a behavior of the C program. -/
  | service (name : String)
  deriving DecidableEq, Repr

inductive Result (model : Model) where
  | value (value : Value model)
  | fault (fault : Fault model)
  deriving DecidableEq, Repr

mutual
/-- Side-effect-free core expressions. -/
inductive Expression (model : Model) where
  | constant (scalar : IntegerScalar.Value model.parameters)
  | read (place : Place model)
  | binary (operator : IntegerBinaryOperator) (first second : Expression model)
  | compare (operator : IntegerOperators.Comparison) (first second : Expression model)
  | cast (type : IntegerType IntegerExtension) (operand : Expression model)
  | addressOf (place : Place model)
  | offset (pointer amount : Expression model)
  | variable (name : String)
  | null

/-- Places denote integer elements. -/
inductive Place (model : Model) where
  | named (name : String)
  | element (name : String) (index : Expression model)
  | deref (pointer : Expression model)
end

/-! ## Lexical scopes of one activation -/

/-- One lexical scope: declared integer objects with their owned lifetimes, and
pointer variables. Pointer variables are not addressable (`register` storage);
an absent value is indeterminate. -/
structure Scope (model : Model) where
  objects : AutomaticObjectScopes.Frame := {}
  pointers : List (String × Option (Value model)) := []

/-- What a name denotes in the innermost scope that declares it. -/
inductive Entity (model : Model) where
  | object (location : Lvalue)
  | pointer (value : Option (Value model))

def Scope.lookup {model : Model} (scope : Scope model) (name : String) : Option (Entity model) :=
  match scope.objects.bindings.lookup name with
  | some location => some (.object location)
  | none => (scope.pointers.lookup name).map Entity.pointer

def resolve {model : Model} : List (Scope model) → String → Option (Entity model)
  | [], _ => none
  | scope :: rest, name =>
      match scope.lookup name with
      | some entity => some entity
      | none => resolve rest name

/-- Independent name resolution: the innermost scope that declares the name. -/
inductive Resolves {model : Model} (name : String) : List (Scope model) → Entity model → Prop where
  | object (scope : Scope model) (rest : List (Scope model)) (location : Lvalue)
      (bound : ScopedLvalues.FrameBinding name scope.objects.bindings location) :
      Resolves name (scope :: rest) (.object location)
  | pointer (scope : Scope model) (rest : List (Scope model)) (value : Option (Value model))
      (noObject : ScopedLvalues.FrameAbsent name scope.objects.bindings)
      (bound : scope.pointers.lookup name = some value) :
      Resolves name (scope :: rest) (.pointer value)
  | outer (scope : Scope model) (rest : List (Scope model)) (entity : Entity model)
      (noObject : ScopedLvalues.FrameAbsent name scope.objects.bindings)
      (noPointer : scope.pointers.lookup name = none) (found : Resolves name rest entity) :
      Resolves name (scope :: rest) entity

/-- Independent absence of a name from every scope. -/
inductive Unbound {model : Model} (name : String) : List (Scope model) → Prop where
  | empty : Unbound name []
  | cons (scope : Scope model) (rest : List (Scope model))
      (noObject : ScopedLvalues.FrameAbsent name scope.objects.bindings)
      (noPointer : scope.pointers.lookup name = none) (absent : Unbound name rest) :
      Unbound name (scope :: rest)

theorem resolve_sound {model : Model} (scopes : List (Scope model)) (name : String) (entity : Entity model)
    (found : resolve scopes name = some entity) : Resolves name scopes entity := by
  induction scopes with
  | nil => simp [resolve] at found
  | cons scope rest ih =>
      unfold resolve Scope.lookup at found
      cases objects : scope.objects.bindings.lookup name with
      | some location =>
          rw [objects] at found
          cases found
          exact .object scope rest location ((ScopedLvalues.lookup_frame_iff _ _ _).mp objects)
      | none =>
          rw [objects] at found
          have noObject := (ScopedLvalues.lookup_absent_iff _ _).mp objects
          cases pointers : scope.pointers.lookup name with
          | some value =>
              rw [pointers] at found
              cases found
              exact .pointer scope rest value noObject pointers
          | none =>
              rw [pointers] at found
              exact .outer scope rest entity noObject pointers (ih found)

theorem resolve_complete {model : Model} (scopes : List (Scope model)) (name : String) (entity : Entity model)
    (resolved : Resolves name scopes entity) : resolve scopes name = some entity := by
  induction resolved with
  | object scope rest location bound =>
      simp [resolve, Scope.lookup, (ScopedLvalues.lookup_frame_iff _ _ _).mpr bound]
  | pointer scope rest value noObject bound =>
      simp [resolve, Scope.lookup, (ScopedLvalues.lookup_absent_iff _ _).mpr noObject, bound]
  | outer scope rest entity noObject noPointer _ ih =>
      simp [resolve, Scope.lookup, (ScopedLvalues.lookup_absent_iff _ _).mpr noObject, noPointer, ih]

theorem resolve_none_iff {model : Model} (scopes : List (Scope model)) (name : String) :
    resolve scopes name = none ↔ Unbound name scopes := by
  induction scopes with
  | nil => exact ⟨fun _ => .empty, fun _ => rfl⟩
  | cons scope rest ih =>
      constructor
      · intro missing
        unfold resolve Scope.lookup at missing
        cases objects : scope.objects.bindings.lookup name with
        | some location => rw [objects] at missing; cases missing
        | none =>
            rw [objects] at missing
            cases pointers : scope.pointers.lookup name with
            | some value => rw [pointers] at missing; cases missing
            | none =>
                rw [pointers] at missing
                exact .cons scope rest ((ScopedLvalues.lookup_absent_iff _ _).mp objects) pointers
                  (ih.mp missing)
      · intro absent
        cases absent with
        | cons _ _ noObject noPointer absent =>
            simp [resolve, Scope.lookup, (ScopedLvalues.lookup_absent_iff _ _).mpr noObject, noPointer,
              ih.mpr absent]

/-! ## Typed element locations -/

/-- The element type of a declared integer object's root location. -/
def elementType : AccessTypes.ObjectType → Option (IntegerType IntegerExtension)
  | .scalar (.integer type) => some type
  | .array (.scalar (.integer type)) _ => some type
  | _ => none

/-- The first element of a declared object. -/
def rootAddress (location : Lvalue) : Option Address :=
  (elementType location.view.type).map fun type =>
    ⟨type, ⟨location.object.address.allocation, 0⟩⟩

/-- The lvalue of the element a pointer designates, once its range is checked. -/
def elementLvalue (target : Address) (range : ByteRanges.Range) : Lvalue :=
  ⟨range, ⟨.scalar (.integer target.type), {}⟩⟩

variable {model : Model}

/-! ## Result plumbing

Faults propagate unchanged and the first operand's fault is reported. C11
gives an execution with undefined behavior no meaning at all, so this choice
of which fault to report is a reporting policy, not an evaluation order. -/

def integerOperand : Result model → Except (Fault model) (IntegerScalar.Value model.parameters)
  | .fault fault => .error fault
  | .value (.integer scalar) => .ok scalar
  | .value _ => .error .constraint

def integerOperands (first second : Result model) :
    Except (Fault model) (IntegerScalar.Value model.parameters × IntegerScalar.Value model.parameters) :=
  match first, second with
  | .fault fault, _ => .error fault
  | _, .fault fault => .error fault
  | .value (.integer left), .value (.integer right) => .ok (left, right)
  | _, _ => .error .constraint

/-- Pointer arithmetic needs a pointer into an array and an integer; a null
pointer has no array. -/
def pointerOperands (first second : Result model) :
    Except (Fault model) (Address × IntegerScalar.Value model.parameters) :=
  match first, second with
  | .fault fault, _ => .error fault
  | _, .fault fault => .error fault
  | .value (.address target), .value (.integer amount) => .ok (target, amount)
  | .value .null, .value (.integer _) => .error .pointer
  | _, _ => .error .constraint

/-- A dereferenced pointer designates its element; null designates nothing. -/
def derefTarget : Result model → Except (Fault model) Address
  | .fault fault => .error fault
  | .value (.address target) => .ok target
  | .value .null => .error .pointer
  | .value (.integer _) => .error .constraint

def arithmeticResult : IntegerScalar.ArithmeticResult model.parameters → Result model
  | .value scalar => .value (.integer scalar)
  | .undefined type reason => .fault (.arithmetic type reason)

def castResult : IntegerScalar.CastResult model.parameters → Result model
  | .value scalar => .value (.integer scalar)
  | .signal identifier => .fault (.signal identifier)

def loadedResult : Loaded model → Result model
  | .value scalar _ => .value (.integer scalar)
  | .trap type reason => .fault (.trap type reason)
  | .paddingTrap type => .fault (.paddingTrap type)

/-- A name read as a value must denote a pointer variable. -/
def variableResult (name : String) : Option (Entity model) → Result model
  | some (.pointer (some value)) => .value value
  | some (.pointer none) => .fault (.indeterminatePointer name)
  | _ => .fault .constraint

/-- A name used as a place must denote a declared integer object. -/
def objectAddress : Option (Entity model) → Except (Fault model) Address
  | some (.object location) =>
      match rootAddress location with
      | some target => .ok target
      | none => .error .constraint
  | _ => .error .constraint

/-! ## Executable evaluation -/

/-- Read one element through its checked range and the typed object memory. -/
def readElement (model : Model) (memory : State model.characters) (arrays : ArrayPointers.Catalog)
    (target : Address) : Result model :=
  match ArrayPointers.elementRange memory.storage arrays target.pointer with
  | none => .fault (.access target)
  | some range =>
      match IntegerMemoryModel.load model memory (elementLvalue target range) with
      | none => .fault (.access target)
      | some loaded => loadedResult loaded

def displace (memory : State model.characters) (arrays : ArrayPointers.Catalog)
    (target : Address) (amount : IntegerScalar.Value model.parameters) : Result model :=
  match ArrayPointers.add memory.storage arrays target.pointer amount.integer.value with
  | some moved => .value (.address ⟨target.type, moved⟩)
  | none => .fault .pointer

def indexAddress (memory : State model.characters) (arrays : ArrayPointers.Catalog)
    (base : Except (Fault model) Address) (index : Result model) : Except (Fault model) Address :=
  match base with
  | .error fault => .error fault
  | .ok target =>
      match integerOperand index with
      | .error fault => .error fault
      | .ok amount =>
          match ArrayPointers.add memory.storage arrays target.pointer amount.integer.value with
          | some moved => .ok ⟨target.type, moved⟩
          | none => .error .pointer

section Executable

variable (model : Model) (policy : SignedConversionPolicy) (memory : State model.characters)
  (arrays : ArrayPointers.Catalog) (scopes : List (Scope model))

mutual
def evaluate : Expression model → Result model
  | .constant scalar => .value (.integer scalar)
  | .read place =>
      match locate place with
      | .error fault => .fault fault
      | .ok target => readElement model memory arrays target
  | .binary operator first second =>
      match integerOperands (evaluate first) (evaluate second) with
      | .error fault => .fault fault
      | .ok (left, right) => arithmeticResult (IntegerScalar.binary model.parameters operator left right)
  | .compare operator first second =>
      match integerOperands (evaluate first) (evaluate second) with
      | .error fault => .fault fault
      | .ok (left, right) => .value (.integer (IntegerOperators.comparison model.parameters operator left right))
  | .cast type operand =>
      match integerOperand (evaluate operand) with
      | .error fault => .fault fault
      | .ok input => castResult (IntegerScalar.cast model.parameters policy type input)
  | .addressOf place =>
      match locate place with
      | .error fault => .fault fault
      | .ok target => .value (.address target)
  | .offset pointer amount =>
      match pointerOperands (evaluate pointer) (evaluate amount) with
      | .error fault => .fault fault
      | .ok (target, distance) => displace memory arrays target distance
  | .variable name => variableResult name (resolve scopes name)
  | .null => .value .null

def locate : Place model → Except (Fault model) Address
  | .named name => objectAddress (resolve scopes name)
  | .element name index => indexAddress memory arrays (objectAddress (resolve scopes name)) (evaluate index)
  | .deref pointer => derefTarget (evaluate pointer)
end

end Executable

/-! ## The independent judgment -/

section Independent

variable (model : Model) (policy : SignedConversionPolicy)
  (memory : SemanticState model.characters) (arrays : ArrayPointers.Catalog) (scopes : List (Scope model))

/-- The independent outcome of reading an element. -/
inductive ReadsElement (target : Address) : Result model → Prop where
  | missing (absent : ¬∃ range, ArrayPointers.ElementRange memory.memory arrays target.pointer range) :
      ReadsElement target (.fault (.access target))
  | refused (range : ByteRanges.Range)
      (inside : ArrayPointers.ElementRange memory.memory arrays target.pointer range)
      (undefined : ¬∃ loaded, Loading model memory (elementLvalue target range) loaded) :
      ReadsElement target (.fault (.access target))
  | loaded (range : ByteRanges.Range) (loaded : Loaded model)
      (inside : ArrayPointers.ElementRange memory.memory arrays target.pointer range)
      (reading : Loading model memory (elementLvalue target range) loaded) :
      ReadsElement target (loadedResult loaded)

/-- The independent outcome of moving a pointer within its array. -/
inductive Displaces (target : Address) (amount : IntegerScalar.Value model.parameters) :
    Result model → Prop where
  | moved (result : ArrayPointers.Pointer)
      (added : ArrayPointers.Addition memory.memory arrays target.pointer amount.integer.value result) :
      Displaces target amount (.value (.address ⟨target.type, result⟩))
  | refused (outside : ¬∃ result, ArrayPointers.Addition memory.memory arrays target.pointer
      amount.integer.value result) :
      Displaces target amount (.fault .pointer)

/-- The independent outcome of indexing from a base address. -/
inductive Indexes : Except (Fault model) Address → Result model → Except (Fault model) Address → Prop where
  | base (fault : Fault model) (index : Result model) : Indexes (.error fault) index (.error fault)
  | index (target : Address) (index : Result model) (fault : Fault model)
      (bad : integerOperand index = .error fault) : Indexes (.ok target) index (.error fault)
  | moved (target : Address) (index : Result model) (amount : IntegerScalar.Value model.parameters)
      (result : ArrayPointers.Pointer) (good : integerOperand index = .ok amount)
      (added : ArrayPointers.Addition memory.memory arrays target.pointer amount.integer.value result) :
      Indexes (.ok target) index (.ok ⟨target.type, result⟩)
  | refused (target : Address) (index : Result model) (amount : IntegerScalar.Value model.parameters)
      (good : integerOperand index = .ok amount)
      (outside : ¬∃ result, ArrayPointers.Addition memory.memory arrays target.pointer
        amount.integer.value result) :
      Indexes (.ok target) index (.error .pointer)

/-- The independent meaning of a name used as a place. -/
inductive Designates (name : String) : Except (Fault model) Address → Prop where
  | object (location : Lvalue) (target : Address) (resolved : Resolves name scopes (.object location))
      (typed : rootAddress location = some target) : Designates name (.ok target)
  | untyped (location : Lvalue) (resolved : Resolves name scopes (.object location))
      (untyped : rootAddress location = none) : Designates name (.error .constraint)
  | pointer (value : Option (Value model)) (resolved : Resolves name scopes (.pointer value)) :
      Designates name (.error .constraint)
  | unbound (absent : Unbound name scopes) : Designates name (.error .constraint)

/-- The independent meaning of a name read as a value. -/
inductive Holds (name : String) : Result model → Prop where
  | value (value : Value model) (resolved : Resolves name scopes (.pointer (some value))) :
      Holds name (.value value)
  | indeterminate (resolved : Resolves name scopes (.pointer none)) :
      Holds name (.fault (.indeterminatePointer name))
  | object (location : Lvalue) (resolved : Resolves name scopes (.object location)) :
      Holds name (.fault .constraint)
  | unbound (absent : Unbound name scopes) : Holds name (.fault .constraint)

mutual
inductive Evaluates : Expression model → Result model → Prop where
  | constant (scalar : IntegerScalar.Value model.parameters) :
      Evaluates (.constant scalar) (.value (.integer scalar))
  | readFault (place : Place model) (fault : Fault model) (located : Locates place (.error fault)) :
      Evaluates (.read place) (.fault fault)
  | read (place : Place model) (target : Address) (result : Result model)
      (located : Locates place (.ok target)) (reading : ReadsElement model memory arrays target result) :
      Evaluates (.read place) result
  | binaryFault (operator : IntegerBinaryOperator) (first second : Expression model)
      (left right : Result model) (fault : Fault model)
      (firstEval : Evaluates first left) (secondEval : Evaluates second right)
      (bad : integerOperands left right = .error fault) :
      Evaluates (.binary operator first second) (.fault fault)
  | binary (operator : IntegerBinaryOperator) (first second : Expression model)
      (left right : Result model) (x y : IntegerScalar.Value model.parameters)
      (result : IntegerScalar.ArithmeticResult model.parameters)
      (firstEval : Evaluates first left) (secondEval : Evaluates second right)
      (good : integerOperands left right = .ok (x, y))
      (arithmetic : IntegerScalar.ArithmeticEvaluation model.parameters policy operator x y result) :
      Evaluates (.binary operator first second) (arithmeticResult result)
  | compareFault (operator : IntegerOperators.Comparison) (first second : Expression model)
      (left right : Result model) (fault : Fault model)
      (firstEval : Evaluates first left) (secondEval : Evaluates second right)
      (bad : integerOperands left right = .error fault) :
      Evaluates (.compare operator first second) (.fault fault)
  | compare (operator : IntegerOperators.Comparison) (first second : Expression model)
      (left right : Result model) (x y result : IntegerScalar.Value model.parameters)
      (firstEval : Evaluates first left) (secondEval : Evaluates second right)
      (good : integerOperands left right = .ok (x, y))
      (compared : IntegerOperators.TypedComparisonEvaluation model.parameters policy operator x y result) :
      Evaluates (.compare operator first second) (.value (.integer result))
  | castFault (type : IntegerType IntegerExtension) (operand : Expression model) (input : Result model)
      (fault : Fault model) (operandEval : Evaluates operand input) (bad : integerOperand input = .error fault) :
      Evaluates (.cast type operand) (.fault fault)
  | cast (type : IntegerType IntegerExtension) (operand : Expression model) (input : Result model)
      (x : IntegerScalar.Value model.parameters) (result : IntegerScalar.CastResult model.parameters)
      (operandEval : Evaluates operand input) (good : integerOperand input = .ok x)
      (conversion : IntegerScalar.CastEvaluation model.parameters policy type x result) :
      Evaluates (.cast type operand) (castResult result)
  | addressFault (place : Place model) (fault : Fault model) (located : Locates place (.error fault)) :
      Evaluates (.addressOf place) (.fault fault)
  | address (place : Place model) (target : Address) (located : Locates place (.ok target)) :
      Evaluates (.addressOf place) (.value (.address target))
  | offsetFault (pointer amount : Expression model) (left right : Result model) (fault : Fault model)
      (pointerEval : Evaluates pointer left) (amountEval : Evaluates amount right)
      (bad : pointerOperands left right = .error fault) :
      Evaluates (.offset pointer amount) (.fault fault)
  | offset (pointer amount : Expression model) (left right : Result model) (target : Address)
      (distance : IntegerScalar.Value model.parameters) (result : Result model)
      (pointerEval : Evaluates pointer left) (amountEval : Evaluates amount right)
      (good : pointerOperands left right = .ok (target, distance))
      (moved : Displaces model memory arrays target distance result) :
      Evaluates (.offset pointer amount) result
  | variable (name : String) (result : Result model) (held : Holds model scopes name result) :
      Evaluates (.variable name) result
  | null : Evaluates .null (.value .null)

inductive Locates : Place model → Except (Fault model) Address → Prop where
  | named (name : String) (result : Except (Fault model) Address)
      (designated : Designates model scopes name result) : Locates (.named name) result
  | element (name : String) (index : Expression model) (base : Except (Fault model) Address)
      (indexResult : Result model) (result : Except (Fault model) Address)
      (designated : Designates model scopes name base) (indexEval : Evaluates index indexResult)
      (indexed : Indexes model memory arrays base indexResult result) :
      Locates (.element name index) result
  | deref (pointer : Expression model) (value : Result model) (pointerEval : Evaluates pointer value) :
      Locates (.deref pointer) (derefTarget value)
end

end Independent

/-! ## Correspondence -/

section Correspondence

variable (model : Model) (policy : SignedConversionPolicy) (memory : State model.characters)
  (arrays : ArrayPointers.Catalog) (scopes : List (Scope model))

theorem readElement_sound (target : Address) :
    ReadsElement model (represent memory) arrays target (readElement model memory arrays target) := by
  cases ranged : ArrayPointers.elementRange memory.storage arrays target.pointer with
  | none =>
      simp only [readElement, ranged]
      refine .missing ?_
      rintro ⟨range, inside⟩
      have found := (ArrayPointers.elementRange_iff _ _ _ _).mpr inside
      rw [ranged] at found
      cases found
  | some range =>
      have inside : ArrayPointers.ElementRange (represent memory).memory arrays target.pointer range :=
        (ArrayPointers.elementRange_iff _ _ _ _).mp ranged
      cases loaded : IntegerMemoryModel.load model memory (elementLvalue target range) with
      | none =>
          simp only [readElement, ranged, loaded]
          refine .refused range inside ?_
          rintro ⟨result, reading⟩
          rw [load_complete _ _ _ _ reading] at loaded
          cases loaded
      | some result =>
          simp only [readElement, ranged, loaded]
          exact .loaded range result inside (load_sound _ _ _ _ loaded)

theorem readElement_complete (target : Address) (result : Result model)
    (reading : ReadsElement model (represent memory) arrays target result) :
    readElement model memory arrays target = result := by
  cases reading with
  | missing absent =>
      cases ranged : ArrayPointers.elementRange memory.storage arrays target.pointer with
      | none => simp only [readElement, ranged]
      | some range => exact absurd ⟨range, (ArrayPointers.elementRange_iff _ _ _ _).mp ranged⟩ absent
  | refused range inside undefined =>
      have ranged := (ArrayPointers.elementRange_iff memory.storage arrays target.pointer range).mpr inside
      cases loaded : IntegerMemoryModel.load model memory (elementLvalue target range) with
      | none => simp only [readElement, ranged, loaded]
      | some result => exact absurd ⟨result, load_sound _ _ _ _ loaded⟩ undefined
  | loaded range loaded inside reading =>
      have ranged := (ArrayPointers.elementRange_iff memory.storage arrays target.pointer range).mpr inside
      simp only [readElement, ranged, load_complete _ _ _ _ reading]

theorem displace_sound (target : Address) (amount : IntegerScalar.Value model.parameters) :
    Displaces model (represent memory) arrays target amount (displace memory arrays target amount) := by
  unfold displace
  cases added : ArrayPointers.add memory.storage arrays target.pointer amount.integer.value with
  | some moved => exact .moved moved ((ArrayPointers.add_iff _ _ _ _ _).mp added)
  | none =>
      refine .refused ?_
      rintro ⟨result, addition⟩
      rw [(ArrayPointers.add_iff _ _ _ _ _).mpr addition] at added
      cases added

theorem displace_complete (target : Address) (amount : IntegerScalar.Value model.parameters)
    (result : Result model) (moved : Displaces model (represent memory) arrays target amount result) :
    displace memory arrays target amount = result := by
  cases moved with
  | moved result added => simp [displace, (ArrayPointers.add_iff _ _ _ _ _).mpr added]
  | refused outside =>
      unfold displace
      cases added : ArrayPointers.add memory.storage arrays target.pointer amount.integer.value with
      | none => rfl
      | some moved => exact absurd ⟨moved, (ArrayPointers.add_iff _ _ _ _ _).mp added⟩ outside

theorem indexAddress_sound (base : Except (Fault model) Address) (index : Result model) :
    Indexes model (represent memory) arrays base index (indexAddress memory arrays base index) := by
  cases base with
  | error fault => exact .base fault index
  | ok target =>
      cases good : integerOperand index with
      | error fault =>
          simp only [indexAddress, good]
          exact .index target index fault good
      | ok amount =>
          cases added : ArrayPointers.add memory.storage arrays target.pointer amount.integer.value with
          | some moved =>
              simp only [indexAddress, good, added]
              have addition : ArrayPointers.Addition (represent memory).memory arrays target.pointer
                  amount.integer.value moved := (ArrayPointers.add_iff _ _ _ _ _).mp added
              exact .moved target index amount moved good addition
          | none =>
              simp only [indexAddress, good, added]
              refine .refused target index amount good ?_
              rintro ⟨result, addition⟩
              rw [(ArrayPointers.add_iff _ _ _ _ _).mpr addition] at added
              cases added

theorem indexAddress_complete (base : Except (Fault model) Address) (index : Result model)
    (result : Except (Fault model) Address)
    (indexed : Indexes model (represent memory) arrays base index result) :
    indexAddress memory arrays base index = result := by
  cases indexed with
  | base fault index => rfl
  | index target index fault bad => simp [indexAddress, bad]
  | moved target index amount result good added =>
      simp [indexAddress, good, (ArrayPointers.add_iff _ _ _ _ _).mpr added]
  | refused target index amount good outside =>
      cases added : ArrayPointers.add memory.storage arrays target.pointer amount.integer.value with
      | none => simp only [indexAddress, good, added]
      | some moved => exact absurd ⟨moved, (ArrayPointers.add_iff _ _ _ _ _).mp added⟩ outside

theorem objectAddress_sound (name : String) :
    Designates model scopes name (objectAddress (resolve scopes name)) := by
  cases found : resolve scopes name with
  | none => exact .unbound ((resolve_none_iff scopes name).mp found)
  | some entity =>
      have resolved := resolve_sound scopes name entity found
      cases entity with
      | pointer value => exact .pointer value resolved
      | object location =>
          cases typed : rootAddress location with
          | none => simpa [objectAddress, typed] using Designates.untyped location resolved typed
          | some target => simpa [objectAddress, typed] using Designates.object location target resolved typed

theorem objectAddress_complete (name : String) (result : Except (Fault model) Address)
    (designated : Designates model scopes name result) : objectAddress (resolve scopes name) = result := by
  cases designated with
  | object location target resolved typed => simp [objectAddress, resolve_complete _ _ _ resolved, typed]
  | untyped location resolved untyped => simp [objectAddress, resolve_complete _ _ _ resolved, untyped]
  | pointer value resolved => simp [objectAddress, resolve_complete _ _ _ resolved]
  | unbound absent => simp [objectAddress, (resolve_none_iff scopes name).mpr absent]

theorem variableResult_sound (name : String) :
    Holds model scopes name (variableResult name (resolve scopes name)) := by
  cases found : resolve scopes name with
  | none => exact .unbound ((resolve_none_iff scopes name).mp found)
  | some entity =>
      have resolved := resolve_sound scopes name entity found
      cases entity with
      | object location => exact .object location resolved
      | pointer value =>
          cases value with
          | none => exact .indeterminate resolved
          | some value => exact .value value resolved

theorem variableResult_complete (name : String) (result : Result model) (held : Holds model scopes name result) :
    variableResult name (resolve scopes name) = result := by
  cases held with
  | value value resolved => simp [variableResult, resolve_complete _ _ _ resolved]
  | indeterminate resolved => simp [variableResult, resolve_complete _ _ _ resolved]
  | object location resolved => simp [variableResult, resolve_complete _ _ _ resolved]
  | unbound absent => simp [variableResult, (resolve_none_iff scopes name).mpr absent]

mutual
theorem evaluate_sound : ∀ expression : Expression model,
    Evaluates model policy (represent memory) arrays scopes expression
      (evaluate model policy memory arrays scopes expression)
  | .constant scalar => .constant scalar
  | .read place => by
      have located := locate_sound place
      rw [evaluate]
      cases found : locate model policy memory arrays scopes place with
      | error fault => exact .readFault place fault (found ▸ located)
      | ok target => exact .read place target _ (found ▸ located) (readElement_sound model memory arrays target)
  | .binary operator first second => by
      have left := evaluate_sound first
      have right := evaluate_sound second
      rw [evaluate]
      cases operands : integerOperands (evaluate model policy memory arrays scopes first)
          (evaluate model policy memory arrays scopes second) with
      | error fault => exact .binaryFault operator first second _ _ fault left right operands
      | ok pair =>
          obtain ⟨x, y⟩ := pair
          exact .binary operator first second _ _ x y _ left right operands
            ((IntegerScalar.binary_iff _ policy _ _ _ _).mp rfl)
  | .compare operator first second => by
      have left := evaluate_sound first
      have right := evaluate_sound second
      rw [evaluate]
      cases operands : integerOperands (evaluate model policy memory arrays scopes first)
          (evaluate model policy memory arrays scopes second) with
      | error fault => exact .compareFault operator first second _ _ fault left right operands
      | ok pair =>
          obtain ⟨x, y⟩ := pair
          exact .compare operator first second _ _ x y _ left right operands
            (IntegerOperators.comparison_sound _ policy _ _ _)
  | .cast type operand => by
      have input := evaluate_sound operand
      rw [evaluate]
      cases good : integerOperand (evaluate model policy memory arrays scopes operand) with
      | error fault => exact .castFault type operand _ fault input good
      | ok x => exact .cast type operand _ x _ input good (IntegerScalar.cast_sound _ policy type x)
  | .addressOf place => by
      have located := locate_sound place
      rw [evaluate]
      cases found : locate model policy memory arrays scopes place with
      | error fault => exact .addressFault place fault (found ▸ located)
      | ok target => exact .address place target (found ▸ located)
  | .offset pointer amount => by
      have left := evaluate_sound pointer
      have right := evaluate_sound amount
      rw [evaluate]
      cases operands : pointerOperands (evaluate model policy memory arrays scopes pointer)
          (evaluate model policy memory arrays scopes amount) with
      | error fault => exact .offsetFault pointer amount _ _ fault left right operands
      | ok pair =>
          obtain ⟨target, distance⟩ := pair
          exact .offset pointer amount _ _ target distance _ left right operands
            (displace_sound model memory arrays target distance)
  | .variable name => .variable name _ (variableResult_sound model scopes name)
  | .null => .null

theorem locate_sound : ∀ place : Place model,
    Locates model policy (represent memory) arrays scopes place
      (locate model policy memory arrays scopes place)
  | .named name => .named name _ (objectAddress_sound model scopes name)
  | .element name index => by
      rw [locate]
      exact .element name index _ _ _ (objectAddress_sound model scopes name) (evaluate_sound index)
        (indexAddress_sound model memory arrays _ _)
  | .deref pointer => by
      rw [locate]
      exact .deref pointer _ (evaluate_sound pointer)
end

mutual
theorem evaluate_complete : ∀ {expression : Expression model} {result : Result model},
    Evaluates model policy (represent memory) arrays scopes expression result →
      evaluate model policy memory arrays scopes expression = result
  | _, _, .constant scalar => rfl
  | _, _, .readFault place fault located => by
      rw [evaluate, locate_complete located]
  | _, _, .read place target result located reading => by
      rw [evaluate, locate_complete located]
      exact readElement_complete model memory arrays target result reading
  | _, _, .binaryFault operator first second left right fault firstEval secondEval bad => by
      rw [evaluate, evaluate_complete firstEval, evaluate_complete secondEval, bad]
  | _, _, .binary operator first second left right x y result firstEval secondEval good arithmetic => by
      rw [evaluate, evaluate_complete firstEval, evaluate_complete secondEval, good]
      simp only [(IntegerScalar.binary_iff _ policy _ _ _ _).mpr arithmetic]
  | _, _, .compareFault operator first second left right fault firstEval secondEval bad => by
      rw [evaluate, evaluate_complete firstEval, evaluate_complete secondEval, bad]
  | _, _, .compare operator first second left right x y result firstEval secondEval good compared => by
      rw [evaluate, evaluate_complete firstEval, evaluate_complete secondEval, good]
      simp only [IntegerOperators.comparison_complete _ policy _ _ _ _ compared]
  | _, _, .castFault type operand input fault operandEval bad => by
      rw [evaluate, evaluate_complete operandEval, bad]
  | _, _, .cast type operand input x result operandEval good conversion => by
      rw [evaluate, evaluate_complete operandEval, good]
      simp only [IntegerScalar.cast_complete _ policy type x result conversion]
  | _, _, .addressFault place fault located => by
      rw [evaluate, locate_complete located]
  | _, _, .address place target located => by
      rw [evaluate, locate_complete located]
  | _, _, .offsetFault pointer amount left right fault pointerEval amountEval bad => by
      rw [evaluate, evaluate_complete pointerEval, evaluate_complete amountEval, bad]
  | _, _, .offset pointer amount left right target distance result pointerEval amountEval good moved => by
      rw [evaluate, evaluate_complete pointerEval, evaluate_complete amountEval, good]
      exact displace_complete model memory arrays target distance result moved
  | _, _, .variable name result held => by
      rw [evaluate]
      exact variableResult_complete model scopes name result held
  | _, _, .null => rfl

theorem locate_complete : ∀ {place : Place model} {result : Except (Fault model) Address},
    Locates model policy (represent memory) arrays scopes place result →
      locate model policy memory arrays scopes place = result
  | _, _, .named name result designated => by
      rw [locate]
      exact objectAddress_complete model scopes name result designated
  | _, _, .element name index base indexResult result designated indexEval indexed => by
      rw [locate, objectAddress_complete model scopes name base designated, evaluate_complete indexEval]
      exact indexAddress_complete model memory arrays base indexResult result indexed
  | _, _, .deref pointer value pointerEval => by
      rw [locate, evaluate_complete pointerEval]
end

/-- **The executable evaluator is the independent judgment.** -/
theorem evaluate_iff (expression : Expression model) (result : Result model) :
    evaluate model policy memory arrays scopes expression = result ↔
      Evaluates model policy (represent memory) arrays scopes expression result :=
  ⟨fun computed => computed ▸ evaluate_sound model policy memory arrays scopes expression,
    evaluate_complete model policy memory arrays scopes⟩

theorem locate_iff (place : Place model) (result : Except (Fault model) Address) :
    locate model policy memory arrays scopes place = result ↔
      Locates model policy (represent memory) arrays scopes place result :=
  ⟨fun computed => computed ▸ locate_sound model policy memory arrays scopes place,
    locate_complete model policy memory arrays scopes⟩

/-- Core expressions are deterministic: every independent derivation has the
executable result. -/
theorem Evaluates.deterministic {expression : Expression model} {first second : Result model}
    (one : Evaluates model policy (represent memory) arrays scopes expression first)
    (two : Evaluates model policy (represent memory) arrays scopes expression second) : first = second :=
  (evaluate_complete model policy memory arrays scopes one).symm.trans
    (evaluate_complete model policy memory arrays scopes two)

end Correspondence

end Mettapedia.Languages.C11.FixedCore
