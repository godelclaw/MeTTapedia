import Mettapedia.Machines.CMemory.Array
import Mettapedia.GSLT.LanguageDef.NativeOpsCScalarRead
import Mettapedia.Languages.C11.IntegerConversion
import Mettapedia.Languages.C11.TypeLanguage

/-!
# Retained scalar expressions with physical block reads

The immutable-local profile resolves identifiers to scalar values. The
current-name profile loads named cells at each reached identifier read, while
declared uninitialized locals shield outer locations. Pointer-array indexing is a typed load
from the actual stored pointer. Field descriptors specify a cell offset and
scalar type, not a field-value oracle. Comparisons and Boolean conversions of
pointers use the shared pointer-equality primitive, whose safety requires live
pointer values. Logical selection keeps the supplied unselected expression
unevaluated. Unsupported syntax or scalar types reach undefined.

Unsigned arithmetic uses the existing UInt32/UInt64 scalar operations and their
declared unsigned widening. Explicit uint32_t and uint64_t casts use the common
C11 modular conversion and evaluate their operand exactly once. A leading
const pointer cast uses the static character-view judgment and retains the
operand's nullable pointer and reached heap. Its type inventory must justify
the native typedefs; byte storage, alignment and lifetime are separate use
obligations. Other pointer conversions remain outside this profile. Signed decimals and unary minus use the common
scalar profile, which rejects signed overflow. Native byte layout, other C promotions and
synchronization remain separate boundaries. This module does not define a second memory or ownership model.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.CMemory.ReadExpressions

open Mettapedia.GSLT.LanguageDef.NativeOps.NativeC
open Mettapedia.GSLT.Logic.AbstractSeparationLogic
open Mettapedia.Languages.C11 hiding CType

inductive FieldKind where
  | byte
  | pointer
  | signedWord
  | word
  | word64
  | boolean
  | embedded
  deriving DecidableEq, Repr

structure Field where
  offset : Nat
  kind : FieldKind
  deriving DecidableEq, Repr


/-- The descriptor selects the same stored scalar type, without value-based
narrowing or repair. -/
def valueKind : CVal → FieldKind
  | .u8 _ => .byte
  | .bool _ => .boolean
  | .i32 _ => .signedWord
  | .u32 _ => .word
  | .u64 _ => .word64
  | .ptr _ => .pointer

abbrev Layout := Name → Option Field
abbrev Environment := Name → Option CVal

def resolved {α : Type} : Option α → CProg CVal α
  | some value => pure value
  | none => CProg.undefined

def scalar (value : CVal) : ScalarRead.Value Ptr := match value with
  | .u8 value => .byte value
  | .bool value => .boolean value
  | .i32 value => .signed value
  | .u32 value => .unsigned value
  | .u64 value => .unsigned64 value
  | .ptr value => .identity value

def cell? : ScalarRead.Value Ptr → Option CVal
  | .byte value => some (.u8 value)
  | .boolean value => some (.bool value)
  | .signed value => some (.i32 value)
  | .unsigned value => some (.u32 value)
  | .unsigned64 value => some (.u64 value)
  | .identity value => some (.ptr value)
  | .identities _ => none
  | .wordRecord _ => none

/-- Pointer truth is a validity-checked comparison, not a test that bypasses
the lifetime contract of the memory primitives. -/
def truth : CVal → CProg CVal Bool
  | .u8 value => pure (value != 0)
  | .bool value => pure value
  | .i32 value => pure (value != 0)
  | .u32 value => pure (value != 0)
  | .u64 value => pure (value != 0)
  | .ptr value => do
      let isNull ← CProg.ptrEq value none
      pure (!isNull)

def pointer : CVal → CProg CVal (Option Ptr)
  | .ptr value => pure value
  | _ => CProg.undefined

def byte : CVal → CProg CVal UInt8
  | .u8 value => pure value
  | _ => CProg.undefined

def word : CVal → CProg CVal UInt32
  | .u32 value => pure value
  | _ => CProg.undefined

def signedWord : CVal → CProg CVal Int32
  | .i32 value => pure value
  | _ => CProg.undefined

def field (layout : Layout) (owner : CVal) (name : Name) : CProg CVal CVal := do
  let owner ← pointer owner
  match owner, layout name with
  | some address, some descriptor =>
      match descriptor.kind with
      | .embedded => CProg.undefined
      | .byte => do
          let value ← CProg.loadU8 (address + descriptor.offset)
          pure (.u8 value)
      | .signedWord => do
          let value ← CProg.loadI32 (address + descriptor.offset)
          pure (.i32 value)
      | .pointer => do
          let value ← CProg.loadPtr (address + descriptor.offset)
          pure (.ptr value)
      | .word => do
          let value ← CProg.loadU32 (address + descriptor.offset)
          pure (.u32 value)
      | .word64 => do
          let value ← CProg.loadU64 (address + descriptor.offset)
          pure (.u64 value)
      | .boolean => do
          let value ← CProg.loadBool (address + descriptor.offset)
          pure (.bool value)
  | _, _ => CProg.undefined

def indexed (array index : CVal) : CProg CVal CVal := do
  let array ← pointer array
  let index ← word index
  match array with
  | some address => CProg.loadPtr (address + index.toNat) >>= fun value => pure (.ptr value)
  | none => CProg.undefined

/-- An explicitly typed array reading retains its unsigned index width and
uses the existing scalar-cell reader at the selected logical offset. Native
element size, bounds, alignment and lifetime remain representation obligations. -/
def indexedScalar (kind : FieldKind) (array index : CVal) : CProg CVal CVal := do
  let array ← pointer array
  let offset ← match index with
    | .u32 value => pure value.toNat
    | .u64 value => pure value.toNat
    | _ => CProg.undefined
  field (fun _ => some ⟨offset, kind⟩) (.ptr array) []

/-- Resolve an aggregate array place without loading its contents. Unsigned
indices retain their full width. Bounds, alignment and live storage belong to
the physical precondition; the stride is a static typed-cell descriptor. -/
def indexedPlace (stride : Nat) (array index : CVal) : CProg CVal Ptr := do
  let array ← pointer array
  let offset ← match index with
    | .u32 value => pure value.toNat
    | .u64 value => pure value.toNat
    | _ => CProg.undefined
  match array with
  | some address => pure (address + offset * stride)
  | none => CProg.undefined

def equal (left right : CVal) : CProg CVal Bool := match left, right with
  | .ptr left, .ptr right => CProg.ptrEq left right
  | _, _ => resolved (ScalarRead.equal? (scalar left) (scalar right))

/-- Numeric unary minus reuses the shared scalar laws; it never treats a
pointer's address as an integer or accepts signed overflow. -/
def negate (value : CVal) : CProg CVal CVal :=
  resolved ((ScalarRead.numericNegation? (scalar value)).bind cell?)

def binary (operator : BinaryOperator) (left right : CVal) : CProg CVal CVal :=
  match operator with
  | .eq => equal left right >>= fun value => pure (.bool value)
  | .ne => equal left right >>= fun value => pure (.bool (!value))
  | .lt =>
      match left, right with
      | .i32 _, _ | _, .i32 _ =>
          resolved ((ScalarRead.numericBinary .lt (scalar left) (scalar right)).bind cell?)
      | .u64 _, _ | _, .u64 _ =>
          resolved ((ScalarRead.numericBinary .lt (scalar left) (scalar right)).bind cell?)
      | _, _ => do
          let left ← word left
          let right ← word right
          pure (.bool (decide (left < right)))
  | other =>
      match left, right with
      | .i32 _, _ | _, .i32 _ =>
          resolved ((ScalarRead.numericBinary other (scalar left) (scalar right)).bind cell?)
      | .u64 _, _ | _, .u64 _ =>
          resolved ((ScalarRead.numericBinary other (scalar left) (scalar right)).bind cell?)
      | _, _ => do
          let left ← word left
          let right ← word right
          resolved ((ScalarRead.unsignedBinary other left right).bind cell?)

/-- A named call service is parameterized by its declared result type. -/
abbrev CallService (α : Type) := Name → List CVal → CProg CVal α

/-- Named calls receive the evaluated arguments in source order. The service
must separately justify its catalogue, conversions, state effects and return
value; it is not authorized merely because a C identifier was recognized.
This order defines the admitted interpreter profile. Applying it to C with
effectful operands needs an evaluation-order or commutation argument. -/
abbrev Calls := CallService CVal

def noCalls : Calls := fun _ _ => CProg.undefined

/-- Whole call arguments are typed snapshots, separate from physical scalar cells. -/
inductive CallArgument where
  | scalar (value : CVal)
  | record (type : CType) (fields : List CVal)
  deriving DecidableEq, Repr

/-- The established scalar call profile remains the default. Whole-value
calls explicitly admit complete record arguments. -/
inductive ArgumentMode where
  | scalar
  | whole
  deriving DecidableEq, Repr

abbrev ArgumentMode.Value : ArgumentMode → Type
  | .scalar => CVal
  | .whole => CallArgument

/-- Call admission fixes the argument representation before evaluating the
source operands. Its implementation must justify effects and returned data. -/
structure ArgumentCall (Result : Type) where
  mode : ArgumentMode := .scalar
  invoke : List mode.Value → CProg CVal Result

/-- The complete source range is read before any callee parameter writes. -/
def snapshotRecord (type : CType) (source : Ptr) (extent : Nat) :
    CProg CVal CallArgument := do
  let fields ← CProg.loadCells source extent
  pure (.record type fields)

/-- Embedded-field addresses do not read an aggregate as a scalar cell.
The offset is admitted by the layout; validity and ownership remain obligations
of the program's physical execution contract. -/
def fieldAddress (layout : Layout) (owner : CVal) (name : Name) : CProg CVal Ptr := do
  let owner ← pointer owner
  match owner, layout name with
  | some owner, some descriptor => pure (owner + descriptor.offset)
  | _, _ => CProg.undefined

/- The recursive operands and field/index names come from the supplied AST.
No successful preparation or scan template is substituted for them. -/
/-- Resolution occurs at each source identifier read and may perform a typed
load. It is distinct from calling a source function or caching a value. -/
abbrev NameReads := Name → CProg CVal CVal
abbrev Locations := Name → Option (Ptr × FieldKind)

/-- A named stored scalar reuses the physical field reader at its supplied
location. Embedded objects remain addressable through separate object operations. -/
def located (locations : Locations) : NameReads := fun name =>
  match locations name with
  | some (address, kind) => field (fun _ => some ⟨0, kind⟩) (.ptr (some address)) name
  | none => CProg.undefined

/-- Declared but uninitialized locals shield same-spelled stored names.
Only names outside that local inventory use the supplied current locations. -/
def localOrLocated (environment : Environment) (declared : Name → Bool)
    (locations : Locations) : NameReads := fun name =>
  match environment name with
  | some value => pure value
  | none => if declared name then CProg.undefined else located locations name

/-- Address and size operations are separate from rvalue reads. The place
lookup establishes local object identities. Pointer operands are evaluated
by the common reader, while sizeof uses only retained type information. Empty providers retain the established scalar-only profile. -/
structure ObjectReads where
  place : Option (Name → Option Ptr) := none
  size : CExpr → Option CVal := fun _ => none
  fields : Option (CExpr → Bool → Layout) := none
  /-- Static array-member admission selects address decay of an embedded
  field. A pointer-valued field still loads its stored pointer normally. -/
  arrayField : CExpr → Bool → Name → Bool := fun _ _ _ => false
  /-- The static array operand determines its effective element type.
  Absent metadata retains the original pointer-array/UInt32 profile. -/
  indexKind : Option (CExpr → Option FieldKind) := none
  /-- Aggregate lvalues need their statically admitted logical cell stride.
  This neither reads an element nor guesses its size from pointer contents. -/
  indexStride : CExpr → Option Nat := fun _ => none
  /-- Static admission of a complete record lvalue. This does not read it. -/
  record : CExpr → Option (CType × Nat) := fun _ => none
  /-- Explicit whole-argument calls coexist with the established scalar service.
  Missing admission retains the original call path. -/
  argumentCalls : Name → Option (ArgumentCall CVal) := fun _ => none
  /-- Elaborated source types are static data, not a predicate on reached values.
  The source profile must justify its declarations and native typedef mapping. -/
  sourceType : CExpr → Option Mettapedia.Languages.C11.CType := fun _ => none
  targetType : CType → Option Mettapedia.Languages.C11.CType := fun _ => none

/-- A static object profile selects descriptors using the actual owner syntax
and the dot/arrow distinction. The default preserves the existing single-layout
profile. Descriptor selection does not evaluate the owner or inspect a value. -/
def ObjectReads.fieldLayout (objects : ObjectReads) (fallback : Layout)
    (owner : CExpr) (throughPointer : Bool) : Layout :=
  match objects.fields with
  | none => fallback
  | some fields => fields owner throughPointer

/-- Array members decay to their own address. The field must be an
embedded object; its first cell is never read as an invented pointer value.
This does not establish array bounds, lifetime or native byte offsets. -/
def arrayFieldAddress (layout : Layout) (owner : CVal) (name : Name) : CProg CVal CVal := do
  let descriptor ← resolved (layout name)
  if descriptor.kind = .embedded then
    let address ← fieldAddress layout owner name
    pure (.ptr (some address))
  else CProg.undefined

/-- Only an explicitly admitted array member receives address decay. The
scalar default, including refusal to read a whole embedded record, is kept. -/
def ObjectReads.fieldRead (objects : ObjectReads) (fallback : Layout)
    (owner : CExpr) (throughPointer : Bool) (actual : CVal) (name : Name) : CProg CVal CVal :=
  if objects.arrayField owner throughPointer name then
    arrayFieldAddress (objects.fieldLayout fallback owner throughPointer) actual name
  else field (objects.fieldLayout fallback owner throughPointer) actual name

/-- Scalar profiles keep the established field operation. Array-address
decay is used only at the statically admitted member, never by inspecting the
stored value or by treating an embedded record as a pointer. -/
@[simp] theorem ObjectReads.fieldRead_of_scalar (objects : ObjectReads) (fallback : Layout)
    (owner : CExpr) (throughPointer : Bool) (actual : CVal) (name : Name)
    (scalar : objects.arrayField owner throughPointer name = false) :
    objects.fieldRead fallback owner throughPointer actual name =
      field (objects.fieldLayout fallback owner throughPointer) actual name := by
  simp only [ObjectReads.fieldRead, scalar, Bool.false_eq_true, ↓reduceIte]

/-- Mathematical integer readout of an admitted scalar. A pointer is not an
integer whose value can be guessed from its address. -/
def integerValue? : CVal → Option Int
  | .u8 value => some value.toNat
  | .bool value => some (if value then 1 else 0)
  | .i32 value => some value.toInt
  | .u32 value => some value.toNat
  | .u64 value => some value.toNat
  | .ptr _ => none

/-- Explicit fixed-width unsigned casts use the shared C11 conversion. The
signed policy is unreachable for these destinations. Other destination types
are outside this physical-reader profile, rather than public language failure. -/
def unsignedCast (type : CType) (value : CVal) : CProg CVal CVal := do
  let input ← resolved (integerValue? value)
  if type = ⟨"uint32_t".toList, 0⟩ then
    match convertInteger (signalingPolicy 0) input (.integer (.unsigned 32 (by decide))) with
    | .value result => pure (.u32 (UInt32.ofNat result.toNat))
    | .signal _ => CProg.undefined
  else if type = ⟨"uint64_t".toList, 0⟩ then
    match convertInteger (signalingPolicy 0) input (.integer (.unsigned 64 (by decide))) with
    | .value result => pure (.u64 (UInt64.ofNat result.toNat))
    | .signal _ => CProg.undefined
  else CProg.undefined

/-- Retain every existing pointee qualifier when adding const. Unsupported
nonpointer destinations have no pointer view; no qualifier is erased. -/
def constPointee? : Mettapedia.Languages.C11.CType → Option Mettapedia.Languages.C11.CType
  | .pointer qualifiers pointee => some (.pointer { qualifiers with const := true } pointee)
  | _ => none

/-- The static permission is checked against the independent C11 character
view relation. A native uint8_t-to-unsigned-char mapping is an explicit source
profile fact. The reached pointer is preserved, including null and allocation
identity; this operation performs no read, callback or lifetime assertion. -/
def readonlyPointerCast (source target : Mettapedia.Languages.C11.CType)
    (value : CVal) : CProg CVal CVal :=
  if CharacterPointerViews.accepted source target then
    match value with
    | .ptr pointer => pure (.ptr pointer)
    | _ => CProg.undefined
  else CProg.undefined

/-- Only static source/type-name information selects a view. Actual operand
execution has already occurred; type refusal cannot erase its effects. -/
def ObjectReads.readonlyCast (objects : ObjectReads) (type : CType)
    (operand : CExpr) (value : CVal) : CProg CVal CVal :=
  match objects.sourceType operand, (objects.targetType type).bind constPointee? with
  | some source, some target => readonlyPointerCast source target value
  | _, _ => CProg.undefined

mutual
 def expressionWithNames (names : NameReads) (calls : Calls) (layout : Layout)
     (operand : CExpr) (objects : ObjectReads := {}) : CProg CVal CVal := match operand with
  | .identifier name => names name
  | .decimal value => resolved ((ScalarRead.signedDecimal? value).bind cell?)
  | .unsignedInteger value =>
      resolved (if value < 2 ^ 32 then some (.u32 (UInt32.ofNat value)) else none)
  | .word value => pure (.u64 (UInt64.ofNat value.toNat))
  | .bool value => pure (.bool value)
  | .null => pure (.ptr none)
  | .call name arguments => match objects.argumentCalls name with
      | none => do
          let values ← argumentsWithNames names calls layout arguments objects .scalar
          calls name values
      | some service => do
          let values ← argumentsWithNames names calls layout arguments objects service.mode
          service.invoke values
  | .unary .address (.field record name true) => do
      let owner ← expressionWithNames names calls layout record objects
      let address ← fieldAddress (objects.fieldLayout layout record true) owner name
      pure (.ptr (some address))
  | .unary .address operand => match objects.place with
      | none => CProg.undefined
      | some _ => do
          let address ← placeWithNames names calls layout operand objects
          pure (.ptr (some address))
  | .sizeOfExpr operand => resolved (objects.size (.sizeOfExpr operand))
  | .sizeOf type => resolved (objects.size (.sizeOf type))
  | .cast type operand => do
      let value ← expressionWithNames names calls layout operand objects
      unsignedCast type value
  | .castPointeeConst type operand => do
      let value ← expressionWithNames names calls layout operand objects
      objects.readonlyCast type operand value
  | .unary .negate operand => do
      let value ← expressionWithNames names calls layout operand objects
      negate value
  | .unary .not operand => do
      let value ← expressionWithNames names calls layout operand objects
      let selected ← truth value
      pure (.bool (!selected))
  | .field record name true => do
      let owner ← expressionWithNames names calls layout record objects
      objects.fieldRead layout record true owner name
  | .field record name false => match objects.place with
      | none => CProg.undefined
      | some _ => do
          let owner ← placeWithNames names calls layout record objects
          objects.fieldRead layout record false (.ptr (some owner)) name
  | .index array index => do
      let address ← expressionWithNames names calls layout array objects
      let position ← expressionWithNames names calls layout index objects
      match objects.indexKind with
      | none => indexed address position
      | some kinds => match kinds array with
          | some kind => indexedScalar kind address position
          | none => CProg.undefined
  | .binary .and left right => do
      let first ← expressionWithNames names calls layout left objects
      let selected ← truth first
      if selected then do
        let second ← expressionWithNames names calls layout right objects
        let selectedSecond ← truth second
        pure (.bool selectedSecond)
      else pure (.bool false)
  | .binary .or left right => do
      let first ← expressionWithNames names calls layout left objects
      let selected ← truth first
      if selected then pure (.bool true) else do
        let second ← expressionWithNames names calls layout right objects
        let selectedSecond ← truth second
        pure (.bool selectedSecond)
  | .binary operator left right => do
      let first ← expressionWithNames names calls layout left objects
      let second ← expressionWithNames names calls layout right objects
      binary operator first second
  | .conditional condition yes no => do
      let value ← expressionWithNames names calls layout condition objects
      let selected ← truth value
      if selected then expressionWithNames names calls layout yes objects else expressionWithNames names calls layout no objects
  | _ => CProg.undefined
 termination_by structural operand

 def argumentsWithNames (names : NameReads) (calls : Calls) (layout : Layout)
     (arguments : List CExpr) (objects : ObjectReads := {}) (mode : ArgumentMode := .scalar) :
     CProg CVal (List mode.Value) := match arguments with
  | [] => pure []
  | argument :: rest => do
      let first : mode.Value ← (match mode with
        | .scalar => expressionWithNames names calls layout argument objects
        | .whole => match objects.record argument with
            | some (type, extent) => do
                let source ← placeWithNames names calls layout argument objects
                snapshotRecord type source extent
            | none => do
                let value ← expressionWithNames names calls layout argument objects
                pure (CallArgument.scalar value))
      let others ← argumentsWithNames names calls layout rest objects mode
      pure (first :: others)
 termination_by structural arguments

 /-- A place is resolved without reading an aggregate value. Pointer operands
 still use the same scalar reader; recursive source operands are structurally
 smaller. The descriptor's offset remains a logical cell offset. -/
 def placeWithNames (names : NameReads) (calls : Calls) (layout : Layout)
     (operand : CExpr) (objects : ObjectReads := {}) : CProg CVal Ptr := match operand with
  | .identifier name => resolved (objects.place.bind (fun places => places name))
  | .unary .dereference operand => do
      let value ← expressionWithNames names calls layout operand objects
      let address ← pointer value
      resolved address
  | .field record name true => do
      let owner ← expressionWithNames names calls layout record objects
      fieldAddress (objects.fieldLayout layout record true) owner name
  | .field record name false => do
      let owner ← placeWithNames names calls layout record objects
      let descriptor ← resolved ((objects.fieldLayout layout record false) name)
      pure (owner + descriptor.offset)
  | .index array index => do
      let stride ← resolved (objects.indexStride array)
      let address ← expressionWithNames names calls layout array objects
      let position ← expressionWithNames names calls layout index objects
      indexedPlace stride address position
  | _ => CProg.undefined
 termination_by structural operand
end



theorem default_owner_field_layout_is_unchanged (fallback : Layout)
    (owner : CExpr) (throughPointer : Bool) :
    ({} : ObjectReads).fieldLayout fallback owner throughPointer = fallback := rfl

/-- Owner-specific addressing uses the selected record descriptor, even when
the fallback layout gives the same spelling a different offset. -/
theorem addressed_field_uses_owner_descriptor (names : NameReads) (calls : Calls)
    (fallback selected : Layout) (owner : CExpr) (name : Name) (address : Ptr)
    (offset : Nat) (kind : FieldKind) (objects : ObjectReads)
    (typed : objects.fieldLayout fallback owner true = selected)
    (readOwner : expressionWithNames names calls fallback owner objects =
      pure (.ptr (some address)))
    (descriptor : selected name = some ⟨offset, kind⟩) :
    expressionWithNames names calls fallback (.unary .address (.field owner name true)) objects =
      pure (.ptr (some (address + offset))) := by
  rw [expressionWithNames.eq_def]
  dsimp only
  rw [readOwner]
  simp only [Prog.bind_eq, Prog.pure_eq, Prog.ret_bind]
  simp only [typed, fieldAddress, pointer, descriptor, Prog.bind_eq, Prog.pure_eq, Prog.ret_bind]

/-- Dot addressing obtains the object's place and then its owner-specific
descriptor; it does not read the aggregate as a scalar. -/
theorem dot_place_uses_owner_descriptor (names : NameReads) (calls : Calls)
    (fallback selected : Layout) (owner : CExpr) (name : Name) (address : Ptr)
    (offset : Nat) (kind : FieldKind) (objects : ObjectReads)
    (typed : objects.fieldLayout fallback owner false = selected)
    (ownerPlace : placeWithNames names calls fallback owner objects = pure address)
    (descriptor : selected name = some ⟨offset, kind⟩) :
    placeWithNames names calls fallback (.field owner name false) objects =
      pure (address + offset) := by
  rw [placeWithNames.eq_def]
  dsimp only
  rw [ownerPlace]
  simp only [Prog.bind_eq, Prog.pure_eq, Prog.ret_bind]
  rw [typed, descriptor]
  rfl


/-- sizeof consults its retained type provider without evaluating the operand,
reading a name or calling a source function. -/
theorem size_retains_unevaluated_operand (names : NameReads) (calls : Calls)
    (layout : Layout) (objects : ObjectReads) (operand : CExpr) (value : CVal)
    (sized : objects.size (.sizeOfExpr operand) = some value) :
    expressionWithNames names calls layout (.sizeOfExpr operand) objects = pure value := by
  simp only [expressionWithNames.eq_def, sized, resolved]

/-- Unsupported sizeof has no invented default size. -/
theorem default_size_is_not_invented (names : NameReads) (calls : Calls)
    (layout : Layout) (operand : CExpr) :
    expressionWithNames names calls layout (.sizeOfExpr operand) = CProg.undefined := rfl

/-- Addressing a supplied local object does not perform an rvalue read. -/
theorem supplied_object_address_skips_rvalue (names : NameReads) (calls : Calls)
    (layout : Layout) (name : Name) (address : Ptr) :
    expressionWithNames names calls layout (.unary .address (.identifier name))
      { place := some (fun _ => some address) } = pure (.ptr (some address)) := rfl

/-- An object provider does not force an unchosen operand. -/
theorem object_profile_false_and_skips_operand (names : NameReads) (calls : Calls)
    (layout : Layout) (objects : ObjectReads) (operand : CExpr) :
    expressionWithNames names calls layout (.binary .and (.bool false) operand) objects =
      pure (.bool false) := rfl

/-- Immutable local values retain their original public interpreter profile. -/
def expressionWith (calls : Calls) (layout : Layout) (environment : Environment)
    (operand : CExpr) : CProg CVal CVal :=
  expressionWithNames (fun name => resolved (environment name)) calls layout operand

def argumentsWith (calls : Calls) (layout : Layout) (environment : Environment)
    (arguments : List CExpr) : CProg CVal (List CVal) :=
  argumentsWithNames (fun name => resolved (environment name)) calls layout arguments

/-- The existing expression equation remains the API of the immutable-local profile. -/
theorem expressionWith_equation (calls : Calls) (layout : Layout) (environment : Environment)
    (operand : CExpr) : expressionWith calls layout environment operand = (match operand with
  | .identifier name => resolved (environment name)
  | .decimal value => resolved ((ScalarRead.signedDecimal? value).bind cell?)
  | .unsignedInteger value =>
      resolved (if value < 2 ^ 32 then some (.u32 (UInt32.ofNat value)) else none)
  | .word value => pure (.u64 (UInt64.ofNat value.toNat))
  | .bool value => pure (.bool value)
  | .null => pure (.ptr none)
  | .call name arguments => do
      let values ← argumentsWith calls layout environment arguments
      calls name values
  | .cast type operand => do
      let value ← expressionWith calls layout environment operand
      unsignedCast type value
  | .castPointeeConst _ operand => do
      let _ ← expressionWith calls layout environment operand
      CProg.undefined
  | .unary .address (.field record name true) => do
      let owner ← expressionWith calls layout environment record
      let address ← fieldAddress layout owner name
      pure (.ptr (some address))
  | .unary .negate operand => do
      let value ← expressionWith calls layout environment operand
      negate value
  | .unary .not operand => do
      let value ← expressionWith calls layout environment operand
      let selected ← truth value
      pure (.bool (!selected))
  | .field record name true => do
      let owner ← expressionWith calls layout environment record
      field layout owner name
  | .index array index => do
      let address ← expressionWith calls layout environment array
      let position ← expressionWith calls layout environment index
      indexed address position
  | .binary .and left right => do
      let first ← expressionWith calls layout environment left
      let selected ← truth first
      if selected then do
        let second ← expressionWith calls layout environment right
        let selectedSecond ← truth second
        pure (.bool selectedSecond)
      else pure (.bool false)
  | .binary .or left right => do
      let first ← expressionWith calls layout environment left
      let selected ← truth first
      if selected then pure (.bool true) else do
        let second ← expressionWith calls layout environment right
        let selectedSecond ← truth second
        pure (.bool selectedSecond)
  | .binary operator left right => do
      let first ← expressionWith calls layout environment left
      let second ← expressionWith calls layout environment right
      binary operator first second
  | .conditional condition yes no => do
      let value ← expressionWith calls layout environment condition
      let selected ← truth value
      if selected then expressionWith calls layout environment yes else expressionWith calls layout environment no
  | _ => CProg.undefined) := by
  cases operand <;> try rfl
  case unary operator operand =>
    cases operator <;> try rfl
    case address =>
      cases operand <;> try rfl
      case field record name throughPointer => cases throughPointer <;> rfl
  case binary operator left right => cases operator <;> rfl
  case field record name throughPointer => cases throughPointer <;> rfl

theorem argumentsWith_equation (calls : Calls) (layout : Layout) (environment : Environment)
    (arguments : List CExpr) : argumentsWith calls layout environment arguments = (match arguments with
  | [] => pure []
  | argument :: rest => do
      let first ← expressionWith calls layout environment argument
      let others ← argumentsWith calls layout environment rest
      pure (first :: others)) := by
  cases arguments <;> rfl

theorem arguments_with_mapM (calls : Calls) (layout : Layout)
    (environment : Environment) (arguments : List CExpr) :
    argumentsWith calls layout environment arguments =
      arguments.mapM (expressionWith calls layout environment) := by
  induction arguments with
  | nil => rfl
  | cons argument rest ih =>
      rw [argumentsWith_equation, List.mapM_cons]
      dsimp only
      rw [ih]

/-- The default profile admits no foreign calls. Its public argument types
remain those of the original physical expression reader. -/
def expression (layout : Layout) (environment : Environment) (operand : CExpr) : CProg CVal CVal :=
  expressionWith noCalls layout environment operand

/-- Scalar field stores check the actual value tag against the admitted field
before writing. Embedded aggregates are addressable but not scalar-writable. -/
def storeField (layout : Layout) (owner : CVal) (name : Name) (value : CVal) :
    CProg CVal Unit := do
  let descriptor ← resolved (layout name)
  if descriptor.kind = valueKind value then do
    let address ← fieldAddress layout owner name
    CProg.store address value
  else CProg.undefined


theorem cell_scalar (value : CVal) : cell? (scalar value) = some value := by
  cases value <;> rfl

theorem undefined_bind {α β : Type} (next : α → CProg CVal β) :
    (CProg.undefined >>= next) = CProg.undefined := by
  simp only [CProg.undefined, Prog.bind_eq, Prog.call_bind]
  congr 1
  funext impossible
  cases impossible

theorem unsignedCast32_exact (value : CVal) (input : Int)
    (read : integerValue? value = some input) :
    unsignedCast ⟨"uint32_t".toList, 0⟩ value =
      pure (.u32 (UInt32.ofNat (input % powerOfTwo 32).toNat)) := by
  simp only [unsignedCast, read, resolved, Prog.bind_eq, Prog.pure_eq,
    Prog.ret_bind, ↓reduceIte, convertInteger]

theorem unsignedCast64_exact (value : CVal) (input : Int)
    (read : integerValue? value = some input) :
    unsignedCast ⟨"uint64_t".toList, 0⟩ value =
      pure (.u64 (UInt64.ofNat (input % powerOfTwo 64).toNat)) := by
  simp only [unsignedCast, read, resolved, Prog.bind_eq, Prog.pure_eq,
    Prog.ret_bind, ↓reduceIte, convertInteger]
  rfl

theorem unsignedCast32_of_u64 (value : UInt64) :
    unsignedCast ⟨"uint32_t".toList, 0⟩ (.u64 value) =
      pure (.u32 (UInt32.ofNat value.toNat)) := by
  rw [unsignedCast32_exact _ _ rfl]
  change (pure (CVal.u32 (UInt32.ofNat (value.toNat % 2 ^ 32))) : CProg CVal CVal) = _
  rw [UInt32.ofNat_mod_size]

private theorem unsigned32_remainder_readout (input : Int) :
    ((UInt32.ofNat (input % powerOfTwo 32).toNat).toNat : Int) =
      input % powerOfTwo 32 := by
  have nonnegative := Int.emod_nonneg input (ne_of_gt (powerOfTwo_positive 32))
  have bound := Int.emod_lt_of_pos input (powerOfTwo_positive 32)
  have limit : (input % powerOfTwo 32).toNat < 2 ^ 32 := by
    norm_num [powerOfTwo] at *
    omega
  rw [UInt32.toNat_ofNat', Nat.mod_eq_of_lt limit]
  exact Int.toNat_of_nonneg nonnegative

private theorem unsigned64_remainder_readout (input : Int) :
    ((UInt64.ofNat (input % powerOfTwo 64).toNat).toNat : Int) =
      input % powerOfTwo 64 := by
  have nonnegative := Int.emod_nonneg input (ne_of_gt (powerOfTwo_positive 64))
  have bound := Int.emod_lt_of_pos input (powerOfTwo_positive 64)
  have limit : (input % powerOfTwo 64).toNat < 2 ^ 64 := by
    norm_num [powerOfTwo] at *
    omega
  rw [UInt64.toNat_ofNat', Nat.mod_eq_of_lt limit]
  exact Int.toNat_of_nonneg nonnegative

/-- No operand-fit premise: overflowing and negative integers use exactly
C11's unsigned reduction relation. -/
theorem unsignedCast32_conversion (policy : SignedConversionPolicy) (input : Int) :
    IntegerConverts policy input (.integer (.unsigned 32 (by decide)))
      (.value ((UInt32.ofNat (input % powerOfTwo 32).toNat).toNat : Int)) := by
  rw [unsigned32_remainder_readout]
  exact convertInteger_sound policy input (.integer (.unsigned 32 (by decide)))

theorem unsignedCast64_conversion (policy : SignedConversionPolicy) (input : Int) :
    IntegerConverts policy input (.integer (.unsigned 64 (by decide)))
      (.value ((UInt64.ofNat (input % powerOfTwo 64).toNat).toNat : Int)) := by
  rw [unsigned64_remainder_readout]
  exact convertInteger_sound policy input (.integer (.unsigned 64 (by decide)))

theorem unsignedCast_pointer_unsupported (type : CType) (pointer : Option Ptr) :
    unsignedCast type (.ptr pointer) = CProg.undefined := by
  simp only [unsignedCast, integerValue?, resolved]
  exact undefined_bind _

theorem unsignedCast_destination_unsupported (type : CType) (value : CVal)
    (not32 : type ≠ ⟨"uint32_t".toList, 0⟩)
    (not64 : type ≠ ⟨"uint64_t".toList, 0⟩) :
    unsignedCast type value = CProg.undefined := by
  cases value <;>
    simp only [unsignedCast, integerValue?, resolved, Prog.bind_eq, Prog.pure_eq,
      Prog.ret_bind, if_neg not32, if_neg not64]
  exact undefined_bind _

namespace UnsignedCastControls

theorem overflow_keeps_low_32_bits :
    unsignedCast ⟨"uint32_t".toList, 0⟩ (.u64 4294967303) = pure (.u32 7) := rfl

theorem negative_integer_reduces_unsigned :
    unsignedCast ⟨"uint32_t".toList, 0⟩ (.i32 (-1)) = pure (.u32 4294967295) := rfl

theorem narrow_integer_widens_without_loss :
    unsignedCast ⟨"uint64_t".toList, 0⟩ (.u32 4294967295) =
      pure (.u64 4294967295) := rfl

theorem unsigned_pointer_destination_is_unsupported :
    unsignedCast ⟨"uint32_t".toList, 1⟩ (.u64 7) = CProg.undefined := rfl

theorem signed_destination_is_not_unsigned_reduction :
    unsignedCast ⟨"int32_t".toList, 0⟩ (.u64 4294967303) = CProg.undefined := rfl

end UnsignedCastControls

/-- A cast evaluates the authored operand once and converts its reached value.
The conversion neither invokes the operand again nor moves its effects. -/
theorem cast_keeps_reached_operand (names : NameReads) (calls : Calls)
    (layout : Layout) (objects : ObjectReads) (type : CType) (operand : CExpr) :
    expressionWithNames names calls layout (.cast type operand) objects =
      (expressionWithNames names calls layout operand objects >>= unsignedCast type) := rfl

theorem immutable_cast_keeps_reached_operand (calls : Calls) (layout : Layout)
    (environment : Environment) (type : CType) (operand : CExpr) :
    expressionWith calls layout environment (.cast type operand) =
      (expressionWith calls layout environment operand >>= unsignedCast type) := rfl

namespace UnsignedCastControls

/-- The actual source reader retains exactly one operand store before narrowing. -/
theorem effectful_operand_occurs_once (address : Ptr) :
    expressionWithNames
      (fun _ => CProg.store address (.u32 1) >>= fun _ => pure (.u64 4294967303))
      noCalls (fun _ => none)
      (.cast ⟨"uint32_t".toList, 0⟩ (.identifier "operand".toList)) =
      (CProg.store address (.u32 1) >>= fun _ => pure (.u32 7)) := rfl

/-- Unsupported destination admission does not erase the already reached
operand effect. It remains outside this physical-reader profile. -/
theorem unsupported_cast_keeps_operand_effect (address : Ptr) :
    expressionWithNames
      (fun _ => CProg.store address (.u32 1) >>= fun _ => pure (.u64 4294967303))
      noCalls (fun _ => none)
      (.cast ⟨"uint32_t".toList, 1⟩ (.identifier "operand".toList)) =
      (CProg.store address (.u32 1) >>= fun _ => CProg.undefined) := rfl

end UnsignedCastControls

/-- Array lvalue resolution evaluates each authored operand once and keeps
its admitted cell stride. It performs no aggregate value read. -/
theorem described_index_place_keeps_operands (names : NameReads) (calls : Calls)
    (layout : Layout) (objects : ObjectReads) (array index : CExpr) (stride : Nat)
    (described : objects.indexStride array = some stride) :
    placeWithNames names calls layout (.index array index) objects =
      (expressionWithNames names calls layout array objects >>= fun address =>
        expressionWithNames names calls layout index objects >>= fun position =>
          indexedPlace stride address position) := by
  rw [placeWithNames.eq_def]
  simp only [described, resolved, Prog.bind_eq, Prog.pure_eq, Prog.ret_bind]

theorem missing_index_place_is_not_guessed (names : NameReads) (calls : Calls)
    (layout : Layout) (objects : ObjectReads) (array index : CExpr)
    (missing : objects.indexStride array = none) :
    placeWithNames names calls layout (.index array index) objects = CProg.undefined := by
  rw [placeWithNames.eq_def]
  simp only [missing, resolved, Prog.bind_eq]
  exact undefined_bind _

theorem indexed_place_retains_stride (array : Ptr) (index : UInt32) (stride : Nat) :
    indexedPlace stride (.ptr (some array)) (.u32 index) =
      pure (array + index.toNat * stride) := rfl

theorem indexed_place_wide_index (array : Ptr) (index : UInt64) (stride : Nat) :
    indexedPlace stride (.ptr (some array)) (.u64 index) =
      pure (array + index.toNat * stride) := rfl

theorem indexed_place_null_is_undefined (index : UInt32) (stride : Nat) :
    indexedPlace stride (.ptr none) (.u32 index) = CProg.undefined := rfl

theorem indexed_place_wrong_index_type (array : Ptr) (stride : Nat) :
    indexedPlace stride (.ptr (some array)) (.ptr none) = CProg.undefined := by
  simp only [indexedPlace, pointer, Prog.bind_eq, Prog.pure_eq, Prog.ret_bind]
  exact undefined_bind _

theorem field_address_retains_offset (layout : Layout) (owner : Ptr) (name : Name)
    (offset : Nat) (kind : FieldKind) (selected : layout name = some ⟨offset, kind⟩) :
    fieldAddress layout (.ptr (some owner)) name = pure (owner + offset) := by
  simp only [fieldAddress, pointer, Prog.pure_eq, Prog.bind_eq, Prog.ret_bind, selected]

theorem field_store_retains_actual_value (layout : Layout) (owner : Ptr) (name : Name)
    (offset : Nat) (value : CVal) (selected : layout name = some ⟨offset, valueKind value⟩) :
    storeField layout (.ptr (some owner)) name value = CProg.store (owner + offset) value := by
  simp only [storeField, selected, resolved, Prog.pure_eq, Prog.bind_eq, Prog.ret_bind, if_true]
  rw [field_address_retains_offset layout owner name offset (valueKind value) selected]
  rfl

theorem call_retains_ordered_arguments (calls : Calls) (layout : Layout)
    (environment : Environment) (name : Name) (arguments : List CExpr) :
    expressionWith calls layout environment (.call name arguments) =
      (argumentsWith calls layout environment arguments >>= calls name) := by
  rw [expressionWith_equation]

theorem embedded_field_is_not_a_scalar_read (layout : Layout) (owner : Ptr) (name : Name)
    (offset : Nat) (selected : layout name = some ⟨offset, .embedded⟩) :
    field layout (.ptr (some owner)) name = CProg.undefined := by
  simp only [field, pointer, Prog.pure_eq, Prog.bind_eq, Prog.ret_bind, selected]

theorem embedded_field_is_not_a_scalar_store (layout : Layout) (owner : Ptr) (name : Name)
    (offset : Nat) (value : CVal) (selected : layout name = some ⟨offset, .embedded⟩) :
    storeField layout (.ptr (some owner)) name value = CProg.undefined := by
  cases value <;>
    simp only [storeField, selected, resolved, valueKind, Prog.pure_eq, Prog.bind_eq,
      Prog.ret_bind, reduceCtorEq, if_false]

theorem pointer_equality_is_primitive (left right : Option Ptr) :
    equal (.ptr left) (.ptr right) = CProg.ptrEq left right := rfl

theorem pointer_truth_is_primitive (value : Option Ptr) :
    truth (.ptr value) = (CProg.ptrEq value none >>= fun isNull => pure (!isNull)) := rfl

theorem pointer_field_uses_actual_offset (layout : Layout) (owner : Ptr) (name : Name)
    (offset : Nat) (selected : layout name = some ⟨offset, .pointer⟩) :
    field layout (.ptr (some owner)) name =
      (CProg.loadPtr (owner + offset) >>= fun value => pure (.ptr value)) := by
  simp only [field, pointer, Prog.pure_eq, Prog.bind_eq, Prog.ret_bind, selected]

theorem word_field_uses_actual_offset (layout : Layout) (owner : Ptr) (name : Name)
    (offset : Nat) (selected : layout name = some ⟨offset, .word⟩) :
    field layout (.ptr (some owner)) name =
      (CProg.loadU32 (owner + offset) >>= fun value => pure (.u32 value)) := by
  simp only [field, pointer, Prog.pure_eq, Prog.bind_eq, Prog.ret_bind, selected]

theorem signed_field_uses_actual_offset (layout : Layout) (owner : Ptr) (name : Name)
    (offset : Nat) (selected : layout name = some ⟨offset, .signedWord⟩) :
    field layout (.ptr (some owner)) name =
      (CProg.loadI32 (owner + offset) >>= fun value => pure (.i32 value)) := by
  simp only [field, pointer, Prog.pure_eq, Prog.bind_eq, Prog.ret_bind, selected]

theorem word64_field_uses_actual_offset (layout : Layout) (owner : Ptr) (name : Name)
    (offset : Nat) (selected : layout name = some ⟨offset, .word64⟩) :
    field layout (.ptr (some owner)) name =
      (CProg.loadU64 (owner + offset) >>= fun value => pure (.u64 value)) := by
  simp only [field, pointer, Prog.pure_eq, Prog.bind_eq, Prog.ret_bind, selected]

/-- Boolean fields retain the typed heap load at their actual descriptor
rather than accepting an arbitrary scalar as a truth value. -/
theorem boolean_field_uses_actual_offset (layout : Layout) (owner : Ptr) (name : Name)
    (offset : Nat) (selected : layout name = some ⟨offset, .boolean⟩) :
    field layout (.ptr (some owner)) name =
      (CProg.loadBool (owner + offset) >>= fun value => pure (.bool value)) := by
  simp only [field, pointer, Prog.pure_eq, Prog.bind_eq, Prog.ret_bind, selected]

/-- A nullable owner does not acquire storage by selecting a field descriptor. -/
theorem null_owner_field_is_undefined (layout : Layout) (name : Name) :
    field layout (.ptr none) name = CProg.undefined := by
  simp only [field, pointer, Prog.pure_eq, Prog.bind_eq, Prog.ret_bind]

theorem index_uses_actual_pointer_and_word (array : Ptr) (index : UInt32) :
    indexed (.ptr (some array)) (.u32 index) =
      (CProg.loadPtr (array + index.toNat) >>= fun value => pure (.ptr value)) := rfl

theorem false_and_skips_arbitrary_operand (layout : Layout) (environment : Environment)
    (operand : CExpr) :
    expression layout environment (.binary .and (.bool false) operand) =
      pure (.bool false) := rfl

theorem true_or_skips_arbitrary_operand (layout : Layout) (environment : Environment)
    (operand : CExpr) :
    expression layout environment (.binary .or (.bool true) operand) =
      pure (.bool true) := rfl

theorem conditional_false_retains_selected_operand (layout : Layout)
    (environment : Environment) (yes no : CExpr) :
    expression layout environment (.conditional (.bool false) yes no) =
      expression layout environment no := rfl

theorem conditional_true_retains_selected_operand (layout : Layout)
    (environment : Environment) (yes no : CExpr) :
    expression layout environment (.conditional (.bool true) yes no) =
      expression layout environment yes := rfl

section Preservation

open Mettapedia.GSLT.SeparationAlgebra
open CellPermission

universe u

variable {L : Type u} [Zero L] [Add L] [SepAlgebra L]
  [CellPermission L (Option CVal)]

/-- Field stores use the existing physical footprint and frame rule; the
descriptor supplies the actual offset and matching scalar kind. -/
theorem field_store_rule (layout : Layout) (owner : Ptr) (name : Name)
    (offset : Nat) (value : CVal)
    (selected : layout name = some ⟨offset, valueKind value⟩) :
    CTriple (L := L) (PointsToAny (owner + offset))
      (storeField layout (.ptr (some owner)) name value)
      (fun _ => PointsTo (owner + offset) value) := by
  rw [field_store_retains_actual_value layout owner name offset value selected]
  exact store_spec (owner + offset) value

/-- Every completed execution retains the same physical heap. This property
does not assert safety, progress, or that the returned observation is current. -/
def ReadOnly {α : Type} (program : CProg CVal α) : Prop :=
  ∀ (σ : Heap L) value σ', program.Runs act σ value σ' → σ' = σ

theorem pure_readOnly {α : Type} (value : α) :
    ReadOnly (L := L) (pure value : CProg CVal α) := by
  intro σ result σ' runs
  exact runs.2.symm

theorem undefined_readOnly {α : Type} :
    ReadOnly (L := L) (CProg.undefined : CProg CVal α) := by
  rintro σ value σ' ⟨_, _, impossible, _⟩
  exact False.elim impossible

theorem bind_readOnly {α β : Type} (first : CProg CVal α)
    (next : α → CProg CVal β) (firstReadOnly : ReadOnly (L := L) first)
    (nextReadOnly : ∀ value, ReadOnly (L := L) (next value)) :
    ReadOnly (L := L) (first >>= next) := by
  intro σ result σ' runs
  obtain ⟨value, between, firstRuns, nextRuns⟩ := (Prog.runs_bind _ _ _ _ _ _).mp runs
  exact (nextReadOnly value between result σ' nextRuns).trans
    (firstReadOnly σ value between firstRuns)

theorem load_readOnly (address : Ptr) :
    ReadOnly (L := L) (CProg.load (V := CVal) address) := by
  rintro σ value σ' ⟨loaded, between, ⟨_, same⟩, _, resultSame⟩
  exact resultSame.symm.trans same

theorem pointer_comparison_readOnly (left right : Option Ptr) :
    ReadOnly (L := L) (CProg.ptrEq (V := CVal) left right) := by
  rintro σ value σ' ⟨loaded, between, ⟨_, same⟩, _, resultSame⟩
  exact resultSame.symm.trans same

theorem load_pointer_readOnly (address : Ptr) :
    ReadOnly (L := L) (CProg.loadPtr address) := by
  apply bind_readOnly _ _ (load_readOnly address)
  intro value
  cases value <;> first | exact pure_readOnly _ | exact undefined_readOnly

theorem load_byte_readOnly (address : Ptr) :
    ReadOnly (L := L) (CProg.loadU8 address) := by
  apply bind_readOnly _ _ (load_readOnly address)
  intro value
  cases value <;> first | exact pure_readOnly _ | exact undefined_readOnly

theorem load_word_readOnly (address : Ptr) :
    ReadOnly (L := L) (CProg.loadU32 address) := by
  apply bind_readOnly _ _ (load_readOnly address)
  intro value
  cases value <;> first | exact pure_readOnly _ | exact undefined_readOnly

theorem load_signed_readOnly (address : Ptr) :
    ReadOnly (L := L) (CProg.loadI32 address) := by
  apply bind_readOnly _ _ (load_readOnly address)
  intro value
  cases value <;> first | exact pure_readOnly _ | exact undefined_readOnly

theorem load_word64_readOnly (address : Ptr) :
    ReadOnly (L := L) (CProg.loadU64 address) := by
  apply bind_readOnly _ _ (load_readOnly address)
  intro value
  cases value <;> first | exact pure_readOnly _ | exact undefined_readOnly


/-- One shared field-read rule covers each admitted scalar. The precondition
names an actual readable cell at the descriptor offset, not a field oracle. -/
theorem field_read_rule (layout : Layout) (owner : Ptr) (name : Name)
    (offset : Nat) (value : CVal) {P : Heap L → Prop}
    (selected : layout name = some ⟨offset, valueKind value⟩)
    (reads : ∀ σ, P σ →
      CellPermission.read ((σ (owner + offset).block).2 (owner + offset).offset) =
        some (some value)) :
    CTriple P (field layout (.ptr (some owner)) name)
      (fun result σ => result = value ∧ P σ) := by
  cases value <;> simp only [valueKind] at selected
  all_goals
    simp only [field, pointer, Prog.pure_eq, Prog.bind_eq, Prog.ret_bind, selected]
    first
      | refine triple_bind _ (loadU8_rule reads) ?_
      | refine triple_bind _ (loadBool_rule reads) ?_
      | refine triple_bind _ (loadI32_rule reads) ?_
      | refine triple_bind _ (loadU32_rule reads) ?_
      | refine triple_bind _ (loadU64_rule reads) ?_
      | refine triple_bind _ (loadPtr_rule reads) ?_
    intro actual
    apply triple_pure
    intro same
    subst actual
    exact triple_pre _ (fun _ held => ⟨rfl, held⟩) (triple_ret _ _ _)

/-- A source identifier is resolved once; its retained field AST is then read
through the same physical cell contract. -/
theorem expression_field_read_rule (layout : Layout) (environment : Environment)
    (localName fieldName : Name) (owner : Ptr) (offset : Nat) (value : CVal)
    {P : Heap L → Prop}
    (localRead : environment localName = some (.ptr (some owner)))
    (selected : layout fieldName = some ⟨offset, valueKind value⟩)
    (reads : ∀ σ, P σ →
      CellPermission.read ((σ (owner + offset).block).2 (owner + offset).offset) =
        some (some value)) :
    CTriple P (expression layout environment
      (.field (.identifier localName) fieldName true))
      (fun result σ => result = value ∧ P σ) := by
  simp only [expression, expressionWith_equation, localRead, resolved, Prog.pure_eq, Prog.bind_eq, Prog.ret_bind]
  exact field_read_rule layout owner fieldName offset value selected reads

/-- A wide cell behind a narrow descriptor cannot become a successful read by
truncating its value. -/
theorem narrow_descriptor_of_wide_cell_is_unsafe (layout : Layout)
    (owner : Ptr) (name : Name) (offset : Nat) (value : UInt64) (σ : Heap L)
    (selected : layout name = some ⟨offset, .word⟩)
    (holds : CellPermission.read
      ((σ (owner + offset).block).2 (owner + offset).offset) = some (some (.u64 value))) :
    ¬ (field layout (.ptr (some owner)) name).Safe act σ := by
  rw [word_field_uses_actual_offset layout owner name offset selected]
  intro safe
  exact CMemory.Controls.loadU32_of_u64_undefined (owner + offset) value σ holds
    ((Prog.safe_bind _ _ _ _).mp safe).1

theorem unsigned_descriptor_of_signed_cell_is_unsafe (layout : Layout)
    (owner : Ptr) (name : Name) (offset : Nat) (value : Int32) (σ : Heap L)
    (selected : layout name = some ⟨offset, .word⟩)
    (holds : CellPermission.read
      ((σ (owner + offset).block).2 (owner + offset).offset) = some (some (.i32 value))) :
    ¬ (field layout (.ptr (some owner)) name).Safe act σ := by
  rw [word_field_uses_actual_offset layout owner name offset selected]
  intro safe
  exact CMemory.Controls.loadU32_of_i32_undefined (owner + offset) value σ holds
    ((Prog.safe_bind _ _ _ _).mp safe).1

theorem signed_descriptor_of_unsigned_cell_is_unsafe (layout : Layout)
    (owner : Ptr) (name : Name) (offset : Nat) (value : UInt32) (σ : Heap L)
    (selected : layout name = some ⟨offset, .signedWord⟩)
    (holds : CellPermission.read
      ((σ (owner + offset).block).2 (owner + offset).offset) = some (some (.u32 value))) :
    ¬ (field layout (.ptr (some owner)) name).Safe act σ := by
  rw [signed_field_uses_actual_offset layout owner name offset selected]
  intro safe
  exact CMemory.Controls.loadI32_of_u32_undefined (owner + offset) value σ holds
    ((Prog.safe_bind _ _ _ _).mp safe).1

/-- A retained predicate is lifted through a read-only program's actual
executions. In particular this preserves well-formedness, without postulating
it anew after every typed load. -/
theorem triple_preserves_predicate {α : Type} {P R : Heap L → Prop}
    {Q : α → Heap L → Prop} {program : CProg CVal α}
    (readOnly : ReadOnly (L := L) program) (spec : CTriple P program Q) :
    CTriple (fun σ => R σ ∧ P σ) program (fun result σ => R σ ∧ Q result σ) := by
  intro σ holds
  refine ⟨(spec σ holds.2).1, ?_⟩
  intro result σ' runs
  exact ⟨(readOnly σ result σ' runs).symm ▸ holds.1, (spec σ holds.2).2 result σ' runs⟩

end Preservation

universe u

def operands (layout : Layout) (environment : Environment)
    (terms : List CExpr) : CProg CVal (List CVal) :=
  terms.mapM (expression layout environment)

def environmentView (environment : Environment) : ScalarRead.Environment Ptr :=
  fun name => (environment name).map scalar

section Physical

open Mettapedia.GSLT.SeparationAlgebra

variable {L : Type u} [Zero L] [Add L] [SepAlgebra L]
  [CellPermission L (Option CVal)]

/-- The readout comes from permission-bearing cells. A descriptor cannot
reinterpret a different stored scalar type. -/
def fieldView (layout : Layout) (heap : Heap L) : ScalarRead.FieldReader Ptr :=
  fun owner name => do
    let descriptor ← layout name
    let stored ← CellPermission.read
      ((heap (owner + descriptor.offset).block).2 (owner + descriptor.offset).offset)
    let value ← stored
    if valueKind value = descriptor.kind then some (scalar value) else none

theorem field_view_of_read (layout : Layout) (heap : Heap L) (owner : Ptr)
    (name : Name) (offset : Nat) (value : CVal)
    (selected : layout name = some ⟨offset, valueKind value⟩)
    (reads : CellPermission.read
      ((heap (owner + offset).block).2 (owner + offset).offset) = some (some value)) :
    fieldView layout heap owner name = some (scalar value) := by
  simp only [fieldView, selected, bind, Option.bind, reads, if_true]

/-- Sequencing actual operand readers retains their order and the common
heap predicate. This is a rule about the supplied programs, not an oracle
for their results. -/
theorem operands_read_rule (layout : Layout) (environment : Environment)
    {P : Heap L → Prop} {terms : List CExpr} {values : List CVal}
    (reads : List.Forall₂ (fun term value =>
      CTriple P (expression layout environment term)
        (fun result heap => result = value ∧ P heap)) terms values) :
    CTriple P (operands layout environment terms)
      (fun result heap => result = values ∧ P heap) := by
  induction reads with
  | nil =>
      exact triple_pre _ (fun _ held => ⟨rfl, held⟩) (triple_ret _ _ _)
  | @cons term value terms values first rest ih =>
      simp only [operands, List.mapM_cons]
      refine triple_bind _ first fun actual => ?_
      apply triple_pure
      intro same
      subst actual
      refine triple_bind _ ih fun actualTail => ?_
      apply triple_pure
      intro same
      subst actualTail
      exact triple_pre _ (fun _ held => ⟨rfl, held⟩) (triple_ret _ _ _)

theorem field_view_rejects_wrong_cell_type (layout : Layout) (heap : Heap L)
    (owner : Ptr) (name : Name) (offset : Nat) (value : CVal) (kind : FieldKind)
    (selected : layout name = some ⟨offset, kind⟩)
    (reads : CellPermission.read
      ((heap (owner + offset).block).2 (owner + offset).offset) = some (some value))
    (different : valueKind value ≠ kind) :
    fieldView layout heap owner name = none := by
  simp only [fieldView, selected, bind, Option.bind, reads, if_neg different]

theorem missing_layout_is_not_a_field_value (layout : Layout) (heap : Heap L)
    (owner : Ptr) (name : Name) (missing : layout name = none) :
    fieldView layout heap owner name = none := by
  simp only [fieldView, missing, bind, Option.bind]

end Physical


namespace Controls

def emptyLayout : Layout := fun _ => none
def emptyEnvironment : Environment := fun _ => none

/-- The physical/scalar boundary retains high-bit and NUL bytes exactly. -/
theorem byte_scalar_roundtrip (value : UInt8) :
    cell? (scalar (.u8 value)) = some (.u8 value) := rfl

theorem byte_truth_retains_high_bit : truth (.u8 128) = pure true := rfl

theorem nul_byte_is_false : truth (.u8 0) = pure false := rfl

/-- C integer promotions for byte arithmetic are outside this typed read profile. -/
theorem byte_addition_is_not_word_addition (left right : UInt8) :
    ScalarRead.numericBinary (Ptr := Ptr) .add (.byte left) (.byte right) = none := rfl

theorem byte_negation_is_not_unsigned_word_wrap (value : UInt8) :
    ScalarRead.numericNegation? (Ptr := Ptr) (.byte value) = none := rfl

theorem missing_local_is_undefined :
    expression emptyLayout emptyEnvironment (.identifier "missing".toList) =
      CProg.undefined := rfl

theorem unsupported_call_is_not_executed :
    expression emptyLayout emptyEnvironment (.call "sideEffect".toList []) =
      CProg.undefined := rfl

theorem null_array_is_not_empty_success (index : UInt32) :
    indexed (.ptr none) (.u32 index) = CProg.undefined := rfl

theorem wrong_index_type_is_not_repaired (array : Ptr) :
    indexed (.ptr (some array)) (.bool false) = CProg.undefined := by
  simp only [indexed, pointer, word, Prog.pure_eq, Prog.bind_eq, Prog.ret_bind]
  exact undefined_bind _

theorem unknown_field_is_not_guessed (owner : Ptr) :
    field emptyLayout (.ptr (some owner)) "missing".toList = CProg.undefined := rfl

theorem oversized_unsigned_constant_is_not_narrowed :
    expression emptyLayout emptyEnvironment (.unsignedInteger (2 ^ 32)) =
      CProg.undefined := rfl

theorem wide_scalar_is_not_narrowed (value : UInt64) :
    cell? (.unsigned64 value) = some (.u64 value) := rfl

theorem inline_record_is_not_a_physical_cell (fields : List (Name × UInt64)) :
    cell? (.wordRecord fields) = none := rfl

theorem supported_cell_retains_its_width (value : UInt32) :
    cell? (.unsigned value) = some (.u32 value) := rfl

theorem wide_index_is_not_narrowed (array : Ptr) (index : UInt64) :
    indexed (.ptr (some array)) (.u64 index) = CProg.undefined := by
  simp only [indexed, pointer, word, Prog.pure_eq, Prog.bind_eq, Prog.ret_bind]
  exact undefined_bind _

theorem wide_nonzero_truth_is_retained :
    truth (.u64 4294967296) = pure true := rfl

theorem full_word_literal_is_retained :
    expression emptyLayout emptyEnvironment (.word 18446744073709551615) =
      pure (.u64 18446744073709551615) := rfl

theorem mixed_unsigned_addition_retains_wide_result :
    expression emptyLayout emptyEnvironment
      (.binary .add (.word 4294967296) (.unsignedInteger 1)) =
      pure (.u64 4294967297) := rfl

theorem narrow_unsigned_addition_still_wraps :
    expression emptyLayout emptyEnvironment
      (.binary .add (.unsignedInteger 4294967295) (.unsignedInteger 1)) =
      pure (.u32 0) := rfl

theorem mixed_unsigned_order_retains_high_bits :
    expression emptyLayout emptyEnvironment
      (.binary .lt (.word 4294967296) (.unsignedInteger 1)) =
      pure (.bool false) := rfl

theorem unary_minus_reads_signed_decimal :
    expression emptyLayout emptyEnvironment (.unary .negate (.decimal 1)) =
      pure (.i32 (-1)) := rfl

theorem unary_minus_does_not_wrap_signed_minimum :
    expression emptyLayout (fun _ => some (.i32 (-2147483648)))
      (.unary .negate (.identifier ['x'])) = CProg.undefined := rfl

theorem oversized_signed_decimal_is_not_narrowed :
    expression emptyLayout emptyEnvironment (.decimal (2 ^ 31)) = CProg.undefined := rfl

theorem unary_minus_does_not_reinterpret_pointer :
    expression emptyLayout (fun _ => some (.ptr (some ⟨1, 0⟩)))
      (.unary .negate (.identifier ['x'])) = CProg.undefined := rfl

end Controls

namespace NamedReadControls

def emptyEnvironment : Environment := fun _ => none
def emptyLayout : Layout := fun _ => none

theorem resolved_local_shields_arbitrary_reads (environment : Environment)
    (declared : Name → Bool) (locations : Locations) (name : Name) (value : CVal)
    (present : environment name = some value) :
    expressionWithNames (localOrLocated environment declared locations) noCalls emptyLayout
      (.identifier name) = pure value := by
  simp only [expressionWithNames.eq_def, localOrLocated, present]

theorem uninitialized_local_does_not_read_global (name : Name) (locations : Locations) :
    expressionWithNames (localOrLocated emptyEnvironment (fun _ => true) locations)
      noCalls emptyLayout (.identifier name) = CProg.undefined := rfl

theorem pointer_name_is_a_current_load (name : Name) (address : Ptr) :
    expressionWithNames (localOrLocated emptyEnvironment (fun _ => false)
      (fun _ => some (address, .pointer))) noCalls emptyLayout (.identifier name) =
      (CProg.loadPtr address >>= fun value => pure (.ptr value)) := by
  have zero : address + 0 = address := by cases address; rfl
  simp [expressionWithNames.eq_def, localOrLocated, emptyEnvironment,
    located, field, pointer, Prog.bind_eq, Prog.pure_eq, Prog.ret_bind, zero]

theorem preceding_store_does_not_freeze_name (name : Name) (address : Ptr) (value : Option Ptr) :
    (CProg.store address (.ptr value) >>= fun _ =>
      expressionWithNames (localOrLocated emptyEnvironment (fun _ => false)
        (fun _ => some (address, .pointer))) noCalls emptyLayout (.identifier name)) =
      (CProg.store address (.ptr value) >>= fun _ =>
        CProg.loadPtr address >>= fun value => pure (.ptr value)) := by
  rw [pointer_name_is_a_current_load]

theorem false_branch_does_not_resolve_sibling (names : NameReads) (name : Name) :
    expressionWithNames names noCalls emptyLayout
      (.conditional (.bool false) (.identifier name) (.bool true)) = pure (.bool true) := rfl

theorem missing_location_is_not_a_source_function_call (name : Name) (calls : Calls) :
    expressionWithNames (localOrLocated emptyEnvironment (fun _ => false) (fun _ => none))
      calls emptyLayout (.identifier name) = CProg.undefined := rfl

section PhysicalReadout

open Mettapedia.GSLT.SeparationAlgebra
open scoped Mettapedia.GSLT.SeparationAlgebra
open CellPermission
variable {L : Type u} [Zero L] [Add L] [SepAlgebra L]
  [CellPermission L (Option CVal)]

/-- The live typed cell supplies the current pointer value and retains its
permission. This is a physical read contract, not a cached-value readout. -/
theorem pointer_name_reads_owned_cell (name : Name) (address : Ptr) (value : Option Ptr) :
    CTriple (L := L) (PointsTo address (.ptr value))
      (expressionWithNames (localOrLocated emptyEnvironment (fun _ => false)
        (fun _ => some (address, .pointer))) noCalls emptyLayout (.identifier name))
      (fun result heap => result = .ptr value ∧ PointsTo address (.ptr value) heap) := by
  rw [pointer_name_is_a_current_load]
  simp only [Prog.bind_eq, Prog.pure_eq]
  apply triple_bind _ (loadPtr_rule (L := L) (P := PointsTo address (.ptr value))
    (p := address) (q := value) ?_)
  · intro actual
    apply triple_pure
    intro same
    subst actual
    exact triple_pre _ (fun _ held => ⟨rfl, held⟩)
      (triple_ret _ (CVal.ptr value)
        (fun result heap => result = CVal.ptr value ∧ PointsTo address (CVal.ptr value) heap))
  · intro heap held
    apply read_of_pointsTo (F := emp)
    simpa only [sepConj_emp] using held

/-- Storing before a source name read changes its returned value while
preserving the same owned cell. No read is moved across that store. -/
theorem pointer_name_observes_preceding_store (name : Name) (address : Ptr) (value : Option Ptr) :
    CTriple (L := L) (PointsToAny address)
      (CProg.store address (.ptr value) >>= fun _ =>
        expressionWithNames (localOrLocated emptyEnvironment (fun _ => false)
          (fun _ => some (address, .pointer))) noCalls emptyLayout (.identifier name))
      (fun result heap => result = .ptr value ∧ PointsTo address (.ptr value) heap) := by
  simp only [Prog.bind_eq]
  apply triple_bind _ (store_spec (L := L) address (.ptr value))
  intro ignored
  exact pointer_name_reads_owned_cell name address value

/-- A snapshot of an earlier value has a different operation tree from a
current read, even when both eventually happen to print equal values. -/
theorem snapshot_is_not_current_name_read (name : Name) (address : Ptr) (value : Option Ptr) :
    expressionWithNames (localOrLocated emptyEnvironment (fun _ => false)
      (fun _ => some (address, .pointer))) noCalls emptyLayout (.identifier name) ≠
      pure (.ptr value) := by
  rw [pointer_name_is_a_current_load]
  intro equality
  cases equality

end PhysicalReadout

end NamedReadControls

/-- A static descriptor selects the typed load after both authored operands
have been evaluated in their original order. It supplies no value oracle. -/
theorem described_index_keeps_operands (names : NameReads) (calls : Calls) (layout : Layout)
    (objects : ObjectReads) (array index : CExpr) (kinds : CExpr → Option FieldKind)
    (kind : FieldKind) (provided : objects.indexKind = some kinds)
    (described : kinds array = some kind) :
    expressionWithNames names calls layout (.index array index) objects =
      (expressionWithNames names calls layout array objects >>= fun address =>
        expressionWithNames names calls layout index objects >>= fun position =>
          indexedScalar kind address position) := by
  rw [expressionWithNames.eq_def]
  simp only [provided, described]

/-- Missing static element information is not guessed from the returned
array value. Earlier operand effects remain part of the source reading. -/
theorem missing_index_descriptor_is_not_guessed (names : NameReads) (calls : Calls)
    (layout : Layout) (objects : ObjectReads) (array index : CExpr)
    (kinds : CExpr → Option FieldKind) (provided : objects.indexKind = some kinds)
    (missing : kinds array = none) :
    expressionWithNames names calls layout (.index array index) objects =
      (expressionWithNames names calls layout array objects >>= fun _ =>
        expressionWithNames names calls layout index objects >>= fun _ => CProg.undefined) := by
  rw [expressionWithNames.eq_def]
  simp only [provided, missing]

/-! ## Explicit scalar-array controls -/

theorem indexed_word64_keeps_full_index (array : Ptr) (index : UInt64) :
    indexedScalar .word64 (.ptr (some array)) (.u64 index) =
      (CProg.loadU64 (array + index.toNat) >>= fun value => pure (.u64 value)) := rfl

theorem indexed_word64_keeps_narrow_index (array : Ptr) (index : UInt32) :
    indexedScalar .word64 (.ptr (some array)) (.u32 index) =
      (CProg.loadU64 (array + index.toNat) >>= fun value => pure (.u64 value)) := rfl

theorem indexed_pointer_keeps_full_index (array : Ptr) (index : UInt64) :
    indexedScalar .pointer (.ptr (some array)) (.u64 index) =
      (CProg.loadPtr (array + index.toNat) >>= fun value => pure (.ptr value)) := rfl

theorem indexed_signed_index_is_not_guessed (array : Ptr) (index : Int32) (kind : FieldKind) :
    indexedScalar kind (.ptr (some array)) (.i32 index) = CProg.undefined := by
  simp only [indexedScalar, pointer, Prog.pure_eq, Prog.bind_eq, Prog.ret_bind]
  exact undefined_bind _

theorem indexed_null_array_is_not_loaded (index : UInt64) (kind : FieldKind) :
    indexedScalar kind (.ptr none) (.u64 index) = CProg.undefined := rfl

theorem indexed_embedded_value_is_not_a_scalar (array : Ptr) (index : UInt64) :
    indexedScalar .embedded (.ptr (some array)) (.u64 index) = CProg.undefined := rfl


/-! ## Static embedded-array decay -/

theorem array_field_address_uses_member_place (layout : Layout) (owner : Ptr)
    (name : Name) (offset : Nat) (declared : layout name = some ⟨offset, .embedded⟩) :
    arrayFieldAddress layout (.ptr (some owner)) name = pure (.ptr (some (owner + offset))) := by
  simp only [arrayFieldAddress, declared, resolved, Prog.bind_eq, Prog.pure_eq, Prog.ret_bind,
    ↓reduceIte, fieldAddress, pointer]

theorem array_field_does_not_load_pointer_member (layout : Layout) (owner : CVal)
    (name : Name) (offset : Nat) (declared : layout name = some ⟨offset, .pointer⟩) :
    arrayFieldAddress layout owner name = CProg.undefined := by
  simp only [arrayFieldAddress, declared, resolved, Prog.bind_eq, Prog.pure_eq, Prog.ret_bind,
    reduceCtorEq, if_false]

theorem array_field_null_owner_is_undefined (layout : Layout) (name : Name) (offset : Nat)
    (declared : layout name = some ⟨offset, .embedded⟩) :
    arrayFieldAddress layout (.ptr none) name = CProg.undefined := by
  simp only [arrayFieldAddress, declared, resolved, Prog.bind_eq, Prog.pure_eq, Prog.ret_bind,
    ↓reduceIte, fieldAddress, pointer]
  exact undefined_bind _

theorem array_field_unknown_member_is_undefined (layout : Layout) (owner : CVal)
    (name : Name) (absent : layout name = none) :
    arrayFieldAddress layout owner name = CProg.undefined := by
  simp only [arrayFieldAddress, absent, resolved]
  exact undefined_bind _

theorem array_member_retains_owner_expression (names : NameReads) (calls : Calls)
    (fallback : Layout) (objects : ObjectReads) (owner : CExpr) (name : Name)
    (admitted : objects.arrayField owner true name = true) :
    expressionWithNames names calls fallback (.field owner name true) objects =
      (expressionWithNames names calls fallback owner objects >>= fun actual =>
        arrayFieldAddress (objects.fieldLayout fallback owner true) actual name) := by
  rw [expressionWithNames]
  simp only [ObjectReads.fieldRead, admitted, ↓reduceIte]

theorem scalar_member_keeps_default_load (names : NameReads) (calls : Calls)
    (fallback : Layout) (objects : ObjectReads) (owner : CExpr) (name : Name)
    (ordinary : objects.arrayField owner true name = false) :
    expressionWithNames names calls fallback (.field owner name true) objects =
      (expressionWithNames names calls fallback owner objects >>= fun actual =>
        field (objects.fieldLayout fallback owner true) actual name) := by
  rw [expressionWithNames]
  simp only [ObjectReads.fieldRead, ordinary, Bool.false_eq_true, ↓reduceIte]

namespace ArrayDecayControls

def owner : Ptr := ⟨31, 0⟩
def effectCell : Ptr := ⟨32, 0⟩
def record : CExpr := .identifier "schema".toList
def member : CExpr := .field record "source_ids".toList true
def layout : Layout := fun name =>
  if name = "source_ids".toList then some ⟨7, .embedded⟩ else none

def objects : ObjectReads where
  arrayField := fun source through name => match source with
    | .identifier recordName => recordName == "schema".toList && through && name == "source_ids".toList
    | _ => false
  indexKind := some (fun source => match source with
    | .field (.identifier recordName) name true =>
        if recordName == "schema".toList && name == "source_ids".toList then some .word64 else none
    | _ => none)

def names : NameReads := fun name =>
  if name = "schema".toList then pure (.ptr (some owner)) else CProg.undefined

theorem array_address_is_not_loaded_from_its_first_element :
    expressionWithNames names noCalls layout member objects =
      pure (.ptr (some (owner + 7))) := by
  unfold member
  rw [array_member_retains_owner_expression _ _ _ _ _ _ (by decide)]
  change (pure (.ptr (some owner)) >>= fun actual => arrayFieldAddress layout actual _) = _
  simp only [Prog.bind_eq, Prog.pure_eq, Prog.ret_bind]
  exact array_field_address_uses_member_place _ _ _ _ (by rfl)

theorem scalar_array_index_loads_actual_member_cell :
    expressionWithNames names noCalls layout (.index member (.unsignedInteger 2)) objects =
      (CProg.loadU64 (owner + 9) >>= fun value => pure (.u64 value)) := by
  rw [described_index_keeps_operands _ _ _ _ _ _ _ .word64 rfl (by rfl),
    array_address_is_not_loaded_from_its_first_element]
  rfl

theorem absent_array_admission_does_not_invent_pointer :
    expressionWithNames names noCalls layout member = CProg.undefined := by
  change field layout (.ptr (some owner)) "source_ids".toList = _
  exact embedded_field_is_not_a_scalar_read _ _ _ _ (by rfl)

def effectOwner : CExpr := .call "owner".toList []
def effectObjects : ObjectReads :=
  { objects with arrayField := fun source through name => match source with
      | .call function [] => function == "owner".toList && through && name == "source_ids".toList
      | _ => false }
def calls : Calls := fun _ _ => CProg.store effectCell (.u32 1) >>= fun _ =>
  pure (.ptr (some owner))

theorem array_owner_effect_occurs_once :
    expressionWithNames names calls layout
      (.field effectOwner "source_ids".toList true) effectObjects =
      (CProg.store effectCell (.u32 1) >>= fun _ => pure (.ptr (some (owner + 7)))) := by
  rw [array_member_retains_owner_expression _ _ _ _ _ _ (by decide)]
  change ((CProg.store effectCell (.u32 1) >>= fun _ => pure (.ptr (some owner))) >>=
    fun actual => arrayFieldAddress layout actual "source_ids".toList) = _
  simp only [Prog.bind_eq, Prog.bind_assoc, Prog.pure_eq, Prog.ret_bind,
    array_field_address_uses_member_place layout owner "source_ids".toList 7 (by rfl)]

end ArrayDecayControls

end Mettapedia.Machines.CMemory.ReadExpressions

namespace Mettapedia.Machines.CMemory.ReadExpressions
open Mettapedia.GSLT.LanguageDef.NativeOps.NativeC
open Mettapedia.GSLT.Logic.AbstractSeparationLogic
section Ownership
open Mettapedia.GSLT.SeparationAlgebra
open scoped Mettapedia.GSLT.SeparationAlgebra
open CellPermission
universe u
variable {L : Type u} [Zero L] [Add L] [SepAlgebra L] [CellPermission L (Option CVal)]

theorem snapshotRecord_complete (type : CType) (source : Ptr) (fields : List CVal) :
    CTriple (L := L) (Cells source (fields.map some))
      (snapshotRecord type source fields.length)
      (fun value heap => value = .record type fields ∧
        Cells source (fields.map some) heap) := by
  unfold snapshotRecord
  refine triple_bind _ (load_cells source fields) fun actual => ?_
  apply triple_pure
  intro equality
  subst actual
  exact triple_pre _ (fun _ held => ⟨rfl, held⟩)
    (triple_ret act (CallArgument.record type fields) (fun value heap =>
      value = CallArgument.record type fields ∧ Cells source (fields.map some) heap))

/-- Uninitialized source storage cannot be made into an argument by taking
its address or silently skipping the first field. -/
theorem snapshotRecord_uninitialized_unsafe (type : CType) (source : Ptr)
    (extent : Nat) (heap : Heap L)
    (uninitialized : read ((heap source.block).2 source.offset) = some none) :
    ¬ (snapshotRecord type source (extent + 1)).Safe act heap := by
  intro safe
  simp only [snapshotRecord, CProg.loadCells, Prog.bind_eq, Prog.bind_assoc] at safe
  have first := (Prog.safe_bind act _ _ heap).mp safe
  obtain ⟨value, loaded⟩ := first.1.1
  rw [uninitialized] at loaded
  cases loaded
end Ownership

end Mettapedia.Machines.CMemory.ReadExpressions


set_option autoImplicit false

namespace Mettapedia.Machines.CMemory.ReadExpressions
open Mettapedia.GSLT.LanguageDef.NativeOps.NativeC
open Mettapedia.GSLT.Logic.AbstractSeparationLogic

/-- The scalar mode keeps its existing single argument fold, even if static
record metadata is available for a different admitted call. -/
theorem arguments_scalar_cons (names : NameReads) (calls : Calls) (layout : Layout)
    (argument : CExpr) (rest : List CExpr) (objects : ObjectReads) :
    argumentsWithNames names calls layout (argument :: rest) objects .scalar =
      (expressionWithNames names calls layout argument objects >>= fun first =>
        argumentsWithNames names calls layout rest objects .scalar >>= fun others =>
        pure (first :: others)) := by
  rw [argumentsWithNames.eq_def]

theorem arguments_whole_record_cons (names : NameReads) (calls : Calls) (layout : Layout)
    (argument : CExpr) (rest : List CExpr) (objects : ObjectReads)
    (type : CType) (extent : Nat) (admitted : objects.record argument = some (type, extent)) :
    argumentsWithNames names calls layout (argument :: rest) objects .whole =
      (placeWithNames names calls layout argument objects >>= fun source =>
        CProg.loadCells source extent >>= fun fields =>
        argumentsWithNames names calls layout rest objects .whole >>= fun others =>
        pure (CallArgument.record type fields :: others)) := by
  rw [argumentsWithNames.eq_def]
  dsimp only [ArgumentMode.Value]
  simp only [admitted, snapshotRecord, Prog.bind_eq, Prog.pure_eq, Prog.bind_assoc, Prog.ret_bind]

theorem explicit_call_waits_for_all_arguments (names : NameReads) (calls : Calls)
    (layout : Layout) (name : Name) (arguments : List CExpr) (objects : ObjectReads)
    (service : ArgumentCall CVal) (admitted : objects.argumentCalls name = some service) :
    expressionWithNames names calls layout (.call name arguments) objects =
      (argumentsWithNames names calls layout arguments objects service.mode >>= service.invoke) := by
  rw [expressionWithNames.eq_def]
  simp only [admitted]

theorem absent_argument_call_preserves_scalar_path (names : NameReads) (calls : Calls)
    (layout : Layout) (name : Name) (arguments : List CExpr) (objects : ObjectReads)
    (absent : objects.argumentCalls name = none) :
    expressionWithNames names calls layout (.call name arguments) objects =
      (argumentsWithNames names calls layout arguments objects .scalar >>= calls name) := by
  rw [expressionWithNames.eq_def]
  simp only [absent]

namespace WholeArgumentControls

def recordType : CType := ⟨"Pair".toList, 0⟩
def recordName : Name := "record".toList
def changeName : Name := "change".toList

def objects (address : Ptr) : ObjectReads where
  place := some (fun name => if name = recordName then some address else none)
  record := fun operand => match operand with
    | .identifier name => if name = recordName then some (recordType, 1) else none
    | _ => none

def calls (address : Ptr) (replacement : CVal) : Calls := fun name arguments =>
  if name = changeName ∧ arguments = [] then do
    CProg.store address replacement
    pure (.bool true)
  else CProg.undefined

def operands : List CExpr :=
  [.identifier recordName, .call changeName [], .identifier recordName]

def capture (address : Ptr) (replacement : CVal) : CProg CVal (List CallArgument) :=
  argumentsWithNames (fun _ => CProg.undefined) (calls address replacement) (fun _ => none)
    operands (objects address) .whole

/-- The first record is captured before the source effect, and the repeated
record argument is read again afterward. Neither snapshot is replayed. -/
theorem capture_order (address : Ptr) (replacement : CVal) :
    capture address replacement =
      (CProg.load address >>= fun first =>
        CProg.store address replacement >>= fun _ =>
        CProg.load address >>= fun last =>
        pure [.record recordType [first], .scalar (.bool true), .record recordType [last]]) := by
  simp only [capture, operands, argumentsWithNames.eq_def, objects,
    placeWithNames.eq_def, Option.bind_some, resolved, snapshotRecord, CProg.loadCells,
    expressionWithNames.eq_def, calls, and_self, ↓reduceIte, Prog.bind_eq, Prog.pure_eq,
    Prog.ret_bind, Prog.bind_assoc]

/-- Record metadata does not make an ordinary scalar read of an embedded
object succeed. Such a use is outside the scalar expression profile. -/
theorem scalar_record_argument_refuses (address : Ptr) :
    argumentsWithNames (fun _ => CProg.undefined) noCalls (fun _ => none)
      [.identifier recordName] (objects address) .scalar = CProg.undefined := by
  rw [arguments_scalar_cons]
  rw [expressionWithNames.eq_def]
  exact undefined_bind _

section Ownership
open Mettapedia.GSLT.SeparationAlgebra
open scoped Mettapedia.GSLT.SeparationAlgebra
open CellPermission
universe u
variable {L : Type u} [Zero L] [Add L] [SepAlgebra L] [CellPermission L (Option CVal)]

theorem capture_observes_old_and_new (address : Ptr) (original replacement : CVal) :
    CTriple (L := L) (PointsTo address original) (capture address replacement)
      (fun actual heap =>
        actual = [.record recordType [original], .scalar (.bool true),
          .record recordType [replacement]] ∧ PointsTo address replacement heap) := by
  rw [capture_order]
  refine triple_bind _ (load_rule (v := original) fun _ held =>
    read_of_pointsTo (F := emp) (by simpa only [sepConj_emp] using held)) fun first => ?_
  apply triple_pure
  intro same
  subst first
  refine triple_bind _ (triple_pre _ (fun _ held => ⟨some original, held⟩)
    (store_spec address replacement)) fun _ => ?_
  refine triple_bind _ (load_rule (v := replacement) fun _ held =>
    read_of_pointsTo (F := emp) (by simpa only [sepConj_emp] using held)) fun last => ?_
  apply triple_pure
  intro same
  subst last
  exact triple_pre _ (fun _ held => ⟨rfl, held⟩)
    (triple_ret act
      [CallArgument.record recordType [original], .scalar (.bool true),
        .record recordType [replacement]]
      (fun actual heap => actual = [.record recordType [original], .scalar (.bool true),
        .record recordType [replacement]] ∧ PointsTo address replacement heap))

end Ownership
end WholeArgumentControls
end Mettapedia.Machines.CMemory.ReadExpressions

namespace Mettapedia.Machines.CMemory.ReadExpressions
open Mettapedia.GSLT.LanguageDef.NativeOps.NativeC
open Mettapedia.GSLT.Logic.AbstractSeparationLogic
open Mettapedia.GSLT.SeparationAlgebra
open Mettapedia.Languages.C11 hiding CType

abbrev PointerSourceType := Mettapedia.Languages.C11.CType

theorem readonly_pointer_cast_pointer {source target : PointerSourceType}
    (admitted : CharacterPointerViews.ReadOnly source target) (pointer : Option Ptr) :
    readonlyPointerCast source target (.ptr pointer) = pure (.ptr pointer) := by
  simp only [readonlyPointerCast,
    (CharacterPointerViews.accepted_iff source target).mpr admitted, ↓reduceIte]

theorem ObjectReads.readonlyCast_pointer (objects : ObjectReads) (type : CType)
    (operand : CExpr) (source declared target : PointerSourceType)
    (sourceTyped : objects.sourceType operand = some source)
    (targetTyped : objects.targetType type = some declared)
    (qualified : constPointee? declared = some target)
    (admitted : CharacterPointerViews.ReadOnly source target) (pointer : Option Ptr) :
    objects.readonlyCast type operand (.ptr pointer) = pure (.ptr pointer) := by
  simp only [ObjectReads.readonlyCast, sourceTyped, targetTyped, Option.bind_some,
    qualified, readonly_pointer_cast_pointer admitted]

theorem readonly_cast_keeps_reached_operand (names : NameReads) (calls : Calls)
    (layout : Layout) (objects : ObjectReads) (type : CType) (operand : CExpr) :
    expressionWithNames names calls layout (.castPointeeConst type operand) objects =
      (expressionWithNames names calls layout operand objects >>=
        objects.readonlyCast type operand) := rfl

section Execution
universe u
variable {L : Type u} [Zero L] [Add L] [SepAlgebra L]
  [CellPermission L (Option CVal)]

private theorem undefined_has_no_run (heap reached : Heap L) (value : CVal) :
    ¬(CProg.undefined : CProg CVal CVal).Runs act heap value reached := by
  rintro ⟨_, _, impossible, _⟩
  exact impossible

theorem readonly_pointer_cast_runs_iff (source target : PointerSourceType)
    (input output : CVal) (heap reached : Heap L) :
    (readonlyPointerCast source target input).Runs act heap output reached ↔
      CharacterPointerViews.ReadOnly source target ∧
        ∃ pointer, input = .ptr pointer ∧ output = .ptr pointer ∧ reached = heap := by
  by_cases accepted : CharacterPointerViews.accepted source target = true
  · have admitted := (CharacterPointerViews.accepted_iff source target).mp accepted
    simp only [readonlyPointerCast, accepted, ↓reduceIte]
    cases input with
    | ptr pointer =>
        change (.ptr pointer = output ∧ heap = reached) ↔ _
        constructor
        · rintro ⟨rfl, rfl⟩
          exact ⟨admitted, pointer, rfl, rfl, rfl⟩
        · rintro ⟨_, other, same, rfl, rfl⟩
          exact ⟨same, rfl⟩
    | _ =>
        constructor
        · intro impossible
          exact False.elim (undefined_has_no_run heap reached output impossible)
        · rintro ⟨_, _, impossible, _, _⟩
          cases impossible
  · have refused : ¬ CharacterPointerViews.ReadOnly source target :=
      fun permitted => accepted ((CharacterPointerViews.accepted_iff source target).mpr permitted)
    simp only [readonlyPointerCast, accepted]
    constructor
    · intro impossible
      exact False.elim (undefined_has_no_run heap reached output impossible)
    · rintro ⟨permitted, _⟩
      exact False.elim (refused permitted)

/-- The source cast's complete executions are exactly one operand execution
followed by the admitted pointer view. The reached heap and nullable pointer
are retained. No second operand execution or fabricated memory read occurs. -/
theorem readonly_cast_runs_iff (names : NameReads) (calls : Calls)
    (layout : Layout) (objects : ObjectReads) (type : CType) (operand : CExpr)
    (source declared target : PointerSourceType)
    (sourceTyped : objects.sourceType operand = some source)
    (targetTyped : objects.targetType type = some declared)
    (qualified : constPointee? declared = some target)
    (output : CVal) (heap reached : Heap L) :
    (expressionWithNames names calls layout (.castPointeeConst type operand) objects).Runs
        act heap output reached ↔
      CharacterPointerViews.ReadOnly source target ∧
        ∃ pointer, (expressionWithNames names calls layout operand objects).Runs
          act heap (.ptr pointer) reached ∧ output = .ptr pointer := by
  rw [readonly_cast_keeps_reached_operand]
  change (Prog.bind (expressionWithNames names calls layout operand objects)
    (objects.readonlyCast type operand)).Runs act heap output reached ↔ _
  rw [Prog.runs_bind]
  constructor
  · rintro ⟨value, between, operandRun, castRun⟩
    simp only [ObjectReads.readonlyCast, sourceTyped, targetTyped,
      Option.bind_some, qualified] at castRun
    obtain ⟨admitted, pointer, rfl, outputSame, rfl⟩ :=
      (readonly_pointer_cast_runs_iff source target value output between reached).mp castRun
    exact ⟨admitted, pointer, operandRun, outputSame⟩
  · rintro ⟨admitted, pointer, operandRun, rfl⟩
    refine ⟨.ptr pointer, reached, operandRun, ?_⟩
    rw [objects.readonlyCast_pointer type operand source declared target sourceTyped
      targetTyped qualified admitted pointer]
    exact ⟨rfl, rfl⟩

end Execution
end Mettapedia.Machines.CMemory.ReadExpressions

namespace Mettapedia.Machines.CMemory.ReadExpressions.ReadonlyCastControls
open Mettapedia.GSLT.LanguageDef.NativeOps.NativeC
open Mettapedia.GSLT.Logic.AbstractSeparationLogic
open Mettapedia.Languages.C11.CharacterPointerViews

def bytes : CExpr := .identifier "bytes".toList

def returnedBytes : CExpr := .call "get_bytes".toList []

def bytePointer : CType := ⟨"uint8_t".toList, 1⟩

def objects : ObjectReads where
  sourceType := fun operand => match operand with
    | .identifier name => if name == "bytes".toList then some (.pointer {} .character) else none
    | .call name [] => if name == "get_bytes".toList then some (.pointer {} .character) else none
    | _ => none
  targetType := fun type =>
    if type = bytePointer then some (.pointer {} unsignedCharacter)
    else if type = ⟨"uint32_t".toList, 1⟩ then
      some (.pointer {} (.arithmetic (.integer (.unsigned (.standard .int)))))
    else none

theorem pointer_only_view (pointer : Option Ptr) :
    objects.readonlyCast bytePointer bytes (.ptr pointer) = pure (.ptr pointer) := rfl

theorem actual_source_reader_returns_same_pointer (pointer : Option Ptr) :
    expressionWithNames (fun _ => pure (.ptr pointer)) noCalls (fun _ => none)
      (.castPointeeConst bytePointer bytes) objects = pure (.ptr pointer) := rfl

theorem effectful_operand_is_evaluated_once (marker : Ptr) (pointer : Option Ptr) :
    expressionWithNames (fun _ => CProg.store marker (.u32 1) >>= fun _ => pure (.ptr pointer))
      noCalls (fun _ => none) (.castPointeeConst bytePointer bytes) objects =
      (CProg.store marker (.u32 1) >>= fun _ => pure (.ptr pointer)) := rfl

theorem actual_call_is_executed_once (marker : Ptr) (pointer : Option Ptr) :
    expressionWithNames (fun _ => CProg.undefined)
      (fun _ _ => CProg.store marker (.u32 1) >>= fun _ => pure (.ptr pointer))
      (fun _ => none) (.castPointeeConst bytePointer returnedBytes) objects =
      (CProg.store marker (.u32 1) >>= fun _ => pure (.ptr pointer)) := rfl

theorem missing_static_type_preserves_reached_effect (marker : Ptr) (pointer : Option Ptr) :
    expressionWithNames (fun _ => CProg.store marker (.u32 1) >>= fun _ => pure (.ptr pointer))
      noCalls (fun _ => none) (.castPointeeConst bytePointer bytes) =
      (CProg.store marker (.u32 1) >>= fun _ => CProg.undefined) := rfl

/-- This reader does not reinterpret integer payloads as pointers. C integer
null-pointer constants require their separate source conversion. -/
theorem nonzero_integer_payload_does_not_gain_pointer_identity :
    objects.readonlyCast bytePointer bytes (.u32 1) = CProg.undefined := rfl

theorem wrong_destination_keeps_effect_before_refusal (marker : Ptr) (pointer : Option Ptr) :
    expressionWithNames (fun _ => CProg.store marker (.u32 1) >>= fun _ => pure (.ptr pointer))
      noCalls (fun _ => none) (.castPointeeConst ⟨"uint32_t".toList, 1⟩ bytes) objects =
      (CProg.store marker (.u32 1) >>= fun _ => CProg.undefined) := rfl

theorem mutable_pointer_cast_not_silently_enabled (pointer : Option Ptr) :
    expressionWithNames (fun _ => pure (.ptr pointer)) noCalls (fun _ => none)
      (.cast bytePointer bytes) objects = CProg.undefined := by
  simp only [expressionWithNames.eq_def, bytes, unsignedCast, integerValue?, resolved,
    Prog.bind_eq, Prog.pure_eq, Prog.ret_bind]
  exact undefined_bind _


end Mettapedia.Machines.CMemory.ReadExpressions.ReadonlyCastControls
