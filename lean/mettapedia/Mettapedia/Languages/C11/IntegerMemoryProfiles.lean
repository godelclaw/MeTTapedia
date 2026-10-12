import Mettapedia.Languages.C11.IntegerMemoryModel

/-!
# Constructed integer object families for named data models

The ILP32, LP64 and LLP64 value profiles receive one coherent eight-bit
character memory with distinct Boolean, character, short, int, long and long
long object layouts. The declared int128 extension has sixteen-byte objects.
Signed/unsigned counterparts have equal extents. Byte order is a parameter.
The Boolean object has one low value bit and a zero-padding trap policy;
ordinary stores construct its canonical zero/one representation.

These are semantic representation profiles. Their construction proves the
extent/range obligations for every canonical integer type; it does not
certify a compiler ABI, source type elaboration or physical alignment.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.C11.IntegerMemoryProfiles

open IntegerMemoryModel

def characters : ByteStorageData.Profile := ⟨8, by decide⟩

def familyBytes (model : IntegerDataModel) : IntegerFamily IntegerExtension → Nat
  | .standard .char => 1
  | .standard .short => 2
  | .standard .int => 4
  | .standard .long => if model = .lp64 then 8 else 4
  | .standard .longLong => 8
  | .extended .int128 => 16

def objectBytes (model : IntegerDataModel) : IntegerType IntegerExtension → Nat
  | .boolean => 1
  | .signed family | .unsigned family => familyBytes model family

def objectFormat (model : IntegerDataModel) (order : BytePacking.Order)
    (type : IntegerType IntegerExtension) : ObjectFormat (integerValueProfile model) characters type where
  byteCount := objectBytes model type
  positiveExtent := by
    cases model <;> cases type with
    | boolean => decide
    | signed family =>
        cases family with
        | standard standard => cases standard <;> decide
        | extended extension => cases extension; decide
    | unsigned family =>
        cases family with
        | standard standard => cases standard <;> decide
        | extended extension => cases extension; decide
  fits := by
    cases model <;> cases type with
    | boolean => decide
    | signed family =>
        cases family with
        | standard standard => cases standard <;> decide
        | extended extension => cases extension; decide
    | unsigned family =>
        cases family with
        | standard standard => cases standard <;> decide
        | extended extension => cases extension; decide
  order := order
  negativeZero := .normal
  padding := if type = .boolean then .zero else .ignored

def memoryModel (model : IntegerDataModel) (order : BytePacking.Order) : Model :=
  ⟨integerValueProfile model, characters, objectFormat model order⟩

theorem counterpart_extents (model : IntegerDataModel) (family : IntegerFamily IntegerExtension) :
    objectBytes model (.signed family) = objectBytes model (.unsigned family) := rfl

theorem boolean_extent (model : IntegerDataModel) (order : BytePacking.Order) :
    ((memoryModel model order).layout .boolean).representation.byteCount = 1 := rfl

theorem extended_integer_extent (model : IntegerDataModel) (order : BytePacking.Order) (signed : Bool) :
    ((memoryModel model order).layout (if signed then .signed (.extended .int128) else .unsigned (.extended .int128))).representation.byteCount = 16 := by
  cases signed <;> rfl

theorem lp64_long_extent (order : BytePacking.Order) :
    ((memoryModel .lp64 order).layout (.signed (.standard .long))).representation.byteCount = 8 := rfl

theorem ilp32_long_extent (order : BytePacking.Order) :
    ((memoryModel .ilp32 order).layout (.signed (.standard .long))).representation.byteCount = 4 := rfl

theorem llp64_long_extent (order : BytePacking.Order) :
    ((memoryModel .llp64 order).layout (.signed (.standard .long))).representation.byteCount = 4 := rfl

theorem order_preserved (model : IntegerDataModel) (order : BytePacking.Order) (type : IntegerType IntegerExtension) :
    ((memoryModel model order).layout type).representation.order = order := rfl

end Mettapedia.Languages.C11.IntegerMemoryProfiles
