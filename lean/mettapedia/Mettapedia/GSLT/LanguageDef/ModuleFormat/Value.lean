import Mathlib.Data.List.Basic
import Mathlib.Data.String.Basic
import Mettapedia.GSLT.LanguageDef.CettaWireTerm

/-!
# Structured values at the MeTTaIL module boundary

The constructors follow the public `RhoValue` carrier at mettail-rust commit
`8c1bb3b0ef3890406e375c2c5387dc9a3cdf0439`, `mettail-elab/src/canonical.rs`.
Record fields are retained as occurrences before schema admission. This is a
structural value boundary, not a byte parser or a BLAKE3 implementation.
Integers use `Int`; machine-width and canonical-value resource admission belong
to the host boundary, outside the structural envelope.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat

inductive Value where
  | record : List (String × Value) → Value
  | list : List Value → Value
  | string : String → Value
  | bytes : List UInt8 → Value
  | integer : Int → Value
  | floatBits : UInt64 → Value
  | boolean : Bool → Value
  | nil : Value
  deriving Repr

mutual

private def decEqValue : (first second : Value) → Decidable (first = second)
  | .record a, .record b =>
      match decEqFields a b with
      | isTrue equal => isTrue (by subst equal; rfl)
      | isFalse different => isFalse (by intro equal; cases equal; exact different rfl)
  | .list a, .list b =>
      match decEqValues a b with
      | isTrue equal => isTrue (by subst equal; rfl)
      | isFalse different => isFalse (by intro equal; cases equal; exact different rfl)
  | .string a, .string b =>
      match decEq a b with
      | isTrue equal => isTrue (by subst equal; rfl)
      | isFalse different => isFalse (by intro equal; cases equal; exact different rfl)
  | .bytes a, .bytes b =>
      match decEq a b with
      | isTrue equal => isTrue (by subst equal; rfl)
      | isFalse different => isFalse (by intro equal; cases equal; exact different rfl)
  | .integer a, .integer b =>
      match decEq a b with
      | isTrue equal => isTrue (by subst equal; rfl)
      | isFalse different => isFalse (by intro equal; cases equal; exact different rfl)
  | .floatBits a, .floatBits b =>
      match decEq a b with
      | isTrue equal => isTrue (by subst equal; rfl)
      | isFalse different => isFalse (by intro equal; cases equal; exact different rfl)
  | .boolean a, .boolean b =>
      match decEq a b with
      | isTrue equal => isTrue (by subst equal; rfl)
      | isFalse different => isFalse (by intro equal; cases equal; exact different rfl)
  | .nil, .nil => isTrue rfl
  | .record _, .list _ => isFalse Value.noConfusion
  | .record _, .string _ => isFalse Value.noConfusion
  | .record _, .bytes _ => isFalse Value.noConfusion
  | .record _, .integer _ => isFalse Value.noConfusion
  | .record _, .floatBits _ => isFalse Value.noConfusion
  | .record _, .boolean _ => isFalse Value.noConfusion
  | .record _, .nil => isFalse Value.noConfusion
  | .list _, .record _ => isFalse Value.noConfusion
  | .list _, .string _ => isFalse Value.noConfusion
  | .list _, .bytes _ => isFalse Value.noConfusion
  | .list _, .integer _ => isFalse Value.noConfusion
  | .list _, .floatBits _ => isFalse Value.noConfusion
  | .list _, .boolean _ => isFalse Value.noConfusion
  | .list _, .nil => isFalse Value.noConfusion
  | .string _, .record _ => isFalse Value.noConfusion
  | .string _, .list _ => isFalse Value.noConfusion
  | .string _, .bytes _ => isFalse Value.noConfusion
  | .string _, .integer _ => isFalse Value.noConfusion
  | .string _, .floatBits _ => isFalse Value.noConfusion
  | .string _, .boolean _ => isFalse Value.noConfusion
  | .string _, .nil => isFalse Value.noConfusion
  | .bytes _, .record _ => isFalse Value.noConfusion
  | .bytes _, .list _ => isFalse Value.noConfusion
  | .bytes _, .string _ => isFalse Value.noConfusion
  | .bytes _, .integer _ => isFalse Value.noConfusion
  | .bytes _, .floatBits _ => isFalse Value.noConfusion
  | .bytes _, .boolean _ => isFalse Value.noConfusion
  | .bytes _, .nil => isFalse Value.noConfusion
  | .integer _, .record _ => isFalse Value.noConfusion
  | .integer _, .list _ => isFalse Value.noConfusion
  | .integer _, .string _ => isFalse Value.noConfusion
  | .integer _, .bytes _ => isFalse Value.noConfusion
  | .integer _, .floatBits _ => isFalse Value.noConfusion
  | .integer _, .boolean _ => isFalse Value.noConfusion
  | .integer _, .nil => isFalse Value.noConfusion
  | .floatBits _, .record _ => isFalse Value.noConfusion
  | .floatBits _, .list _ => isFalse Value.noConfusion
  | .floatBits _, .string _ => isFalse Value.noConfusion
  | .floatBits _, .bytes _ => isFalse Value.noConfusion
  | .floatBits _, .integer _ => isFalse Value.noConfusion
  | .floatBits _, .boolean _ => isFalse Value.noConfusion
  | .floatBits _, .nil => isFalse Value.noConfusion
  | .boolean _, .record _ => isFalse Value.noConfusion
  | .boolean _, .list _ => isFalse Value.noConfusion
  | .boolean _, .string _ => isFalse Value.noConfusion
  | .boolean _, .bytes _ => isFalse Value.noConfusion
  | .boolean _, .integer _ => isFalse Value.noConfusion
  | .boolean _, .floatBits _ => isFalse Value.noConfusion
  | .boolean _, .nil => isFalse Value.noConfusion
  | .nil, .record _ => isFalse Value.noConfusion
  | .nil, .list _ => isFalse Value.noConfusion
  | .nil, .string _ => isFalse Value.noConfusion
  | .nil, .bytes _ => isFalse Value.noConfusion
  | .nil, .integer _ => isFalse Value.noConfusion
  | .nil, .floatBits _ => isFalse Value.noConfusion
  | .nil, .boolean _ => isFalse Value.noConfusion

private def decEqValues : (first second : List Value) → Decidable (first = second)
  | [], [] => isTrue rfl
  | x :: xs, y :: ys =>
      match decEqValue x y, decEqValues xs ys with
      | isTrue head, isTrue tail => isTrue (by subst head; subst tail; rfl)
      | isFalse head, _ => isFalse (by intro equal; cases equal; exact head rfl)
      | _, isFalse tail => isFalse (by intro equal; cases equal; exact tail rfl)
  | [], _ :: _ => isFalse (by intro equal; cases equal)
  | _ :: _, [] => isFalse (by intro equal; cases equal)

private def decEqFields :
    (first second : List (String × Value)) → Decidable (first = second)
  | [], [] => isTrue rfl
  | (k, x) :: xs, (l, y) :: ys =>
      match decEq k l, decEqValue x y, decEqFields xs ys with
      | isTrue key, isTrue head, isTrue tail =>
          isTrue (by subst key; subst head; subst tail; rfl)
      | isFalse key, _, _ => isFalse (by intro equal; cases equal; exact key rfl)
      | _, isFalse head, _ => isFalse (by intro equal; cases equal; exact head rfl)
      | _, _, isFalse tail => isFalse (by intro equal; cases equal; exact tail rfl)
  | [], _ :: _ => isFalse (by intro equal; cases equal)
  | _ :: _, [] => isFalse (by intro equal; cases equal)

end

instance : DecidableEq Value := decEqValue

namespace Value

def field? (fields : List (String × Value)) (key : String) : Option Value :=
  (fields.find? fun field => field.1 == key).map Prod.snd

def record? (keys : List String) : Value → Option (List (String × Value))
  | .record fields => if (fields.map Prod.fst).Perm keys then some fields else none
  | _ => none

def string? : Value → Option String
  | .string value => some value
  | _ => none

def list? : Value → Option (List Value)
  | .list values => some values
  | _ => none

def bytes? : Value → Option (List UInt8)
  | .bytes values => some values
  | _ => none

@[simp] theorem field?_nil (key : String) : field? [] key = none := rfl

@[simp] theorem field?_cons (key name : String) (value : Value)
    (rest : List (String × Value)) :
    field? ((name, value) :: rest) key =
      if name = key then some value else field? rest key := by
  by_cases equal : name = key
  · simp [field?, equal]
  · simp [field?, equal]

theorem record?_some_iff (keys : List String) (value : Value)
    (fields : List (String × Value)) :
    record? keys value = some fields ↔
      value = .record fields ∧ (fields.map Prod.fst).Perm keys := by
  cases value <;> simp [record?]
  constructor
  · rintro ⟨permutation, rfl⟩
    exact ⟨rfl, permutation⟩
  · rintro ⟨rfl, permutation⟩
    exact ⟨permutation, rfl⟩

end Value

/-- Registry references retain their suffix; file references retain the exact
path. Parsing a bare file path and its `file:` spelling yields the same key. -/
inductive ModuleRef where
  | registry : String → ModuleRef
  | file : String → ModuleRef
  deriving Repr, DecidableEq

namespace ModuleRef

def valid : ModuleRef → Prop
  | .registry name => name ≠ ""
  | .file path => path ≠ ""

instance (reference : ModuleRef) : Decidable reference.valid := by
  cases reference <;> unfold valid <;> infer_instance

def external : ModuleRef → String
  | .registry name => "rho:" ++ name
  | .file path => "file:" ++ path

def parseChars? : List Char → Option ModuleRef
  | 'r' :: 'h' :: 'o' :: ':' :: name =>
      if name = [] then none else some (.registry (String.ofList name))
  | 'f' :: 'i' :: 'l' :: 'e' :: ':' :: path =>
      if path = [] then none else some (.file (String.ofList path))
  | chars =>
      if chars = [] ∨ ':' ∈ chars then none else some (.file (String.ofList chars))

def parse? (text : String) : Option ModuleRef := parseChars? text.toList

@[simp] theorem parse_external (reference : ModuleRef) (accepted : reference.valid) :
    parse? reference.external = some reference := by
  cases reference with
  | registry name =>
      simp only [valid] at accepted
      simp [parse?, external, parseChars?, String.toList_append, accepted]
  | file path =>
      simp only [valid] at accepted
      simp [parse?, external, parseChars?, String.toList_append, accepted]

end ModuleRef

/-- The ASCII identifier rule used for module and exported-language names. -/
def identifier (text : String) : Bool :=
  match text.toList with
  | [] => false
  | first :: rest =>
      (first.isAlpha || first == '_') &&
        rest.all (fun c => c.isAlphanum || c == '_')


/-! ## The shared physical term carrier

Records retain field occurrences before schema admission, including repeated
keys. Numeric tags distinguish integers, byte strings and exact floating-point
bit patterns. This structural transport does not interpret an export payload.
-/

namespace Value.Wire

open Mettapedia.GSLT.LanguageDef.CettaWire (Term)

private def integer : Int → Term
  | .ofNat n => .application "Integer" [.natural n]
  | .negSucc n => .application "NegativeInteger" [.natural n]

private def integer? : Term → Option Int
  | .application "Integer" [.natural n] => some (.ofNat n)
  | .application "NegativeInteger" [.natural n] => some (.negSucc n)
  | _ => none

private def byte? : Term → Option UInt8
  | .natural n => if n < UInt8.size then some (UInt8.ofNat n) else none
  | _ => none

mutual
  def encode : Value → Term
    | .record fields => .application "Record" (encodeFields fields)
    | .list values => .application "List" (encodeValues values)
    | .string text => .string text
    | .bytes octets => .application "Bytes" (octets.map fun byte => .natural byte.toNat)
    | .integer n => integer n
    | .floatBits bits => .application "FloatBits" [.natural bits.toNat]
    | .boolean true => .symbol "True"
    | .boolean false => .symbol "False"
    | .nil => .symbol "Nil"

  def encodeValues : List Value → List Term
    | [] => []
    | first :: rest => encode first :: encodeValues rest

  def encodeFields : List (String × Value) → List Term
    | [] => []
    | (key, value) :: rest => .application "Field" [.string key, encode value] :: encodeFields rest
end

mutual
  def decode? : Term → Option Value
    | .application "Record" fields => .record <$> decodeFields? fields
    | .application "List" values => .list <$> decodeValues? values
    | .string text => some (.string text)
    | .application "Bytes" octets => .bytes <$> octets.mapM byte?
    | .application "Integer" [.natural n] => some (.integer (.ofNat n))
    | .application "NegativeInteger" [.natural n] => some (.integer (.negSucc n))
    | .application "FloatBits" [.natural bits] =>
        if bits < UInt64.size then some (.floatBits (UInt64.ofNat bits)) else none
    | .symbol "True" => some (.boolean true)
    | .symbol "False" => some (.boolean false)
    | .symbol "Nil" => some .nil
    | _ => none
  termination_by value => sizeOf value

  def decodeValues? : List Term → Option (List Value)
    | [] => some []
    | first :: rest => do pure ((← decode? first) :: (← decodeValues? rest))
  termination_by values => sizeOf values

  def decodeFields? : List Term → Option (List (String × Value))
    | [] => some []
    | .application "Field" [.string key, value] :: rest => do
        pure ((key, ← decode? value) :: (← decodeFields? rest))
    | _ => none
  termination_by values => sizeOf values
end

private theorem bytes_roundtrip (bytes : List UInt8) :
    (bytes.map fun byte => Term.natural byte.toNat).mapM byte? = some bytes := by
  induction bytes with
  | nil => rfl
  | cons first rest ih => simp [byte?, UInt8.toNat_lt_size, ih]

mutual
  @[simp] theorem decode_encode (value : Value) : decode? (encode value) = some value := by
    cases value with
    | record fields => simp [encode, decode?, decodeFields_encodeFields fields]
    | list values => simp [encode, decode?, decodeValues_encodeValues values]
    | string text => simp [encode, decode?]
    | bytes bytes =>
        simp only [encode, decode?, bytes_roundtrip]
        rfl
    | integer value => cases value <;> simp [encode, decode?, integer]
    | floatBits bits => simp [encode, decode?, UInt64.toNat_lt_size]
    | boolean value => cases value <;> simp [encode, decode?]
    | nil => simp [encode, decode?]
  termination_by sizeOf value

  @[simp] theorem decodeValues_encodeValues (values : List Value) :
      decodeValues? (encodeValues values) = some values := by
    cases values with
    | nil => simp [encodeValues, decodeValues?]
    | cons first rest => simp [encodeValues, decodeValues?, decode_encode first, decodeValues_encodeValues rest]
  termination_by sizeOf values

  @[simp] theorem decodeFields_encodeFields (values : List (String × Value)) :
      decodeFields? (encodeFields values) = some values := by
    cases values with
    | nil => simp [encodeFields, decodeFields?]
    | cons first rest =>
        rcases first with ⟨key, value⟩
        simp [encodeFields, decodeFields?, decode_encode value, decodeFields_encodeFields rest]
  termination_by sizeOf values
end

theorem encode_injective : Function.Injective encode := by
  intro first second same
  have := congrArg decode? same
  simpa only [decode_encode, Option.some.injEq] using this

/-! The converse transport is used for a semantic presentation inside an
opaque `module/1` export. Constructor heads remain distinct from string data.
It is deliberately structural: it grants no execution permission. -/

mutual
  def quoteTerm : Term → Value
    | .symbol name => .record [("symbol", .string name)]
    | .string text => .string text
    | .natural value => .integer (.ofNat value)
    | .application head arguments =>
        .record [("head", .string head), ("arguments", .list (quoteTerms arguments))]

  def quoteTerms : List Term → List Value
    | [] => []
    | first :: rest => quoteTerm first :: quoteTerms rest
end

mutual
  def readTerm? : Value → Option Term
    | .record [("symbol", .string name)] => some (.symbol name)
    | .string text => some (.string text)
    | .integer (.ofNat value) => some (.natural value)
    | .record [("head", .string head), ("arguments", .list arguments)] =>
        .application head <$> readTerms? arguments
    | _ => none
  termination_by value => sizeOf value

  def readTerms? : List Value → Option (List Term)
    | [] => some []
    | first :: rest => do pure ((← readTerm? first) :: (← readTerms? rest))
  termination_by values => sizeOf values
end

mutual
  @[simp] theorem readTerm_quoteTerm (value : Term) :
      readTerm? (quoteTerm value) = some value := by
    cases value with
    | symbol name => simp [quoteTerm, readTerm?]
    | string text => simp [quoteTerm, readTerm?]
    | natural value =>
        unfold quoteTerm readTerm?
        rfl
    | application head arguments => simp [quoteTerm, readTerm?, readTerms_quoteTerms arguments]
  termination_by sizeOf value

  @[simp] theorem readTerms_quoteTerms (values : List Term) :
      readTerms? (quoteTerms values) = some values := by
    cases values with
    | nil => simp [quoteTerms, readTerms?]
    | cons first rest => simp [quoteTerms, readTerms?, readTerm_quoteTerm first, readTerms_quoteTerms rest]
  termination_by sizeOf values
end

theorem quoteTerm_injective : Function.Injective quoteTerm := by
  intro first second same
  have := congrArg readTerm? same
  simpa only [readTerm_quoteTerm, Option.some.injEq] using this

end Value.Wire

end Mettapedia.GSLT.LanguageDef.ModuleFormat
