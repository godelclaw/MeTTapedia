import Mettapedia.OSLF.MeTTaIL.Syntax
import Mathlib.Data.Nat.Digits.Defs

/-!
# Flat structural tokens for shared patterns

The prefix codec retains every pattern constructor and metadata field. String
payloads are separate tokens, so their content needs no escaping. Numeric fields
use binary digits, followed by an explicit terminator. The executable reader
returns the unused suffix; complete decoding rejects trailing tokens.
-/

set_option autoImplicit false
namespace Mettapedia.OSLF.MeTTaIL.PatternTokens
open Syntax

def bits (value : Nat) : List String :=
  (Nat.digits 2 value).map fun digit => if digit = 0 then "0" else "1"

def readNat : List String → Option (Nat × List String)
  | "e" :: rest => some (0, rest)
  | "0" :: rest => do
      let (value, tail) ← readNat rest
      pure (2 * value, tail)
  | "1" :: rest => do
      let (value, tail) ← readNat rest
      pure (2 * value + 1, tail)
  | _ => none

theorem readNat_bits (value : Nat) (tail : List String) :
    readNat (bits value ++ "e" :: tail) = some (value, tail) := by
  have digits : ∀ (digits : List Nat), (∀ digit ∈ digits, digit < 2) →
      readNat ((digits.map fun digit => if digit = 0 then "0" else "1") ++ "e" :: tail) =
        some (Nat.ofDigits 2 digits, tail) := by
    intro digits
    induction digits with
    | nil => simp [readNat]
    | cons digit digits ih =>
      intro bound
      have rest := ih (fun n member => bound n (by simp [member]))
      have digitBound := bound digit (by simp)
      by_cases zero : digit = 0
      · simp [zero, readNat, rest, Nat.ofDigits]
      · have one : digit = 1 := by omega
        simp [one, readNat, rest, Nat.ofDigits, Nat.mul_comm, Nat.add_comm]
  simpa [bits, Nat.ofDigits_digits] using
    digits (Nat.digits 2 value) (fun _ member => Nat.digits_lt_base (by decide) member)

def option (value : Option String) (tail : List String) : List String :=
  match value with
  | none => "n" :: tail
  | some name => "o" :: name :: tail

def readOption : List String → Option (Option String × List String)
  | "n" :: tail => some (none, tail)
  | "o" :: name :: tail => some (some name, tail)
  | _ => none

theorem readOption_option (value : Option String) (tail : List String) :
    readOption (option value tail) = some (value, tail) := by cases value <;> rfl

def names : List String → List String → List String
  | [], tail => "z" :: tail
  | name :: rest, tail => "h" :: name :: names rest tail

def readNames : List String → Option (List String × List String)
  | "z" :: tail => some ([], tail)
  | "h" :: name :: rest => do
      let (names, tail) ← readNames rest
      pure (name :: names, tail)
  | _ => none

theorem readNames_names (values tail : List String) :
    readNames (names values tail) = some (values, tail) := by
  induction values with
  | nil => rfl
  | cons name rest ih => simp [names, readNames, ih]

def collection (kind : CollType) : String :=
  match kind with | .vec => "v" | .hashBag => "b" | .hashSet => "s"

def readCollection : String → Option CollType
  | "v" => some .vec
  | "b" => some .hashBag
  | "s" => some .hashSet
  | _ => none

theorem readCollection_collection (kind : CollType) :
    readCollection (collection kind) = some kind := by cases kind <;> rfl

mutual
  def write : Pattern → List String → List String
    | .bvar index, tail => "b" :: bits index ++ "e" :: tail
    | .fvar name, tail => "v" :: name :: tail
    | .apply name arguments, tail => "a" :: name :: writeList arguments tail
    | .lambda name body, tail => "l" :: option name (write body tail)
    | .multiLambda arity binderNames body, tail =>
        "m" :: bits arity ++ "e" :: names binderNames (write body tail)
    | .subst body replacement, tail => "s" :: write body (write replacement tail)
    | .collection kind elements rest, tail =>
        "c" :: collection kind :: option rest (writeList elements tail)
  def writeList : List Pattern → List String → List String
    | [], tail => "z" :: tail
    | value :: values, tail => "h" :: write value (writeList values tail)
end

mutual
  def read : Nat → List String → Option (Pattern × List String)
    | 0, _ => none
    | _ + 1, "b" :: rest => do
        let (index, tail) ← readNat rest
        pure (.bvar index, tail)
    | _ + 1, "v" :: name :: tail => some (.fvar name, tail)
    | fuel + 1, "a" :: name :: rest => do
        let (arguments, tail) ← readList fuel rest
        pure (.apply name arguments, tail)
    | fuel + 1, "l" :: rest => do
        let (name, rest) ← readOption rest
        let (body, tail) ← read fuel rest
        pure (.lambda name body, tail)
    | fuel + 1, "m" :: rest => do
        let (arity, rest) ← readNat rest
        let (binderNames, rest) ← readNames rest
        let (body, tail) ← read fuel rest
        pure (.multiLambda arity binderNames body, tail)
    | fuel + 1, "s" :: rest => do
        let (body, rest) ← read fuel rest
        let (replacement, tail) ← read fuel rest
        pure (.subst body replacement, tail)
    | fuel + 1, "c" :: kind :: rest => do
        let kind ← readCollection kind
        let (capture, rest) ← readOption rest
        let (elements, tail) ← readList fuel rest
        pure (.collection kind elements capture, tail)
    | _ + 1, _ => none
  def readList : Nat → List String → Option (List Pattern × List String)
    | 0, _ => none
    | _ + 1, "z" :: tail => some ([], tail)
    | fuel + 1, "h" :: rest => do
        let (value, rest) ← read fuel rest
        let (values, tail) ← readList fuel rest
        pure (value :: values, tail)
    | _ + 1, _ => none
end

mutual
  def depth : Pattern → Nat
    | .bvar _ | .fvar _ => 1
    | .apply _ arguments => listDepth arguments + 1
    | .lambda _ body | .multiLambda _ _ body => depth body + 1
    | .subst body replacement => max (depth body) (depth replacement) + 1
    | .collection _ elements _ => listDepth elements + 1
  def listDepth : List Pattern → Nat
    | [] => 1
    | value :: values => max (depth value) (listDepth values) + 1
end

mutual
  theorem read_write (value : Pattern) (tail : List String) (fuel : Nat)
      (enough : depth value ≤ fuel) : read fuel (write value tail) = some (value, tail) := by
    cases fuel with
    | zero => cases value <;> simp [depth] at enough
    | succ fuel =>
      cases value with
      | bvar index => simp [write, read, readNat_bits]
      | fvar name => rfl
      | apply name arguments =>
          have child : listDepth arguments ≤ fuel := by simp [depth] at enough; omega
          simp [write, read, readList_writeList arguments tail fuel child]
      | lambda name body =>
          have child : depth body ≤ fuel := by simp [depth] at enough; omega
          simp [write, read, readOption_option, read_write body tail fuel child]
      | multiLambda arity binderNames body =>
          have child : depth body ≤ fuel := by simp [depth] at enough; omega
          simp [write, read, readNat_bits, readNames_names, read_write body tail fuel child]
      | subst body replacement =>
          have left : depth body ≤ fuel := by simp [depth] at enough; omega
          have right : depth replacement ≤ fuel := by simp [depth] at enough; omega
          simp [write, read, read_write body (write replacement tail) fuel left,
            read_write replacement tail fuel right]
      | collection kind elements capture =>
          have child : listDepth elements ≤ fuel := by simp [depth] at enough; omega
          simp [write, read, readCollection_collection, readOption_option,
            readList_writeList elements tail fuel child]
  termination_by sizeOf value
  decreasing_by all_goals sizeOf_pattern_dec

  theorem readList_writeList (values : List Pattern) (tail : List String) (fuel : Nat)
      (enough : listDepth values ≤ fuel) :
      readList fuel (writeList values tail) = some (values, tail) := by
    cases fuel with
    | zero => cases values <;> simp [listDepth] at enough
    | succ fuel =>
      cases values with
      | nil => rfl
      | cons value values =>
          have left : depth value ≤ fuel := by simp [listDepth] at enough; omega
          have right : listDepth values ≤ fuel := by simp [listDepth] at enough; omega
          simp [writeList, readList, read_write value (writeList values tail) fuel left,
            readList_writeList values tail fuel right]
  termination_by sizeOf values
  decreasing_by all_goals sizeOf_pattern_dec
end

def encode (value : Pattern) : List String := write value []

theorem names_length (values tail : List String) :
    (names values tail).length = 2 * values.length + 1 + tail.length := by
  induction values with
  | nil => simp [names]; omega
  | cons name rest ih => simp [names, ih]; omega

theorem option_length (value : Option String) (tail : List String) :
    (option value tail).length = (option value []).length + tail.length := by
  cases value <;> simp [option] <;> omega

mutual
  theorem write_length (value : Pattern) (tail : List String) :
      (write value tail).length = (write value []).length + tail.length := by
    cases value with
    | bvar index => simp [write]; omega
    | fvar name => simp [write]; omega
    | apply name arguments =>
        have ih := writeList_length arguments tail
        simp only [write, List.length_cons]
        omega
    | lambda name body =>
        have ih := write_length body tail
        cases name <;> simp only [write, option, List.length_cons] <;> omega
    | multiLambda arity binderNames body =>
        have ih := write_length body tail
        simp only [write, List.length_cons, List.length_append, names_length]
        omega
    | subst body replacement =>
        have left := write_length body (write replacement tail)
        have base := write_length body (write replacement [])
        have right := write_length replacement tail
        simp only [write, List.length_cons]
        omega
    | collection kind elements rest =>
        have ih := writeList_length elements tail
        cases rest <;> simp only [write, option, List.length_cons] <;> omega
  termination_by sizeOf value
  decreasing_by all_goals sizeOf_pattern_dec
  theorem writeList_length (values : List Pattern) (tail : List String) :
      (writeList values tail).length = (writeList values []).length + tail.length := by
    cases values with
    | nil => simp [writeList]; omega
    | cons value values =>
        have left := write_length value (writeList values tail)
        have base := write_length value (writeList values [])
        have right := writeList_length values tail
        simp only [writeList, List.length_cons]
        omega
  termination_by sizeOf values
  decreasing_by all_goals sizeOf_pattern_dec
end

mutual
  theorem depth_le_length (value : Pattern) : depth value ≤ (encode value).length := by
    cases value with
    | bvar index => simp [depth, encode, write]
    | fvar name => simp [depth, encode, write]
    | apply name arguments =>
        have ih := listDepth_le_length arguments
        simp [depth, encode, write] at *
        omega
    | lambda name body =>
        have ih := depth_le_length body
        cases name <;> simp [depth, encode, write, option] at * <;> omega
    | multiLambda arity binderNames body =>
        have ih := depth_le_length body
        simp [depth, encode, write, names_length] at *
        omega
    | subst body replacement =>
        have left := depth_le_length body
        have right := depth_le_length replacement
        have length := write_length body (write replacement [])
        simp only [depth, encode, write, List.length_cons] at *
        omega
    | collection kind elements rest =>
        have ih := listDepth_le_length elements
        cases rest <;> simp [depth, encode, write, option] at * <;> omega
  termination_by sizeOf value
  decreasing_by all_goals sizeOf_pattern_dec
  theorem listDepth_le_length (values : List Pattern) :
      listDepth values ≤ (writeList values []).length := by
    cases values with
    | nil => simp [listDepth, writeList]
    | cons value values =>
        have left := depth_le_length value
        have right := listDepth_le_length values
        have length := write_length value (writeList values [])
        simp only [listDepth, encode, writeList, List.length_cons] at *
        omega
  termination_by sizeOf values
  decreasing_by all_goals sizeOf_pattern_dec
end

def decode (tokens : List String) : Option Pattern := do
  let (value, rest) ← read tokens.length tokens
  if rest.isEmpty then some value else none

theorem decode_encode (value : Pattern) : decode (encode value) = some value := by
  unfold decode encode
  rw [read_write value [] (write value []).length (depth_le_length value)]
  rfl

theorem encode_injective : Function.Injective encode := by
  intro first second equal
  have decoded := congrArg decode equal
  simpa [decode_encode] using decoded

/-- Token storage includes both the UTF-8 payload and one component boundary. -/
def tokenSize : List String → Nat
  | [] => 0
  | token :: tokens => token.utf8ByteSize + 1 + tokenSize tokens

theorem tokenSize_append (first second : List String) :
    tokenSize (first ++ second) = tokenSize first + tokenSize second := by
  induction first with
  | nil => simp [tokenSize]
  | cons token tokens ih => simp [tokenSize, ih]; omega

@[simp] private theorem tag_0_bytes : "0".utf8ByteSize = 1 := by decide
@[simp] private theorem tag_1_bytes : "1".utf8ByteSize = 1 := by decide
@[simp] private theorem tag_b_bytes : "b".utf8ByteSize = 1 := by decide
@[simp] private theorem tag_v_bytes : "v".utf8ByteSize = 1 := by decide
@[simp] private theorem tag_a_bytes : "a".utf8ByteSize = 1 := by decide
@[simp] private theorem tag_l_bytes : "l".utf8ByteSize = 1 := by decide
@[simp] private theorem tag_m_bytes : "m".utf8ByteSize = 1 := by decide
@[simp] private theorem tag_s_bytes : "s".utf8ByteSize = 1 := by decide
@[simp] private theorem tag_c_bytes : "c".utf8ByteSize = 1 := by decide
@[simp] private theorem tag_e_bytes : "e".utf8ByteSize = 1 := by decide
@[simp] private theorem tag_n_bytes : "n".utf8ByteSize = 1 := by decide
@[simp] private theorem tag_o_bytes : "o".utf8ByteSize = 1 := by decide
@[simp] private theorem tag_z_bytes : "z".utf8ByteSize = 1 := by decide
@[simp] private theorem tag_h_bytes : "h".utf8ByteSize = 1 := by decide

theorem tokenSize_bits (value : Nat) :
    tokenSize (bits value) = 2 * (Nat.digits 2 value).length := by
  have mapped : ∀ (digits : List Nat),
      tokenSize (digits.map fun digit => if digit = 0 then "0" else "1") =
        2 * digits.length := by
    intro digits
    induction digits with
    | nil => rfl
    | cons digit digits ih =>
      by_cases zero : digit = 0 <;> simp [zero, tokenSize, ih] <;> omega
  exact mapped _

def optionWeight : Option String → Nat
  | none => 1
  | some name => 1 + name.utf8ByteSize

def namesWeight : List String → Nat
  | [] => 1
  | name :: rest => 1 + name.utf8ByteSize + namesWeight rest

mutual
  /-- Structural source storage, with binary numeric fields and UTF-8 names. -/
  def weight : Pattern → Nat
    | .bvar index => 1 + (Nat.digits 2 index).length
    | .fvar name => 1 + name.utf8ByteSize
    | .apply name arguments => 1 + name.utf8ByteSize + listWeight arguments
    | .lambda name body => 1 + optionWeight name + weight body
    | .multiLambda arity binderNames body =>
        1 + (Nat.digits 2 arity).length + namesWeight binderNames + weight body
    | .subst body replacement => 1 + weight body + weight replacement
    | .collection _ elements rest => 1 + listWeight elements + optionWeight rest
  def listWeight : List Pattern → Nat
    | [] => 1
    | value :: values => 1 + weight value + listWeight values
end

theorem option_size (value : Option String) (tail : List String) :
    tokenSize (option value tail) ≤ 6 * optionWeight value + tokenSize tail := by
  cases value with
  | none => simp [option, tokenSize, optionWeight]
  | some name => simp [option, tokenSize, optionWeight]; omega

theorem names_size (values tail : List String) :
    tokenSize (names values tail) ≤ 6 * namesWeight values + tokenSize tail := by
  induction values with
  | nil => simp [names, tokenSize, namesWeight]
  | cons name rest ih => simp [names, tokenSize, namesWeight] at *; omega

mutual
  theorem write_size (value : Pattern) (tail : List String) :
      tokenSize (write value tail) ≤ 6 * weight value + tokenSize tail := by
    cases value with
    | bvar index => simp [write, weight, tokenSize, tokenSize_append, tokenSize_bits]; omega
    | fvar name => simp [write, weight, tokenSize]; omega
    | apply name arguments =>
        have ih := writeList_size arguments tail
        simp [write, weight, tokenSize] at *
        omega
    | lambda name body =>
        have child := write_size body tail
        have metadata := option_size name (write body tail)
        simp [write, weight, tokenSize]
        omega
    | multiLambda arity binderNames body =>
        have child := write_size body tail
        have metadata := names_size binderNames (write body tail)
        simp [write, weight, tokenSize, tokenSize_append, tokenSize_bits]
        omega
    | subst body replacement =>
        have left := write_size body (write replacement tail)
        have right := write_size replacement tail
        simp [write, weight, tokenSize]
        omega
    | collection kind elements rest =>
        have child := writeList_size elements tail
        have metadata := option_size rest (writeList elements tail)
        cases kind <;> simp [write, collection, weight, tokenSize] <;> omega
  termination_by sizeOf value
  decreasing_by all_goals sizeOf_pattern_dec
  theorem writeList_size (values : List Pattern) (tail : List String) :
      tokenSize (writeList values tail) ≤ 6 * listWeight values + tokenSize tail := by
    cases values with
    | nil => simp [writeList, tokenSize, listWeight]
    | cons value values =>
        have left := write_size value (writeList values tail)
        have right := writeList_size values tail
        simp [writeList, tokenSize, listWeight]
        omega
  termination_by sizeOf values
  decreasing_by all_goals sizeOf_pattern_dec
end

theorem encode_size (value : Pattern) : tokenSize (encode value) ≤ 6 * weight value := by
  simpa [encode, tokenSize] using write_size value []

namespace Controls

def binderCollection : Pattern :=
  .multiLambda 2 ["h", "e"]
    (.collection .hashBag [.lambda (some "z") (.bvar 0), .fvar "o"] (some "n"))

example : decode (encode binderCollection) = some binderCollection := decode_encode _
example : decode ["a", "name", "h", "b", "1"] = none := by decide
example : decode (encode (.fvar "a") ++ ["trailing"]) = none := by decide
example : encode (.fvar "h") ≠ encode (.bvar 0) := by decide

end Controls
end Mettapedia.OSLF.MeTTaIL.PatternTokens
