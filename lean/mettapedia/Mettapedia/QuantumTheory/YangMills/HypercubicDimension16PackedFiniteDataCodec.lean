import Mathlib.Init

/-!
# Flat finite-data codec for OUR dimension-sixteen realizations

Generated finite tables are carried as flat text payloads or bounded pages of
packed numerals rather than unbounded structure-literal arrays.  This module
contains the small kernel-reducible decoders shared by those payloads.
-/

set_option autoImplicit false

namespace Mettapedia
namespace QuantumTheory
namespace YangMills
namespace HypercubicDimension16PackedFiniteDataCodec

/-- Decode one lowercase hexadecimal ASCII digit. -/
@[reducible] def hexadecimalDigit (byte : UInt8) : Nat :=
  let value := byte.toNat
  if 48 ≤ value ∧ value ≤ 57 then value - 48
  else if 97 ≤ value ∧ value ≤ 102 then value - 87
  else 0

/-- Decode newline-delimited lowercase hexadecimal natural numbers from one
flat byte payload.  A newline terminates a word; an optional final unterminated
word is retained. -/
@[reducible] def decodeHexadecimalNatArray (payload : ByteArray) : Array Nat :=
  let state := payload.foldl
    (fun (state : Array Nat × Nat × Bool) byte =>
      if byte.toNat = 10 then
        if state.2.2 then (state.1.push state.2.1, 0, false) else state
      else
        (state.1, 16 * state.2.1 + hexadecimalDigit byte, true))
    (#[], 0, false)
  if state.2.2 then state.1.push state.2.1 else state.1

/-- Decode one newline-delimited hexadecimal numeral beginning at `start`.
The second component is the first byte after the numeral.  This local decoder
is used by sparse replay interfaces so a lookup never materializes a whole
table merely to read one row. -/
@[reducible] def decodeHexadecimalNatAtLoop (payload : ByteArray) :
    Nat → Nat → Nat → Nat × Nat
  | 0, position, value => (value, position)
  | fuel + 1, position, value =>
      let byte := payload.get! position
      if byte.toNat = 10 then (value, position + 1)
      else decodeHexadecimalNatAtLoop payload fuel (position + 1)
        (16 * value + hexadecimalDigit byte)

@[reducible] def decodeHexadecimalNatAt (payload : ByteArray) (start : Nat) : Nat × Nat :=
  decodeHexadecimalNatAtLoop payload 8 start 0

/-- The offset payload stores fixed-width hexadecimal byte positions, enabling
direct access to a variable-width row in a flat data payload. -/
@[reducible] def decodeFixedWidthHexadecimalNatAt
    (offsets : ByteArray) (width index : Nat) : Nat :=
  (List.range width).foldl (fun value offset =>
    16 * value + hexadecimalDigit (offsets.get! (width * index + offset))) 0

@[reducible] def decodeNatValuesAtLoop (payload : ByteArray) :
    Nat → Nat → Array Nat → Array Nat
  | 0, _, values => values
  | count + 1, position, values =>
      let (value, next) := decodeHexadecimalNatAt payload position
      decodeNatValuesAtLoop payload count next (values.push value)

/-- Decode one count-prefixed row through its fixed-width byte offset.  The
kernel checks the decoder together with the exact replay; no external parser
or native evaluator is trusted. -/
@[reducible] def decodeCountPrefixedNatRowAt
    (payload offsets : ByteArray) (offsetWidth row : Nat) : Array Nat :=
  let start := decodeFixedWidthHexadecimalNatAt offsets offsetWidth row
  let (count, next) := decodeHexadecimalNatAt payload start
  decodeNatValuesAtLoop payload count next #[]

/-- The sparse rank payloads use `String` literals directly.  Avoiding a
whole-string UTF-8 conversion on every lookup is essential: the kernel reads
only the bytes belonging to the requested row. -/
@[reducible] def hexadecimalCharDigit (character : Char) : Nat :=
  let value := character.toNat
  if 48 ≤ value ∧ value ≤ 57 then value - 48
  else if 97 ≤ value ∧ value ≤ 102 then value - 87
  else 0

@[reducible] def decodeStringHexadecimalNatAtLoop (payload : String) :
    Nat → Nat → Nat → Nat × Nat
  | 0, position, value => (value, position)
  | fuel + 1, position, value =>
      let character := String.Pos.Raw.get! payload ⟨position⟩
      if character.toNat = 10 then (value, position + 1)
      else decodeStringHexadecimalNatAtLoop payload fuel (position + 1)
        (16 * value + hexadecimalCharDigit character)

/-- Generated sparse payloads terminate every hexadecimal word with a newline
and use at most four hexadecimal digits per word.  A fixed local fuel bound
therefore prevents an indexed lookup from traversing the enclosing payload. -/
@[reducible] def stringHexadecimalTokenFuel : Nat := 8

@[reducible] def decodeStringHexadecimalNatAt (payload : String) (start : Nat) : Nat × Nat :=
  decodeStringHexadecimalNatAtLoop payload stringHexadecimalTokenFuel start 0

@[reducible] def decodeFixedWidthStringHexadecimalNatAt
    (offsets : String) (width index : Nat) : Nat :=
  (List.range width).foldl (fun value offset =>
    16 * value + hexadecimalCharDigit
      (String.Pos.Raw.get! offsets ⟨width * index + offset⟩)) 0

@[reducible] def decodeStringNatValuesAtLoop (payload : String) :
    Nat → Nat → Array Nat → Array Nat
  | 0, _, values => values
  | count + 1, position, values =>
      let (value, next) := decodeStringHexadecimalNatAt payload position
      decodeStringNatValuesAtLoop payload count next (values.push value)

/-- Decode one count-prefixed sparse row directly from a string payload and
its fixed-width byte-offset table. -/
@[reducible] def decodeCountPrefixedStringRowAt
    (payload offsets : String) (offsetWidth row : Nat) : Array Nat :=
  let start := decodeFixedWidthStringHexadecimalNatAt offsets offsetWidth row
  let (count, next) := decodeStringHexadecimalNatAt payload start
  decodeStringNatValuesAtLoop payload count next #[]

/-- Extract one fixed-width little-endian field from a packed natural number.
`Nat` arithmetic on closed numerals is kernel-optimized, unlike indexed
structural traversal of a byte payload. -/
@[reducible] def packedNatField (payload width index : Nat) : Nat :=
  (payload / 2 ^ (width * index)) % (2 ^ width)

@[reducible] def decodePackedNatValuesLoop (payload width : Nat) :
    Nat → Nat → Array Nat → Array Nat
  | 0, _, values => values
  | count + 1, position, values =>
      decodePackedNatValuesLoop payload width count (position + 1)
        (values.push (packedNatField payload width position))

/-- Decode one variable-width count-prefixed row from a packed numeral and a
packed fixed-width row-offset table.  `fieldWidth` records how many scalar
tokens form one encoded entry: one for scalar replay rows, two for integer
sparse rows, and three for rational sparse rows. -/
@[reducible] def decodeCountPrefixedPackedNatRow
    (payload offsets offsetWidth fieldWidth row : Nat) : Array Nat :=
  let start := packedNatField offsets offsetWidth row
  let count := packedNatField payload 16 start
  decodePackedNatValuesLoop payload 16 (count * fieldWidth) (start + 1) #[]

/-- Decode one count-prefixed row contained entirely in one packed natural
number.  Paged rank payloads use this form so every arithmetic shift is local
to one row rather than proportional to an entire certificate block. -/
@[reducible] def decodeCountPrefixedPackedNat (payload fieldWidth : Nat) : Array Nat :=
  let count := packedNatField payload 16 0
  decodePackedNatValuesLoop payload 16 (count * fieldWidth) 1 #[]

/-- Extract one field from a bounded row-local array of packed numerals.
The generator puts at most sixteen fields in each numeral, so kernel reduction
never divides by a power belonging to an entire dense sparse row. -/
@[reducible] def packedNatChunkField
    (payload : Array Nat) (width index : Nat) : Nat :=
  packedNatField (payload.getD (index / 16) 0) width (index % 16)

@[reducible] def decodePackedNatChunkValuesLoop (payload : Array Nat) (width : Nat) :
    Nat → Nat → Array Nat → Array Nat
  | 0, _, values => values
  | count + 1, position, values =>
      decodePackedNatChunkValuesLoop payload width count (position + 1)
        (values.push (packedNatChunkField payload width position))

/-- Decode one count-prefixed row from bounded row-local packed numerals. -/
@[reducible] def decodeCountPrefixedPackedNatChunks
    (payload : Array Nat) (fieldWidth : Nat) : Array Nat :=
  let count := packedNatChunkField payload 16 0
  decodePackedNatChunkValuesLoop payload 16 (count * fieldWidth) 1 #[]

/-- Consume a fixed number of values from a decoded token list. -/
@[reducible] def takeNatValues : Nat → List Nat → Array Nat → Option (Array Nat × List Nat)
  | 0, values, output => some (output, values)
  | _ + 1, [], _ => none
  | count + 1, value :: values, output =>
      takeNatValues count values (output.push value)

/-- Consume one count-prefixed row from a decoded token list. -/
@[reducible] def takeCountPrefixedNatRow :
    List Nat → Option (Array Nat × List Nat)
  | [] => none
  | count :: values => takeNatValues count values #[]

/-- Decode count-prefixed rows with a fuel bound supplied by the token count.
Malformed payloads decode to `none`, allowing a certificate replay to reject
them through its ordinary finite checks. -/
@[reducible] def decodeCountPrefixedNatRowsLoop :
    Nat → List Nat → Array (Array Nat) → Option (Array (Array Nat))
  | 0, [], output => some output
  | 0, _ :: _, _ => none
  | _ + 1, [], output => some output
  | fuel + 1, values, output => do
      let (row, remaining) ← takeCountPrefixedNatRow values
      decodeCountPrefixedNatRowsLoop fuel remaining (output.push row)

/-- Decode count-prefixed rows carried by one flat byte payload. -/
@[reducible] def decodeCountPrefixedNatRows (payload : ByteArray) : Array (Array Nat) :=
  let values := (decodeHexadecimalNatArray payload).toList
  match decodeCountPrefixedNatRowsLoop values.length values #[] with
  | some rows => rows
  | none => #[]

/-- Kernel check of the byte-level numeral convention used by OUR packed
finite-data realizations. -/
example :
    decodeHexadecimalNatArray "a\n10\n".toUTF8 = #[10, 16] := by
  decide +kernel

example :
    decodeCountPrefixedNatRows "2\na\nb\n0\n".toUTF8 = #[#[10, 11], #[]] := by
  decide +kernel

example :
    decodeCountPrefixedNatRowAt "2\na\nb\n1\nc\n".toUTF8 "0000000000000006".toUTF8 8 1 = #[12] := by
  decide +kernel

example :
    decodeCountPrefixedStringRowAt "2\na\nb\n1\nc\n" "0000000000000006" 8 1 = #[12] := by
  decide +kernel

example :
    decodeCountPrefixedPackedNatRow 0x000c0001000b000a0002 0x0000000300000000 32 1 1 = #[12] := by
  decide +kernel

example :
    decodeCountPrefixedPackedNat 0x000c0001 1 = #[12] := by
  decide +kernel

example :
    decodeCountPrefixedPackedNatChunks #[0x000c0001] 1 = #[12] := by
  decide +kernel

end HypercubicDimension16PackedFiniteDataCodec
end YangMills
end QuantumTheory
end Mettapedia
