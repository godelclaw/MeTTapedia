import Mettapedia.Computability.KolmogorovComplexity.SelfDelimitingCode

/-!
# Canonical framing for binary records

A record contains its field count, then each field in the existing E2 code.
Decoders return the unused suffix. Both the count and every field header must
be canonical: accepting a redundant binary length would make measured lengths
depend on which spelling of an otherwise identical record was supplied.

The fields are arbitrary bit strings. Application schemas separately assign
meaning to signatures, literal payloads, definitions and residuals. This layer
does not obtain any such data from an uncharged external dictionary.
-/

namespace Mettapedia.Algorithms.Compression.Framing

open KolmogorovComplexity

def readField (input : BinString) : Option (BinString × BinString) :=
  match e2decode input with
  | none => none
  | some (field, rest) =>
      if e2encode field ++ rest = input then some (field, rest) else none

theorem readField_encode (field rest : BinString) :
    readField (e2encode field ++ rest) = some (field, rest) := by
  simp [readField, e2decode_e2encode_append]

theorem readField_sound {input field rest : BinString}
    (decoded : readField input = some (field, rest)) :
    e2encode field ++ rest = input := by
  unfold readField at decoded
  cases h : e2decode input with
  | none => simp [h] at decoded
  | some value =>
      rcases value with ⟨head, tail⟩
      simp only [h] at decoded
      split at decoded
      · rename_i canonical
        cases Option.some.inj decoded
        exact canonical
      · cases decoded

def writeNat (value : Nat) : BinString := e2encode (binaryBits value)

def readNat (input : BinString) : Option (Nat × BinString) :=
  match readField input with
  | none => none
  | some (digits, rest) =>
      let value := ofBinaryBits digits
      if binaryBits value = digits then some (value, rest) else none

theorem readNat_write (value : Nat) (rest : BinString) :
    readNat (writeNat value ++ rest) = some (value, rest) := by
  simp [readNat, writeNat, readField_encode, ofBinaryBits_binaryBits]

theorem readNat_sound {input rest : BinString} {value : Nat}
    (decoded : readNat input = some (value, rest)) :
    writeNat value ++ rest = input := by
  unfold readNat at decoded
  cases hf : readField input with
  | none => simp [hf] at decoded
  | some pair =>
      rcases pair with ⟨digits, tail⟩
      simp only [hf] at decoded
      split at decoded
      · rename_i canonical
        cases Option.some.inj decoded
        simpa [writeNat, canonical] using readField_sound hf
      · cases decoded

def writeFields (fields : List BinString) : BinString := fields.flatMap e2encode

def readFields : Nat → BinString → Option (List BinString × BinString)
  | 0, input => some ([], input)
  | count + 1, input =>
      match readField input with
      | none => none
      | some (field, tail) =>
          match readFields count tail with
          | none => none
          | some (fields, rest) => some (field :: fields, rest)

theorem readFields_write (fields : List BinString) (rest : BinString) :
    readFields fields.length (writeFields fields ++ rest) = some (fields, rest) := by
  induction fields with
  | nil => rfl
  | cons field fields ih =>
      simp only [List.length_cons, writeFields, List.flatMap_cons, List.append_assoc]
      simp only [readFields, readField_encode]
      change (match readFields fields.length (writeFields fields ++ rest) with
        | none => none
        | some (tail, suffix) => some (field :: tail, suffix)) = _
      rw [ih]

theorem readFields_sound {count : Nat} {input rest : BinString} {fields : List BinString}
    (decoded : readFields count input = some (fields, rest)) :
    fields.length = count ∧ writeFields fields ++ rest = input := by
  induction count generalizing input fields with
  | zero =>
      cases Option.some.inj decoded
      exact ⟨rfl, rfl⟩
  | succ count ih =>
      simp only [readFields] at decoded
      cases hf : readField input with
      | none => simp [hf] at decoded
      | some pair =>
          rcases pair with ⟨field, tail⟩
          simp only [hf] at decoded
          cases hs : readFields count tail with
          | none => simp [hs] at decoded
          | some pair =>
              rcases pair with ⟨remaining, suffix⟩
              simp only [hs] at decoded
              cases Option.some.inj decoded
              obtain ⟨length, reconstructed⟩ := ih hs
              refine ⟨by simp [length], ?_⟩
              simpa [writeFields, List.append_assoc, ← reconstructed] using readField_sound hf

def encode (fields : List BinString) : BinString :=
  writeNat fields.length ++ writeFields fields

def decode (input : BinString) : Option (List BinString × BinString) :=
  match readNat input with
  | none => none
  | some (count, rest) => readFields count rest

theorem decode_encode_append (fields : List BinString) (suffix : BinString) :
    decode (encode fields ++ suffix) = some (fields, suffix) := by
  simp only [decode, encode, List.append_assoc, readNat_write, readFields_write]

theorem decode_sound {input rest : BinString} {fields : List BinString}
    (decoded : decode input = some (fields, rest)) :
    encode fields ++ rest = input := by
  unfold decode at decoded
  cases hn : readNat input with
  | none => simp [hn] at decoded
  | some pair =>
      rcases pair with ⟨count, tail⟩
      simp only [hn] at decoded
      obtain ⟨length, reconstructed⟩ := readFields_sound decoded
      simpa [encode, length, List.append_assoc, reconstructed] using readNat_sound hn

theorem encode_prefix {left right : List BinString} (hpref : encode left <+: encode right) :
    left = right := by
  obtain ⟨suffix, equality⟩ := hpref
  have hl := decode_encode_append left suffix
  have hr := decode_encode_append right []
  rw [List.append_nil, ← equality, hl] at hr
  exact congrArg Prod.fst (Option.some.inj hr)

theorem encode_injective : Function.Injective encode := by
  intro left right equal
  exact encode_prefix ⟨[], by simpa using equal⟩

theorem record_prefixFree : PrefixFree (Set.range encode) := by
  intro left hl right hr different hpref
  obtain ⟨a, rfl⟩ := hl
  obtain ⟨b, rfl⟩ := hr
  exact different (congrArg encode (encode_prefix hpref))

theorem encoded_length (fields : List BinString) :
    (encode fields).length = (writeNat fields.length).length +
      (fields.map fun field => field.length + 2 * (binaryBits field.length).length + 1).sum := by
  simp [encode, writeFields, List.length_flatMap, e2encode_length]

/-- Byte packing must pay for its final partial byte. -/
def byteLength (fields : List BinString) : Nat := ((encode fields).length + 7) / 8

/-- Exact packed length from payload bit lengths, without constructing fields. -/
def measure (lengths : List Nat) : Nat :=
  ((writeNat lengths.length).length +
    (lengths.map fun n => n + 2 * (binaryBits n).length + 1).sum + 7) / 8

theorem byteLength_measure (fields : List BinString) :
    byteLength fields = measure (fields.map List.length) := by
  simp only [byteLength, measure, encoded_length, List.length_map, List.map_map, Function.comp_def]

theorem byteLength_covers (fields : List BinString) :
    (encode fields).length ≤ 8 * byteLength fields ∧
      8 * byteLength fields < (encode fields).length + 8 := by
  unfold byteLength
  omega

def paddingLength (bits : Nat) : Nat := (8 - bits % 8) % 8

theorem paddingLength_lt (bits : Nat) : paddingLength bits < 8 := by
  exact Nat.mod_lt _ (by decide)

theorem paddingLength_total (bits : Nat) :
    bits + paddingLength bits = 8 * ((bits + 7) / 8) := by
  unfold paddingLength
  omega

/-- Most-significant-bit-first byte packing completes precisely one final
partial byte. These bit strings have length divisible by eight. -/
def encodePadded (fields : List BinString) : BinString :=
  encode fields ++ List.replicate (paddingLength (encode fields).length) false

def decodePadded (input : BinString) : Option (List BinString) :=
  match decode input with
  | none => none
  | some (fields, rest) =>
      if input.length % 8 = 0 ∧ rest.length < 8 ∧
          rest = List.replicate rest.length false then some fields else none

theorem encodePadded_length (fields : List BinString) :
    (encodePadded fields).length = 8 * byteLength fields := by
  simpa [encodePadded, byteLength] using paddingLength_total (encode fields).length

theorem decodePadded_encode (fields : List BinString) :
    decodePadded (encodePadded fields) = some fields := by
  have aligned : (encodePadded fields).length % 8 = 0 := by
    rw [encodePadded_length]
    omega
  unfold decodePadded
  rw [show decode (encodePadded fields) =
    some (fields, List.replicate (paddingLength (encode fields).length) false) from
      decode_encode_append _ _]
  simp [aligned, paddingLength_lt]

/-- Successful padded decoding admits exactly the canonical packed bytes;
neither an extra zero byte nor a redundant E2 header is another spelling. -/
theorem decodePadded_sound {input : BinString} {fields : List BinString}
    (decoded : decodePadded input = some fields) : encodePadded fields = input := by
  unfold decodePadded at decoded
  cases hd : decode input with
  | none => simp [hd] at decoded
  | some pair =>
      rcases pair with ⟨values, rest⟩
      simp only [hd] at decoded
      split at decoded
      · rename_i canonical
        cases Option.some.inj decoded
        have reconstructed := decode_sound hd
        have lengths : (encode fields).length + rest.length = input.length := by
          simpa using congrArg List.length reconstructed
        have padding : rest.length = paddingLength (encode fields).length := by
          unfold paddingLength
          have := canonical.1
          have := canonical.2.1
          omega
        rw [encodePadded, ← padding, ← canonical.2.2]
        exact reconstructed
      · cases decoded

theorem encodePadded_injective : Function.Injective encodePadded := by
  intro left right same
  have h := decodePadded_encode left
  rw [same, decodePadded_encode] at h
  exact (Option.some.inj h).symm

theorem extra_zero_byte_refused : decodePadded (List.replicate 16 false) = none := by decide

theorem noncanonical_field_refused : readField [true, false, false] = none := by decide

theorem empty_record_is_framed : encode [] = [false] := by decide

theorem truncated_record_refused : decode ((encode [[true, false]]).dropLast) = none := by
  decide

end Mettapedia.Algorithms.Compression.Framing
