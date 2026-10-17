import Mettapedia.GSLT.LanguageDef.CertificateGSLTOpenChecker
import Mettapedia.OSLF.MeTTaIL.PatternTokens
import Mettapedia.OSLF.Syntax.BindingWireBinary
import Mathlib.Data.Nat.Digits.Lemmas
import Mathlib.Tactic.FinCases
import Mathlib.Computability.Encoding

/-!
# Finite-alphabet storage of open and chronological certificates

The source objects remain the original open proof trees and ordered lemma
list. This module supplies their executable storage encoding, without changing
checking or rule admission. Names use the existing UTF-8 codec, patterns use
`PatternTokens`, and arbitrary premise indices use terminated binary digits.
The structural source weight counts numeric bits and UTF-8 payload bytes.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.CertificateDataEncoding

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.LanguageDef.CertificateGSLT
open Mettapedia.OSLF.Binding.WireCodec
open Mettapedia.OSLF.Binding.WireCodec.Binary

open Mettapedia.OSLF.MeTTaIL

/-- Pattern payloads retain the original exact token representation. -/
def patternCodec : Codec Pattern :=
  (Codec.list Codec.string).mapped PatternTokens.encode PatternTokens.decode PatternTokens.decode_encode

def instanceCodec : Codec RuleInstance :=
  (Codec.prod Codec.string (Codec.list patternCodec)).mapped
    (fun ruleInstance => (ruleInstance.ruleId.value, ruleInstance.arguments))
    (fun value => some ⟨⟨value.1⟩, value.2⟩) (fun _ => rfl)

mutual
  def putProof : RawOpenProof → Data
    | .premise index => .pair (.atom 0) (.atom index)
    | .node ruleInstance children => .pair (.atom 1)
        (.pair (instanceCodec.put ruleInstance) (putProofs children))
  def putProofs : List RawOpenProof → Data
    | [] => .atom 0
    | proof :: proofs => .pair (putProof proof) (putProofs proofs)
end

mutual
  def getProof : Data → Option RawOpenProof
    | .pair (.atom 0) (.atom index) => some (.premise index)
    | .pair (.atom 1) (.pair ruleInstance children) => do
        let ruleInstance ← instanceCodec.get ruleInstance
        let children ← getProofs children
        pure (.node ruleInstance children)
    | _ => none
  def getProofs : Data → Option (List RawOpenProof)
    | .atom 0 => some []
    | .pair proof proofs => do
        let proof ← getProof proof
        let proofs ← getProofs proofs
        pure (proof :: proofs)
    | _ => none
end

mutual
  theorem getProof_putProof (proof : RawOpenProof) : getProof (putProof proof) = some proof := by
    cases proof with
    | premise index => rfl
    | node ruleInstance children =>
        simp [putProof, getProof, instanceCodec.get_put, getProofs_putProofs children]
  termination_by sizeOf proof
  theorem getProofs_putProofs (proofs : List RawOpenProof) :
      getProofs (putProofs proofs) = some proofs := by
    cases proofs with
    | nil => rfl
    | cons proof proofs => simp [putProofs, getProofs, getProof_putProof proof,
        getProofs_putProofs proofs]
  termination_by sizeOf proofs
end

def proofCodec : Codec RawOpenProof := ⟨putProof, getProof, getProof_putProof⟩

/-- The existing chronological carrier, without a domain-specific dependency. -/
def sharedCodec : Codec (List (Pattern × RawOpenProof) × RawOpenProof) :=
  Codec.prod (Codec.list (Codec.prod patternCodec proofCodec)) proofCodec

def encodeProof : RawOpenProof → List Alphabet := encodeWith proofCodec
def decodeProof : List Alphabet → Option RawOpenProof := decodeWith proofCodec

def encodeShared : (List (Pattern × RawOpenProof) × RawOpenProof) → List Alphabet :=
  encodeWith sharedCodec

def decodeShared : List Alphabet → Option (List (Pattern × RawOpenProof) × RawOpenProof) :=
  decodeWith sharedCodec

theorem decodeProof_encodeProof (proof : RawOpenProof) : decodeProof (encodeProof proof) = some proof :=
  decodeWith_encodeWith proofCodec proof

theorem decodeShared_encodeShared (source : List (Pattern × RawOpenProof) × RawOpenProof) :
    decodeShared (encodeShared source) = some source := decodeWith_encodeWith sharedCodec source

theorem encodeProof_injective : Function.Injective encodeProof := encodeWith_injective proofCodec
theorem encodeShared_injective : Function.Injective encodeShared := encodeWith_injective sharedCodec

mutual
  /-- Counts source constructor boundaries, numeric bits, and UTF-8 name bytes.
  Pattern storage is measured by the existing independent structural weight. -/
  def proofWeight : RawOpenProof → Nat
    | .premise index => 1 + (Nat.digits 2 index).length
    | .node ruleInstance children => 1 + ruleInstance.ruleId.value.utf8ByteSize +
        PatternTokens.listWeight ruleInstance.arguments + proofsWeight children
  def proofsWeight : List RawOpenProof → Nat
    | [] => 1
    | proof :: proofs => 1 + proofWeight proof + proofsWeight proofs
end

def lemmasWeight : List (Pattern × RawOpenProof) → Nat
  | [] => 1
  | (goal, proof) :: lemmas => 1 + PatternTokens.weight goal + proofWeight proof + lemmasWeight lemmas

/-- Every submitted lemma contributes to the original packet footprint. -/
theorem lemmas_length_le_weight (lemmas : List (Pattern × RawOpenProof)) :
    lemmas.length ≤ lemmasWeight lemmas := by
  induction lemmas with
  | nil => simp [lemmasWeight]
  | cons entry lemmas ih =>
      rcases entry with ⟨goal, proof⟩
      simp only [List.length_cons, lemmasWeight]
      omega

/-- Any chronological goal prefix is charged by the entire submitted history,
including proofs that a later root never uses. -/
theorem lemmaGoals_prefix_weight (lemmas : List (Pattern × RawOpenProof)) (count : Nat) :
    PatternTokens.listWeight ((lemmas.take count).map Prod.fst) ≤ lemmasWeight lemmas := by
  induction lemmas generalizing count with
  | nil => simp [lemmasWeight, PatternTokens.listWeight]
  | cons entry lemmas ih =>
      rcases entry with ⟨goal, proof⟩
      cases count with
      | zero => simp only [List.take_zero, List.map_nil, PatternTokens.listWeight, lemmasWeight]; omega
      | succ count =>
          have later := ih count
          simp only [List.take_succ_cons, List.map_cons, PatternTokens.listWeight, lemmasWeight]
          omega

def sharedWeight (source : List (Pattern × RawOpenProof) × RawOpenProof) : Nat :=
  1 + lemmasWeight source.1 + proofWeight source.2

/-- Independent full-bit source measure: UTF-8 bytes cost eight bits, while
constructor boundaries and binary numeric fields are charged conservatively. -/
def proofBitWeight (proof : RawOpenProof) : Nat := 8 * proofWeight proof
def sharedBitWeight (source : List (Pattern × RawOpenProof) × RawOpenProof) : Nat :=
  8 * sharedWeight source


/-- The submitted goal is part of the physical input as well as the source
certificate. All chronological lemmas are stored, including unused entries. -/
def inputCodec : Codec (Pattern × (List (Pattern × RawOpenProof) × RawOpenProof)) :=
  Codec.prod patternCodec sharedCodec

def encodeInput (goal : Pattern) (source : List (Pattern × RawOpenProof) × RawOpenProof) :
    List Alphabet := encodeWith inputCodec (goal, source)

def decodeInput : List Alphabet → Option (Pattern × (List (Pattern × RawOpenProof) × RawOpenProof)) :=
  decodeWith inputCodec

def inputWeight (goal : Pattern) (source : List (Pattern × RawOpenProof) × RawOpenProof) : Nat :=
  1 + PatternTokens.weight goal + sharedWeight source

def inputBitWeight (goal : Pattern) (source : List (Pattern × RawOpenProof) × RawOpenProof) : Nat :=
  8 * inputWeight goal source

theorem decodeInput_encodeInput (goal : Pattern)
    (source : List (Pattern × RawOpenProof) × RawOpenProof) :
    decodeInput (encodeInput goal source) = some (goal, source) :=
  decodeWith_encodeWith inputCodec (goal, source)

theorem encodeInput_injective :
    Function.Injective (fun input : Pattern × (List (Pattern × RawOpenProof) × RawOpenProof) =>
      encodeInput input.1 input.2) := encodeWith_injective inputCodec

/-- Standard computability encoding of the original source tree. -/
def proofEncoding : Computability.Encoding RawOpenProof Alphabet where
  encode := encodeProof
  decode := decodeProof
  decode_encode := decodeProof_encodeProof

/-- Standard computability encoding of the original chronological carrier. -/
def sharedEncoding : Computability.Encoding (List (Pattern × RawOpenProof) × RawOpenProof) Alphabet where
  encode := encodeShared
  decode := decodeShared
  decode_encode := decodeShared_encodeShared

/-- The complete submitted input, including its independently supplied goal. -/
def inputEncoding : Computability.Encoding
    (Pattern × (List (Pattern × RawOpenProof) × RawOpenProof)) Alphabet where
  encode input := encodeInput input.1 input.2
  decode := decodeInput
  decode_encode input := decodeInput_encodeInput input.1 input.2

private theorem dataWeight_tokens (values : List String) :
    dataWeight ((Codec.list Codec.string).put values) ≤ 12 * PatternTokens.tokenSize values + 2 := by
  induction values with
  | nil => simp only [dataWeight_list_nil, PatternTokens.tokenSize]; omega
  | cons value values ih =>
    rw [dataWeight_list_cons, PatternTokens.tokenSize]
    have head := dataWeight_string value
    omega

mutual
  theorem patternWeight_positive (value : Pattern) : 1 ≤ PatternTokens.weight value := by
    cases value <;> simp [PatternTokens.weight] <;> omega
  theorem patternListWeight_positive (values : List Pattern) : 1 ≤ PatternTokens.listWeight values := by
    cases values with
    | nil => rfl
    | cons value values => simp only [PatternTokens.listWeight]; omega
end

/-- The serialized pattern payload is bounded by its structural source weight. -/
theorem dataWeight_pattern (value : Pattern) :
    dataWeight (patternCodec.put value) ≤ 74 * PatternTokens.weight value := by
  have payload := dataWeight_tokens (PatternTokens.encode value)
  have tokens := PatternTokens.encode_size value
  have positive := patternWeight_positive value
  change dataWeight ((Codec.list Codec.string).put (PatternTokens.encode value)) ≤ _
  omega

theorem dataWeight_patterns (values : List Pattern) :
    dataWeight ((Codec.list patternCodec).put values) ≤ 75 * PatternTokens.listWeight values := by
  induction values with
  | nil => simp only [dataWeight_list_nil, PatternTokens.listWeight]; omega
  | cons value values ih =>
    rw [dataWeight_list_cons, PatternTokens.listWeight]
    have head := dataWeight_pattern value
    omega

private theorem dataWeight_instance (ruleInstance : RuleInstance) :
    dataWeight (instanceCodec.put ruleInstance) ≤
      80 * (1 + ruleInstance.ruleId.value.utf8ByteSize + PatternTokens.listWeight ruleInstance.arguments) := by
  change dataWeight ((Codec.prod Codec.string (Codec.list patternCodec)).put
    (ruleInstance.ruleId.value, ruleInstance.arguments)) ≤ _
  rw [dataWeight_prod]
  change 1 + dataWeight (Codec.string.put ruleInstance.ruleId.value) +
    dataWeight ((Codec.list patternCodec).put ruleInstance.arguments) ≤ _
  have name := dataWeight_string ruleInstance.ruleId.value
  have arguments := dataWeight_patterns ruleInstance.arguments
  omega

mutual
  theorem dataWeight_proof (proof : RawOpenProof) :
      dataWeight (proofCodec.put proof) ≤ 128 * proofWeight proof := by
    cases proof with
    | premise index => simp [proofCodec, putProof, dataWeight, proofWeight]; omega
    | node ruleInstance children =>
      have arguments := dataWeight_instance ruleInstance
      have childrenBound := dataWeight_proofs children
      change dataWeight (putProof (.node ruleInstance children)) ≤ _
      simp only [putProof, dataWeight, proofWeight]
      have digits0 : (Nat.digits 2 1).length = 1 := by decide
      rw [digits0]
      omega
  termination_by sizeOf proof
  theorem dataWeight_proofs (proofs : List RawOpenProof) :
      dataWeight (putProofs proofs) ≤ 128 * proofsWeight proofs := by
    cases proofs with
    | nil => simp [putProofs, dataWeight, proofsWeight]
    | cons proof proofs =>
      have head := dataWeight_proof proof
      have tail := dataWeight_proofs proofs
      change dataWeight (putProofs (proof :: proofs)) ≤ _
      change dataWeight (putProof proof) ≤ _ at head
      simp only [putProofs, dataWeight, proofsWeight]
      omega
  termination_by sizeOf proofs
end

private theorem dataWeight_lemmas (lemmas : List (Pattern × RawOpenProof)) :
    dataWeight ((Codec.list (Codec.prod patternCodec proofCodec)).put lemmas) ≤
      128 * lemmasWeight lemmas := by
  induction lemmas with
  | nil => simp [dataWeight_list_nil, lemmasWeight]
  | cons entry lemmas ih =>
    rcases entry with ⟨goal, proof⟩
    rw [dataWeight_list_cons, dataWeight_prod, lemmasWeight]
    change 1 + (1 + dataWeight (patternCodec.put goal) + dataWeight (proofCodec.put proof)) +
      dataWeight ((Codec.list (Codec.prod patternCodec proofCodec)).put lemmas) ≤ _
    have goalBound := dataWeight_pattern goal
    have proofBound := dataWeight_proof proof
    omega

theorem dataWeight_shared (source : List (Pattern × RawOpenProof) × RawOpenProof) :
    dataWeight (sharedCodec.put source) ≤ 128 * sharedWeight source := by
  change dataWeight ((Codec.prod _ _).put source) ≤ _
  rw [dataWeight_prod, sharedWeight]
  have lemmas := dataWeight_lemmas source.1
  have root := dataWeight_proof source.2
  omega

/-- Physical finite-alphabet length, bounded independently of the encoder. -/
theorem encodeProof_length (proof : RawOpenProof) :
    (encodeProof proof).length ≤ 128 * proofWeight proof := by
  simpa [encodeProof, encodeWith, encodeData, writeData_length] using dataWeight_proof proof

theorem encodeShared_length (source : List (Pattern × RawOpenProof) × RawOpenProof) :
    (encodeShared source).length ≤ 128 * sharedWeight source := by
  simpa [encodeShared, encodeWith, encodeData, writeData_length] using dataWeight_shared source

theorem encodeInput_length (goal : Pattern)
    (source : List (Pattern × RawOpenProof) × RawOpenProof) :
    (encodeInput goal source).length ≤ 128 * inputWeight goal source := by
  have bound : dataWeight (inputCodec.put (goal, source)) ≤ 128 * inputWeight goal source := by
    change dataWeight ((Codec.prod _ _).put (goal, source)) ≤ _
    rw [dataWeight_prod, inputWeight]
    change 1 + dataWeight (patternCodec.put goal) + dataWeight (sharedCodec.put source) ≤ _
    have goalBound := dataWeight_pattern goal
    have sourceBound := dataWeight_shared source
    omega
  simpa [encodeInput, encodeWith, encodeData, writeData_length] using bound

/-- Three physical bits suffice per alphabet symbol. This is a storage bound,
not a bound on decoder execution time. -/
theorem encodeInput_bit_bound (goal : Pattern)
    (source : List (Pattern × RawOpenProof) × RawOpenProof) :
    3 * (encodeInput goal source).length ≤ 48 * inputBitWeight goal source := by
  have length := encodeInput_length goal source
  unfold inputBitWeight
  omega

theorem encodeShared_bit_bound (source : List (Pattern × RawOpenProof) × RawOpenProof) :
    3 * (encodeShared source).length ≤ 48 * sharedBitWeight source := by
  have length := encodeShared_length source
  unfold sharedBitWeight
  omega

private theorem option_weight_lower (value : Option String) (tail : List String) :
    PatternTokens.optionWeight value + PatternTokens.tokenSize tail ≤
      PatternTokens.tokenSize (PatternTokens.option value tail) := by
  cases value <;> simp only [PatternTokens.optionWeight, PatternTokens.option, PatternTokens.tokenSize] <;> omega

private theorem names_weight_lower (values tail : List String) :
    PatternTokens.namesWeight values + PatternTokens.tokenSize tail ≤
      PatternTokens.tokenSize (PatternTokens.names values tail) := by
  induction values with
  | nil => simp only [PatternTokens.namesWeight, PatternTokens.names, PatternTokens.tokenSize]; omega
  | cons name rest ih =>
    simp only [PatternTokens.namesWeight, PatternTokens.names, PatternTokens.tokenSize]
    omega

mutual
  theorem pattern_write_weight_lower (value : Pattern) (tail : List String) :
      PatternTokens.weight value + PatternTokens.tokenSize tail ≤
        PatternTokens.tokenSize (PatternTokens.write value tail) := by
    cases value with
    | bvar index =>
      simp only [PatternTokens.weight, PatternTokens.write, PatternTokens.tokenSize,
        PatternTokens.tokenSize_append, PatternTokens.tokenSize_bits]
      omega
    | fvar name => simp only [PatternTokens.weight, PatternTokens.write, PatternTokens.tokenSize]; omega
    | apply name arguments =>
      have child := patterns_write_weight_lower arguments tail
      simp only [PatternTokens.weight, PatternTokens.write, PatternTokens.tokenSize]
      omega
    | lambda name body =>
      have child := pattern_write_weight_lower body tail
      have metadata := option_weight_lower name (PatternTokens.write body tail)
      simp only [PatternTokens.weight, PatternTokens.write, PatternTokens.tokenSize]
      omega
    | multiLambda arity binderNames body =>
      have child := pattern_write_weight_lower body tail
      have metadata := names_weight_lower binderNames (PatternTokens.write body tail)
      simp only [PatternTokens.weight, PatternTokens.write, PatternTokens.tokenSize,
        PatternTokens.tokenSize_append, PatternTokens.tokenSize_bits]
      omega
    | subst body replacement =>
      have first := pattern_write_weight_lower body (PatternTokens.write replacement tail)
      have second := pattern_write_weight_lower replacement tail
      simp only [PatternTokens.weight, PatternTokens.write, PatternTokens.tokenSize]
      omega
    | collection kind elements rest =>
      have child := patterns_write_weight_lower elements tail
      have metadata := option_weight_lower rest (PatternTokens.writeList elements tail)
      cases kind <;> simp only [PatternTokens.weight, PatternTokens.write, PatternTokens.collection,
        PatternTokens.tokenSize] <;> omega
  termination_by sizeOf value
  decreasing_by all_goals sizeOf_pattern_dec
  theorem patterns_write_weight_lower (values : List Pattern) (tail : List String) :
      PatternTokens.listWeight values + PatternTokens.tokenSize tail ≤
        PatternTokens.tokenSize (PatternTokens.writeList values tail) := by
    cases values with
    | nil => simp only [PatternTokens.listWeight, PatternTokens.writeList, PatternTokens.tokenSize]; omega
    | cons value values =>
      have first := pattern_write_weight_lower value (PatternTokens.writeList values tail)
      have rest := patterns_write_weight_lower values tail
      simp only [PatternTokens.listWeight, PatternTokens.writeList, PatternTokens.tokenSize]
      omega
  termination_by sizeOf values
  decreasing_by all_goals sizeOf_pattern_dec
end

private theorem dataWeight_tokens_lower (values : List String) :
    PatternTokens.tokenSize values ≤ dataWeight ((Codec.list Codec.string).put values) := by
  induction values with
  | nil => simp only [PatternTokens.tokenSize, dataWeight_list_nil]; omega
  | cons value values ih =>
    rw [dataWeight_list_cons, PatternTokens.tokenSize]
    have head := dataWeight_string_lower value
    omega

theorem dataWeight_pattern_lower (value : Pattern) :
    PatternTokens.weight value ≤ dataWeight (patternCodec.put value) := by
  have tokens := pattern_write_weight_lower value []
  have data := dataWeight_tokens_lower (PatternTokens.encode value)
  change PatternTokens.weight value ≤
    dataWeight ((Codec.list Codec.string).put (PatternTokens.encode value))
  simpa only [PatternTokens.encode, PatternTokens.tokenSize, Nat.add_zero] using tokens.trans data

theorem dataWeight_patterns_lower (values : List Pattern) :
    PatternTokens.listWeight values ≤ dataWeight ((Codec.list patternCodec).put values) := by
  induction values with
  | nil => simp only [PatternTokens.listWeight, dataWeight_list_nil]; omega
  | cons value values ih =>
    rw [dataWeight_list_cons, PatternTokens.listWeight]
    have head := dataWeight_pattern_lower value
    omega

private theorem dataWeight_instance_lower (ruleInstance : RuleInstance) :
    1 + ruleInstance.ruleId.value.utf8ByteSize + PatternTokens.listWeight ruleInstance.arguments ≤
      dataWeight (instanceCodec.put ruleInstance) := by
  have name := dataWeight_string_lower ruleInstance.ruleId.value
  have arguments := dataWeight_patterns_lower ruleInstance.arguments
  change 1 + ruleInstance.ruleId.value.utf8ByteSize + PatternTokens.listWeight ruleInstance.arguments ≤
    1 + dataWeight (Codec.string.put ruleInstance.ruleId.value) +
      dataWeight ((Codec.list patternCodec).put ruleInstance.arguments)
  omega

mutual
  theorem dataWeight_proof_lower (proof : RawOpenProof) :
      proofWeight proof ≤ dataWeight (proofCodec.put proof) := by
    cases proof with
    | premise index => simp only [proofCodec, putProof, dataWeight, proofWeight]; omega
    | node ruleInstance children =>
      have arguments := dataWeight_instance_lower ruleInstance
      have childrenBound := dataWeight_proofs_lower children
      change proofWeight (.node ruleInstance children) ≤ dataWeight (putProof (.node ruleInstance children))
      simp only [putProof, dataWeight, proofWeight]
      omega
  termination_by sizeOf proof
  theorem dataWeight_proofs_lower (proofs : List RawOpenProof) :
      proofsWeight proofs ≤ dataWeight (putProofs proofs) := by
    cases proofs with
    | nil => simp only [putProofs, proofsWeight, dataWeight]; decide
    | cons proof proofs =>
      have first := dataWeight_proof_lower proof
      have rest := dataWeight_proofs_lower proofs
      change proofWeight proof ≤ dataWeight (putProof proof) at first
      simp only [putProofs, proofsWeight, dataWeight]
      omega
  termination_by sizeOf proofs
end

private theorem dataWeight_lemmas_lower (lemmas : List (Pattern × RawOpenProof)) :
    lemmasWeight lemmas ≤ dataWeight ((Codec.list (Codec.prod patternCodec proofCodec)).put lemmas) := by
  induction lemmas with
  | nil => simp only [dataWeight_list_nil, lemmasWeight]; decide
  | cons entry lemmas ih =>
    rcases entry with ⟨goal, proof⟩
    rw [dataWeight_list_cons, dataWeight_prod, lemmasWeight]
    have goalBound := dataWeight_pattern_lower goal
    have proofBound := dataWeight_proof_lower proof
    change 1 + PatternTokens.weight goal + proofWeight proof + lemmasWeight lemmas ≤
      1 + (1 + dataWeight (patternCodec.put goal) + dataWeight (proofCodec.put proof)) +
        dataWeight ((Codec.list (Codec.prod patternCodec proofCodec)).put lemmas)
    omega

theorem dataWeight_shared_lower (source : List (Pattern × RawOpenProof) × RawOpenProof) :
    sharedWeight source ≤ dataWeight (sharedCodec.put source) := by
  have lemmas := dataWeight_lemmas_lower source.1
  have root := dataWeight_proof_lower source.2
  change 1 + lemmasWeight source.1 + proofWeight source.2 ≤
    1 + dataWeight ((Codec.list (Codec.prod patternCodec proofCodec)).put source.1) +
      dataWeight (proofCodec.put source.2)
  omega

theorem encodeInput_length_lower (goal : Pattern)
    (source : List (Pattern × RawOpenProof) × RawOpenProof) :
    inputWeight goal source ≤ (encodeInput goal source).length := by
  have goalBound := dataWeight_pattern_lower goal
  have sourceBound := dataWeight_shared_lower source
  rw [encodeInput, encodeWith, encodeData, writeData_length]
  change 1 + PatternTokens.weight goal + sharedWeight source ≤
    (1 + dataWeight (patternCodec.put goal) + dataWeight (sharedCodec.put source)) + 0
  omega

/-- The independent bit measure is also bounded by the actual encoded input.
Together with `encodeInput_length`, this rules out hidden uncharged payloads. -/
theorem inputBitWeight_le_encoded (goal : Pattern)
    (source : List (Pattern × RawOpenProof) × RawOpenProof) :
    inputBitWeight goal source ≤ 8 * (encodeInput goal source).length := by
  unfold inputBitWeight
  exact Nat.mul_le_mul_left 8 (encodeInput_length_lower goal source)

theorem binary_digits_power (exponent : Nat) : (Nat.digits 2 (2 ^ exponent)).length = exponent + 1 := by
  have lower : exponent < (Nat.digits 2 (2 ^ exponent)).length :=
    (Nat.lt_digits_length_iff (by decide) _).mpr (Nat.le_refl _)
  have upper : (Nat.digits 2 (2 ^ exponent)).length ≤ exponent + 1 := by
    apply (Nat.digits_length_le_iff (by decide) _).mpr
    have positive : 0 < 2 ^ exponent := pow_pos (by decide) exponent
    rw [pow_succ]
    omega
  omega

theorem encodeProof_premise_length (index : Nat) :
    (encodeProof (.premise index)).length = 5 + (Nat.digits 2 index).length := by
  simp [encodeProof, encodeWith, encodeData, writeData_length, proofCodec, putProof, dataWeight]
  omega

theorem proofWeight_premise_power (exponent : Nat) :
    proofWeight (.premise (2 ^ exponent)) = exponent + 2 := by
  rw [proofWeight, binary_digits_power]
  omega

namespace Controls

def hugeReference : RawOpenProof := .premise (2 ^ 4096)

def unicodeName : String := String.join (List.replicate 1024 "λ漢🙂\x00")

def unicodeProof : RawOpenProof :=
  .node ⟨⟨unicodeName⟩, [.lambda (some unicodeName) (.bvar 0)]⟩ []

def chronological : List (Pattern × RawOpenProof) × RawOpenProof :=
  ([(.fvar unicodeName, hugeReference), (.bvar 1, unicodeProof)], .premise 0)

theorem huge_roundtrip : decodeProof (encodeProof hugeReference) = some hugeReference :=
  decodeProof_encodeProof _

theorem huge_storage_length : (encodeProof hugeReference).length = 4102 := by
  rw [hugeReference, encodeProof_premise_length, binary_digits_power]

theorem huge_refused (definition : ValidatedCalculusLanguageDef) (goal : Pattern) :
    checkOpenRaw definition [] goal hugeReference = false := by
  change checkOpenRaw definition [] goal (.premise _) = false
  rw [checkOpenRaw]
  rfl

theorem unicode_roundtrip : decodeProof (encodeProof unicodeProof) = some unicodeProof :=
  decodeProof_encodeProof _

theorem chronological_roundtrip : decodeShared (encodeShared chronological) = some chronological :=
  decodeShared_encodeShared _

theorem goal_roundtrip :
    decodeInput (encodeInput (.fvar unicodeName) chronological) =
      some (.fvar unicodeName, chronological) := decodeInput_encodeInput _ _

theorem unterminated_natural_refused : decodeData [3, 1, 0] = none := by decide

theorem malformed_pair_refused : decodeProof [4, 3, 2] = none := by decide

theorem different_references : encodeProof (.premise 0) ≠ encodeProof (.premise 1) := by
  intro same
  have source := encodeProof_injective same
  cases source

end Controls

end Mettapedia.GSLT.LanguageDef.CertificateDataEncoding
