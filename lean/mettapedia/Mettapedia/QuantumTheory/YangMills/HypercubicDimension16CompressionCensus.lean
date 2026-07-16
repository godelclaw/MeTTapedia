import Mettapedia.QuantumTheory.YangMills.HypercubicRawFDCharacterCertificate
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16SU2TraceRelations

/-!
# Exact evaluation of a dimension-sixteen cycle-index compression target

This module evaluates an explicitly defined cycle-index expression motivated
by three elementary reductions which do not use Bianchi, EOM, IBP, the
covariant commutator, or matrix trace identities:

* field antisymmetry replaces each ordered axis pair by the six-dimensional
  signed two-form representation;
* adjacent different-owner shuffles retain one ordered derivative word for
  each field letter;
* simultaneous field relabeling makes the trace permutation and decorated
  field letters unlabeled.

For a field-label permutation of cycle type `lambda`, its centralizer count
cancels the conjugacy-class denominator in Burnside averaging.  The remaining
character contribution is a product over the parts `r` of `lambda`.  A part
of length `r` contributes the two-form character of `h^r` and a local
derivative word whose `k` axes contribute `trace(h^r)^k` at derivative degree
`r*k`.

The resulting values are a compression target, not yet a carrier theorem and
not the rank of the physical relation quotient.  In particular, this module
does not construct a finite normal-form carrier whose character is the
cycle-index expression, and it does not claim a quotient equivalence between
the adjacent-shuffle row span and the selected local-word normal form.
-/

set_option autoImplicit false
set_option maxHeartbeats 8000000
noncomputable section

open scoped BigOperators

namespace Mettapedia
namespace QuantumTheory
namespace YangMills
namespace HypercubicDimension16CompressionCensus

open V14HypercubicFDCensus
open V14HypercubicQuarticCensus
open HypercubicRawFDCharacterCensus

/-! ## Transparent integer partitions through eight fields -/

def fieldPartitions : ℕ → List (List ℕ)
  | 1 => [[1]]
  | 2 => [[2], [1, 1]]
  | 3 => [[3], [2, 1], [1, 1, 1]]
  | 4 => [[4], [3, 1], [2, 2], [2, 1, 1], [1, 1, 1, 1]]
  | 5 => [[5], [4, 1], [3, 2], [3, 1, 1], [2, 2, 1],
      [2, 1, 1, 1], [1, 1, 1, 1, 1]]
  | 6 => [[6], [5, 1], [4, 2], [4, 1, 1], [3, 3], [3, 2, 1],
      [3, 1, 1, 1], [2, 2, 2], [2, 2, 1, 1], [2, 1, 1, 1, 1],
      [1, 1, 1, 1, 1, 1]]
  | 7 => [[7], [6, 1], [5, 2], [5, 1, 1], [4, 3], [4, 2, 1],
      [4, 1, 1, 1], [3, 3, 1], [3, 2, 2], [3, 2, 1, 1],
      [3, 1, 1, 1, 1], [2, 2, 2, 1], [2, 2, 1, 1, 1],
      [2, 1, 1, 1, 1, 1], [1, 1, 1, 1, 1, 1, 1]]
  | 8 => [[8], [7, 1], [6, 2], [6, 1, 1], [5, 3], [5, 2, 1],
      [5, 1, 1, 1], [4, 4], [4, 3, 1], [4, 2, 2], [4, 2, 1, 1],
      [4, 1, 1, 1, 1], [3, 3, 2], [3, 3, 1, 1], [3, 2, 2, 1],
      [3, 2, 1, 1, 1], [3, 1, 1, 1, 1, 1], [2, 2, 2, 2],
      [2, 2, 2, 1, 1], [2, 2, 1, 1, 1, 1],
      [2, 1, 1, 1, 1, 1, 1], [1, 1, 1, 1, 1, 1, 1, 1]]
  | _ => []

def derivativeCountForFields (fieldCount : ℕ) : ℕ :=
  16 - 2 * fieldCount

/-! ## Signed two-form and local-word characters -/

/-- Character of the standard signed four-vector representation. -/
def vectorCharacter (h : Hypercubic4) : ℚ :=
  signedAxisTrace h

/-! Powers are evaluated through an axis-level recurrence.  This is
definitionally much smaller than repeatedly constructing signed-permutation
structures, while the bridge theorem below identifies it with the literal
group power. -/

def powerAxis (h : Hypercubic4) : ℕ → Axis → Axis
  | 0, axis => axis
  | exponent + 1, axis => powerAxis h exponent (h.perm axis)

def powerReflected (h : Hypercubic4) : ℕ → Axis → Bool
  | 0, _ => false
  | exponent + 1, axis =>
      h.reflected axis ^^ powerReflected h exponent (h.perm axis)

theorem hypercubic_pow_perm_apply (h : Hypercubic4)
    (exponent : ℕ) (axis : Axis) :
    (h ^ exponent).perm axis = powerAxis h exponent axis := by
  induction exponent generalizing axis with
  | zero => rfl
  | succ exponent ih =>
      rw [pow_succ, hypercubic_mul_def]
      simp only [Hypercubic4.compose_perm_apply, powerAxis]
      exact ih (h.perm axis)

theorem hypercubic_pow_reflected_apply (h : Hypercubic4)
    (exponent : ℕ) (axis : Axis) :
    (h ^ exponent).reflected axis = powerReflected h exponent axis := by
  induction exponent generalizing axis with
  | zero => rfl
  | succ exponent ih =>
      rw [pow_succ, hypercubic_mul_def]
      simp only [Hypercubic4.compose_reflected, powerReflected]
      rw [ih]

def recurrentVectorPowerTraceTerm (h : Hypercubic4)
    (exponent : ℕ) (axis : Axis) : ℤ :=
  if powerAxis h exponent axis = axis then
    if powerReflected h exponent axis then -1 else 1
  else 0

def recurrentVectorPowerTrace (h : Hypercubic4)
    (exponent : ℕ) : ℤ :=
  ((recurrentVectorPowerTraceTerm h exponent 0 +
    recurrentVectorPowerTraceTerm h exponent 1) +
    recurrentVectorPowerTraceTerm h exponent 2) +
    recurrentVectorPowerTraceTerm h exponent 3

def recurrentVectorPowerCharacter (h : Hypercubic4)
    (exponent : ℕ) : ℚ :=
  recurrentVectorPowerTrace h exponent

theorem recurrentVectorPowerCharacter_eq (h : Hypercubic4)
    (exponent : ℕ) :
    recurrentVectorPowerCharacter h exponent =
      vectorCharacter (h ^ exponent) := by
  unfold recurrentVectorPowerCharacter recurrentVectorPowerTrace
  unfold recurrentVectorPowerTraceTerm vectorCharacter
  rw [signedAxisTrace_four_terms]
  simp only [Int.cast_add, Int.cast_ite, Int.cast_neg, Int.cast_one,
    Int.cast_zero, hypercubic_pow_perm_apply,
    hypercubic_pow_reflected_apply, Hypercubic4.axisSign]

/-- Character of its exterior square, obtained from
`chi_{Lambda^2 V}(h) = (chi_V(h)^2 - chi_V(h^2))/2`. -/
def twoFormCharacter (h : Hypercubic4) : ℚ :=
  (vectorCharacter h ^ 2 - vectorCharacter (h ^ 2)) / 2

/-- Contribution of one field-label cycle of length `cycleLength`, carrying
`localDerivativeCount` ordered derivative axes per field. -/
def cycleLetterCharacter (h : Hypercubic4) (cycleLength : ℕ)
    (localDerivativeCount : ℕ) : ℚ :=
  let powered := h ^ cycleLength
  twoFormCharacter powered *
    vectorCharacter powered ^ localDerivativeCount

@[simp] theorem hypercubicLiteralOne_pow (exponent : ℕ) :
    Hypercubic4.one ^ exponent = Hypercubic4.one := by
  rw [← hypercubic_one_def]
  simp only [one_pow]

@[simp] theorem vectorCharacter_hypercubicLiteralOne :
    vectorCharacter Hypercubic4.one = 4 := by
  norm_num [vectorCharacter, signedAxisTrace, Hypercubic4.axisSign,
    Hypercubic4.one, Fin.sum_univ_succ]

@[simp] theorem twoFormCharacter_hypercubicLiteralOne :
    twoFormCharacter Hypercubic4.one = 6 := by
  norm_num [twoFormCharacter]

/-- Coefficient at total derivative degree `remainingDegree` in the product
of the cycle-letter series for `parts`. -/
def partitionDerivativeCharacter (h : Hypercubic4) :
    List ℕ → ℕ → ℚ
  | [], remainingDegree => if remainingDegree = 0 then 1 else 0
  | cycleLength :: rest, remainingDegree =>
      ∑ localDerivativeCount ∈
          Finset.range (remainingDegree / cycleLength + 1),
        cycleLetterCharacter h cycleLength localDerivativeCount *
          partitionDerivativeCharacter h rest
            (remainingDegree - cycleLength * localDerivativeCount)

/-- Proposed cycle-index character expression in the `fieldCount` sector. -/
def compressedSectorCharacter (h : Hypercubic4)
    (fieldCount : ℕ) : ℚ :=
  ∑ parts ∈ (fieldPartitions fieldCount).toFinset,
    partitionDerivativeCharacter h parts
      (derivativeCountForFields fieldCount)

/-! ## Encoded Reynolds moments and certified values -/

def encodedCompressionReflectionMoment
    (parity : ContractionParity) (permutation : Fin 24)
    (fieldCount : ℕ) : ℚ :=
  ∑ reflectionMask : Fin 16,
    let h := decodedHypercubicCharacterElement permutation reflectionMask
    parity.character h * compressedSectorCharacter h fieldCount

def encodedCompressionMoment (parity : ContractionParity)
    (fieldCount : ℕ) : ℚ :=
  ∑ permutation : Fin 24,
    encodedCompressionReflectionMoment parity permutation fieldCount

def compressedInvariantMultiplicity (parity : ContractionParity)
    (fieldCount : ℕ) : ℚ :=
  encodedCompressionMoment parity fieldCount / 384

/-- Expected cycle-index Reynolds values, in field counts one through eight. -/
def expectedCompressedInvariantMultiplicity
    (parity : ContractionParity) (fieldCount : ℕ) : ℕ :=
  match parity, fieldCount with
  | .scalar, 1 => 8390656
  | .scalar, 2 => 40913408
  | .scalar, 3 => 78150656
  | .scalar, 4 => 73875844
  | .scalar, 5 => 35789694
  | .scalar, 6 => 8280892
  | .scalar, 7 => 723988
  | .scalar, 8 => 11654
  | .pseudoscalar, 1 => 8390656
  | .pseudoscalar, 2 => 40909312
  | .pseudoscalar, 3 => 78150656
  | .pseudoscalar, 4 => 73868100
  | .pseudoscalar, 5 => 35789694
  | .pseudoscalar, 6 => 8277340
  | .pseudoscalar, 7 => 723988
  | .pseudoscalar, 8 => 11346
  | _, _ => 0

/-- Expected identity-specialized cycle-index values in sectors one through
eight.  A carrier-realization theorem would identify these with normal-form
carrier sizes. -/
def expectedCompressedCarrierCardinality (fieldCount : ℕ) : ℕ :=
  match fieldCount with
  | 1 => 1610612736
  | 2 => 7851761664
  | 3 => 14998818816
  | 4 => 14174097504
  | 5 => 6867338688
  | 6 => 1587351600
  | 7 => 139096944
  | 8 => 2083902
  | _ => 0

/-! ## Fourteen power-trace classes of the literal hypercubic group -/

abbrev PowerTraceClass := Fin 14

def powerTraceRows : List (List ℤ) :=
  [ [-4, 4, -4, 4, -4, 4, -4, 4, -4, 4, -4, 4, -4, 4, -4, 4]
  , [-2, 0, -2, 4, -2, 0, -2, 4, -2, 0, -2, 4, -2, 0, -2, 4]
  , [-2, 4, -2, 4, -2, 4, -2, 4, -2, 4, -2, 4, -2, 4, -2, 4]
  , [-1, 1, -4, 1, -1, 4, -1, 1, -4, 1, -1, 4, -1, 1, -4, 1]
  , [-1, 1, 2, 1, -1, 4, -1, 1, 2, 1, -1, 4, -1, 1, 2, 1]
  , [0, -4, 0, 4, 0, -4, 0, 4, 0, -4, 0, 4, 0, -4, 0, 4]
  , [0, 0, 0, -4, 0, 0, 0, 4, 0, 0, 0, -4, 0, 0, 0, 4]
  , [0, 0, 0, 4, 0, 0, 0, 4, 0, 0, 0, 4, 0, 0, 0, 4]
  , [0, 4, 0, 4, 0, 4, 0, 4, 0, 4, 0, 4, 0, 4, 0, 4]
  , [1, 1, -2, 1, 1, 4, 1, 1, -2, 1, 1, 4, 1, 1, -2, 1]
  , [1, 1, 4, 1, 1, 4, 1, 1, 4, 1, 1, 4, 1, 1, 4, 1]
  , [2, 0, 2, 4, 2, 0, 2, 4, 2, 0, 2, 4, 2, 0, 2, 4]
  , [2, 4, 2, 4, 2, 4, 2, 4, 2, 4, 2, 4, 2, 4, 2, 4]
  , [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4] ]

def classPowerTraceInt (traceClass : PowerTraceClass)
    (exponent : ℕ) : ℤ :=
  if exponent = 0 then 4 else
    (powerTraceRows.getD traceClass.1 []).getD
      (exponent - 1) 0

def classPowerTrace (traceClass : PowerTraceClass)
    (exponent : ℕ) : ℚ :=
  classPowerTraceInt traceClass exponent

def classOrientationSign (traceClass : PowerTraceClass) : ℚ :=
  match traceClass.1 with
  | 2 | 4 | 7 | 9 | 12 => -1
  | _ => 1

def classMultiplicity (traceClass : PowerTraceClass) : ℕ :=
  match traceClass.1 with
  | 0 => 1
  | 1 => 12
  | 2 => 16
  | 3 => 32
  | 4 => 32
  | 5 => 12
  | 6 => 48
  | 7 => 96
  | 8 => 42
  | 9 => 32
  | 10 => 32
  | 11 => 12
  | 12 => 16
  | 13 => 1
  | _ => 0

/-- Classification from the first four standard-representation power
traces. -/
def powerTraceClassFrom (t1 t2 t3 t4 : ℤ) : PowerTraceClass :=
  if t1 = -4 then 0
  else if t1 = -2 then if t2 = 0 then 1 else 2
  else if t1 = -1 then if t3 = -4 then 3 else 4
  else if t1 = 0 then
    if t2 = -4 then 5
    else if t2 = 0 then if t4 = -4 then 6 else 7
    else 8
  else if t1 = 1 then if t3 = -2 then 9 else 10
  else if t1 = 2 then if t2 = 0 then 11 else 12
  else 13

/-- Classification by the first few standard-representation power traces.
The exhaustive replay below proves that these branches cover the literal
`384` signed permutations and have the advertised full power traces. -/
def powerTraceClassOf (h : Hypercubic4) : PowerTraceClass :=
  powerTraceClassFrom
    (recurrentVectorPowerTrace h 1)
    (recurrentVectorPowerTrace h 2)
    (recurrentVectorPowerTrace h 3)
    (recurrentVectorPowerTrace h 4)

theorem recurrentVectorPowerTrace_semantic (h : Hypercubic4)
    (exponent : ℕ) :
    (recurrentVectorPowerTrace h exponent : ℚ) =
      vectorCharacter (h ^ exponent) :=
  recurrentVectorPowerCharacter_eq h exponent

def allFin16 (predicate : Fin 16 → Bool) : Bool :=
  predicate 0 && predicate 1 && predicate 2 && predicate 3 &&
  predicate 4 && predicate 5 && predicate 6 && predicate 7 &&
  predicate 8 && predicate 9 && predicate 10 && predicate 11 &&
  predicate 12 && predicate 13 && predicate 14 && predicate 15

def decodedPowerTraceReplayCheckAt (permutation : Fin 24) : Bool :=
  allFin16 fun reflectionMask =>
    let h := decodedHypercubicCharacterElement permutation reflectionMask
    allFin16 fun exponentIndex =>
      decide (recurrentVectorPowerTrace h (exponentIndex.1 + 1) =
        classPowerTraceInt (powerTraceClassOf h) (exponentIndex.1 + 1))

def decodedOrientationReplayCheckAt (permutation : Fin 24) : Bool :=
  allFin16 fun reflectionMask =>
    let h := decodedHypercubicCharacterElement permutation reflectionMask
    decide (Hypercubic4.orientationSign h =
      classOrientationSign (powerTraceClassOf h))

def sumFin16Nat (value : Fin 16 → ℕ) : ℕ :=
  value 0 + value 1 + value 2 + value 3 + value 4 + value 5 +
  value 6 + value 7 + value 8 + value 9 + value 10 + value 11 +
  value 12 + value 13 + value 14 + value 15

def sumFin24Nat (value : Fin 24 → ℕ) : ℕ :=
  value 0 + value 1 + value 2 + value 3 + value 4 + value 5 +
  value 6 + value 7 + value 8 + value 9 + value 10 + value 11 +
  value 12 + value 13 + value 14 + value 15 + value 16 + value 17 +
  value 18 + value 19 + value 20 + value 21 + value 22 + value 23

def decodedPowerTraceClassAt (permutation : Fin 24)
    (reflectionMask : Fin 16) : PowerTraceClass :=
  powerTraceClassOf
    (decodedHypercubicCharacterElement permutation reflectionMask)

def decodedClassMultiplicityAt (permutation : Fin 24)
    (traceClass : PowerTraceClass) : ℕ :=
  sumFin16Nat fun reflectionMask =>
    if decodedPowerTraceClassAt permutation reflectionMask = traceClass
    then 1 else 0

def decodedClassMultiplicity (traceClass : PowerTraceClass) : ℕ :=
  sumFin24Nat fun permutation =>
    decodedClassMultiplicityAt permutation traceClass

def expectedPowerTraceClassRows : List (List ℕ) :=
  [ [13, 12, 12, 8, 12, 8, 8, 2, 12, 8, 8, 2, 8, 2, 2, 0]
  , [12, 8, 8, 2, 11, 7, 7, 1, 11, 7, 7, 1, 12, 8, 8, 2]
  , [12, 8, 11, 7, 11, 7, 12, 8, 8, 2, 7, 1, 7, 1, 8, 2]
  , [10, 4, 9, 3, 9, 3, 10, 4, 9, 3, 10, 4, 10, 4, 9, 3]
  , [10, 4, 9, 3, 9, 3, 10, 4, 9, 3, 10, 4, 10, 4, 9, 3]
  , [12, 8, 11, 7, 8, 2, 7, 1, 11, 7, 12, 8, 7, 1, 8, 2]
  , [12, 11, 11, 12, 8, 7, 7, 8, 8, 7, 7, 8, 2, 1, 1, 2]
  , [8, 7, 7, 8, 7, 5, 5, 7, 7, 5, 5, 7, 8, 7, 7, 8]
  , [10, 9, 9, 10, 9, 10, 10, 9, 4, 3, 3, 4, 3, 4, 4, 3]
  , [7, 6, 6, 7, 6, 7, 7, 6, 6, 7, 7, 6, 7, 6, 6, 7]
  , [7, 6, 6, 7, 6, 7, 7, 6, 6, 7, 7, 6, 7, 6, 6, 7]
  , [10, 9, 9, 10, 4, 3, 3, 4, 9, 10, 10, 9, 3, 4, 4, 3]
  , [10, 9, 9, 10, 9, 10, 10, 9, 4, 3, 3, 4, 3, 4, 4, 3]
  , [7, 6, 6, 7, 6, 7, 7, 6, 6, 7, 7, 6, 7, 6, 6, 7]
  , [12, 11, 8, 7, 11, 12, 7, 8, 8, 7, 2, 1, 7, 8, 1, 2]
  , [10, 9, 4, 3, 9, 10, 3, 4, 9, 10, 3, 4, 10, 9, 4, 3]
  , [8, 7, 7, 5, 7, 8, 5, 7, 7, 5, 8, 7, 5, 7, 7, 8]
  , [7, 6, 6, 7, 6, 7, 7, 6, 6, 7, 7, 6, 7, 6, 6, 7]
  , [7, 6, 6, 7, 6, 7, 7, 6, 6, 7, 7, 6, 7, 6, 6, 7]
  , [10, 9, 9, 10, 4, 3, 3, 4, 9, 10, 10, 9, 3, 4, 4, 3]
  , [10, 9, 4, 3, 9, 10, 3, 4, 9, 10, 3, 4, 10, 9, 4, 3]
  , [12, 11, 8, 7, 8, 7, 2, 1, 11, 12, 7, 8, 7, 8, 1, 2]
  , [7, 6, 6, 7, 6, 7, 7, 6, 6, 7, 7, 6, 7, 6, 6, 7]
  , [8, 7, 7, 5, 7, 5, 8, 7, 7, 8, 5, 7, 5, 7, 7, 8] ]

def expectedPowerTraceClassAt (permutation : Fin 24)
    (reflectionMask : Fin 16) : PowerTraceClass :=
  ⟨(expectedPowerTraceClassRows.getD permutation.1 []).getD
      reflectionMask.1 0,
    by fin_cases permutation <;> fin_cases reflectionMask <;> decide⟩

/-! ## Class-compressed character formula -/

def classCycleLetterCharacter (traceClass : PowerTraceClass)
    (cycleLength localDerivativeCount : ℕ) : ℚ :=
  let trace := classPowerTrace traceClass cycleLength
  let twoForm :=
    (trace ^ 2 - classPowerTrace traceClass (2 * cycleLength)) / 2
  twoForm * trace ^ localDerivativeCount

def classPartitionDerivativeCharacter (traceClass : PowerTraceClass) :
    List ℕ → ℕ → ℚ
  | [], remainingDegree => if remainingDegree = 0 then 1 else 0
  | cycleLength :: rest, remainingDegree =>
      ∑ localDerivativeCount ∈
          Finset.range (remainingDegree / cycleLength + 1),
        classCycleLetterCharacter traceClass cycleLength
            localDerivativeCount *
          classPartitionDerivativeCharacter traceClass rest
            (remainingDegree - cycleLength * localDerivativeCount)

def classCompressedSectorCharacter (traceClass : PowerTraceClass)
    (fieldCount : ℕ) : ℚ :=
  ∑ parts ∈ (fieldPartitions fieldCount).toFinset,
    classPartitionDerivativeCharacter traceClass parts
      (derivativeCountForFields fieldCount)

def classCompressedInvariantMultiplicity (parity : ContractionParity)
    (fieldCount : ℕ) : ℚ :=
  (1 / 384) * ∑ traceClass : PowerTraceClass,
    classMultiplicity traceClass *
      (match parity with
      | .scalar => 1
      | .pseudoscalar => classOrientationSign traceClass) *
      classCompressedSectorCharacter traceClass fieldCount

def expectedClassCompressedSectorCharacter
    (traceClass : PowerTraceClass) (fieldCount : ℕ) : ℚ :=
  let row : List ℤ :=
    match traceClass.1 with
    | 0 | 13 => [1610612736, 7851761664, 14998818816, 14174097504,
        6867338688, 1587351600, 139096944, 2083902]
    | 1 | 11 => [32768, 212992, 536576, 658848, 406992, 118288,
        13456, 382]
    | 2 | 12 => [0, 24576, 0, 46176, 0, 21456, 0, 1590]
    | 5 | 8 => [0, 24576, -12288, 52320, -22272, 30384, -9360, 4350]
    | 6 | 7 => [0, 0, 0, 96, 0, -48, 0, 86]
    | _ => [0, 0, 0, 0, 0, 0, 0, 0]
  if fieldCount = 0 then 0 else (row.getD (fieldCount - 1) 0 : ℤ)

/-- Identity-character specialization: every two-form letter has dimension
six and every derivative axis has dimension four. -/
def identityPartitionDerivativeCount : List ℕ → ℕ → ℕ
  | [], remainingDegree => if remainingDegree = 0 then 1 else 0
  | cycleLength :: rest, remainingDegree =>
      ∑ localDerivativeCount ∈
          Finset.range (remainingDegree / cycleLength + 1),
        (6 * 4 ^ localDerivativeCount) *
          identityPartitionDerivativeCount rest
            (remainingDegree - cycleLength * localDerivativeCount)

/-- Identity specialization of the cycle-index expression.  No finite-carrier
cardinality identification is asserted in this module. -/
def compressedCarrierCardinality (fieldCount : ℕ) : ℕ :=
  ∑ parts ∈ (fieldPartitions fieldCount).toFinset,
    identityPartitionDerivativeCount parts
      (derivativeCountForFields fieldCount)

theorem expectedCompressedCarrierCardinality_total :
    (∑ fieldCount ∈ Finset.Icc 1 8,
      expectedCompressedCarrierCardinality fieldCount) =
      47231161854 := by
  decide

theorem expectedCompressedScalarMultiplicity_total :
    (∑ fieldCount ∈ Finset.Icc 1 8,
      expectedCompressedInvariantMultiplicity .scalar fieldCount) =
      246136792 := by
  decide

theorem expectedCompressedPseudoscalarMultiplicity_total :
    (∑ fieldCount ∈ Finset.Icc 1 8,
      expectedCompressedInvariantMultiplicity .pseudoscalar fieldCount) =
      246121092 := by
  decide

end HypercubicDimension16CompressionCensus
end YangMills
end QuantumTheory
end Mettapedia
