import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16CompressionCensus

/-!
# Hypercubic Cartan--Maxwell Hilbert certificate through dimension sixteen

This file evaluates the finite-group version of the standard operator-basis
Hilbert series for one four-dimensional field strength.  The single-particle
module is the closed two-form jet module off shell and the Maxwell jet module
on shell.  The determinant factor is the translation Koszul factor for
integration by parts.  A simultaneous sign average is the Weyl action on the
`SU(2)` Cartan line.

The computation uses the fourteen power-trace classes of the literal signed
hypercubic group.  It is a bounded character calculation: no raw monomial
matrix is constructed.  The generic-field semantic recurrence and the
exact-division integer evaluator are kept separate.
-/

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 10000000

noncomputable section

open scoped BigOperators

namespace Mettapedia
namespace QuantumTheory
namespace YangMills
namespace HypercubicCartanMaxwellHilbertCertificate

open HypercubicDimension16CompressionCensus

inductive MaxwellRelationPolicy where
  | derivativeFree
  | offShell
  | onShell
deriving DecidableEq, Repr

/-! ## Periodic power traces of the fourteen hypercubic classes -/

def periodicPowerTraceRow (traceClass : PowerTraceClass) : List ℤ :=
  match traceClass.1 with
  | 0 => [-4, 4]
  | 1 => [-2, 0, -2, 4]
  | 2 => [-2, 4]
  | 3 => [-1, 1, -4, 1, -1, 4]
  | 4 => [-1, 1, 2, 1, -1, 4]
  | 5 => [0, -4, 0, 4]
  | 6 => [0, 0, 0, -4, 0, 0, 0, 4]
  | 7 => [0, 0, 0, 4]
  | 8 => [0, 4]
  | 9 => [1, 1, -2, 1, 1, 4]
  | 10 => [1, 1, 4]
  | 11 => [2, 0, 2, 4]
  | 12 => [2, 4]
  | 13 => [4]
  | _ => []

def periodicPowerTraceInt (traceClass : PowerTraceClass)
    (exponent : ℕ) : ℤ :=
  if exponent = 0 then 4
  else
    let row := periodicPowerTraceRow traceClass
    row.getD ((exponent - 1) % row.length) 0

def classOrientationInt (traceClass : PowerTraceClass) : ℤ :=
  match traceClass.1 with
  | 2 | 4 | 7 | 9 | 12 => -1
  | _ => 1

theorem periodicPowerTraceInt_agrees_through_sixteen
    (traceClass : PowerTraceClass) (exponent : Fin 16) :
    periodicPowerTraceInt traceClass (exponent.1 + 1) =
      classPowerTraceInt traceClass (exponent.1 + 1) := by
  fin_cases traceClass <;> fin_cases exponent <;> decide

theorem classOrientationInt_agrees (traceClass : PowerTraceClass) :
    (classOrientationInt traceClass : ℚ) =
      classOrientationSign traceClass := by
  fin_cases traceClass <;> norm_num [classOrientationInt,
    classOrientationSign]

/-! ## Exterior characters and the two single-particle resolutions -/

def exteriorCharacter {K : Type*} [Field K]
    (traceClass : PowerTraceClass) (power degree : ℕ) : K :=
  let p1 : K := periodicPowerTraceInt traceClass power
  let p2 : K := periodicPowerTraceInt traceClass (2 * power)
  let p3 : K := periodicPowerTraceInt traceClass (3 * power)
  match degree with
  | 0 => 1
  | 1 => p1
  | 2 => (p1 ^ 2 - p2) / 2
  | 3 => (p1 ^ 3 - 3 * p1 * p2 + 2 * p3) / 6
  | 4 => (classOrientationInt traceClass ^ power : ℤ)
  | _ => 0

def determinantCoefficient {K : Type*} [Field K]
    (traceClass : PowerTraceClass) (power degree : ℕ) : K :=
  (-1 : K) ^ degree * exteriorCharacter traceClass power degree

def inverseDeterminantSeries {K : Type*} [Field K]
    (traceClass : PowerTraceClass) (power maximum : ℕ) : Array K :=
  (List.range maximum).foldl (fun values index =>
    let degree := index + 1
    let correction :=
      ∑ shift ∈ Finset.Icc 1 (min 4 degree),
        determinantCoefficient traceClass power shift *
          values.getD (degree - shift) 0
    values.push (-correction)) #[1]

def singleParticleNumeratorCoefficient {K : Type*} [Field K]
    (policy : MaxwellRelationPolicy) (traceClass : PowerTraceClass)
    (power degree : ℕ) : K :=
  match policy, degree with
  | .derivativeFree, 2 => exteriorCharacter traceClass power 2
  | .offShell, 2 => exteriorCharacter traceClass power 2
  | .offShell, 3 => -exteriorCharacter traceClass power 3
  | .offShell, 4 => exteriorCharacter traceClass power 4
  | .onShell, 2 => exteriorCharacter traceClass power 2
  | .onShell, 3 =>
      -(exteriorCharacter traceClass power 1 +
        exteriorCharacter traceClass power 3)
  | .onShell, 4 =>
      exteriorCharacter traceClass power 0 +
        exteriorCharacter traceClass power 4
  | _, _ => 0

def singleParticleSeries {K : Type*} [Field K]
    (policy : MaxwellRelationPolicy) (traceClass : PowerTraceClass)
    (power maximum : ℕ) : Array K :=
  let inverse := inverseDeterminantSeries traceClass power maximum
  (List.range (maximum + 1)).foldl (fun values degree =>
    let coefficient :=
      ∑ shift ∈ Finset.Icc 2 (min 4 degree),
        singleParticleNumeratorCoefficient policy traceClass power shift *
          inverse.getD (degree - shift) 0
    values.push coefficient) #[]

/-! ## Plethystic, Weyl, translation, and hypercubic averages -/

def plethysticLogSeries {K : Type*} [Field K]
    (policy : MaxwellRelationPolicy) (traceClass : PowerTraceClass)
    (fieldSign : K) (maximum : ℕ) : Array K :=
  (List.range (maximum + 1)).foldl (fun values degree =>
    let coefficient :=
      if degree = 0 then 0 else
        ∑ power ∈ Finset.Icc 1 degree,
          if degree % power = 0 then
            fieldSign ^ power / power *
              (singleParticleSeries policy traceClass power
                (degree / power)).getD (degree / power) 0
          else 0
    values.push coefficient) #[]

def plethysticSeries {K : Type*} [Field K]
    (policy : MaxwellRelationPolicy) (traceClass : PowerTraceClass)
    (fieldSign : K) (maximum : ℕ) : Array K :=
  let logarithm := plethysticLogSeries policy traceClass fieldSign maximum
  (List.range maximum).foldl (fun values index =>
    let degree := index + 1
    let coefficient :=
      (∑ sourceDegree ∈ Finset.Icc 1 degree,
        sourceDegree * logarithm.getD sourceDegree 0 *
          values.getD (degree - sourceDegree) 0) / degree
    values.push coefficient) #[1]

def ibpSeries {K : Type*} [Field K]
    (policy : MaxwellRelationPolicy) (traceClass : PowerTraceClass)
    (fieldSign : K) (maximum : ℕ) : Array K :=
  let series := plethysticSeries policy traceClass fieldSign maximum
  (List.range (maximum + 1)).foldl (fun values degree =>
    let coefficient :=
      ∑ shift ∈ Finset.Icc 0 (min 4 degree),
        determinantCoefficient traceClass 1 shift *
          series.getD (degree - shift) 0
    values.push coefficient) #[]

def cartanClassSeries {K : Type*} [Field K]
    (policy : MaxwellRelationPolicy) (traceClass : PowerTraceClass)
    (maximum : ℕ) : Array K :=
  let positive := ibpSeries policy traceClass 1 maximum
  let negative := ibpSeries policy traceClass (-1) maximum
  (List.range (maximum + 1)).foldl (fun values degree =>
    values.push ((positive.getD degree 0 + negative.getD degree 0) / 2)) #[]

def cartanHilbertSeries {K : Type*} [Field K]
    (policy : MaxwellRelationPolicy) (maximum : ℕ) : Array K :=
  let classRows : Array (Array K) :=
    Array.ofFn fun traceClass : PowerTraceClass =>
      cartanClassSeries policy traceClass maximum
  (List.range (maximum + 1)).foldl (fun values degree =>
    let coefficient :=
      (∑ traceClass : PowerTraceClass,
        (classMultiplicity traceClass : K) *
          (classRows.getD traceClass.1 #[]).getD degree 0) / 384
    values.push coefficient) #[]

def ibpCoefficient {K : Type*} [Field K]
    (policy : MaxwellRelationPolicy) (traceClass : PowerTraceClass)
    (fieldSign : K) (degree : ℕ) : K :=
  (ibpSeries policy traceClass fieldSign degree).getD degree 0

def cartanClassCoefficient {K : Type*} [Field K]
    (policy : MaxwellRelationPolicy) (traceClass : PowerTraceClass)
    (degree : ℕ) : K :=
  (cartanClassSeries policy traceClass degree).getD degree 0

def cartanHilbertCoefficient {K : Type*} [Field K]
    (policy : MaxwellRelationPolicy) (degree : ℕ) : K :=
  (cartanHilbertSeries policy degree).getD degree 0

def cartanHilbertDimensionThrough {K : Type*} [Field K]
    (policy : MaxwellRelationPolicy) (maximum : ℕ) : K :=
  (cartanHilbertSeries policy maximum).foldl (· + ·) 0

/-! ## Exact-division integer evaluator

The Hilbert coefficients are integral, although Newton's identities, the
plethystic recurrence, the Weyl average, and the hypercubic average contain
division.  This evaluator carries a Boolean ledger asserting that every such
integer division is exact.  It avoids building large normalized rational
expressions and records the divisibility obligations needed for a rational
interpretation.
-/

structure IntegerSeriesReplay where
  values : Array ℤ
  exact : Bool
deriving Repr, DecidableEq

def exteriorCharacterInt (traceClass : PowerTraceClass)
    (power degree : ℕ) : ℤ :=
  let p1 := periodicPowerTraceInt traceClass power
  let p2 := periodicPowerTraceInt traceClass (2 * power)
  let p3 := periodicPowerTraceInt traceClass (3 * power)
  match degree with
  | 0 => 1
  | 1 => p1
  | 2 => (p1 ^ 2 - p2) / 2
  | 3 => (p1 ^ 3 - 3 * p1 * p2 + 2 * p3) / 6
  | 4 => classOrientationInt traceClass ^ power
  | _ => 0

def exteriorCharacterDivisionExact (traceClass : PowerTraceClass)
    (power : ℕ) : Bool :=
  let p1 := periodicPowerTraceInt traceClass power
  let p2 := periodicPowerTraceInt traceClass (2 * power)
  let p3 := periodicPowerTraceInt traceClass (3 * power)
  decide ((p1 ^ 2 - p2) % 2 = 0) &&
    decide ((p1 ^ 3 - 3 * p1 * p2 + 2 * p3) % 6 = 0)

def determinantCoefficientInt (traceClass : PowerTraceClass)
    (power degree : ℕ) : ℤ :=
  (-1 : ℤ) ^ degree * exteriorCharacterInt traceClass power degree

def inverseDeterminantSeriesInt (traceClass : PowerTraceClass)
    (power maximum : ℕ) : Array ℤ :=
  (List.range maximum).foldl (fun values index =>
    let degree := index + 1
    let correction :=
      ∑ shift ∈ Finset.Icc 1 (min 4 degree),
        determinantCoefficientInt traceClass power shift *
          values.getD (degree - shift) 0
    values.push (-correction)) #[1]

def singleParticleNumeratorCoefficientInt
    (policy : MaxwellRelationPolicy) (traceClass : PowerTraceClass)
    (power degree : ℕ) : ℤ :=
  match policy, degree with
  | .derivativeFree, 2 => exteriorCharacterInt traceClass power 2
  | .offShell, 2 => exteriorCharacterInt traceClass power 2
  | .offShell, 3 => -exteriorCharacterInt traceClass power 3
  | .offShell, 4 => exteriorCharacterInt traceClass power 4
  | .onShell, 2 => exteriorCharacterInt traceClass power 2
  | .onShell, 3 =>
      -(exteriorCharacterInt traceClass power 1 +
        exteriorCharacterInt traceClass power 3)
  | .onShell, 4 =>
      exteriorCharacterInt traceClass power 0 +
        exteriorCharacterInt traceClass power 4
  | _, _ => 0

def singleParticleSeriesInt (policy : MaxwellRelationPolicy)
    (traceClass : PowerTraceClass) (power maximum : ℕ) : Array ℤ :=
  let inverse := inverseDeterminantSeriesInt traceClass power maximum
  (List.range (maximum + 1)).foldl (fun values degree =>
    let coefficient :=
      ∑ shift ∈ Finset.Icc 2 (min 4 degree),
        singleParticleNumeratorCoefficientInt policy traceClass power shift *
          inverse.getD (degree - shift) 0
    values.push coefficient) #[]

def singleParticleTableInt (policy : MaxwellRelationPolicy)
    (traceClass : PowerTraceClass) (maximum : ℕ) : Array (Array ℤ) :=
  (List.range (maximum + 1)).foldl (fun rows power =>
    rows.push (if power = 0 then #[] else
      singleParticleSeriesInt policy traceClass power (maximum / power))) #[]

/-- The coefficient `degree * [t^degree] log PE`; it is integral before the
plethystic recurrence divides by `degree`. -/
def weightedPlethysticLogSeriesIntOfTable
    (particles : Array (Array ℤ)) (fieldSign : ℤ)
    (maximum : ℕ) : Array ℤ :=
  (List.range (maximum + 1)).foldl (fun values degree =>
    let coefficient :=
      if degree = 0 then 0 else
        ∑ power ∈ Finset.Icc 1 degree,
          if degree % power = 0 then
            (degree / power : ℕ) * fieldSign ^ power *
              (particles.getD power #[]).getD (degree / power) 0
          else 0
    values.push coefficient) #[]

def plethysticSeriesIntOfTable (traceClass : PowerTraceClass)
    (particles : Array (Array ℤ)) (fieldSign : ℤ)
    (maximum : ℕ) : IntegerSeriesReplay :=
  let logarithm :=
    weightedPlethysticLogSeriesIntOfTable particles fieldSign maximum
  let initialExact :=
    (List.range (maximum + 1)).all fun power =>
      exteriorCharacterDivisionExact traceClass power
  (List.range maximum).foldl (fun replay index =>
    let degree := index + 1
    let numerator :=
      ∑ sourceDegree ∈ Finset.Icc 1 degree,
        logarithm.getD sourceDegree 0 *
          replay.values.getD (degree - sourceDegree) 0
    { values := replay.values.push (numerator / degree)
      exact := replay.exact && decide (numerator % degree = 0) })
    { values := #[1], exact := initialExact }

def ibpSeriesIntOfTable (traceClass : PowerTraceClass)
    (particles : Array (Array ℤ)) (fieldSign : ℤ)
    (maximum : ℕ) : IntegerSeriesReplay :=
  let replay :=
    plethysticSeriesIntOfTable traceClass particles fieldSign maximum
  { values := (List.range (maximum + 1)).foldl (fun values degree =>
      let coefficient :=
        ∑ shift ∈ Finset.Icc 0 (min 4 degree),
          determinantCoefficientInt traceClass 1 shift *
            replay.values.getD (degree - shift) 0
      values.push coefficient) #[]
    exact := replay.exact }

def cartanClassSeriesInt (policy : MaxwellRelationPolicy)
    (traceClass : PowerTraceClass) (maximum : ℕ) : IntegerSeriesReplay :=
  let particles := singleParticleTableInt policy traceClass maximum
  let positive := ibpSeriesIntOfTable traceClass particles 1 maximum
  let negative := ibpSeriesIntOfTable traceClass particles (-1) maximum
  (List.range (maximum + 1)).foldl (fun replay degree =>
    let numerator :=
      positive.values.getD degree 0 + negative.values.getD degree 0
    { values := replay.values.push (numerator / 2)
      exact := replay.exact && decide (numerator % 2 = 0) })
    { values := #[], exact := positive.exact && negative.exact }

def cartanHilbertSeriesInt (policy : MaxwellRelationPolicy)
    (maximum : ℕ) : IntegerSeriesReplay :=
  let classRows : Array IntegerSeriesReplay :=
    Array.ofFn fun traceClass : PowerTraceClass =>
      cartanClassSeriesInt policy traceClass maximum
  let initialExact := classRows.all (fun replay => replay.exact)
  (List.range (maximum + 1)).foldl (fun replay degree =>
    let numerator :=
      ∑ traceClass : PowerTraceClass,
        (classMultiplicity traceClass : ℤ) *
          (classRows.getD traceClass.1 { values := #[], exact := false }).values.getD
            degree 0
    { values := replay.values.push (numerator / 384)
      exact := replay.exact && decide (numerator % 384 = 0) })
    { values := #[], exact := initialExact }

end HypercubicCartanMaxwellHilbertCertificate
end YangMills
end QuantumTheory
end Mettapedia
