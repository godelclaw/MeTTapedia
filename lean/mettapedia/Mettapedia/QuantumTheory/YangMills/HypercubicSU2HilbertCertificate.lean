import Mettapedia.QuantumTheory.YangMills.HypercubicCartanMaxwellHilbertCertificate

/-!
# A finite hypercubic--SU(2) Hilbert evaluator through dimension sixteen

This is our realization of the standard character calculation for gauge-
singlet local polynomials.  It replaces the Cartan-line Weyl average by the
full adjoint `SU(2)` character and its Weyl constant-term functional.  This is
a clearly labeled strengthening of the Cartan specialization: it computes a
finite character-model census, but identifying that census with the separate
syntactic physical quotient requires an additional semantic bridge.

Color Laurent polynomials are stored in a fixed window.  At canonical degree
`maximum`, adjoint weights lie between `-2 * maximum` and `2 * maximum`, so no
coefficient used by the bounded recurrence is truncated.
-/

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 10000000

namespace Mettapedia
namespace QuantumTheory
namespace YangMills
namespace HypercubicSU2HilbertCertificate

open HypercubicDimension16CompressionCensus
open HypercubicCartanMaxwellHilbertCertificate

abbrev ColorPolynomial := Array ℤ

def colorWidth (maximum : ℕ) : ℕ := 4 * maximum + 1

def colorCenter (maximum : ℕ) : ℕ := 2 * maximum

def colorZero (maximum : ℕ) : ColorPolynomial :=
  Array.replicate (colorWidth maximum) 0

def colorOne (maximum : ℕ) : ColorPolynomial :=
  Array.ofFn fun index : Fin (colorWidth maximum) =>
    if index.1 = colorCenter maximum then 1 else 0

def adjointCharacter (maximum power : ℕ) : ColorPolynomial :=
  Array.ofFn fun index : Fin (colorWidth maximum) =>
    if index.1 = colorCenter maximum - 2 * power ∨
        index.1 = colorCenter maximum ∨
        index.1 = colorCenter maximum + 2 * power
    then 1 else 0

def colorAddScaled (maximum : ℕ) (left right : ColorPolynomial)
    (scale : ℤ) : ColorPolynomial :=
  Array.ofFn fun index : Fin (colorWidth maximum) =>
    left.getD index.1 0 + scale * right.getD index.1 0

def colorScale (scale : ℤ) (value : ColorPolynomial) : ColorPolynomial :=
  value.map fun coefficient => scale * coefficient

def colorMultiply (maximum : ℕ)
    (left right : ColorPolynomial) : ColorPolynomial :=
  Array.ofFn fun target : Fin (colorWidth maximum) =>
    (List.range (colorWidth maximum)).foldl (fun coefficient leftIndex =>
      let combined := target.1 + colorCenter maximum
      if leftIndex ≤ combined then
        coefficient + left.getD leftIndex 0 *
          right.getD (combined - leftIndex) 0
      else coefficient) 0

structure ColorSeriesReplay where
  values : Array ColorPolynomial
  exact : Bool
deriving Repr, DecidableEq

/-- External certificates expose every intermediate row, so each recurrence
step can be checked without reducing the full nested computation. -/
structure SU2ClassCertificate where
  particles : Array (Array ℤ)
  logarithm : Array ColorPolynomial
  plethystic : Array ColorPolynomial
  ibp : Array ColorPolynomial
  singlets : Array ℤ
deriving Repr, DecidableEq

def weightedPlethysticLogColorCoefficientIntOfTable
    (particles : Array (Array ℤ)) (maximum degree : ℕ) :
    ColorPolynomial :=
  if degree = 0 then colorZero maximum else
    (List.range (degree + 1)).foldl (fun value power =>
      if power = 0 ∨ degree % power ≠ 0 then value else
        let sourceDegree := degree / power
        colorAddScaled maximum value (adjointCharacter maximum power)
          ((sourceDegree : ℤ) *
            (particles.getD power #[]).getD sourceDegree 0))
      (colorZero maximum)

def weightedPlethysticLogColorSeriesInt
    (policy : MaxwellRelationPolicy) (traceClass : PowerTraceClass)
    (maximum : ℕ) : Array ColorPolynomial :=
  let particles := singleParticleTableInt policy traceClass maximum
  (List.range (maximum + 1)).foldl (fun values degree =>
    values.push
      (weightedPlethysticLogColorCoefficientIntOfTable
        particles maximum degree)) #[]

def divideColorExact (degree : ℕ) (value : ColorPolynomial) :
    ColorPolynomial × Bool :=
  (value.map fun coefficient => coefficient / degree,
    value.all fun coefficient => decide (coefficient % degree = 0))

def plethysticColorSeriesInt
    (policy : MaxwellRelationPolicy) (traceClass : PowerTraceClass)
    (maximum : ℕ) : ColorSeriesReplay :=
  let logarithm :=
    weightedPlethysticLogColorSeriesInt policy traceClass maximum
  let initialExact :=
    (List.range (maximum + 1)).all fun power =>
      exteriorCharacterDivisionExact traceClass power
  (List.range maximum).foldl (fun replay index =>
    let degree := index + 1
    let numerator := (List.range degree).foldl (fun value sourceIndex =>
      let sourceDegree := sourceIndex + 1
      colorAddScaled maximum value
        (colorMultiply maximum
          (logarithm.getD sourceDegree (colorZero maximum))
          (replay.values.getD (degree - sourceDegree)
            (colorZero maximum))) 1) (colorZero maximum)
    let divided := divideColorExact degree numerator
    { values := replay.values.push divided.1
      exact := replay.exact && divided.2 })
    { values := #[colorOne maximum], exact := initialExact }

def ibpColorSeriesInt
    (policy : MaxwellRelationPolicy) (traceClass : PowerTraceClass)
    (maximum : ℕ) : ColorSeriesReplay :=
  let replay := plethysticColorSeriesInt policy traceClass maximum
  { values := (List.range (maximum + 1)).foldl (fun values degree =>
      let coefficient := (List.range (min 4 degree + 1)).foldl
        (fun value shift =>
          colorAddScaled maximum value
            (replay.values.getD (degree - shift) (colorZero maximum))
            (determinantCoefficientInt traceClass 1 shift))
        (colorZero maximum)
      values.push coefficient) #[]
    exact := replay.exact }

/-- Weyl's constant-term formula for the multiplicity of the trivial
`SU(2)` representation in a symmetric Laurent character. -/
def su2SingletMultiplicity (maximum : ℕ)
    (value : ColorPolynomial) : ℤ :=
  value.getD (colorCenter maximum) 0 -
    value.getD (colorCenter maximum + 2) 0

def su2ClassSeriesInt
    (policy : MaxwellRelationPolicy) (traceClass : PowerTraceClass)
    (maximum : ℕ) : IntegerSeriesReplay :=
  let replay := ibpColorSeriesInt policy traceClass maximum
  { values := replay.values.map (su2SingletMultiplicity maximum)
    exact := replay.exact }

def su2HypercubicHilbertSeriesInt
    (policy : MaxwellRelationPolicy) (maximum : ℕ) : IntegerSeriesReplay :=
  let classRows : Array IntegerSeriesReplay :=
    Array.ofFn fun traceClass : PowerTraceClass =>
      su2ClassSeriesInt policy traceClass maximum
  let initialExact := classRows.all fun replay => replay.exact
  (List.range (maximum + 1)).foldl (fun replay degree =>
    let numerator := ∑ traceClass : PowerTraceClass,
      (classMultiplicity traceClass : ℤ) *
        (classRows.getD traceClass.1
          { values := #[], exact := false }).values.getD degree 0
    { values := replay.values.push (numerator / 384)
      exact := replay.exact && decide (numerator % 384 = 0) })
    { values := #[], exact := initialExact }

/-! ## Bounded certificate replay -/

def certificateParticlesValid
    (policy : MaxwellRelationPolicy) (traceClass : PowerTraceClass)
    (maximum : ℕ) (certificate : SU2ClassCertificate) : Bool :=
  decide (certificate.particles =
    singleParticleTableInt policy traceClass maximum) &&
  (List.range (maximum + 1)).all fun power =>
    exteriorCharacterDivisionExact traceClass power

def certificateLogarithmValidAt (maximum degree : ℕ)
    (certificate : SU2ClassCertificate) : Bool :=
  decide (certificate.logarithm.getD degree #[] =
    weightedPlethysticLogColorCoefficientIntOfTable
      certificate.particles maximum degree)

def certificatePlethysticValidAt (maximum degree : ℕ)
    (certificate : SU2ClassCertificate) : Bool :=
  if degree = 0 then
    decide (certificate.plethystic.getD 0 #[] = colorOne maximum)
  else
    let numerator := (List.range degree).foldl (fun value sourceIndex =>
      let sourceDegree := sourceIndex + 1
      colorAddScaled maximum value
        (colorMultiply maximum
          (certificate.logarithm.getD sourceDegree (colorZero maximum))
          (certificate.plethystic.getD (degree - sourceDegree)
            (colorZero maximum))) 1) (colorZero maximum)
    let divided := divideColorExact degree numerator
    divided.2 && decide
      (certificate.plethystic.getD degree #[] = divided.1)

def certificateIBPValidAt (traceClass : PowerTraceClass)
    (maximum degree : ℕ) (certificate : SU2ClassCertificate) : Bool :=
  let coefficient := (List.range (min 4 degree + 1)).foldl
    (fun value shift =>
      colorAddScaled maximum value
        (certificate.plethystic.getD (degree - shift) (colorZero maximum))
        (determinantCoefficientInt traceClass 1 shift))
    (colorZero maximum)
  decide (certificate.ibp.getD degree #[] = coefficient)

def certificateSingletValidAt (maximum degree : ℕ)
    (certificate : SU2ClassCertificate) : Bool :=
  decide (certificate.singlets.getD degree 0 =
    su2SingletMultiplicity maximum
      (certificate.ibp.getD degree (colorZero maximum)))

def certificateDegreeValidAt (traceClass : PowerTraceClass)
    (maximum degree : ℕ) (certificate : SU2ClassCertificate) : Bool :=
  certificateLogarithmValidAt maximum degree certificate &&
  certificatePlethysticValidAt maximum degree certificate &&
  certificateIBPValidAt traceClass maximum degree certificate &&
  certificateSingletValidAt maximum degree certificate

/-! ## Sparse certificate format

The executable census above uses dense fixed-window arrays.  Certificate
payloads omit zero coefficients and replay every operation through a
canonical increasing-exponent normalization. -/

abbrev SparseColorPolynomial := List (ℤ × ℤ)

structure SparseSU2ClassCertificate where
  particles : Array (Array ℤ)
  logarithm : Array SparseColorPolynomial
  plethystic : Array SparseColorPolynomial
  ibp : Array SparseColorPolynomial
  singlets : Array ℤ
deriving Repr, DecidableEq

def sparseColorCoefficient (value : SparseColorPolynomial)
    (exponent : ℤ) : ℤ :=
  value.foldl (fun result entry =>
    if entry.1 = exponent then result + entry.2 else result) 0

def boundedColorExponent (maximum index : ℕ) : ℤ :=
  (index : ℤ) - colorCenter maximum

def sparseColorNormalize (maximum : ℕ)
    (coefficient : ℤ → ℤ) : SparseColorPolynomial :=
  (List.range (colorWidth maximum)).filterMap fun index =>
    let exponent := boundedColorExponent maximum index
    let value := coefficient exponent
    if value = 0 then none else some (exponent, value)

def sparseColorAddScaled (maximum : ℕ)
    (left right : SparseColorPolynomial) (scale : ℤ) :
    SparseColorPolynomial :=
  sparseColorNormalize maximum fun exponent =>
    sparseColorCoefficient left exponent +
      scale * sparseColorCoefficient right exponent

def sparseColorMultiply (maximum : ℕ)
    (left right : SparseColorPolynomial) : SparseColorPolynomial :=
  sparseColorNormalize maximum fun exponent =>
    left.foldl (fun coefficient entry =>
      coefficient + entry.2 *
        sparseColorCoefficient right (exponent - entry.1)) 0

def sparseAdjointCharacter (maximum power : ℕ) :
    SparseColorPolynomial :=
  sparseColorNormalize maximum fun exponent =>
    if exponent = -(2 * (power : ℤ)) ∨ exponent = 0 ∨
        exponent = 2 * (power : ℤ)
    then 1 else 0

def sparseWeightedLogCoefficientIntOfTable
    (particles : Array (Array ℤ)) (maximum degree : ℕ) :
    SparseColorPolynomial :=
  if degree = 0 then [] else
    (List.range (degree + 1)).foldl (fun value power =>
      if power = 0 ∨ degree % power ≠ 0 then value else
        let sourceDegree := degree / power
        sparseColorAddScaled maximum value
          (sparseAdjointCharacter maximum power)
          ((sourceDegree : ℤ) *
            (particles.getD power #[]).getD sourceDegree 0)) []

def divideSparseColorExact (degree : ℕ)
    (value : SparseColorPolynomial) : SparseColorPolynomial × Bool :=
  (value.map fun entry => (entry.1, entry.2 / degree),
    value.all fun entry => decide (entry.2 % degree = 0))

def sparseCertificateParticlesValid
    (policy : MaxwellRelationPolicy) (traceClass : PowerTraceClass)
    (maximum : ℕ) (certificate : SparseSU2ClassCertificate) : Bool :=
  decide (certificate.particles =
    singleParticleTableInt policy traceClass maximum) &&
  (List.range (maximum + 1)).all fun power =>
    exteriorCharacterDivisionExact traceClass power

def sparseCertificateLogarithmValidAt (maximum degree : ℕ)
    (certificate : SparseSU2ClassCertificate) : Bool :=
  decide (certificate.logarithm.getD degree [] =
    sparseWeightedLogCoefficientIntOfTable
      certificate.particles maximum degree)

def sparseCertificatePlethysticValidAt (maximum degree : ℕ)
    (certificate : SparseSU2ClassCertificate) : Bool :=
  if degree = 0 then
    decide (certificate.plethystic.getD 0 [] = [(0, 1)])
  else
    let numerator := (List.range degree).foldl (fun value sourceIndex =>
      let sourceDegree := sourceIndex + 1
      sparseColorAddScaled maximum value
        (sparseColorMultiply maximum
          (certificate.logarithm.getD sourceDegree [])
          (certificate.plethystic.getD (degree - sourceDegree) [])) 1) []
    let divided := divideSparseColorExact degree numerator
    divided.2 && decide
      (certificate.plethystic.getD degree [] = divided.1)

def sparseCertificateIBPValidAt (traceClass : PowerTraceClass)
    (maximum degree : ℕ) (certificate : SparseSU2ClassCertificate) : Bool :=
  let coefficient := (List.range (min 4 degree + 1)).foldl
    (fun value shift =>
      sparseColorAddScaled maximum value
        (certificate.plethystic.getD (degree - shift) [])
        (determinantCoefficientInt traceClass 1 shift)) []
  decide (certificate.ibp.getD degree [] = coefficient)

def sparseSU2SingletMultiplicity
    (value : SparseColorPolynomial) : ℤ :=
  sparseColorCoefficient value 0 - sparseColorCoefficient value 2

def sparseCertificateSingletValidAt (degree : ℕ)
    (certificate : SparseSU2ClassCertificate) : Bool :=
  decide (certificate.singlets.getD degree 0 =
    sparseSU2SingletMultiplicity (certificate.ibp.getD degree []))

def sparseCertificateDegreeValidAt (traceClass : PowerTraceClass)
    (maximum degree : ℕ) (certificate : SparseSU2ClassCertificate) : Bool :=
  sparseCertificateLogarithmValidAt maximum degree certificate &&
  sparseCertificatePlethysticValidAt maximum degree certificate &&
  sparseCertificateIBPValidAt traceClass maximum degree certificate &&
  sparseCertificateSingletValidAt degree certificate

end HypercubicSU2HilbertCertificate
end YangMills
end QuantumTheory
end Mettapedia
