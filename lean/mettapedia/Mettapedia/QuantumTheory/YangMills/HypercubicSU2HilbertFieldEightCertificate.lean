import Mettapedia.QuantumTheory.YangMills.HypercubicSU2HilbertCertificate

/-!
# Field-eight certificate for our hypercubic--SU(2) Hilbert realization

Eight field-strength letters already have dimension sixteen, so neither a
positive-degree translation factor nor a derivative commutator can contribute
to this coefficient.  Newton's recurrence computes the `H(4) × SU(2)`
invariant multiplicity in the eighth symmetric power of the
two-form--adjoint letter representation.
-/

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Mettapedia
namespace QuantumTheory
namespace YangMills
namespace HypercubicSU2HilbertFieldEightCertificate

open HypercubicDimension16CompressionCensus
open HypercubicCartanMaxwellHilbertCertificate
open HypercubicSU2HilbertCertificate

/-- Adams-power character of one two-form letter tensored with the adjoint
`SU(2)` color representation. -/
def fieldStrengthPowerSum (maximum : ℕ) (traceClass : PowerTraceClass)
    (power : ℕ) : SparseColorPolynomial :=
  sparseColorAddScaled maximum []
    (sparseAdjointCharacter maximum power)
    (exteriorCharacterInt traceClass power 2)

structure SymmetricPowerReplay where
  values : Array SparseColorPolynomial
  exact : Bool
deriving Repr, DecidableEq

/-- Newton recurrence for complete symmetric powers.  `maximum = 8` gives a
color window `[-16,16]`, exactly the possible adjoint weights of eight
letters. -/
def fieldStrengthSymmetricPowerSeries (traceClass : PowerTraceClass)
    (maximum : ℕ) : SymmetricPowerReplay :=
  (List.range maximum).foldl (fun replay index =>
    let degree := index + 1
    let numerator := (List.range degree).foldl (fun value powerIndex =>
      let power := powerIndex + 1
      sparseColorAddScaled maximum value
        (sparseColorMultiply maximum
          (fieldStrengthPowerSum maximum traceClass power)
          (replay.values.getD (degree - power) [])) 1) []
    let divided := divideSparseColorExact degree numerator
    { values := replay.values.push divided.1
      exact := replay.exact && divided.2 })
    { values := #[[(0, 1)]], exact := true }

def fieldEightClassSinglet (traceClass : PowerTraceClass) : ℤ :=
  sparseSU2SingletMultiplicity
    ((fieldStrengthSymmetricPowerSeries traceClass 8).values.getD 8 [])

def fieldEightClassExactFlags : Array Bool :=
  Array.ofFn fun traceClass : PowerTraceClass =>
    (fieldStrengthSymmetricPowerSeries traceClass 8).exact

def fieldEightHypercubicSingletNumerator : ℤ :=
  ∑ traceClass : PowerTraceClass,
    (classMultiplicity traceClass : ℤ) *
      fieldEightClassSinglet traceClass

def fieldEightHypercubicSingletCount : ℤ :=
  fieldEightHypercubicSingletNumerator / 384

def fieldEightHypercubicAverageExact : Bool :=
  decide (fieldEightHypercubicSingletNumerator % 384 = 0)

theorem fieldEightClassSinglets_replay :
    (Array.ofFn fun traceClass : PowerTraceClass =>
      fieldEightClassSinglet traceClass) =
      #[10521, 9, 105, 0, 0, 217, 9, 9, 217, 0, 0, 9, 105, 10521] := by
  decide

theorem fieldEightClassExactFlags_replay :
    fieldEightClassExactFlags =
      #[true, true, true, true, true, true, true,
        true, true, true, true, true, true, true] := by
  decide

theorem fieldEightHypercubicSingletNumerator_replay :
    fieldEightHypercubicSingletNumerator = 37632 := by
  decide

theorem fieldEightCharacterReplay_exact :
    fieldEightClassExactFlags =
        #[true, true, true, true, true, true, true,
          true, true, true, true, true, true, true] ∧
      fieldEightHypercubicAverageExact = true ∧
      fieldEightHypercubicSingletCount = 98 := by
  refine ⟨fieldEightClassExactFlags_replay, ?_, ?_⟩
  · unfold fieldEightHypercubicAverageExact
    rw [fieldEightHypercubicSingletNumerator_replay]
    decide
  · unfold fieldEightHypercubicSingletCount
    rw [fieldEightHypercubicSingletNumerator_replay]
    decide

#print axioms fieldEightClassSinglets_replay
#print axioms fieldEightClassExactFlags_replay
#print axioms fieldEightHypercubicSingletNumerator_replay
#print axioms fieldEightCharacterReplay_exact

end HypercubicSU2HilbertFieldEightCertificate
end YangMills
end QuantumTheory
end Mettapedia
