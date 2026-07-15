import Mettapedia.QuantumTheory.YangMills.SU2CanonicalTruncationObstruction

/-!
# An intrinsic `SU(2)` Cayley--Hamilton obstruction to hard truncation

This module replaces the boundary-extension pilot as the decisive
quotient-extraction test.  It uses one actual plaquette and the exact
two-by-two determinant-one trace identity

`trace (U²) = trace(U)² - 2`.

Let `a(U) = 2 - trace(U)` be the centered fundamental trace word and let
`b(U) = 2 - trace(U²)` be the centered twice-wound trace word.  Both are
gauge-invariant Wilson expressions whose small-plaquette expansion starts
with two field-strength factors, hence canonical dimension four.  The exact
identity becomes `b = 4a - a²`.  Multiplication by `a³` yields

`b*a³ - 4*a⁴ + a⁵ = 0`,

with canonical dimensions `16`, `16`, and `20`.  Hard truncation through
dimension sixteen deletes only the last term.  An explicit `SU(2)` plaquette
with holonomy `diag(i,-i)` makes the truncated expression equal to `-32`.

Thus the obstruction is an intrinsic exact Wilson trace relation explicitly
belonging to the off-shell relation policy; it does not use equations of
motion, a boundary-shift convention, or a free polynomial evaluation.
-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators Matrix.Norms.Elementwise

namespace Mettapedia
namespace QuantumTheory
namespace YangMills
namespace SU2CayleyHamiltonTruncationObstruction

open SU2WilsonBlockPilot
open SU2CanonicalTruncationObstruction

/-! ## Exact determinant-one trace relation -/

/-- The two-by-two Cayley--Hamilton trace consequence, proved directly from
matrix multiplication and the determinant formula. -/
theorem trace_square_eq_trace_sq_sub_two_det
    (M : Matrix (Fin 2) (Fin 2) ℂ) :
    Matrix.trace (M * M) = (Matrix.trace M) ^ 2 - 2 * Matrix.det M := by
  simp [Matrix.trace, Matrix.mul_apply, Matrix.det_fin_two,
    Fin.sum_univ_two]
  ring

/-- Centered fundamental plaquette trace word. -/
def centeredTrace (U : SU2) : ℂ :=
  2 - Matrix.trace U.1

/-- Centered twice-wound plaquette trace word. -/
def centeredDoubleTrace (U : SU2) : ℂ :=
  2 - Matrix.trace (U.1 * U.1)

/-- Exact `SU(2)` Cayley--Hamilton relation in centered trace coordinates. -/
theorem centeredDoubleTrace_eq (U : SU2) :
    centeredDoubleTrace U = 4 * centeredTrace U - centeredTrace U ^ 2 := by
  have hdet := U.2.2
  change Matrix.det U.1 = 1 at hdet
  unfold centeredDoubleTrace centeredTrace
  rw [trace_square_eq_trace_sq_sub_two_det, hdet]
  ring

theorem centeredTrace_conjugation (g U : SU2) :
    centeredTrace (g * U * g⁻¹) = centeredTrace U := by
  unfold centeredTrace
  congr 1
  change Matrix.trace ((g.1 * U.1) * (g⁻¹).1) = Matrix.trace U.1
  rw [Matrix.trace_mul_cycle]
  change Matrix.trace ((g⁻¹ * g : SU2).1 * U.1) = Matrix.trace U.1
  rw [inv_mul_cancel]
  simp

theorem centeredDoubleTrace_conjugation (g U : SU2) :
    centeredDoubleTrace (g * U * g⁻¹) = centeredDoubleTrace U := by
  rw [centeredDoubleTrace_eq, centeredDoubleTrace_eq,
    centeredTrace_conjugation]

/-! ## Actual plaquette observables and construction-derived dimensions -/

/-- Fundamental centered trace evaluated on one actual block plaquette. -/
def plaquetteCenteredTrace
    (U : BlockLinkField) (p : BlockPlaquette) : ℂ :=
  centeredTrace (plaquetteHolonomy U p)

/-- Twice-wound centered trace evaluated on the same actual block plaquette. -/
def plaquetteCenteredDoubleTrace
    (U : BlockLinkField) (p : BlockPlaquette) : ℂ :=
  centeredDoubleTrace (plaquetteHolonomy U p)

theorem plaquetteCenteredTrace_gaugeAct
    (g : BlockGaugeTransform) (U : BlockLinkField) (p : BlockPlaquette) :
    plaquetteCenteredTrace (gaugeAct g U) p = plaquetteCenteredTrace U p := by
  unfold plaquetteCenteredTrace
  rw [plaquetteHolonomy_gaugeAct]
  exact centeredTrace_conjugation _ _

theorem plaquetteCenteredDoubleTrace_gaugeAct
    (g : BlockGaugeTransform) (U : BlockLinkField) (p : BlockPlaquette) :
    plaquetteCenteredDoubleTrace (gaugeAct g U) p =
      plaquetteCenteredDoubleTrace U p := by
  unfold plaquetteCenteredDoubleTrace
  rw [plaquetteHolonomy_gaugeAct]
  exact centeredDoubleTrace_conjugation _ _

/-- The three monomials in the cross-cutoff Cayley--Hamilton relation:
`a³b`, `a⁴`, and `a⁵`, respectively. -/
abbrev TraceRelationMonomial := Fin 3

/-- Powers of the fundamental and twice-wound trace coordinates. -/
def traceRelationPowers : TraceRelationMonomial → ℕ × ℕ
  | 0 => (3, 1)
  | 1 => (4, 0)
  | 2 => (5, 0)

/-- Each centered trace primitive begins with two field-strength factors and
therefore has canonical dimension `2 * 2 = 4`.  Monomial dimension is derived
additively from its powers; it is not a caller-supplied label. -/
def traceRelationCanonicalDimension (m : TraceRelationMonomial) : ℕ :=
  4 * (traceRelationPowers m).1 + 4 * (traceRelationPowers m).2

theorem traceRelationCanonicalDimensions :
    traceRelationCanonicalDimension 0 = 16 ∧
    traceRelationCanonicalDimension 1 = 16 ∧
    traceRelationCanonicalDimension 2 = 20 := by
  decide

/-- Evaluation of a catalog monomial as an actual plaquette trace-word
observable. -/
def evaluateTraceRelationMonomial
    (m : TraceRelationMonomial) (U : BlockLinkField)
    (p : BlockPlaquette) : ℂ :=
  plaquetteCenteredTrace U p ^ (traceRelationPowers m).1 *
    plaquetteCenteredDoubleTrace U p ^ (traceRelationPowers m).2

theorem evaluateTraceRelationMonomial_gaugeAct
    (m : TraceRelationMonomial) (g : BlockGaugeTransform)
    (U : BlockLinkField) (p : BlockPlaquette) :
    evaluateTraceRelationMonomial m (gaugeAct g U) p =
      evaluateTraceRelationMonomial m U p := by
  simp [evaluateTraceRelationMonomial,
    plaquetteCenteredTrace_gaugeAct,
    plaquetteCenteredDoubleTrace_gaugeAct]

abbrev TraceRelationCoefficients := TraceRelationMonomial → ℂ

def evaluateTraceRelationCoefficients
    (c : TraceRelationCoefficients) (U : BlockLinkField)
    (p : BlockPlaquette) : ℂ :=
  ∑ m : TraceRelationMonomial, c m * evaluateTraceRelationMonomial m U p

/-- Coefficients of `a³b - 4a⁴ + a⁵`. -/
def cayleyHamiltonRelationCoefficients : TraceRelationCoefficients
  | 0 => 1
  | 1 => -4
  | 2 => 1

/-- Hard coordinate truncation through canonical dimension sixteen. -/
def traceRelationTruncateThrough16
    (c : TraceRelationCoefficients) : TraceRelationCoefficients :=
  fun m => if traceRelationCanonicalDimension m ≤ 16 then c m else 0

theorem evaluate_cayleyHamiltonRelation
    (U : BlockLinkField) (p : BlockPlaquette) :
    evaluateTraceRelationCoefficients cayleyHamiltonRelationCoefficients U p = 0 := by
  have hCH := centeredDoubleTrace_eq (plaquetteHolonomy U p)
  simp [evaluateTraceRelationCoefficients,
    cayleyHamiltonRelationCoefficients, evaluateTraceRelationMonomial,
    traceRelationPowers, Fin.sum_univ_three,
    plaquetteCenteredTrace, plaquetteCenteredDoubleTrace]
  rw [hCH]
  ring

theorem evaluate_truncatedCayleyHamiltonRelation
    (U : BlockLinkField) (p : BlockPlaquette) :
    evaluateTraceRelationCoefficients
        (traceRelationTruncateThrough16 cayleyHamiltonRelationCoefficients)
        U p =
      plaquetteCenteredTrace U p ^ 3 * plaquetteCenteredDoubleTrace U p -
        4 * plaquetteCenteredTrace U p ^ 4 := by
  simp [evaluateTraceRelationCoefficients,
    traceRelationTruncateThrough16, traceRelationCanonicalDimension,
    traceRelationPowers, cayleyHamiltonRelationCoefficients,
    evaluateTraceRelationMonomial, Fin.sum_univ_three]
  ring

/-! ## Semantic quotient and intrinsic non-descent -/

/-- Semantic equality on every actual block field and every actual block
plaquette. -/
def TraceSemanticallyEquivalent
    (c d : TraceRelationCoefficients) : Prop :=
  ∀ (U : BlockLinkField) (p : BlockPlaquette),
    evaluateTraceRelationCoefficients c U p =
      evaluateTraceRelationCoefficients d U p

instance traceSemanticSetoid : Setoid TraceRelationCoefficients where
  r := TraceSemanticallyEquivalent
  iseqv := ⟨
    fun _ _ _ => rfl,
    fun h U p => (h U p).symm,
    fun hcd hde U p => (hcd U p).trans (hde U p)⟩

abbrev EvaluatedTraceWordQuotient := Quotient traceSemanticSetoid

def traceQuotientClass
    (c : TraceRelationCoefficients) : EvaluatedTraceWordQuotient :=
  Quotient.mk traceSemanticSetoid c

theorem cayleyHamiltonRelation_semantically_zero :
    TraceSemanticallyEquivalent cayleyHamiltonRelationCoefficients 0 := by
  intro U p
  rw [evaluate_cayleyHamiltonRelation]
  simp [evaluateTraceRelationCoefficients]

theorem quarterTurn_centeredTrace : centeredTrace quarterTurn = 2 := by
  norm_num [centeredTrace, quarterTurn, quarterTurnMatrix,
    Matrix.trace, Fin.sum_univ_two]

theorem quarterTurn_centeredDoubleTrace : centeredDoubleTrace quarterTurn = 4 := by
  rw [centeredDoubleTrace_eq, quarterTurn_centeredTrace]
  norm_num

theorem truncatedCayleyHamiltonRelation_witness :
    evaluateTraceRelationCoefficients
        (traceRelationTruncateThrough16 cayleyHamiltonRelationCoefficients)
        witnessField (profilePlaquette 1) = -32 := by
  rw [evaluate_truncatedCayleyHamiltonRelation]
  simp [plaquetteCenteredTrace, plaquetteCenteredDoubleTrace,
    witnessHolonomy_one, quarterTurn_centeredTrace,
    quarterTurn_centeredDoubleTrace]
  norm_num

theorem truncatedCayleyHamiltonRelation_not_semantically_zero :
    ¬ TraceSemanticallyEquivalent
      (traceRelationTruncateThrough16 cayleyHamiltonRelationCoefficients) 0 := by
  intro h
  have hw := h witnessField (profilePlaquette 1)
  rw [truncatedCayleyHamiltonRelation_witness] at hw
  norm_num [evaluateTraceRelationCoefficients] at hw

/-- A representative-wise hard truncation descended to the actual trace-word
semantic quotient. -/
def TraceCanonicalTruncationDescends : Prop :=
  ∃ P : EvaluatedTraceWordQuotient → EvaluatedTraceWordQuotient,
    ∀ c : TraceRelationCoefficients,
      P (traceQuotientClass c) =
        traceQuotientClass (traceRelationTruncateThrough16 c)

/-- **Intrinsic quotient obstruction.**  Dimension-sixteen hard truncation
does not descend through the exact `SU(2)` Cayley--Hamilton trace relation. -/
theorem cayleyHamiltonTruncation_does_not_descend :
    ¬ TraceCanonicalTruncationDescends := by
  rintro ⟨P, hP⟩
  have hrelation :
      traceQuotientClass cayleyHamiltonRelationCoefficients =
        traceQuotientClass 0 :=
    Quotient.sound cayleyHamiltonRelation_semantically_zero
  have hclasses :
      traceQuotientClass
          (traceRelationTruncateThrough16 cayleyHamiltonRelationCoefficients) =
        traceQuotientClass 0 := by
    calc
      traceQuotientClass
          (traceRelationTruncateThrough16 cayleyHamiltonRelationCoefficients) =
          P (traceQuotientClass cayleyHamiltonRelationCoefficients) :=
        (hP cayleyHamiltonRelationCoefficients).symm
      _ = P (traceQuotientClass 0) := congrArg P hrelation
      _ = traceQuotientClass (traceRelationTruncateThrough16 0) := hP 0
      _ = traceQuotientClass 0 := by
        congr 1
        funext m
        simp [traceRelationTruncateThrough16]
  exact truncatedCayleyHamiltonRelation_not_semantically_zero
    (Quotient.exact hclasses)

theorem traceSemanticKernel_not_stable_under_truncation :
    ¬ (∀ c : TraceRelationCoefficients,
      TraceSemanticallyEquivalent c 0 →
        TraceSemanticallyEquivalent (traceRelationTruncateThrough16 c) 0) := by
  intro h
  exact truncatedCayleyHamiltonRelation_not_semantically_zero
    (h cayleyHamiltonRelationCoefficients
      cayleyHamiltonRelation_semantically_zero)

end SU2CayleyHamiltonTruncationObstruction
end YangMills
end QuantumTheory
end Mettapedia
