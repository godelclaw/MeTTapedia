import Mettapedia.QuantumTheory.YangMills.SU2WilsonBlockPilot

/-!
# Boundary-extension truncation regression on the evaluated `SU(2)` block

This module records an auxiliary boundary-convention regression on the exact
`SU(2)`, `b = 2` Wilson block.  It uses two adjacent
plaquette positions and the forward finite difference with fixed-boundary zero
extension.  The zero extension is the minimal block-local convention after
subtracting the fixed boundary value from the fluctuation coordinate.

On this two-cell carrier the shift squares to zero, so `δ = T - 1` satisfies
`δ² + 2δ + 1 = 0`.  Multiplication by `δ³` gives an exact evaluated relation
whose terms have canonical dimensions `15`, `16`, and `17` when applied to the
cubic Wilson density of base dimension `12`.  Hard truncation through dimension
`16` deletes the last term, but an explicit special-unitary link field makes
the surviving expression nonzero.  Consequently truncation is not an
operator on the quotient induced by this zero-extension convention.

This boundary-induced relation is not the manuscript-facing decision theorem:
the manuscript does not itself select zero extension for its plaquette-log
operator coordinates.  The intrinsic decision is instead supplied by
`SU2CayleyHamiltonTruncationObstruction`, using the exact trace relation that
the off-shell policy explicitly requires.  This module remains useful as a
regression for any future block-local zero-extension implementation.
-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators Matrix.Norms.Elementwise

namespace Mettapedia
namespace QuantumTheory
namespace YangMills
namespace SU2CanonicalTruncationObstruction

open SU2WilsonBlockPilot

/-! ## An actual special-unitary witness on adjacent block plaquettes -/

/-- A diagonal quarter turn in the defining representation of `SU(2)`. -/
def quarterTurnMatrix : Matrix (Fin 2) (Fin 2) ℂ :=
  !![Complex.I, 0; 0, -Complex.I]

/-- The quarter-turn matrix as an element of the actual matrix group `SU(2)`. -/
def quarterTurn : SU2 :=
  ⟨quarterTurnMatrix, by
    rw [Matrix.mem_specialUnitaryGroup_iff]
    constructor
    · rw [Matrix.mem_unitaryGroup_iff]
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [quarterTurnMatrix, Matrix.mul_apply]
    · simp [quarterTurnMatrix, Matrix.det_fin_two]⟩

theorem quarterTurn_trace_real :
    (Matrix.trace (quarterTurn : Matrix (Fin 2) (Fin 2) ℂ)).re = 0 := by
  norm_num [quarterTurn, quarterTurnMatrix, Matrix.trace, Fin.sum_univ_two]

/-- Origins of two adjacent plaquettes in the first block direction. -/
def profileOrigin (i : Fin 2) : BlockVertex :=
  ![Fin.castLE (by decide) i, 0, 0, 1]

/-- Two adjacent `(1,2)` plaquettes.  The first is boundary-adjacent and the
second meets it across the first block direction. -/
def profilePlaquette (i : Fin 2) : BlockPlaquette where
  origin := profileOrigin i
  first := 1
  second := 2
  ordered := by decide
  canStepFirst := by simp [profileOrigin]
  canStepSecond := by simp [profileOrigin]

/-- A link field whose only nonidentity link is the first edge of the second
profile plaquette.  This is an actual `SU(2)` field on the exact block. -/
def witnessField : BlockLinkField := fun e =>
  if e = (profilePlaquette 1).firstLink then quarterTurn else 1

theorem witnessHolonomy_zero :
    plaquetteHolonomy witnessField (profilePlaquette 0) = 1 := by
  have hff : (profilePlaquette 0).firstLink ≠
      (profilePlaquette 1).firstLink := by decide
  have hsf : (profilePlaquette 0).secondAfterFirst ≠
      (profilePlaquette 1).firstLink := by decide
  have hfs : (profilePlaquette 0).firstAfterSecond ≠
      (profilePlaquette 1).firstLink := by decide
  have hss : (profilePlaquette 0).secondLink ≠
      (profilePlaquette 1).firstLink := by decide
  simp [plaquetteHolonomy, witnessField, hff, hsf, hfs, hss]

theorem witnessHolonomy_one :
    plaquetteHolonomy witnessField (profilePlaquette 1) = quarterTurn := by
  have hsf : (profilePlaquette 1).secondAfterFirst ≠
      (profilePlaquette 1).firstLink := by decide
  have hfs : (profilePlaquette 1).firstAfterSecond ≠
      (profilePlaquette 1).firstLink := by decide
  have hss : (profilePlaquette 1).secondLink ≠
      (profilePlaquette 1).firstLink := by decide
  simp [plaquetteHolonomy, witnessField, hsf, hfs, hss]

theorem witnessPotential_zero :
    plaquettePotential witnessField (profilePlaquette 0) = 0 := by
  rw [plaquettePotential, witnessHolonomy_zero]
  norm_num [specialUnitaryWilsonPotential, Matrix.trace, Fin.sum_univ_two]

theorem witnessPotential_one :
    plaquettePotential witnessField (profilePlaquette 1) = 1 := by
  rw [plaquettePotential, witnessHolonomy_one]
  simp [specialUnitaryWilsonPotential, quarterTurn_trace_real]

/-- The cubic Wilson density on the two selected plaquettes.  Since the
normalized plaquette coordinate has leading canonical dimension four, this
actual gauge-invariant observable has base canonical dimension twelve. -/
def wilsonDensity12Profile (U : BlockLinkField) : Fin 2 → ℝ :=
  fun i => (plaquettePotential U (profilePlaquette i)) ^ 3

/-- The concrete two-site profile used by the witness. -/
def sampleProfile : Fin 2 → ℝ
  | 0 => 0
  | 1 => 1

theorem witness_wilsonDensity12Profile :
    wilsonDensity12Profile witnessField = sampleProfile := by
  funext i
  fin_cases i
  · norm_num [wilsonDensity12Profile, witnessPotential_zero, sampleProfile]
  · norm_num [wilsonDensity12Profile, witnessPotential_one, sampleProfile]

/-! ## Fixed-boundary finite differences and their exact relation -/

/-- Forward translation on the two-cell fluctuation profile, extended by zero
beyond the fixed boundary. -/
def zeroBoundaryShift (f : Fin 2 → ℝ) : Fin 2 → ℝ
  | 0 => f 1
  | 1 => 0

/-- The block-local forward difference `T - 1`. -/
def finiteDifference (f : Fin 2 → ℝ) : Fin 2 → ℝ :=
  zeroBoundaryShift f - f

/-- Iterated block-local forward difference. -/
def iteratedDifference : ℕ → (Fin 2 → ℝ) → (Fin 2 → ℝ)
  | 0, f => f
  | n + 1, f => finiteDifference (iteratedDifference n f)

theorem zeroBoundaryShift_sq (f : Fin 2 → ℝ) :
    zeroBoundaryShift (zeroBoundaryShift f) = 0 := by
  funext i
  fin_cases i <;> simp [zeroBoundaryShift]

/-- Exact two-cell relation `δ⁵ + 2δ⁴ + δ³ = 0`. -/
theorem order_five_relation (f : Fin 2 → ℝ) :
    iteratedDifference 5 f + 2 • iteratedDifference 4 f +
      iteratedDifference 3 f = 0 := by
  funext i
  fin_cases i <;>
    simp [iteratedDifference, finiteDifference, zeroBoundaryShift] <;> ring

theorem witness_order_five_value :
    iteratedDifference 5 sampleProfile 0 = 5 := by
  norm_num [iteratedDifference, finiteDifference, zeroBoundaryShift,
    sampleProfile]

/-! ## A finite action-sector slice and canonical truncation -/

/-- Coefficients of derivatives of order zero through five.  This finite slice
is sufficient for a no-descent result: an operator on the full evaluated
quotient would restrict to it. -/
abbrev DerivativeCoefficients := Fin 6 → ℝ

/-- Evaluation of a derivative-coefficient vector on a two-site profile. -/
def evaluateCoefficients (c : DerivativeCoefficients) (f : Fin 2 → ℝ) :
    Fin 2 → ℝ :=
  fun i => ∑ k : Fin 6, c k * iteratedDifference k f i

/-- Coefficients of `δ³ + 2δ⁴ + δ⁵`. -/
def orderFiveRelationCoefficients : DerivativeCoefficients := fun k =>
  if k = 3 then 1 else if k = 4 then 2 else if k = 5 then 1 else 0

/-- Canonical dimension of the `k`th derivative of the dimension-twelve
Wilson density. -/
def canonicalDimension (k : Fin 6) : ℕ := 12 + k

/-- Hard coefficient truncation through canonical dimension sixteen. -/
def truncateThrough16 (c : DerivativeCoefficients) : DerivativeCoefficients :=
  fun k => if canonicalDimension k ≤ 16 then c k else 0

theorem evaluate_orderFiveRelation (f : Fin 2 → ℝ) :
    evaluateCoefficients orderFiveRelationCoefficients f = 0 := by
  rw [show evaluateCoefficients orderFiveRelationCoefficients f =
      iteratedDifference 3 f + 2 • iteratedDifference 4 f +
        iteratedDifference 5 f by
    funext i
    simp [evaluateCoefficients, orderFiveRelationCoefficients,
      Fin.sum_univ_six]]
  simpa [add_comm, add_left_comm, add_assoc] using order_five_relation f

theorem evaluate_truncated_orderFiveRelation (f : Fin 2 → ℝ) :
    evaluateCoefficients (truncateThrough16 orderFiveRelationCoefficients) f =
      iteratedDifference 3 f + 2 • iteratedDifference 4 f := by
  funext i
  simp [evaluateCoefficients, truncateThrough16, canonicalDimension,
    orderFiveRelationCoefficients, Fin.sum_univ_six]

/-- Semantic equality after evaluation on every actual block link field. -/
def SemanticallyEquivalent (c d : DerivativeCoefficients) : Prop :=
  ∀ U : BlockLinkField,
    evaluateCoefficients c (wilsonDensity12Profile U) =
      evaluateCoefficients d (wilsonDensity12Profile U)

instance semanticSetoid : Setoid DerivativeCoefficients where
  r := SemanticallyEquivalent
  iseqv := ⟨
    fun _ _ => rfl,
    fun h U => (h U).symm,
    fun hcd hde U => (hcd U).trans (hde U)⟩

/-- The evaluated Wilson relation quotient on the finite action-sector slice. -/
abbrev EvaluatedWilsonQuotient := Quotient semanticSetoid

def quotientClass (c : DerivativeCoefficients) : EvaluatedWilsonQuotient :=
  Quotient.mk semanticSetoid c

theorem orderFiveRelation_semantically_zero :
    SemanticallyEquivalent orderFiveRelationCoefficients 0 := by
  intro U
  rw [evaluate_orderFiveRelation]
  funext i
  simp [evaluateCoefficients]

theorem truncatedRelation_nonzero_on_witness :
    evaluateCoefficients
        (truncateThrough16 orderFiveRelationCoefficients)
        (wilsonDensity12Profile witnessField) 0 = -5 := by
  rw [witness_wilsonDensity12Profile,
    evaluate_truncated_orderFiveRelation]
  norm_num [iteratedDifference, finiteDifference, zeroBoundaryShift,
    sampleProfile]

theorem truncatedRelation_not_semantically_zero :
    ¬ SemanticallyEquivalent
      (truncateThrough16 orderFiveRelationCoefficients) 0 := by
  intro h
  have h0 := congrFun (h witnessField) 0
  rw [truncatedRelation_nonzero_on_witness] at h0
  norm_num [evaluateCoefficients] at h0

/-- A descended truncation would be a function on semantic quotient classes
whose value on every coefficient representative is represented by its hard
canonical truncation. -/
def ZeroBoundaryTruncationDescends : Prop :=
  ∃ P : EvaluatedWilsonQuotient → EvaluatedWilsonQuotient,
    ∀ c : DerivativeCoefficients,
      P (quotientClass c) = quotientClass (truncateThrough16 c)

/-- Under the selected zero-extension convention, canonical-dimension
truncation through dimension sixteen is not well-defined on the induced
evaluated quotient. -/
theorem zeroBoundaryTruncation_does_not_descend :
    ¬ ZeroBoundaryTruncationDescends := by
  rintro ⟨P, hP⟩
  have hrelation :
      quotientClass orderFiveRelationCoefficients = quotientClass 0 :=
    Quotient.sound orderFiveRelation_semantically_zero
  have hclasses :
      quotientClass (truncateThrough16 orderFiveRelationCoefficients) =
        quotientClass 0 := by
    calc
      quotientClass (truncateThrough16 orderFiveRelationCoefficients) =
          P (quotientClass orderFiveRelationCoefficients) :=
        (hP orderFiveRelationCoefficients).symm
      _ = P (quotientClass 0) := congrArg P hrelation
      _ = quotientClass (truncateThrough16 0) := hP 0
      _ = quotientClass 0 := by
        congr 1
        funext k
        simp [truncateThrough16]
  exact truncatedRelation_not_semantically_zero (Quotient.exact hclasses)

/-- Equivalent kernel-stability statement: a semantic zero relation is sent
to a nonzero semantic class by hard canonical truncation. -/
theorem zeroBoundarySemanticKernel_not_stable_under_truncation :
    ¬ (∀ c : DerivativeCoefficients,
      SemanticallyEquivalent c 0 →
        SemanticallyEquivalent (truncateThrough16 c) 0) := by
  intro h
  exact truncatedRelation_not_semantically_zero
    (h orderFiveRelationCoefficients orderFiveRelation_semantically_zero)

end SU2CanonicalTruncationObstruction
end YangMills
end QuantumTheory
end Mettapedia
