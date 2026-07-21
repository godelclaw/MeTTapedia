import Mettapedia.QuantumTheory.YangMills.WilsonBlockMajorant
import Mathlib.Tactic

/-!
# Transfer audit for the v14 extended-extraction projection

The manuscript defines extended extraction only as "the projection onto" a
finite-dimensional low-canonical-dimension subspace.  That range specification
does not determine the projection kernel or its dual jet functionals.  This file
closes the resulting logical question in both directions.

* A concrete two-coordinate projection can have the prescribed low-dimensional
  range, be idempotent, and fix every low vector, while having arbitrarily large
  coefficient `ℓ¹` norm.  Thus no bound `≤ 2` follows from the manuscript's bare
  projection definition.
* If explicit basis and dual-jet matrices are supplied, their column sums give
  a machine-checked operator bound.  Applied around the norm-one canonical
  Wilson-coordinate truncation, this is the precise transfer route required by
  the completion blueprint.

The counterexample concerns underdetermination of the extended projection, not
the explicit dimension-`4` observable jets in the manuscript's Appendix I.
-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators

namespace Mettapedia
namespace QuantumTheory
namespace YangMills

/-! ## A projection-range specification cannot control the norm -/

/-- Coefficient `ℓ¹` size on a two-coordinate chart. -/
def pairL1 (x : ℝ × ℝ) : ℝ := |x.1| + |x.2|

/-- The exact algebraic content of "a projection onto the low-coordinate
subspace": idempotence, low output, and identity on low vectors. -/
structure IsProjectionOntoFirstCoordinate (P : (ℝ × ℝ) → (ℝ × ℝ)) : Prop where
  idempotent : ∀ x, P (P x) = P x
  output_low : ∀ x, (P x).2 = 0
  fixes_low : ∀ x, x.2 = 0 → P x = x

/-- A family of skew projections onto the first-coordinate subspace.  The
parameter `M` is the hidden choice of complement/dual functional. -/
def skewLowProjection (M : ℝ) (x : ℝ × ℝ) : ℝ × ℝ :=
  (x.1 + M * x.2, 0)

theorem skewLowProjection_isProjection (M : ℝ) :
    IsProjectionOntoFirstCoordinate (skewLowProjection M) := by
  constructor
  · intro x
    simp [skewLowProjection]
  · intro x
    simp [skewLowProjection]
  · intro x hx
    ext <;> simp [skewLowProjection, hx]

theorem pairL1_skewLowProjection_zero_one (M : ℝ) :
    pairL1 (skewLowProjection M (0, 1)) = |M| := by
  simp [pairL1, skewLowProjection]

/-- **Machine-checked transfer obstruction.**  Merely being a projection onto
the requested low-dimensional subspace does not imply the advertised operator
bound `2`: the skew projection with `M = 3` violates it on `(0,1)`. -/
theorem projectionRangeSpecification_does_not_imply_bound_two :
    ∃ P : (ℝ × ℝ) → (ℝ × ℝ),
      IsProjectionOntoFirstCoordinate P ∧
      ¬ ∀ x, pairL1 (P x) ≤ 2 * pairL1 x := by
  refine ⟨skewLowProjection 3, skewLowProjection_isProjection 3, ?_⟩
  intro h
  have hw := h (0, 1)
  norm_num [pairL1, skewLowProjection] at hw

/-! ## The exact finite-matrix transfer route -/

variable {Input Output Middle : Type*}

/-- Coefficient `ℓ¹` norm for a finite coordinate vector. -/
def coefficientL1 [Fintype Input] (c : Input → ℝ) : ℝ :=
  ∑ i, |c i|

/-- Matrix action written without choosing a basis library representation. -/
def coefficientMatrixApply [Fintype Input]
    (A : Output → Input → ℝ) (c : Input → ℝ) : Output → ℝ :=
  fun o => ∑ i, A o i * c i

/-- A uniform column-sum budget, the exact induced coefficient-`ℓ¹` matrix
bound. -/
def HasCoefficientL1ColumnBound [Fintype Output]
    (A : Output → Input → ℝ) (C : ℝ) : Prop :=
  ∀ i, (∑ o, |A o i|) ≤ C

/-- Finite column-sum estimate for a basis or dual-jet matrix. -/
theorem coefficientL1_matrixApply_le
    [Fintype Input] [Fintype Output]
    (A : Output → Input → ℝ) (c : Input → ℝ) {C : ℝ}
    (hA : HasCoefficientL1ColumnBound A C) :
    coefficientL1 (Input := Output) (coefficientMatrixApply A c) ≤
      C * coefficientL1 c := by
  classical
  calc
    coefficientL1 (Input := Output) (coefficientMatrixApply A c)
        = ∑ o, |∑ i, A o i * c i| := by
            rfl
    _ ≤ ∑ o, ∑ i, |A o i * c i| := by
          exact Finset.sum_le_sum fun o _ => Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i, (∑ o, |A o i|) * |c i| := by
          simp_rw [abs_mul]
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro i _
          rw [Finset.sum_mul]
    _ ≤ ∑ i, C * |c i| := by
          exact Finset.sum_le_sum fun i _ =>
            mul_le_mul_of_nonneg_right (hA i) (abs_nonneg _)
    _ = C * coefficientL1 c := by
          simp [coefficientL1, Finset.mul_sum]

/-- Encoding through dual jets and then embedding the invariant basis. -/
def basisJetProjection
    [Fintype Input] [Fintype Middle]
    (embed : Output → Middle → ℝ)
    (jet : Middle → Input → ℝ)
    (c : Input → ℝ) : Output → ℝ :=
  coefficientMatrixApply embed (coefficientMatrixApply jet c)

/-- **Faithful transfer theorem.**  Once the manuscript supplies explicit
dual-jet and basis-embedding matrices, their coefficient `ℓ¹` column bounds
multiply.  This is the finite conditioning factor omitted by the bare phrase
"the projection". -/
theorem coefficientL1_basisJetProjection_le
    [Fintype Input] [Fintype Output] [Fintype Middle]
    (embed : Output → Middle → ℝ)
    (jet : Middle → Input → ℝ)
    (c : Input → ℝ) {Cembed Cjet : ℝ}
    (hEmbed : HasCoefficientL1ColumnBound embed Cembed)
    (hJet : HasCoefficientL1ColumnBound jet Cjet)
    (hCembed : 0 ≤ Cembed) :
    coefficientL1 (Input := Output) (basisJetProjection embed jet c) ≤
      (Cembed * Cjet) * coefficientL1 c := by
  unfold basisJetProjection
  calc
    coefficientL1 (Input := Output)
        (coefficientMatrixApply embed (coefficientMatrixApply jet c))
      ≤ Cembed * coefficientL1 (Input := Middle)
          (coefficientMatrixApply jet c) :=
        coefficientL1_matrixApply_le embed _ hEmbed
    _ ≤ Cembed * (Cjet * coefficientL1 c) := by
          exact mul_le_mul_of_nonneg_left
            (coefficientL1_matrixApply_le jet c hJet) hCembed
    _ = (Cembed * Cjet) * coefficientL1 c := by ring

end YangMills
end QuantumTheory
end Mettapedia
