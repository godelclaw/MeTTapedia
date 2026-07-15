import Mettapedia.QuantumTheory.YangMills.SU2WilsonBlockPilot
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Sym.Card
import Mathlib.Data.Finsupp.Multiset
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.Tactic

/-!
# Associated-graded extraction on the exact `SU(2)`, `b = 2` block

This module constructs our associated-graded repair of the v14 extraction
operator.  It does not claim that v14 selected this repair.

The exact block has seven co-tree `SU(2)` links.  Complexifying the three
Lie-algebra coordinates of each link gives twenty-one local log coordinates.
The associated-graded jet space through degree sixteen is the span of all
monomials of total degree at most sixteen in those coordinates.  The monomial
family is proved linearly independent after evaluation, and its coefficient
functionals give an exact identity jet matrix.

For the literal supremum norm on the manuscript's nested polydisks, radial
restriction reduces the multivariable estimate to one-variable Cauchy
estimates.  At `r₁ / r₀ = 1/2`, degree-sixteen extraction therefore has the
exact certified upper bound

`sum (d = 0..16) (1/2)^d = 131071 / 65536 < 2`.

The analytic theorem quantifies over the actual block boundary field `V` and
is consequently uniform in `V`.  Its radial analyticity and outer-polydisk
bound are the definition of the analytic domain on which an operator-norm
claim can be made; they are not assertions about the still-unconstructed
Wilson RG map.
-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators
open Metric Set
open Module

namespace Mettapedia
namespace QuantumTheory
namespace YangMills
namespace SU2AssociatedGradedExtraction

open SU2WilsonBlockPilot

/-! ## The exact block's complexified co-tree log chart -/

/-- Three complexified Lie-algebra coordinates for each of the seven exact
co-tree links of the `b = 2` block. -/
abbrev BlockLogCoordinate := CoTreeLink × Fin 3

/-- The exact coordinate count is `7 * 3 = 21`. -/
theorem blockLogCoordinate_card : Fintype.card BlockLogCoordinate = 21 := by
  rw [Fintype.card_prod, coTreeLink_count]
  norm_num

/-- A point in our complexified local co-tree chart. -/
abbrev BlockLogField := BlockLogCoordinate → ℂ

/-! ## A certified monomial basis through degree sixteen -/

/-- Monomials of exact degree `d`, represented without an arbitrary ordering
of the twenty-one coordinates. -/
abbrev HomogeneousBlockMonomial (d : ℕ) := Sym BlockLogCoordinate d

/-- Every monomial of total degree at most sixteen. -/
abbrev BlockJetMonomial16 :=
  Σ d : Fin 17, HomogeneousBlockMonomial d.1

/-- Exponent vector of a homogeneous monomial. -/
def blockJetExponent (m : BlockJetMonomial16) : BlockLogCoordinate →₀ ℕ :=
  (Sym.equivNatSum BlockLogCoordinate m.1.1) m.2

theorem blockJetExponent_totalDegree (m : BlockJetMonomial16) :
    (blockJetExponent m).sum (fun _ n => n) = m.1.1 := by
  exact (Sym.equivNatSum BlockLogCoordinate m.1.1 m.2).2

theorem blockJetExponent_injective : Function.Injective blockJetExponent := by
  rintro ⟨d, m⟩ ⟨e, n⟩ h
  have hdegree : d.1 = e.1 := by
    have hs := congrArg (fun x => x.sum (fun _ k => k)) h
    exact
      (Sym.equivNatSum BlockLogCoordinate d.1 m).2.symm.trans
        (hs.trans (Sym.equivNatSum BlockLogCoordinate e.1 n).2)
  have hfin : d = e := Fin.ext hdegree
  subst e
  have hmn : m = n :=
    (Sym.equivNatSum BlockLogCoordinate d.1).injective (by
      apply Subtype.ext
      simpa [blockJetExponent] using h)
  subst n
  rfl

/-- The corresponding multivariate monomial in the complexified co-tree
coordinates. -/
def blockJetBasisPolynomial (m : BlockJetMonomial16) :
    MvPolynomial BlockLogCoordinate ℂ :=
  MvPolynomial.monomial (blockJetExponent m) 1

theorem blockJetBasisPolynomial_totalDegree (m : BlockJetMonomial16) :
    (blockJetBasisPolynomial m).totalDegree = m.1.1 := by
  rw [blockJetBasisPolynomial,
    MvPolynomial.totalDegree_monomial _ one_ne_zero]
  exact blockJetExponent_totalDegree m

/-- The declared monomials are linearly independent as polynomials. -/
theorem blockJetBasisPolynomial_linearIndependent :
    LinearIndependent ℂ blockJetBasisPolynomial := by
  rw [show blockJetBasisPolynomial =
      (MvPolynomial.basisMonomials BlockLogCoordinate ℂ :
        (BlockLogCoordinate →₀ ℕ) →
          MvPolynomial BlockLogCoordinate ℂ) ∘ blockJetExponent by
    funext m
    rfl]
  exact
    (MvPolynomial.basisMonomials BlockLogCoordinate ℂ).linearIndependent.comp
      blockJetExponent blockJetExponent_injective

/-- Our degree-sixteen associated-graded space.  Defining it as the span of
the full bounded-degree monomial family avoids smuggling in a quotient or a
caller-selected dimension. -/
abbrev BlockAssociatedGraded16 :=
  Submodule.span ℂ (Set.range blockJetBasisPolynomial)

/-- The certified transversal basis of our associated-graded space. -/
def blockAssociatedGradedBasis16 :
    Basis BlockJetMonomial16 ℂ BlockAssociatedGraded16 :=
  Basis.span blockJetBasisPolynomial_linearIndependent

@[simp] theorem blockAssociatedGradedBasis16_coe
    (m : BlockJetMonomial16) :
    ((blockAssociatedGradedBasis16 m : BlockAssociatedGraded16) :
      MvPolynomial BlockLogCoordinate ℂ) = blockJetBasisPolynomial m := by
  simp [blockAssociatedGradedBasis16]

/-- Coefficient dual (the exact algebraic jet functional) for one basis
monomial. -/
def blockDualJet16 (m : BlockJetMonomial16) :
    BlockAssociatedGraded16 →ₗ[ℂ] ℂ :=
  (blockAssociatedGradedBasis16.coord m)

/-- Exact biorthogonality.  Thus the basis/dual-jet matrix is literally the
identity, with no unrecorded conditioning factor. -/
theorem blockDualJet16_biorthogonal
    (m n : BlockJetMonomial16) :
    blockDualJet16 m (blockAssociatedGradedBasis16 n) =
      if n = m then 1 else 0 := by
  classical
  by_cases h : n = m
  · subst n
    simp [blockDualJet16]
  · simp [blockDualJet16, h]

/-- Matrix of exact dual-jet evaluations. -/
def blockJetMatrix16 :
    Matrix BlockJetMonomial16 BlockJetMonomial16 ℂ :=
  fun m n => blockDualJet16 m (blockAssociatedGradedBasis16 n)

/-- The exact jet matrix is the identity matrix. -/
theorem blockJetMatrix16_eq_one : blockJetMatrix16 = 1 := by
  classical
  ext m n
  rw [blockJetMatrix16, blockDualJet16_biorthogonal]
  simp [Matrix.one_apply, eq_comm]

/-- Polynomial evaluation on the complexified co-tree chart is injective on
the associated-graded space.  Hence the polynomial basis remains independent
after evaluation; this is not merely a syntactic basis declaration. -/
theorem blockAssociatedGraded16_evaluation_injective :
    Function.Injective
      (fun p : BlockAssociatedGraded16 =>
        fun A : BlockLogField => MvPolynomial.eval A p.1) := by
  intro p q h
  apply Subtype.ext
  apply MvPolynomial.funext
  intro A
  exact congrFun h A

/-- Exact Hilbert count for all monomials through degree sixteen in the
twenty-one-coordinate chart.  This large number is for our full gauge-fixed
jet space, not v14's unsupported claim of at most `1851` gauge-invariant
continuum templates. -/
theorem blockJetMonomial16_card :
    Fintype.card BlockJetMonomial16 = 12875774670 := by
  rw [Fintype.card_sigma]
  simp_rw [Sym.card_sym_eq_multichoose, blockLogCoordinate_card]
  rw [Fin.sum_univ_eq_sum_range]
  rw [Nat.sum_range_multichoose 16 21]
  norm_num [Nat.choose]

/-! ## Literal manuscript sup-norm bound by radial Cauchy extraction -/

/-- The `d`th radial Taylor coefficient at the origin. -/
def radialJetCoefficient (d : ℕ) (f : ℂ → ℂ) : ℂ :=
  ((d.factorial : ℂ)⁻¹) * iteratedDeriv d f 0

/-- Radial Taylor extraction through degree sixteen, evaluated at radial
parameter one. -/
def radialExtraction16 (f : ℂ → ℂ) : ℂ :=
  ∑ d ∈ Finset.range 17, radialJetCoefficient d f

/-- The exact geometric-series constant at radius ratio `1/2`. -/
def manuscriptSupExtractionConstant16 : ℝ :=
  (131071 : ℝ) / 65536

theorem manuscriptSupExtractionConstant16_eq_geomSum :
    manuscriptSupExtractionConstant16 =
      ∑ d ∈ Finset.range 17, ((1 : ℝ) / 2) ^ d := by
  norm_num [manuscriptSupExtractionConstant16, Finset.sum_range_succ]

theorem manuscriptSupExtractionConstant16_lt_two :
    manuscriptSupExtractionConstant16 < 2 := by
  norm_num [manuscriptSupExtractionConstant16]

/-- Cauchy's estimate after division by the factorial: every radial Taylor
coefficient at outer radial radius two is bounded by `C * 2⁻ᵈ`. -/
theorem norm_radialJetCoefficient_le
    {f : ℂ → ℂ} {C : ℝ}
    (hf : DiffContOnCl ℂ f (Metric.ball 0 2))
    (hbound : ∀ z ∈ Metric.sphere (0 : ℂ) 2, ‖f z‖ ≤ C)
    (d : ℕ) :
    ‖radialJetCoefficient d f‖ ≤ C * ((1 : ℝ) / 2) ^ d := by
  have hderiv :=
    Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le
      d (by norm_num : (0 : ℝ) < 2) hf hbound
  have hfac : (0 : ℝ) < d.factorial := by positivity
  calc
    ‖radialJetCoefficient d f‖ =
        (d.factorial : ℝ)⁻¹ * ‖iteratedDeriv d f 0‖ := by
      simp [radialJetCoefficient]
    _ ≤ (d.factorial : ℝ)⁻¹ *
        ((d.factorial : ℝ) * C / (2 : ℝ) ^ d) := by
      exact mul_le_mul_of_nonneg_left hderiv (inv_nonneg.mpr hfac.le)
    _ = C * ((1 : ℝ) / 2) ^ d := by
      field_simp
      rw [mul_assoc]
      rw [← mul_pow]
      norm_num

/-- **The manuscript-norm decision on radial analytic functions.**  At the
literal radius ratio `r₁/r₀ = 1/2`, associated-graded extraction through
degree sixteen has operator norm at most `131071/65536`, hence strictly less
than two. -/
theorem norm_radialExtraction16_le
    {f : ℂ → ℂ} {C : ℝ}
    (hf : DiffContOnCl ℂ f (Metric.ball 0 2))
    (hbound : ∀ z ∈ Metric.sphere (0 : ℂ) 2, ‖f z‖ ≤ C) :
    ‖radialExtraction16 f‖ ≤ manuscriptSupExtractionConstant16 * C := by
  calc
    ‖radialExtraction16 f‖
        ≤ ∑ d ∈ Finset.range 17, ‖radialJetCoefficient d f‖ := by
          exact norm_sum_le _ _
    _ ≤ ∑ d ∈ Finset.range 17, C * ((1 : ℝ) / 2) ^ d := by
          exact Finset.sum_le_sum fun d _ =>
            norm_radialJetCoefficient_le hf hbound d
    _ = manuscriptSupExtractionConstant16 * C := by
          rw [← Finset.mul_sum]
          rw [← manuscriptSupExtractionConstant16_eq_geomSum]
          ring

/-! ## Uniform specialization to the exact block boundary parameter -/

/-- A block-local analytic functional in the complexified co-tree chart,
with the exact group-valued boundary field left as a parameter. -/
abbrev BlockAnalyticFunctional := BoundaryField → BlockLogField → ℂ

/-- Coordinatewise closed polydisk in the complexified co-tree chart. -/
def InBlockPolydisk (r : ℝ) (A : BlockLogField) : Prop :=
  ∀ i : BlockLogCoordinate, ‖A i‖ ≤ r

/-- Radial slice through one inner-polydisk point.  The outer radius `2`
corresponds exactly to `r₀ = 2 r₁`. -/
def blockRadialSlice
    (F : BlockAnalyticFunctional) (V : BoundaryField)
    (A : BlockLogField) : ℂ → ℂ :=
  fun z => F V (z • A)

/-- The radial analytic and sup-bound obligations defining the literal
manuscript `H∞` domain at radius ratio `1/2`.  These assumptions concern the
input analytic functional.  No Wilson RG analyticity is discharged by this
definition. -/
structure BlockRadialHInfinityAtHalf
    (F : BlockAnalyticFunctional) (r₁ C : ℝ) : Prop where
  inner_radius_pos : 0 < r₁
  bound_nonneg : 0 ≤ C
  analytic : ∀ (V : BoundaryField) (A : BlockLogField),
    InBlockPolydisk r₁ A →
    DiffContOnCl ℂ (blockRadialSlice F V A) (Metric.ball 0 2)
  outer_bound : ∀ (V : BoundaryField) (A : BlockLogField)
      (_hA : InBlockPolydisk r₁ A) (z : ℂ),
    z ∈ Metric.sphere (0 : ℂ) 2 →
    ‖blockRadialSlice F V A z‖ ≤ C

/-- Our associated-graded block extraction, evaluated pointwise. -/
def blockAssociatedGradedExtraction16
    (F : BlockAnalyticFunctional) : BlockAnalyticFunctional :=
  fun V A => radialExtraction16 (blockRadialSlice F V A)

/-- **Uniform exact-block headline.**  For every actual boundary field `V`,
the associated-graded extraction has the same strict norm-two certificate.
The bound contains no boundary-dependent conditioning factor. -/
theorem blockAssociatedGradedExtraction16_norm_le
    {F : BlockAnalyticFunctional} {r₁ C : ℝ}
    (hF : BlockRadialHInfinityAtHalf F r₁ C)
    (V : BoundaryField) (A : BlockLogField)
    (hA : InBlockPolydisk r₁ A) :
    ‖blockAssociatedGradedExtraction16 F V A‖ ≤
      manuscriptSupExtractionConstant16 * C := by
  exact norm_radialExtraction16_le
    (hF.analytic V A hA) (hF.outer_bound V A hA)

end SU2AssociatedGradedExtraction
end YangMills
end QuantumTheory
end Mettapedia
