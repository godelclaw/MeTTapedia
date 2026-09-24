import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeAdaptiveStrainCover
import Mathlib.Analysis.Fourier.AddCircleMulti

/-!
# Finite Fourier approximation of adaptive cover weights

The adaptive strain cover supplies continuous partition weights but the
periodic multiplier argument consumes finite Fourier polynomials.  The
multivariate Stone--Weierstrass theorem for the unit torus says that the
linear span of its Fourier characters is uniformly dense.  This file turns
that density statement into an explicit finitely supported coefficient
approximation, first for one complex continuous function and then
simultaneously for every weight in a finite adaptive partition.

The approximating polynomials need not themselves be nonnegative or sum
exactly to one.  Their quantitative coverage loss is handled separately; no
such property is silently assumed here.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes
namespace PancakeAdaptiveFourierPartition

open scoped BigOperators
open Set Submodule

/-- A continuous real function regarded as a complex continuous function. -/
def complexifyContinuousMap {X : Type*} [TopologicalSpace X]
    (f : C(X, ℝ)) : C(X, ℂ) where
  toFun x := (f x : ℂ)
  continuous_toFun := Complex.continuous_ofReal.comp f.continuous

@[simp]
theorem complexifyContinuousMap_apply {X : Type*} [TopologicalSpace X]
    (f : C(X, ℝ)) (x : X) :
    complexifyContinuousMap f x = (f x : ℂ) := rfl

/-- Squaring the norm of a complex approximation to a real number in
`[0,1]` costs at most `delta * (delta + 2)`. -/
theorem abs_normSq_sub_sq_le_of_norm_sub
    (z : ℂ) (r delta : ℝ) (hr : 0 ≤ r) (hrone : r ≤ 1)
    (hdelta : 0 ≤ delta) (hclose : ‖z - (r : ℂ)‖ ≤ delta) :
    |Complex.normSq z - r ^ 2| ≤ delta * (delta + 2) := by
  have hrnorm : ‖(r : ℂ)‖ = r := by simp [abs_of_nonneg hr]
  have hdiff : |‖z‖ - r| ≤ delta := by
    rw [← hrnorm]
    exact (abs_norm_sub_norm_le z (r : ℂ)).trans hclose
  have hzle : ‖z‖ ≤ delta + r := by
    calc
      ‖z‖ = ‖(z - (r : ℂ)) + (r : ℂ)‖ := by rw [sub_add_cancel]
      _ ≤ ‖z - (r : ℂ)‖ + ‖(r : ℂ)‖ := norm_add_le _ _
      _ ≤ delta + r := by rw [hrnorm]; gcongr
  have hsum : ‖z‖ + r ≤ delta + 2 := by linarith
  rw [Complex.normSq_eq_norm_sq]
  calc
    |‖z‖ ^ 2 - r ^ 2| = |‖z‖ - r| * (‖z‖ + r) := by
      rw [sq_sub_sq, abs_mul, abs_of_nonneg (add_nonneg (norm_nonneg z) hr)]
      ring
    _ ≤ delta * (‖z‖ + r) :=
      mul_le_mul_of_nonneg_right hdiff (add_nonneg (norm_nonneg z) hr)
    _ ≤ delta * (delta + 2) :=
      mul_le_mul_of_nonneg_left hsum hdelta

/-- Uniform Stone--Weierstrass approximation on a finite-dimensional unit
torus, with the approximant represented by finitely supported Fourier
coefficients. -/
theorem exists_finsupp_mFourier_approximation
    {d : Type*} [Fintype d]
    (f : C(UnitAddTorus d, ℂ)) {epsilon : ℝ}
    (hepsilon : 0 < epsilon) :
    ∃ coeff : (d → ℤ) →₀ ℂ,
      ‖f - coeff.sum (fun k a ↦
        a • UnitAddTorus.mFourier k)‖ < epsilon := by
  have hf : f ∈
      (span ℂ (range (UnitAddTorus.mFourier (d := d)))).topologicalClosure := by
    rw [UnitAddTorus.span_mFourier_closure_eq_top]
    trivial
  obtain ⟨g, hg, hfg⟩ := Metric.mem_closure_iff.mp hf epsilon hepsilon
  obtain ⟨coeff, hcoeff⟩ :=
    Finsupp.mem_span_range_iff_exists_finsupp.mp hg
  refine ⟨coeff, ?_⟩
  rw [hcoeff]
  simpa only [dist_eq_norm] using hfg

/-- Pointwise form of the same uniform finite-Fourier approximation. -/
theorem exists_finsupp_mFourier_pointwise_approximation
    {d : Type*} [Fintype d]
    (f : C(UnitAddTorus d, ℂ)) {epsilon : ℝ}
    (hepsilon : 0 < epsilon) :
    ∃ coeff : (d → ℤ) →₀ ℂ,
      ∀ x : UnitAddTorus d,
        ‖f x - (coeff.sum (fun k a ↦
          a • UnitAddTorus.mFourier k)) x‖ < epsilon := by
  obtain ⟨coeff, hcoeff⟩ :=
    exists_finsupp_mFourier_approximation f hepsilon
  refine ⟨coeff, fun x ↦ ?_⟩
  exact lt_of_le_of_lt
    ((f - coeff.sum (fun k a ↦
      a • UnitAddTorus.mFourier k)).norm_coe_le_norm x) hcoeff

/-- Every continuous real torus weight has a finite complex Fourier
polynomial uniformly approximating its real inclusion. -/
theorem exists_finsupp_mFourier_realWeight_approximation
    {d : Type*} [Fintype d]
    (weight : C(UnitAddTorus d, ℝ)) {epsilon : ℝ}
    (hepsilon : 0 < epsilon) :
    ∃ coeff : (d → ℤ) →₀ ℂ,
      ∀ x : UnitAddTorus d,
        ‖(weight x : ℂ) - (coeff.sum (fun k a ↦
          a • UnitAddTorus.mFourier k)) x‖ < epsilon := by
  simpa only [complexifyContinuousMap_apply] using
    exists_finsupp_mFourier_pointwise_approximation
      (complexifyContinuousMap weight) hepsilon

/-- A finite family of continuous real torus weights admits simultaneous
finite-Fourier approximants at one common tolerance. -/
theorem exists_finsupp_mFourier_finiteWeightFamily_approximation
    {d ι : Type*} [Fintype d] [Fintype ι]
    (weight : ι → C(UnitAddTorus d, ℝ)) {epsilon : ℝ}
    (hepsilon : 0 < epsilon) :
    ∃ coeff : ι → ((d → ℤ) →₀ ℂ),
      ∀ i x, ‖(weight i x : ℂ) -
        ((coeff i).sum (fun k a ↦
          a • UnitAddTorus.mFourier k)) x‖ < epsilon := by
  choose coeff hcoeff using fun i ↦
    exists_finsupp_mFourier_realWeight_approximation
      (weight i) hepsilon
  exact ⟨coeff, hcoeff⟩

/-! ## Nonnegative quadratic Fourier weights -/

/-- Continuous square root of a nonnegative continuous weight.  The
definition is continuous even without recording nonnegativity in its type. -/
def sqrtContinuousMap {X : Type*} [TopologicalSpace X]
    (weight : C(X, ℝ)) : C(X, ℝ) where
  toFun x := Real.sqrt (weight x)
  continuous_toFun := Real.continuous_sqrt.comp weight.continuous

@[simp]
theorem sqrtContinuousMap_apply {X : Type*} [TopologicalSpace X]
    (weight : C(X, ℝ)) (x : X) :
    sqrtContinuousMap weight x = Real.sqrt (weight x) := rfl

/-- Approximate the square roots of a finite partition of unity.  Squared
complex norms of the resulting trigonometric polynomials are nonnegative and
approximate the original weights quantitatively. -/
theorem exists_finsupp_mFourier_partition_normSq_approximation
    {d ι : Type*} [Fintype d] [Fintype ι]
    (weight : PartitionOfUnity ι (UnitAddTorus d))
    {delta : ℝ} (hdelta : 0 < delta) :
    ∃ coeff : ι → ((d → ℤ) →₀ ℂ),
      ∀ i x,
        |Complex.normSq
            (((coeff i).sum (fun k a ↦
              a • UnitAddTorus.mFourier k)) x) - weight i x| ≤
          delta * (delta + 2) := by
  obtain ⟨coeff, hcoeff⟩ :=
    exists_finsupp_mFourier_finiteWeightFamily_approximation
      (fun i ↦ sqrtContinuousMap (weight i)) hdelta
  refine ⟨coeff, ?_⟩
  intro i x
  let polynomial : ℂ :=
    ((coeff i).sum (fun k a ↦
      a • UnitAddTorus.mFourier k)) x
  let root : ℝ := Real.sqrt (weight i x)
  have hclose : ‖polynomial - (root : ℂ)‖ ≤ delta := by
    have h := le_of_lt (hcoeff i x)
    simpa only [sqrtContinuousMap_apply, norm_sub_rev,
      polynomial, root] using h
  have hroot_nonneg : 0 ≤ root := Real.sqrt_nonneg _
  have hroot_le_one : root ≤ 1 := by
    exact Real.sqrt_le_one.mpr (weight.le_one i x)
  have hsquare : root ^ 2 = weight i x := by
    exact Real.sq_sqrt (weight.nonneg i x)
  simpa only [hsquare, polynomial] using
    abs_normSq_sub_sq_le_of_norm_sub polynomial root delta
      hroot_nonneg hroot_le_one hdelta.le hclose

/-- The same quadratic approximation retains quantitative locality.  Where
an original partition weight vanishes, the Fourier polynomial may have a
tail, but its squared norm is strictly smaller than `delta ^ 2`. -/
theorem exists_finsupp_mFourier_partition_normSq_approximation_with_leakage
    {d ι : Type*} [Fintype d] [Fintype ι]
    (weight : PartitionOfUnity ι (UnitAddTorus d))
    {delta : ℝ} (hdelta : 0 < delta) :
    ∃ coeff : ι → ((d → ℤ) →₀ ℂ),
      (∀ i x,
        |Complex.normSq
            (((coeff i).sum (fun k a ↦
              a • UnitAddTorus.mFourier k)) x) - weight i x| ≤
          delta * (delta + 2)) ∧
      (∀ i x, weight i x = 0 →
        Complex.normSq
            (((coeff i).sum (fun k a ↦
              a • UnitAddTorus.mFourier k)) x) < delta ^ 2) := by
  obtain ⟨coeff, hcoeff⟩ :=
    exists_finsupp_mFourier_finiteWeightFamily_approximation
      (fun i ↦ sqrtContinuousMap (weight i)) hdelta
  refine ⟨coeff, ?_, ?_⟩
  · intro i x
    let polynomial : ℂ :=
      ((coeff i).sum (fun k a ↦
        a • UnitAddTorus.mFourier k)) x
    let root : ℝ := Real.sqrt (weight i x)
    have hclose : ‖polynomial - (root : ℂ)‖ ≤ delta := by
      have h := le_of_lt (hcoeff i x)
      simpa only [sqrtContinuousMap_apply, norm_sub_rev,
        polynomial, root] using h
    have hroot_nonneg : 0 ≤ root := Real.sqrt_nonneg _
    have hroot_le_one : root ≤ 1 := by
      exact Real.sqrt_le_one.mpr (weight.le_one i x)
    have hsquare : root ^ 2 = weight i x := by
      exact Real.sq_sqrt (weight.nonneg i x)
    simpa only [hsquare, polynomial] using
      abs_normSq_sub_sq_le_of_norm_sub polynomial root delta
        hroot_nonneg hroot_le_one hdelta.le hclose
  · intro i x hzero
    let polynomial : ℂ :=
      ((coeff i).sum (fun k a ↦
        a • UnitAddTorus.mFourier k)) x
    have hpoly : ‖polynomial‖ < delta := by
      have h := hcoeff i x
      simpa [sqrtContinuousMap_apply, hzero, polynomial] using h
    rw [Complex.normSq_eq_norm_sq]
    nlinarith [norm_nonneg polynomial]

/-- Summing the nonnegative quadratic Fourier approximants preserves the
partition coverage up to the explicit finite-family error. -/
theorem exists_finsupp_mFourier_partition_coverage
    {d ι : Type*} [Fintype d] [Fintype ι]
    (weight : PartitionOfUnity ι (UnitAddTorus d))
    {delta : ℝ} (hdelta : 0 < delta) :
    ∃ coeff : ι → ((d → ℤ) →₀ ℂ),
      ∀ x,
        |∑ i : ι, Complex.normSq
              (((coeff i).sum (fun k a ↦
                a • UnitAddTorus.mFourier k)) x) - 1| ≤
          (Fintype.card ι : ℝ) * (delta * (delta + 2)) := by
  obtain ⟨coeff, hcoeff⟩ :=
    exists_finsupp_mFourier_partition_normSq_approximation
      weight hdelta
  refine ⟨coeff, ?_⟩
  intro x
  have hsum : (∑ i : ι, weight i x) = 1 := by
    simpa only [finsum_eq_sum_of_fintype] using
      weight.sum_eq_one (Set.mem_univ x)
  have hreplace :
      (∑ i : ι, Complex.normSq
          (((coeff i).sum (fun k a ↦
            a • UnitAddTorus.mFourier k)) x)) - 1 =
        (∑ i : ι, Complex.normSq
          (((coeff i).sum (fun k a ↦
            a • UnitAddTorus.mFourier k)) x)) -
          ∑ i : ι, weight i x := by
    exact congrArg
      (fun t : ℝ ↦
        (∑ i : ι, Complex.normSq
          (((coeff i).sum (fun k a ↦
            a • UnitAddTorus.mFourier k)) x)) - t)
      hsum |>.symm
  rw [hreplace, ← Finset.sum_sub_distrib]
  calc
    |∑ i : ι,
        (Complex.normSq
            (((coeff i).sum (fun k a ↦
              a • UnitAddTorus.mFourier k)) x) - weight i x)| ≤
        ∑ i : ι, |Complex.normSq
            (((coeff i).sum (fun k a ↦
              a • UnitAddTorus.mFourier k)) x) - weight i x| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : ι, delta * (delta + 2) := by
      exact Finset.sum_le_sum fun i hi ↦ hcoeff i x
    _ = (Fintype.card ι : ℝ) * (delta * (delta + 2)) := by
      simp

/-- At sufficiently fine approximation tolerance the quadratic Fourier
weights retain a uniform positive coverage, so their total weight never
degenerates. -/
theorem exists_finsupp_mFourier_partition_coverage_bounds
    {d ι : Type*} [Fintype d] [Fintype ι]
    (weight : PartitionOfUnity ι (UnitAddTorus d))
    {delta : ℝ} (hdelta : 0 < delta)
    (hsmall :
      (Fintype.card ι : ℝ) * (delta * (delta + 2)) ≤ 1 / 2) :
    ∃ coeff : ι → ((d → ℤ) →₀ ℂ),
      ∀ x,
        1 / 2 ≤
          ∑ i : ι, Complex.normSq
            (((coeff i).sum (fun k a ↦
              a • UnitAddTorus.mFourier k)) x) ∧
        (∑ i : ι, Complex.normSq
            (((coeff i).sum (fun k a ↦
              a • UnitAddTorus.mFourier k)) x)) ≤ 3 / 2 := by
  obtain ⟨coeff, hcoeff⟩ :=
    exists_finsupp_mFourier_partition_coverage weight hdelta
  refine ⟨coeff, ?_⟩
  intro x
  have habs := hcoeff x
  rw [abs_le] at habs
  constructor <;> linarith

end PancakeAdaptiveFourierPartition
end NavierStokes
end FluidDynamics
end Mettapedia
