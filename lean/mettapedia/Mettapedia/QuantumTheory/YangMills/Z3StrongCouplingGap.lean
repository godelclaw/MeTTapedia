import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
import Mettapedia.QuantumTheory.YangMills.FiniteOSReconstruction

/-!
# Finite `Z3` strong-coupling lattice gap

This module records a fully explicit three-configuration finite lattice gauge
canary.  The one-link transfer kernel has eigenvalue `1` on constants and
`exp (-1)` on the two-dimensional mean-zero sector, so the dimensionless
transfer gap is `1`.

The final theorems are finite-lattice and scaling diagnostics only.  They do
not claim the continuum Yang-Mills mass gap.
-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators

namespace Mettapedia
namespace QuantumTheory
namespace YangMills

/-- One-link `Z3` lattice gauge configurations, represented by three group values. -/
abbrev Z3OneLinkConfig := Fin 3

/-- Constant transfer eigenvector. -/
def z3ConstantObservable : FiniteObservable Z3OneLinkConfig :=
  fun _ => 1

/-- First mean-zero transfer eigenvector. -/
def z3FirstObservable : FiniteObservable Z3OneLinkConfig :=
  fun x => if x = 0 then 1 else if x = 1 then -1 else 0

/-- Second mean-zero transfer eigenvector. -/
def z3SecondObservable : FiniteObservable Z3OneLinkConfig :=
  fun x => if x = 0 then 1 else if x = 1 then 1 else -2

/-- Strong-coupling heat-kernel ratio at heat time `1`. -/
def z3StrongCouplingRatio : ℝ :=
  Real.exp (-1)

/-- The one-link three-state strong-coupling heat kernel. -/
def z3StrongCouplingKernel
    (x y : Z3OneLinkConfig) : ℝ :=
  if x = y then
    (1 + 2 * z3StrongCouplingRatio) / 3
  else
    (1 - z3StrongCouplingRatio) / 3

/-- The transfer operator induced by the finite heat kernel. -/
def z3StrongCouplingTransfer
    (f : FiniteObservable Z3OneLinkConfig) :
    FiniteObservable Z3OneLinkConfig :=
  fun x => ∑ y : Z3OneLinkConfig, z3StrongCouplingKernel x y * f y

/-- The largest transfer eigenvalue. -/
def z3StrongCouplingLambdaOne : ℝ := 1

/-- The nontrivial transfer eigenvalue on the mean-zero sector. -/
def z3StrongCouplingLambdaTwo : ℝ := z3StrongCouplingRatio

/-- The dimensionless transfer spectral gap. -/
def z3StrongCouplingGap : ℝ :=
  -Real.log (z3StrongCouplingLambdaTwo / z3StrongCouplingLambdaOne)

theorem z3StrongCouplingRatio_pos : 0 < z3StrongCouplingRatio := by
  exact Real.exp_pos _

theorem z3StrongCouplingKernel_symmetric :
    OSSymmetric z3StrongCouplingKernel := by
  intro f g
  unfold osBilinearForm z3StrongCouplingKernel z3StrongCouplingRatio
  repeat rw [Fin.sum_univ_three]
  norm_num [Fin.ext_iff]
  ring_nf

theorem z3StrongCouplingKernel_self_pairing
    (f : FiniteObservable Z3OneLinkConfig) :
    osBilinearForm z3StrongCouplingKernel f f =
      ((f 0 + f 1 + f 2) ^ 2 +
        z3StrongCouplingRatio *
          ((f 0 - f 1) ^ 2 + (f 0 - f 2) ^ 2 + (f 1 - f 2) ^ 2)) / 3 := by
  unfold osBilinearForm z3StrongCouplingKernel z3StrongCouplingRatio
  repeat rw [Fin.sum_univ_three]
  norm_num [Fin.ext_iff]
  ring_nf

theorem z3StrongCouplingKernel_reflectionPositive :
    OSReflectionPositive z3StrongCouplingKernel := by
  intro f
  rw [z3StrongCouplingKernel_self_pairing f]
  have hsum : 0 ≤ (f 0 + f 1 + f 2) ^ 2 := sq_nonneg _
  have hdiff_sum :
      0 ≤ (f 0 - f 1) ^ 2 + (f 0 - f 2) ^ 2 + (f 1 - f 2) ^ 2 := by
    nlinarith [sq_nonneg (f 0 - f 1), sq_nonneg (f 0 - f 2),
      sq_nonneg (f 1 - f 2)]
  have hdiff :
      0 ≤ z3StrongCouplingRatio *
        ((f 0 - f 1) ^ 2 + (f 0 - f 2) ^ 2 + (f 1 - f 2) ^ 2) :=
    mul_nonneg (le_of_lt z3StrongCouplingRatio_pos) hdiff_sum
  nlinarith

theorem z3StrongCouplingTransfer_selfAdjoint :
    OSTransferSelfAdjoint z3StrongCouplingKernel z3StrongCouplingTransfer := by
  intro f g
  unfold osBilinearForm z3StrongCouplingTransfer
    z3StrongCouplingKernel z3StrongCouplingRatio
  repeat rw [Fin.sum_univ_three]
  norm_num [Fin.ext_iff]
  ring_nf

theorem z3StrongCouplingTransfer_constant_eigen :
    z3StrongCouplingTransfer z3ConstantObservable =
      fun x => z3StrongCouplingLambdaOne * z3ConstantObservable x := by
  funext x
  fin_cases x <;>
    simp [z3StrongCouplingTransfer, z3StrongCouplingKernel,
      z3StrongCouplingRatio, z3StrongCouplingLambdaOne,
      z3ConstantObservable, Fin.sum_univ_three]
    <;> ring_nf

theorem z3StrongCouplingTransfer_first_eigen :
    z3StrongCouplingTransfer z3FirstObservable =
      fun x => z3StrongCouplingLambdaTwo * z3FirstObservable x := by
  funext x
  fin_cases x <;>
    simp [z3StrongCouplingTransfer, z3StrongCouplingKernel,
      z3StrongCouplingRatio, z3StrongCouplingLambdaTwo,
      z3FirstObservable, Fin.sum_univ_three]
    <;> ring_nf

theorem z3StrongCouplingTransfer_second_eigen :
    z3StrongCouplingTransfer z3SecondObservable =
      fun x => z3StrongCouplingLambdaTwo * z3SecondObservable x := by
  funext x
  fin_cases x <;>
    simp [z3StrongCouplingTransfer, z3StrongCouplingKernel,
      z3StrongCouplingRatio, z3StrongCouplingLambdaTwo,
      z3SecondObservable, Fin.sum_univ_three]
    <;> ring_nf

theorem z3Observable_eigenbasis
    (f : FiniteObservable Z3OneLinkConfig) :
    ∃ a b c : ℝ,
      f =
        fun x =>
          a * z3ConstantObservable x +
            b * z3FirstObservable x +
              c * z3SecondObservable x := by
  refine
    ⟨(f 0 + f 1 + f 2) / 3, (f 0 - f 1) / 2,
      (f 0 + f 1 - 2 * f 2) / 6, ?_⟩
  funext x
  fin_cases x <;>
    simp [z3ConstantObservable, z3FirstObservable, z3SecondObservable] <;> ring

theorem z3StrongCouplingGap_eq_one :
    z3StrongCouplingGap = 1 := by
  simp [z3StrongCouplingGap, z3StrongCouplingLambdaTwo,
    z3StrongCouplingLambdaOne, z3StrongCouplingRatio, Real.log_exp]

theorem z3StrongCouplingGap_lower_bound_one :
    (1 : ℝ) ≤ z3StrongCouplingGap := by
  rw [z3StrongCouplingGap_eq_one]

theorem z3StrongCouplingGap_positive :
    0 < z3StrongCouplingGap := by
  rw [z3StrongCouplingGap_eq_one]
  norm_num

theorem z3OneLinkConfig_nontrivial :
    ∃ x y : Z3OneLinkConfig, x ≠ y := by
  exact ⟨0, 1, by norm_num⟩

/-- A concrete finite-lattice mass-gap canary tying together reflection
positivity, OS reconstruction, transfer eigenvectors, and the numeric gap. -/
structure Z3StrongCouplingGapCanary where
  nontrivialConfig : ∃ x y : Z3OneLinkConfig, x ≠ y
  reflectionPositive : OSReflectionPositive z3StrongCouplingKernel
  osReconstruction :
    FiniteOSReconstruction z3StrongCouplingKernel z3StrongCouplingTransfer
  constantEigen :
    z3StrongCouplingTransfer z3ConstantObservable =
      fun x => z3StrongCouplingLambdaOne * z3ConstantObservable x
  firstEigen :
    z3StrongCouplingTransfer z3FirstObservable =
      fun x => z3StrongCouplingLambdaTwo * z3FirstObservable x
  secondEigen :
    z3StrongCouplingTransfer z3SecondObservable =
      fun x => z3StrongCouplingLambdaTwo * z3SecondObservable x
  eigenbasis :
    ∀ f : FiniteObservable Z3OneLinkConfig,
      ∃ a b c : ℝ,
        f =
          fun x =>
            a * z3ConstantObservable x +
              b * z3FirstObservable x +
                c * z3SecondObservable x
  lambdaOnePositive : 0 < z3StrongCouplingLambdaOne
  lambdaTwoPositive : 0 < z3StrongCouplingLambdaTwo
  gapFormula :
    z3StrongCouplingGap =
      -Real.log (z3StrongCouplingLambdaTwo / z3StrongCouplingLambdaOne)
  gapEqualsOne : z3StrongCouplingGap = 1
  gapLowerBoundOne : (1 : ℝ) ≤ z3StrongCouplingGap

/-- The explicit positive finite-lattice canary. -/
def z3StrongCouplingPositiveCanary : Z3StrongCouplingGapCanary where
  nontrivialConfig := z3OneLinkConfig_nontrivial
  reflectionPositive := z3StrongCouplingKernel_reflectionPositive
  osReconstruction :=
    finiteOSReconstruction_of_reflectionPositive_selfAdjoint
      z3StrongCouplingKernel_reflectionPositive
      z3StrongCouplingKernel_symmetric
      z3StrongCouplingTransfer_selfAdjoint
  constantEigen := z3StrongCouplingTransfer_constant_eigen
  firstEigen := z3StrongCouplingTransfer_first_eigen
  secondEigen := z3StrongCouplingTransfer_second_eigen
  eigenbasis := z3Observable_eigenbasis
  lambdaOnePositive := by
    norm_num [z3StrongCouplingLambdaOne]
  lambdaTwoPositive := z3StrongCouplingRatio_pos
  gapFormula := rfl
  gapEqualsOne := z3StrongCouplingGap_eq_one
  gapLowerBoundOne := z3StrongCouplingGap_lower_bound_one

/-- End-to-end finite lattice theorem: the explicit `Z3` strong-coupling model
is nontrivial, reflection positive, has an OS transfer operator, and has
dimensionless transfer gap at least `1`. -/
theorem z3StrongCoupling_latticeYangMills_massGap_landmark :
    ∃ _ : Z3StrongCouplingGapCanary,
      (∃ x y : Z3OneLinkConfig, x ≠ y) ∧
        OSReflectionPositive z3StrongCouplingKernel ∧
        z3StrongCouplingGap = 1 ∧
        (1 : ℝ) ≤ z3StrongCouplingGap ∧
        0 < z3StrongCouplingGap := by
  exact
    ⟨z3StrongCouplingPositiveCanary,
      z3OneLinkConfig_nontrivial,
      z3StrongCouplingKernel_reflectionPositive,
      z3StrongCouplingGap_eq_one,
      z3StrongCouplingGap_lower_bound_one,
      z3StrongCouplingGap_positive⟩

/-- Dimensionless heat-time gap for the same three-state transfer spectrum. -/
def z3HeatTimeDimensionlessGap (t : ℝ) : ℝ :=
  -Real.log (Real.exp (-t) / 1)

theorem z3HeatTimeDimensionlessGap_eq (t : ℝ) :
    z3HeatTimeDimensionlessGap t = t := by
  simp [z3HeatTimeDimensionlessGap, Real.log_exp]

/-- Physical gap obtained by dividing the dimensionless heat-time gap by lattice
spacing.  This is a scaling diagnostic, not a continuum mass-gap theorem. -/
def z3HeatTimePhysicalGap (a t : ℝ) : ℝ :=
  z3HeatTimeDimensionlessGap t / a

/-- Concrete half-scale refinement contraction constant. -/
def z3HalfScaleKappa : ℝ := 1 / 2

theorem z3HalfScaleKappa_pos :
    0 < z3HalfScaleKappa := by
  norm_num [z3HalfScaleKappa]

theorem z3HalfScaleKappa_lt_one :
    z3HalfScaleKappa < 1 := by
  norm_num [z3HalfScaleKappa]

theorem z3LinearHeatTime_physicalGap_eq
    {a κ : ℝ} (ha : a ≠ 0) :
    z3HeatTimePhysicalGap a (κ * a) = κ := by
  rw [z3HeatTimePhysicalGap, z3HeatTimeDimensionlessGap_eq]
  field_simp [ha]

/-- A half-scale refinement step preserves the physical gap on linear heat-time
schedules `t(a)=k*a`.  This is a one-step gap-uniformity diagnostic. -/
theorem z3HalfScaleLinearRGStep_preserves_physicalGap
    {a κ : ℝ} (ha : a ≠ 0) :
    z3HeatTimePhysicalGap
        (z3HalfScaleKappa * a) (κ * (z3HalfScaleKappa * a)) =
      z3HeatTimePhysicalGap a (κ * a) := by
  have hk : z3HalfScaleKappa ≠ 0 := by
    norm_num [z3HalfScaleKappa]
  have hka : z3HalfScaleKappa * a ≠ 0 := mul_ne_zero hk ha
  rw [z3LinearHeatTime_physicalGap_eq hka,
    z3LinearHeatTime_physicalGap_eq ha]

theorem z3LinearHeatTime_unitLowerBound
    {a : ℝ} (ha : a ≠ 0) :
    (1 : ℝ) ≤ z3HeatTimePhysicalGap a (1 * a) := by
  rw [z3LinearHeatTime_physicalGap_eq ha]

theorem z3LinearHeatTime_uniformPositive
    {a κ : ℝ} (ha : a ≠ 0) (hκ : 0 < κ) :
    0 < z3HeatTimePhysicalGap a (κ * a) := by
  rw [z3LinearHeatTime_physicalGap_eq ha]
  exact hκ

theorem z3QuadraticHeatTime_physicalGap_eq
    {a : ℝ} (ha : a ≠ 0) :
    z3HeatTimePhysicalGap a (a ^ 2) = a := by
  rw [z3HeatTimePhysicalGap, z3HeatTimeDimensionlessGap_eq]
  field_simp [ha]

/-- The quadratic heat-time schedule still closes the physical gap; this keeps
the finite gap from being promoted to a continuum endpoint. -/
theorem z3QuadraticHeatTime_physicalGap_closes :
    ∀ ε : ℝ, 0 < ε →
      ∃ a : ℝ,
        0 < a ∧ a < ε ∧
          z3HeatTimePhysicalGap a (a ^ 2) < ε := by
  intro ε hε
  refine ⟨ε / 2, by linarith, by linarith, ?_⟩
  have hne : ε / 2 ≠ 0 := by linarith
  rw [z3QuadraticHeatTime_physicalGap_eq hne]
  linarith

/-- A concrete one-step refinement canary with contraction constant `1/2`. -/
structure Z3HalfScaleRGCanary where
  kappaPositive : 0 < z3HalfScaleKappa
  kappaLessThanOne : z3HalfScaleKappa < 1
  baseSpacingPositive : 0 < (1 : ℝ)
  refinedSpacingPositive : 0 < z3HalfScaleKappa * 1
  physicalGapPreserved :
    z3HeatTimePhysicalGap
        (z3HalfScaleKappa * 1) (1 * (z3HalfScaleKappa * 1)) =
      z3HeatTimePhysicalGap 1 (1 * 1)
  refinedUniformLowerBound :
    (1 : ℝ) ≤
      z3HeatTimePhysicalGap
        (z3HalfScaleKappa * 1) (1 * (z3HalfScaleKappa * 1))

/-- Positive inhabited canary for the half-scale refinement step. -/
def z3HalfScaleRGPositiveCanary : Z3HalfScaleRGCanary where
  kappaPositive := z3HalfScaleKappa_pos
  kappaLessThanOne := z3HalfScaleKappa_lt_one
  baseSpacingPositive := by
    norm_num
  refinedSpacingPositive := by
    norm_num [z3HalfScaleKappa]
  physicalGapPreserved := by
    exact
      z3HalfScaleLinearRGStep_preserves_physicalGap
        (a := 1) (κ := 1) (by norm_num)
  refinedUniformLowerBound := by
    exact
      z3LinearHeatTime_unitLowerBound
        (a := z3HalfScaleKappa * 1) (by norm_num [z3HalfScaleKappa])

end YangMills
end QuantumTheory
end Mettapedia
