import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
import Mettapedia.QuantumTheory.YangMills.FiniteOSReconstruction

/-!
# Finite `Z₂` strong-coupling lattice gap

This module records a fully explicit finite lattice gauge canary: the one-link
`Z₂` heat-kernel transfer matrix at heat time `1`.  The transfer has eigenvalues
`1` and `exp (-1)`, hence dimensionless gap `-log (exp (-1) / 1) = 1`.

The theorem is finite-lattice only.  The continuum Yang-Mills mass gap is not
claimed.
-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators

namespace Mettapedia
namespace QuantumTheory
namespace YangMills

/-- One-link `Z₂` lattice gauge configurations, represented by two group values. -/
abbrev Z2OneLinkConfig := Fin 2

/-- The nontrivial `Z₂` character. -/
def z2Character (x : Z2OneLinkConfig) : ℝ :=
  if x = 0 then 1 else -1

/-- Constant transfer eigenvector. -/
def z2ConstantObservable : FiniteObservable Z2OneLinkConfig :=
  fun _ => 1

/-- Sign transfer eigenvector. -/
def z2SignObservable : FiniteObservable Z2OneLinkConfig :=
  z2Character

/-- Strong-coupling heat-kernel ratio at heat time `1`. -/
def z2StrongCouplingRatio : ℝ :=
  Real.exp (-1)

/-- The one-link `Z₂` heat-kernel transfer matrix. -/
def z2StrongCouplingKernel
    (x y : Z2OneLinkConfig) : ℝ :=
  (1 + z2StrongCouplingRatio * z2Character x * z2Character y) / 2

/-- The transfer operator induced by the finite heat kernel. -/
def z2StrongCouplingTransfer
    (f : FiniteObservable Z2OneLinkConfig) :
    FiniteObservable Z2OneLinkConfig :=
  fun x => ∑ y : Z2OneLinkConfig, z2StrongCouplingKernel x y * f y

/-- The largest transfer eigenvalue. -/
def z2StrongCouplingLambdaOne : ℝ := 1

/-- The first nontrivial transfer eigenvalue. -/
def z2StrongCouplingLambdaTwo : ℝ := z2StrongCouplingRatio

/-- The dimensionless transfer spectral gap. -/
def z2StrongCouplingGap : ℝ :=
  -Real.log (z2StrongCouplingLambdaTwo / z2StrongCouplingLambdaOne)

theorem z2StrongCouplingRatio_pos : 0 < z2StrongCouplingRatio := by
  exact Real.exp_pos _

theorem z2StrongCouplingKernel_symmetric :
    OSSymmetric z2StrongCouplingKernel := by
  intro f g
  unfold osBilinearForm z2StrongCouplingKernel z2StrongCouplingRatio z2Character
  repeat rw [Fin.sum_univ_two]
  norm_num
  ring

theorem z2StrongCouplingKernel_self_pairing
    (f : FiniteObservable Z2OneLinkConfig) :
    osBilinearForm z2StrongCouplingKernel f f =
      ((f 0 + f 1) ^ 2 +
        z2StrongCouplingRatio * (f 0 - f 1) ^ 2) / 2 := by
  unfold osBilinearForm z2StrongCouplingKernel z2StrongCouplingRatio z2Character
  repeat rw [Fin.sum_univ_two]
  norm_num
  ring

theorem z2StrongCouplingKernel_reflectionPositive :
    OSReflectionPositive z2StrongCouplingKernel := by
  intro f
  rw [z2StrongCouplingKernel_self_pairing f]
  have hsum : 0 ≤ (f 0 + f 1) ^ 2 := sq_nonneg _
  have hdiff : 0 ≤ z2StrongCouplingRatio * (f 0 - f 1) ^ 2 :=
    mul_nonneg (le_of_lt z2StrongCouplingRatio_pos) (sq_nonneg _)
  nlinarith

theorem z2StrongCouplingTransfer_selfAdjoint :
    OSTransferSelfAdjoint z2StrongCouplingKernel z2StrongCouplingTransfer := by
  intro f g
  unfold osBilinearForm z2StrongCouplingTransfer
    z2StrongCouplingKernel z2StrongCouplingRatio z2Character
  repeat rw [Fin.sum_univ_two]
  ring

theorem z2StrongCouplingTransfer_constant_eigen :
    z2StrongCouplingTransfer z2ConstantObservable =
      fun x => z2StrongCouplingLambdaOne * z2ConstantObservable x := by
  funext x
  fin_cases x <;>
    simp [z2StrongCouplingTransfer, z2StrongCouplingKernel,
      z2StrongCouplingRatio, z2StrongCouplingLambdaOne,
      z2ConstantObservable, z2Character, Fin.sum_univ_two]
    <;> ring

theorem z2StrongCouplingTransfer_sign_eigen :
    z2StrongCouplingTransfer z2SignObservable =
      fun x => z2StrongCouplingLambdaTwo * z2SignObservable x := by
  funext x
  fin_cases x <;>
    simp [z2StrongCouplingTransfer, z2StrongCouplingKernel,
      z2StrongCouplingRatio, z2StrongCouplingLambdaTwo,
      z2SignObservable, z2Character, Fin.sum_univ_two]
    <;> ring

theorem z2Observable_eigenbasis
    (f : FiniteObservable Z2OneLinkConfig) :
    ∃ a b : ℝ,
      f = fun x => a * z2ConstantObservable x + b * z2SignObservable x := by
  refine ⟨(f 0 + f 1) / 2, (f 0 - f 1) / 2, ?_⟩
  funext x
  fin_cases x <;>
    simp [z2ConstantObservable, z2SignObservable, z2Character] <;> ring

theorem z2StrongCouplingGap_eq_one :
    z2StrongCouplingGap = 1 := by
  simp [z2StrongCouplingGap, z2StrongCouplingLambdaTwo,
    z2StrongCouplingLambdaOne, z2StrongCouplingRatio, Real.log_exp]

theorem z2StrongCouplingGap_lower_bound_one :
    (1 : ℝ) ≤ z2StrongCouplingGap := by
  rw [z2StrongCouplingGap_eq_one]

theorem z2StrongCouplingGap_positive :
    0 < z2StrongCouplingGap := by
  rw [z2StrongCouplingGap_eq_one]
  norm_num

theorem z2OneLinkConfig_nontrivial :
    ∃ x y : Z2OneLinkConfig, x ≠ y := by
  exact ⟨0, 1, by norm_num⟩

/-- A concrete finite-lattice mass-gap canary tying together reflection
positivity, OS reconstruction, transfer eigenvectors, and the numeric gap. -/
structure Z2StrongCouplingGapCanary where
  nontrivialConfig : ∃ x y : Z2OneLinkConfig, x ≠ y
  reflectionPositive : OSReflectionPositive z2StrongCouplingKernel
  osReconstruction :
    FiniteOSReconstruction z2StrongCouplingKernel z2StrongCouplingTransfer
  constantEigen :
    z2StrongCouplingTransfer z2ConstantObservable =
      fun x => z2StrongCouplingLambdaOne * z2ConstantObservable x
  signEigen :
    z2StrongCouplingTransfer z2SignObservable =
      fun x => z2StrongCouplingLambdaTwo * z2SignObservable x
  eigenbasis :
    ∀ f : FiniteObservable Z2OneLinkConfig,
      ∃ a b : ℝ,
        f = fun x => a * z2ConstantObservable x + b * z2SignObservable x
  lambdaOnePositive : 0 < z2StrongCouplingLambdaOne
  lambdaTwoPositive : 0 < z2StrongCouplingLambdaTwo
  gapFormula :
    z2StrongCouplingGap =
      -Real.log (z2StrongCouplingLambdaTwo / z2StrongCouplingLambdaOne)
  gapEqualsOne : z2StrongCouplingGap = 1
  gapLowerBoundOne : (1 : ℝ) ≤ z2StrongCouplingGap

/-- The explicit positive finite-lattice canary. -/
def z2StrongCouplingPositiveCanary : Z2StrongCouplingGapCanary where
  nontrivialConfig := z2OneLinkConfig_nontrivial
  reflectionPositive := z2StrongCouplingKernel_reflectionPositive
  osReconstruction :=
    finiteOSReconstruction_of_reflectionPositive_selfAdjoint
      z2StrongCouplingKernel_reflectionPositive
      z2StrongCouplingKernel_symmetric
      z2StrongCouplingTransfer_selfAdjoint
  constantEigen := z2StrongCouplingTransfer_constant_eigen
  signEigen := z2StrongCouplingTransfer_sign_eigen
  eigenbasis := z2Observable_eigenbasis
  lambdaOnePositive := by
    norm_num [z2StrongCouplingLambdaOne]
  lambdaTwoPositive := z2StrongCouplingRatio_pos
  gapFormula := rfl
  gapEqualsOne := z2StrongCouplingGap_eq_one
  gapLowerBoundOne := z2StrongCouplingGap_lower_bound_one

/-- End-to-end finite lattice theorem: the explicit `Z₂` strong-coupling model is
nontrivial, reflection positive, has an OS transfer operator, and has
dimensionless transfer gap at least `1`. -/
theorem z2StrongCoupling_latticeYangMills_massGap_landmark :
    ∃ _ : Z2StrongCouplingGapCanary,
      (∃ x y : Z2OneLinkConfig, x ≠ y) ∧
        OSReflectionPositive z2StrongCouplingKernel ∧
        z2StrongCouplingGap = 1 ∧
        (1 : ℝ) ≤ z2StrongCouplingGap ∧
        0 < z2StrongCouplingGap := by
  exact
    ⟨z2StrongCouplingPositiveCanary,
      z2OneLinkConfig_nontrivial,
      z2StrongCouplingKernel_reflectionPositive,
      z2StrongCouplingGap_eq_one,
      z2StrongCouplingGap_lower_bound_one,
      z2StrongCouplingGap_positive⟩

/-- Dimensionless heat-time gap for the same two-state transfer spectrum. -/
def z2HeatTimeDimensionlessGap (t : ℝ) : ℝ :=
  -Real.log (Real.exp (-t) / 1)

theorem z2HeatTimeDimensionlessGap_eq (t : ℝ) :
    z2HeatTimeDimensionlessGap t = t := by
  simp [z2HeatTimeDimensionlessGap, Real.log_exp]

/-- Physical gap obtained by dividing the dimensionless heat-time gap by lattice
spacing.  This is a scaling diagnostic, not a continuum mass-gap theorem. -/
def z2HeatTimePhysicalGap (a t : ℝ) : ℝ :=
  z2HeatTimeDimensionlessGap t / a

theorem z2QuadraticHeatTime_physicalGap_eq
    {a : ℝ} (ha : a ≠ 0) :
    z2HeatTimePhysicalGap a (a ^ 2) = a := by
  rw [z2HeatTimePhysicalGap, z2HeatTimeDimensionlessGap_eq]
  field_simp [ha]

/-- A concrete gap-closing schedule for the finite model under the heat-time
scaling `t(a)=a²`: the physical gap can be made smaller than any positive
threshold by taking the lattice spacing small enough. -/
theorem z2QuadraticHeatTime_physicalGap_closes :
    ∀ ε : ℝ, 0 < ε →
      ∃ a : ℝ,
        0 < a ∧ a < ε ∧
          z2HeatTimePhysicalGap a (a ^ 2) < ε := by
  intro ε hε
  refine ⟨ε / 2, by linarith, by linarith, ?_⟩
  have hne : ε / 2 ≠ 0 := by linarith
  rw [z2QuadraticHeatTime_physicalGap_eq hne]
  linarith

end YangMills
end QuantumTheory
end Mettapedia
