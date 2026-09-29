import Mettapedia.QuantumTheory.YangMills.WilsonBlockElimination

/-!
# A two-plaquette Wilson test of boundary simplification

The gauge group is `Z/2Z`, written multiplicatively. The Wilson potential is
`1 - sign g`, and the coupling is `log 2`; a positive plaquette has weight one
and a negative plaquette weight `1/4`. Six independent outer links and one
independent seam link form the literal two-plaquette rectangle from
`WilsonBlockElimination.Rectangle`.

The two plaquette signs have covariance zero. After the seam is integrated
out, their separate conditional expectations have covariance `72/425`. The
averaged conditional covariance is `-72/425`, cancelling this apparent
correlation exactly. Thus even this finite Wilson law cannot transport a
two-marked correlation using only the separate one-marked projections.

Both exterior three-link path marginals remain uniform, but their joint law
has Wilson-loop expectation `9/25`. Replacing that law by the product of its
marginals loses this gauge-invariant observable. The boundary weight is also
identified with the weighted semantics of a GSLT route.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory
open scoped Topology BigOperators

namespace Mettapedia.QuantumTheory.YangMills.WilsonRectangleElimination

open WilsonBlockElimination
open CompactTransferGap
open StrongCouplingTwist (holonomy)

/-- The two-element gauge group, with its discrete topology and full sigma algebra. -/
def Gauge := Multiplicative (ZMod 2)

instance : CommGroup Gauge := inferInstanceAs (CommGroup (Multiplicative (ZMod 2)))
instance : Fintype Gauge := inferInstanceAs (Fintype (Multiplicative (ZMod 2)))
instance : DecidableEq Gauge := inferInstanceAs (DecidableEq (Multiplicative (ZMod 2)))
instance : TopologicalSpace Gauge := ⊥
instance : DiscreteTopology Gauge := ⟨rfl⟩
instance : MeasurableSpace Gauge := ⊤
instance : BorelSpace Gauge := ⟨borel_eq_top_of_discrete.symm⟩

def negative : Gauge := Multiplicative.ofAdd 1

@[simp] theorem negative_ne_one : negative ≠ 1 := by decide
@[simp] theorem negative_mul_negative : negative * negative = 1 := by decide
@[simp] theorem negative_inv : negative⁻¹ = negative := by decide

theorem eq_one_or_negative (g : Gauge) : g = 1 ∨ g = negative := by
  fin_cases g
  · exact Or.inl rfl
  · exact Or.inr rfl

@[simp] theorem inv_eq_self (g : Gauge) : g⁻¹ = g := by
  rcases eq_one_or_negative g with rfl | rfl <;> simp

/-- The real nontrivial character of the gauge group. -/
def sign (g : Gauge) : ℝ := if g = 1 then 1 else -1

theorem sign_mul (g h : Gauge) : sign (g * h) = sign g * sign h := by
  rcases eq_one_or_negative g with rfl | rfl <;>
    rcases eq_one_or_negative h with rfl | rfl <;> norm_num [sign]

def potential (g : Gauge) : ℝ := 1 - sign g

theorem potential_continuous : Continuous potential := continuous_of_discreteTopology

theorem potential_bounds (g : Gauge) : 0 ≤ potential g ∧ potential g ≤ 2 := by
  unfold potential sign
  split_ifs <;> norm_num

def singleWeight (g : Gauge) : ℝ := if g = 1 then 1 else 1 / 4

theorem singleWeight_pos (g : Gauge) : 0 < singleWeight g := by
  unfold singleWeight
  split_ifs <;> norm_num

/-- This rational weight is exactly the Wilson weight at the stated coupling. -/
theorem singleWeight_eq_exp (g : Gauge) :
    singleWeight g = Real.exp (-Real.log 2 * potential g) := by
  have h : Real.exp (-(Real.log 2) * 2) = (1 / 4 : ℝ) := by
    rw [show -(Real.log 2) * 2 = -(Real.log 2) + -(Real.log 2) by ring,
      Real.exp_add, Real.exp_neg, Real.exp_log (by norm_num)]
    norm_num
  by_cases hg : g = 1
  · simp [singleWeight, potential, sign, hg]
  · simp only [singleWeight, potential, sign, hg, ↓reduceIte]
    convert h.symm using 1
    congr 1
    ring

abbrev Boundary := Rectangle.Boundary Gauge

/-- Rational presentation of the two-plaquette Wilson density. -/
def weight : C(Boundary × Gauge, ℝ) :=
  ⟨fun p => singleWeight (holonomy (Rectangle.leftPlaquette p)) *
      singleWeight (holonomy (Rectangle.rightPlaquette p)), continuous_of_discreteTopology⟩

theorem weight_pos (p : Boundary × Gauge) : 0 < weight p :=
  mul_pos (singleWeight_pos _) (singleWeight_pos _)

theorem weight_eq_wilson : weight = Rectangle.density potential potential_continuous (Real.log 2) := by
  ext p
  exact congrArg₂ (· * ·) (singleWeight_eq_exp _) (singleWeight_eq_exp _)

def leftSign : C(Boundary × Gauge, ℝ) :=
  ⟨fun p => sign (holonomy (Rectangle.leftPlaquette p)), continuous_of_discreteTopology⟩

def rightSign : C(Boundary × Gauge, ℝ) :=
  ⟨fun p => sign (holonomy (Rectangle.rightPlaquette p)), continuous_of_discreteTopology⟩

/-- Uniform reference law on one link. -/
def linkMeasure : Measure Gauge := StrongCouplingTransferGap.WilsonFinite.uniformReference Gauge

instance : IsProbabilityMeasure linkMeasure := by unfold linkMeasure; infer_instance

def boundaryMeasure : Measure Boundary := Measure.pi fun _ : Fin 6 => linkMeasure

instance : IsProbabilityMeasure boundaryMeasure := by unfold boundaryMeasure; infer_instance

theorem sum_gauge (f : Gauge → ℝ) : (∑ g, f g) = f 1 + f negative := by
  change (∑ g : Fin 2, f g) = _
  exact Fin.sum_univ_two _

theorem integral_link (f : Gauge → ℝ) :
    (∫ g, f g ∂linkMeasure) = (f 1 + f negative) / 2 := by
  rw [integral_fintype (.of_finite)]
  simp only [Measure.real, linkMeasure, StrongCouplingTransferGap.WilsonFinite.uniformReference,
    PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _), PMF.uniformOfFintype_apply,
    ENNReal.toReal_inv, ENNReal.toReal_natCast, smul_eq_mul, ← Finset.mul_sum]
  rw [sum_gauge]
  change (2 : ℝ)⁻¹ * (f 1 + f negative) = _
  ring

theorem integral_mul_right (f : Gauge → ℝ) (c : Gauge) :
    (∫ g, f (g * c) ∂linkMeasure) = ∫ g, f g ∂linkMeasure := by
  rcases eq_one_or_negative c with rfl | rfl <;> simp [integral_link, add_comm]

def path (u : Fin 3 → Gauge) : Gauge := u 0 * (u 1)⁻¹ * (u 2)⁻¹

/-- The product along three independent uniform links is uniform. -/
theorem integral_path (f : Gauge → ℝ) :
    (∫ u : Fin 3 → Gauge, f (path u) ∂Measure.pi (fun _ => linkMeasure)) =
      ∫ g, f g ∂linkMeasure := by
  rw [ProductMeasure.integral_cons linkMeasure _ continuous_of_discreteTopology]
  change (∫ x, ∫ u : Fin 2 → Gauge, f (x * (u 0)⁻¹ * (u 1)⁻¹)
    ∂Measure.pi (fun _ => linkMeasure) ∂linkMeasure) = _
  rw [integral_integral_swap (.of_finite)]
  simp_rw [mul_assoc, integral_mul_right]
  simp

def leftPath (b : Boundary) : Gauge := b 0 * (b 1)⁻¹ * (b 2)⁻¹

def rightPath (b : Boundary) : Gauge := b 3 * (b 4)⁻¹ * (b 5)⁻¹

/-- This is an exact integration identity for all six boundary links, not a
replacement of their law by an assumed smaller model. -/
theorem integral_paths (f : Gauge → Gauge → ℝ) :
    (∫ b, f (leftPath b) (rightPath b) ∂boundaryMeasure) =
      ∫ a, ∫ b, f a b ∂linkMeasure ∂linkMeasure := by
  unfold boundaryMeasure
  rw [ProductMeasure.integral_append linkMeasure 3 3 _ continuous_of_discreteTopology]
  change (∫ u : Fin 3 → Gauge, ∫ v : Fin 3 → Gauge, f (path u) (path v)
    ∂Measure.pi (fun _ => linkMeasure) ∂Measure.pi (fun _ => linkMeasure)) = _
  simp_rw [integral_path]
  exact integral_path (fun a => ∫ b, f a b ∂linkMeasure)

theorem integral_paths_seam (f : Gauge → Gauge → Gauge → ℝ) :
    (∫ p, f (leftPath p.1) (rightPath p.1) p.2 ∂boundaryMeasure.prod linkMeasure) =
      ∫ a, ∫ b, ∫ h, f a b h ∂linkMeasure ∂linkMeasure ∂linkMeasure := by
  rw [integral_prod _ (.of_finite)]
  exact integral_paths (fun a b => ∫ h, f a b h ∂linkMeasure)

theorem left_holonomy (p : Boundary × Gauge) :
    holonomy (Rectangle.leftPlaquette p) = leftPath p.1 * p.2 := by
  change p.1 0 * p.2 * (p.1 1)⁻¹ * (p.1 2)⁻¹ = (p.1 0 * (p.1 1)⁻¹ * (p.1 2)⁻¹) * p.2
  ac_rfl

theorem right_holonomy (p : Boundary × Gauge) :
    holonomy (Rectangle.rightPlaquette p) = rightPath p.1 * p.2 := by
  change p.1 3 * p.1 4 * (p.1 5)⁻¹ * p.2⁻¹ = (p.1 3 * (p.1 4)⁻¹ * (p.1 5)⁻¹) * p.2
  simp

theorem weight_apply (p : Boundary × Gauge) : weight p =
    singleWeight (leftPath p.1 * p.2) * singleWeight (rightPath p.1 * p.2) := by
  change singleWeight (holonomy (Rectangle.leftPlaquette p)) *
    singleWeight (holonomy (Rectangle.rightPlaquette p)) = _
  rw [left_holonomy, right_holonomy]

theorem leftSign_apply (p : Boundary × Gauge) : leftSign p = sign (leftPath p.1 * p.2) :=
  congrArg sign (left_holonomy p)

theorem rightSign_apply (p : Boundary × Gauge) : rightSign p = sign (rightPath p.1 * p.2) :=
  congrArg sign (right_holonomy p)

/-- One plaquette as a weighted kernel between its two boundary paths. -/
def plaquetteKernel : C(Gauge × Gauge, ℝ) :=
  ⟨fun p => singleWeight (p.1 * p.2), continuous_of_discreteTopology⟩

def plaquetteRoute : Mettapedia.GSLT.Ultrainfinite.Route (KernelRoute.Step (X := Gauge)) () () :=
  .cons plaquetteKernel (.refl ())

/-- The literal Wilson seam integration has the weighted GSLT route semantics. -/
theorem boundaryWeight_eq_route (b : Boundary) :
    marginal linkMeasure weight b =
      KernelRoute.action linkMeasure plaquetteRoute (plaquetteKernel.curry (rightPath b))
        (leftPath b) := by
  unfold plaquetteRoute
  rw [KernelRoute.action_singleton]
  change (∫ h, weight (b, h) ∂linkMeasure) = _
  simp only [weight_apply, plaquetteKernel, ContinuousMap.coe_mk, ContinuousMap.curry_apply]

theorem partition_value : (∫ p, weight p ∂boundaryMeasure.prod linkMeasure) = 25 / 64 := by
  simp_rw [weight_apply]
  rw [integral_paths_seam (fun a b h => singleWeight (a * h) * singleWeight (b * h))]
  norm_num [integral_link, singleWeight]

theorem left_numerator :
    (∫ p, weight p * leftSign p ∂boundaryMeasure.prod linkMeasure) = 15 / 64 := by
  simp_rw [weight_apply, leftSign_apply]
  rw [integral_paths_seam (fun a b h => singleWeight (a * h) * singleWeight (b * h) * sign (a * h))]
  norm_num [integral_link, singleWeight, sign]

theorem right_numerator :
    (∫ p, weight p * rightSign p ∂boundaryMeasure.prod linkMeasure) = 15 / 64 := by
  simp_rw [weight_apply, rightSign_apply]
  rw [integral_paths_seam (fun a b h => singleWeight (a * h) * singleWeight (b * h) * sign (b * h))]
  norm_num [integral_link, singleWeight, sign]

theorem joint_numerator :
    (∫ p, weight p * (leftSign p * rightSign p) ∂boundaryMeasure.prod linkMeasure) = 9 / 64 := by
  simp_rw [weight_apply, leftSign_apply, rightSign_apply]
  rw [integral_paths_seam (fun a b h =>
    singleWeight (a * h) * singleWeight (b * h) * (sign (a * h) * sign (b * h)))]
  norm_num [integral_link, singleWeight, sign]

theorem plaquette_covariance_zero :
    covariance (boundaryMeasure.prod linkMeasure) weight leftSign rightSign = 0 := by
  simp only [covariance, expectation, ContinuousMap.mul_apply]
  rw [partition_value, left_numerator, right_numerator, joint_numerator]
  norm_num

theorem projected_joint_numerator :
    (∫ b, marginal linkMeasure weight b *
      (project linkMeasure weight weight_pos leftSign b *
        project linkMeasure weight weight_pos rightSign b) ∂boundaryMeasure) = 225 / 1088 := by
  simp only [project, marginal, ProductMeasure.partialIntegral, ContinuousMap.coe_mk,
    ContinuousMap.mul_apply]
  simp_rw [weight_apply, leftSign_apply, rightSign_apply]
  rw [integral_paths (fun a b =>
    (∫ h, singleWeight (a * h) * singleWeight (b * h) ∂linkMeasure) *
      (((∫ h, singleWeight (a * h) * singleWeight (b * h) * sign (a * h) ∂linkMeasure) /
        (∫ h, singleWeight (a * h) * singleWeight (b * h) ∂linkMeasure)) *
       ((∫ h, singleWeight (a * h) * singleWeight (b * h) * sign (b * h) ∂linkMeasure) /
        (∫ h, singleWeight (a * h) * singleWeight (b * h) ∂linkMeasure))))]
  norm_num [integral_link, singleWeight, sign]

theorem projected_covariance_value :
    covariance boundaryMeasure (marginal linkMeasure weight)
      (project linkMeasure weight weight_pos leftSign)
      (project linkMeasure weight weight_pos rightSign) = 72 / 425 := by
  rw [covariance, expectation_project, expectation_project]
  simp only [expectation, ContinuousMap.mul_apply]
  rw [projected_joint_numerator, integral_marginal, partition_value,
    left_numerator, right_numerator]
  norm_num

theorem averaged_fiber_covariance_value :
    expectation boundaryMeasure (marginal linkMeasure weight)
      (fiberCovariance linkMeasure weight weight_pos leftSign rightSign) = -(72 / 425) := by
  have h := covariance_decomposition boundaryMeasure linkMeasure weight weight_pos leftSign rightSign
  rw [plaquette_covariance_zero, projected_covariance_value] at h
  linarith

/-- One-marked transport is exact for every observable, but transporting the
two marks separately changes their connected correlation. -/
theorem one_marked_exact_two_marked_fails :
    (∀ F : C(Boundary × Gauge, ℝ),
      expectation boundaryMeasure (marginal linkMeasure weight)
        (project linkMeasure weight weight_pos F) =
      expectation (boundaryMeasure.prod linkMeasure) weight F) ∧
    covariance (boundaryMeasure.prod linkMeasure) weight leftSign rightSign ≠
      covariance boundaryMeasure (marginal linkMeasure weight)
        (project linkMeasure weight weight_pos leftSign)
        (project linkMeasure weight weight_pos rightSign) := by
  refine ⟨expectation_project boundaryMeasure linkMeasure weight weight_pos, ?_⟩
  rw [plaquette_covariance_zero, projected_covariance_value]
  norm_num

/-- An arbitrary observation of one of the two exterior paths. -/
def onLeft (f : Gauge → ℝ) : C(Boundary, ℝ) :=
  ⟨fun b => f (leftPath b), continuous_of_discreteTopology⟩

def onRight (f : Gauge → ℝ) : C(Boundary, ℝ) :=
  ⟨fun b => f (rightPath b), continuous_of_discreteTopology⟩

/-- Each separate path marginal is still exactly uniform after seam elimination. -/
theorem left_path_marginal (f : Gauge → ℝ) :
    expectation boundaryMeasure (marginal linkMeasure weight) (onLeft f) =
      ∫ g, f g ∂linkMeasure := by
  rw [← expectation_boundary boundaryMeasure linkMeasure weight weight_pos]
  simp only [expectation, lift, onLeft, ContinuousMap.coe_mk, partition_value]
  simp_rw [weight_apply]
  rw [integral_paths_seam (fun a b h => singleWeight (a * h) * singleWeight (b * h) * f a)]
  norm_num [integral_link, singleWeight]
  ring

theorem right_path_marginal (f : Gauge → ℝ) :
    expectation boundaryMeasure (marginal linkMeasure weight) (onRight f) =
      ∫ g, f g ∂linkMeasure := by
  rw [← expectation_boundary boundaryMeasure linkMeasure weight weight_pos]
  simp only [expectation, lift, onRight, ContinuousMap.coe_mk, partition_value]
  simp_rw [weight_apply]
  rw [integral_paths_seam (fun a b h => singleWeight (a * h) * singleWeight (b * h) * f b)]
  norm_num [integral_link, singleWeight]
  ring

/-- Although both path marginals are uniform, their product (the exterior Wilson
loop character) has expectation `9/25`, not the product of the marginal means. -/
theorem boundary_path_correlation :
    covariance boundaryMeasure (marginal linkMeasure weight) (onLeft sign) (onRight sign) = 9 / 25 := by
  rw [covariance, left_path_marginal, right_path_marginal]
  rw [← expectation_boundary boundaryMeasure linkMeasure weight weight_pos]
  simp only [expectation, lift, onLeft, onRight, ContinuousMap.coe_mk,
    ContinuousMap.mul_apply, partition_value]
  simp_rw [weight_apply]
  rw [integral_paths_seam (fun a b h =>
    singleWeight (a * h) * singleWeight (b * h) * (sign a * sign b))]
  norm_num [integral_link, singleWeight, sign]

theorem product_path_correlation_zero :
    (∫ p : Gauge × Gauge, sign p.1 * sign p.2 ∂linkMeasure.prod linkMeasure) -
      (∫ g, sign g ∂linkMeasure) * (∫ g, sign g ∂linkMeasure) = 0 := by
  rw [integral_prod _ (.of_finite)]
  norm_num [integral_link, sign]

/-- The oriented product around the six outer links of the rectangle. -/
def outerHolonomy (b : Boundary) : Gauge :=
  b 0 * b 3 * b 4 * (b 5)⁻¹ * (b 1)⁻¹ * (b 2)⁻¹

theorem outerHolonomy_eq_paths (b : Boundary) : outerHolonomy b = leftPath b * rightPath b := by
  simp only [outerHolonomy, leftPath, rightPath, inv_eq_self]
  ac_rfl

def outerLoop : C(Boundary, ℝ) :=
  ⟨fun b => sign (outerHolonomy b), continuous_of_discreteTopology⟩

theorem outerLoop_eq : outerLoop = onLeft sign * onRight sign := by
  ext b
  exact (congrArg sign (outerHolonomy_eq_paths b)).trans (sign_mul _ _)

theorem outer_loop_expectation :
    expectation boundaryMeasure (marginal linkMeasure weight) outerLoop = 9 / 25 := by
  have h := boundary_path_correlation
  rw [covariance, left_path_marginal, right_path_marginal] at h
  norm_num [integral_link, sign] at h
  rw [outerLoop_eq]
  exact h

#print axioms boundaryWeight_eq_route
#print axioms weight_eq_wilson
#print axioms plaquette_covariance_zero
#print axioms projected_covariance_value
#print axioms averaged_fiber_covariance_value
#print axioms one_marked_exact_two_marked_fails
#print axioms left_path_marginal
#print axioms right_path_marginal
#print axioms boundary_path_correlation
#print axioms product_path_correlation_zero
#print axioms outer_loop_expectation

end Mettapedia.QuantumTheory.YangMills.WilsonRectangleElimination
