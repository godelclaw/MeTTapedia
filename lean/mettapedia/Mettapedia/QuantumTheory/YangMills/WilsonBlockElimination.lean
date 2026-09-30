import Mettapedia.QuantumTheory.YangMills.CompactTransferGap
import Mettapedia.GSLT.Core.Ultrainfinite

/-!
# Exact weighted block elimination

Integrating the interior of a block preserves its boundary expectations. For
two observables the exact transport law contains the averaged conditional
covariance. All weights and observables here are continuous on compact spaces;
the weight is strictly positive. In particular all displayed integrals are
integrable and every normalization denominator is positive.

The conditional covariance is kept as a continuous boundary observable, so its
contribution can be transported through further eliminations. A quantitative
bound on this contribution gives a bound on the error in transporting the
correlation by the two separately projected observables.

`KernelRoute.action` gives continuous-kernel integral semantics to the existing
GSLT route type. Concatenation composes the weighted operators. The concrete
Wilson consumer is a rectangle of two plaquettes sharing a seam link.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory
open scoped Topology

namespace Mettapedia.QuantumTheory.YangMills.WilsonBlockElimination

open CompactTransferGap

section Weighted

variable {X : Type*} [TopologicalSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X]
  (μ : Measure X) [IsProbabilityMeasure μ]

/-- Normalized expectation under a continuous density. -/
def expectation (W F : C(X, ℝ)) : ℝ :=
  (∫ x, W x * F x ∂μ) / ∫ x, W x ∂μ

/-- Connected two-point function under the same density. -/
def covariance (W F G : C(X, ℝ)) : ℝ :=
  expectation μ W (F * G) - expectation μ W F * expectation μ W G

@[simp] theorem expectation_zero (W : C(X, ℝ)) : expectation μ W 0 = 0 := by
  simp [expectation]

theorem partition_pos (W : C(X, ℝ)) (hW : ∀ x, 0 < W x) :
    0 < ∫ x, W x ∂μ := by
  rw [integral_pos_iff_support_of_nonneg (fun x => (hW x).le)
    (IntegralKernel.integrable_continuous_fun μ W.continuous)]
  have hs : Function.support W = Set.univ := by
    ext x
    simp only [Function.mem_support, ne_eq, (hW x).ne', not_false_eq_true, Set.mem_univ]
  simp [hs]

theorem expectation_sub (W F G : C(X, ℝ)) :
    expectation μ W (F - G) = expectation μ W F - expectation μ W G := by
  simp only [expectation, ContinuousMap.sub_apply, mul_sub]
  rw [integral_sub (IntegralKernel.integrable_continuous_fun μ (by fun_prop))
    (IntegralKernel.integrable_continuous_fun μ (by fun_prop)), sub_div]

theorem expectation_add (W F G : C(X, ℝ)) :
    expectation μ W (F + G) = expectation μ W F + expectation μ W G := by
  simp only [expectation, ContinuousMap.add_apply, mul_add]
  rw [integral_add (IntegralKernel.integrable_continuous_fun μ (by fun_prop))
    (IntegralKernel.integrable_continuous_fun μ (by fun_prop)), add_div]

theorem expectation_one (W : C(X, ℝ)) (hW : ∀ x, 0 < W x) :
    expectation μ W 1 = 1 := by
  simp only [expectation, ContinuousMap.one_apply, mul_one]
  exact div_self (partition_pos μ W hW).ne'

/-- A uniform observable bound survives normalization by a positive weight. -/
theorem abs_expectation_le (W F : C(X, ℝ)) (hW : ∀ x, 0 < W x)
    {C : ℝ} (hF : ∀ x, |F x| ≤ C) : |expectation μ W F| ≤ C := by
  have hZ := partition_pos μ W hW
  rw [expectation, abs_div, abs_of_pos hZ, div_le_iff₀ hZ]
  calc
    |∫ x, W x * F x ∂μ| ≤ ∫ x, |W x * F x| ∂μ := by
      simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm (fun x => W x * F x)
    _ = ∫ x, W x * |F x| ∂μ := by
      congr 1
      funext x
      rw [abs_mul, abs_of_pos (hW x)]
    _ ≤ ∫ x, W x * C ∂μ := integral_mono
      (IntegralKernel.integrable_continuous_fun μ (by fun_prop))
      (IntegralKernel.integrable_continuous_fun μ (by fun_prop))
      (fun x => mul_le_mul_of_nonneg_left (hF x) (hW x).le)
    _ = C * ∫ x, W x ∂μ := by rw [integral_mul_const, mul_comm]

end Weighted

section Elimination

variable {B I : Type*} [TopologicalSpace B] [CompactSpace B]
  [MeasurableSpace B] [BorelSpace B] [SecondCountableTopology B]
  [TopologicalSpace I] [CompactSpace I] [MeasurableSpace I]
  [BorelSpace I] [SecondCountableTopology I]
  (μ : Measure B) (ν : Measure I) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]

/-- Exact boundary weight after integrating all interior variables. -/
def marginal (W : C(B × I, ℝ)) : C(B, ℝ) := ProductMeasure.partialIntegral ν W

omit [MeasurableSpace B] [BorelSpace B] [SecondCountableTopology I] in
theorem marginal_pos (W : C(B × I, ℝ)) (hW : ∀ p, 0 < W p) (b : B) :
    0 < marginal ν W b :=
  partition_pos ν (W.curry b) (fun i => hW (b, i))

/-- Conditional expectation of an observable at fixed boundary data. -/
def project (W : C(B × I, ℝ)) (hW : ∀ p, 0 < W p) (F : C(B × I, ℝ)) : C(B, ℝ) :=
  ⟨fun b => marginal ν (W * F) b / marginal ν W b,
    (marginal ν (W * F)).continuous.div (marginal ν W).continuous
      (fun b => (marginal_pos ν W hW b).ne')⟩

/-- View a boundary observable as an observable of the full block. -/
def lift (F : C(B, ℝ)) : C(B × I, ℝ) := ⟨fun p => F p.1, by fun_prop⟩

/-- The connected correlation left inside the eliminated fiber. -/
def fiberCovariance (W : C(B × I, ℝ)) (hW : ∀ p, 0 < W p)
    (F G : C(B × I, ℝ)) : C(B, ℝ) :=
  project ν W hW (F * G) - project ν W hW F * project ν W hW G

omit [MeasurableSpace B] [BorelSpace B] [SecondCountableTopology I] in
/-- A projected observable is the normalized expectation in its actual fiber. -/
theorem project_apply (W : C(B × I, ℝ)) (hW : ∀ p, 0 < W p)
    (F : C(B × I, ℝ)) (b : B) :
    project ν W hW F b = expectation ν (W.curry b) (F.curry b) := rfl

omit [MeasurableSpace B] [BorelSpace B] [SecondCountableTopology I] in
theorem abs_project_le (W : C(B × I, ℝ)) (hW : ∀ p, 0 < W p)
    (F : C(B × I, ℝ)) {C : ℝ} (hF : ∀ p, |F p| ≤ C) (b : B) :
    |project ν W hW F b| ≤ C := by
  rw [project_apply]
  exact abs_expectation_le ν (W.curry b) (F.curry b)
    (fun i => hW (b, i)) (fun i => hF (b, i))

theorem integral_marginal (W : C(B × I, ℝ)) :
    (∫ b, marginal ν W b ∂μ) = ∫ p, W p ∂μ.prod ν :=
  (integral_prod _ (IntegralKernel.integrable_continuous_fun (μ.prod ν) W.continuous)).symm

/-- Exact one-observable transport. -/
theorem expectation_project (W : C(B × I, ℝ)) (hW : ∀ p, 0 < W p)
    (F : C(B × I, ℝ)) :
    expectation μ (marginal ν W) (project ν W hW F) = expectation (μ.prod ν) W F := by
  unfold expectation
  rw [integral_marginal]
  have hn : (∫ b, marginal ν W b * project ν W hW F b ∂μ) =
      ∫ b, marginal ν (W * F) b ∂μ := by
    apply integral_congr_ae
    exact ae_of_all μ (fun b => by
      change marginal ν W b * (marginal ν (W * F) b / marginal ν W b) = _
      field_simp [(marginal_pos ν W hW b).ne'])
  rw [hn, integral_marginal]
  rfl

omit [MeasurableSpace B] [BorelSpace B] [SecondCountableTopology I] in
theorem project_lift (W : C(B × I, ℝ)) (hW : ∀ p, 0 < W p) (F : C(B, ℝ)) :
    project ν W hW (lift F) = F := by
  ext b
  change (∫ i, W (b, i) * F b ∂ν) / (∫ i, W (b, i) ∂ν) = F b
  rw [integral_mul_const]
  exact mul_div_cancel_left₀ _ (marginal_pos ν W hW b).ne'

/-- The boundary marginal reproduces every continuous boundary expectation. -/
theorem expectation_boundary (W : C(B × I, ℝ)) (hW : ∀ p, 0 < W p) (F : C(B, ℝ)) :
    expectation (μ.prod ν) W (lift F) = expectation μ (marginal ν W) F := by
  rw [← expectation_project μ ν W hW, project_lift]

/-- Exact two-observable transport: the conditional covariance cannot be dropped. -/
theorem covariance_decomposition (W : C(B × I, ℝ)) (hW : ∀ p, 0 < W p)
    (F G : C(B × I, ℝ)) :
    covariance (μ.prod ν) W F G =
      covariance μ (marginal ν W) (project ν W hW F) (project ν W hW G) +
        expectation μ (marginal ν W) (fiberCovariance ν W hW F G) := by
  rw [fiberCovariance, expectation_sub]
  simp only [covariance, expectation_project]
  ring

/-- A bound on the actual fiber covariance controls the correlation-transport error. -/
theorem covariance_transport_error_le (W : C(B × I, ℝ)) (hW : ∀ p, 0 < W p)
    (F G : C(B × I, ℝ)) {ε : ℝ}
    (hε : ∀ b, |fiberCovariance ν W hW F G b| ≤ ε) :
    |covariance (μ.prod ν) W F G -
      covariance μ (marginal ν W) (project ν W hW F) (project ν W hW G)| ≤ ε := by
  rw [covariance_decomposition μ ν W hW, add_sub_cancel_left]
  exact abs_expectation_le μ _ _ (marginal_pos ν W hW) hε

omit [MeasurableSpace B] [BorelSpace B] [SecondCountableTopology I] in
/-- A surrounding boundary weight passes through exact interior integration. -/
theorem marginal_mul_lift (W : C(B × I, ℝ)) (H : C(B, ℝ)) :
    marginal ν (W * lift H) = marginal ν W * H := by
  ext b
  exact integral_mul_const (H b) (fun i => W (b, i))

/-- The replacement by the boundary weight is valid in every positive exterior
context, with the normalization belonging to that same context. -/
theorem expectation_boundary_context (W : C(B × I, ℝ)) (hW : ∀ p, 0 < W p)
    (H F : C(B, ℝ)) (hH : ∀ b, 0 < H b) :
    expectation (μ.prod ν) (W * lift H) (lift F) =
      expectation μ (marginal ν W * H) F := by
  rw [expectation_boundary μ ν _ (fun p => mul_pos (hW p) (hH p.1)), marginal_mul_lift]

end Elimination

section Composition

variable {B I J : Type*}
  [TopologicalSpace B] [CompactSpace B] [MeasurableSpace B] [BorelSpace B]
  [SecondCountableTopology B]
  [TopologicalSpace I] [CompactSpace I] [MeasurableSpace I] [BorelSpace I]
  [SecondCountableTopology I]
  [TopologicalSpace J] [CompactSpace J] [MeasurableSpace J] [BorelSpace J]
  [SecondCountableTopology J]
  (μ : Measure B) (ν : Measure I) (ρ : Measure J)
  [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] [IsProbabilityMeasure ρ]

/-- Both inner variables are eliminated together, with the same configuration
as in staged elimination. -/
def reassociate (F : C((B × I) × J, ℝ)) : C(B × (I × J), ℝ) :=
  ⟨fun p => F ((p.1, p.2.1), p.2.2), by fun_prop⟩

omit [MeasurableSpace B] [BorelSpace B] in
/-- Weighted gluing is associative: no intermediate boundary variable is reset. -/
theorem marginal_staged (W : C((B × I) × J, ℝ)) :
    marginal ν (marginal ρ W) = marginal (ν.prod ρ) (reassociate W) := by
  ext b
  exact (integral_prod _ (IntegralKernel.integrable_continuous_fun (ν.prod ρ)
    (show Continuous (fun p : I × J => W ((b, p.1), p.2)) by fun_prop))).symm

/-- The first conditional-covariance remainder is itself transported through
the next block elimination. The second remainder is added, not substituted. -/
theorem covariance_two_stage (W : C((B × I) × J, ℝ)) (hW : ∀ p, 0 < W p)
    (F G : C((B × I) × J, ℝ)) :
    covariance ((μ.prod ν).prod ρ) W F G =
      covariance μ (marginal ν (marginal ρ W))
        (project ν (marginal ρ W) (marginal_pos ρ W hW) (project ρ W hW F))
        (project ν (marginal ρ W) (marginal_pos ρ W hW) (project ρ W hW G)) +
      expectation μ (marginal ν (marginal ρ W))
        (fiberCovariance ν (marginal ρ W) (marginal_pos ρ W hW)
            (project ρ W hW F) (project ρ W hW G) +
          project ν (marginal ρ W) (marginal_pos ρ W hW) (fiberCovariance ρ W hW F G)) := by
  rw [expectation_add, expectation_project,
    covariance_decomposition (μ.prod ν) ρ W hW,
    covariance_decomposition μ ν (marginal ρ W) (marginal_pos ρ W hW)]
  ring

/-- Two stages consume the sum of their actual conditional-covariance bounds. -/
theorem covariance_two_stage_error_le (W : C((B × I) × J, ℝ)) (hW : ∀ p, 0 < W p)
    (F G : C((B × I) × J, ℝ)) {ε₁ ε₂ : ℝ}
    (h₁ : ∀ bi, |fiberCovariance ρ W hW F G bi| ≤ ε₁)
    (h₂ : ∀ b, |fiberCovariance ν (marginal ρ W) (marginal_pos ρ W hW)
      (project ρ W hW F) (project ρ W hW G) b| ≤ ε₂) :
    |covariance ((μ.prod ν).prod ρ) W F G -
      covariance μ (marginal ν (marginal ρ W))
        (project ν (marginal ρ W) (marginal_pos ρ W hW) (project ρ W hW F))
        (project ν (marginal ρ W) (marginal_pos ρ W hW) (project ρ W hW G))| ≤ ε₁ + ε₂ := by
  rw [covariance_two_stage μ ν ρ W hW, add_sub_cancel_left]
  apply abs_expectation_le μ _ _ (marginal_pos ν _ (marginal_pos ρ W hW))
  intro b
  exact (abs_add_le _ _).trans (by
    have hp := abs_project_le ν (marginal ρ W) (marginal_pos ρ W hW)
      (fiberCovariance ρ W hW F G) h₁ b
    have hq := h₂ b
    change |fiberCovariance ν (marginal ρ W) (marginal_pos ρ W hW)
      (project ρ W hW F) (project ρ W hW G) b| +
      |project ν (marginal ρ W) (marginal_pos ρ W hW) (fiberCovariance ρ W hW F G) b| ≤ _
    linarith)

end Composition

namespace KernelRoute

open Mettapedia.GSLT.Ultrainfinite

variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [MeasurableSpace X]
  [BorelSpace X]
  (μ : Measure X) [IsProbabilityMeasure μ]

/-- A weighted step carries the complete continuous kernel at its two ends. -/
abbrev Step (_ _ : Unit) := C(X × X, ℝ)

/-- Numerical semantics for the existing GSLT route type. Each intermediate
state is integrated with its weight; mere existence of a state does not suffice. -/
def action {a b : Unit} : Route (Step (X := X)) a b → C(X, ℝ) → C(X, ℝ)
  | .refl _, F => F
  | .cons K rest, F => IntegralKernel.continuousOperator μ K (action rest F)

/-- GSLT route concatenation is interpreted by composition of weighted integral
operators, including every intermediate integration. -/
theorem action_append {a b c : Unit} (r : Route (Step (X := X)) a b)
    (s : Route (Step (X := X)) b c) (F : C(X, ℝ)) :
    action μ (r.append s) F = action μ r (action μ s F) := by
  induction r with
  | refl => rfl
  | cons K rest ih =>
    change IntegralKernel.continuousOperator μ K (action μ (rest.append s) F) = _
    rw [ih]
    rfl

theorem action_singleton (K : C(X × X, ℝ)) (F : C(X, ℝ)) (x : X) :
    action μ (a := ()) (.cons K (.refl ())) F x = ∫ y, K (x, y) * F y ∂μ :=
  IntegralKernel.continuousOperator_apply μ K F x

end KernelRoute

namespace Rectangle

open StrongCouplingTwist (holonomy)

variable {E : Type*} [Group E] [TopologicalSpace E] [IsTopologicalGroup E]
  [CompactSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

/-- Six outer links of a two-plaquette rectangle. The remaining link is the
vertical seam: it appears positively in the left plaquette and negatively in
the right plaquette. With horizontal links oriented right and vertical links
oriented up, the lower outer links are `0, 3`, the upper outer links `1, 5`,
and the left and right vertical outer links are `2, 4`. -/
abbrev Boundary (E : Type*) := Fin 6 → E

def leftPlaquette (p : Boundary E × E) : Fin 4 → E := ![p.1 0, p.2, p.1 1, p.1 2]

def rightPlaquette (p : Boundary E × E) : Fin 4 → E := ![p.1 3, p.1 4, p.1 5, p.2]

/-- The genuine Wilson density of the two oriented plaquettes. -/
def density (ψ : E → ℝ) (hψ : Continuous ψ) (β : ℝ) : C(Boundary E × E, ℝ) :=
  ⟨fun p => Real.exp (-β * ψ (holonomy (leftPlaquette p))) *
      Real.exp (-β * ψ (holonomy (rightPlaquette p))), by
    change Continuous (fun p : Boundary E × E =>
      Real.exp (-β * ψ (p.1 0 * p.2 * (p.1 1)⁻¹ * (p.1 2)⁻¹)) *
      Real.exp (-β * ψ (p.1 3 * p.1 4 * (p.1 5)⁻¹ * p.2⁻¹)))
    fun_prop⟩

omit [CompactSpace E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] in
theorem density_pos (ψ : E → ℝ) (hψ : Continuous ψ) (β : ℝ) (p : Boundary E × E) :
    0 < density ψ hψ β p := mul_pos (Real.exp_pos _) (Real.exp_pos _)

variable (ν₀ : Measure E) [IsProbabilityMeasure ν₀]

/-- Boundary expectation preservation for the two-plaquette Wilson complex,
with arbitrary continuous exterior boundary weight. -/
theorem boundary_expectation (ψ : E → ℝ) (hψ : Continuous ψ) (β : ℝ)
    (H F : C(Boundary E, ℝ)) (hH : ∀ b, 0 < H b) :
    expectation ((Measure.pi fun _ : Fin 6 => ν₀).prod ν₀)
      (density ψ hψ β * lift H) (lift F) =
      expectation (Measure.pi fun _ : Fin 6 => ν₀) (marginal ν₀ (density ψ hψ β) * H) F :=
  expectation_boundary_context _ _ _ (density_pos ψ hψ β) H F hH

/-- Correlation transport on the same Wilson complex and the same product law. -/
theorem correlation (ψ : E → ℝ) (hψ : Continuous ψ) (β : ℝ)
    (F G : C(Boundary E × E, ℝ)) :
    covariance ((Measure.pi fun _ : Fin 6 => ν₀).prod ν₀) (density ψ hψ β) F G =
      covariance (Measure.pi fun _ : Fin 6 => ν₀) (marginal ν₀ (density ψ hψ β))
        (project ν₀ _ (density_pos ψ hψ β) F) (project ν₀ _ (density_pos ψ hψ β) G) +
      expectation (Measure.pi fun _ : Fin 6 => ν₀) (marginal ν₀ (density ψ hψ β))
        (fiberCovariance ν₀ _ (density_pos ψ hψ β) F G) :=
  covariance_decomposition _ _ _ (density_pos ψ hψ β) F G

end Rectangle

#print axioms expectation_project
#print axioms expectation_boundary_context
#print axioms marginal_staged
#print axioms covariance_decomposition
#print axioms covariance_transport_error_le
#print axioms covariance_two_stage
#print axioms covariance_two_stage_error_le
#print axioms KernelRoute.action_append
#print axioms Rectangle.boundary_expectation
#print axioms Rectangle.correlation

end Mettapedia.QuantumTheory.YangMills.WilsonBlockElimination
