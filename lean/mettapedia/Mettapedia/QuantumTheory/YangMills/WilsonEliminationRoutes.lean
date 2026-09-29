import Mettapedia.QuantumTheory.YangMills.WilsonSeparator

/-!
# Compositional weighted elimination with marked observables

A state carries its actual positive density and reference probability law.
An admissible elimination is a linear conditional-expectation operator that
preserves normalized expectation and contracts uniform bounds. The existing
GSLT route syntax composes these operators. Its two-observable defect is kept
as a function on the final boundary, with an exact concatenation law.

Retaining a coordinate is deterministic and need not have a continuous kernel
with respect to product Haar measure. The operator semantics therefore does
not impose such a kernel on exact boundary elimination.
-/
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped Topology

namespace Mettapedia.QuantumTheory.YangMills.WilsonEliminationRoutes
open WilsonBlockElimination WilsonSeparator CompactTransferGap
open Mettapedia.GSLT.Ultrainfinite

/-- A concrete weighted configuration space. -/
structure State where
  X : Type
  topology : TopologicalSpace X
  compact : CompactSpace X
  measurable : MeasurableSpace X
  borel : BorelSpace X
  μ : Measure X
  probability : IsProbabilityMeasure μ
  W : C(X, ℝ)
  positive : ∀ x, 0 < W x

attribute [instance] State.topology State.compact State.measurable State.borel State.probability

/-- The density is part of the state; expectation preservation is a proved
admissibility condition on the map between its observables. -/
structure Step (a b : State) where
  project : C(a.X, ℝ) →ₗ[ℝ] C(b.X, ℝ)
  expectation : ∀ F, expectation b.μ b.W (project F) = expectation a.μ a.W F
  contract : ∀ F C, (∀ x, |F x| ≤ C) → ∀ y, |project F y| ≤ C

/-- Forward transport of marks along the existing finite GSLT routes. -/
def action {a b : State} : Route Step a b → C(a.X, ℝ) →ₗ[ℝ] C(b.X, ℝ)
  | .refl _ => LinearMap.id
  | .cons e r => (action r).comp e.project

@[simp] theorem action_refl (a : State) (F : C(a.X, ℝ)) : action (.refl a) F = F := rfl

@[simp] theorem action_cons {a b c : State} (e : Step a b) (r : Route Step b c)
    (F : C(a.X, ℝ)) : action (.cons e r) F = action r (e.project F) := rfl

theorem action_append {a b c : State} (r : Route Step a b) (s : Route Step b c)
    (F : C(a.X, ℝ)) : action (r.append s) F = action s (action r F) := by
  induction r with
  | refl => rfl
  | cons e r ih => exact ih s (e.project F)

/-- Every finite chain preserves the original weighted expectation. -/
theorem expectation_action {a b : State} (r : Route Step a b) (F : C(a.X, ℝ)) :
    expectation b.μ b.W (action r F) = expectation a.μ a.W F := by
  induction r with
  | refl => rfl
  | cons e r ih => rw [action_cons, ih, e.expectation]

/-- Every finite chain preserves the original uniform observable bound. -/
theorem action_contract {a b : State} (r : Route Step a b)
    (F : C(a.X, ℝ)) (C : ℝ) (hF : ∀ x, |F x| ≤ C) :
    ∀ y, |action r F y| ≤ C := by
  induction r with
  | refl => exact hF
  | cons e r ih => exact ih _ (e.contract F C hF)

/-- The full transported covariance remainder, still an observable. -/
def remainder {a b : State} (r : Route Step a b) (F G : C(a.X, ℝ)) : C(b.X, ℝ) :=
  action r (F * G) - action r F * action r G

@[simp] theorem remainder_refl (a : State) (F G : C(a.X, ℝ)) :
    remainder (.refl a) F G = 0 := by simp [remainder]

/-- Earlier remainders are transported through later eliminations and added
to the later remainder. Neither term is dropped. -/
theorem remainder_append {a b c : State} (r : Route Step a b) (s : Route Step b c)
    (F G : C(a.X, ℝ)) :
    remainder (r.append s) F G =
      action s (remainder r F G) + remainder s (action r F) (action r G) := by
  simp only [remainder, action_append, map_sub]
  abel

/-- Exact finite-chain two-observable transport against the actual densities. -/
theorem covariance_action {a b : State} (r : Route Step a b) (F G : C(a.X, ℝ)) :
    covariance a.μ a.W F G =
      covariance b.μ b.W (action r F) (action r G) +
        expectation b.μ b.W (remainder r F G) := by
  rw [remainder, expectation_sub]
  simp only [covariance, expectation_action]
  ring

/-- Any pointwise estimate on the retained remainder gives the precise
correlation error for the whole chain. -/
theorem covariance_action_error {a b : State} (r : Route Step a b)
    (F G : C(a.X, ℝ)) {ε : ℝ} (h : ∀ y, |remainder r F G y| ≤ ε) :
    |covariance a.μ a.W F G - covariance b.μ b.W (action r F) (action r G)| ≤ ε := by
  rw [covariance_action, add_sub_cancel_left]
  exact abs_expectation_le b.μ b.W _ b.positive h

/-- Bounds for two consecutive route remainders add, because subsequent
conditional expectations contract the first remainder. -/
theorem remainder_append_bound {a b c : State} (r : Route Step a b) (s : Route Step b c)
    (F G : C(a.X, ℝ)) {ε₁ ε₂ : ℝ}
    (h₁ : ∀ y, |remainder r F G y| ≤ ε₁)
    (h₂ : ∀ z, |remainder s (action r F) (action r G) z| ≤ ε₂) :
    ∀ z, |remainder (r.append s) F G z| ≤ ε₁ + ε₂ := by
  intro z
  rw [remainder_append]
  exact (abs_add_le _ _).trans (add_le_add (action_contract s _ ε₁ h₁ z) (h₂ z))

section Concrete
variable {B I : Type} [TopologicalSpace B] [CompactSpace B]
  [MeasurableSpace B] [BorelSpace B] [SecondCountableTopology B]
  [TopologicalSpace I] [CompactSpace I] [MeasurableSpace I]
  [BorelSpace I] [SecondCountableTopology I]
  (μ : Measure B) (ν : Measure I) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
  (W : C(B × I, ℝ)) (hW : ∀ p, 0 < W p)

/-- Actual integration over the interior, as a linear map on marks. -/
def projectLinear : C(B × I, ℝ) →ₗ[ℝ] C(B, ℝ) where
  toFun := project ν W hW
  map_add' F G := by
    ext b
    exact expectation_add ν (W.curry b) (F.curry b) (G.curry b)
  map_smul' c F := by
    ext b
    exact expectation_const_mul ν (W.curry b) (F.curry b) c

def source : State :=
  ⟨B × I, inferInstance, inferInstance, inferInstance, inferInstance,
    μ.prod ν, inferInstance, W, hW⟩

def target : State :=
  ⟨B, inferInstance, inferInstance, inferInstance, inferInstance,
    μ, inferInstance, marginal ν W, marginal_pos ν W hW⟩

/-- The admissibility obligations are discharged for the original weighted
Haar/product integral, rather than postulated for an abstract RG map. -/
def elimination : Step (source μ ν W hW) (target μ ν W hW) where
  project := projectLinear ν W hW
  expectation := expectation_project μ ν W hW
  contract := fun F _ hF => abs_project_le ν W hW F hF

theorem elimination_remainder (F G : C(B × I, ℝ)) :
    remainder (.cons (elimination μ ν W hW) (.refl _)) F G =
      fiberCovariance ν W hW F G := rfl

end Concrete

#print axioms expectation_action
#print axioms remainder_append
#print axioms covariance_action
#print axioms remainder_append_bound
#print axioms elimination

end Mettapedia.QuantumTheory.YangMills.WilsonEliminationRoutes
