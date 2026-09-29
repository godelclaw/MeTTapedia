import Mettapedia.QuantumTheory.YangMills.StrongCouplingCrossing

/-!
# Uniform strong-coupling bounds with fixed boundary data

The crossing expansion allows a different potential at every plaquette.
Its constants are uniform over the volume, all choices of potentials in
`[0,2]`, plaquette masks, and fixed link variables. Holding a link fixed is
implemented inside the local potential; its unused reference variable has
integral one. No boundary interaction is discarded.
-/

set_option autoImplicit false
noncomputable section
open Finset MeasureTheory
open Mettapedia.Combinatorics.PolymerGas

namespace Mettapedia.QuantumTheory.YangMills.InhomogeneousWilsonCrossing

open StrongCouplingCrossing

variable (d : ℕ) (E : Type*) [MeasurableSpace E]

/-- All inhomogeneous local models with the same dimension and potential bounds.
Indexing the crossing input by this entire type gives constants uniform in
boundary values as well as volume. -/
structure Model where
  n : ℕ
  φ : Plaquette d n → (Fin 4 → E) → ℝ
  measurable : ∀ p, Measurable (φ p)
  nonneg : ∀ p v, 0 ≤ φ p v
  le_two : ∀ p v, φ p v ≤ 2

variable {d E}

/-- The spatially homogeneous model is included without changing its density. -/
def homogeneous (n : ℕ) (φ : (Fin 4 → E) → ℝ) (hm : Measurable φ)
    (h0 : ∀ v, 0 ≤ φ v) (h2 : ∀ v, φ v ≤ 2) : Model d E :=
  ⟨n, fun _ => φ, fun _ => hm, fun _ => h0, fun _ => h2⟩

/-- Fix arbitrary link variables, including all shared separator links. -/
abbrev Model.pinned (M : Model d E) (held : Finset (Link d M.n))
    (value : Link d M.n → E) : Model d E where
  n := M.n
  φ p v := M.φ p (fun i => if linkAt p i ∈ held then value (linkAt p i) else v i)
  measurable p := (M.measurable p).comp (measurable_pi_lambda _ fun i => by
    by_cases h : linkAt p i ∈ held <;> simp only [h, ↓reduceIte]
    · exact measurable_const
    · exact measurable_pi_apply i)
  nonneg p v := M.nonneg p _
  le_two p v := M.le_two p _

/-- Select an arbitrary collection of plaquettes, for example an open box
embedded in a larger torus. The remaining factors are exactly one. -/
abbrev Model.masked (M : Model d E) (active : Finset (Plaquette d M.n)) : Model d E where
  n := M.n
  φ p v := if p ∈ active then M.φ p v else 0
  measurable p := by
    by_cases h : p ∈ active <;> simp only [h, ↓reduceIte]
    · exact M.measurable p
    · exact measurable_const
  nonneg p v := by split <;> simp_all [M.nonneg]
  le_two p v := by split <;> simp_all [M.le_two]

def factor (M : Model d E) (β : ℝ) (p : Plaquette d M.n)
    (ω : Link d M.n → E) : ℂ := perturbation (M.φ p) β p ω

def density (M : Model d E) (β : ℝ) (ω : Link d M.n → E) : ℂ :=
  ∏ p, (Real.exp (-β * potential (M.φ p) p ω) : ℂ)

def activity (base : E) (β : ℝ) (M : Model d E)
    (S : Finset (Link d M.n)) : (S → E) → ℂ :=
  plaquetteActivity support base (factor M β) S

theorem factor_local (M : Model d E) (β : ℝ) :
    PlaquetteLocal support (factor M β) := by
  intro p ω ω' h
  exact perturbation_local (M.φ p) β p ω ω' h

theorem measurable_factor (M : Model d E) (β : ℝ) (p : Plaquette d M.n) :
    Measurable (factor M β p) := measurable_perturbation (M.measurable p) β p

theorem norm_factor_le (M : Model d E) {β : ℝ} (hβ : 0 ≤ β)
    (p : Plaquette d M.n) (ω : Link d M.n → E) : ‖factor M β p ω‖ ≤ 2 * β :=
  norm_perturbation_le (M.nonneg p) (M.le_two p) hβ p ω

theorem density_eq_polymerDensity (M : Model d E) (base : E) (β : ℝ)
    (ω : Link d M.n → E) :
    density M β ω = polymerDensity (activity base β M) univ ω := by
  unfold activity
  convert prod_one_add_eq_polymerDensity support support_nonempty base
    (factor M β) (factor_local M β) ω using 1
  simp [density, factor, perturbation]

/-- One crossing input covers all volumes and all admissible local potentials,
including arbitrary pinning and masks, with the original explicit threshold. -/
theorem crossingInput (d : ℕ) (base : E) {β : ℝ} (hβ : 0 ≤ β)
    (hβ0 : β ≤ beta0 d) :
    CrossingInput.CrossingInput (fun M : Model d E => Link d M.n) E (activity base β) := by
  have : Nonempty E := ⟨base⟩
  refine ⟨fun M S => measurable_plaquetteActivity support base (factor M β)
    (measurable_factor M β) S, ?_⟩
  refine ⟨fun M => plaquetteMajorant (support (d := d) (n := M.n)) (2 * β),
    1, Real.exp (-1), by norm_num, (Real.exp_pos _).le, ?_, ?_, ?_, ?_⟩
  · rw [← Real.exp_add]
    norm_num
  · intro M S v
    exact norm_plaquetteActivity_le support base (factor M β) (norm_factor_le M hβ) S v
  · intro M
    exact plaquetteMajorant_empty support support_nonempty _
  · intro M
    apply activitySmall_plaquetteMajorant support
      (δ := 2 * β) (κ := 1) (r := 1) (ε := Real.exp (-1))
      (s := 4) (Δ := 16 * (d * d)) (D := 4 * (d * d))
      (by positivity) (by norm_num) (by norm_num) (Real.exp_pos _).le
    · rw [← Real.exp_add]
      norm_num
    · exact card_support_le
    · exact diam_support_le
    · intro p
      convert degree_plaquetteGraph_le d M.n p using 1
      congr 1
      exact Subsingleton.elim _ _
    · exact card_incident_le d M.n
    · unfold beta0 at hβ0
      linarith

def wilsonExpectation (ν₀ : Measure E) (M : Model d E) (β : ℝ)
    (F : (Link d M.n → E) → ℂ) : ℂ :=
  (∫ ω, F ω * density M β ω ∂Measure.pi (fun _ : Link d M.n => ν₀)) /
    (∫ ω, density M β ω ∂Measure.pi (fun _ : Link d M.n => ν₀))

theorem wilsonExpectation_eq_expectation (ν₀ : Measure E) [IsProbabilityMeasure ν₀]
    (M : Model d E) (base : E) {β : ℝ} (hβ : 0 ≤ β)
    (F : (Link d M.n → E) → ℂ) :
    wilsonExpectation ν₀ M β F = expectation ν₀ F (activity base β M) univ := by
  have : Nonempty E := ⟨base⟩
  unfold wilsonExpectation expectation
  simp_rw [density_eq_polymerDensity M base]
  rw [integral_polymerDensity ν₀ (activity base β M)
    (fun S => measurable_plaquetteActivity support base (factor M β)
      (measurable_factor M β) S)
    (plaquetteMajorant support (2 * β))
    (norm_plaquetteActivity_le support base (factor M β) (norm_factor_le M hβ))]

/-- The decay rate is chosen before the volume, potential, mask, and boundary
values. This quantifier order is essential for fixed-boundary estimates. -/
theorem wilson_clustering (d : ℕ) (ν₀ : Measure E) [IsProbabilityMeasure ν₀] (base : E)
    {β : ℝ} (hβ : 0 ≤ β) (hβ0 : β ≤ beta0 d) :
    ∃ κ > 0, ∀ (M : Model d E) (S₁ S₂ : Finset (Link d M.n)), S₁.Nonempty →
      ∀ (F₁ : (S₁ → E) → ℂ) (F₂ : (S₂ → E) → ℂ) (C₁ C₂ : ℝ),
      Measurable F₁ → Measurable F₂ → (∀ v, ‖F₁ v‖ ≤ C₁) → (∀ v, ‖F₂ v‖ ≤ C₂) →
      ‖wilsonExpectation ν₀ M β (fun ω => F₁ (restrictTo S₁ ω) * F₂ (restrictTo S₂ ω)) -
        wilsonExpectation ν₀ M β (fun ω => F₁ (restrictTo S₁ ω)) *
          wilsonExpectation ν₀ M β (fun ω => F₂ (restrictTo S₂ ω))‖ ≤
        3 * C₁ * C₂ * Real.exp (3 * S₁.card + 3 * S₂.card) *
          Real.exp (-κ * polymerDist S₁ S₂) := by
  have : Nonempty E := ⟨base⟩
  obtain ⟨κ, hκ, hc⟩ := CrossingInput.clustering (ν₀ := ν₀)
    (crossingInput d base hβ hβ0)
  refine ⟨κ, hκ, ?_⟩
  intro M S₁ S₂ hS₁ F₁ F₂ C₁ C₂ hF₁ hF₂ hb₁ hb₂
  simp_rw [wilsonExpectation_eq_expectation ν₀ M base hβ]
  exact hc M univ S₁ S₂ hS₁ F₁ F₂ C₁ C₂ hF₁ hF₂ hb₁ hb₂

#print axioms density_eq_polymerDensity
#print axioms crossingInput
#print axioms wilson_clustering

end Mettapedia.QuantumTheory.YangMills.InhomogeneousWilsonCrossing
