import Mettapedia.QuantumTheory.YangMills.InhomogeneousWilsonCrossing
import Mettapedia.QuantumTheory.YangMills.WilsonBoundaryResponse

/-!
# Exponential decay of a local mixed free-energy response

Inhomogeneous Wilson interactions, including arbitrary fixed link variables,
satisfy a volume-uniform response bound at the explicit strong-coupling
threshold. The response is the logarithm of the four actual partition
functions. The marked density changes have finite prescribed supports;
pointwise lower bounds account for their normalization costs.
-/
set_option autoImplicit false
noncomputable section
open Finset MeasureTheory
open scoped Topology
open Mettapedia.Combinatorics.PolymerGas

namespace Mettapedia.QuantumTheory.YangMills.WilsonLocalResponse
open StrongCouplingCrossing InhomogeneousWilsonCrossing
open WilsonBlockElimination WilsonBoundaryResponse

variable {E : Type*} [TopologicalSpace E] [CompactSpace E] [MeasurableSpace E]
  [BorelSpace E] [SecondCountableTopology E] {d : ℕ}

/-- The continuous real density underlying the complex polymer convention. -/
def realDensity (M : Model d E) (hφ : ∀ p, Continuous (M.φ p)) (β : ℝ) :
    C(Link d M.n → E, ℝ) :=
  ⟨fun ω => ∏ p, Real.exp (-β * potential (M.φ p) p ω), by
    apply continuous_finsetProd
    intro p _
    apply Continuous.rexp
    apply continuous_const.mul
    exact (hφ p).comp (continuous_pi (fun _ => continuous_apply _))⟩

omit [CompactSpace E] [BorelSpace E] [SecondCountableTopology E] in
theorem realDensity_pos (M : Model d E) (hφ : ∀ p, Continuous (M.φ p))
    (β : ℝ) (ω : Link d M.n → E) : 0 < realDensity M hφ β ω :=
  prod_pos (fun _ _ => Real.exp_pos _)

omit [CompactSpace E] [BorelSpace E] [SecondCountableTopology E] in
theorem density_ofReal (M : Model d E) (hφ : ∀ p, Continuous (M.φ p))
    (β : ℝ) (ω : Link d M.n → E) :
    InhomogeneousWilsonCrossing.density M β ω = (realDensity M hφ β ω : ℂ) := by
  simp [InhomogeneousWilsonCrossing.density, realDensity]

/-- Fixing coordinates preserves continuity, uniformly for arbitrary values. -/
theorem continuous_pinned (M : Model d E) (hφ : ∀ p, Continuous (M.φ p))
    (held : Finset (Link d M.n)) (value : Link d M.n → E) :
    ∀ p, Continuous ((M.pinned held value).φ p) := by
  classical
  intro p
  dsimp only [Model.pinned]
  apply (hφ p).comp
  apply continuous_pi
  intro i
  split_ifs
  · exact continuous_const
  · exact continuous_apply i

/-- A local continuous mark, viewed on the original full configuration. -/
def localObservable {n : ℕ} (S : Finset (Link d n)) (F : C(S → E, ℝ)) :
    C(Link d n → E, ℝ) :=
  ⟨fun ω => F (restrictTo S ω), F.continuous.comp (continuous_pi fun _ => continuous_apply _)⟩

omit [CompactSpace E] [BorelSpace E] [SecondCountableTopology E] in
theorem ofReal_expectation (ν₀ : Measure E) [IsProbabilityMeasure ν₀]
    (M : Model d E) (hφ : ∀ p, Continuous (M.φ p)) (β : ℝ)
    (F : C(Link d M.n → E, ℝ)) :
    InhomogeneousWilsonCrossing.wilsonExpectation ν₀ M β (fun ω => (F ω : ℂ)) =
      (WilsonBlockElimination.expectation (Measure.pi fun _ => ν₀) (realDensity M hφ β) F : ℂ) := by
  simp only [InhomogeneousWilsonCrossing.wilsonExpectation, density_ofReal M hφ,
    ← Complex.ofReal_mul, integral_complex_ofReal, ← Complex.ofReal_div,
    WilsonBlockElimination.expectation]
  congr 2
  congr 1
  funext ω
  exact mul_comm _ _

omit [CompactSpace E] in
/-- Real continuous covariance inherits the crossing estimate, with the decay
rate chosen uniformly over the entire family of boundary conditions. -/
theorem covariance_clustering (d : ℕ) (ν₀ : Measure E) [IsProbabilityMeasure ν₀]
    (base : E) {β : ℝ} (hβ : 0 ≤ β) (hβ0 : β ≤ beta0 d) :
    ∃ κ > 0, ∀ (M : Model d E) (hφ : ∀ p, Continuous (M.φ p))
      (S₁ S₂ : Finset (Link d M.n)), S₁.Nonempty →
      ∀ (F : C(S₁ → E, ℝ)) (G : C(S₂ → E, ℝ)) (C₁ C₂ : ℝ),
      (∀ v, |F v| ≤ C₁) → (∀ v, |G v| ≤ C₂) →
      |covariance (Measure.pi fun _ => ν₀) (realDensity M hφ β)
        (localObservable S₁ F) (localObservable S₂ G)| ≤
        3 * C₁ * C₂ * Real.exp (3 * S₁.card + 3 * S₂.card) *
          Real.exp (-κ * polymerDist S₁ S₂) := by
  obtain ⟨κ, hκ, hc⟩ := InhomogeneousWilsonCrossing.wilson_clustering d ν₀ base hβ hβ0
  refine ⟨κ, hκ, ?_⟩
  intro M hφ S₁ S₂ hS F G C₁ C₂ hF hG
  have h := hc M S₁ S₂ hS (fun v => (F v : ℂ)) (fun v => (G v : ℂ)) C₁ C₂
    (Complex.measurable_ofReal.comp F.continuous.measurable)
    (Complex.measurable_ofReal.comp G.continuous.measurable)
    (fun v => by simpa using hF v) (fun v => by simpa using hG v)
  change ‖InhomogeneousWilsonCrossing.wilsonExpectation ν₀ M β
      (fun ω => (localObservable S₁ F ω : ℂ) * (localObservable S₂ G ω : ℂ)) -
    InhomogeneousWilsonCrossing.wilsonExpectation ν₀ M β
      (fun ω => (localObservable S₁ F ω : ℂ)) *
    InhomogeneousWilsonCrossing.wilsonExpectation ν₀ M β
      (fun ω => (localObservable S₂ G ω : ℂ))‖ ≤ _ at h
  simp_rw [← Complex.ofReal_mul] at h
  have hFG := ofReal_expectation ν₀ M hφ β (localObservable S₁ F * localObservable S₂ G)
  simp only [ContinuousMap.mul_apply] at hFG
  rw [hFG,
    ofReal_expectation ν₀ M hφ β (localObservable S₁ F),
    ofReal_expectation ν₀ M hφ β (localObservable S₂ G)] at h
  simpa only [← Complex.ofReal_mul, ← Complex.ofReal_sub, Complex.norm_real,
    Real.norm_eq_abs, covariance] using h

/-- A genuine spatial estimate for the mixed logarithm of four partition
functions. The prefactor depends on the changed patches and their factor
bounds, but not on the surrounding volume or fixed boundary values. -/
theorem mixedResponse_clustering (d : ℕ) (ν₀ : Measure E) [IsProbabilityMeasure ν₀]
    (base : E) {β : ℝ} (hβ : 0 ≤ β) (hβ0 : β ≤ beta0 d) :
    ∃ κ > 0, ∀ (M : Model d E) (hφ : ∀ p, Continuous (M.φ p))
      (S₁ S₂ : Finset (Link d M.n)), S₁.Nonempty →
      ∀ (A : C(S₁ → E, ℝ)) (B : C(S₂ → E, ℝ)) (lA lB uA uB : ℝ),
      0 < lA → 0 < lB →
      (∀ v, lA ≤ A v) → (∀ v, A v ≤ uA) →
      (∀ v, lB ≤ B v) → (∀ v, B v ≤ uB) →
      |mixedResponse (Measure.pi fun _ => ν₀) (realDensity M hφ β)
        (localObservable S₁ A) (localObservable S₂ B)| ≤
        (3 * uA * uB * Real.exp (3 * S₁.card + 3 * S₂.card) *
          Real.exp (-κ * polymerDist S₁ S₂)) / (lA * lB) := by
  obtain ⟨κ, hκ, hc⟩ := covariance_clustering d ν₀ base hβ hβ0
  refine ⟨κ, hκ, ?_⟩
  intro M hφ S₁ S₂ hS A B lA lB uA uB hlA hlB hAl hAu hBl hBu
  apply abs_mixedResponse_le_of_covariance _ _ _ _ (realDensity_pos M hφ β) hlA hlB
    (fun ω => hAl _) (fun ω => hBl _)
  exact hc M hφ S₁ S₂ hS A B uA uB
    (fun v => by rw [abs_of_pos (hlA.trans_le (hAl v))]; exact hAu v)
    (fun v => by rw [abs_of_pos (hlB.trans_le (hBl v))]; exact hBu v)

#print axioms ofReal_expectation
#print axioms covariance_clustering
#print axioms mixedResponse_clustering

end Mettapedia.QuantumTheory.YangMills.WilsonLocalResponse
