import Mettapedia.QuantumTheory.YangMills.InhomogeneousWilsonCrossing
import Mettapedia.QuantumTheory.YangMills.WilsonBoundaryResponse
import Mettapedia.QuantumTheory.YangMills.WilsonPatchGeometry

/-!
# Exponential decay of a local mixed free-energy response

Inhomogeneous Wilson interactions, including arbitrary fixed link variables,
satisfy a volume-uniform response bound at the explicit strong-coupling
threshold. The response is the logarithm of the four actual partition
functions. The marked density changes have finite prescribed supports;
pointwise lower bounds account for their normalization costs.

Three bounded collar-local marks have exponential tree decay, derived from
the three singleton-versus-pair covariance cuts. The resulting second/third
weighted budgets are uniform over all models and fixed boundary values.
-/
set_option autoImplicit false
noncomputable section
open Finset MeasureTheory
open scoped Topology
open Mettapedia.Combinatorics.PolymerGas

namespace Mettapedia.QuantumTheory.YangMills.WilsonLocalResponse
open StrongCouplingCrossing InhomogeneousWilsonCrossing
open WilsonBlockElimination WilsonBoundaryResponse

/-- Coordinate dependence of a real observable. -/
def DependsOn {X E : Type*} (S : Finset X) (F : (X → E) → ℝ) : Prop :=
  ∀ ω ω', (∀ x ∈ S, ω x = ω' x) → F ω = F ω'

/-- Dependence only on coordinates outside the specified set. -/
def DependsOff {X E : Type*} (S : Finset X) (F : (X → E) → ℝ) : Prop :=
  ∀ ω ω', (∀ x, x ∉ S → ω x = ω' x) → F ω = F ω'

theorem DependsOn.mono {X E : Type*} {S T : Finset X} {F : (X → E) → ℝ}
    (hF : DependsOn S F) (hST : S ⊆ T) : DependsOn T F :=
  fun ω ω' h ↦ hF ω ω' (fun x hx ↦ h x (hST hx))

theorem DependsOn.mul {X E : Type*} {S : Finset X} {F G : (X → E) → ℝ}
    (hF : DependsOn S F) (hG : DependsOn S G) : DependsOn S (fun ω ↦ F ω * G ω) := by
  intro ω ω' h
  change F ω * G ω = F ω' * G ω'
  rw [hF ω ω' h, hG ω ω' h]

theorem DependsOn.sub {X E : Type*} {S : Finset X} {F G : (X → E) → ℝ}
    (hF : DependsOn S F) (hG : DependsOn S G) : DependsOn S (fun ω ↦ F ω - G ω) := by
  intro ω ω' h
  change F ω - G ω = F ω' - G ω'
  rw [hF ω ω' h, hG ω ω' h]

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

/-- Fill unused coordinates only to evaluate a function whose dependence on
the retained coordinates has already been established. -/
def extend {n : ℕ} (base : E) (S : Finset (Link d n)) : C(S → E, Link d n → E) :=
  ⟨extendConfiguration base S, by
    classical
    apply continuous_pi
    intro l
    dsimp [extendConfiguration]
    split_ifs
    · exact continuous_apply _
    · exact continuous_const⟩

theorem localObservable_reconstruct {n : ℕ} (base : E) (S : Finset (Link d n))
    (F : C(Link d n → E, ℝ)) (hF : DependsOn S F) :
    localObservable S (F.comp (extend base S)) = F := by
  ext ω
  apply hF
  intro l hl
  simp [extend, extendConfiguration, restrictTo, hl]

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

/-- The same estimate for full configuration observables with proved local
dependence, so products and transported marks can use one common interface. -/
theorem covariance_clustering_local (d : ℕ) (ν₀ : Measure E) [IsProbabilityMeasure ν₀]
    (base : E) {β : ℝ} (hβ : 0 ≤ β) (hβ0 : β ≤ beta0 d) :
    ∃ κ > 0, ∀ (M : Model d E) (hφ : ∀ p, Continuous (M.φ p))
      (S T : Finset (Link d M.n)), S.Nonempty →
      ∀ (F G : C(Link d M.n → E, ℝ)) (CF CG : ℝ),
      DependsOn S F → DependsOn T G →
      (∀ ω, |F ω| ≤ CF) → (∀ ω, |G ω| ≤ CG) →
      |covariance (Measure.pi fun _ ↦ ν₀) (realDensity M hφ β) F G| ≤
        3 * CF * CG * Real.exp (3 * S.card + 3 * T.card) *
          Real.exp (-κ * polymerDist S T) := by
  obtain ⟨κ, hκ, hc⟩ := covariance_clustering d ν₀ base hβ hβ0
  refine ⟨κ, hκ, ?_⟩
  intro M hφ S T hS F G CF CG hFS hGT hF hG
  have h := hc M hφ S T hS (F.comp (extend base S)) (G.comp (extend base T)) CF CG
    (fun _ ↦ hF _) (fun _ ↦ hG _)
  rwa [localObservable_reconstruct base S F hFS,
    localObservable_reconstruct base T G hGT] at h

/-- Explicit support-size and separation cost for one metric ball against
the union of two balls in four dimensions. -/
def ballResponseEnvelope (r κ : ℝ) : ℝ :=
  Real.exp (9 * (Real.exp r * exponentialVolumeBound 4 1) + 2 * κ * r)

/-- Spatial covariance after a local elimination may involve the boundaries
of whole cells. The radius enters the prefactor explicitly and the decay
rate is chosen before the radius, model, volume and marks. -/
theorem covariance_ball_union_clustering (ν₀ : Measure E) [IsProbabilityMeasure ν₀]
    (base : E) {β : ℝ} (hβ : 0 ≤ β) (hβ0 : β ≤ beta0 4) :
    ∃ κ > 0, ∀ (M : Model 4 E) (hφ : ∀ p, Continuous (M.φ p))
      (r : ℝ), 0 ≤ r → ∀ (l m k : Link 4 M.n)
      (F G : C(Link 4 M.n → E, ℝ)) (CF CG : ℝ), 0 ≤ CF → 0 ≤ CG →
      DependsOn (WilsonPatchGeometry.linkBall r l) F →
      DependsOn (WilsonPatchGeometry.linkBall r m ∪ WilsonPatchGeometry.linkBall r k) G →
      (∀ ω, |F ω| ≤ CF) → (∀ ω, |G ω| ≤ CG) →
      |covariance (Measure.pi fun _ ↦ ν₀) (realDensity M hφ β) F G| ≤
        3 * CF * CG * ballResponseEnvelope r κ *
          Real.exp (-κ * min (dist l m) (dist l k)) := by
  obtain ⟨κ, hκ, hc⟩ := covariance_clustering_local 4 ν₀ base hβ hβ0
  refine ⟨κ, hκ, ?_⟩
  intro M hφ r hr l m k F G CF CG hCF hCG hFdep hGdep hF hG
  have h := hc M hφ (WilsonPatchGeometry.linkBall r l)
    (WilsonPatchGeometry.linkBall r m ∪ WilsonPatchGeometry.linkBall r k)
    (WilsonPatchGeometry.linkBall_nonempty hr l) F G CF CG hFdep hGdep hF hG
  have hcard (x : Link 4 M.n) := WilsonPatchGeometry.card_linkBall_le (by decide) r x
  have hcardUnion :
      ((WilsonPatchGeometry.linkBall r m ∪ WilsonPatchGeometry.linkBall r k).card : ℝ) ≤
        2 * (Real.exp r * exponentialVolumeBound 4 1) := by
    have hle :
        ((WilsonPatchGeometry.linkBall r m ∪ WilsonPatchGeometry.linkBall r k).card : ℝ) ≤
        (WilsonPatchGeometry.linkBall r m).card + (WilsonPatchGeometry.linkBall r k).card := by
      exact_mod_cast card_union_le (WilsonPatchGeometry.linkBall r m) (WilsonPatchGeometry.linkBall r k)
    linarith [hcard m, hcard k]
  have hd := WilsonPatchGeometry.separation_linkBall_union hr l m k
  have he : Real.exp (3 * (WilsonPatchGeometry.linkBall r l).card +
      3 * (WilsonPatchGeometry.linkBall r m ∪ WilsonPatchGeometry.linkBall r k).card) *
      Real.exp (-κ * polymerDist (WilsonPatchGeometry.linkBall r l)
        (WilsonPatchGeometry.linkBall r m ∪ WilsonPatchGeometry.linkBall r k)) ≤
      ballResponseEnvelope r κ * Real.exp (-κ * min (dist l m) (dist l k)) := by
    unfold ballResponseEnvelope
    rw [← Real.exp_add, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith [hcard l, mul_nonneg hκ.le (sub_nonneg.mpr hd)]
  exact h.trans (by
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left he
      (show 0 ≤ 3 * CF * CG by positivity))

theorem covariance_ball_clustering (ν₀ : Measure E) [IsProbabilityMeasure ν₀]
    (base : E) {β : ℝ} (hβ : 0 ≤ β) (hβ0 : β ≤ beta0 4) :
    ∃ κ > 0, ∀ (M : Model 4 E) (hφ : ∀ p, Continuous (M.φ p))
      (r : ℝ), 0 ≤ r → ∀ (l m : Link 4 M.n)
      (F G : C(Link 4 M.n → E, ℝ)) (CF CG : ℝ), 0 ≤ CF → 0 ≤ CG →
      DependsOn (WilsonPatchGeometry.linkBall r l) F →
      DependsOn (WilsonPatchGeometry.linkBall r m) G →
      (∀ ω, |F ω| ≤ CF) → (∀ ω, |G ω| ≤ CG) →
      |covariance (Measure.pi fun _ ↦ ν₀) (realDensity M hφ β) F G| ≤
        3 * CF * CG * ballResponseEnvelope r κ * Real.exp (-κ * dist l m) := by
  obtain ⟨κ, hκ, hc⟩ := covariance_ball_union_clustering ν₀ base hβ hβ0
  refine ⟨κ, hκ, ?_⟩
  intro M hφ r hr l m F G CF CG hCF hCG hFdep hGdep hF hG
  simpa only [union_self, min_self] using hc M hφ r hr l m m F G CF CG hCF hCG
    hFdep (by simpa only [union_self] using hGdep) hF hG

/-- Three bounded marks supported in metric balls have tree decay. This
form accommodates the exact enlargement of support under cell integration. -/
theorem thirdCumulant_ball_clustering (ν₀ : Measure E) [IsProbabilityMeasure ν₀]
    (base : E) {β : ℝ} (hβ : 0 ≤ β) (hβ0 : β ≤ beta0 4) :
    ∃ κ > 0, ∀ (M : Model 4 E) (hφ : ∀ p, Continuous (M.φ p))
      (r : ℝ), 0 ≤ r → ∀ (l m k : Link 4 M.n)
      (F G H : C(Link 4 M.n → E, ℝ)) (B : ℝ), 0 ≤ B →
      DependsOn (WilsonPatchGeometry.linkBall r l) F →
      DependsOn (WilsonPatchGeometry.linkBall r m) G →
      DependsOn (WilsonPatchGeometry.linkBall r k) H →
      (∀ ω, |F ω| ≤ B) → (∀ ω, |G ω| ≤ B) → (∀ ω, |H ω| ≤ B) →
      |thirdCumulant (Measure.pi fun _ ↦ ν₀) (realDensity M hφ β) F G H| ≤
        9 * B ^ 3 * ballResponseEnvelope r κ *
          Real.exp (-(κ / 2) * threeTreeLength l m k) := by
  obtain ⟨κ, hκ, hc⟩ := covariance_ball_union_clustering ν₀ base hβ hβ0
  refine ⟨κ, hκ, ?_⟩
  intro M hφ r hr l m k F G H B hB hFdep hGdep hHdep hF hG hH
  have hcut (a b c : Link 4 M.n) (A J K : C(Link 4 M.n → E, ℝ))
      (hAdep : DependsOn (WilsonPatchGeometry.linkBall r a) A)
      (hJdep : DependsOn (WilsonPatchGeometry.linkBall r b) J)
      (hKdep : DependsOn (WilsonPatchGeometry.linkBall r c) K)
      (hA : ∀ ω, |A ω| ≤ B) (hJ : ∀ ω, |J ω| ≤ B) (hK : ∀ ω, |K ω| ≤ B) :
      |thirdCumulant (Measure.pi fun _ ↦ ν₀) (realDensity M hφ β) A J K| ≤
        9 * B ^ 3 * ballResponseEnvelope r κ *
          Real.exp (-κ * min (dist a b) (dist a c)) := by
    have hJK := hc M hφ r hr a b c A (J * K) B (B * B) hB (mul_nonneg hB hB)
      hAdep ((hJdep.mono subset_union_left).mul (hKdep.mono subset_union_right)) hA
      (fun ω ↦ by
        rw [ContinuousMap.mul_apply, abs_mul]
        exact mul_le_mul (hJ ω) (hK ω) (abs_nonneg _) hB)
    have hAJ := hc M hφ r hr a b c A J B B hB hB hAdep
      (hJdep.mono subset_union_left) hA hJ
    have hAK := hc M hφ r hr a b c A K B B hB hB hAdep
      (hKdep.mono subset_union_right) hA hK
    have hEJ := abs_expectation_le (Measure.pi fun _ ↦ ν₀) (realDensity M hφ β) J
      (realDensity_pos M hφ β) hJ
    have hEK := abs_expectation_le (Measure.pi fun _ ↦ ν₀) (realDensity M hφ β) K
      (realDensity_pos M hφ β) hK
    rw [thirdCumulant_eq_covariances]
    have ht (x y z : ℝ) : |x - y - z| ≤ |x| + |y| + |z| := by
      linarith [abs_sub (x - y) z, abs_sub x y]
    apply (ht _ _ _).trans
    simp only [abs_mul]
    apply (add_le_add (add_le_add hJK (mul_le_mul hEJ hAK (abs_nonneg _) hB))
      (mul_le_mul hEK hAJ (abs_nonneg _) hB)).trans_eq
    ring
  have hex (δ : ℝ) (hδ : threeTreeLength l m k ≤ 2 * δ) :
      9 * B ^ 3 * ballResponseEnvelope r κ * Real.exp (-κ * δ) ≤
        9 * B ^ 3 * ballResponseEnvelope r κ *
          Real.exp (-(κ / 2) * threeTreeLength l m k) := by
    apply mul_le_mul_of_nonneg_left _ (by unfold ballResponseEnvelope; positivity)
    apply Real.exp_le_exp.mpr
    nlinarith [mul_nonneg hκ.le (sub_nonneg.mpr hδ)]
  rcases threeTreeLength_cut l m k with h | h | h
  · exact (hcut l m k F G H hFdep hGdep hHdep hF hG hH).trans (hex _ h)
  · rw [thirdCumulant_rotate]
    exact (hcut m k l G H F hGdep hHdep hFdep hG hH hF).trans (hex _ h)
  · rw [thirdCumulant_rotate, thirdCumulant_rotate]
    exact (hcut k l m H F G hHdep hFdep hGdep hH hF hG).trans (hex _ h)

/-- Volume-uniform second and third budgets for the enlarged supports.
The radius is fixed before all models and marks, with its cost explicit. -/
theorem uniform_ball_response_bounds (ν₀ : Measure E) [IsProbabilityMeasure ν₀]
    (base : E) {β B r : ℝ} (hβ : 0 ≤ β) (hβ0 : β ≤ beta0 4)
    (hB : 0 ≤ B) (hr : 0 ≤ r) :
    ∃ η > 0, ∃ C₂ ≥ 0, ∃ C₃ ≥ 0,
      ∀ (M : Model 4 E) (hφ : ∀ p, Continuous (M.φ p))
        (F : Link 4 M.n → C(Link 4 M.n → E, ℝ)),
        (∀ l, DependsOn (WilsonPatchGeometry.linkBall r l) (F l)) →
        (∀ l ω, |F l ω| ≤ B) →
        weightedResponseSeminorm η (fun l m ↦
          covariance (Measure.pi fun _ ↦ ν₀) (realDensity M hφ β) (F l) (F m)) ≤ C₂ ∧
        weightedThirdSeminorm η (fun l m k ↦
          thirdCumulant (Measure.pi fun _ ↦ ν₀) (realDensity M hφ β) (F l) (F m) (F k)) ≤ C₃ := by
  obtain ⟨κ₂, hκ₂, hc₂⟩ := covariance_ball_clustering ν₀ base hβ hβ0
  obtain ⟨κ₃, hκ₃, hc₃⟩ := thirdCumulant_ball_clustering ν₀ base hβ hβ0
  let η := min κ₂ (κ₃ / 2) / 2
  have hη : 0 < η := by dsimp [η]; positivity
  have hη₂ : η < κ₂ := by
    have := min_le_left κ₂ (κ₃ / 2)
    dsimp [η] at *
    linarith
  have hη₃ : η < κ₃ / 2 := by
    have := min_le_right κ₂ (κ₃ / 2)
    dsimp [η] at *
    linarith
  have hM₂ : 0 ≤ 3 * B ^ 2 * ballResponseEnvelope r κ₂ := by
    unfold ballResponseEnvelope; positivity
  have hM₃ : 0 ≤ 9 * B ^ 3 * ballResponseEnvelope r κ₃ := by
    unfold ballResponseEnvelope; positivity
  have hV₂ : 0 ≤ exponentialVolumeBound 4 (κ₂ - η) := by
    unfold exponentialVolumeBound; positivity
  have hV₃ : 0 ≤ exponentialVolumeBound 4 ((κ₃ / 2 - η) / 2) := by
    unfold exponentialVolumeBound; positivity
  refine ⟨η, hη, 3 * B ^ 2 * ballResponseEnvelope r κ₂ *
    exponentialVolumeBound 4 (κ₂ - η), mul_nonneg hM₂ hV₂,
    9 * B ^ 3 * ballResponseEnvelope r κ₃ *
      (exponentialVolumeBound 4 ((κ₃ / 2 - η) / 2)) ^ 2, by positivity, ?_⟩
  intro M hφ F hlocal hF
  constructor
  · apply weightedResponseSeminorm_le_of_envelope η κ₂ _ hM₂ hV₂
    · intro l m
      simpa only [pow_two, mul_assoc] using
        hc₂ M hφ r hr l m (F l) (F m) B B hB hB (hlocal l) (hlocal m) (hF l) (hF m)
    · intro l
      exact sum_exp_dist_le (by decide) (sub_pos.mpr hη₂) l
  · apply weightedThirdSeminorm_le_of_envelope η (κ₃ / 2) hη₃.le _ hM₃ hV₃
      (fun l m k ↦ hc₃ M hφ r hr l m k (F l) (F m) (F k) B hB
        (hlocal l) (hlocal m) (hlocal k) (hF l) (hF m) (hF k))
    intro l
    exact sum_exp_dist_le (by decide) (by linarith) l

/-- Explicit three-collar prefactor in four dimensions. Each singleton
collar has at most 256 links; the bound does not depend on the volume. -/
def thirdCumulantEnvelope (B κ : ℝ) : ℝ :=
  9 * B ^ 3 * Real.exp (2304 + 2 * κ)

def covarianceEnvelope (B κ : ℝ) : ℝ :=
  3 * B ^ 2 * Real.exp (1536 + 2 * κ)

/-- Collar covariance decay also holds at coincident coordinates, without
using a separated-patch derivative formula. -/
theorem covariance_collar_clustering (ν₀ : Measure E) [IsProbabilityMeasure ν₀]
    (base : E) {β : ℝ} (hβ : 0 ≤ β) (hβ0 : β ≤ beta0 4) :
    ∃ κ > 0, ∀ (M : Model 4 E) (hφ : ∀ p, Continuous (M.φ p))
      (l m : Link 4 M.n) (F G : C(Link 4 M.n → E, ℝ)) (B : ℝ), 0 ≤ B →
      DependsOn (WilsonPatchGeometry.collar {l}) F →
      DependsOn (WilsonPatchGeometry.collar {m}) G →
      (∀ ω, |F ω| ≤ B) → (∀ ω, |G ω| ≤ B) →
      |covariance (Measure.pi fun _ ↦ ν₀) (realDensity M hφ β) F G| ≤
        covarianceEnvelope B κ * Real.exp (-κ * dist l m) := by
  obtain ⟨κ, hκ, hc⟩ := covariance_clustering_local 4 ν₀ base hβ hβ0
  refine ⟨κ, hκ, ?_⟩
  intro M hφ l m F G B hB hFS hGT hF hG
  have hS := WilsonPatchGeometry.singleton_collar_nonempty l
  have hT := WilsonPatchGeometry.singleton_collar_nonempty m
  have h := hc M hφ (WilsonPatchGeometry.collar {l}) (WilsonPatchGeometry.collar {m})
    hS F G B B hFS hGT hF hG
  have hcard (x : Link 4 M.n) :
      ((WilsonPatchGeometry.collar {x}).card : ℝ) ≤ 256 := by
    exact_mod_cast (by simpa using
      WilsonPatchGeometry.card_collar_le ({x} : Finset (Link 4 M.n)))
  have hd := WilsonPatchGeometry.separation_collar hS hT
  rw [WilsonPatchGeometry.polymerDist_singletons] at hd
  have he :
      Real.exp (3 * (WilsonPatchGeometry.collar {l}).card +
        3 * (WilsonPatchGeometry.collar {m}).card) *
        Real.exp (-κ * polymerDist (WilsonPatchGeometry.collar {l}) (WilsonPatchGeometry.collar {m})) ≤
      Real.exp (1536 + 2 * κ) * Real.exp (-κ * dist l m) := by
    rw [← Real.exp_add, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith [hcard l, hcard m, mul_nonneg hκ.le (sub_nonneg.mpr hd)]
  apply h.trans
  simpa only [covarianceEnvelope, pow_two, mul_assoc] using
    mul_le_mul_of_nonneg_left he (show 0 ≤ 3 * B * B by positivity)

private theorem thirdCumulant_cut_bound (ν₀ : Measure E) [IsProbabilityMeasure ν₀]
    {β κ : ℝ} (hκ : 0 ≤ κ) (M : Model 4 E) (hφ : ∀ p, Continuous (M.φ p))
    (hc : ∀ (S T : Finset (Link 4 M.n)), S.Nonempty →
      ∀ (F G : C(Link 4 M.n → E, ℝ)) (CF CG : ℝ),
      DependsOn S F → DependsOn T G →
      (∀ ω, |F ω| ≤ CF) → (∀ ω, |G ω| ≤ CG) →
      |covariance (Measure.pi fun _ ↦ ν₀) (realDensity M hφ β) F G| ≤
        3 * CF * CG * Real.exp (3 * S.card + 3 * T.card) *
          Real.exp (-κ * polymerDist S T))
    (l m k : Link 4 M.n) (F G H : C(Link 4 M.n → E, ℝ))
    {B : ℝ} (hB : 0 ≤ B)
    (hFS : DependsOn (WilsonPatchGeometry.collar {l}) F)
    (hGT : DependsOn (WilsonPatchGeometry.collar {m}) G)
    (hHU : DependsOn (WilsonPatchGeometry.collar {k}) H)
    (hF : ∀ ω, |F ω| ≤ B) (hG : ∀ ω, |G ω| ≤ B) (hH : ∀ ω, |H ω| ≤ B) :
    |thirdCumulant (Measure.pi fun _ ↦ ν₀) (realDensity M hφ β) F G H| ≤
      thirdCumulantEnvelope B κ * Real.exp (-κ * min (dist l m) (dist l k)) := by
  let S := WilsonPatchGeometry.collar {l}
  let T := WilsonPatchGeometry.collar {m}
  let U := WilsonPatchGeometry.collar {k}
  let δ := min (dist l m) (dist l k)
  let Q := 3 * B * Real.exp (2304 + 2 * κ) * Real.exp (-κ * δ)
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  have hcard (x : Link 4 M.n) :
      (WilsonPatchGeometry.collar {x}).card ≤ 256 := by
    simpa using WilsonPatchGeometry.card_collar_le ({x} : Finset (Link 4 M.n))
  have hS := WilsonPatchGeometry.singleton_collar_nonempty l
  have hT := WilsonPatchGeometry.singleton_collar_nonempty m
  have hU := WilsonPatchGeometry.singleton_collar_nonempty k
  have hbound (V : Finset (Link 4 M.n)) (J : C(Link 4 M.n → E, ℝ))
      (C : ℝ) (hC : 0 ≤ C) (hJV : DependsOn V J) (hJ : ∀ ω, |J ω| ≤ C)
      (hV : V.card ≤ 512) (hd : δ - 2 ≤ polymerDist S V) :
      |covariance (Measure.pi fun _ ↦ ν₀) (realDensity M hφ β) F J| ≤ Q * C := by
    have h := hc S V hS F J B C hFS hJV hF hJ
    have hs : (S.card : ℝ) ≤ 256 := by exact_mod_cast hcard l
    have hv : (V.card : ℝ) ≤ 512 := by exact_mod_cast hV
    have he : Real.exp (3 * S.card + 3 * V.card) * Real.exp (-κ * polymerDist S V) ≤
        Real.exp (2304 + 2 * κ) * Real.exp (-κ * δ) := by
      rw [← Real.exp_add, ← Real.exp_add]
      apply Real.exp_le_exp.mpr
      nlinarith [mul_nonneg hκ (sub_nonneg.mpr hd)]
    calc
      _ ≤ (3 * B * C) * (Real.exp (3 * S.card + 3 * V.card) *
          Real.exp (-κ * polymerDist S V)) := by simpa only [mul_assoc] using h
      _ ≤ (3 * B * C) * (Real.exp (2304 + 2 * κ) * Real.exp (-κ * δ)) :=
        mul_le_mul_of_nonneg_left he (by positivity)
      _ = Q * C := by dsimp [Q]; ring
  have hFGH := hbound (T ∪ U) (G * H) (B * B) (mul_nonneg hB hB)
    ((hGT.mono subset_union_left).mul (hHU.mono subset_union_right))
    (fun ω ↦ by
      rw [ContinuousMap.mul_apply, abs_mul]
      exact mul_le_mul (hG ω) (hH ω) (abs_nonneg _) hB)
    ((card_union_le T U).trans (by
      dsimp only [T, U]
      have := hcard m
      have := hcard k
      omega))
    (by simpa only [WilsonPatchGeometry.polymerDist_singletons] using
      WilsonPatchGeometry.separation_collar_union hS hT hU)
  have hFH := hbound U H B hB hHU hH ((hcard k).trans (by decide)) (by
    have h := WilsonPatchGeometry.separation_collar hS hU
    rw [WilsonPatchGeometry.polymerDist_singletons] at h
    dsimp only [δ]
    linarith [min_le_right (dist l m) (dist l k)])
  have hFG := hbound T G B hB hGT hG ((hcard m).trans (by decide)) (by
    have h := WilsonPatchGeometry.separation_collar hS hT
    rw [WilsonPatchGeometry.polymerDist_singletons] at h
    dsimp only [δ]
    linarith [min_le_left (dist l m) (dist l k)])
  have hEG := abs_expectation_le (Measure.pi fun _ ↦ ν₀) (realDensity M hφ β) G
    (realDensity_pos M hφ β) hG
  have hEH := abs_expectation_le (Measure.pi fun _ ↦ ν₀) (realDensity M hφ β) H
    (realDensity_pos M hφ β) hH
  rw [thirdCumulant_eq_covariances]
  have htri (a b c : ℝ) : |a - b - c| ≤ |a| + |b| + |c| := by
    linarith [abs_sub (a - b) c, abs_sub a b]
  apply (htri _ _ _).trans
  simp only [abs_mul]
  apply (add_le_add (add_le_add hFGH
    (mul_le_mul hEG hFH (abs_nonneg _) hB))
    (mul_le_mul hEH hFG (abs_nonneg _) hB)).trans_eq
  dsimp [Q, δ, thirdCumulantEnvelope]
  ring

/-- Uniform tree decay for three arbitrary bounded local marks on singleton
plaquette collars. The same rate covers all continuous inhomogeneous Wilson
potentials, including fixed boundary fields and omitted plaquettes. -/
theorem thirdCumulant_collar_clustering (ν₀ : Measure E) [IsProbabilityMeasure ν₀]
    (base : E) {β : ℝ} (hβ : 0 ≤ β) (hβ0 : β ≤ beta0 4) :
    ∃ κ > 0, ∀ (M : Model 4 E) (hφ : ∀ p, Continuous (M.φ p))
      (l m k : Link 4 M.n) (F G H : C(Link 4 M.n → E, ℝ)) (B : ℝ), 0 ≤ B →
      DependsOn (WilsonPatchGeometry.collar {l}) F →
      DependsOn (WilsonPatchGeometry.collar {m}) G →
      DependsOn (WilsonPatchGeometry.collar {k}) H →
      (∀ ω, |F ω| ≤ B) → (∀ ω, |G ω| ≤ B) → (∀ ω, |H ω| ≤ B) →
      |thirdCumulant (Measure.pi fun _ ↦ ν₀) (realDensity M hφ β) F G H| ≤
        thirdCumulantEnvelope B κ * Real.exp (-(κ / 2) * threeTreeLength l m k) := by
  obtain ⟨κ, hκ, hc⟩ := covariance_clustering_local 4 ν₀ base hβ hβ0
  refine ⟨κ, hκ, ?_⟩
  intro M hφ l m k F G H B hB hFS hGT hHU hF hG hH
  have henv : 0 ≤ thirdCumulantEnvelope B κ := by
    unfold thirdCumulantEnvelope
    positivity
  have hcut := thirdCumulant_cut_bound ν₀ hκ.le M hφ (hc M hφ)
  have hex (δ : ℝ) (hδ : threeTreeLength l m k ≤ 2 * δ) :
      thirdCumulantEnvelope B κ * Real.exp (-κ * δ) ≤
        thirdCumulantEnvelope B κ * Real.exp (-(κ / 2) * threeTreeLength l m k) := by
    apply mul_le_mul_of_nonneg_left _ henv
    apply Real.exp_le_exp.mpr
    nlinarith [mul_nonneg hκ.le (sub_nonneg.mpr hδ)]
  rcases threeTreeLength_cut l m k with h | h | h
  · exact (hcut l m k F G H hB hFS hGT hHU hF hG hH).trans (hex _ h)
  · rw [thirdCumulant_rotate]
    exact (hcut m k l G H F hB hGT hHU hFS hG hH hF).trans (hex _ h)
  · rw [thirdCumulant_rotate, thirdCumulant_rotate]
    exact (hcut k l m H F G hB hHU hFS hGT hH hF hG).trans (hex _ h)

/-- A common second/third response budget for every bounded collar-local
family under every original or pinned inhomogeneous Wilson law. All three
constants precede the model, volume and the chosen marks. -/
theorem uniform_collar_response_bounds (ν₀ : Measure E) [IsProbabilityMeasure ν₀]
    (base : E) {β B : ℝ} (hβ : 0 ≤ β) (hβ0 : β ≤ beta0 4) (hB : 0 ≤ B) :
    ∃ η > 0, ∃ C₂ ≥ 0, ∃ C₃ ≥ 0,
      ∀ (M : Model 4 E) (hφ : ∀ p, Continuous (M.φ p))
        (F : Link 4 M.n → C(Link 4 M.n → E, ℝ)),
        (∀ l, DependsOn (WilsonPatchGeometry.collar {l}) (F l)) →
        (∀ l ω, |F l ω| ≤ B) →
        weightedResponseSeminorm η (fun l m ↦
          covariance (Measure.pi fun _ ↦ ν₀) (realDensity M hφ β) (F l) (F m)) ≤ C₂ ∧
        weightedThirdSeminorm η (fun l m k ↦
          thirdCumulant (Measure.pi fun _ ↦ ν₀) (realDensity M hφ β) (F l) (F m) (F k)) ≤ C₃ := by
  obtain ⟨κ₂, hκ₂, hc₂⟩ := covariance_collar_clustering ν₀ base hβ hβ0
  obtain ⟨κ₃, hκ₃, hc₃⟩ := thirdCumulant_collar_clustering ν₀ base hβ hβ0
  let η := min κ₂ (κ₃ / 2) / 2
  have hη : 0 < η := by dsimp [η]; positivity
  have hη₂ : η < κ₂ := by
    have := min_le_left κ₂ (κ₃ / 2)
    dsimp [η] at *
    linarith
  have hη₃ : η < κ₃ / 2 := by
    have := min_le_right κ₂ (κ₃ / 2)
    dsimp [η] at *
    linarith
  have hM₂ : 0 ≤ covarianceEnvelope B κ₂ := by unfold covarianceEnvelope; positivity
  have hM₃ : 0 ≤ thirdCumulantEnvelope B κ₃ := by unfold thirdCumulantEnvelope; positivity
  have hV₂ : 0 ≤ exponentialVolumeBound 4 (κ₂ - η) := by
    unfold exponentialVolumeBound
    positivity
  have hV₃ : 0 ≤ exponentialVolumeBound 4 ((κ₃ / 2 - η) / 2) := by
    unfold exponentialVolumeBound
    positivity
  refine ⟨η, hη, covarianceEnvelope B κ₂ * exponentialVolumeBound 4 (κ₂ - η),
    mul_nonneg hM₂ hV₂,
    thirdCumulantEnvelope B κ₃ * (exponentialVolumeBound 4 ((κ₃ / 2 - η) / 2)) ^ 2,
    by positivity, ?_⟩
  intro M hφ F hlocal hF
  constructor
  · apply weightedResponseSeminorm_le_of_envelope η κ₂ _ hM₂ hV₂
      (fun l m ↦ hc₂ M hφ l m (F l) (F m) B hB (hlocal l) (hlocal m) (hF l) (hF m))
    intro l
    exact sum_exp_dist_le (by decide) (sub_pos.mpr hη₂) l
  · apply weightedThirdSeminorm_le_of_envelope η (κ₃ / 2) hη₃.le _ hM₃ hV₃
      (fun l m k ↦ hc₃ M hφ l m k (F l) (F m) (F k) B hB
        (hlocal l) (hlocal m) (hlocal k) (hF l) (hF m) (hF k))
    intro l
    exact sum_exp_dist_le (by decide) (by linarith) l

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
