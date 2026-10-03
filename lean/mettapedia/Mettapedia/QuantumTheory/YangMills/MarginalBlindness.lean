import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Constructions.Pi
import Mettapedia.QuantumTheory.YangMills.SU2WilsonAssemblyLocality
import Mettapedia.QuantumTheory.YangMills.CalibrationSeparation

/-!
# Marginal criteria cannot certify clustering

For a probability measure `μ` on `E` and a finite set of sites `X`, the product
measure `⊗ μ` and the diagonal measure, the law of the constant configuration
`fun _ => e` with `e ∼ μ`, have the same marginal `μ` at every site
(`map_eval_pi`, `map_eval_diagonal`).  Under the product measure, observables at
distinct sites are uncorrelated (`truncated_pi_eq_zero`).  Under the diagonal
measure, the truncated two-point function of `F` and `G` at any two sites is the
covariance of `F` and `G` under `μ` (`truncated_diagonal`), whatever the distance
between the sites.  So no uniform exponential bound holds for the diagonal
measures once the sites can be arbitrarily far apart, unless that covariance
vanishes (`covariance_eq_zero_of_exponentialBound`).

A condition on the one-site laws alone, applied at any block scale (a threshold
on block energies, on the fraction of blocks with large field strength, or on the
law of a blocked plaquette), therefore cannot imply decay of correlations: it
holds or fails for both measures at once.  A crossing criterion has to constrain
correlations or conditional laws.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory

namespace Mettapedia.QuantumTheory.YangMills.MarginalBlindness

variable {X : Type*} {E : Type*} [MeasurableSpace E] (μ : Measure E) [IsProbabilityMeasure μ]

/-- The diagonal measure: the law of the constant configuration `fun _ => e` with
`e ∼ μ`. -/
def diagonal : Measure (X → E) :=
  μ.map fun e _ => e

theorem measurable_diag : Measurable fun (e : E) (_ : X) => e :=
  measurable_pi_lambda _ fun _ => measurable_id

theorem map_eval_pi [Fintype X] (x : X) : (Measure.pi fun _ : X => μ).map (fun ω => ω x) = μ :=
  (measurePreserving_eval (fun _ : X => μ) x).map_eq

omit [IsProbabilityMeasure μ] in
theorem map_eval_diagonal (x : X) : (diagonal (X := X) μ).map (fun ω => ω x) = μ := by
  unfold diagonal
  rw [Measure.map_map (measurable_pi_apply x) measurable_diag]
  exact Measure.map_id

theorem integral_eval_pi [Fintype X] (F : E → ℝ) (hF : Measurable F) (x : X) :
    ∫ ω, F (ω x) ∂(Measure.pi fun _ : X => μ) = ∫ e, F e ∂μ := by
  calc ∫ ω, F (ω x) ∂(Measure.pi fun _ : X => μ)
      = ∫ e, F e ∂((Measure.pi fun _ : X => μ).map fun ω => ω x) :=
        (integral_map (μ := Measure.pi fun _ : X => μ) (f := F) (measurable_pi_apply x).aemeasurable
          (by rw [map_eval_pi]; exact hF.aestronglyMeasurable)).symm
    _ = ∫ e, F e ∂μ := by rw [map_eval_pi]

/-- Under the product measure, observables at distinct sites are uncorrelated. -/
theorem truncated_pi_eq_zero [Fintype X] [DecidableEq X] (F G : E → ℝ) (hF : Measurable F)
    (hG : Measurable G) {x y : X} (hxy : x ≠ y) :
    ∫ ω, F (ω x) * G (ω y) ∂(Measure.pi fun _ : X => μ) -
      (∫ ω, F (ω x) ∂(Measure.pi fun _ : X => μ)) *
        ∫ ω, G (ω y) ∂(Measure.pi fun _ : X => μ) = 0 := by
  set f : X → E → ℝ := fun i => if i = x then F else if i = y then G else fun _ => 1 with hf
  have hprod : ∀ ω : X → E, ∏ i, f i (ω i) = F (ω x) * G (ω y) := by
    intro ω
    rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ y),
      ← Finset.prod_erase_mul _ _ (Finset.mem_erase.mpr ⟨hxy, Finset.mem_univ x⟩)]
    have hrest : ∏ i ∈ (Finset.univ.erase y).erase x, f i (ω i) = 1 := by
      refine Finset.prod_eq_one fun i hi => ?_
      obtain ⟨hix, hi'⟩ := Finset.mem_erase.mp hi
      obtain ⟨hiy, -⟩ := Finset.mem_erase.mp hi'
      simp [hf, hix, hiy]
    rw [hrest, one_mul]
    simp [hf, hxy.symm]
  have hint : ∀ i, ∫ e, f i e ∂μ = if i = x then ∫ e, F e ∂μ else if i = y then ∫ e, G e ∂μ
      else 1 := by
    intro i
    by_cases hix : i = x
    · simp [hf, hix]
    · by_cases hiy : i = y
      · subst hiy
        simp [hf, hix]
      · simp [hf, hix, hiy]
  have hmain : ∫ ω, F (ω x) * G (ω y) ∂(Measure.pi fun _ : X => μ) =
      (∫ e, F e ∂μ) * ∫ e, G e ∂μ := by
    simp_rw [← hprod]
    rw [integral_fintype_prod_eq_prod (μ := fun _ : X => μ) f]
    rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ y),
      ← Finset.prod_erase_mul _ _ (Finset.mem_erase.mpr ⟨hxy, Finset.mem_univ x⟩)]
    have hrest : ∏ i ∈ (Finset.univ.erase y).erase x, ∫ e, f i e ∂μ = 1 := by
      refine Finset.prod_eq_one fun i hi => ?_
      obtain ⟨hix, hi'⟩ := Finset.mem_erase.mp hi
      obtain ⟨hiy, -⟩ := Finset.mem_erase.mp hi'
      rw [hint i]
      simp [hix, hiy]
    rw [hrest, one_mul, hint x, hint y]
    simp [hxy.symm]
  rw [hmain, integral_eval_pi μ F hF, integral_eval_pi μ G hG]
  ring

omit [IsProbabilityMeasure μ] in
/-- Under the diagonal measure, the truncated two-point function of `F` and `G`
at any two sites is their covariance under `μ`. -/
theorem truncated_diagonal (F G : E → ℝ) (hF : Measurable F) (hG : Measurable G) (x y : X) :
    ∫ ω, F (ω x) * G (ω y) ∂(diagonal μ) -
      (∫ ω, F (ω x) ∂(diagonal μ)) * ∫ ω, G (ω y) ∂(diagonal μ) =
    ∫ e, F e * G e ∂μ - (∫ e, F e ∂μ) * ∫ e, G e ∂μ := by
  unfold diagonal
  rw [integral_map (f := fun ω : X → E => F (ω x) * G (ω y)) measurable_diag.aemeasurable
      ((hF.comp (measurable_pi_apply x)).mul (hG.comp (measurable_pi_apply y))).aestronglyMeasurable,
    integral_map (f := fun ω : X → E => F (ω x)) measurable_diag.aemeasurable
      (hF.comp (measurable_pi_apply x)).aestronglyMeasurable,
    integral_map (f := fun ω : X → E => G (ω y)) measurable_diag.aemeasurable
      (hG.comp (measurable_pi_apply y)).aestronglyMeasurable]

omit [IsProbabilityMeasure μ] in
/-- If the diagonal measures on a family of pseudometric site sets satisfied a
uniform exponential bound on truncated two-point functions at pairs of sites that
are arbitrarily far apart, the covariance would vanish. -/
theorem covariance_eq_zero_of_exponentialBound {ι : Type*} (Sites : ι → Type*)
    [∀ L, PseudoMetricSpace (Sites L)]
    (F G : E → ℝ) (hF : Measurable F) (hG : Measurable G) (C κ : ℝ) (hκ : 0 < κ)
    (hbound : ∀ L (x y : Sites L),
      |∫ ω, F (ω x) * G (ω y) ∂(diagonal μ) -
          (∫ ω, F (ω x) ∂(diagonal μ)) * ∫ ω, G (ω y) ∂(diagonal μ)| ≤
        C * Real.exp (-κ * dist x y))
    (hfar : ∀ R : ℝ, ∃ L, ∃ x y : Sites L, R ≤ dist x y) :
    ∫ e, F e * G e ∂μ - (∫ e, F e ∂μ) * ∫ e, G e ∂μ = 0 := by
  set c := ∫ e, F e * G e ∂μ - (∫ e, F e ∂μ) * ∫ e, G e ∂μ
  have hle : ∀ R : ℝ, |c| ≤ |C| * Real.exp (-κ * R) := by
    intro R
    obtain ⟨L, x, y, hR⟩ := hfar R
    have h := hbound L x y
    rw [truncated_diagonal μ F G hF hG x y] at h
    calc |c| ≤ C * Real.exp (-κ * dist x y) := h
      _ ≤ |C| * Real.exp (-κ * dist x y) :=
          mul_le_mul_of_nonneg_right (le_abs_self C) (Real.exp_pos _).le
      _ ≤ |C| * Real.exp (-κ * R) := by
          apply mul_le_mul_of_nonneg_left _ (abs_nonneg C)
          apply Real.exp_le_exp.mpr
          nlinarith
  by_contra hc
  have hpos : 0 < |c| := abs_pos.mpr hc
  by_cases hC : |C| = 0
  · have := hle 0
    rw [hC, zero_mul] at this
    linarith
  · have hCpos : 0 < |C| := lt_of_le_of_ne (abs_nonneg C) (Ne.symm hC)
    set R := (Real.log |C| - Real.log (|c| / 2)) / κ + 1 with hR
    have h := hle R
    have hlt : |C| * Real.exp (-κ * R) < |c| := by
      have hkR : -κ * R = Real.log (|c| / 2) - Real.log |C| - κ := by
        rw [hR]
        field_simp
        ring
      rw [hkR, Real.exp_sub, Real.exp_sub, Real.exp_log (by positivity), Real.exp_log hCpos]
      have hek : 1 < Real.exp κ := Real.one_lt_exp_iff.mpr hκ
      rw [mul_div_assoc', mul_div_assoc', mul_comm |C|, mul_div_assoc,
        div_self hCpos.ne', mul_one, div_div]
      rw [div_lt_iff₀ (by positivity)]
      nlinarith
    linarith

#print axioms truncated_pi_eq_zero
#print axioms truncated_diagonal
#print axioms covariance_eq_zero_of_exponentialBound

end Mettapedia.QuantumTheory.YangMills.MarginalBlindness

/-! ## Correlations invisible to a nondegenerate paired-link marginal -/

namespace Mettapedia.QuantumTheory.YangMills.MarginalBlindness.Blocking
open Finset
open scoped Topology Classical
open WilsonBlockElimination WilsonBlockElimination.PairedLinks WilsonLocalResponse
open WilsonConditionalProjection.PairedHaar

variable {X I J E : Type*} [Fintype X] [Fintype I] [Fintype J] [DecidableEq X]
  [Group E] [TopologicalSpace E] [IsTopologicalGroup E] [CompactSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

/-- A bounded positive perturbation coupling two centered local marks. Its
purpose is to test a marginal-only criterion, not to identify a Wilson action. -/
def correlationDensity (ε : ℝ) (F G : C(X → E, ℝ)) : C(X → E, ℝ) := 1 + ε • (F*G)

theorem correlationDensity_pos {ε : ℝ} (hε : |ε| < 1) (F G : C(X → E, ℝ))
    (hF : ∀ U, |F U| ≤ 1) (hG : ∀ U, |G U| ≤ 1) (U : X → E) :
    0 < correlationDensity ε F G U := by
  have hp : |ε * (F U * G U)| ≤ |ε| := by
    rw [abs_mul, abs_mul]
    have hfg : |F U| * |G U| ≤ 1 := by
      nlinarith [hF U, hG U, abs_nonneg (F U), abs_nonneg (G U)]
    nlinarith [abs_nonneg ε]
  have hn := neg_abs_le (ε * (F U * G U))
  change 0 < 1 + ε * (F U * G U)
  linarith

variable (ν : Measure E) [IsProbabilityMeasure ν] [Measure.IsMulLeftInvariant ν]
  (e : ((I ⊕ I) ⊕ J) ≃ X) (S T : Finset X)
  (hST : Disjoint S T) (hret : retainedSupport e (S ∪ T) = ∅)

include hST hret

theorem blocked_product_of_no_retained_support (F G : C(X → E, ℝ))
    (hF : DependsOn S F) (hG : DependsOn T G) :
    blockedDensity ν e (F*G) =
      ((∫ U, F U ∂Measure.pi (fun _ : X => ν)) * (∫ U, G U ∂Measure.pi (fun _ : X => ν))) • 1 := by
  rw [blockedDensity_eq_integral ν e (S ∪ T) (F*G)
    ((hF.mono subset_union_left).mul (hG.mono subset_union_right)) hret]
  have hg : DependsOff S G := by
    intro U V h
    apply hG U V
    intro x hx
    exact h x (fun hxS => (Finset.disjoint_left.mp hST hxS hx).elim)
  simp only [ContinuousMap.mul_apply]
  rw [WilsonProductLocality.integral_mul_factor ν (1 : E) S F G
    F.continuous.measurable G.continuous.measurable hF hg]

/-- All four unnormalized marked integrals are calculated under the actual
paired Haar map, with the original two observables. -/
theorem correlationDensity_blocked_moments (ε : ℝ) (F G : C(X → E, ℝ))
    (hF : DependsOn S F) (hG : DependsOn T G)
    (hF0 : (∫ U, F U ∂Measure.pi (fun _ : X => ν)) = 0)
    (hG0 : (∫ U, G U ∂Measure.pi (fun _ : X => ν)) = 0) :
    let W := correlationDensity ε F G
    blockedDensity ν e W = 1 ∧ blockedDensity ν e (W*F) = 0 ∧
      blockedDensity ν e (W*G) = 0 ∧
      blockedDensity ν e (W*(F*G)) =
        (ε * (∫ U, F U*F U ∂Measure.pi (fun _ : X => ν)) *
          (∫ U, G U*G U ∂Measure.pi (fun _ : X => ν))) • 1 := by
  let B := blockedDensityLinear ν e
  have h1 : B 1 = 1 := by
    ext c
    change (∫ f : (I → E) × (J → E), (1 : ℝ)
      ∂(Measure.pi (fun _ : I => ν)).prod (Measure.pi (fun _ : J => ν))) = 1
    simp
  have hf : B F = 0 := by
    change blockedDensity ν e F = 0
    have h := blocked_product_of_no_retained_support ν e S T hST hret F 1 hF (fun _ _ _ => rfl)
    simpa only [mul_one, hF0, zero_mul, zero_smul] using h
  have hg : B G = 0 := by
    change blockedDensity ν e G = 0
    have h := blocked_product_of_no_retained_support ν e S T hST hret 1 G (fun _ _ _ => rfl) hG
    simpa only [one_mul, hG0, mul_zero, zero_smul] using h
  have hfg : B (F*G) = 0 := by
    change blockedDensity ν e (F*G) = 0
    simpa only [hF0, zero_mul, zero_smul] using
      blocked_product_of_no_retained_support ν e S T hST hret F G hF hG
  have hffg : B ((F*F)*G) = 0 := by
    change blockedDensity ν e ((F*F)*G) = 0
    simpa only [hG0, mul_zero, zero_smul] using
      blocked_product_of_no_retained_support ν e S T hST hret (F*F) G (hF.mul hF) hG
  have hfgg : B (F*(G*G)) = 0 := by
    change blockedDensity ν e (F*(G*G)) = 0
    simpa only [hF0, zero_mul, zero_smul] using
      blocked_product_of_no_retained_support ν e S T hST hret F (G*G) hF (hG.mul hG)
  have hfgfg : B ((F*G)*(F*G)) =
      ((∫ U, F U*F U ∂Measure.pi (fun _ : X => ν)) *
        (∫ U, G U*G U ∂Measure.pi (fun _ : X => ν))) • 1 := by
    rw [show (F*G)*(F*G) = (F*F)*(G*G) by ring]
    exact blocked_product_of_no_retained_support ν e S T hST hret (F*F) (G*G) (hF.mul hF) (hG.mul hG)
  change B (1 + ε • (F*G)) = 1 ∧ B ((1 + ε • (F*G))*F) = 0 ∧
    B ((1 + ε • (F*G))*G) = 0 ∧ _
  refine ⟨by rw [map_add, map_smul, h1, hfg, smul_zero, add_zero], ?_, ?_, ?_⟩
  · rw [show (1 + ε • (F*G))*F = F + ε • ((F*F)*G) by
      ext U; simp only [ContinuousMap.add_apply, ContinuousMap.mul_apply,
        ContinuousMap.smul_apply, ContinuousMap.one_apply, smul_eq_mul]; ring]
    rw [map_add, map_smul, hf, hffg, smul_zero, add_zero]
  · rw [show (1 + ε • (F*G))*G = G + ε • (F*(G*G)) by
      ext U; simp only [ContinuousMap.add_apply, ContinuousMap.mul_apply,
        ContinuousMap.smul_apply, ContinuousMap.one_apply, smul_eq_mul]; ring]
    rw [map_add, map_smul, hg, hfgg, smul_zero, add_zero]
  · change B ((1 + ε • (F*G))*(F*G)) = _
    rw [add_mul, one_mul, smul_mul_assoc, map_add, map_smul, hfg, hfgfg,
      zero_add, smul_smul, mul_assoc]

/-- The complete coarse density is constant, while the original covariance
is entirely contained in the conditional covariance. Positivity refers to
the original density, so every normalized projection is well defined. -/
theorem correlationDensity_projection (ε : ℝ) (F G : C(X → E, ℝ))
    (hF : DependsOn S F) (hG : DependsOn T G)
    (hF0 : (∫ U, F U ∂Measure.pi (fun _ : X => ν)) = 0)
    (hG0 : (∫ U, G U ∂Measure.pi (fun _ : X => ν)) = 0)
    (hW : ∀ U, 0 < correlationDensity ε F G U) :
    let W := correlationDensity ε F G
    let c := ε * (∫ U, F U*F U ∂Measure.pi (fun _ : X => ν)) *
      (∫ U, G U*G U ∂Measure.pi (fun _ : X => ν))
    blockedDensity ν e W = 1 ∧ blockedProject ν e W hW F = 0 ∧
      blockedProject ν e W hW G = 0 ∧ blockedProject ν e W hW (F*G) = c • 1 ∧
      covariance (Measure.pi fun _ : X => ν) W F G = c := by
  dsimp only
  obtain ⟨h0, hf, hg, hfg⟩ := correlationDensity_blocked_moments ν e S T hST hret
    ε F G hF hG hF0 hG0
  rw [blockedDensity_mul_project ν e _ hW, h0, one_mul] at hf hg hfg
  refine ⟨h0, hf, hg, hfg, ?_⟩
  unfold covariance
  rw [← expectation_blockedProject ν e _ hW (F*G),
    ← expectation_blockedProject ν e _ hW F,
    ← expectation_blockedProject ν e _ hW G, h0, hf, hg, hfg]
  simp [expectation]

end Mettapedia.QuantumTheory.YangMills.MarginalBlindness.Blocking

namespace Mettapedia.QuantumTheory.YangMills.MarginalBlindness.SU2Blocking
open Finset
open scoped Topology Classical
open StrongCouplingCrossing WilsonDyadicGeometry SU2WilsonBlockPilot SU2BoundaryResponse
open WilsonBlockElimination WilsonBlockElimination.PairedLinks
open WilsonConditionalProjection.PairedHaar SU2WilsonAssembly.ScaleTwo
open Mettapedia.Combinatorics.PolymerGas

/-- A plaquette in the 0,1 plane, translated in the transverse direction 2. -/
def transversePlaquette (n : ℕ) (s : ZMod (doubleIndex n + 3)) : Plaquette 4 (doubleIndex n) :=
  (fun i => if i = 2 then s else 0, ⟨(0,1), by decide⟩)

theorem transverse_coordinate (n : ℕ) (s : ZMod (doubleIndex n + 3))
    (l : Link 4 (doubleIndex n)) (hl : l ∈ support (transversePlaquette n s)) : l.1 2 = s := by
  obtain ⟨i, _, rfl⟩ := mem_image.mp hl
  fin_cases i <;> simp [linkAt, transversePlaquette, step]

/-- Opposite transverse translates are separated by at least half the fine
period. This distance tends to infinity with the lattice side. -/
theorem transverse_separation (n : ℕ) :
    (n : ℝ) + 3 ≤ polymerDist (support (transversePlaquette n 0))
      (support (transversePlaquette n (n+3))) := by
  have hcircle : dist (coordinateCircle (doubleIndex n) 0)
      (coordinateCircle (doubleIndex n) (n+3)) = (n : ℝ)+3 := by
    have h := CalibrationSeparation.coordinate_dist_eq_abs
      (n := doubleIndex n) (j := (n : ℤ)+3) (by
        simp only [Int.cast_add, Int.cast_natCast, Int.cast_ofNat,
          abs_of_nonneg (by positivity : (0 : ℝ) ≤ (n : ℝ)+3)]
        simp only [doubleIndex, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
        linarith)
    simpa only [Int.cast_add, Int.cast_natCast, Int.cast_ofNat,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ (n : ℝ)+3)] using h
  simp only [polymerDist, support_nonempty, ↓reduceDIte]
  apply Finset.le_inf'
  intro b hb
  apply (Metric.le_infDist (support_nonempty (transversePlaquette n 0))).mpr
  intro a ha
  have h := dist_le_pi_dist (position a) (position b) (2 : Fin 4)
  change dist (coordinateCircle (doubleIndex n) (a.1 2))
    (coordinateCircle (doubleIndex n) (b.1 2)) ≤ dist a b at h
  rw [transverse_coordinate n 0 a ha, transverse_coordinate n (n+3) b hb, hcircle] at h
  simpa only [dist_comm] using h

theorem separated_plaquette_disjoint {n : ℕ} (p q : Plaquette 4 (doubleIndex n))
    (hsep : 1 < polymerDist (support p) (support q)) : Disjoint (support p) (support q) := by
  by_contra h
  have hz := polymerDist_eq_zero_of_not_disjoint (fun hd => h hd.symm)
  linarith

/-- Distant plaquettes cannot jointly complete a retained two-link product. -/
theorem separated_plaquette_retainedSupport {n : ℕ} (p q : Plaquette 4 (doubleIndex n))
    (hsep : 1 < polymerDist (support p) (support q)) :
    retainedSupport (blockIndexEquiv 4 n) (support p ∪ support q) = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro l hl
  obtain ⟨h0, h1⟩ := (mem_retainedSupport _ _ _).mp hl
  simp only [blockIndexEquiv_first, blockIndexEquiv_second, mem_union] at h0 h1
  have hd := dist_blockEdge_halves_le l
  rcases h0 with h0 | h0 <;> rcases h1 with h1 | h1
  · exact no_blockPair_in_support p l ⟨h0,h1⟩
  · have h := (polymerDist_le_infDist h1).trans (Metric.infDist_le_dist_of_mem h0)
    rw [dist_comm] at h
    exact (not_lt_of_ge (h.trans hd)) hsep
  · have h := (polymerDist_le_infDist h0).trans (Metric.infDist_le_dist_of_mem h1)
    exact (not_lt_of_ge (h.trans hd)) hsep
  · exact no_blockPair_in_support q l ⟨h0,h1⟩

/-- A positive, gauge-invariant density coupling two plaquette traces. It
is an engineered calibration density, not a nearest-neighbour Wilson action. -/
def plaquetteCorrelationDensity {n : ℕ} (ε : ℝ) (p q : Plaquette 4 n) : C(Link 4 n → SU2, ℝ) :=
  Blocking.correlationDensity ε (plaquetteTrace p) (plaquetteTrace q)

theorem plaquetteCorrelationDensity_pos {n : ℕ} {ε : ℝ} (hε : |ε| < 1)
    (p q : Plaquette 4 n) (U : Link 4 n → SU2) : 0 < plaquetteCorrelationDensity ε p q U :=
  Blocking.correlationDensity_pos hε _ _ (abs_plaquetteTrace_le p) (abs_plaquetteTrace_le q) U

theorem plaquetteCorrelationDensity_gauge {n : ℕ} (ε : ℝ) (p q : Plaquette 4 n)
    (g : Site 4 n → SU2) (U : Link 4 n → SU2) :
    plaquetteCorrelationDensity ε p q (gaugeAct g U) = plaquetteCorrelationDensity ε p q U := by
  change 1 + ε * (plaquetteTrace p (gaugeAct g U) * plaquetteTrace q (gaugeAct g U)) = _
  rw [plaquetteTrace_gauge, plaquetteTrace_gauge]
  rfl

/-- Exact positive covariance at arbitrary separation, despite a constant
complete coarse density and zero transported original marks. -/
theorem plaquetteCorrelation_projection {n : ℕ} {ε : ℝ} (hε : |ε| < 1)
    (p q : Plaquette 4 (doubleIndex n)) (hsep : 1 < polymerDist (support p) (support q)) :
    let W := plaquetteCorrelationDensity ε p q
    let hW := plaquetteCorrelationDensity_pos hε p q
    let P := blockedProject volume (blockIndexEquiv 4 n) W hW
    blockedDensity volume (blockIndexEquiv 4 n) W = 1 ∧ P (plaquetteTrace p) = 0 ∧
      P (plaquetteTrace q) = 0 ∧
      P (plaquetteTrace p * plaquetteTrace q) = (ε * plaquetteHaarVariance^2) • 1 ∧
      covariance volume W (plaquetteTrace p) (plaquetteTrace q) = ε * plaquetteHaarVariance^2 := by
  have h := Blocking.correlationDensity_projection (volume : Measure SU2) (blockIndexEquiv 4 n)
    (support p) (support q) (separated_plaquette_disjoint p q hsep)
    (separated_plaquette_retainedSupport p q hsep) ε (plaquetteTrace p) (plaquetteTrace q)
    (plaquetteTrace_local p) (plaquetteTrace_local q)
    (integral_plaquetteTrace_zero p) (integral_plaquetteTrace_zero q)
    (plaquetteCorrelationDensity_pos hε p q)
  simp only [← MeasureTheory.volume_pi] at h
  rw [integral_plaquetteTrace_sq, integral_plaquetteTrace_sq] at h
  simpa only [plaquetteCorrelationDensity, mul_assoc, ← pow_two] using h

/-- The retained variables remain nondegenerate: coarse Wilson plaquettes
are exactly transported and have a fixed strictly positive Haar variance. -/
theorem retained_plaquette_variance {n : ℕ} {ε : ℝ} (hε : |ε| < 1)
    (p q : Plaquette 4 (doubleIndex n)) (hsep : 1 < polymerDist (support p) (support q))
    (r : Plaquette 4 n) :
    let W := plaquetteCorrelationDensity ε p q
    let hW := plaquetteCorrelationDensity_pos hε p q
    blockedProject volume (blockIndexEquiv 4 n) W hW (retainedWilsonObservable r) = plaquetteTrace r ∧
      covariance volume (blockedDensity volume (blockIndexEquiv 4 n) W)
        (plaquetteTrace r) (plaquetteTrace r) = plaquetteHaarVariance ∧ 0 < plaquetteHaarVariance := by
  refine ⟨blockedProject_lift volume _ _ _ _, ?_, plaquetteHaarVariance_pos⟩
  rw [(plaquetteCorrelation_projection hε p q hsep).1]
  exact covariance_plaquetteTrace_haar r

/-- A constant complete coarse interaction cannot, by itself, imply a
volume-uniform spatial covariance bound under this actual Haar block map.
The family uses gauge-invariant local marks and strictly positive densities. -/
theorem no_uniform_covariance_bound :
    ¬ ∃ C κ : ℝ, 0 < κ ∧ ∀ n : ℕ,
      let p := transversePlaquette n 0
      let q := transversePlaquette n (n+3)
      |covariance volume (plaquetteCorrelationDensity (1/2) p q) (plaquetteTrace p) (plaquetteTrace q)| ≤
        C * Real.exp (-κ * polymerDist (support p) (support q)) := by
  rintro ⟨C, κ, hκ, hb⟩
  have hc : 0 < (1/2 : ℝ) * plaquetteHaarVariance^2 := by
    have := plaquetteHaarVariance_pos
    positivity
  have hle (n : ℕ) : (1/2 : ℝ) * plaquetteHaarVariance^2 ≤ |C| * Real.exp (-κ*((n : ℝ)+3)) := by
    have hsep : 1 < polymerDist (support (transversePlaquette n 0))
        (support (transversePlaquette n (n+3))) := lt_of_lt_of_le
      (by have := Nat.cast_nonneg (α := ℝ) n; linarith) (transverse_separation n)
    have he := (plaquetteCorrelation_projection (by norm_num : |(1/2 : ℝ)| < 1)
      (transversePlaquette n 0) (transversePlaquette n (n+3)) hsep).2.2.2.2
    have h := hb n
    dsimp only at h
    rw [he, abs_of_pos hc] at h
    apply h.trans
    apply mul_le_mul (le_abs_self C) _ (Real.exp_pos _).le (abs_nonneg C)
    apply Real.exp_le_exp.mpr
    nlinarith [transverse_separation n]
  have ht : Filter.Tendsto (fun n : ℕ => κ*((n : ℝ)+3)) Filter.atTop Filter.atTop :=
    (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds).const_mul_atTop hκ
  have he : Filter.Tendsto (fun n : ℕ => Real.exp (-κ*((n : ℝ)+3))) Filter.atTop (𝓝 0) := by
    simpa only [Function.comp_def, neg_mul] using Real.tendsto_exp_neg_atTop_nhds_zero.comp ht
  have hz := he.const_mul |C|
  rw [mul_zero] at hz
  exact (not_le_of_gt hc) (ge_of_tendsto' hz hle)

end Mettapedia.QuantumTheory.YangMills.MarginalBlindness.SU2Blocking
