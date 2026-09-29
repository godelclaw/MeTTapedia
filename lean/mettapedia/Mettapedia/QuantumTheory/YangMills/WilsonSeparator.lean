import Mettapedia.QuantumTheory.YangMills.WilsonBlockElimination

/-!
# Separator-sensitive correlation transport

An exact boundary elimination preserves two-marked correlations when the two
interiors decouple after conditioning on the retained separator. A bounded
positive interaction between those interiors gives an explicit error bound
depending on its distortion, rather than on the size of either interior.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory
open scoped Topology BigOperators

namespace Mettapedia.QuantumTheory.YangMills.WilsonSeparator

open WilsonBlockElimination CompactTransferGap

section Perturbation

variable {X : Type*} [TopologicalSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X]
  (μ : Measure X) [IsProbabilityMeasure μ]

theorem expectation_const (W : C(X, ℝ)) (hW : ∀ x, 0 < W x) (c : ℝ) :
    expectation μ W (ContinuousMap.const X c) = c := by
  simp only [expectation, ContinuousMap.const_apply]
  rw [integral_mul_const]
  exact mul_div_cancel_left₀ c (partition_pos μ W hW).ne'

omit [CompactSpace X] [BorelSpace X] [IsProbabilityMeasure μ] in
theorem expectation_const_mul (W F : C(X, ℝ)) (c : ℝ) :
    expectation μ W (ContinuousMap.const X c * F) = c * expectation μ W F := by
  simp only [expectation, ContinuousMap.mul_apply, ContinuousMap.const_apply]
  simp_rw [mul_left_comm (W _) c]
  rw [integral_const_mul, mul_div_assoc]

theorem expectation_mono (W F G : C(X, ℝ)) (hW : ∀ x, 0 < W x)
    (hFG : ∀ x, F x ≤ G x) : expectation μ W F ≤ expectation μ W G := by
  apply div_le_div_of_nonneg_right _ (partition_pos μ W hW).le
  exact integral_mono
    (IntegralKernel.integrable_continuous_fun μ (by fun_prop))
    (IntegralKernel.integrable_continuous_fun μ (by fun_prop))
    (fun x => mul_le_mul_of_nonneg_left (hFG x) (hW x).le)

theorem expectation_reweight (W R F : C(X, ℝ)) (hW : ∀ x, 0 < W x)
    (hR : ∀ x, 0 < R x) :
    expectation μ (W * R) F = expectation μ W (R * F) / expectation μ W R := by
  have hZ := (partition_pos μ W hW).ne'
  have hZR := (partition_pos μ (W * R) (fun x => mul_pos (hW x) (hR x))).ne'
  simp only [expectation, ContinuousMap.mul_apply] at *
  simp_rw [mul_assoc]
  field_simp

/-- The change in an expectation is bounded by the distortion of the actual
positive reweighting factor. No covariance estimate is an input. -/
theorem expectation_reweight_error (W R F : C(X, ℝ)) (hW : ∀ x, 0 < W x)
    {l u M : ℝ} (hl : 0 < l) (hRl : ∀ x, l ≤ R x) (hRu : ∀ x, R x ≤ u)
    (hM : 0 ≤ M) (hF : ∀ x, |F x| ≤ M) :
    |expectation μ (W * R) F - expectation μ W F| ≤ (u / l - 1) * M := by
  let c := expectation μ W R
  have hlc : l ≤ c := by
    simpa only [expectation_const μ W hW] using
      expectation_mono μ W (ContinuousMap.const X l) R hW hRl
  have hcu : c ≤ u := by
    simpa only [expectation_const μ W hW] using
      expectation_mono μ W R (ContinuousMap.const X u) hW hRu
  have hc : 0 < c := hl.trans_le hlc
  have hlu : l ≤ u := hlc.trans hcu
  have hD : ∀ x, |((R - ContinuousMap.const X c) * F) x| ≤ (u - l) * M := by
    intro x
    simp only [ContinuousMap.mul_apply, ContinuousMap.sub_apply, ContinuousMap.const_apply, abs_mul]
    have hr : |R x - c| ≤ u - l := abs_le.mpr ⟨by linarith [hRl x], by linarith [hRu x]⟩
    exact mul_le_mul hr (hF x) (abs_nonneg _) (sub_nonneg.mpr hlu)
  have hE := abs_expectation_le μ W ((R - ContinuousMap.const X c) * F) hW hD
  have hid : expectation μ (W * R) F - expectation μ W F =
      expectation μ W ((R - ContinuousMap.const X c) * F) / c := by
    rw [sub_mul, expectation_sub, expectation_const_mul,
      expectation_reweight μ W R F hW (fun x => hl.trans_le (hRl x))]
    change expectation μ W (R * F) / c - expectation μ W F = _
    field_simp
  rw [hid, abs_div, abs_of_pos hc]
  calc
    |expectation μ W ((R - ContinuousMap.const X c) * F)| / c ≤ ((u - l) * M) / c :=
      div_le_div_of_nonneg_right hE hc.le
    _ ≤ ((u - l) * M) / l :=
      div_le_div_of_nonneg_left (mul_nonneg (sub_nonneg.mpr hlu) hM) hl hlc
    _ = (u / l - 1) * M := by field_simp

/-- A bounded change of density changes a covariance by at most three
expectation errors. The constant is uniform in the underlying space. -/
theorem covariance_reweight_error (W R F G : C(X, ℝ)) (hW : ∀ x, 0 < W x)
    {l u M N : ℝ} (hl : 0 < l) (hRl : ∀ x, l ≤ R x) (hRu : ∀ x, R x ≤ u)
    (hM : 0 ≤ M) (hN : 0 ≤ N) (hF : ∀ x, |F x| ≤ M) (hG : ∀ x, |G x| ≤ N) :
    |covariance μ (W * R) F G - covariance μ W F G| ≤ 3 * (u / l - 1) * M * N := by
  have hWR : ∀ x, 0 < (W * R) x := fun x => mul_pos (hW x) (hl.trans_le (hRl x))
  have hFG : ∀ x, |(F * G) x| ≤ M * N := by
    intro x
    simpa only [ContinuousMap.mul_apply, abs_mul] using
      mul_le_mul (hF x) (hG x) (abs_nonneg _) hM
  have h₀ := expectation_reweight_error μ W R (F * G) hW hl hRl hRu
    (mul_nonneg hM hN) hFG
  have h₁ := expectation_reweight_error μ W R F hW hl hRl hRu hM hF
  have h₂ := expectation_reweight_error μ W R G hW hl hRl hRu hN hG
  have h₃ := abs_expectation_le μ (W * R) G hWR hG
  have h₄ := abs_expectation_le μ W F hW hF
  have hid : covariance μ (W * R) F G - covariance μ W F G =
      (expectation μ (W * R) (F * G) - expectation μ W (F * G)) -
      (expectation μ (W * R) F - expectation μ W F) * expectation μ (W * R) G -
      expectation μ W F * (expectation μ (W * R) G - expectation μ W G) := by
    unfold covariance
    ring
  rw [hid]
  calc
    _ ≤ |expectation μ (W * R) (F * G) - expectation μ W (F * G)| +
        |expectation μ (W * R) F - expectation μ W F| * |expectation μ (W * R) G| +
        |expectation μ W F| * |expectation μ (W * R) G - expectation μ W G| := by
      have ht (a b c : ℝ) : |a - b - c| ≤ |a| + |b| + |c| :=
        (abs_sub (a - b) c).trans (add_le_add (abs_sub a b) (le_refl |c|))
      simpa only [abs_mul] using ht
        (expectation μ (W * R) (F * G) - expectation μ W (F * G))
        ((expectation μ (W * R) F - expectation μ W F) * expectation μ (W * R) G)
        (expectation μ W F * (expectation μ (W * R) G - expectation μ W G))
    _ ≤ (u / l - 1) * (M * N) + ((u / l - 1) * M) * N + M * ((u / l - 1) * N) := by
      have hq : 0 ≤ u / l - 1 := by
        have hnonempty : Nonempty X := nonempty_of_isProbabilityMeasure μ
        obtain ⟨x⟩ := hnonempty
        exact sub_nonneg.mpr ((le_div_iff₀ hl).mpr (by linarith [hRl x, hRu x]))
      exact add_le_add (add_le_add h₀
        (mul_le_mul h₁ h₃ (abs_nonneg _) (mul_nonneg hq hM)))
        (mul_le_mul h₄ h₂ (abs_nonneg _) hM)
    _ = _ := by ring

end Perturbation

section Product

variable {I J : Type*}
  [TopologicalSpace I] [CompactSpace I] [MeasurableSpace I] [BorelSpace I]
  [SecondCountableTopology I]
  [TopologicalSpace J] [CompactSpace J] [MeasurableSpace J] [BorelSpace J]
  [SecondCountableTopology J]
  (ν : Measure I) (ρ : Measure J) [IsProbabilityMeasure ν] [IsProbabilityMeasure ρ]

/-- Product of observables or weights on independent coordinates. -/
def tensor (F : C(I, ℝ)) (G : C(J, ℝ)) : C(I × J, ℝ) :=
  ⟨fun p => F p.1 * G p.2, by fun_prop⟩

theorem integral_tensor (F : C(I, ℝ)) (G : C(J, ℝ)) :
    (∫ p, tensor F G p ∂ν.prod ρ) = (∫ i, F i ∂ν) * ∫ j, G j ∂ρ := by
  rw [integral_prod _ (IntegralKernel.integrable_continuous_fun _ (tensor F G).continuous)]
  simp only [tensor, ContinuousMap.coe_mk, integral_const_mul, integral_mul_const]

/-- Factorization under the normalized product density. -/
theorem expectation_tensor (U F : C(I, ℝ)) (V G : C(J, ℝ)) :
    expectation (ν.prod ρ) (tensor U V) (tensor F G) =
      expectation ν U F * expectation ρ V G := by
  have hmul : tensor U V * tensor F G = tensor (U * F) (V * G) := by
    ext p
    simp only [tensor, ContinuousMap.coe_mk, ContinuousMap.mul_apply]
    ring
  change (∫ p, (tensor U V * tensor F G) p ∂ν.prod ρ) /
    (∫ p, tensor U V p ∂ν.prod ρ) = _
  rw [hmul, integral_tensor, integral_tensor]
  simp only [expectation, ContinuousMap.mul_apply]
  exact mul_div_mul_comm _ _ _ _

theorem covariance_tensor_zero (U F : C(I, ℝ)) (V G : C(J, ℝ))
    (hU : ∀ i, 0 < U i) (hV : ∀ j, 0 < V j) :
    covariance (ν.prod ρ) (tensor U V) (tensor F 1) (tensor 1 G) = 0 := by
  have hmul : tensor F (1 : C(J, ℝ)) * tensor (1 : C(I, ℝ)) G = tensor F G := by
    ext p
    simp [tensor]
  rw [covariance, hmul, expectation_tensor, expectation_tensor, expectation_tensor,
    expectation_one ν U hU, expectation_one ρ V hV]
  ring

end Product

section Separator

variable {B I J : Type*}
  [TopologicalSpace B] [CompactSpace B] [MeasurableSpace B] [BorelSpace B]
  [SecondCountableTopology B]
  [TopologicalSpace I] [CompactSpace I] [MeasurableSpace I] [BorelSpace I]
  [SecondCountableTopology I]
  [TopologicalSpace J] [CompactSpace J] [MeasurableSpace J] [BorelSpace J]
  [SecondCountableTopology J]
  (μ : Measure B) (ν : Measure I) (ρ : Measure J)
  [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] [IsProbabilityMeasure ρ]

/-- An observable involving only the separator and the left interior. -/
def fromLeft (F : C(B × I, ℝ)) : C(B × (I × J), ℝ) :=
  ⟨fun p => F (p.1, p.2.1), by fun_prop⟩

/-- An observable involving only the separator and the right interior. -/
def fromRight (G : C(B × J, ℝ)) : C(B × (I × J), ℝ) :=
  ⟨fun p => G (p.1, p.2.2), by fun_prop⟩

/-- A density with no factor linking the two interiors at fixed separator. -/
def separated (U : C(B × I, ℝ)) (V : C(B × J, ℝ)) : C(B × (I × J), ℝ) :=
  fromLeft U * fromRight V

omit [CompactSpace B] [MeasurableSpace B] [BorelSpace B] [SecondCountableTopology B]
  [CompactSpace I] [MeasurableSpace I] [BorelSpace I] [SecondCountableTopology I]
  [CompactSpace J] [MeasurableSpace J] [BorelSpace J] [SecondCountableTopology J] in
theorem separated_pos (U : C(B × I, ℝ)) (V : C(B × J, ℝ))
    (hU : ∀ p, 0 < U p) (hV : ∀ p, 0 < V p) (p : B × (I × J)) :
    0 < separated U V p := mul_pos (hU _) (hV _)

omit [MeasurableSpace B] [BorelSpace B] in
/-- Conditional independence is proved from the factors of the density. -/
theorem fiberCovariance_separated (U F : C(B × I, ℝ)) (V G : C(B × J, ℝ))
    (hU : ∀ p, 0 < U p) (hV : ∀ p, 0 < V p) :
    fiberCovariance (ν.prod ρ) (separated U V) (separated_pos U V hU hV)
      (fromLeft F) (fromRight G) = 0 := by
  ext b
  change covariance (ν.prod ρ) (tensor (U.curry b) (V.curry b))
    (fromLeft F |>.curry b) (fromRight G |>.curry b) = 0
  have hF : (fromLeft F (J := J)).curry b = tensor (F.curry b) 1 := by
    ext p
    simp [fromLeft, tensor]
  have hG : (fromRight G (I := I)).curry b = tensor 1 (G.curry b) := by
    ext p
    simp [fromRight, tensor]
  rw [hF, hG]
  exact covariance_tensor_zero ν ρ _ _ _ _ (fun i => hU (b, i)) (fun j => hV (b, j))

/-- Exact two-marked transport when the retained boundary separates the sources. -/
theorem covariance_transport_exact (U F : C(B × I, ℝ)) (V G : C(B × J, ℝ))
    (hU : ∀ p, 0 < U p) (hV : ∀ p, 0 < V p) :
    covariance (μ.prod (ν.prod ρ)) (separated U V) (fromLeft F) (fromRight G) =
      covariance μ (marginal (ν.prod ρ) (separated U V))
        (project (ν.prod ρ) (separated U V) (separated_pos U V hU hV) (fromLeft F))
        (project (ν.prod ρ) (separated U V) (separated_pos U V hU hV) (fromRight G)) := by
  rw [covariance_decomposition μ (ν.prod ρ) _ (separated_pos U V hU hV),
    fiberCovariance_separated ν ρ U F V G hU hV]
  simp [expectation]

omit [MeasurableSpace B] [BorelSpace B] in
/-- Only the distortion of the factor coupling the interiors enters this
conditional-covariance bound. The two internal weights can be arbitrarily large. -/
theorem fiberCovariance_interaction_le
    (U F : C(B × I, ℝ)) (V G : C(B × J, ℝ)) (R : C(B × (I × J), ℝ))
    (hU : ∀ p, 0 < U p) (hV : ∀ p, 0 < V p)
    {l u M N : ℝ} (hl : 0 < l) (hRl : ∀ p, l ≤ R p) (hRu : ∀ p, R p ≤ u)
    (hM : 0 ≤ M) (hN : 0 ≤ N) (hF : ∀ p, |F p| ≤ M) (hG : ∀ p, |G p| ≤ N)
    (b : B) :
    |fiberCovariance (ν.prod ρ) (separated U V * R)
      (fun p => mul_pos (separated_pos U V hU hV p) (hl.trans_le (hRl p)))
      (fromLeft F) (fromRight G) b| ≤ 3 * (u / l - 1) * M * N := by
  have h := covariance_reweight_error (ν.prod ρ)
    ((separated U V).curry b) (R.curry b) ((fromLeft F).curry b) ((fromRight G).curry b)
    (fun p => separated_pos U V hU hV (b, p)) hl
    (fun p => hRl (b, p)) (fun p => hRu (b, p)) hM hN
    (fun p => hF (b, p.1)) (fun p => hG (b, p.2))
  have hz : covariance (ν.prod ρ) ((separated U V).curry b)
      ((fromLeft F).curry b) ((fromRight G).curry b) = 0 :=
    congrArg (fun H : C(B, ℝ) => H b) (fiberCovariance_separated ν ρ U F V G hU hV)
  rw [hz, sub_zero] at h
  exact h

/-- The same interaction bound controls the error in the actual full-volume
correlation after exact boundary elimination. -/
theorem covariance_transport_interaction_le
    (U F : C(B × I, ℝ)) (V G : C(B × J, ℝ)) (R : C(B × (I × J), ℝ))
    (hU : ∀ p, 0 < U p) (hV : ∀ p, 0 < V p)
    {l u M N : ℝ} (hl : 0 < l) (hRl : ∀ p, l ≤ R p) (hRu : ∀ p, R p ≤ u)
    (hM : 0 ≤ M) (hN : 0 ≤ N) (hF : ∀ p, |F p| ≤ M) (hG : ∀ p, |G p| ≤ N) :
    let W := separated U V * R
    let hW := fun p => mul_pos (separated_pos U V hU hV p) (hl.trans_le (hRl p))
    |covariance (μ.prod (ν.prod ρ)) W (fromLeft F) (fromRight G) -
      covariance μ (marginal (ν.prod ρ) W)
        (project (ν.prod ρ) W hW (fromLeft F))
        (project (ν.prod ρ) W hW (fromRight G))| ≤ 3 * (u / l - 1) * M * N := by
  exact covariance_transport_error_le μ (ν.prod ρ) _ _ _ _
    (fiberCovariance_interaction_le ν ρ U F V G R hU hV hl hRl hRu hM hN hF hG)

end Separator

section Boltzmann

variable {X : Type*} [TopologicalSpace X]

/-- A finite product of the actual interaction factors. -/
def interaction {q : ℕ} (φ : Fin q → C(X, ℝ)) (β : ℝ) : C(X, ℝ) :=
  ⟨fun x => Real.exp (-β * ∑ p, φ p x), by fun_prop⟩

theorem interaction_eq_prod {q : ℕ} (φ : Fin q → C(X, ℝ)) (β : ℝ) (x : X) :
    interaction φ β x = ∏ p, Real.exp (-β * φ p x) := by
  simp only [interaction, ContinuousMap.coe_mk, Finset.mul_sum, Real.exp_sum]

theorem interaction_pos {q : ℕ} (φ : Fin q → C(X, ℝ)) (β : ℝ) (x : X) :
    0 < interaction φ β x := Real.exp_pos _

/-- The distortion depends only on the number of coupling factors. -/
theorem interaction_bounds {q : ℕ} (φ : Fin q → C(X, ℝ)) {β : ℝ} (hβ : 0 ≤ β)
    (hφ : ∀ p x, 0 ≤ φ p x ∧ φ p x ≤ 2) (x : X) :
    Real.exp (-2 * β * q) ≤ interaction φ β x ∧ interaction φ β x ≤ 1 := by
  have hs₀ : 0 ≤ ∑ p, φ p x := Finset.sum_nonneg (fun p _ => (hφ p x).1)
  have hs₂ : (∑ p, φ p x) ≤ (q : ℝ) * 2 := by
    simpa using Finset.sum_le_sum (s := Finset.univ) (fun p _ => (hφ p x).2)
  constructor
  · apply Real.exp_le_exp.mpr
    nlinarith
  · exact Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hβ) hs₀)

variable {E : Type*} [Group E] [TopologicalSpace E] [IsTopologicalGroup E]

/-- The potential of an oriented Wilson plaquette, using the existing holonomy. -/
def plaquettePotential (ψ : C(E, ℝ)) (v : Fin 4 → C(X, E)) : C(X, ℝ) :=
  ⟨fun x => ψ (StrongCouplingTwist.holonomy (fun i => v i x)), by
    change Continuous (fun x => ψ (v 0 x * v 1 x * (v 2 x)⁻¹ * (v 3 x)⁻¹))
    fun_prop⟩

theorem plaquettePotential_bounds (ψ : C(E, ℝ)) (hψ : ∀ g, 0 ≤ ψ g ∧ ψ g ≤ 2)
    (v : Fin 4 → C(X, E)) (x : X) :
    0 ≤ plaquettePotential ψ v x ∧ plaquettePotential ψ v x ≤ 2 := hψ _

end Boltzmann

section WilsonBound

variable {B I J : Type*}
  [TopologicalSpace B] [CompactSpace B] [MeasurableSpace B] [BorelSpace B]
  [SecondCountableTopology B]
  [TopologicalSpace I] [CompactSpace I] [MeasurableSpace I] [BorelSpace I]
  [SecondCountableTopology I]
  [TopologicalSpace J] [CompactSpace J] [MeasurableSpace J] [BorelSpace J]
  [SecondCountableTopology J]
  (μ : Measure B) (ν : Measure I) (ρ : Measure J)
  [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] [IsProbabilityMeasure ρ]

omit [MeasurableSpace B] [BorelSpace B] in
/-- The pointwise remainder bound from `q` actual bounded interaction factors. -/
theorem fiberCovariance_boltzmann_le
    (U F : C(B × I, ℝ)) (V G : C(B × J, ℝ))
    (hU : ∀ p, 0 < U p) (hV : ∀ p, 0 < V p)
    {q : ℕ} (φ : Fin q → C(B × (I × J), ℝ)) {β : ℝ} (hβ : 0 ≤ β)
    (hφ : ∀ p x, 0 ≤ φ p x ∧ φ p x ≤ 2)
    {M N : ℝ} (hM : 0 ≤ M) (hN : 0 ≤ N)
    (hF : ∀ p, |F p| ≤ M) (hG : ∀ p, |G p| ≤ N) (b : B) :
    |fiberCovariance (ν.prod ρ) (separated U V * interaction φ β)
      (fun p => mul_pos (separated_pos U V hU hV p) (interaction_pos φ β p))
      (fromLeft F) (fromRight G) b| ≤ 3 * (Real.exp (2 * β * q) - 1) * M * N := by
  have h := fiberCovariance_interaction_le ν ρ U F V G (interaction φ β) hU hV
    (Real.exp_pos (-2 * β * q))
    (fun p => (interaction_bounds φ hβ hφ p).1)
    (fun p => (interaction_bounds φ hβ hφ p).2) hM hN hF hG b
  simpa only [one_div, ← Real.exp_neg, neg_mul, neg_neg] using h

variable {E : Type*} [Group E] [TopologicalSpace E] [IsTopologicalGroup E]

omit [MeasurableSpace B] [BorelSpace B] in
/-- A Wilson specialization: each mixed factor is the potential of its actual
four ordered links. No assumption on the covariance appears in the hypotheses. -/
theorem fiberCovariance_wilson_le
    (U F : C(B × I, ℝ)) (V G : C(B × J, ℝ))
    (hU : ∀ p, 0 < U p) (hV : ∀ p, 0 < V p)
    {q : ℕ} (ψ : C(E, ℝ)) (hψ : ∀ g, 0 ≤ ψ g ∧ ψ g ≤ 2)
    (v : Fin q → Fin 4 → C(B × (I × J), E)) {β : ℝ} (hβ : 0 ≤ β)
    {M N : ℝ} (hM : 0 ≤ M) (hN : 0 ≤ N)
    (hF : ∀ p, |F p| ≤ M) (hG : ∀ p, |G p| ≤ N) (b : B) :
    let φ := fun p => plaquettePotential ψ (v p)
    |fiberCovariance (ν.prod ρ) (separated U V * interaction φ β)
      (fun p => mul_pos (separated_pos U V hU hV p) (interaction_pos φ β p))
      (fromLeft F) (fromRight G) b| ≤ 3 * (Real.exp (2 * β * q) - 1) * M * N :=
  fiberCovariance_boltzmann_le ν ρ U F V G hU hV _ hβ
    (fun p x => plaquettePotential_bounds ψ hψ (v p) x) hM hN hF hG b

/-- The derived Wilson bound controls the full correlation-transport error. -/
theorem covariance_transport_wilson_le
    (U F : C(B × I, ℝ)) (V G : C(B × J, ℝ))
    (hU : ∀ p, 0 < U p) (hV : ∀ p, 0 < V p)
    {q : ℕ} (ψ : C(E, ℝ)) (hψ : ∀ g, 0 ≤ ψ g ∧ ψ g ≤ 2)
    (v : Fin q → Fin 4 → C(B × (I × J), E)) {β : ℝ} (hβ : 0 ≤ β)
    {M N : ℝ} (hM : 0 ≤ M) (hN : 0 ≤ N)
    (hF : ∀ p, |F p| ≤ M) (hG : ∀ p, |G p| ≤ N) :
    let φ := fun p => plaquettePotential ψ (v p)
    let W := separated U V * interaction φ β
    let hW := fun p => mul_pos (separated_pos U V hU hV p) (interaction_pos φ β p)
    |covariance (μ.prod (ν.prod ρ)) W (fromLeft F) (fromRight G) -
      covariance μ (marginal (ν.prod ρ) W)
        (project (ν.prod ρ) W hW (fromLeft F))
        (project (ν.prod ρ) W hW (fromRight G))| ≤ 3 * (Real.exp (2 * β * q) - 1) * M * N := by
  exact covariance_transport_error_le μ (ν.prod ρ) _ _ _ _
    (fiberCovariance_wilson_le ν ρ U F V G hU hV ψ hψ v hβ hM hN hF hG)

end WilsonBound

#print axioms expectation_reweight_error
#print axioms covariance_reweight_error
#print axioms fiberCovariance_separated
#print axioms covariance_transport_exact
#print axioms covariance_transport_interaction_le
#print axioms interaction_bounds
#print axioms fiberCovariance_wilson_le
#print axioms covariance_transport_wilson_le

end Mettapedia.QuantumTheory.YangMills.WilsonSeparator
