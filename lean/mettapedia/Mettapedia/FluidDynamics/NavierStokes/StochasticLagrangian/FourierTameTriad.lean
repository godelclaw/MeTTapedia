import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeHigherSobolevWeights
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeHigherSobolevWindow
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeInfinitePressureCoefficients
import Mathlib.Algebra.Module.ZLattice.Summable
import Mathlib.Analysis.MeanInequalities

/-!
# A tame bound for the higher-order Fourier triad

The existing order-`m` triad estimate controls the convolution by
`E_m √D_m`, which is quadratic in the top norm after absorption and only
gives a local window. Here the same two Young inequalities are kept with
the Wiener sums

```text
W₀ = ∑ aₖ,   W₁ = ∑ |k| aₖ,
orderTriad ≤ 2^m (E_m W₁ + W₀ √(E_m D_m)).
```

The lattice sum `∑ (1+|k|)^(-7/2)` is finite, so both Wiener sums are
controlled by intermediate weighted energies with fewer than two extra
derivatives. Hölder interpolation between the order-one energy `E₁` and the
dissipation `D_m` (which bounds the order-`(m+1)` energy on nonzero modes)
then gives

```text
orderTriad ≤ C E₁^(1/2 + 1/(8m)) D_m^(1 - 1/(8m)),
```

strictly below the dissipation exponent one. Hence, for every `ε > 0`,
`orderTriad ≤ ε D_m + C_ε E₁^(4m+1)`: an order-one bound controls every
higher-order rate. These are inequalities for finite Fourier sums; the
passage to an actual solution is separate.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.FourierTameTriad

open scoped BigOperators
open Filter
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeFrequencyProjectorCommutator
open PancakeFiniteConvolutionL2 PancakeSobolevWeights PancakeHigherSobolevWeights
open PancakeInfinitePressureCoefficients PancakeIndexedFourierMoments
open PancakeSobolevVelocityRate PancakeHigherSobolevVelocityRate PancakeHigherSobolevWindow
open PancakeLocalVelocityExistence PancakeGalerkinKineticEnergy

/-- The Wiener sum of the amplitudes. -/
def wiener0 (M : Finset Wavevector) (a : Wavevector → ℝ) : ℝ := ∑ k ∈ M, a k

/-- The Wiener sum of the frequency-weighted amplitudes. -/
def wiener1 (M : Finset Wavevector) (a : Wavevector → ℝ) : ℝ :=
  ∑ k ∈ M, ‖frequencyVec k‖ * a k

/-! ### The tame triad bound -/

theorem sizeL2_eq_sqrt (M : Finset Wavevector) (a : Wavevector → ℝ) :
    sizeL2 M a = Real.sqrt (∑ q ∈ M, (a q) ^ 2) := rfl

/-- The two Young inequalities of the existing estimate, without converting the
Wiener sums into top-order norms. -/
theorem orderTriad_le_tame (m : ℕ) (M : Finset Wavevector) (a : Wavevector → ℝ)
    (ha : ∀ k, 0 ≤ a k) :
    orderTriad m M a ≤ (2 : ℝ)^m *
      (orderEnergy m M a * wiener1 M a +
        wiener0 M a * Real.sqrt (orderEnergy m M a * orderDissipation m M a)) := by
  let b := fun k ↦ orderWeight m k * a k
  let c := fun k ↦ ‖frequencyVec k‖ * a k
  have hc : ∀ k, 0 ≤ c k := fun k ↦ mul_nonneg (norm_nonneg _) (ha k)
  have hE : sizeL2 M b = Real.sqrt (orderEnergy m M a) := rfl
  have hD : sizeL2 M (fun k ↦ orderWeight m k * c k) =
      Real.sqrt (orderDissipation m M a) := rfl
  have h1 := triadSum_le_rightL1 M b b c (fun k _ ↦ hc k)
  have h2 := triadSum_le_leftL1 M b a (fun k ↦ orderWeight m k * c k) (fun k _ ↦ ha k)
  rw [hE] at h1
  rw [hE, hD] at h2
  have hs := orderTriad_split m M a ha
  change orderTriad m M a ≤ (2 : ℝ)^m *
    (triadSum M b b c + triadSum M b a (fun k ↦ orderWeight m k * c k)) at hs
  have hEn := orderEnergy_nonneg m M a
  have hDn := orderDissipation_nonneg m M a
  have h1' : triadSum M b b c ≤ orderEnergy m M a * wiener1 M a := by
    calc triadSum M b b c ≤ _ := h1
      _ = orderEnergy m M a * wiener1 M a := by
        rw [Real.mul_self_sqrt hEn]
        rfl
  have h2' : triadSum M b a (fun k ↦ orderWeight m k * c k) ≤
      wiener0 M a * Real.sqrt (orderEnergy m M a * orderDissipation m M a) := by
    calc triadSum M b a (fun k ↦ orderWeight m k * c k) ≤ _ := h2
      _ = wiener0 M a * Real.sqrt (orderEnergy m M a * orderDissipation m M a) := by
        rw [Real.sqrt_mul hEn]
        unfold wiener0
        ring
  exact hs.trans (mul_le_mul_of_nonneg_left (add_le_add h1' h2') (by positivity))

/-! ### A lattice sum with fewer than two extra derivatives -/

private abbrev integerLattice : Submodule ℤ (Fin 3 → ℝ) :=
  Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Fin 3)))

private instance : DiscreteTopology integerLattice := ZSpan.discreteTopology_pi_basisFun

private def latticePoint (k : Wavevector) : integerLattice :=
  ⟨fun j ↦ (k j : ℝ), by
    apply ((Pi.basisFun ℝ (Fin 3)).mem_span_iff_repr_mem ℤ _).mpr
    intro j
    exact ⟨k j, by simp⟩⟩

private theorem latticePoint_injective : Function.Injective latticePoint := by
  intro k l h
  funext j
  have hh := congrFun (congrArg Subtype.val h) j
  change (k j : ℝ) = (l j : ℝ) at hh
  exact_mod_cast hh

private theorem latticePoint_zero : latticePoint 0 = 0 := by ext j; simp [latticePoint]

private theorem norm_latticePoint_le (k : Wavevector) :
    ‖latticePoint k‖ ≤ ‖frequencyVec k‖ := by
  change ‖fun j ↦ (k j : ℝ)‖ ≤ _
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
  intro j
  simpa using norm_frequency_coordinate_le k j

/-- The weight `(1+|k|)^(-7/2)`. -/
def tameDecay (k : Wavevector) : ℝ := (1 + ‖frequencyVec k‖) ^ (-(7 / 2 : ℝ))

theorem tameDecay_pos (k : Wavevector) : 0 < tameDecay k :=
  Real.rpow_pos_of_pos (by positivity) _

theorem summable_tameDecay : Summable tameDecay := by
  have hr : Module.finrank ℤ integerLattice = 3 := by
    rw [ZLattice.rank ℝ integerLattice]
    simp
  have hs := (ZLattice.summable_norm_rpow integerLattice (-(7 / 2 : ℝ))
    (by rw [hr]; norm_num)).comp_injective latticePoint_injective
  apply hs.of_norm_bounded_eventually
  filter_upwards [show ∀ᶠ k : Wavevector in cofinite, k ≠ 0 from eventually_cofinite_ne 0]
    with k hk
  have hn : 0 < ‖latticePoint k‖ := norm_pos_iff.mpr (fun hz ↦ hk
    (latticePoint_injective (hz.trans latticePoint_zero.symm)))
  rw [Real.norm_eq_abs, abs_of_pos (tameDecay_pos k)]
  change (1 + ‖frequencyVec k‖) ^ (-(7 / 2 : ℝ)) ≤ ‖latticePoint k‖ ^ (-(7 / 2 : ℝ))
  exact Real.rpow_le_rpow_of_nonpos hn
    ((norm_latticePoint_le k).trans (le_add_of_nonneg_left zero_le_one)) (by norm_num)

/-- The lattice constant of the tame weight. -/
def tameMass : ℝ := ∑' k : Wavevector, tameDecay k

theorem tameMass_nonneg : 0 ≤ tameMass := tsum_nonneg fun k ↦ (tameDecay_pos k).le

theorem sum_tameDecay_le (M : Finset Wavevector) : ∑ k ∈ M, tameDecay k ≤ tameMass :=
  summable_tameDecay.sum_le_tsum M (fun k _ ↦ (tameDecay_pos k).le)

/-- Cauchy–Schwarz against the tame weight: a weighted sum costs `7/4` powers. -/
theorem sum_rpow_mul_le (M : Finset Wavevector) (a : Wavevector → ℝ) (p : ℝ) :
    ∑ k ∈ M, (1 + ‖frequencyVec k‖) ^ p * a k ≤
      Real.sqrt tameMass *
        Real.sqrt (∑ k ∈ M, (1 + ‖frequencyVec k‖) ^ (2 * p + 7 / 2) * a k ^ 2) := by
  have hb (k : Wavevector) : 0 < 1 + ‖frequencyVec k‖ := by positivity
  have he (k : Wavevector) : (1 + ‖frequencyVec k‖) ^ p * a k =
      (1 + ‖frequencyVec k‖) ^ (-(7 / 4 : ℝ)) *
        ((1 + ‖frequencyVec k‖) ^ (p + 7 / 4) * a k) := by
    rw [← mul_assoc, ← Real.rpow_add (hb k)]
    congr 2
    ring
  calc ∑ k ∈ M, (1 + ‖frequencyVec k‖) ^ p * a k
      = ∑ k ∈ M, (1 + ‖frequencyVec k‖) ^ (-(7 / 4 : ℝ)) *
          ((1 + ‖frequencyVec k‖) ^ (p + 7 / 4) * a k) := Finset.sum_congr rfl fun k _ ↦ he k
    _ ≤ Real.sqrt (∑ k ∈ M, ((1 + ‖frequencyVec k‖) ^ (-(7 / 4 : ℝ))) ^ 2) *
          Real.sqrt (∑ k ∈ M, ((1 + ‖frequencyVec k‖) ^ (p + 7 / 4) * a k) ^ 2) :=
        Real.sum_mul_le_sqrt_mul_sqrt M _ _
    _ ≤ _ := by
        apply mul_le_mul _ (le_of_eq _) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
        · apply Real.sqrt_le_sqrt
          apply le_trans (le_of_eq _) (sum_tameDecay_le M)
          refine Finset.sum_congr rfl fun k _ ↦ ?_
          rw [← Real.rpow_natCast, ← Real.rpow_mul (hb k).le]
          unfold tameDecay
          norm_num
        · congr 1
          refine Finset.sum_congr rfl fun k _ ↦ ?_
          rw [mul_pow, ← Real.rpow_natCast, ← Real.rpow_mul (hb k).le]
          congr 2
          push_cast
          ring

/-! ### Hölder interpolation of weighted energies -/

/-- Hölder's inequality for finite sums, in interpolation form. -/
theorem sum_rpow_mul_rpow_le {ι : Type*} (s : Finset ι) (x y : ι → ℝ)
    (hx : ∀ i ∈ s, 0 ≤ x i) (hy : ∀ i ∈ s, 0 ≤ y i) {θ : ℝ} (h0 : 0 < θ) (h1 : θ < 1) :
    ∑ i ∈ s, x i ^ (1 - θ) * y i ^ θ ≤ (∑ i ∈ s, x i) ^ (1 - θ) * (∑ i ∈ s, y i) ^ θ := by
  have hpq : (1 / (1 - θ)).HolderConjugate (1 / θ) := by
    rw [Real.holderConjugate_iff]
    constructor
    · rw [lt_div_iff₀ (by linarith)]
      linarith
    · field_simp
      ring
  have h := Real.inner_le_Lp_mul_Lq_of_nonneg s hpq
    (f := fun i ↦ x i ^ (1 - θ)) (g := fun i ↦ y i ^ θ)
    (fun i hi ↦ Real.rpow_nonneg (hx i hi) _) (fun i hi ↦ Real.rpow_nonneg (hy i hi) _)
  have hf : ∀ i ∈ s, (x i ^ (1 - θ)) ^ (1 / (1 - θ)) = x i := fun i hi ↦ by
    rw [← Real.rpow_mul (hx i hi), mul_one_div_cancel (by linarith), Real.rpow_one]
  have hg : ∀ i ∈ s, (y i ^ θ) ^ (1 / θ) = y i := fun i hi ↦ by
    rw [← Real.rpow_mul (hy i hi), mul_one_div_cancel h0.ne', Real.rpow_one]
  rw [Finset.sum_congr rfl hf, Finset.sum_congr rfl hg, one_div_one_div, one_div_one_div] at h
  exact h

/-- The weighted mass `∑ (1+|k|)^r aₖ²`. -/
def weightedMass (M : Finset Wavevector) (a : Wavevector → ℝ) (r : ℝ) : ℝ :=
  ∑ k ∈ M, (1 + ‖frequencyVec k‖) ^ r * a k ^ 2

theorem weightedMass_nonneg (M : Finset Wavevector) (a : Wavevector → ℝ) (r : ℝ) :
    0 ≤ weightedMass M a r :=
  Finset.sum_nonneg fun _ _ ↦ mul_nonneg (Real.rpow_nonneg (by positivity) _) (sq_nonneg _)

theorem orderEnergy_eq_weightedMass (n : ℕ) (M : Finset Wavevector) (a : Wavevector → ℝ) :
    orderEnergy n M a = weightedMass M a (2 * n) := by
  unfold orderEnergy weightedMass orderWeight
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [mul_pow, ← pow_mul, ← Real.rpow_natCast]
  congr 2
  push_cast
  ring

/-- On nonzero modes the order-`(m+1)` mass is controlled by the order-`m`
dissipation. -/
theorem weightedMass_top_le (m : ℕ) (M : Finset Wavevector) (a : Wavevector → ℝ)
    (hM : ∀ k ∈ M, k ≠ 0) :
    weightedMass M a (2 * m + 2) ≤ 4 * orderDissipation m M a := by
  unfold weightedMass orderDissipation orderEnergy orderWeight
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun k hk ↦ ?_
  have ht := one_le_norm_frequencyVec (hM k hk)
  set t := ‖frequencyVec k‖
  have hexp : (1 + t) ^ (2 * (m : ℝ) + 2) = ((1 + t) ^ m) ^ 2 * (1 + t) ^ 2 := by
    rw [show (2 * (m : ℝ) + 2) = ((2 * m + 2 : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast]
    ring
  have h2 : (1 + t) ^ 2 ≤ 4 * t ^ 2 := by nlinarith
  have hw : 0 ≤ ((1 + t) ^ m) ^ 2 * a k ^ 2 := by positivity
  rw [hexp]
  calc ((1 + t) ^ m) ^ 2 * (1 + t) ^ 2 * a k ^ 2
      = (((1 + t) ^ m) ^ 2 * a k ^ 2) * (1 + t) ^ 2 := by ring
    _ ≤ (((1 + t) ^ m) ^ 2 * a k ^ 2) * (4 * t ^ 2) := mul_le_mul_of_nonneg_left h2 hw
    _ = 4 * ((1 + t) ^ m * (t * a k)) ^ 2 := by ring

/-- Interpolation between the order-one and order-`(m+1)` masses. -/
theorem weightedMass_interp (m : ℕ) (hm : 1 ≤ m) (M : Finset Wavevector)
    (a : Wavevector → ℝ) {r : ℝ} (hr2 : 2 < r) (hrm : r < 2 * m + 2) :
    weightedMass M a r ≤
      weightedMass M a 2 ^ (1 - (r - 2) / (2 * m)) *
        weightedMass M a (2 * m + 2) ^ ((r - 2) / (2 * m)) := by
  set θ := (r - 2) / (2 * m) with hθ
  have hm' : (0 : ℝ) < 2 * m := by
    have : (1 : ℝ) ≤ m := by exact_mod_cast hm
    linarith
  have h0 : 0 < θ := div_pos (by linarith) hm'
  have h1 : θ < 1 := by
    rw [hθ, div_lt_one hm']
    linarith
  have hexp : 2 * (1 - θ) + (2 * m + 2) * θ = r := by
    rw [hθ]
    field_simp
    ring
  have hpt : ∀ k ∈ M, (1 + ‖frequencyVec k‖) ^ r * a k ^ 2 =
      ((1 + ‖frequencyVec k‖) ^ (2 : ℝ) * a k ^ 2) ^ (1 - θ) *
        ((1 + ‖frequencyVec k‖) ^ (2 * (m : ℝ) + 2) * a k ^ 2) ^ θ := by
    intro k _
    set t := 1 + ‖frequencyVec k‖
    have ht : 0 < t := by positivity
    have ha : 0 ≤ a k ^ 2 := sq_nonneg _
    rw [Real.mul_rpow (Real.rpow_nonneg ht.le _) ha, Real.mul_rpow (Real.rpow_nonneg ht.le _) ha,
      ← Real.rpow_mul ht.le, ← Real.rpow_mul ht.le]
    rcases ha.eq_or_lt with h | h
    · rw [← h, Real.zero_rpow (by linarith : (1 : ℝ) - θ ≠ 0), Real.zero_rpow h0.ne']
      ring
    · symm
      calc t ^ (2 * (1 - θ)) * (a k ^ 2) ^ (1 - θ) *
            (t ^ ((2 * (m : ℝ) + 2) * θ) * (a k ^ 2) ^ θ)
          = t ^ (2 * (1 - θ)) * t ^ ((2 * (m : ℝ) + 2) * θ) *
              ((a k ^ 2) ^ (1 - θ) * (a k ^ 2) ^ θ) := by ring
        _ = t ^ r * a k ^ 2 := by
          rw [← Real.rpow_add ht, ← Real.rpow_add h, hexp, sub_add_cancel, Real.rpow_one]
  calc weightedMass M a r
      = ∑ k ∈ M, ((1 + ‖frequencyVec k‖) ^ (2 : ℝ) * a k ^ 2) ^ (1 - θ) *
          ((1 + ‖frequencyVec k‖) ^ (2 * (m : ℝ) + 2) * a k ^ 2) ^ θ :=
        Finset.sum_congr rfl hpt
    _ ≤ _ := sum_rpow_mul_rpow_le M _ _
        (fun k _ ↦ mul_nonneg (Real.rpow_nonneg (by positivity) _) (sq_nonneg _))
        (fun k _ ↦ mul_nonneg (Real.rpow_nonneg (by positivity) _) (sq_nonneg _)) h0 h1

/-! ### The Wiener sums through intermediate masses -/

theorem wiener1_le (M : Finset Wavevector) (a : Wavevector → ℝ) (ha : ∀ k, 0 ≤ a k) :
    wiener1 M a ≤ Real.sqrt tameMass * Real.sqrt (weightedMass M a (11 / 2)) := by
  have hle : wiener1 M a ≤ ∑ k ∈ M, (1 + ‖frequencyVec k‖) ^ (1 : ℝ) * a k := by
    unfold wiener1
    refine Finset.sum_le_sum fun k _ ↦ ?_
    rw [Real.rpow_one]
    exact mul_le_mul_of_nonneg_right (by linarith) (ha k)
  have h := sum_rpow_mul_le M a 1
  have hw : weightedMass M a (11 / 2) =
      ∑ k ∈ M, (1 + ‖frequencyVec k‖) ^ (2 * (1 : ℝ) + 7 / 2) * a k ^ 2 := by
    unfold weightedMass
    norm_num
  rw [hw]
  exact hle.trans h

theorem wiener0_le (M : Finset Wavevector) (a : Wavevector → ℝ) :
    wiener0 M a ≤ Real.sqrt tameMass * Real.sqrt (weightedMass M a (7 / 2)) := by
  have he : wiener0 M a = ∑ k ∈ M, (1 + ‖frequencyVec k‖) ^ (0 : ℝ) * a k := by
    unfold wiener0
    simp
  have h := sum_rpow_mul_le M a 0
  have hw : weightedMass M a (7 / 2) =
      ∑ k ∈ M, (1 + ‖frequencyVec k‖) ^ (2 * (0 : ℝ) + 7 / 2) * a k ^ 2 := by
    unfold weightedMass
    norm_num
  rw [he, hw]
  exact h

/-! ### Exponent bookkeeping -/

theorem mul_le_rpow_mul_rpow {e d X Y a₁ b₁ a₂ b₂ : ℝ} (he : 0 ≤ e) (hd : 0 ≤ d)
    (_hX : 0 ≤ X) (hY : 0 ≤ Y) (h1 : X ≤ e ^ a₁ * d ^ b₁) (h2 : Y ≤ e ^ a₂ * d ^ b₂)
    (ha : a₁ + a₂ ≠ 0) (hb : b₁ + b₂ ≠ 0) :
    X * Y ≤ e ^ (a₁ + a₂) * d ^ (b₁ + b₂) := by
  calc X * Y ≤ (e ^ a₁ * d ^ b₁) * (e ^ a₂ * d ^ b₂) :=
        mul_le_mul h1 h2 hY (mul_nonneg (Real.rpow_nonneg he _) (Real.rpow_nonneg hd _))
    _ = (e ^ a₁ * e ^ a₂) * (d ^ b₁ * d ^ b₂) := by ring
    _ = e ^ (a₁ + a₂) * d ^ (b₁ + b₂) := by rw [← Real.rpow_add' he ha, ← Real.rpow_add' hd hb]

theorem sqrt_le_rpow_mul_rpow {e d X a b : ℝ} (he : 0 ≤ e) (hd : 0 ≤ d)
    (h : X ≤ e ^ a * d ^ b) :
    Real.sqrt X ≤ e ^ (a / 2) * d ^ (b / 2) := by
  calc Real.sqrt X ≤ Real.sqrt (e ^ a * d ^ b) := Real.sqrt_le_sqrt h
    _ = e ^ (a / 2) * d ^ (b / 2) := by
      rw [Real.sqrt_eq_rpow, Real.mul_rpow (Real.rpow_nonneg he _) (Real.rpow_nonneg hd _),
        ← Real.rpow_mul he, ← Real.rpow_mul hd]
      ring_nf

/-! ### The subcritical bound and its absorption -/

/-- The order-one energy as a weighted mass. -/
theorem orderEnergy_one_eq (M : Finset Wavevector) (a : Wavevector → ℝ) :
    orderEnergy 1 M a = weightedMass M a 2 := by
  rw [orderEnergy_eq_weightedMass]
  norm_num

/-- **Subcritical triad bound.** On nonzero modes, for `m ≥ 2`,
`orderTriad ≤ 2^(m+1) √L E₁^(1/2 + 1/(8m)) (4 D_m)^(1 - 1/(8m))`. -/
theorem orderTriad_le_subcritical (m : ℕ) (hm : 2 ≤ m) (M : Finset Wavevector)
    (a : Wavevector → ℝ) (ha : ∀ k, 0 ≤ a k) (hM : ∀ k ∈ M, k ≠ 0) :
    orderTriad m M a ≤ (2 : ℝ) ^ (m + 1) * Real.sqrt tameMass *
      orderEnergy 1 M a ^ (1 / 2 + 1 / (8 * m) : ℝ) *
      (4 * orderDissipation m M a) ^ (1 - 1 / (8 * m) : ℝ) := by
  have hm1 : 1 ≤ m := by omega
  have hmR : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hmpos : (0 : ℝ) < m := by linarith
  set e := orderEnergy 1 M a with he_def
  set D := orderDissipation m M a with hD_def
  set d := 4 * D with hd_def
  have he : 0 ≤ e := orderEnergy_nonneg 1 M a
  have hD : 0 ≤ D := orderDissipation_nonneg m M a
  have hd : 0 ≤ d := by positivity
  have hDd : D ≤ d := by linarith
  have hW : weightedMass M a (2 * m + 2) ≤ d := weightedMass_top_le m M a hM
  have hW0 := weightedMass_nonneg M a (2 * m + 2)
  have hE1 : weightedMass M a 2 = e := (orderEnergy_one_eq M a).symm
  have hL : 0 ≤ Real.sqrt tameMass := Real.sqrt_nonneg _
  -- interpolation, pushed to the dissipation
  have interp : ∀ r : ℝ, 2 < r → r < 2 * m + 2 →
      weightedMass M a r ≤ e ^ (1 - (r - 2) / (2 * m)) * d ^ ((r - 2) / (2 * m)) := by
    intro r hr2 hrm
    have h := weightedMass_interp m hm1 M a hr2 hrm
    rw [hE1] at h
    have hθ : 0 ≤ (r - 2) / (2 * m) := div_nonneg (by linarith) (by positivity)
    exact h.trans (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hW0 hW hθ)
      (Real.rpow_nonneg he _))
  set μ : ℝ := (2 * (m : ℝ) - 2) / (2 * m) with hμ
  set l₁ : ℝ := (11 / 2 - 2) / (2 * (m : ℝ)) with hl₁
  set l₀ : ℝ := (7 / 2 - 2) / (2 * (m : ℝ)) with hl₀
  have hEm : orderEnergy m M a ≤ e ^ (1 - μ) * d ^ μ := by
    rw [orderEnergy_eq_weightedMass]
    exact interp (2 * m) (by linarith) (by linarith)
  have h11 : weightedMass M a (11 / 2) ≤ e ^ (1 - l₁) * d ^ l₁ :=
    interp (11 / 2) (by norm_num) (by linarith)
  have h7 : weightedMass M a (7 / 2) ≤ e ^ (1 - l₀) * d ^ l₀ :=
    interp (7 / 2) (by norm_num) (by linarith)
  have hW1 : wiener1 M a ≤ Real.sqrt tameMass * (e ^ ((1 - l₁) / 2) * d ^ (l₁ / 2)) :=
    (wiener1_le M a ha).trans (mul_le_mul_of_nonneg_left
      (sqrt_le_rpow_mul_rpow he hd h11) hL)
  have hW0' : wiener0 M a ≤ Real.sqrt tameMass * (e ^ ((1 - l₀) / 2) * d ^ (l₀ / 2)) :=
    (wiener0_le M a).trans (mul_le_mul_of_nonneg_left
      (sqrt_le_rpow_mul_rpow he hd h7) hL)
  have hEmn := orderEnergy_nonneg m M a
  have hw1n : 0 ≤ wiener1 M a :=
    Finset.sum_nonneg fun k _ ↦ mul_nonneg (norm_nonneg _) (ha k)
  have hw0n : 0 ≤ wiener0 M a := Finset.sum_nonneg fun k _ ↦ ha k
  have hμ1 : 1 - μ = 1 / m := by rw [hμ]; field_simp; ring
  have hβ1 : (1 - μ) + (1 - l₁) / 2 = 1 / 2 + 1 / (8 * m) := by
    rw [hμ1, hl₁]; field_simp; ring
  have hγ1 : μ + l₁ / 2 = 1 - 1 / (8 * m) := by rw [hμ, hl₁]; field_simp; ring
  have hβ2 : (1 - l₀) / 2 + (1 - μ) / 2 = 1 / 2 + 1 / (8 * m) := by
    rw [hμ1, hl₀]; field_simp; ring
  have hγ2 : l₀ / 2 + (μ + 1) / 2 = 1 - 1 / (8 * m) := by rw [hμ, hl₀]; field_simp; ring
  have hβpos : (0 : ℝ) < 1 / 2 + 1 / (8 * m) := by positivity
  have hγpos : (0 : ℝ) < 1 - 1 / (8 * m) := by
    have : 1 / (8 * (m : ℝ)) < 1 := by rw [div_lt_one (by positivity)]; linarith
    linarith
  -- first term
  have hT1 : orderEnergy m M a * wiener1 M a ≤ Real.sqrt tameMass *
      (e ^ (1 / 2 + 1 / (8 * m) : ℝ) * d ^ (1 - 1 / (8 * m) : ℝ)) := by
    rcases hL.eq_or_lt with h0 | hpos
    · have hw1z : wiener1 M a = 0 := by
        have := hW1
        rw [← h0, zero_mul] at this
        linarith
      rw [hw1z, mul_zero, ← h0, zero_mul]
    · have hq : wiener1 M a / Real.sqrt tameMass ≤ e ^ ((1 - l₁) / 2) * d ^ (l₁ / 2) := by
        rw [div_le_iff₀ hpos]
        linarith [hW1]
      have hc := mul_le_rpow_mul_rpow he hd hEmn (div_nonneg hw1n hL) hEm hq
        (by rw [hβ1]; exact hβpos.ne') (by rw [hγ1]; exact hγpos.ne')
      rw [hβ1, hγ1] at hc
      calc orderEnergy m M a * wiener1 M a
          = Real.sqrt tameMass * (orderEnergy m M a * (wiener1 M a / Real.sqrt tameMass)) := by
            field_simp
        _ ≤ _ := mul_le_mul_of_nonneg_left hc hL
  -- second term
  have hT2 : wiener0 M a * Real.sqrt (orderEnergy m M a * D) ≤ Real.sqrt tameMass *
      (e ^ (1 / 2 + 1 / (8 * m) : ℝ) * d ^ (1 - 1 / (8 * m) : ℝ)) := by
    have hμpos : 0 ≤ μ := by rw [hμ]; exact div_nonneg (by linarith) (by positivity)
    have hEmD : orderEnergy m M a * D ≤ e ^ (1 - μ) * d ^ (μ + 1) := by
      rw [Real.rpow_add' hd (by linarith), Real.rpow_one]
      calc orderEnergy m M a * D ≤ (e ^ (1 - μ) * d ^ μ) * d := mul_le_mul hEm hDd hD
              (mul_nonneg (Real.rpow_nonneg he _) (Real.rpow_nonneg hd _))
        _ = _ := by ring
    have hs := sqrt_le_rpow_mul_rpow he hd hEmD
    rcases hL.eq_or_lt with h0 | hpos
    · have hw0z : wiener0 M a = 0 := by
        have := hW0'
        rw [← h0, zero_mul] at this
        linarith
      rw [hw0z, zero_mul, ← h0, zero_mul]
    · have hq : wiener0 M a / Real.sqrt tameMass ≤ e ^ ((1 - l₀) / 2) * d ^ (l₀ / 2) := by
        rw [div_le_iff₀ hpos]
        linarith [hW0']
      have hc := mul_le_rpow_mul_rpow he hd (div_nonneg hw0n hL) (Real.sqrt_nonneg _) hq hs
        (by rw [hβ2]; exact hβpos.ne') (by rw [hγ2]; exact hγpos.ne')
      rw [hβ2, hγ2] at hc
      calc wiener0 M a * Real.sqrt (orderEnergy m M a * D)
          = Real.sqrt tameMass * ((wiener0 M a / Real.sqrt tameMass) *
              Real.sqrt (orderEnergy m M a * D)) := by field_simp
        _ ≤ _ := mul_le_mul_of_nonneg_left hc hL
  have htame := orderTriad_le_tame m M a ha
  calc orderTriad m M a ≤ (2 : ℝ)^m * (orderEnergy m M a * wiener1 M a +
        wiener0 M a * Real.sqrt (orderEnergy m M a * D)) := htame
    _ ≤ (2 : ℝ)^m * (Real.sqrt tameMass * (e ^ (1 / 2 + 1 / (8 * m) : ℝ) *
          d ^ (1 - 1 / (8 * m) : ℝ)) + Real.sqrt tameMass * (e ^ (1 / 2 + 1 / (8 * m) : ℝ) *
          d ^ (1 - 1 / (8 * m) : ℝ))) :=
        mul_le_mul_of_nonneg_left (add_le_add hT1 hT2) (by positivity)
    _ = _ := by ring

/-- **Absorption.** For every `ε > 0` the triad is paid by `ε D_m` and a power
of the order-one energy, with a constant independent of the modes and data. -/
theorem orderTriad_le_absorb (m : ℕ) (hm : 2 ≤ m) (M : Finset Wavevector)
    (a : Wavevector → ℝ) (ha : ∀ k, 0 ≤ a k) (hM : ∀ k ∈ M, k ≠ 0) {ε : ℝ} (hε : 0 < ε) :
    orderTriad m M a ≤ ε * orderDissipation m M a +
      ((2 : ℝ) ^ (m + 1) * Real.sqrt tameMass * 4 ^ (1 - 1 / (8 * m) : ℝ) *
        ε ^ (-(1 - 1 / (8 * m)) : ℝ)) ^ (8 * m : ℝ) * orderEnergy 1 M a ^ (4 * m + 1) := by
  have hmR : (2 : ℝ) ≤ m := by exact_mod_cast hm
  set δ : ℝ := 1 / (8 * m) with hδ
  have hδ0 : 0 < δ := by positivity
  have hδ1 : δ < 1 := by rw [hδ, div_lt_one (by positivity)]; linarith
  set e := orderEnergy 1 M a
  set D := orderDissipation m M a
  have he : 0 ≤ e := orderEnergy_nonneg 1 M a
  have hD : 0 ≤ D := orderDissipation_nonneg m M a
  set A : ℝ := (2 : ℝ) ^ (m + 1) * Real.sqrt tameMass * 4 ^ (1 - δ) with hA
  have hA0 : 0 ≤ A := by positivity
  have hsub := orderTriad_le_subcritical m hm M a ha hM
  rw [Real.mul_rpow (by norm_num) hD] at hsub
  have hsub' : orderTriad m M a ≤ A * (e ^ (1 / 2 + δ) * D ^ (1 - δ)) := by
    calc orderTriad m M a ≤ _ := hsub
      _ = A * (e ^ (1 / 2 + δ) * D ^ (1 - δ)) := by rw [hA]; ring
  set Y : ℝ := (A * ε ^ (-(1 - δ)) * e ^ (1 / 2 + δ)) ^ (1 / δ) with hY
  have hB0 : 0 ≤ A * ε ^ (-(1 - δ)) * e ^ (1 / 2 + δ) :=
    mul_nonneg (mul_nonneg hA0 (Real.rpow_nonneg hε.le _)) (Real.rpow_nonneg he _)
  have hYpow : Y ^ δ = A * ε ^ (-(1 - δ)) * e ^ (1 / 2 + δ) := by
    rw [hY, ← Real.rpow_mul hB0, one_div_mul_cancel hδ0.ne', Real.rpow_one]
  have hY0 : 0 ≤ Y := Real.rpow_nonneg hB0 _
  have hamgm := Real.geom_mean_le_arith_mean2_weighted (w₁ := 1 - δ) (w₂ := δ)
    (p₁ := ε * D) (p₂ := Y) (by linarith) hδ0.le (by positivity) hY0 (by ring)
  have hkey : A * (e ^ (1 / 2 + δ) * D ^ (1 - δ)) = (ε * D) ^ (1 - δ) * Y ^ δ := by
    rw [hYpow, Real.mul_rpow hε.le hD]
    have hε' : ε ^ (1 - δ) * ε ^ (-(1 - δ)) = 1 := by
      rw [← Real.rpow_add hε, add_neg_cancel, Real.rpow_zero]
    calc A * (e ^ (1 / 2 + δ) * D ^ (1 - δ))
        = A * (e ^ (1 / 2 + δ) * D ^ (1 - δ)) * (ε ^ (1 - δ) * ε ^ (-(1 - δ))) := by
          rw [hε', mul_one]
      _ = _ := by ring
  have hYval : Y = (A * ε ^ (-(1 - δ))) ^ (8 * m : ℝ) * e ^ (4 * m + 1) := by
    rw [hY, Real.mul_rpow (mul_nonneg hA0 (Real.rpow_nonneg hε.le _)) (Real.rpow_nonneg he _),
      ← Real.rpow_mul he, hδ, one_div_one_div]
    congr 1
    rw [show (1 / 2 + 1 / (8 * (m : ℝ))) * (8 * m) = ((4 * m + 1 : ℕ) : ℝ) by
      push_cast; field_simp; ring, Real.rpow_natCast]
  calc orderTriad m M a ≤ A * (e ^ (1 / 2 + δ) * D ^ (1 - δ)) := hsub'
    _ = (ε * D) ^ (1 - δ) * Y ^ δ := hkey
    _ ≤ (1 - δ) * (ε * D) + δ * Y := hamgm
    _ ≤ ε * D + Y := by nlinarith [mul_nonneg hε.le hD]
    _ = _ := by rw [hYval, hA]

/-! ### The Galerkin rate controlled by the order-one energy -/

/-- The constant of the tame rate inequality. -/
def tameRateConst (m : ℕ) (nu : ℝ) : ℝ :=
  2 * (2 * Real.pi) * ((2 : ℝ) ^ (m + 1) * Real.sqrt tameMass * 4 ^ (1 - 1 / (8 * m) : ℝ) *
    (nu * (2 * Real.pi) / 2) ^ (-(1 - 1 / (8 * m)) : ℝ)) ^ (8 * m : ℝ)

theorem tameRateConst_nonneg (m : ℕ) {nu : ℝ} (hnu : 0 < nu) : 0 ≤ tameRateConst m nu := by
  unfold tameRateConst
  have : 0 ≤ (2 : ℝ) ^ (m + 1) * Real.sqrt tameMass * 4 ^ (1 - 1 / (8 * m) : ℝ) *
      (nu * (2 * Real.pi) / 2) ^ (-(1 - 1 / (8 * m)) : ℝ) := by positivity
  positivity

/-- **Tame rate.** The order-`m` Galerkin rate is paid by half the dissipation
and a power of the order-one energy. -/
theorem orderVelocityRate_le_tame (m : ℕ) (hm : 2 ≤ m) (M : Finset Wavevector)
    (u : FourierVelocity) {nu : ℝ} (hnu : 0 < nu)
    (hk : ∀ k ∈ M, frequencyVec k ≠ 0) (hd : ∀ k ∈ M, modeDot k (u k) = 0) :
    orderVelocityRate m M u (velocityRHS M u nu) +
        nu * (2 * Real.pi) ^ 2 * velocityDissipation m M u ≤
      tameRateConst m nu * velocityEnergy 1 M u ^ (4 * m + 1) := by
  have hM : ∀ k ∈ M, k ≠ 0 := by
    intro k hkM h0
    apply hk k hkM
    subst h0
    ext i
    simp [frequencyVec, coefficientVec, PancakePeriodicComplexStretch.wavevectorCoefficient]
  have hε : 0 < nu * (2 * Real.pi) / 2 := by positivity
  have hab := orderTriad_le_absorb m hm M (amplitude u) (fun k ↦ norm_nonneg _) hM hε
  rw [orderVelocityRate_velocityRHS m M u nu hk hd]
  have h1 := orderConvectionRate_le m M u
  have h2 := mul_le_mul_of_nonneg_left hab (show 0 ≤ 2 * (2 * Real.pi) by positivity)
  change orderConvectionRate m M u - 2 * nu * (2 * Real.pi) ^ 2 * velocityDissipation m M u +
      nu * (2 * Real.pi) ^ 2 * velocityDissipation m M u ≤ _
  have hD : velocityDissipation m M u = orderDissipation m M (amplitude u) := rfl
  have hE : velocityEnergy 1 M u = orderEnergy 1 M (amplitude u) := rfl
  rw [hD, hE]
  unfold tameRateConst
  nlinarith [h1, h2]

/-- **Order-one control of a Galerkin solution.** If the order-one energy stays
below `K` on `[0, t]`, the order-`m` energy grows at most linearly. -/
theorem galerkin_orderEnergy_le (m : ℕ) (hm : 2 ≤ m) {M : Finset Wavevector} {nu T : ℝ}
    {u₀ : FourierVelocity} (s : LocalVelocitySolution M nu u₀ T) (hnu : 0 < nu)
    (hk : ∀ k ∈ M, frequencyVec k ≠ 0) {K t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T)
    (hK : ∀ τ ∈ Set.Icc (0 : ℝ) t, velocityEnergy 1 M (s.coefficients τ) ≤ K) :
    velocityEnergy m M (s.coefficients t) ≤
      velocityEnergy m M (s.coefficients 0) + tameRateConst m nu * K ^ (4 * m + 1) * t := by
  set f := fun τ ↦ velocityEnergy m M (s.coefficients τ)
  have hsub : Set.Icc (0 : ℝ) t ⊆ Set.Icc (0 : ℝ) T :=
    Set.Icc_subset_Icc le_rfl ht.2
  have hderiv : ∀ τ ∈ Set.Icc (0 : ℝ) t, HasDerivAt f
      (orderVelocityRate m M (s.coefficients τ) (velocityRHS M (s.coefficients τ) nu)) τ :=
    fun τ hτ ↦ localSolution_order_derivative m s τ (hsub hτ)
  have hcont : ContinuousOn f (Set.Icc (0 : ℝ) t) :=
    fun τ hτ ↦ (hderiv τ hτ).continuousAt.continuousWithinAt
  have hdiff : DifferentiableOn ℝ f (interior (Set.Icc (0 : ℝ) t)) :=
    fun τ hτ ↦ (hderiv τ (interior_subset hτ)).differentiableAt.differentiableWithinAt
  have hbound : ∀ τ ∈ interior (Set.Icc (0 : ℝ) t),
      deriv f τ ≤ tameRateConst m nu * K ^ (4 * m + 1) := by
    intro τ hτ
    have hτ' := interior_subset hτ
    rw [(hderiv τ hτ').deriv]
    have hrate := orderVelocityRate_le_tame m hm M (s.coefficients τ) hnu hk
      (fun q hq ↦ s.transverse τ q hq)
    have hDn : 0 ≤ nu * (2 * Real.pi) ^ 2 * velocityDissipation m M (s.coefficients τ) :=
      mul_nonneg (by positivity) (orderDissipation_nonneg m M _)
    have hE1n : 0 ≤ velocityEnergy 1 M (s.coefficients τ) := orderEnergy_nonneg 1 M _
    have hpow : velocityEnergy 1 M (s.coefficients τ) ^ (4 * m + 1) ≤ K ^ (4 * m + 1) :=
      pow_le_pow_left₀ hE1n (hK τ hτ') _
    have := mul_le_mul_of_nonneg_left hpow (tameRateConst_nonneg m hnu)
    linarith
  have hmv := (convex_Icc (0 : ℝ) t).image_sub_le_mul_sub_of_deriv_le hcont hdiff hbound
    0 ⟨le_rfl, ht.1⟩ t ⟨ht.1, le_rfl⟩ ht.1
  simp only [f, sub_zero] at hmv
  linarith

end Mettapedia.FluidDynamics.NavierStokes.FourierTameTriad
