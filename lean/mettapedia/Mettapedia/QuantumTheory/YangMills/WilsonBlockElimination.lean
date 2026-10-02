import Mettapedia.QuantumTheory.YangMills.CompactTransferGap
import Mettapedia.GSLT.Core.Ultrainfinite
import Mathlib.MeasureTheory.Group.Prod

/-!
# Exact weighted block elimination

Integrating the interior of a block preserves its boundary expectations. For
two observables the exact transport law contains the averaged conditional
covariance. All weights and observables here are continuous on compact spaces;
the weight is strictly positive. In particular all displayed integrals are
integrable and every normalization denominator is positive.

The conditional covariance is kept as a continuous boundary observable, so its
contribution can be transported through further eliminations. Third and fourth
cumulants use common moment polynomials, retaining all five and fifteen terms
of their respective conditioning laws. Weighted expectation and interior
projection are linear maps on marks.

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

/-- The third connected-moment polynomial of a normalized moment map. The
definition also makes sense for linear projections with function-valued output. -/
def thirdMoment {A B : Type*} [CommRing A] [CommRing B] [Module ℝ B]
    (P : A → B) (F G H : A) : B :=
  P (F * G * H) - P (F * G) * P H - P (F * H) * P G - P (G * H) * P F +
    (2 : ℝ) • (P F * P G * P H)

/-- The algebraic law of total third cumulance. Linearity retains the
conditional third moment and all three conditional-covariance corrections. -/
theorem thirdMoment_comp {A B D : Type*} [CommRing A] [CommRing B] [CommRing D]
    [Module ℝ A] [Module ℝ B] [Module ℝ D]
    (P : A →ₗ[ℝ] B) (Q : B →ₗ[ℝ] D) (F G H : A) :
    thirdMoment (Q.comp P) F G H =
      thirdMoment Q (P F) (P G) (P H) + Q (thirdMoment P F G H) +
      (Q (P F * (P (G * H) - P G * P H)) - Q (P F) * Q (P (G * H) - P G * P H)) +
      (Q (P G * (P (F * H) - P F * P H)) - Q (P G) * Q (P (F * H) - P F * P H)) +
      (Q (P H * (P (F * G) - P F * P G)) - Q (P H) * Q (P (F * G) - P F * P G)) := by
  simp only [thirdMoment, LinearMap.comp_apply, mul_sub, map_sub, map_add, two_smul ℝ]
  ring

def secondMoment {A B : Type*} [CommRing A] [CommRing B] (P : A → B) (F G : A) : B :=
  P (F * G) - P F * P G

/-- The fourth joint cumulant polynomial, with all fifteen set partitions. -/
def fourthMoment {A B : Type*} [CommRing A] [CommRing B] (P : A → B) (F G H K : A) : B :=
  P (F * G * H * K) -
    (P (F * G * H) * P K + P (F * G * K) * P H + P (F * H * K) * P G + P (G * H * K) * P F) -
    (P (F * G) * P (H * K) + P (F * H) * P (G * K) + P (F * K) * P (G * H)) +
    2 • (P (F * G) * P H * P K + P (F * H) * P G * P K + P (F * K) * P G * P H +
      P (G * H) * P F * P K + P (G * K) * P F * P H + P (H * K) * P F * P G) -
    6 • (P F * P G * P H * P K)

/-- Total fourth cumulance: four mean/third covariances, three pair/pair
covariances and six outer third-cumulant corrections accompany the two
fourth cumulants. This identity is algebraic in the actual linear maps. -/
theorem fourthMoment_comp {A B D : Type*} [CommRing A] [CommRing B] [CommRing D]
    [Module ℝ A] [Module ℝ B] [Module ℝ D]
    (P : A →ₗ[ℝ] B) (Q : B →ₗ[ℝ] D) (F G H K : A) :
    fourthMoment (Q.comp P) F G H K =
      Q (fourthMoment P F G H K) + fourthMoment Q (P F) (P G) (P H) (P K) +
      secondMoment Q (P F) (thirdMoment P G H K) +
      secondMoment Q (P G) (thirdMoment P F H K) +
      secondMoment Q (P H) (thirdMoment P F G K) +
      secondMoment Q (P K) (thirdMoment P F G H) +
      secondMoment Q (secondMoment P F G) (secondMoment P H K) +
      secondMoment Q (secondMoment P F H) (secondMoment P G K) +
      secondMoment Q (secondMoment P F K) (secondMoment P G H) +
      thirdMoment Q (P F) (P G) (secondMoment P H K) +
      thirdMoment Q (P F) (P H) (secondMoment P G K) +
      thirdMoment Q (P F) (P K) (secondMoment P G H) +
      thirdMoment Q (P G) (P H) (secondMoment P F K) +
      thirdMoment Q (P G) (P K) (secondMoment P F H) +
      thirdMoment Q (P H) (P K) (secondMoment P F G) := by
  simp only [fourthMoment, thirdMoment, secondMoment, LinearMap.comp_apply,
    show (6 : ℕ) = 2 + 2 + 2 by norm_num, add_nsmul, two_nsmul, two_smul ℝ,
    mul_sub, mul_add, sub_mul, map_sub, map_add]
  ring

theorem fourthMoment_eq_singleton_cut {A : Type*} [CommRing A]
    (P : A → ℝ) (F G H K : A) :
    fourthMoment P F G H K = secondMoment P F (G * H * K) -
      P G * secondMoment P F (H * K) - P H * secondMoment P F (G * K) -
      P K * secondMoment P F (G * H) -
      P (G * H) * secondMoment P F K - P (G * K) * secondMoment P F H -
      P (H * K) * secondMoment P F G +
      2 * (P G * P H * secondMoment P F K + P G * P K * secondMoment P F H +
        P H * P K * secondMoment P F G) := by
  simp only [fourthMoment, secondMoment, nsmul_eq_mul, ← mul_assoc]
  ring

theorem fourthMoment_eq_centeredProducts {A : Type*} [CommRing A] [Algebra ℝ A]
    (P : A →ₗ[ℝ] ℝ) (hP : P 1 = 1) (F G H K : A) :
    fourthMoment P F G H K =
      P ((F - (P F) • 1) * (G - (P G) • 1) * (H - (P H) • 1) * (K - (P K) • 1)) -
      secondMoment P F G * secondMoment P H K -
      secondMoment P F H * secondMoment P G K -
      secondMoment P F K * secondMoment P G H := by
  simp only [fourthMoment, secondMoment, mul_sub, sub_mul, mul_smul_comm,
    smul_mul_assoc, one_mul, mul_one, map_sub, map_smul,
    hP, smul_eq_mul, nsmul_eq_mul]
  ring

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

/-- Third connected correlation under the same normalized positive density. -/
def thirdCumulant (W F G H : C(X, ℝ)) : ℝ :=
  thirdMoment (expectation μ W) F G H

theorem thirdCumulant_swap (W F G H : C(X, ℝ)) :
    thirdCumulant μ W F G H = thirdCumulant μ W G F H := by
  simp only [thirdCumulant, thirdMoment, smul_eq_mul, mul_comm G F]
  ring

theorem thirdCumulant_rotate (W F G H : C(X, ℝ)) :
    thirdCumulant μ W F G H = thirdCumulant μ W G H F := by
  have hp : F * G * H = G * H * F := by ring
  simp only [thirdCumulant, thirdMoment, smul_eq_mul, hp, mul_comm H F, mul_comm G F]
  ring

/-- Isolating one mark reduces third cumulance to three covariances. This
form transfers two-set spatial mixing to a three-point tree estimate. -/
theorem thirdCumulant_eq_covariances (W F G H : C(X, ℝ)) :
    thirdCumulant μ W F G H = covariance μ W F (G * H) -
      expectation μ W G * covariance μ W F H -
      expectation μ W H * covariance μ W F G := by
  simp only [thirdCumulant, thirdMoment, covariance, smul_eq_mul,
    mul_assoc F G H, mul_comm G H, mul_comm H F, mul_comm G F]
  ring

def fourthCumulant (W F G H K : C(X, ℝ)) : ℝ :=
  fourthMoment (expectation μ W) F G H K

omit [CompactSpace X] [BorelSpace X] [IsProbabilityMeasure μ] in
theorem fourthCumulant_swap (W F G H K : C(X, ℝ)) :
    fourthCumulant μ W F G H K = fourthCumulant μ W G F H K := by
  have hFG : F * G = G * F := mul_comm _ _
  simp only [fourthCumulant, fourthMoment, nsmul_eq_mul, hFG]
  ring

omit [CompactSpace X] [BorelSpace X] [IsProbabilityMeasure μ] in
theorem fourthCumulant_rotate (W F G H K : C(X, ℝ)) :
    fourthCumulant μ W F G H K = fourthCumulant μ W G H K F := by
  have hFGH : F * G * H = G * H * F := by ring
  have hFGK : F * G * K = G * K * F := by ring
  have hFHK : F * H * K = H * K * F := by ring
  simp only [fourthCumulant, fourthMoment, nsmul_eq_mul, hFGH, hFGK, hFHK,
    mul_comm K F, mul_comm H F, mul_comm G F]
  ring

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

omit [CompactSpace X] [BorelSpace X] [IsProbabilityMeasure μ] in
theorem expectation_const_mul (W F : C(X, ℝ)) (c : ℝ) :
    expectation μ W (ContinuousMap.const X c * F) = c * expectation μ W F := by
  simp only [expectation, ContinuousMap.mul_apply, ContinuousMap.const_apply]
  simp_rw [mul_left_comm (W _) c]
  rw [integral_const_mul, mul_div_assoc]

/-- The weighted expectation as a linear map on continuous marks. -/
def expectationLinear (W : C(X, ℝ)) : C(X, ℝ) →ₗ[ℝ] ℝ where
  toFun := expectation μ W
  map_add' := expectation_add μ W
  map_smul' c F := expectation_const_mul μ W F c

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

/-- A contact-free bound requiring no spatial separation; useful at the
diagonal as well as at nearby coordinates. -/
theorem abs_covariance_le (W F G : C(X, ℝ)) (hW : ∀ x, 0 < W x)
    {CF CG : ℝ} (hCF : 0 ≤ CF) (hCG : 0 ≤ CG)
    (hF : ∀ x, |F x| ≤ CF) (hG : ∀ x, |G x| ≤ CG) :
    |covariance μ W F G| ≤ 2 * CF * CG := by
  have hFG : |expectation μ W (F * G)| ≤ CF * CG :=
    abs_expectation_le μ W (F * G) hW (fun x ↦ by
      rw [ContinuousMap.mul_apply, abs_mul]
      exact mul_le_mul (hF x) (hG x) (abs_nonneg _) hCF)
  have hp : |expectation μ W F * expectation μ W G| ≤ CF * CG := by
    rw [abs_mul, mul_comm |expectation μ W F|, mul_comm CF]
    exact mul_le_mul (abs_expectation_le μ W G hW hG)
      (abs_expectation_le μ W F hW hF) (abs_nonneg _) hCG
  exact (abs_sub _ _).trans (by nlinarith)

/-- Remove the mean under the explicitly supplied generated density. -/
def centered (W F : C(X, ℝ)) : C(X, ℝ) := F - (expectation μ W F) • 1

theorem abs_centered_le (W F : C(X, ℝ)) (hW : ∀ x, 0 < W x)
    {B : ℝ} (hF : ∀ x, |F x| ≤ B) (x : X) : |centered μ W F x| ≤ 2 * B := by
  change |F x - expectation μ W F * 1| ≤ _
  rw [mul_one]
  exact (abs_sub _ _).trans (by linarith [hF x, abs_expectation_le μ W F hW hF])

theorem expectation_centered (W F : C(X, ℝ)) (hW : ∀ x, 0 < W x) :
    expectation μ W (centered μ W F) = 0 := by
  change (expectationLinear μ W) (F - (expectation μ W F) • 1) = 0
  rw [map_sub, map_smul]
  change expectation μ W F - expectation μ W F * expectation μ W 1 = 0
  rw [expectation_one μ W hW]
  ring

theorem covariance_centered (W F G : C(X, ℝ)) (hW : ∀ x, 0 < W x) :
    covariance μ W (centered μ W F) (centered μ W G) = covariance μ W F G := by
  let P := expectationLinear μ W
  have hP : P 1 = 1 := expectation_one μ W hW
  change P ((F - (P F) • 1) * (G - (P G) • 1)) - P (F - (P F) • 1) *
    P (G - (P G) • 1) = P (F * G) - P F * P G
  simp only [mul_sub, sub_mul, mul_smul_comm, smul_mul_assoc,
    one_mul, mul_one, map_sub, map_smul, hP, smul_eq_mul]
  ring

theorem fourthCumulant_eq_centeredProducts (W F G H K : C(X, ℝ))
    (hW : ∀ x, 0 < W x) :
    fourthCumulant μ W F G H K =
      expectation μ W (centered μ W F * centered μ W G * centered μ W H * centered μ W K) -
      covariance μ W F G * covariance μ W H K -
      covariance μ W F H * covariance μ W G K -
      covariance μ W F K * covariance μ W G H :=
  fourthMoment_eq_centeredProducts (expectationLinear μ W) (expectation_one μ W hW) F G H K

theorem fourthCumulant_eq_pair_cut (W F G H K : C(X, ℝ)) (hW : ∀ x, 0 < W x) :
    fourthCumulant μ W F G H K =
      covariance μ W (centered μ W F * centered μ W G) (centered μ W H * centered μ W K) -
      covariance μ W F H * covariance μ W G K -
      covariance μ W F K * covariance μ W G H := by
  rw [fourthCumulant_eq_centeredProducts μ W F G H K hW]
  have hm (A B : C(X, ℝ)) : expectation μ W (centered μ W A * centered μ W B) = covariance μ W A B := by
    have h := covariance_centered μ W A B hW
    simpa only [covariance, expectation_centered μ W _ hW, zero_mul, sub_zero] using h
  simp only [covariance, hm]
  simp only [mul_assoc]

theorem fourthCumulant_eq_singleton_cut (W F G H K : C(X, ℝ)) (hW : ∀ x, 0 < W x) :
    fourthCumulant μ W F G H K =
      covariance μ W (centered μ W F) (centered μ W G * centered μ W H * centered μ W K) -
      covariance μ W F G * covariance μ W H K -
      covariance μ W F H * covariance μ W G K -
      covariance μ W F K * covariance μ W G H := by
  rw [fourthCumulant_eq_centeredProducts μ W F G H K hW]
  simp only [covariance, expectation_centered μ W F hW, zero_mul, sub_zero, mul_assoc]

theorem abs_fourthCumulant_le (W F G H K : C(X, ℝ)) (hW : ∀ x, 0 < W x)
    {B : ℝ} (hB : 0 ≤ B) (hF : ∀ x, |F x| ≤ B) (hG : ∀ x, |G x| ≤ B)
    (hH : ∀ x, |H x| ≤ B) (hK : ∀ x, |K x| ≤ B) :
    |fourthCumulant μ W F G H K| ≤ 28 * B^4 := by
  have hprod : |expectation μ W (centered μ W F * centered μ W G * centered μ W H * centered μ W K)| ≤ 16 * B^4 := by
    apply abs_expectation_le μ W _ hW
    intro x
    simp only [ContinuousMap.mul_apply, abs_mul]
    calc
      _ ≤ (2*B)*(2*B)*(2*B)*(2*B) := by
        gcongr
        · exact abs_centered_le μ W F hW hF x
        · exact abs_centered_le μ W G hW hG x
        · exact abs_centered_le μ W H hW hH x
        · exact abs_centered_le μ W K hW hK x
      _ = _ := by ring
  have hb (A D : C(X, ℝ)) (hA : ∀ x, |A x| ≤ B) (hD : ∀ x, |D x| ≤ B) :
      |covariance μ W A D| ≤ 2*B^2 := by
    simpa only [pow_two, mul_assoc] using abs_covariance_le μ W A D hW hB hB hA hD
  have hpair (A D V Z : C(X, ℝ))
      (hA : ∀ x, |A x| ≤ B) (hD : ∀ x, |D x| ≤ B)
      (hV : ∀ x, |V x| ≤ B) (hZ : ∀ x, |Z x| ≤ B) :
      |covariance μ W A D * covariance μ W V Z| ≤ 4*B^4 := by
    rw [abs_mul]
    calc
      _ ≤ (2*B^2)*(2*B^2) := mul_le_mul (hb A D hA hD) (hb V Z hV hZ) (abs_nonneg _) (by positivity)
      _ = _ := by ring
  rw [fourthCumulant_eq_centeredProducts μ W F G H K hW]
  have ht (a b c d : ℝ) : |a-b-c-d| ≤ |a|+|b|+|c|+|d| := by
    linarith [abs_sub (a-b-c) d, abs_sub (a-b) c, abs_sub a b]
  apply (ht _ _ _ _).trans
  linarith [hpair F G H K hF hG hH hK, hpair F H G K hF hH hG hK,
    hpair F K G H hF hK hG hH]

omit [CompactSpace X] [BorelSpace X] [IsProbabilityMeasure μ] in
theorem fourthCumulant_swap_middle (W F G H K : C(X, ℝ)) :
    fourthCumulant μ W F G H K = fourthCumulant μ W F H G K := by
  simp only [fourthCumulant, fourthMoment, nsmul_eq_mul]
  ring

omit [CompactSpace X] [BorelSpace X] [IsProbabilityMeasure μ] in
theorem fourthCumulant_swap_last (W F G H K : C(X, ℝ)) :
    fourthCumulant μ W F G H K = fourthCumulant μ W F G K H := by
  simp only [fourthCumulant, fourthMoment, nsmul_eq_mul]
  ring

/-- A singleton cut or a pair cut controls the fourth connected response.
Only covariances crossing the cut require a spatial estimate. -/
theorem abs_fourthCumulant_le_singleton_cut (W F G H K : C(X, ℝ)) (hW : ∀ x, 0 < W x)
    {B C : ℝ} (hB : 0 ≤ B) (hC : 0 ≤ C)
    (_hF : ∀ x, |F x| ≤ B) (hG : ∀ x, |G x| ≤ B)
    (hH : ∀ x, |H x| ≤ B) (hK : ∀ x, |K x| ≤ B)
    (hFGHK : |covariance μ W (centered μ W F)
      (centered μ W G * centered μ W H * centered μ W K)| ≤ 16 * B^4 * C)
    (hFG : |covariance μ W F G| ≤ B^2*C)
    (hFH : |covariance μ W F H| ≤ B^2*C)
    (hFK : |covariance μ W F K| ≤ B^2*C) :
    |fourthCumulant μ W F G H K| ≤ 22 * B^4 * C := by
  have hb (A D : C(X, ℝ)) (hA : ∀ x, |A x| ≤ B) (hD : ∀ x, |D x| ≤ B) :
      |covariance μ W A D| ≤ 2*B^2 := by
    simpa only [pow_two, mul_assoc] using abs_covariance_le μ W A D hW hB hB hA hD
  have hpair (a b : ℝ) (ha : |a| ≤ B^2*C) (hb : |b| ≤ 2*B^2) : |a*b| ≤ 2*B^4*C := by
    rw [abs_mul]
    calc
      _ ≤ (B^2*C)*(2*B^2) := mul_le_mul ha hb (abs_nonneg _) (by positivity)
      _ = _ := by ring
  rw [fourthCumulant_eq_singleton_cut μ W F G H K hW]
  have ht (a b c d : ℝ) : |a-b-c-d| ≤ |a|+|b|+|c|+|d| := by
    linarith [abs_sub (a-b-c) d, abs_sub (a-b) c, abs_sub a b]
  apply (ht _ _ _ _).trans
  linarith [hpair _ _ hFG (hb H K hH hK), hpair _ _ hFH (hb G K hG hK),
    hpair _ _ hFK (hb G H hG hH)]

theorem abs_fourthCumulant_le_pair_cut (W F G H K : C(X, ℝ)) (hW : ∀ x, 0 < W x)
    {B C : ℝ} (hB : 0 ≤ B) (hC : 0 ≤ C)
    (_hF : ∀ x, |F x| ≤ B) (hG : ∀ x, |G x| ≤ B)
    (hH : ∀ x, |H x| ≤ B) (hK : ∀ x, |K x| ≤ B)
    (hFGHK : |covariance μ W (centered μ W F * centered μ W G)
      (centered μ W H * centered μ W K)| ≤ 16 * B^4 * C)
    (hFH : |covariance μ W F H| ≤ B^2*C)
    (hFK : |covariance μ W F K| ≤ B^2*C) :
    |fourthCumulant μ W F G H K| ≤ 22 * B^4 * C := by
  have hb (A D : C(X, ℝ)) (hA : ∀ x, |A x| ≤ B) (hD : ∀ x, |D x| ≤ B) :
      |covariance μ W A D| ≤ 2*B^2 := by
    simpa only [pow_two, mul_assoc] using abs_covariance_le μ W A D hW hB hB hA hD
  have hpair (a b : ℝ) (ha : |a| ≤ B^2*C) (hb : |b| ≤ 2*B^2) : |a*b| ≤ 2*B^4*C := by
    rw [abs_mul]
    calc
      _ ≤ (B^2*C)*(2*B^2) := mul_le_mul ha hb (abs_nonneg _) (by positivity)
      _ = _ := by ring
  rw [fourthCumulant_eq_pair_cut μ W F G H K hW]
  have ht (a b c : ℝ) : |a-b-c| ≤ |a|+|b|+|c| := by
    linarith [abs_sub (a-b) c, abs_sub a b]
  apply (ht _ _ _).trans
  nlinarith [hpair _ _ hFH (hb G K hG hK), hpair _ _ hFK (hb G H hG hH),
    mul_nonneg (pow_nonneg hB 4) hC]

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

/-- Actual normalized interior integration, linear in the transported mark. -/
def projectLinear (W : C(B × I, ℝ)) (hW : ∀ p, 0 < W p) :
    C(B × I, ℝ) →ₗ[ℝ] C(B, ℝ) where
  toFun := project ν W hW
  map_add' F G := by
    ext b
    exact expectation_add ν (W.curry b) (F.curry b) (G.curry b)
  map_smul' c F := by
    ext b
    exact expectation_const_mul ν (W.curry b) (F.curry b) c

/-- View a boundary observable as an observable of the full block. -/
def lift (F : C(B, ℝ)) : C(B × I, ℝ) := ⟨fun p => F p.1, by fun_prop⟩

/-- The connected correlation left inside the eliminated fiber. -/
def fiberCovariance (W : C(B × I, ℝ)) (hW : ∀ p, 0 < W p)
    (F G : C(B × I, ℝ)) : C(B, ℝ) :=
  project ν W hW (F * G) - project ν W hW F * project ν W hW G

/-- The conditional third cumulant remains a continuous boundary mark. -/
def fiberThirdCumulant (W : C(B × I, ℝ)) (hW : ∀ p, 0 < W p)
    (F G H : C(B × I, ℝ)) : C(B, ℝ) :=
  thirdMoment (project ν W hW) F G H

/-- The exact conditional fourth cumulant, under the generated fiber law. -/
def fiberFourthCumulant (W : C(B × I, ℝ)) (hW : ∀ p, 0 < W p)
    (F G H K : C(B × I, ℝ)) : C(B, ℝ) :=
  fourthMoment (project ν W hW) F G H K

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

/-- Every actual normalized integration fixes constant marks. -/
@[simp] theorem project_one (W : C(B × I, ℝ)) (hW : ∀ p, 0 < W p) :
    project ν W hW (1 : C(B × I, ℝ)) = 1 := by
  ext b
  exact expectation_one ν (W.curry b) (fun i ↦ hW (b, i))

/-- The uniform norm contraction factor of raw mark transport cannot be
strictly smaller than one: the constant observable already saturates it.
An RG contraction therefore needs a suitable centered or extracted sector. -/
theorem one_le_project_uniform_bound (W : C(B × I, ℝ)) (hW : ∀ p, 0 < W p)
    (b : B) {q : ℝ}
    (hq : ∀ F : C(B × I, ℝ), (∀ p, |F p| ≤ 1) → |project ν W hW F b| ≤ q) :
    1 ≤ q := by
  have h := hq 1 (fun _ ↦ by simp)
  simpa only [project_one, ContinuousMap.one_apply, abs_one] using h

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

/-! ## Exact Haar coordinates for ordered link pairs -/

namespace PairedLinks

variable {X I J E : Type*} [MeasurableSpace E]

/-- Reindex two link families and the unused edges without changing their order. -/
def reassembly (e : ((I ⊕ I) ⊕ J) ≃ X) :
    (((I → E) × (I → E)) × (J → E)) ≃ᵐ (X → E) :=
  (((MeasurableEquiv.sumPiEquivProdPi (fun _ : I ⊕ I ↦ E)).symm.prodCongr
    (MeasurableEquiv.refl (J → E))).trans
    (MeasurableEquiv.sumPiEquivProdPi (fun _ : (I ⊕ I) ⊕ J ↦ E)).symm).trans
    (MeasurableEquiv.piCongrLeft (fun _ : X ↦ E) e)

@[simp] theorem reassembly_first (e : ((I ⊕ I) ⊕ J) ≃ X)
    (p : ((I → E) × (I → E)) × (J → E)) (i : I) :
    reassembly e p (e (.inl (.inl i))) = p.1.1 i := by
  simp only [reassembly, MeasurableEquiv.trans_apply, MeasurableEquiv.piCongrLeft_apply_apply]
  rfl

@[simp] theorem reassembly_second (e : ((I ⊕ I) ⊕ J) ≃ X)
    (p : ((I → E) × (I → E)) × (J → E)) (i : I) :
    reassembly e p (e (.inl (.inr i))) = p.1.2 i := by
  simp only [reassembly, MeasurableEquiv.trans_apply, MeasurableEquiv.piCongrLeft_apply_apply]
  rfl

@[simp] theorem reassembly_unused (e : ((I ⊕ I) ⊕ J) ≃ X)
    (p : ((I → E) × (I → E)) × (J → E)) (j : J) :
    reassembly e p (e (.inr j)) = p.2 j := by
  simp only [reassembly, MeasurableEquiv.trans_apply, MeasurableEquiv.piCongrLeft_apply_apply]
  rfl

section Group
variable [Group E] [MeasurableMul₂ E] [MeasurableInv E]

/-- Reconstruct fine links from the coarse product, the first link of each
pair, and all unused edges. The second link is exactly `a⁻¹ * c`. -/
def chart (e : ((I ⊕ I) ⊕ J) ≃ X) :
    ((I → E) × ((I → E) × (J → E))) ≃ᵐ (X → E) :=
  ((MeasurableEquiv.prodAssoc : ((I → E) × (I → E)) × (J → E) ≃ᵐ _).symm.trans
    (((MeasurableEquiv.prodComm : (I → E) × (I → E) ≃ᵐ _).trans
      (MeasurableEquiv.shearMulRight (I → E)).symm).prodCongr
      (MeasurableEquiv.refl (J → E)))).trans (reassembly e)

@[simp] theorem chart_first (e : ((I ⊕ I) ⊕ J) ≃ X)
    (p : (I → E) × ((I → E) × (J → E))) (i : I) :
    chart e p (e (.inl (.inl i))) = p.2.1 i := by
  simp only [chart, MeasurableEquiv.trans_apply, reassembly_first]
  rfl

@[simp] theorem chart_second (e : ((I ⊕ I) ⊕ J) ≃ X)
    (p : (I → E) × ((I → E) × (J → E))) (i : I) :
    chart e p (e (.inl (.inr i))) = (p.2.1 i)⁻¹ * p.1 i := by
  simp only [chart, MeasurableEquiv.trans_apply, reassembly_second]
  rfl

@[simp] theorem chart_unused (e : ((I ⊕ I) ⊕ J) ≃ X)
    (p : (I → E) × ((I → E) × (J → E))) (j : J) :
    chart e p (e (.inr j)) = p.2.2 j := by
  simp only [chart, MeasurableEquiv.trans_apply, reassembly_unused]
  rfl

/-- Ordered multiplication recovers the requested coarse field exactly. -/
def block (e : ((I ⊕ I) ⊕ J) ≃ X) (U : X → E) : I → E :=
  fun i ↦ U (e (.inl (.inl i))) * U (e (.inl (.inr i)))

@[simp] theorem block_chart (e : ((I ⊕ I) ⊕ J) ≃ X)
    (p : (I → E) × ((I → E) × (J → E))) : block e (chart e p) = p.1 := by
  funext i
  simp [block]

variable [Fintype X] [Fintype I] [Fintype J]

omit [Group E] [MeasurableMul₂ E] [MeasurableInv E] in
/-- Reindexing preserves the independent reference laws. -/
theorem measurePreserving_reassembly (ν : Measure E) [IsProbabilityMeasure ν]
    (e : ((I ⊕ I) ⊕ J) ≃ X) :
    MeasurePreserving (reassembly (E := E) e)
      (((Measure.pi fun _ : I ↦ ν).prod (Measure.pi fun _ : I ↦ ν)).prod
        (Measure.pi fun _ : J ↦ ν)) (Measure.pi fun _ : X ↦ ν) := by
  exact (measurePreserving_piCongrLeft (fun _ : X ↦ ν) e).comp
    ((measurePreserving_sumPiEquivProdPi_symm (fun _ : (I ⊕ I) ⊕ J ↦ ν)).comp
      ((measurePreserving_sumPiEquivProdPi_symm (fun _ : I ⊕ I ↦ ν)).prod
        (MeasurePreserving.id (Measure.pi fun _ : J ↦ ν))))

/-- The coarse product and all fluctuation coordinates are independent Haar
variables before inserting the full interaction density. -/
theorem measurePreserving_chart (ν : Measure E) [IsProbabilityMeasure ν]
    [Measure.IsMulLeftInvariant ν] (e : ((I ⊕ I) ⊕ J) ≃ X) :
    MeasurePreserving (chart (E := E) e)
      ((Measure.pi fun _ : I ↦ ν).prod ((Measure.pi fun _ : I ↦ ν).prod
        (Measure.pi fun _ : J ↦ ν))) (Measure.pi fun _ : X ↦ ν) := by
  exact (measurePreserving_reassembly ν e).comp
    (((measurePreserving_prod_inv_mul_swap (Measure.pi fun _ : I ↦ ν)
      (Measure.pi fun _ : I ↦ ν)).prod
      (MeasurePreserving.id (Measure.pi fun _ : J ↦ ν))).comp
      (measurePreserving_prodAssoc (Measure.pi fun _ : I ↦ ν)
        (Measure.pi fun _ : I ↦ ν) (Measure.pi fun _ : J ↦ ν)).symm)

/-- Multiplication of independent pairs pushes product Haar to product Haar. -/
theorem measurePreserving_block (ν : Measure E) [IsProbabilityMeasure ν]
    [Measure.IsMulLeftInvariant ν] (e : ((I ⊕ I) ⊕ J) ≃ X) :
    MeasurePreserving (block (E := E) e) (Measure.pi fun _ : X ↦ ν)
      (Measure.pi fun _ : I ↦ ν) := by
  have hb : block (E := E) e = fun U ↦ ((chart (E := E) e).symm U).1 := by
    funext U
    rw [← block_chart e ((chart e).symm U), (chart e).apply_symm_apply]
  rw [hb]
  exact measurePreserving_fst.comp (measurePreserving_chart ν e).symm

section Continuous
variable [TopologicalSpace E] [IsTopologicalGroup E]

omit [Fintype X] [Fintype I] [Fintype J] in
@[fun_prop] theorem continuous_chart (e : ((I ⊕ I) ⊕ J) ≃ X) :
    Continuous (chart (E := E) e) := by
  apply continuous_pi
  intro x
  obtain ⟨s, rfl⟩ := e.surjective x
  rcases s with (i | i) | j
  · simp only [chart_first]
    fun_prop
  · simp only [chart_second]
    fun_prop
  · simp only [chart_unused]
    fun_prop

omit [MeasurableSpace E] [MeasurableMul₂ E] [MeasurableInv E]
    [Fintype X] [Fintype I] [Fintype J] in
@[fun_prop] theorem continuous_block (e : ((I ⊕ I) ⊕ J) ≃ X) :
    Continuous (block (E := E) e) := by
  apply continuous_pi
  intro i
  exact (continuous_apply _).mul (continuous_apply _)

def chartMap (e : ((I ⊕ I) ⊕ J) ≃ X) :
    C((I → E) × ((I → E) × (J → E)), X → E) := ⟨chart e, continuous_chart e⟩

def blockMap (e : ((I ⊕ I) ⊕ J) ≃ X) : C(X → E, I → E) :=
  ⟨block e, continuous_block e⟩

variable [CompactSpace E] [BorelSpace E] [SecondCountableTopology E]

/-- Exact generated coarse density; every unused and fluctuation link is
integrated, and every original interaction is retained in the integrand. -/
def blockedDensity (ν : Measure E) [IsProbabilityMeasure ν]
    (e : ((I ⊕ I) ⊕ J) ≃ X) (W : C(X → E, ℝ)) : C(I → E, ℝ) :=
  marginal ((Measure.pi fun _ : I ↦ ν).prod (Measure.pi fun _ : J ↦ ν))
    (W.comp (chartMap e))

theorem blockedDensity_pos (ν : Measure E) [IsProbabilityMeasure ν]
    (e : ((I ⊕ I) ⊕ J) ≃ X) (W : C(X → E, ℝ)) (hW : ∀ U, 0 < W U) :
    ∀ c, 0 < blockedDensity ν e W c :=
  marginal_pos _ _ (fun _ ↦ hW _)

/-- The corresponding exact conditional transport of a fine observable. -/
def blockedProject (ν : Measure E) [IsProbabilityMeasure ν]
    (e : ((I ⊕ I) ⊕ J) ≃ X) (W : C(X → E, ℝ)) (hW : ∀ U, 0 < W U)
    (F : C(X → E, ℝ)) : C(I → E, ℝ) :=
  project ((Measure.pi fun _ : I ↦ ν).prod (Measure.pi fun _ : J ↦ ν))
    (W.comp (chartMap e)) (fun _ ↦ hW _) (F.comp (chartMap e))

/-- Exact block integration is linear in the observable. -/
def blockedProjectLinear (ν : Measure E) [IsProbabilityMeasure ν]
    (e : ((I ⊕ I) ⊕ J) ≃ X) (W : C(X → E, ℝ)) (hW : ∀ U, 0 < W U) :
    C(X → E, ℝ) →ₗ[ℝ] C(I → E, ℝ) where
  toFun := blockedProject ν e W hW
  map_add' F G := by
    ext c
    exact expectation_add _ ((W.comp (chartMap e)).curry c)
      ((F.comp (chartMap e)).curry c) ((G.comp (chartMap e)).curry c)
  map_smul' a F := by
    ext c
    exact expectation_const_mul _ ((W.comp (chartMap e)).curry c)
      ((F.comp (chartMap e)).curry c) a

theorem abs_blockedProject_le (ν : Measure E) [IsProbabilityMeasure ν]
    (e : ((I ⊕ I) ⊕ J) ≃ X) (W : C(X → E, ℝ)) (hW : ∀ U, 0 < W U)
    (F : C(X → E, ℝ)) {B : ℝ} (hF : ∀ U, |F U| ≤ B) :
    ∀ c, |blockedProject ν e W hW F c| ≤ B :=
  abs_project_le _ _ _ _ (fun _ ↦ hF _)

omit [TopologicalSpace E] [IsTopologicalGroup E] [CompactSpace E]
    [BorelSpace E] [SecondCountableTopology E] in
theorem integral_chart (ν : Measure E) [IsProbabilityMeasure ν]
    [Measure.IsMulLeftInvariant ν] (e : ((I ⊕ I) ⊕ J) ≃ X) (F : (X → E) → ℝ) :
    (∫ p, F (chart e p) ∂(Measure.pi fun _ : I ↦ ν).prod
      ((Measure.pi fun _ : I ↦ ν).prod (Measure.pi fun _ : J ↦ ν))) =
      ∫ U, F U ∂Measure.pi (fun _ : X ↦ ν) :=
  (measurePreserving_chart ν e).integral_comp' F

/-- Partition normalization is unchanged by genuine link blocking. -/
theorem integral_blockedDensity (ν : Measure E) [IsProbabilityMeasure ν]
    [Measure.IsMulLeftInvariant ν] (e : ((I ⊕ I) ⊕ J) ≃ X) (W : C(X → E, ℝ)) :
    (∫ c, blockedDensity ν e W c ∂Measure.pi (fun _ : I ↦ ν)) =
      ∫ U, W U ∂Measure.pi (fun _ : X ↦ ν) :=
  (integral_marginal _ _ (W.comp (chartMap e))).trans (integral_chart ν e W)

/-- Fine expectations agree with those under the complete generated coarse
law. Positivity and compactness justify all normalized integrals. -/
theorem expectation_blockedProject (ν : Measure E) [IsProbabilityMeasure ν]
    [Measure.IsMulLeftInvariant ν] (e : ((I ⊕ I) ⊕ J) ≃ X)
    (W : C(X → E, ℝ)) (hW : ∀ U, 0 < W U) (F : C(X → E, ℝ)) :
    expectation (Measure.pi fun _ : I ↦ ν) (blockedDensity ν e W)
      (blockedProject ν e W hW F) = expectation (Measure.pi fun _ : X ↦ ν) W F := by
  rw [blockedDensity, blockedProject, expectation_project]
  unfold expectation
  change (∫ p, (W * F) (chart e p) ∂(Measure.pi fun _ : I ↦ ν).prod
    ((Measure.pi fun _ : I ↦ ν).prod (Measure.pi fun _ : J ↦ ν))) /
      (∫ p, W (chart e p) ∂(Measure.pi fun _ : I ↦ ν).prod
        ((Measure.pi fun _ : I ↦ ν).prod (Measure.pi fun _ : J ↦ ν))) = _
  rw [integral_chart, integral_chart]
  rfl

/-- An observable already expressed in the coarse products is preserved
pointwise, without a projection error or an interaction truncation. -/
theorem blockedProject_lift (ν : Measure E) [IsProbabilityMeasure ν]
    (e : ((I ⊕ I) ⊕ J) ≃ X) (W : C(X → E, ℝ)) (hW : ∀ U, 0 < W U)
    (F : C(I → E, ℝ)) :
    blockedProject ν e W hW (F.comp (blockMap e)) = F := by
  have hF : (F.comp (blockMap e)).comp (chartMap e) = lift F := by
    ext p
    exact congrArg F (block_chart e p)
  rw [blockedProject, hF, project_lift]

end Continuous

end Group
end PairedLinks

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
