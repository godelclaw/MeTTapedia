import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeSmoothCutoffFourierTail
import Mathlib.Analysis.Fourier.PoissonSummation
import Mathlib.Analysis.Normed.Ring.InfiniteSum

/-!
# A concrete smooth periodic cell cutoff

This file removes the abstract Fourier-summability premise from the pancake
localization step.  We start from a compactly supported smooth bump on the
line, periodize it on the unit circle, and take the product in the three
spatial coordinates.  Poisson transference identifies its Fourier
coefficients with samples of a Schwartz Fourier transform, hence they are
absolutely summable.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes
namespace PancakeConcreteSmoothCellCutoff

open PeriodicFourierTriad
open PancakeSmoothCutoffFourierTail
open PancakeMisalignmentEnergyBridge
open PancakeFiniteFourierLocalization
open PancakeBufferedAnnularMultiplier
open PancakeAnnularSectorProjector
open PancakeFrameCovariance
open MeasureTheory
open ContinuousMap
open TopologicalSpace
open scoped BigOperators FourierTransform SchwartzMap

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

/-! ## A compactly supported one-dimensional seed -/

/-- A fixed smooth bump equal to one on `[-1/8,1/8]` and supported in
`(-1/4,1/4)`.  The small outer radius makes distinct integer translates
disjoint. -/
def cellBump : ContDiffBump (0 : ℝ) where
  rIn := 1 / 8
  rOut := 1 / 4
  rIn_pos := by norm_num
  rIn_lt_rOut := by norm_num

/-- The scalar bump, embedded in `ℂ`, as a Schwartz function. -/
def cellBumpSchwartz : SchwartzMap ℝ ℂ :=
  (cellBump.hasCompactSupport.comp_left rfl).toSchwartzMap
    (Complex.ofRealCLM.contDiff.comp cellBump.contDiff)

@[simp]
theorem cellBumpSchwartz_apply (x : ℝ) :
    cellBumpSchwartz x = cellBump x :=
  rfl

@[simp]
theorem cellBumpSchwartz_toContinuousMap_apply (x : ℝ) :
    cellBumpSchwartz.toContinuousMap x = cellBump x :=
  rfl

/-- Schwartz decay gives locally uniform summability of all integer
translates of the seed. -/
theorem summable_cellBumpSchwartz_translates_on_compact
    (K : Compacts ℝ) :
    Summable fun n : ℤ ↦
      ‖(cellBumpSchwartz.toContinuousMap.comp
          (ContinuousMap.addRight (n : ℝ))).restrict K‖ := by
  exact summable_of_isBigO (Real.summable_abs_int_rpow one_lt_two)
    ((isBigO_norm_restrict_cocompact
      cellBumpSchwartz.toContinuousMap zero_lt_two
      (cellBumpSchwartz.isBigO_cocompact_rpow (-2)) K).comp_tendsto
        Int.tendsto_coe_cofinite)

/-- The periodized one-dimensional seed as a genuine continuous function on
the unit circle. -/
def circleCellCutoff : C(UnitAddCircle, ℂ) :=
  ⟨( cellBumpSchwartz.toContinuousMap.periodic_tsum_comp_add_zsmul 1).lift,
    continuous_coinduced_dom.mpr (map_continuous _)⟩

/-- On a real representative, the circle cutoff is the locally uniformly
convergent sum of integer translates of the compact seed. -/
theorem circleCellCutoff_coe (x : ℝ) :
    circleCellCutoff (x : UnitAddCircle) =
      ∑' n : ℤ, cellBumpSchwartz.toContinuousMap (x + n) := by
  simpa only [circleCellCutoff, ContinuousMap.coe_mk,
    Function.Periodic.lift_coe, zsmul_one, ContinuousMap.comp_apply,
    ContinuousMap.coe_addRight] using
    (hasSum_apply
      (summable_of_locally_summable_norm
        summable_cellBumpSchwartz_translates_on_compact).hasSum x).tsum_eq.symm

/-- Away from the zero translate, every term vanishes on the centered
half-cell. -/
theorem cellBumpSchwartz_translate_eq_zero
    {x : ℝ} (hx : |x| ≤ 1 / 2) {n : ℤ} (hn : n ≠ 0) :
    cellBumpSchwartz.toContinuousMap (x + n) = 0 := by
  have hnZ : (1 : ℤ) ≤ |n| := Int.one_le_abs hn
  have hnR : (1 : ℝ) ≤ |(n : ℝ)| := by exact_mod_cast hnZ
  have htri : |(n : ℝ)| ≤ |x + (n : ℝ)| + |x| := by
    calc
      |(n : ℝ)| = |(x + (n : ℝ)) - x| := by ring_nf
      _ ≤ |x + (n : ℝ)| + |x| := abs_sub _ _
  have hout : (1 / 4 : ℝ) ≤ |x + (n : ℝ)| := by
    nlinarith
  have hzero := cellBump.zero_of_le_dist
    (x := x + (n : ℝ)) (by
      simpa [cellBump, Real.dist_eq] using hout)
  rw [cellBumpSchwartz_toContinuousMap_apply, hzero]
  simp

/-- On the inner eighth of the centered circle chart, the cutoff is exactly
one. -/
theorem circleCellCutoff_eq_one_of_abs_le_eighth
    {x : ℝ} (hx : |x| ≤ 1 / 8) :
    circleCellCutoff (x : UnitAddCircle) = 1 := by
  rw [circleCellCutoff_coe]
  calc
    (∑' n : ℤ, cellBumpSchwartz.toContinuousMap (x + n)) =
        cellBumpSchwartz.toContinuousMap (x + (0 : ℤ)) := by
      apply tsum_eq_single 0
      intro n hn
      exact cellBumpSchwartz_translate_eq_zero (by linarith) hn
    _ = 1 := by
      rw [cellBumpSchwartz_toContinuousMap_apply]
      simp only [Int.cast_zero, add_zero]
      have hmem : x ∈ Metric.closedBall (0 : ℝ) cellBump.rIn := by
        simpa [Metric.mem_closedBall, Real.dist_eq, cellBump] using hx
      rw [cellBump.one_of_mem_closedBall hmem]
      simp

/-- On the centered half-cell, the cutoff vanishes outside the outer quarter
of the chart. -/
theorem circleCellCutoff_eq_zero_of_quarter_le_abs
    {x : ℝ} (hquarter : 1 / 4 ≤ |x|) (hhalf : |x| ≤ 1 / 2) :
    circleCellCutoff (x : UnitAddCircle) = 0 := by
  rw [circleCellCutoff_coe]
  calc
    (∑' n : ℤ, cellBumpSchwartz.toContinuousMap (x + n)) =
        ∑' _n : ℤ, (0 : ℂ) := by
      apply tsum_congr
      intro n
      by_cases hn : n = 0
      · subst n
        rw [cellBumpSchwartz_toContinuousMap_apply]
        simp only [Int.cast_zero, add_zero]
        have hzero := cellBump.zero_of_le_dist (x := x) (by
          simpa [cellBump, Real.dist_eq] using hquarter)
        rw [hzero]
        simp
      · exact cellBumpSchwartz_translate_eq_zero hhalf hn
    _ = 0 := tsum_zero

/-- The Fourier coefficients of the periodized seed are exactly the integer
samples of its Euclidean Schwartz Fourier transform. -/
theorem fourierCoeff_circleCellCutoff (m : ℤ) :
    fourierCoeff circleCellCutoff m =
      FourierTransform.fourier (cellBumpSchwartz : ℝ → ℂ) m := by
  change fourierCoeff
      (Function.Periodic.lift <|
        cellBumpSchwartz.toContinuousMap.periodic_tsum_comp_add_zsmul 1) m = _
  rw [Real.fourierCoeff_tsum_comp_add
    summable_cellBumpSchwartz_translates_on_compact]
  rfl

/-- Integer samples of the Fourier transform of the seed are absolutely
summable. -/
theorem summable_fourier_cellBumpSchwartz :
    Summable fun m : ℤ ↦
      (FourierTransform.fourier cellBumpSchwartz : SchwartzMap ℝ ℂ) (m : ℝ) := by
  convert! summable_of_isBigO
    (Real.summable_abs_int_rpow one_lt_two)
    (((FourierTransform.fourier cellBumpSchwartz).isBigO_cocompact_rpow
      (-2)).comp_tendsto Int.tendsto_coe_cofinite) using 1

/-- Consequently, the genuine circle cutoff has absolutely summable Fourier
coefficients. -/
theorem summable_fourierCoeff_circleCellCutoff :
    Summable (fourierCoeff circleCellCutoff) := by
  exact summable_fourier_cellBumpSchwartz.congr fun m ↦ by
    rw [fourierCoeff_circleCellCutoff]
    rfl

/-! ## The spatial three-torus cutoff -/

/-- The concrete spatial cutoff is the tensor product of the periodized bump
in the three coordinate directions. -/
def torusCellCutoff : C(UnitAddTorus (Fin 3), ℂ) where
  toFun q := ∏ i : Fin 3, circleCellCutoff (q i)
  continuous_toFun := by fun_prop

/-- The product cutoff equals one on the central eighth-cube in real
representatives. -/
theorem torusCellCutoff_eq_one_of_mem_innerCube
    (x : Fin 3 → ℝ) (hx : ∀ i, |x i| ≤ 1 / 8) :
    torusCellCutoff (fun i ↦ (x i : UnitAddCircle)) = 1 := by
  change (∏ i : Fin 3, circleCellCutoff (x i : UnitAddCircle)) = 1
  apply Finset.prod_eq_one
  intro i _hi
  exact circleCellCutoff_eq_one_of_abs_le_eighth (hx i)

/-- On the central half-cube, leaving the outer quarter-cube forces the
product cutoff to vanish. -/
theorem torusCellCutoff_eq_zero_of_not_mem_outerCube
    (x : Fin 3 → ℝ) (hhalf : ∀ i, |x i| ≤ 1 / 2)
    (hout : ∃ i, 1 / 4 ≤ |x i|) :
    torusCellCutoff (fun i ↦ (x i : UnitAddCircle)) = 0 := by
  obtain ⟨i, hi⟩ := hout
  change (∏ j : Fin 3, circleCellCutoff (x j : UnitAddCircle)) = 0
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  exact circleCellCutoff_eq_zero_of_quarter_le_abs hi (hhalf i)

/-! ## A finite translated cover -/

/-- Translate the concrete cutoff to an arbitrary torus center. -/
def translatedTorusCellCutoff
    (c : UnitAddTorus (Fin 3)) : C(UnitAddTorus (Fin 3), ℂ) where
  toFun x := torusCellCutoff (x - c)
  continuous_toFun := by fun_prop

/-- A multivariate Fourier monomial is an additive character in its torus
argument. -/
theorem mFourier_add_apply (k : Wavevector)
    (x y : UnitAddTorus (Fin 3)) :
    UnitAddTorus.mFourier k (x + y) =
      UnitAddTorus.mFourier k x * UnitAddTorus.mFourier k y := by
  unfold UnitAddTorus.mFourier
  simp only [ContinuousMap.coe_mk, Pi.add_apply, fourier_apply, zsmul_add,
    AddCircle.toCircle_add]
  push_cast
  exact Finset.prod_mul_distrib

/-- Translation changes a Fourier coefficient only by the corresponding
unit complex phase. -/
theorem mFourierCoeff_translatedTorusCellCutoff
    (c : UnitAddTorus (Fin 3)) (k : Wavevector) :
    UnitAddTorus.mFourierCoeff (translatedTorusCellCutoff c) k =
      UnitAddTorus.mFourier (-k) c *
        UnitAddTorus.mFourierCoeff torusCellCutoff k := by
  unfold UnitAddTorus.mFourierCoeff translatedTorusCellCutoff
  simp only [ContinuousMap.coe_mk, smul_eq_mul]
  let f : UnitAddTorus (Fin 3) → ℂ := fun y ↦
    UnitAddTorus.mFourier (-k) (y + c) * torusCellCutoff y
  calc
    (∫ x, UnitAddTorus.mFourier (-k) x * torusCellCutoff (x - c)) =
        ∫ x, f (x - c) := by
      apply integral_congr_ae
      filter_upwards with x
      simp [f]
    _ = ∫ y, f y := integral_sub_right_eq_self f c
    _ = ∫ y, UnitAddTorus.mFourier (-k) c *
          (UnitAddTorus.mFourier (-k) y * torusCellCutoff y) := by
      apply integral_congr_ae
      filter_upwards with y
      dsimp only [f]
      rw [mFourier_add_apply]
      ring
    _ = UnitAddTorus.mFourier (-k) c *
          ∫ y, UnitAddTorus.mFourier (-k) y * torusCellCutoff y := by
      rw [integral_const_mul]

/-- Every value of a multivariate Fourier monomial has norm one. -/
theorem norm_mFourier_apply (k : Wavevector)
    (x : UnitAddTorus (Fin 3)) :
    ‖UnitAddTorus.mFourier k x‖ = 1 := by
  unfold UnitAddTorus.mFourier
  simp only [ContinuousMap.coe_mk, norm_prod]
  apply Finset.prod_eq_one
  intro i _hi
  exact Circle.norm_coe _

/-- Five real representatives of the quarter-grid.  The endpoints `0` and
`1` represent the same circle point; retaining both makes the centered-chart
cover proof completely explicit. -/
def quarterGridRealCenter (j : Fin 5) : ℝ := (j : ℝ) / 4

/-- Every point of the unit circle is within `1/8` of one of the five
quarter-grid representatives, with equality recorded in the quotient. -/
theorem exists_quarterGridRepresentative (q : UnitAddCircle) :
    ∃ j : Fin 5, ∃ d : ℝ,
      |d| ≤ 1 / 8 ∧
        q - (quarterGridRealCenter j : UnitAddCircle) =
          (d : UnitAddCircle) := by
  let r : ℝ := (AddCircle.equivIoc 1 0 q).1
  have hrmem : r ∈ Set.Ioc (0 : ℝ) 1 := by
    simpa using (AddCircle.equivIoc 1 0 q).2
  have hq : (r : UnitAddCircle) = q := by
    exact AddCircle.coe_equivIoc
  by_cases h₁ : r ≤ 1 / 8
  · refine ⟨⟨0, by decide⟩, r, ?_, ?_⟩
    · rw [abs_of_nonneg hrmem.1.le]
      exact h₁
    · rw [← hq]
      rw [← AddCircle.coe_sub]
      norm_num [quarterGridRealCenter]
  by_cases h₃ : r ≤ 3 / 8
  · refine ⟨⟨1, by decide⟩, r - 1 / 4, ?_, ?_⟩
    · rw [abs_le]
      constructor <;> linarith
    · rw [← hq]
      rw [← AddCircle.coe_sub]
      norm_num [quarterGridRealCenter]
  by_cases h₅ : r ≤ 5 / 8
  · refine ⟨⟨2, by decide⟩, r - 1 / 2, ?_, ?_⟩
    · rw [abs_le]
      constructor <;> linarith
    · rw [← hq]
      rw [← AddCircle.coe_sub]
      norm_num [quarterGridRealCenter]
  by_cases h₇ : r ≤ 7 / 8
  · refine ⟨⟨3, by decide⟩, r - 3 / 4, ?_, ?_⟩
    · rw [abs_le]
      constructor <;> linarith
    · rw [← hq]
      rw [← AddCircle.coe_sub]
      norm_num [quarterGridRealCenter]
  · refine ⟨⟨4, by decide⟩, r - 1, ?_, ?_⟩
    · rw [abs_le]
      constructor
      · have hr₇ : (7 / 8 : ℝ) < r := lt_of_not_ge h₇
        linarith
      · exact (sub_nonpos.mpr hrmem.2).trans (by norm_num)
    · rw [← hq]
      rw [← AddCircle.coe_sub]
      norm_num [quarterGridRealCenter]

/-- Indices for the fixed `5³` spatial cover. -/
abbrev SpatialCellIndex := Fin 3 → Fin 5

/-- The torus center associated to one spatial cell. -/
def spatialCellCenter (j : SpatialCellIndex) : UnitAddTorus (Fin 3) :=
  fun i ↦ (quarterGridRealCenter (j i) : UnitAddCircle)

/-- The translated smooth cutoff associated to one spatial cell. -/
def spatialCellCutoff (j : SpatialCellIndex) :
    C(UnitAddTorus (Fin 3), ℂ) :=
  translatedTorusCellCutoff (spatialCellCenter j)

/-- The fixed translated family really covers the spatial torus: at every
point, one of its members is identically one. -/
theorem exists_spatialCellCutoff_eq_one
    (x : UnitAddTorus (Fin 3)) :
    ∃ j : SpatialCellIndex, spatialCellCutoff j x = 1 := by
  have hcoord : ∀ i : Fin 3, ∃ j : Fin 5, ∃ d : ℝ,
      |d| ≤ 1 / 8 ∧
        x i - (quarterGridRealCenter j : UnitAddCircle) =
          (d : UnitAddCircle) := by
    intro i
    exact exists_quarterGridRepresentative (x i)
  choose j d hd hxd using hcoord
  refine ⟨j, ?_⟩
  change (∏ i : Fin 3,
    circleCellCutoff
      (x i - (quarterGridRealCenter (j i) : UnitAddCircle))) = 1
  apply Finset.prod_eq_one
  intro i _hi
  rw [hxd i]
  exact circleCellCutoff_eq_one_of_abs_le_eighth (hd i)

/-- The covering cell can be chosen from the explicit finite family. -/
theorem exists_mem_univ_spatialCellCutoff_eq_one
    (x : UnitAddTorus (Fin 3)) :
    ∃ j ∈ (Finset.univ : Finset SpatialCellIndex),
      spatialCellCutoff j x = 1 := by
  obtain ⟨j, hj⟩ := exists_spatialCellCutoff_eq_one x
  exact ⟨j, Finset.mem_univ _, hj⟩

/-- The explicit cover contains exactly `5³ = 125` indexed cells. -/
theorem card_spatialCellIndex : Fintype.card SpatialCellIndex = 125 := by
  simp [SpatialCellIndex]

/-- Nonnegative quadratic weight attached to one cover cutoff. -/
def spatialCoverWeight (j : SpatialCellIndex)
    (x : UnitAddTorus (Fin 3)) : ℝ :=
  Complex.normSq (spatialCellCutoff j x)

theorem spatialCoverWeight_nonneg (j : SpatialCellIndex)
    (x : UnitAddTorus (Fin 3)) :
    0 ≤ spatialCoverWeight j x :=
  Complex.normSq_nonneg _

/-- At least one cutoff is one, so the quadratic cover weight never loses
mass. -/
theorem one_le_sum_spatialCoverWeight (x : UnitAddTorus (Fin 3)) :
    1 ≤ ∑ j : SpatialCellIndex, spatialCoverWeight j x := by
  obtain ⟨j, hj⟩ := exists_spatialCellCutoff_eq_one x
  calc
    1 = spatialCoverWeight j x := by
      simp [spatialCoverWeight, hj]
    _ ≤ ∑ i : SpatialCellIndex, spatialCoverWeight i x := by
      exact Finset.single_le_sum
        (fun i _hi ↦ spatialCoverWeight_nonneg i x)
        (Finset.mem_univ j)

/-- Translation does not enlarge the pointwise bound supplied by the sup norm
of the seed cutoff. -/
theorem norm_spatialCellCutoff_le (j : SpatialCellIndex)
    (x : UnitAddTorus (Fin 3)) :
    ‖spatialCellCutoff j x‖ ≤ ‖torusCellCutoff‖ := by
  exact torusCellCutoff.norm_coe_le_norm
    (x - spatialCellCenter j)

/-- The total quadratic cover weight has an explicit frequency-independent
bound.  The deliberately redundant cover costs only the fixed factor `125`.
-/
theorem sum_spatialCoverWeight_le (x : UnitAddTorus (Fin 3)) :
    (∑ j : SpatialCellIndex, spatialCoverWeight j x) ≤
      125 * ‖torusCellCutoff‖ ^ 2 := by
  calc
    (∑ j : SpatialCellIndex, spatialCoverWeight j x) ≤
        ∑ _j : SpatialCellIndex, ‖torusCellCutoff‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro j _hj
      rw [spatialCoverWeight, Complex.normSq_eq_norm_sq]
      exact pow_le_pow_left₀ (norm_nonneg _)
        (norm_spatialCellCutoff_le j x) 2
    _ = 125 * ‖torusCellCutoff‖ ^ 2 := by
      simp [nsmul_eq_mul]

/-- Pointwise energy is captured by the finite smooth cover. -/
theorem normSq_le_sum_spatialCoverWeight_mul
    {E : Type*} [NormedAddCommGroup E]
    (U : UnitAddTorus (Fin 3) → E) (x : UnitAddTorus (Fin 3)) :
    ‖U x‖ ^ 2 ≤
      ∑ j : SpatialCellIndex, spatialCoverWeight j x * ‖U x‖ ^ 2 := by
  rw [← Finset.sum_mul]
  simpa only [one_mul] using
    mul_le_mul_of_nonneg_right
      (one_le_sum_spatialCoverWeight x) (sq_nonneg ‖U x‖)

/-- The multivariate Fourier coefficient of the tensor-product cutoff factors
as the product of its three one-dimensional coefficients. -/
theorem mFourierCoeff_torusCellCutoff (k : Wavevector) :
    UnitAddTorus.mFourierCoeff torusCellCutoff k =
      ∏ i : Fin 3, fourierCoeff circleCellCutoff (k i) := by
  unfold UnitAddTorus.mFourierCoeff torusCellCutoff UnitAddTorus.mFourier
  simp only [ContinuousMap.coe_mk, smul_eq_mul, Pi.neg_apply,
    ← Finset.prod_mul_distrib]
  rw [MeasureTheory.integral_fintype_prod_volume_eq_prod
    (fun i : Fin 3 ↦ fun x : UnitAddCircle ↦
      fourier (-(k i)) x * circleCellCutoff x)]
  rfl

/-- Coordinate functions on `Fin 3` are canonically triples.  Naming this
equivalence lets the absolute-convergence proof use the standard product
theorem for series. -/
def wavevectorEquivTriple : Wavevector ≃ ((ℤ × ℤ) × ℤ) where
  toFun k := ((k 0, k 1), k 2)
  invFun p := ![p.1.1, p.1.2, p.2]
  left_inv k := by
    funext i
    fin_cases i <;> rfl
  right_inv p := by
    rcases p with ⟨⟨p, q⟩, r⟩
    rfl

/-- A product of three copies of an absolutely summable complex sequence is
summable on the product index. -/
theorem summable_tripleProduct (a : ℤ → ℂ) (ha : Summable a) :
    Summable (fun p : (ℤ × ℤ) × ℤ ↦
      (a p.1.1 * a p.1.2) * a p.2) := by
  have hp : Summable (fun p : ℤ × ℤ ↦ ‖a p.1‖ * ‖a p.2‖) :=
    ha.norm.mul_of_nonneg ha.norm
      (fun _ ↦ norm_nonneg _) (fun _ ↦ norm_nonneg _)
  have ht : Summable (fun p : (ℤ × ℤ) × ℤ ↦
      (‖a p.1.1‖ * ‖a p.1.2‖) * ‖a p.2‖) :=
    hp.mul_of_nonneg ha.norm
      (fun _ ↦ mul_nonneg (norm_nonneg _) (norm_nonneg _))
      (fun _ ↦ norm_nonneg _)
  apply Summable.of_norm
  simpa only [norm_mul] using ht

/-- The same product, transported to the native wavevector index. -/
theorem summable_wavevectorTripleProduct (a : ℤ → ℂ) (ha : Summable a) :
    Summable (fun k : Wavevector ↦
      (a (k 0) * a (k 1)) * a (k 2)) := by
  have ht := summable_tripleProduct a ha
  have hw := wavevectorEquivTriple.summable_iff.mpr ht
  change Summable (fun k : Wavevector ↦
    (a (k 0) * a (k 1)) * a (k 2)) at hw
  exact hw

/-- The concrete three-dimensional cell cutoff has absolutely summable
Fourier coefficients.  This is the hypothesis previously left abstract by
`PancakeSmoothCutoffFourierTail`. -/
theorem summable_mFourierCoeff_torusCellCutoff :
    Summable (UnitAddTorus.mFourierCoeff torusCellCutoff) := by
  let a : ℤ → ℂ := fourierCoeff circleCellCutoff
  have ha : Summable a := summable_fourierCoeff_circleCellCutoff
  have hw := summable_wavevectorTripleProduct a ha
  apply hw.congr
  intro k
  rw [mFourierCoeff_torusCellCutoff]
  simp [a, Fin.prod_univ_succ, mul_assoc]

/-- Absolute Fourier summability is preserved by every torus translation of
the concrete cutoff. -/
theorem summable_mFourierCoeff_translatedTorusCellCutoff
    (c : UnitAddTorus (Fin 3)) :
    Summable (UnitAddTorus.mFourierCoeff
      (translatedTorusCellCutoff c)) := by
  apply Summable.of_norm
  exact summable_mFourierCoeff_torusCellCutoff.norm.congr fun k ↦ by
    rw [mFourierCoeff_translatedTorusCellCutoff, norm_mul,
      norm_mFourier_apply, one_mul]

/-- Every member of the explicit spatial cover has absolutely summable
Fourier coefficients. -/
theorem summable_mFourierCoeff_spatialCellCutoff
    (j : SpatialCellIndex) :
    Summable (UnitAddTorus.mFourierCoeff (spatialCellCutoff j)) := by
  exact summable_mFourierCoeff_translatedTorusCellCutoff
    (spatialCellCenter j)

/-- **Concrete scale-compatible localization.**  The fixed smooth cell
cutoff admits a uniformly accurate finite Fourier approximation whose modes
fit the anisotropic localization margin at every sufficiently large scale,
simultaneously for all frozen oriented frames. -/
theorem exists_eventually_margin_torusCellCutoff_uniformFrame
    {ε : ℝ} (hε : 0 < ε) :
    ∃ s : Finset Wavevector, ∃ N₀ : ℕ,
      2 ≤ N₀ ∧
      (∀ x : UnitAddTorus (Fin 3),
        ‖torusCellCutoff x -
          finiteScalarFourierReconstruction s
            (UnitAddTorus.mFourierCoeff torusCellCutoff) x‖ < ε) ∧
      ∀ (F : OrientedFrameEquiv) (N : ℕ),
        N₀ ≤ N → ∀ p ∈ s,
          InNormalizedPancakeShift
            localizationTransverseMargin localizationAxialMargin
            (orientedFrameSquareDyadicNormalizedMode F N p) :=
  exists_eventually_margin_finiteFourierApproximation_uniformFrame
    torusCellCutoff summable_mFourierCoeff_torusCellCutoff hε

/-- Every translated member of the spatial cover has a scale-compatible
finite Fourier approximation, uniformly over oriented frames. -/
theorem exists_eventually_margin_spatialCellCutoff_uniformFrame
    (j : SpatialCellIndex) {ε : ℝ} (hε : 0 < ε) :
    ∃ s : Finset Wavevector, ∃ N₀ : ℕ,
      2 ≤ N₀ ∧
      (∀ x : UnitAddTorus (Fin 3),
        ‖spatialCellCutoff j x -
          finiteScalarFourierReconstruction s
            (UnitAddTorus.mFourierCoeff (spatialCellCutoff j)) x‖ < ε) ∧
      ∀ (F : OrientedFrameEquiv) (N : ℕ),
        N₀ ≤ N → ∀ p ∈ s,
          InNormalizedPancakeShift
            localizationTransverseMargin localizationAxialMargin
            (orientedFrameSquareDyadicNormalizedMode F N p) :=
  exists_eventually_margin_finiteFourierApproximation_uniformFrame
    (spatialCellCutoff j)
    (summable_mFourierCoeff_spatialCellCutoff j) hε

/-- **One cutoff scale for the whole cover.**  For any target accuracy, all
`125` concrete cells admit finite Fourier approximations whose supports fit
the localization margin at one common threshold, uniformly over every
oriented frame and every larger square-dyadic scale. -/
theorem exists_uniform_spatialCoverFourierApproximation
    {ε : ℝ} (hε : 0 < ε) :
    ∃ modes : SpatialCellIndex → Finset Wavevector, ∃ N₀ : ℕ,
      2 ≤ N₀ ∧
      (∀ j x,
        ‖spatialCellCutoff j x -
          finiteScalarFourierReconstruction (modes j)
            (UnitAddTorus.mFourierCoeff (spatialCellCutoff j)) x‖ < ε) ∧
      ∀ (j : SpatialCellIndex) (F : OrientedFrameEquiv) (N : ℕ),
        N₀ ≤ N → ∀ p ∈ modes j,
          InNormalizedPancakeShift
            localizationTransverseMargin localizationAxialMargin
            (orientedFrameSquareDyadicNormalizedMode F N p) := by
  have heach : ∀ j : SpatialCellIndex,
      ∃ s : Finset Wavevector, ∃ Nj : ℕ,
        2 ≤ Nj ∧
        (∀ x : UnitAddTorus (Fin 3),
          ‖spatialCellCutoff j x -
            finiteScalarFourierReconstruction s
              (UnitAddTorus.mFourierCoeff (spatialCellCutoff j)) x‖ < ε) ∧
        ∀ (F : OrientedFrameEquiv) (N : ℕ),
          Nj ≤ N → ∀ p ∈ s,
            InNormalizedPancakeShift
              localizationTransverseMargin localizationAxialMargin
              (orientedFrameSquareDyadicNormalizedMode F N p) := by
    intro j
    exact exists_eventually_margin_spatialCellCutoff_uniformFrame j hε
  choose modes cellScale hdata using heach
  let N₀ : ℕ := Finset.univ.sup cellScale
  have hle (j : SpatialCellIndex) : cellScale j ≤ N₀ := by
    exact Finset.le_sup (Finset.mem_univ j)
  let j₀ : SpatialCellIndex := fun _ ↦ 0
  have htwo : 2 ≤ N₀ :=
    (hdata j₀).1.trans (hle j₀)
  refine ⟨modes, N₀, htwo, ?_, ?_⟩
  · intro j x
    exact (hdata j).2.1 x
  · intro j F N hN p hp
    exact (hdata j).2.2 F N ((hle j).trans hN) p hp

end PancakeConcreteSmoothCellCutoff
end NavierStokes
end FluidDynamics
end Mettapedia
