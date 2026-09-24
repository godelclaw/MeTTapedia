import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeConcreteSpatialCoverTransfer
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# Square-dyadic pancake blocks of arbitrary periodic Fourier data

The previous physical multiplier theorems accepted arbitrary coefficients but
asked the caller for a finite ambient support.  A genuine frequency block does
not need this hypothesis: its radial shell is a finite subset of the integer
lattice even when the underlying field has infinitely many nonzero Fourier
coefficients.

This module constructs a concrete finite lattice box at square-dyadic scale,
filters it by the already proved physical shell-and-cone predicate, and applies
the resulting projector to an arbitrary Fourier coefficient field.  It then
specializes both the exact annular coherent identity and the concrete smooth
spatial-cell transfer to these blocks.  No finite-support assumption is made
on the input data.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes
namespace PancakeArbitraryDataBlocks

open PeriodicFourierTriad
open PancakeBilinearPeriodization
open PancakePeriodicCoherentSplit
open PancakeSmoothCoherentSymbol
open PancakeSmoothCoherentStretchSymbol
open PancakeMisalignmentEnergyBridge
open PancakeAnnularChartCutoff
open PancakeAnnularMultiplierAssembly
open PancakeAnnularSectorProjector
open PancakeSquareDyadicSectorProjector
open PancakeFrameCovariance
open PancakeFrozenFrameKernelTransfer
open PancakePhysicalFrameKernelTransfer
open PancakeAnnularPhysicalFrameTransfer
open PancakeBufferedAnnularPhysicalFrameTransfer
open PancakeConcreteSmoothCellCutoff
open PancakeConcreteSpatialCoverTransfer
open MeasureTheory
open scoped BigOperators

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

/-- Full vector-valued finite Parseval identity in the normalization used by
the unit three-torus. -/
theorem integral_complexEuclideanNormSq_finiteFourierReconstruction
    (s : Finset Wavevector) (omega : FourierVelocity) :
    (∫ x : UnitAddTorus (Fin 3),
        complexEuclideanNormSq (finiteFourierReconstruction s omega x)) =
      ∑ k ∈ s, coefficientEnergy (omega k) := by
  have hint (i : Fin 3) :
      MeasureTheory.Integrable (fun x : UnitAddTorus (Fin 3) ↦
        Complex.normSq (finiteFourierReconstruction s omega x i)) := by
    have hcomponent : Continuous (fun x : UnitAddTorus (Fin 3) ↦
        finiteFourierReconstruction s omega x i) :=
      (continuous_apply i).comp
        (continuous_finiteFourierReconstruction s omega)
    have hcont : Continuous (fun x : UnitAddTorus (Fin 3) ↦
        Complex.normSq (finiteFourierReconstruction s omega x i)) :=
      Complex.continuous_normSq.comp hcomponent
    simpa only [MeasureTheory.integrableOn_univ] using
      hcont.continuousOn.integrableOn_compact
        (isCompact_univ : IsCompact (Set.univ : Set (UnitAddTorus (Fin 3))))
  unfold complexEuclideanNormSq coefficientEnergy
  simp only [Fin.sum_univ_three]
  have houter :
      (∫ x : UnitAddTorus (Fin 3),
        (Complex.normSq (finiteFourierReconstruction s omega x 0) +
          Complex.normSq (finiteFourierReconstruction s omega x 1)) +
          Complex.normSq (finiteFourierReconstruction s omega x 2)) =
        (∫ x : UnitAddTorus (Fin 3),
          Complex.normSq (finiteFourierReconstruction s omega x 0) +
            Complex.normSq (finiteFourierReconstruction s omega x 1)) +
        ∫ x : UnitAddTorus (Fin 3),
          Complex.normSq (finiteFourierReconstruction s omega x 2) := by
    simpa only [Pi.add_apply] using
      integral_add ((hint 0).add (hint 1)) (hint 2)
  have hinner :
      (∫ x : UnitAddTorus (Fin 3),
        Complex.normSq (finiteFourierReconstruction s omega x 0) +
          Complex.normSq (finiteFourierReconstruction s omega x 1)) =
        (∫ x : UnitAddTorus (Fin 3),
          Complex.normSq (finiteFourierReconstruction s omega x 0)) +
        ∫ x : UnitAddTorus (Fin 3),
          Complex.normSq (finiteFourierReconstruction s omega x 1) := by
    simpa only [Pi.add_apply] using integral_add (hint 0) (hint 1)
  rw [houter, hinner]
  rw [show (∫ x : UnitAddTorus (Fin 3),
      Complex.normSq (finiteFourierReconstruction s omega x 0)) =
      ∑ k ∈ s, Complex.normSq (omega k 0) by
        simpa only [finiteFourierReconstruction_component] using
          integral_normSq_finiteScalarFourierReconstruction s
            (fun k ↦ omega k 0)]
  rw [show (∫ x : UnitAddTorus (Fin 3),
      Complex.normSq (finiteFourierReconstruction s omega x 1)) =
      ∑ k ∈ s, Complex.normSq (omega k 1) by
        simpa only [finiteFourierReconstruction_component] using
          integral_normSq_finiteScalarFourierReconstruction s
            (fun k ↦ omega k 1)]
  rw [show (∫ x : UnitAddTorus (Fin 3),
      Complex.normSq (finiteFourierReconstruction s omega x 2)) =
      ∑ k ∈ s, Complex.normSq (omega k 2) by
        simpa only [finiteFourierReconstruction_component] using
          integral_normSq_finiteScalarFourierReconstruction s
            (fun k ↦ omega k 2)]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]

/-- The finite centered box of integer wavevectors with every coordinate in
`[-R,R]`. -/
def wavevectorBox (R : ℕ) : Finset Wavevector :=
  Fintype.piFinset (fun _ : Fin 3 ↦ Finset.Icc (-((R : ℤ))) (R : ℤ))

theorem mem_wavevectorBox_iff {R : ℕ} {k : Wavevector} :
    k ∈ wavevectorBox R ↔ ∀ i, |k i| ≤ (R : ℤ) := by
  simp [wavevectorBox, Fintype.mem_piFinset, Finset.mem_Icc, ← abs_le]

/-- A finite ambient box large enough for a radial shell of radius below
`2 N²`.  The filtering predicate itself contains the exact radial shell and
angular aperture conditions. -/
def squareDyadicAmbientModes (N : ℕ) : Finset Wavevector :=
  wavevectorBox (2 * N ^ 2)

/-- Every integer mode whose squared radius is below `4 N⁴` lies in the
ambient box.  Thus the finite enumeration below loses no shell mode. -/
theorem mem_squareDyadicAmbientModes_of_modeSquareNat_lt
    {N : ℕ} {k : Wavevector} (hk : modeSquareNat k < 4 * N ^ 4) :
    k ∈ squareDyadicAmbientModes N := by
  rw [squareDyadicAmbientModes, mem_wavevectorBox_iff]
  intro i
  have hiSq : (k i).natAbs ^ 2 < 4 * N ^ 4 := by
    unfold modeSquareNat at hk
    simp only [Fin.sum_univ_three] at hk
    fin_cases i
    · change (k 0).natAbs ^ 2 < 4 * N ^ 4
      omega
    · change (k 1).natAbs ^ 2 < 4 * N ^ 4
      omega
    · change (k 2).natAbs ^ 2 < 4 * N ^ 4
      omega
  have hi : (k i).natAbs ≤ 2 * N ^ 2 := by
    nlinarith
  rw [Int.abs_eq_natAbs]
  exact_mod_cast hi

/-- The complete finite radial shell `N² ≤ |k| < 2N²`, expressed with
integer squared radii. -/
def squareDyadicShellModes (N : ℕ) : Finset Wavevector :=
  (squareDyadicAmbientModes N).filter fun k ↦
    N ^ 4 ≤ modeSquareNat k ∧ modeSquareNat k < 4 * N ^ 4

theorem mem_squareDyadicShellModes_iff
    (N : ℕ) (k : Wavevector) :
    k ∈ squareDyadicShellModes N ↔
      N ^ 4 ≤ modeSquareNat k ∧ modeSquareNat k < 4 * N ^ 4 := by
  constructor
  · intro hk
    exact (Finset.mem_filter.mp hk).2
  · intro hk
    exact Finset.mem_filter.mpr
      ⟨mem_squareDyadicAmbientModes_of_modeSquareNat_lt hk.2, hk⟩

/-- The usual dyadic frequency radius `2^q`. -/
def dyadicRadius (q : ℕ) : ℕ := 2 ^ q

/-- The complete ordinary dyadic shell
`2^q ≤ |k| < 2^(q+1)`. -/
def dyadicShellModes (q : ℕ) : Finset Wavevector :=
  (wavevectorBox (2 * dyadicRadius q)).filter fun k ↦
    (dyadicRadius q) ^ 2 ≤ modeSquareNat k ∧
      modeSquareNat k < 4 * (dyadicRadius q) ^ 2

theorem mem_wavevectorBox_two_mul_of_modeSquareNat_lt
    {R : ℕ} {k : Wavevector} (hk : modeSquareNat k < 4 * R ^ 2) :
    k ∈ wavevectorBox (2 * R) := by
  rw [mem_wavevectorBox_iff]
  intro i
  have hiSq : (k i).natAbs ^ 2 < 4 * R ^ 2 := by
    unfold modeSquareNat at hk
    simp only [Fin.sum_univ_three] at hk
    fin_cases i
    · change (k 0).natAbs ^ 2 < 4 * R ^ 2
      omega
    · change (k 1).natAbs ^ 2 < 4 * R ^ 2
      omega
    · change (k 2).natAbs ^ 2 < 4 * R ^ 2
      omega
  have hi : (k i).natAbs ≤ 2 * R := by
    nlinarith
  rw [Int.abs_eq_natAbs]
  exact_mod_cast hi

theorem mem_dyadicShellModes_iff (q : ℕ) (k : Wavevector) :
    k ∈ dyadicShellModes q ↔
      (dyadicRadius q) ^ 2 ≤ modeSquareNat k ∧
        modeSquareNat k < 4 * (dyadicRadius q) ^ 2 := by
  constructor
  · intro hk
    exact (Finset.mem_filter.mp hk).2
  · intro hk
    exact Finset.mem_filter.mpr
      ⟨mem_wavevectorBox_two_mul_of_modeSquareNat_lt hk.2, hk⟩

theorem dyadicRadius_sq (q : ℕ) :
    (dyadicRadius q) ^ 2 = 4 ^ q := by
  unfold dyadicRadius
  rw [pow_two, ← mul_pow]
  norm_num

/-- Equivalent base-four form of ordinary dyadic-shell membership. -/
theorem mem_dyadicShellModes_iff_pow_four (q : ℕ) (k : Wavevector) :
    k ∈ dyadicShellModes q ↔
      4 ^ q ≤ modeSquareNat k ∧ modeSquareNat k < 4 ^ (q + 1) := by
  rw [mem_dyadicShellModes_iff, dyadicRadius_sq]
  simp only [pow_succ]
  omega

/-- Every nonzero lattice mode belongs to an ordinary dyadic shell. -/
theorem exists_mem_dyadicShellModes
    (k : Wavevector) (hk : modeSquareNat k ≠ 0) :
    ∃ q : ℕ, k ∈ dyadicShellModes q := by
  let q := Nat.log 4 (modeSquareNat k)
  refine ⟨q, ?_⟩
  rw [mem_dyadicShellModes_iff_pow_four]
  exact ⟨Nat.pow_log_le_self 4 hk,
    Nat.lt_pow_succ_log_self (by omega) (modeSquareNat k)⟩

/-- Strictly ordered ordinary dyadic shells are disjoint. -/
theorem disjoint_dyadicShellModes_of_lt {q r : ℕ} (hqr : q < r) :
    Disjoint (dyadicShellModes q) (dyadicShellModes r) := by
  rw [Finset.disjoint_left]
  intro k hkq hkr
  have hq := (mem_dyadicShellModes_iff_pow_four q k).mp hkq
  have hr := (mem_dyadicShellModes_iff_pow_four r k).mp hkr
  have hpow : 4 ^ (q + 1) ≤ 4 ^ r :=
    Nat.pow_le_pow_right (by omega) (Nat.succ_le_iff.mpr hqr)
  omega

/-- Distinct ordinary dyadic shells are disjoint. -/
theorem disjoint_dyadicShellModes_of_ne {q r : ℕ} (hqr : q ≠ r) :
    Disjoint (dyadicShellModes q) (dyadicShellModes r) := by
  rcases lt_or_gt_of_ne hqr with hlt | hgt
  · exact disjoint_dyadicShellModes_of_lt hlt
  · exact (disjoint_dyadicShellModes_of_lt hgt).symm

/-- No nonzero lattice mode can occur in two different dyadic shells. -/
theorem dyadicShell_index_unique
    {q r : ℕ} {k : Wavevector}
    (hkq : k ∈ dyadicShellModes q) (hkr : k ∈ dyadicShellModes r) :
    q = r := by
  by_contra hne
  exact Finset.disjoint_left.mp (disjoint_dyadicShellModes_of_ne hne)
    hkq hkr

/-- Integral squared frequency vanishes exactly at the zero lattice vector. -/
theorem modeSquareNat_eq_zero_iff (k : Wavevector) :
    modeSquareNat k = 0 ↔ k = 0 := by
  constructor
  · intro h
    unfold modeSquareNat at h
    simp only [Fin.sum_univ_three] at h
    have h0sq : (k 0).natAbs ^ 2 = 0 := by omega
    have h1sq : (k 1).natAbs ^ 2 = 0 := by omega
    have h2sq : (k 2).natAbs ^ 2 = 0 := by omega
    have h0abs : (k 0).natAbs = 0 := by nlinarith
    have h1abs : (k 1).natAbs = 0 := by nlinarith
    have h2abs : (k 2).natAbs = 0 := by nlinarith
    funext i
    fin_cases i
    · exact Int.natAbs_eq_zero.mp h0abs
    · exact Int.natAbs_eq_zero.mp h1abs
    · exact Int.natAbs_eq_zero.mp h2abs
  · rintro rfl
    simp [modeSquareNat]

/-- Nonzero lattice frequencies, which are exactly the frequencies covered by
the ordinary dyadic shells. -/
abbrev NonzeroWavevector := {k : Wavevector // k ≠ 0}

/-- Nonzero wavevectors are the complement of the zero singleton. -/
def nonzeroWavevectorEquivSingletonCompl :
    NonzeroWavevector ≃
      {k : Wavevector // k ∉ ({0} : Finset Wavevector)} where
  toFun k := ⟨k.1, by simpa using k.2⟩
  invFun k := ⟨k.1, by simpa using k.2⟩
  left_inv k := by ext; rfl
  right_inv k := by ext; rfl

/-- The `q`th dyadic shell as a set of nonzero lattice frequencies. -/
def nonzeroDyadicShellSet (q : ℕ) : Set NonzeroWavevector :=
  {k | k.1 ∈ dyadicShellModes q}

/-- The ordinary dyadic shells partition all nonzero lattice frequencies. -/
theorem existsUnique_mem_nonzeroDyadicShellSet (k : NonzeroWavevector) :
    ∃! q : ℕ, k ∈ nonzeroDyadicShellSet q := by
  have hkSq : modeSquareNat k.1 ≠ 0 := by
    intro hk
    exact k.2 ((modeSquareNat_eq_zero_iff k.1).mp hk)
  obtain ⟨q, hq⟩ := exists_mem_dyadicShellModes k.1 hkSq
  refine ⟨q, hq, ?_⟩
  intro r hr
  change k.1 ∈ dyadicShellModes r at hr
  exact (dyadicShell_index_unique hq hr).symm

/-- Forgetting the redundant nonzero proof identifies one set-theoretic shell
with the corresponding finite shell subtype. -/
def nonzeroDyadicShellEquiv (q : ℕ) :
    {k : NonzeroWavevector // k ∈ nonzeroDyadicShellSet q} ≃
      ↥(dyadicShellModes q) where
  toFun k := ⟨k.1.1, k.2⟩
  invFun k :=
    ⟨⟨k.1, by
      have hk := (mem_dyadicShellModes_iff_pow_four q k.1).mp k.2
      have hpow : 0 < 4 ^ q := by positivity
      intro hkzero
      have hsq : modeSquareNat k.1 = 0 :=
        (modeSquareNat_eq_zero_iff k.1).mpr hkzero
      omega⟩, k.2⟩
  left_inv k := by ext; rfl
  right_inv k := by ext; rfl

/-- The hard ordinary Littlewood--Paley shell block of arbitrary Fourier
coefficients. -/
def dyadicShellBlock (q : ℕ) (omega : FourierVelocity) :
    BilinearSpatialTorus → ComplexVec3 :=
  finiteFourierReconstruction (dyadicShellModes q) omega

/-- Parseval-side energy of an ordinary hard dyadic block. -/
def dyadicShellEnergy (q : ℕ) (omega : FourierVelocity) : ℝ :=
  fourierEnergy (dyadicShellModes q) omega

theorem coefficientEnergy_nonneg (v : VelocityCoefficient) :
    0 ≤ coefficientEnergy v := by
  unfold coefficientEnergy
  exact Finset.sum_nonneg fun _ _ ↦ Complex.normSq_nonneg _

theorem dyadicShellEnergy_nonneg (q : ℕ) (omega : FourierVelocity) :
    0 ≤ dyadicShellEnergy q omega := by
  unfold dyadicShellEnergy fourierEnergy
  exact Finset.sum_nonneg fun _ _ ↦ coefficientEnergy_nonneg _

/-- The infinite sum over one set-theoretic nonzero shell is its finite
Parseval energy. -/
theorem tsum_nonzeroDyadicShellSet_eq_dyadicShellEnergy
    (q : ℕ) (omega : FourierVelocity) :
    (∑' k : nonzeroDyadicShellSet q,
        coefficientEnergy (omega k.1.1)) = dyadicShellEnergy q omega := by
  unfold dyadicShellEnergy fourierEnergy
  calc
    (∑' k : nonzeroDyadicShellSet q,
        coefficientEnergy (omega k.1.1)) =
        ∑' k : ↥(dyadicShellModes q), coefficientEnergy (omega k.1) := by
          simpa [nonzeroDyadicShellEquiv] using
            (nonzeroDyadicShellEquiv q).tsum_eq
              (fun k : ↥(dyadicShellModes q) ↦ coefficientEnergy (omega k.1))
    _ = ∑ k ∈ dyadicShellModes q, coefficientEnergy (omega k) :=
      Finset.tsum_subtype (dyadicShellModes q)
        (fun k ↦ coefficientEnergy (omega k))

/-- Exact physical-space/Parseval identification for an arbitrary-data
ordinary dyadic block. -/
theorem integral_complexEuclideanNormSq_dyadicShellBlock
    (q : ℕ) (omega : FourierVelocity) :
    (∫ x : BilinearSpatialTorus,
        complexEuclideanNormSq (dyadicShellBlock q omega x)) =
      dyadicShellEnergy q omega := by
  exact integral_complexEuclideanNormSq_finiteFourierReconstruction
    (dyadicShellModes q) omega

/-- If `N²` brackets the ordinary dyadic radius and adjacent square scales
overlap, the whole ordinary dyadic shell is covered by the two square-dyadic
shells `N` and `N+1`. -/
theorem dyadicShellModes_subset_two_squareDyadicShells
    (q N : ℕ)
    (hlower : N ^ 2 ≤ dyadicRadius q)
    (hupper : dyadicRadius q < (N + 1) ^ 2)
    (hoverlap : (N + 1) ^ 4 ≤ 4 * N ^ 4) :
    dyadicShellModes q ⊆
      squareDyadicShellModes N ∪ squareDyadicShellModes (N + 1) := by
  intro k hk
  have hradius := (mem_dyadicShellModes_iff q k).mp hk
  by_cases hfirst : modeSquareNat k < 4 * N ^ 4
  · apply Finset.mem_union_left
    rw [mem_squareDyadicShellModes_iff]
    constructor
    · nlinarith
    · exact hfirst
  · apply Finset.mem_union_right
    rw [mem_squareDyadicShellModes_iff]
    constructor
    · have hNouter : 4 * N ^ 4 ≤ modeSquareNat k :=
        Nat.le_of_not_gt hfirst
      exact hoverlap.trans hNouter
    · nlinarith

/-- Adjacent square-dyadic shells overlap once `N ≥ 3`. -/
theorem adjacent_squareDyadicShells_overlap
    {N : ℕ} (hN : 3 ≤ N) :
    (N + 1) ^ 4 ≤ 4 * N ^ 4 := by
  have hsq : (N + 1) ^ 2 ≤ 2 * N ^ 2 := by
    nlinarith
  have hpow := Nat.pow_le_pow_left hsq 2
  nlinarith

/-- Canonical lower square scale associated to the ordinary dyadic radius. -/
def squareScaleForDyadic (q : ℕ) : ℕ :=
  Nat.sqrt (dyadicRadius q)

theorem three_le_squareScaleForDyadic {q : ℕ} (hq : 4 ≤ q) :
    3 ≤ squareScaleForDyadic q := by
  have hpow : 16 ≤ dyadicRadius q := by
    unfold dyadicRadius
    have h := Nat.pow_le_pow_right (by decide : 0 < 2) hq
    norm_num at h ⊢
    exact h
  rw [squareScaleForDyadic, Nat.le_sqrt']
  omega

/-- Every ordinary dyadic shell from `q = 4` onward is covered by two
adjacent complete square-dyadic shells, chosen canonically by integer square
root. -/
theorem dyadicShellModes_subset_canonical_squareDyadicShells
    {q : ℕ} (hq : 4 ≤ q) :
    dyadicShellModes q ⊆
      squareDyadicShellModes (squareScaleForDyadic q) ∪
        squareDyadicShellModes (squareScaleForDyadic q + 1) := by
  apply dyadicShellModes_subset_two_squareDyadicShells
  · exact Nat.sqrt_le' (dyadicRadius q)
  · exact Nat.lt_succ_sqrt' (dyadicRadius q)
  · exact adjacent_squareDyadicShells_overlap
      (three_le_squareScaleForDyadic hq)

/-- Disjoint lower piece of an ordinary dyadic shell, assigned to the
canonical lower square scale. -/
def dyadicLowerSquareModes (q : ℕ) : Finset Wavevector :=
  dyadicShellModes q ∩ squareDyadicShellModes (squareScaleForDyadic q)

/-- The remaining modes of the ordinary dyadic shell, assigned to the next
square scale. -/
def dyadicUpperSquareModes (q : ℕ) : Finset Wavevector :=
  dyadicShellModes q \ dyadicLowerSquareModes q

theorem dyadicLowerSquareModes_subset_lowerShell (q : ℕ) :
    dyadicLowerSquareModes q ⊆
      squareDyadicShellModes (squareScaleForDyadic q) :=
  Finset.inter_subset_right

theorem dyadicUpperSquareModes_subset_upperShell
    {q : ℕ} (hq : 4 ≤ q) :
    dyadicUpperSquareModes q ⊆
      squareDyadicShellModes (squareScaleForDyadic q + 1) := by
  intro k hk
  rcases Finset.mem_sdiff.mp hk with ⟨hdyadic, hnotLower⟩
  have hcover :=
    dyadicShellModes_subset_canonical_squareDyadicShells hq hdyadic
  rcases Finset.mem_union.mp hcover with hlower | hupper
  · exact False.elim (hnotLower (Finset.mem_inter.mpr ⟨hdyadic, hlower⟩))
  · exact hupper

theorem dyadicShellModes_eq_lower_union_upper (q : ℕ) :
    dyadicShellModes q =
      dyadicLowerSquareModes q ∪ dyadicUpperSquareModes q := by
  exact (Finset.union_sdiff_of_subset Finset.inter_subset_left).symm

theorem disjoint_dyadicLowerSquareModes_upperSquareModes (q : ℕ) :
    Disjoint (dyadicLowerSquareModes q) (dyadicUpperSquareModes q) :=
  Finset.disjoint_sdiff

/-- The ordinary dyadic block is exactly the sum of its two canonically
assigned square-scale pieces. -/
theorem dyadicShellBlock_eq_lower_add_upper
    (q : ℕ) (omega : FourierVelocity) (x : BilinearSpatialTorus) :
    dyadicShellBlock q omega x =
      finiteFourierReconstruction (dyadicLowerSquareModes q) omega x +
        finiteFourierReconstruction (dyadicUpperSquareModes q) omega x := by
  unfold dyadicShellBlock finiteFourierReconstruction
  rw [dyadicShellModes_eq_lower_union_upper q,
    Finset.sum_union (disjoint_dyadicLowerSquareModes_upperSquareModes q)]

theorem dyadicShellEnergy_eq_lower_add_upper
    (q : ℕ) (omega : FourierVelocity) :
    dyadicShellEnergy q omega =
      fourierEnergy (dyadicLowerSquareModes q) omega +
        fourierEnergy (dyadicUpperSquareModes q) omega := by
  unfold dyadicShellEnergy fourierEnergy
  rw [dyadicShellModes_eq_lower_union_upper q,
    Finset.sum_union (disjoint_dyadicLowerSquareModes_upperSquareModes q)]

/-- Pancake modes inside an arbitrary finite portion of one square-dyadic
shell. -/
def pancakeModesWithin (F : OrientedFrameEquiv) (N : ℕ)
    (s : Finset Wavevector) : Finset Wavevector :=
  squareDyadicPancakeSectorModes F N s

/-- The complementary modes in the same finite portion. -/
def nonpancakeModesWithin (F : OrientedFrameEquiv) (N : ℕ)
    (s : Finset Wavevector) : Finset Wavevector :=
  s \ pancakeModesWithin F N s

theorem pancakeModesWithin_subset
    (F : OrientedFrameEquiv) (N : ℕ) (s : Finset Wavevector) :
    pancakeModesWithin F N s ⊆ s := by
  intro k hk
  exact (mem_squareDyadicPancakeSectorModes_iff F N s k).mp hk |>.1

theorem finiteFourierReconstruction_eq_pancakeWithin_add_nonpancake
    (F : OrientedFrameEquiv) (N : ℕ) (s : Finset Wavevector)
    (omega : FourierVelocity) (x : BilinearSpatialTorus) :
    finiteFourierReconstruction s omega x =
      finiteFourierReconstruction (pancakeModesWithin F N s) omega x +
        finiteFourierReconstruction (nonpancakeModesWithin F N s) omega x := by
  unfold finiteFourierReconstruction nonpancakeModesWithin
  rw [← Finset.sum_union Finset.disjoint_sdiff,
    Finset.union_sdiff_of_subset (pancakeModesWithin_subset F N s)]

theorem fourierEnergy_eq_pancakeWithin_add_nonpancake
    (F : OrientedFrameEquiv) (N : ℕ) (s : Finset Wavevector)
    (omega : FourierVelocity) :
    fourierEnergy s omega =
      fourierEnergy (pancakeModesWithin F N s) omega +
        fourierEnergy (nonpancakeModesWithin F N s) omega := by
  unfold fourierEnergy nonpancakeModesWithin
  rw [← Finset.sum_union Finset.disjoint_sdiff,
    Finset.union_sdiff_of_subset (pancakeModesWithin_subset F N s)]

/-- Named coherent action of two pancake projections of arbitrary coefficient
fields. -/
def pancakeModesWithinCoherentAction
    (F : OrientedFrameEquiv) (N : ℕ)
    (s t : Finset Wavevector) (omega eta : FourierVelocity)
    (x : BilinearSpatialTorus) : ComplexVec3 :=
  orientedFrameInverseComplexLinearMap F
    (∑ k ∈ pancakeModesWithin F N s,
      ∑ l ∈ pancakeModesWithin F N t,
      (UnitAddTorus.mFourier k x * UnitAddTorus.mFourier l x) •
        (((((1 : ℝ) / N) : ℂ)) •
          coherentProjectedNormalizedStretch ((1 : ℝ) / N)
            (frozenFrameSquareDyadicFrequencyPairChart
              (orientedFrameFrequencyPairLinearIsometryEquiv F) N k l)
            (orientedFrameComplexLinearMap F (omega k))
            (orientedFrameComplexLinearMap F (eta l))))

/-- Exact coherent identity on pancake projections of any two finite mode
sets. -/
theorem physicalAnnularAction_on_pancakeModesWithin_eq_coherent
    (F : OrientedFrameEquiv) {N : ℕ} (hN : 2 ≤ N)
    (s t : Finset Wavevector) (omega eta : FourierVelocity)
    (x : BilinearSpatialTorus) :
    physicalOrientedFrameAnnularSquareDyadicKernelAction F N
        (finiteFourierReconstruction (pancakeModesWithin F N s) omega)
        (finiteFourierReconstruction (pancakeModesWithin F N t) eta) x =
      pancakeModesWithinCoherentAction F N s t omega eta x := by
  exact physicalAnnularAction_on_squareDyadicPancakeSectorProjections_eq_coherent
    F hN s t omega eta x

/-- Coefficient `ℓ¹` mass of a pancake projection of a finite shell piece. -/
def pancakeModesWithinCoefficientMass
    (F : OrientedFrameEquiv) (N : ℕ) (s : Finset Wavevector)
    (omega : FourierVelocity) : ℝ :=
  ∑ k ∈ pancakeModesWithin F N s, ‖omega k‖

theorem norm_pancakeModesWithin_reconstruction_le
    (F : OrientedFrameEquiv) (N : ℕ) (s : Finset Wavevector)
    (omega : FourierVelocity) (x : BilinearSpatialTorus) :
    ‖finiteFourierReconstruction (pancakeModesWithin F N s) omega x‖ ≤
      pancakeModesWithinCoefficientMass F N s omega :=
  norm_finiteFourierReconstruction_le _ _ _

/-- **Smooth-cell transfer on an arbitrary-data shell piece.**  A finite
frequency window `s` is applied to arbitrary coefficients, then filtered by
the genuine physical pancake predicate.  Actual smooth localization of the
result converges to the explicit coherent convolution, uniformly in the
frame, cells, window cardinality, and scale. -/
theorem exists_uniform_actualSpatialCells_to_coherent_on_pancakeModesWithin :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {epsilon : ℝ} (P : SpatialCoverFourierPackage epsilon)
        (sourceCell receiverCell : SpatialCellIndex)
        (F : OrientedFrameEquiv) (N : ℕ), P.threshold ≤ N →
      ∀ (sourceWindow receiverWindow : Finset Wavevector)
        (omega eta : FourierVelocity) (x : BilinearSpatialTorus),
        ‖physicalOrientedFrameLocalizationSquareDyadicKernelAction F N
              (fun y ↦ spatialCellCutoff sourceCell y •
                finiteFourierReconstruction
                  (pancakeModesWithin F N sourceWindow) omega y)
              (fun y ↦ spatialCellCutoff receiverCell y •
                finiteFourierReconstruction
                  (pancakeModesWithin F N receiverWindow) eta y) x -
            finiteSpatialCellsCoherentAction P sourceCell receiverCell F N
              (pancakeModesWithin F N sourceWindow)
              (pancakeModesWithin F N receiverWindow) omega eta x‖ ≤
          243 * (C / N) *
              (epsilon * pancakeModesWithinCoefficientMass F N
                sourceWindow omega) *
              (‖torusCellCutoff‖ *
                pancakeModesWithinCoefficientMass F N receiverWindow eta) +
            243 * (C / N) *
              ((epsilon + ‖torusCellCutoff‖) *
                pancakeModesWithinCoefficientMass F N sourceWindow omega) *
              (epsilon * pancakeModesWithinCoefficientMass F N
                receiverWindow eta) := by
  obtain ⟨C, hC, htransfer⟩ :=
    exists_uniform_actualSpatialCells_to_coherent
  refine ⟨C, hC, ?_⟩
  intro epsilon P sourceCell receiverCell F N hN
    sourceWindow receiverWindow omega eta x
  apply htransfer P sourceCell receiverCell F N hN
      (pancakeModesWithin F N sourceWindow)
      (pancakeModesWithin F N receiverWindow)
      omega eta x
      (pancakeModesWithinCoefficientMass F N sourceWindow omega)
      (pancakeModesWithinCoefficientMass F N receiverWindow eta)
  · intro k hk
    apply normalizedMode_mem_of_mem_orientedSquarePancakeConeAnnulus F
      (P.two_le_threshold.trans hN) k
    exact (mem_squareDyadicPancakeSectorModes_iff
      F N sourceWindow k).mp hk |>.2
  · intro l hl
    apply normalizedMode_mem_of_mem_orientedSquarePancakeConeAnnulus F
      (P.two_le_threshold.trans hN) l
    exact (mem_squareDyadicPancakeSectorModes_iff
      F N receiverWindow l).mp hl |>.2
  · exact norm_pancakeModesWithin_reconstruction_le F N sourceWindow omega
  · exact norm_pancakeModesWithin_reconstruction_le F N receiverWindow eta

/-- Lower-square pancake share of the ordinary dyadic block. -/
def dyadicLowerPancakeBlock
    (F : OrientedFrameEquiv) (q : ℕ) (omega : FourierVelocity) :
    BilinearSpatialTorus → ComplexVec3 :=
  finiteFourierReconstruction
    (pancakeModesWithin F (squareScaleForDyadic q)
      (dyadicLowerSquareModes q)) omega

/-- Lower-square nonpancake share of the ordinary dyadic block. -/
def dyadicLowerNonpancakeBlock
    (F : OrientedFrameEquiv) (q : ℕ) (omega : FourierVelocity) :
    BilinearSpatialTorus → ComplexVec3 :=
  finiteFourierReconstruction
    (nonpancakeModesWithin F (squareScaleForDyadic q)
      (dyadicLowerSquareModes q)) omega

/-- Upper-square pancake share of the ordinary dyadic block. -/
def dyadicUpperPancakeBlock
    (F : OrientedFrameEquiv) (q : ℕ) (omega : FourierVelocity) :
    BilinearSpatialTorus → ComplexVec3 :=
  finiteFourierReconstruction
    (pancakeModesWithin F (squareScaleForDyadic q + 1)
      (dyadicUpperSquareModes q)) omega

/-- Upper-square nonpancake share of the ordinary dyadic block. -/
def dyadicUpperNonpancakeBlock
    (F : OrientedFrameEquiv) (q : ℕ) (omega : FourierVelocity) :
    BilinearSpatialTorus → ComplexVec3 :=
  finiteFourierReconstruction
    (nonpancakeModesWithin F (squareScaleForDyadic q + 1)
      (dyadicUpperSquareModes q)) omega

/-- Total Parseval energy in the two pancake shares of one ordinary dyadic
block. -/
def dyadicPancakeEnergy
    (F : OrientedFrameEquiv) (q : ℕ) (omega : FourierVelocity) : ℝ :=
  fourierEnergy
      (pancakeModesWithin F (squareScaleForDyadic q)
        (dyadicLowerSquareModes q)) omega +
    fourierEnergy
      (pancakeModesWithin F (squareScaleForDyadic q + 1)
        (dyadicUpperSquareModes q)) omega

/-- Total Parseval energy in the two nonpancake shares of the same block. -/
def dyadicNonpancakeEnergy
    (F : OrientedFrameEquiv) (q : ℕ) (omega : FourierVelocity) : ℝ :=
  fourierEnergy
      (nonpancakeModesWithin F (squareScaleForDyadic q)
        (dyadicLowerSquareModes q)) omega +
    fourierEnergy
      (nonpancakeModesWithin F (squareScaleForDyadic q + 1)
        (dyadicUpperSquareModes q)) omega

/-- **Actual ordinary-dyadic field split.**  Every hard Littlewood--Paley
block from `q=4` onward is exactly the sum of two pancake shares and two
nonpancake shares at adjacent square scales.  The identity holds for arbitrary
Fourier data. -/
theorem dyadicShellBlock_eq_four_pancake_shares
    (F : OrientedFrameEquiv) (q : ℕ) (omega : FourierVelocity)
    (x : BilinearSpatialTorus) :
    dyadicShellBlock q omega x =
      (dyadicLowerPancakeBlock F q omega x +
        dyadicLowerNonpancakeBlock F q omega x) +
      (dyadicUpperPancakeBlock F q omega x +
        dyadicUpperNonpancakeBlock F q omega x) := by
  rw [dyadicShellBlock_eq_lower_add_upper]
  rw [finiteFourierReconstruction_eq_pancakeWithin_add_nonpancake
    F (squareScaleForDyadic q) (dyadicLowerSquareModes q)]
  rw [finiteFourierReconstruction_eq_pancakeWithin_add_nonpancake
    F (squareScaleForDyadic q + 1) (dyadicUpperSquareModes q)]
  rfl

/-- The Parseval energy of an ordinary dyadic block splits exactly across the
same four disjoint frequency shares. -/
theorem dyadicShellEnergy_eq_four_pancake_shares
    (F : OrientedFrameEquiv) (q : ℕ) (omega : FourierVelocity) :
    dyadicShellEnergy q omega =
      (fourierEnergy
          (pancakeModesWithin F (squareScaleForDyadic q)
            (dyadicLowerSquareModes q)) omega +
        fourierEnergy
          (nonpancakeModesWithin F (squareScaleForDyadic q)
            (dyadicLowerSquareModes q)) omega) +
      (fourierEnergy
          (pancakeModesWithin F (squareScaleForDyadic q + 1)
            (dyadicUpperSquareModes q)) omega +
        fourierEnergy
          (nonpancakeModesWithin F (squareScaleForDyadic q + 1)
            (dyadicUpperSquareModes q)) omega) := by
  rw [dyadicShellEnergy_eq_lower_add_upper]
  rw [fourierEnergy_eq_pancakeWithin_add_nonpancake
    F (squareScaleForDyadic q) (dyadicLowerSquareModes q)]
  rw [fourierEnergy_eq_pancakeWithin_add_nonpancake
    F (squareScaleForDyadic q + 1) (dyadicUpperSquareModes q)]

/-- Exact energy partition of an ordinary dyadic block into its total
pancake and nonpancake shares. -/
theorem dyadicShellEnergy_eq_pancake_add_nonpancake
    (F : OrientedFrameEquiv) (q : ℕ) (omega : FourierVelocity) :
    dyadicShellEnergy q omega =
      dyadicPancakeEnergy F q omega +
        dyadicNonpancakeEnergy F q omega := by
  rw [dyadicShellEnergy_eq_four_pancake_shares]
  unfold dyadicPancakeEnergy dyadicNonpancakeEnergy
  ring

/-- Exact coherent multiplier formula for the lower-square pancake share of
an ordinary dyadic block. -/
theorem physicalAnnularAction_on_dyadicLowerPancakeBlocks_eq_coherent
    (F : OrientedFrameEquiv) {q : ℕ} (hq : 4 ≤ q)
    (omega eta : FourierVelocity) (x : BilinearSpatialTorus) :
    physicalOrientedFrameAnnularSquareDyadicKernelAction F
        (squareScaleForDyadic q)
        (dyadicLowerPancakeBlock F q omega)
        (dyadicLowerPancakeBlock F q eta) x =
      pancakeModesWithinCoherentAction F (squareScaleForDyadic q)
        (dyadicLowerSquareModes q) (dyadicLowerSquareModes q)
        omega eta x := by
  have hscale : 2 ≤ squareScaleForDyadic q :=
    (by omega : 2 ≤ 3).trans (three_le_squareScaleForDyadic hq)
  exact physicalAnnularAction_on_pancakeModesWithin_eq_coherent
    F hscale (dyadicLowerSquareModes q) (dyadicLowerSquareModes q)
      omega eta x

/-- Exact coherent multiplier formula for the upper-square pancake share of
an ordinary dyadic block. -/
theorem physicalAnnularAction_on_dyadicUpperPancakeBlocks_eq_coherent
    (F : OrientedFrameEquiv) {q : ℕ} (hq : 4 ≤ q)
    (omega eta : FourierVelocity) (x : BilinearSpatialTorus) :
    physicalOrientedFrameAnnularSquareDyadicKernelAction F
        (squareScaleForDyadic q + 1)
        (dyadicUpperPancakeBlock F q omega)
        (dyadicUpperPancakeBlock F q eta) x =
      pancakeModesWithinCoherentAction F (squareScaleForDyadic q + 1)
        (dyadicUpperSquareModes q) (dyadicUpperSquareModes q)
        omega eta x := by
  have hbase : 2 ≤ squareScaleForDyadic q :=
    (by omega : 2 ≤ 3).trans (three_le_squareScaleForDyadic hq)
  have hscale : 2 ≤ squareScaleForDyadic q + 1 :=
    hbase.trans (Nat.le_succ _)
  exact physicalAnnularAction_on_pancakeModesWithin_eq_coherent
    F hscale (dyadicUpperSquareModes q) (dyadicUpperSquareModes q)
      omega eta x

/-- The actual finite square-dyadic pancake modes selected from the complete
radial shell at scale `N²` in frame `F`. -/
def squareDyadicPancakeModes (F : OrientedFrameEquiv) (N : ℕ) :
    Finset Wavevector :=
  squareDyadicPancakeSectorModes F N (squareDyadicShellModes N)

theorem mem_squareDyadicPancakeModes_iff
    (F : OrientedFrameEquiv) (N : ℕ) (k : Wavevector) :
    k ∈ squareDyadicPancakeModes F N ↔
      k ∈ squareDyadicShellModes N ∧
        InOrientedSquarePancakeConeAnnulus F N k := by
  exact mem_squareDyadicPancakeSectorModes_iff
    F N (squareDyadicShellModes N) k

theorem squareDyadicPancakeModes_subset_shell
    (F : OrientedFrameEquiv) (N : ℕ) :
    squareDyadicPancakeModes F N ⊆ squareDyadicShellModes N := by
  intro k hk
  exact (mem_squareDyadicPancakeModes_iff F N k).mp hk |>.1

/-- The complementary nonpancake modes in the same complete radial shell. -/
def squareDyadicNonpancakeModes (F : OrientedFrameEquiv) (N : ℕ) :
    Finset Wavevector :=
  squareDyadicShellModes N \ squareDyadicPancakeModes F N

theorem mem_squareDyadicNonpancakeModes_iff
    (F : OrientedFrameEquiv) (N : ℕ) (k : Wavevector) :
    k ∈ squareDyadicNonpancakeModes F N ↔
      k ∈ squareDyadicShellModes N ∧
        ¬ InOrientedSquarePancakeConeAnnulus F N k := by
  rw [squareDyadicNonpancakeModes, Finset.mem_sdiff]
  constructor
  · rintro ⟨hshell, hnot⟩
    refine ⟨hshell, ?_⟩
    intro hcone
    exact hnot ((mem_squareDyadicPancakeModes_iff F N k).mpr
      ⟨hshell, hcone⟩)
  · rintro ⟨hshell, hnot⟩
    refine ⟨hshell, ?_⟩
    intro hpancake
    exact hnot ((mem_squareDyadicPancakeModes_iff F N k).mp hpancake).2

theorem squareDyadicShellModes_eq_pancake_union_nonpancake
    (F : OrientedFrameEquiv) (N : ℕ) :
    squareDyadicShellModes N =
      squareDyadicPancakeModes F N ∪ squareDyadicNonpancakeModes F N := by
  exact (Finset.union_sdiff_of_subset
    (squareDyadicPancakeModes_subset_shell F N)).symm

theorem disjoint_squareDyadicPancakeModes_nonpancakeModes
    (F : OrientedFrameEquiv) (N : ℕ) :
    Disjoint (squareDyadicPancakeModes F N)
      (squareDyadicNonpancakeModes F N) := by
  exact Finset.disjoint_sdiff

/-- Every selected mode automatically satisfies the normalized annular
premise used by the coherent multiplier. -/
theorem normalizedMode_mem_of_mem_squareDyadicPancakeModes
    (F : OrientedFrameEquiv) {N : ℕ} (hN : 2 ≤ N) {k : Wavevector}
    (hk : k ∈ squareDyadicPancakeModes F N) :
    InNormalizedPancakeAnnulus
      (orientedFrameSquareDyadicNormalizedMode F N k) := by
  apply normalizedMode_mem_of_mem_orientedSquarePancakeConeAnnulus F hN k
  exact (mem_squareDyadicPancakeModes_iff F N k).mp hk |>.2

/-- The full hard radial block at square-dyadic scale. -/
def squareDyadicShellBlock (N : ℕ) (omega : FourierVelocity) :
    BilinearSpatialTorus → ComplexVec3 :=
  finiteFourierReconstruction (squareDyadicShellModes N) omega

/-- The hard square-dyadic pancake block of an arbitrary coefficient field.
The result is a trigonometric polynomial because the frequency block, not the
input data, is finite. -/
def squareDyadicPancakeBlock
    (F : OrientedFrameEquiv) (N : ℕ) (omega : FourierVelocity) :
    BilinearSpatialTorus → ComplexVec3 :=
  finiteFourierReconstruction (squareDyadicPancakeModes F N) omega

/-- The nonpancake complement of the hard block. -/
def squareDyadicNonpancakeBlock
    (F : OrientedFrameEquiv) (N : ℕ) (omega : FourierVelocity) :
    BilinearSpatialTorus → ComplexVec3 :=
  finiteFourierReconstruction (squareDyadicNonpancakeModes F N) omega

/-- Exact field-level shell decomposition into pancake and nonpancake
shares, for completely arbitrary Fourier coefficients. -/
theorem squareDyadicShellBlock_eq_pancake_add_nonpancake
    (F : OrientedFrameEquiv) (N : ℕ) (omega : FourierVelocity)
    (x : BilinearSpatialTorus) :
    squareDyadicShellBlock N omega x =
      squareDyadicPancakeBlock F N omega x +
        squareDyadicNonpancakeBlock F N omega x := by
  unfold squareDyadicShellBlock squareDyadicPancakeBlock
    squareDyadicNonpancakeBlock finiteFourierReconstruction
  rw [squareDyadicShellModes_eq_pancake_union_nonpancake F N,
    Finset.sum_union
      (disjoint_squareDyadicPancakeModes_nonpancakeModes F N)]

theorem continuous_squareDyadicPancakeBlock
    (F : OrientedFrameEquiv) (N : ℕ) (omega : FourierVelocity) :
    Continuous (squareDyadicPancakeBlock F N omega) :=
  continuous_finiteFourierReconstruction _ _

/-- The coefficient `ℓ¹` mass of one concrete square-dyadic pancake block. -/
def squareDyadicPancakeCoefficientMass
    (F : OrientedFrameEquiv) (N : ℕ) (omega : FourierVelocity) : ℝ :=
  ∑ k ∈ squareDyadicPancakeModes F N, ‖omega k‖

theorem norm_squareDyadicPancakeBlock_le
    (F : OrientedFrameEquiv) (N : ℕ) (omega : FourierVelocity)
    (x : BilinearSpatialTorus) :
    ‖squareDyadicPancakeBlock F N omega x‖ ≤
      squareDyadicPancakeCoefficientMass F N omega :=
  norm_finiteFourierReconstruction_le _ _ _

/-- Exact coherent kernel formula on square-dyadic pancake blocks of
arbitrary Fourier data.  There is no ambient finite-support argument. -/
theorem physicalAnnularAction_on_squareDyadicPancakeBlocks_eq_coherent
    (F : OrientedFrameEquiv) {N : ℕ} (hN : 2 ≤ N)
    (omega eta : FourierVelocity) (x : BilinearSpatialTorus) :
    physicalOrientedFrameAnnularSquareDyadicKernelAction F N
        (squareDyadicPancakeBlock F N omega)
        (squareDyadicPancakeBlock F N eta) x =
      orientedFrameInverseComplexLinearMap F
        (∑ k ∈ squareDyadicPancakeModes F N,
          ∑ l ∈ squareDyadicPancakeModes F N,
          (UnitAddTorus.mFourier k x * UnitAddTorus.mFourier l x) •
            (((((1 : ℝ) / N) : ℂ)) •
              coherentProjectedNormalizedStretch ((1 : ℝ) / N)
                (frozenFrameSquareDyadicFrequencyPairChart
                  (orientedFrameFrequencyPairLinearIsometryEquiv F) N k l)
                (orientedFrameComplexLinearMap F (omega k))
                (orientedFrameComplexLinearMap F (eta l)))) := by
  exact physicalAnnularAction_on_squareDyadicPancakeSectorProjections_eq_coherent
    F hN (squareDyadicShellModes N) (squareDyadicShellModes N)
      omega eta x

/-- Componentwise Fourier coefficients of an arbitrary complex vector field
on the unit three-torus. -/
def torusFourierVelocity
    (u : BilinearSpatialTorus → ComplexVec3) : FourierVelocity :=
  fun k i ↦ UnitAddTorus.mFourierCoeff (fun x ↦ u x i) k

/-- A square-integrable complex velocity field, represented componentwise on
the unit three-torus. -/
abbrev TorusL2Velocity :=
  Fin 3 → Lp ℂ 2 (volume : Measure BilinearSpatialTorus)

/-- Fourier coefficients of a componentwise `L²` velocity field. -/
def l2FourierVelocity (u : TorusL2Velocity) : FourierVelocity :=
  fun k i ↦ UnitAddTorus.mFourierCoeff (u i) k

/-- Total componentwise physical `L²` energy. -/
def totalL2VelocityEnergy (u : TorusL2Velocity) : ℝ :=
  ∑ i : Fin 3, ∫ x : BilinearSpatialTorus, ‖u i x‖ ^ 2

/-- Vector-valued Parseval identity for genuine `L²` data. -/
theorem hasSum_coefficientEnergy_l2FourierVelocity
    (u : TorusL2Velocity) :
    HasSum (fun k : Wavevector ↦ coefficientEnergy (l2FourierVelocity u k))
      (totalL2VelocityEnergy u) := by
  have h0 := UnitAddTorus.hasSum_sq_mFourierCoeff (u 0)
  have h1 := UnitAddTorus.hasSum_sq_mFourierCoeff (u 1)
  have h2 := UnitAddTorus.hasSum_sq_mFourierCoeff (u 2)
  simpa [l2FourierVelocity, totalL2VelocityEnergy, coefficientEnergy,
    Fin.sum_univ_three, Complex.sq_norm] using (h0.add h1).add h2

/-- The ordinary dyadic shell energies of every componentwise `L²` velocity
field form a summable nonnegative series. -/
theorem summable_dyadicShellEnergy_l2FourierVelocity
    (u : TorusL2Velocity) :
    Summable (fun q : ℕ ↦ dyadicShellEnergy q (l2FourierVelocity u)) := by
  have hglobal : Summable (fun k : Wavevector ↦
      coefficientEnergy (l2FourierVelocity u k)) :=
    (hasSum_coefficientEnergy_l2FourierVelocity u).summable
  have hnonzero : Summable (fun k : NonzeroWavevector ↦
      coefficientEnergy (l2FourierVelocity u k.1)) :=
    hglobal.subtype (fun k : Wavevector ↦ k ≠ 0)
  have hpartition :=
    (summable_partition
      (fun k : NonzeroWavevector ↦
        coefficientEnergy_nonneg (l2FourierVelocity u k.1))
      existsUnique_mem_nonzeroDyadicShellSet).mp hnonzero
  simpa only [tsum_nonzeroDyadicShellSet_eq_dyadicShellEnergy] using
    hpartition.2

/-- Reindexing by the unique dyadic shell loses no nonzero Fourier energy. -/
theorem tsum_dyadicShellEnergy_eq_tsum_nonzero_l2FourierVelocity
    (u : TorusL2Velocity) :
    (∑' q : ℕ, dyadicShellEnergy q (l2FourierVelocity u)) =
      ∑' k : NonzeroWavevector,
        coefficientEnergy (l2FourierVelocity u k.1) := by
  let f : NonzeroWavevector → ℝ := fun k ↦
    coefficientEnergy (l2FourierVelocity u k.1)
  let e := Set.sigmaEquiv nonzeroDyadicShellSet
    existsUnique_mem_nonzeroDyadicShellSet
  have hglobal : Summable (fun k : Wavevector ↦
      coefficientEnergy (l2FourierVelocity u k)) :=
    (hasSum_coefficientEnergy_l2FourierVelocity u).summable
  have hnonzero : Summable f := by
    exact hglobal.subtype (fun k : Wavevector ↦ k ≠ 0)
  have hsigma : Summable (fun p : (Σ q, nonzeroDyadicShellSet q) ↦ f p.2) := by
    simpa [e, f, Function.comp_def, Set.sigmaEquiv] using
      (e.summable_iff.mpr hnonzero)
  calc
    (∑' q : ℕ, dyadicShellEnergy q (l2FourierVelocity u)) =
        ∑' q : ℕ, ∑' k : nonzeroDyadicShellSet q, f k := by
          congr 1
          funext q
          exact (tsum_nonzeroDyadicShellSet_eq_dyadicShellEnergy
            q (l2FourierVelocity u)).symm
    _ = ∑' p : (Σ q, nonzeroDyadicShellSet q), f p.2 :=
      hsigma.tsum_sigma.symm
    _ = ∑' k : NonzeroWavevector, f k := by
      simpa [e, Set.sigmaEquiv] using e.tsum_eq f

/-- The zero Fourier mode plus the complete dyadic-shell ledger is exactly the
physical `L²` energy. -/
theorem zeroModeEnergy_add_tsum_dyadicShellEnergy_l2FourierVelocity
    (u : TorusL2Velocity) :
    coefficientEnergy (l2FourierVelocity u 0) +
        (∑' q : ℕ, dyadicShellEnergy q (l2FourierVelocity u)) =
      totalL2VelocityEnergy u := by
  let g : Wavevector → ℝ := fun k ↦
    coefficientEnergy (l2FourierVelocity u k)
  have hsum : Summable g :=
    (hasSum_coefficientEnergy_l2FourierVelocity u).summable
  have hreindex :
      (∑' k : NonzeroWavevector, g k.1) =
        ∑' k : {k : Wavevector // k ∉ ({0} : Finset Wavevector)}, g k.1 := by
    simpa [nonzeroWavevectorEquivSingletonCompl] using
      nonzeroWavevectorEquivSingletonCompl.tsum_eq
        (fun k : {k : Wavevector // k ∉ ({0} : Finset Wavevector)} ↦ g k.1)
  calc
    coefficientEnergy (l2FourierVelocity u 0) +
          (∑' q : ℕ, dyadicShellEnergy q (l2FourierVelocity u)) =
        g 0 + ∑' k : NonzeroWavevector, g k.1 := by
          rw [tsum_dyadicShellEnergy_eq_tsum_nonzero_l2FourierVelocity]
    _ = g 0 +
        ∑' k : {k : Wavevector // k ∉ ({0} : Finset Wavevector)}, g k.1 := by
          rw [hreindex]
    _ = ∑' k : Wavevector, g k := by
      simpa using hsum.sum_add_tsum_subtype_compl ({0} : Finset Wavevector)
    _ = totalL2VelocityEnergy u :=
      (hasSum_coefficientEnergy_l2FourierVelocity u).tsum_eq

/-- Equivalently, the shell series is the physical energy with the conserved
spatial mean removed. -/
theorem tsum_dyadicShellEnergy_l2FourierVelocity
    (u : TorusL2Velocity) :
    (∑' q : ℕ, dyadicShellEnergy q (l2FourierVelocity u)) =
      totalL2VelocityEnergy u -
        coefficientEnergy (l2FourierVelocity u 0) := by
  linarith [zeroModeEnergy_add_tsum_dyadicShellEnergy_l2FourierVelocity u]

/-- For mean-zero `L²` data, the dyadic shell energies sum to the entire
physical energy. -/
theorem tsum_dyadicShellEnergy_eq_total_of_zeroMode
    (u : TorusL2Velocity) (hzero : l2FourierVelocity u 0 = 0) :
    (∑' q : ℕ, dyadicShellEnergy q (l2FourierVelocity u)) =
      totalL2VelocityEnergy u := by
  rw [tsum_dyadicShellEnergy_l2FourierVelocity, hzero]
  simp [coefficientEnergy]

/-- Joint continuity of a time-dependent periodic field implies continuity of
each of its Fourier coefficients in time. -/
theorem continuous_torusFourierVelocity_of_continuous_uncurry
    (u : ℝ → BilinearSpatialTorus → ComplexVec3)
    (hu : Continuous u.uncurry) (k : Wavevector) (i : Fin 3) :
    Continuous (fun t ↦ torusFourierVelocity (u t) k i) := by
  have hintegrand : Continuous (fun p : ℝ × BilinearSpatialTorus ↦
      UnitAddTorus.mFourier (-k) p.2 • u p.1 p.2 i) := by
    fun_prop
  have hparam := continuous_parametric_integral_of_continuous
    (μ := (volume : Measure BilinearSpatialTorus))
    (f := fun t x ↦ UnitAddTorus.mFourier (-k) x • u t x i)
    hintegrand (isCompact_univ : IsCompact (Set.univ : Set BilinearSpatialTorus))
  simpa [torusFourierVelocity, UnitAddTorus.mFourierCoeff] using hparam

/-- Physical-space hard dyadic block of an arbitrary periodic vector field. -/
def dyadicShellBlockOfField
    (q : ℕ) (u : BilinearSpatialTorus → ComplexVec3) :
    BilinearSpatialTorus → ComplexVec3 :=
  dyadicShellBlock q (torusFourierVelocity u)

/-- The actual dyadic Parseval-energy time profile of a time-dependent
periodic vector field. -/
def dyadicShellEnergyTimeProfile
    (u : ℝ → BilinearSpatialTorus → ComplexVec3) (q : ℕ) (t : ℝ) : ℝ :=
  dyadicShellEnergy q (torusFourierVelocity (u t))

/-- Finite-shell energy is continuous in time whenever every Fourier
coefficient is continuous in time. -/
theorem continuous_dyadicShellEnergy_of_continuous_coefficients
    (omega : ℝ → FourierVelocity)
    (homega : ∀ k i, Continuous (fun t ↦ omega t k i)) (q : ℕ) :
    Continuous (fun t ↦ dyadicShellEnergy q (omega t)) := by
  unfold dyadicShellEnergy fourierEnergy coefficientEnergy
  apply continuous_finsetSum
  intro k hk
  apply continuous_finsetSum
  intro i hi
  exact Complex.continuous_normSq.comp (homega k i)

theorem intervalIntegrable_dyadicShellEnergy_of_continuous_coefficients
    (omega : ℝ → FourierVelocity)
    (homega : ∀ k i, Continuous (fun t ↦ omega t k i))
    (q : ℕ) (a b : ℝ) :
    IntervalIntegrable (fun t ↦ dyadicShellEnergy q (omega t)) volume a b :=
  (continuous_dyadicShellEnergy_of_continuous_coefficients
    omega homega q).intervalIntegrable a b

/-- Its pancake share in a supplied frozen frame at each time. -/
def dyadicPancakeEnergyTimeProfile
    (u : ℝ → BilinearSpatialTorus → ComplexVec3)
    (F : ℝ → OrientedFrameEquiv) (q : ℕ) (t : ℝ) : ℝ :=
  dyadicPancakeEnergy (F t) q (torusFourierVelocity (u t))

/-- Its nonpancake share in the same frozen frame. -/
def dyadicNonpancakeEnergyTimeProfile
    (u : ℝ → BilinearSpatialTorus → ComplexVec3)
    (F : ℝ → OrientedFrameEquiv) (q : ℕ) (t : ℝ) : ℝ :=
  dyadicNonpancakeEnergy (F t) q (torusFourierVelocity (u t))

theorem dyadicShellEnergyTimeProfile_eq_pancake_add_nonpancake
    (u : ℝ → BilinearSpatialTorus → ComplexVec3)
    (F : ℝ → OrientedFrameEquiv) (q : ℕ) (t : ℝ) :
    dyadicShellEnergyTimeProfile u q t =
      dyadicPancakeEnergyTimeProfile u F q t +
        dyadicNonpancakeEnergyTimeProfile u F q t := by
  exact dyadicShellEnergy_eq_pancake_add_nonpancake
    (F t) q (torusFourierVelocity (u t))

theorem dyadicShellEnergyTimeProfile_nonneg
    (u : ℝ → BilinearSpatialTorus → ComplexVec3) (q : ℕ) (t : ℝ) :
    0 ≤ dyadicShellEnergyTimeProfile u q t :=
  dyadicShellEnergy_nonneg q (torusFourierVelocity (u t))

theorem intervalIntegrable_dyadicShellEnergyTimeProfile
    (u : ℝ → BilinearSpatialTorus → ComplexVec3)
    (hcoeff : ∀ k i, Continuous
      (fun t ↦ torusFourierVelocity (u t) k i))
    (q : ℕ) (a b : ℝ) :
    IntervalIntegrable (dyadicShellEnergyTimeProfile u q) volume a b := by
  exact intervalIntegrable_dyadicShellEnergy_of_continuous_coefficients
    (fun t ↦ torusFourierVelocity (u t)) hcoeff q a b

/-- Jointly continuous periodic fields have interval-integrable dyadic energy
profiles on every finite time interval. -/
theorem intervalIntegrable_dyadicShellEnergyTimeProfile_of_continuous_uncurry
    (u : ℝ → BilinearSpatialTorus → ComplexVec3)
    (hu : Continuous u.uncurry) (q : ℕ) (a b : ℝ) :
    IntervalIntegrable (dyadicShellEnergyTimeProfile u q) volume a b := by
  apply intervalIntegrable_dyadicShellEnergyTimeProfile u
  intro k i
  exact continuous_torusFourierVelocity_of_continuous_uncurry u hu k i

/-- At every time, the coefficient energy profile is exactly the physical
`L²` energy of the corresponding hard dyadic block. -/
theorem integral_complexEuclideanNormSq_dyadicShellBlockOfField
    (q : ℕ) (u : BilinearSpatialTorus → ComplexVec3) :
    (∫ x : BilinearSpatialTorus,
        complexEuclideanNormSq (dyadicShellBlockOfField q u x)) =
      dyadicShellEnergy q (torusFourierVelocity u) := by
  exact integral_complexEuclideanNormSq_dyadicShellBlock
    q (torusFourierVelocity u)

/-- The concrete hard pancake block of a periodic vector field. -/
def squareDyadicPancakeBlockOfField
    (F : OrientedFrameEquiv) (N : ℕ)
    (u : BilinearSpatialTorus → ComplexVec3) :
    BilinearSpatialTorus → ComplexVec3 :=
  squareDyadicPancakeBlock F N (torusFourierVelocity u)

theorem continuous_squareDyadicPancakeBlockOfField
    (F : OrientedFrameEquiv) (N : ℕ)
    (u : BilinearSpatialTorus → ComplexVec3) :
    Continuous (squareDyadicPancakeBlockOfField F N u) :=
  continuous_squareDyadicPancakeBlock _ _ _

/-- **Concrete smooth-cell transfer for arbitrary Fourier data.**  For every
pair of actual cover cells and every sufficiently large scale, their localized
hard pancake blocks differ from the explicit coherent finite convolution by
the stated `O(epsilon/N)` error.  The bound contains the actual coefficient
masses of the two blocks and no hypothesis that the input data are finitely
supported. -/
theorem exists_uniform_actualSpatialCells_to_coherent_on_arbitraryDataBlocks :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {epsilon : ℝ} (P : SpatialCoverFourierPackage epsilon)
        (sourceCell receiverCell : SpatialCellIndex)
        (F : OrientedFrameEquiv) (N : ℕ), P.threshold ≤ N →
      ∀ (omega eta : FourierVelocity) (x : BilinearSpatialTorus),
        ‖physicalOrientedFrameLocalizationSquareDyadicKernelAction F N
              (fun y ↦ spatialCellCutoff sourceCell y •
                squareDyadicPancakeBlock F N omega y)
              (fun y ↦ spatialCellCutoff receiverCell y •
                squareDyadicPancakeBlock F N eta y) x -
            finiteSpatialCellsCoherentAction P sourceCell receiverCell F N
              (squareDyadicPancakeModes F N)
              (squareDyadicPancakeModes F N) omega eta x‖ ≤
          243 * (C / N) *
              (epsilon * squareDyadicPancakeCoefficientMass F N omega) *
              (‖torusCellCutoff‖ *
                squareDyadicPancakeCoefficientMass F N eta) +
            243 * (C / N) *
              ((epsilon + ‖torusCellCutoff‖) *
                squareDyadicPancakeCoefficientMass F N omega) *
              (epsilon * squareDyadicPancakeCoefficientMass F N eta) := by
  obtain ⟨C, hC, htransfer⟩ :=
    exists_uniform_actualSpatialCells_to_coherent
  refine ⟨C, hC, ?_⟩
  intro epsilon P sourceCell receiverCell F N hN omega eta x
  apply htransfer P sourceCell receiverCell F N hN
      (squareDyadicPancakeModes F N) (squareDyadicPancakeModes F N)
      omega eta x
      (squareDyadicPancakeCoefficientMass F N omega)
      (squareDyadicPancakeCoefficientMass F N eta)
  · intro k hk
    exact normalizedMode_mem_of_mem_squareDyadicPancakeModes F
      (P.two_le_threshold.trans hN) hk
  · intro l hl
    exact normalizedMode_mem_of_mem_squareDyadicPancakeModes F
      (P.two_le_threshold.trans hN) hl
  · exact norm_squareDyadicPancakeBlock_le F N omega
  · exact norm_squareDyadicPancakeBlock_le F N eta

/-- Field-level specialization of the arbitrary-coefficient theorem. -/
theorem exists_uniform_actualSpatialCells_to_coherent_on_periodicFieldBlocks :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {epsilon : ℝ} (P : SpatialCoverFourierPackage epsilon)
        (sourceCell receiverCell : SpatialCellIndex)
        (F : OrientedFrameEquiv) (N : ℕ), P.threshold ≤ N →
      ∀ (u v : BilinearSpatialTorus → ComplexVec3)
        (x : BilinearSpatialTorus),
        ‖physicalOrientedFrameLocalizationSquareDyadicKernelAction F N
              (fun y ↦ spatialCellCutoff sourceCell y •
                squareDyadicPancakeBlockOfField F N u y)
              (fun y ↦ spatialCellCutoff receiverCell y •
                squareDyadicPancakeBlockOfField F N v y) x -
            finiteSpatialCellsCoherentAction P sourceCell receiverCell F N
              (squareDyadicPancakeModes F N)
              (squareDyadicPancakeModes F N)
              (torusFourierVelocity u) (torusFourierVelocity v) x‖ ≤
          243 * (C / N) *
              (epsilon * squareDyadicPancakeCoefficientMass F N
                (torusFourierVelocity u)) *
              (‖torusCellCutoff‖ *
                squareDyadicPancakeCoefficientMass F N
                  (torusFourierVelocity v)) +
            243 * (C / N) *
              ((epsilon + ‖torusCellCutoff‖) *
                squareDyadicPancakeCoefficientMass F N
                  (torusFourierVelocity u)) *
              (epsilon * squareDyadicPancakeCoefficientMass F N
                (torusFourierVelocity v)) := by
  obtain ⟨C, hC, htransfer⟩ :=
    exists_uniform_actualSpatialCells_to_coherent_on_arbitraryDataBlocks
  refine ⟨C, hC, ?_⟩
  intro epsilon P sourceCell receiverCell F N hN u v x
  simpa [squareDyadicPancakeBlockOfField] using
    htransfer P sourceCell receiverCell F N hN
      (torusFourierVelocity u) (torusFourierVelocity v) x

end PancakeArbitraryDataBlocks
end NavierStokes
end FluidDynamics
end Mettapedia
