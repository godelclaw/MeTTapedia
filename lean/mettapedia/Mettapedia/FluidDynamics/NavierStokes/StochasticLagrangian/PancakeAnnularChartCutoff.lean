import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeSmoothCoherentStretchSymbol
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeConeLatticeCount

/-!
# Four signed charts for the normalized pancake annulus

The square-dyadic pancake annulus has two connected axial components for each
frequency: positive and negative.  This module constructs the resulting four
source/receiver charts.  Each chart uses a compact six-dimensional bump and
two signed axial gates.  The gates keep both coherent-line denominators away
from their axial degeneracy, while the six-dimensional bump supplies compact
support.

No finite frequency catalogue is involved: the four charts are the four
connected sign components of the same normalized annular geometry.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes
namespace PancakeAnnularChartCutoff

open PancakeRealCoherentPairEstimate
open PancakeCoherentStretchFactorization
open PancakeSmoothCoherentStretchSymbol
open PancakeConeLatticeCount
open scoped ContDiff

/-- The two connected axial components of a pancake annulus. -/
inductive AxialSign where
  | positive
  | negative
  deriving DecidableEq, Fintype

def AxialSign.opposite : AxialSign → AxialSign
  | .positive => .negative
  | .negative => .positive

/-- The center of the signed normalized axial interval. -/
def axialChartCenter : AxialSign → ℝ
  | .positive => 3 / 2
  | .negative => -(3 / 2)

/-- Center of a source/receiver sign chart. -/
def annularPairCenter (sourceSign receiverSign : AxialSign) : FrequencyPair :=
  ((0, 0, axialChartCenter sourceSign),
    (0, 0, axialChartCenter receiverSign))

/-- Compact retained bump in all six normalized frequency variables. -/
def annularPairInnerBump (sourceSign receiverSign : AxialSign) :
    ContDiffBump (annularPairCenter sourceSign receiverSign) :=
  ⟨9 / 4, 5 / 2, by norm_num, by norm_num⟩

/-- A wider six-dimensional buffer which is one on the retained bump. -/
def annularPairOuterBump (sourceSign receiverSign : AxialSign) :
    ContDiffBump (annularPairCenter sourceSign receiverSign) :=
  ⟨5 / 2, 3, by norm_num, by norm_num⟩

/-- Retained signed axial gate.  It is one on the interval of distance at
most `3/4` from the signed center and vanishes outside distance `1`. -/
def annularAxialInnerBump (sign : AxialSign) :
    ContDiffBump (axialChartCenter sign) :=
  ⟨3 / 4, 1, by norm_num, by norm_num⟩

/-- Wider signed axial buffer.  Its support remains at distance at least
`1/4` from zero. -/
def annularAxialOuterBump (sign : AxialSign) :
    ContDiffBump (axialChartCenter sign) :=
  ⟨1, 5 / 4, by norm_num, by norm_num⟩

/-- The compact retained cutoff for one source/receiver sign pair. -/
def annularStretchInner (sourceSign receiverSign : AxialSign)
    (p : FrequencyPair) : ℝ :=
  annularPairInnerBump sourceSign receiverSign p *
    annularAxialInnerBump sourceSign p.1.2.2 *
    annularAxialInnerBump receiverSign p.2.2.2

/-- The wider buffer for one source/receiver sign pair. -/
def annularStretchOuter (sourceSign receiverSign : AxialSign)
    (p : FrequencyPair) : ℝ :=
  annularPairOuterBump sourceSign receiverSign p *
    annularAxialOuterBump sourceSign p.1.2.2 *
    annularAxialOuterBump receiverSign p.2.2.2

theorem contDiff_sourceAxial :
    ContDiff ℝ ∞ (fun p : FrequencyPair ↦ p.1.2.2) := by
  fun_prop

theorem contDiff_receiverAxial :
    ContDiff ℝ ∞ (fun p : FrequencyPair ↦ p.2.2.2) := by
  fun_prop

theorem contDiff_annularStretchInner (sourceSign receiverSign : AxialSign) :
    ContDiff ℝ ∞ (annularStretchInner sourceSign receiverSign) := by
  exact ((annularPairInnerBump sourceSign receiverSign).contDiff.mul
      ((annularAxialInnerBump sourceSign).contDiff.comp contDiff_sourceAxial)).mul
    ((annularAxialInnerBump receiverSign).contDiff.comp contDiff_receiverAxial)

theorem contDiff_annularStretchOuter (sourceSign receiverSign : AxialSign) :
    ContDiff ℝ ∞ (annularStretchOuter sourceSign receiverSign) := by
  exact ((annularPairOuterBump sourceSign receiverSign).contDiff.mul
      ((annularAxialOuterBump sourceSign).contDiff.comp contDiff_sourceAxial)).mul
    ((annularAxialOuterBump receiverSign).contDiff.comp contDiff_receiverAxial)

theorem hasCompactSupport_annularStretchInner
    (sourceSign receiverSign : AxialSign) :
    HasCompactSupport (annularStretchInner sourceSign receiverSign) := by
  exact (annularPairInnerBump sourceSign receiverSign).hasCompactSupport.mul_right.mul_right

theorem annularPairOuterBump_eq_one_of_inner_ne_zero
    (sourceSign receiverSign : AxialSign) (p : FrequencyPair)
    (hp : annularPairInnerBump sourceSign receiverSign p ≠ 0) :
    annularPairOuterBump sourceSign receiverSign p = 1 := by
  apply (annularPairOuterBump sourceSign receiverSign).one_of_mem_closedBall
  have hmem : p ∈ Function.support
      (annularPairInnerBump sourceSign receiverSign) := hp
  rw [(annularPairInnerBump sourceSign receiverSign).support_eq] at hmem
  change dist p (annularPairCenter sourceSign receiverSign) < 5 / 2 at hmem
  change dist p (annularPairCenter sourceSign receiverSign) ≤ 5 / 2
  exact hmem.le

theorem annularAxialOuterBump_eq_one_of_inner_ne_zero
    (sign : AxialSign) (z : ℝ)
    (hz : annularAxialInnerBump sign z ≠ 0) :
    annularAxialOuterBump sign z = 1 := by
  apply (annularAxialOuterBump sign).one_of_mem_closedBall
  have hmem : z ∈ Function.support (annularAxialInnerBump sign) := hz
  rw [(annularAxialInnerBump sign).support_eq] at hmem
  change dist z (axialChartCenter sign) < 1 at hmem
  change dist z (axialChartCenter sign) ≤ 1
  exact hmem.le

theorem annularStretchOuter_eq_one_of_inner_ne_zero
    (sourceSign receiverSign : AxialSign) (p : FrequencyPair)
    (hp : annularStretchInner sourceSign receiverSign p ≠ 0) :
    annularStretchOuter sourceSign receiverSign p = 1 := by
  have hpair : annularPairInnerBump sourceSign receiverSign p ≠ 0 := by
    intro hzero
    apply hp
    simp [annularStretchInner, hzero]
  have hsource : annularAxialInnerBump sourceSign p.1.2.2 ≠ 0 := by
    intro hzero
    apply hp
    simp [annularStretchInner, hzero]
  have hreceiver : annularAxialInnerBump receiverSign p.2.2.2 ≠ 0 := by
    intro hzero
    apply hp
    simp [annularStretchInner, hzero]
  rw [annularStretchOuter,
    annularPairOuterBump_eq_one_of_inner_ne_zero _ _ _ hpair,
    annularAxialOuterBump_eq_one_of_inner_ne_zero _ _ hsource,
    annularAxialOuterBump_eq_one_of_inner_ne_zero _ _ hreceiver]
  norm_num

/-- Every nonzero signed outer gate quantitatively avoids the axial origin. -/
theorem quarter_lt_abs_of_annularAxialOuterBump_ne_zero
    (sign : AxialSign) (z : ℝ)
    (hz : annularAxialOuterBump sign z ≠ 0) :
    (1 : ℝ) / 4 < |z| := by
  have hmem : z ∈ Function.support (annularAxialOuterBump sign) := hz
  rw [(annularAxialOuterBump sign).support_eq] at hmem
  have hdist : dist z (axialChartCenter sign) < 5 / 4 := by
    simpa [annularAxialOuterBump] using hmem
  cases sign with
  | positive =>
      have habs : |z - 3 / 2| < 5 / 4 := by
        simpa [axialChartCenter, Real.dist_eq] using hdist
      have hzpos : 1 / 4 < z := by
        have := (abs_lt.mp habs).1
        linarith
      simpa [abs_of_pos (by linarith : 0 < z)] using hzpos
  | negative =>
      have habs : |z - (-(3 / 2))| < 5 / 4 := by
        simpa [axialChartCenter, Real.dist_eq] using hdist
      have hzneg : z < -(1 / 4) := by
        have := (abs_lt.mp habs).2
        linarith
      rw [abs_of_neg (by linarith : z < 0)]
      linarith

theorem source_axial_ne_of_annularStretchOuter_ne_zero
    (sourceSign receiverSign : AxialSign) (p : FrequencyPair)
    (hp : annularStretchOuter sourceSign receiverSign p ≠ 0) :
    p.1.2.2 ≠ 0 := by
  have hgate : annularAxialOuterBump sourceSign p.1.2.2 ≠ 0 := by
    intro hzero
    apply hp
    simp [annularStretchOuter, hzero]
  have hquarter := quarter_lt_abs_of_annularAxialOuterBump_ne_zero
    sourceSign p.1.2.2 hgate
  exact fun hzero ↦ by norm_num [hzero] at hquarter

theorem receiver_axial_ne_of_annularStretchOuter_ne_zero
    (sourceSign receiverSign : AxialSign) (p : FrequencyPair)
    (hp : annularStretchOuter sourceSign receiverSign p ≠ 0) :
    p.2.2.2 ≠ 0 := by
  have hgate : annularAxialOuterBump receiverSign p.2.2.2 ≠ 0 := by
    intro hzero
    apply hp
    simp [annularStretchOuter, hzero]
  have hquarter := quarter_lt_abs_of_annularAxialOuterBump_ne_zero
    receiverSign p.2.2.2 hgate
  exact fun hzero ↦ by norm_num [hzero] at hquarter

theorem annular_source_denominator_ne
    (sourceSign receiverSign : AxialSign) (delta : ℝ) (p : FrequencyPair) :
    normSq (coherentW (sourceFrequency delta p)) +
      (1 - annularStretchOuter sourceSign receiverSign p) ^ 2 ≠ 0 := by
  by_cases hp : annularStretchOuter sourceSign receiverSign p = 0
  · have hnonneg := normSq_nonneg (coherentW (sourceFrequency delta p))
    rw [hp]
    norm_num
    linarith
  · have hz := source_axial_ne_of_annularStretchOuter_ne_zero
      sourceSign receiverSign p hp
    have hpos := normSq_coherentW_scaled_pos delta
      p.1.1 p.1.2.1 p.1.2.2 hz
    unfold sourceFrequency
    nlinarith [sq_nonneg (1 - annularStretchOuter sourceSign receiverSign p)]

theorem annular_receiver_denominator_ne
    (sourceSign receiverSign : AxialSign) (delta : ℝ) (p : FrequencyPair) :
    normSq (coherentW (receiverFrequency delta p)) +
      (1 - annularStretchOuter sourceSign receiverSign p) ^ 2 ≠ 0 := by
  by_cases hp : annularStretchOuter sourceSign receiverSign p = 0
  · have hnonneg := normSq_nonneg (coherentW (receiverFrequency delta p))
    rw [hp]
    norm_num
    linarith
  · have hz := receiver_axial_ne_of_annularStretchOuter_ne_zero
      sourceSign receiverSign p hp
    have hpos := normSq_coherentW_scaled_pos delta
      p.2.1 p.2.2.1 p.2.2.2 hz
    unfold receiverFrequency
    nlinarith [sq_nonneg (1 - annularStretchOuter sourceSign receiverSign p)]

/-- One of the four buffered charts on the normalized pancake annulus. -/
def annularBufferedStretchCutoff
    (sourceSign receiverSign : AxialSign) : BufferedStretchCutoff where
  inner := annularStretchInner sourceSign receiverSign
  outer := annularStretchOuter sourceSign receiverSign
  inner_contDiff := contDiff_annularStretchInner sourceSign receiverSign
  outer_contDiff := contDiff_annularStretchOuter sourceSign receiverSign
  inner_compact := hasCompactSupport_annularStretchInner sourceSign receiverSign
  outer_eq_one_on_inner :=
    annularStretchOuter_eq_one_of_inner_ne_zero sourceSign receiverSign
  source_denominator_ne := annular_source_denominator_ne sourceSign receiverSign
  receiver_denominator_ne := annular_receiver_denominator_ne sourceSign receiverSign

/-! ## Coverage of the square-dyadic annulus -/

/-- The dyadic annulus inside the existing square pancake cone ball.  Its
physical radius lies between `N²` and `2 N²`. -/
def InSquarePancakeConeAnnulus (N : ℕ) (k : Lattice3) : Prop :=
  InSquarePancakeConeBall N k ∧ (N : ℤ) ^ 4 ≤ latticeNormSq k

/-- A lattice vector in normalized square-dyadic pancake coordinates. -/
def squareDyadicNormalizedLatticeVector (N : ℕ) (k : Lattice3) : RealVec3 :=
  ((k.1 : ℝ) / N, (k.2.1 : ℝ) / N, (k.2.2 : ℝ) / (N ^ 2))

/-- A source/receiver lattice pair in the normalized six-frequency chart. -/
def squareDyadicNormalizedLatticePair
    (N : ℕ) (k l : Lattice3) : FrequencyPair :=
  (squareDyadicNormalizedLatticeVector N k,
    squareDyadicNormalizedLatticeVector N l)

/-- The cone aperture forces at least three quarters of the squared radial
mass into the axial coordinate. -/
theorem three_mul_norm_le_four_mul_axial_sq
    {N : ℕ} {k : Lattice3} (hN : 2 ≤ N)
    (hk : InSquarePancakeConeBall N k) :
    3 * latticeNormSq k ≤ 4 * k.2.2 ^ 2 := by
  obtain ⟨x, y, z⟩ := k
  rcases hk with ⟨_hNpos, _hnorm, _houter, hcone⟩
  have hN2 : (4 : ℤ) ≤ (N : ℤ) ^ 2 := by
    have hNZ : (2 : ℤ) ≤ N := by exact_mod_cast hN
    nlinarith
  have htrans : 0 ≤ x ^ 2 + y ^ 2 := by positivity
  have hscale : 0 ≤ ((N : ℤ) ^ 2 - 4) * (x ^ 2 + y ^ 2) :=
    mul_nonneg (by linarith) htrans
  simp only [latticeNormSq] at hcone ⊢
  nlinarith

/-- On the dyadic annulus the axial magnitude is at least `3/4` of the
inner shell radius. -/
theorem nine_mul_shell_le_sixteen_mul_axial_sq
    {N : ℕ} {k : Lattice3} (hN : 2 ≤ N)
    (hk : InSquarePancakeConeAnnulus N k) :
    9 * (N : ℤ) ^ 4 ≤ 16 * k.2.2 ^ 2 := by
  have haxial := three_mul_norm_le_four_mul_axial_sq hN hk.1
  have hinner := hk.2
  nlinarith

/-- Both normalized transverse coordinates lie in `[-2,2]`. -/
theorem normalized_transverse_abs_le_two
    {N : ℕ} {k : Lattice3} (hk : InSquarePancakeConeBall N k) :
    |(k.1 : ℝ) / N| ≤ 2 ∧ |(k.2.1 : ℝ) / N| ≤ 2 := by
  obtain ⟨x, y, z⟩ := k
  have hbox := mem_pancakeBox_of_mem_coneBall hk
  change (x, y, z) ∈
      transverseRange N ×ˢ (transverseRange N ×ˢ axialRange N) at hbox
  rw [Finset.mem_product, Finset.mem_product, transverseRange, axialRange,
    Finset.mem_Icc, Finset.mem_Icc, Finset.mem_Icc] at hbox
  rcases hbox with ⟨⟨hxlo, hxhi⟩, ⟨⟨hylo, hyhi⟩, _hz⟩⟩
  have hNR : 0 < (N : ℝ) := by exact_mod_cast hk.1
  have hxloR : -(2 * (N : ℝ)) ≤ (x : ℝ) := by exact_mod_cast hxlo
  have hxhiR : (x : ℝ) ≤ 2 * (N : ℝ) := by exact_mod_cast hxhi
  have hyloR : -(2 * (N : ℝ)) ≤ (y : ℝ) := by exact_mod_cast hylo
  have hyhiR : (y : ℝ) ≤ 2 * (N : ℝ) := by exact_mod_cast hyhi
  constructor <;> rw [abs_le] <;> constructor
  · exact (le_div_iff₀ hNR).2 (by nlinarith)
  · exact (div_le_iff₀ hNR).2 (by nlinarith)
  · exact (le_div_iff₀ hNR).2 (by nlinarith)
  · exact (div_le_iff₀ hNR).2 (by nlinarith)

/-- The normalized axial magnitude lies in `[3/4,2]` on the annulus. -/
theorem normalized_axial_abs_mem
    {N : ℕ} {k : Lattice3} (hNlarge : 2 ≤ N)
    (hk : InSquarePancakeConeAnnulus N k) :
    (3 : ℝ) / 4 ≤ |(k.2.2 : ℝ) / (N ^ 2)| ∧
      |(k.2.2 : ℝ) / (N ^ 2)| ≤ 2 := by
  obtain ⟨x, y, z⟩ := k
  have hN : 0 < N := hk.1.1
  have hN2R : 0 < (N : ℝ) ^ 2 := by positivity
  have hlowerZ := nine_mul_shell_le_sixteen_mul_axial_sq hNlarge hk
  have hupperZ : z ^ 2 ≤ 4 * (N : ℤ) ^ 4 := by
    have houter := hk.1.2.2.1
    simp only [latticeNormSq] at houter
    nlinarith [sq_nonneg x, sq_nonneg y]
  have hlowerR : 9 * (N : ℝ) ^ 4 ≤ 16 * (z : ℝ) ^ 2 := by
    exact_mod_cast hlowerZ
  have hupperR : (z : ℝ) ^ 2 ≤ 4 * (N : ℝ) ^ 4 := by
    exact_mod_cast hupperZ
  have hlowerSq : (3 * (N : ℝ) ^ 2) ^ 2 ≤ (4 * (z : ℝ)) ^ 2 := by
    nlinarith
  have hupperSq : ((z : ℝ)) ^ 2 ≤ (2 * (N : ℝ) ^ 2) ^ 2 := by
    nlinarith
  have hlowerAbs := (sq_le_sq.mp hlowerSq)
  have hupperAbs := (sq_le_sq.mp hupperSq)
  have hN2nonneg : 0 ≤ (N : ℝ) ^ 2 := hN2R.le
  have hlower : 3 * (N : ℝ) ^ 2 ≤ 4 * |(z : ℝ)| := by
    simpa [abs_mul, abs_of_nonneg hN2nonneg] using hlowerAbs
  have hupper : |(z : ℝ)| ≤ 2 * (N : ℝ) ^ 2 := by
    simpa [abs_mul, abs_of_nonneg hN2nonneg] using hupperAbs
  rw [abs_div, abs_of_pos hN2R]
  constructor
  · exact (le_div_iff₀ hN2R).2 (by nlinarith)
  · exact (div_le_iff₀ hN2R).2 hupper

/-- Every annular lattice vector lies within the retained radius of one signed
axial center. -/
theorem exists_sign_axial_center_dist_le
    {N : ℕ} {k : Lattice3} (hN : 2 ≤ N)
    (hk : InSquarePancakeConeAnnulus N k) :
    ∃ sign : AxialSign,
      dist (squareDyadicNormalizedLatticeVector N k).2.2
        (axialChartCenter sign) ≤ 3 / 4 := by
  let q : ℝ := (k.2.2 : ℝ) / (N ^ 2)
  have hqabs := normalized_axial_abs_mem hN hk
  change (3 : ℝ) / 4 ≤ |q| ∧ |q| ≤ 2 at hqabs
  by_cases hq : 0 ≤ q
  · refine ⟨.positive, ?_⟩
    have hqlo : 3 / 4 ≤ q := by simpa [abs_of_nonneg hq] using hqabs.1
    have hqhi : q ≤ 2 := by simpa [abs_of_nonneg hq] using hqabs.2
    change dist q (3 / 2) ≤ 3 / 4
    rw [Real.dist_eq, abs_le]
    constructor <;> linarith
  · refine ⟨.negative, ?_⟩
    have hqneg : q < 0 := lt_of_not_ge hq
    have hqlo : 3 / 4 ≤ -q := by
      simpa [abs_of_neg hqneg] using hqabs.1
    have hqhi : -q ≤ 2 := by
      simpa [abs_of_neg hqneg] using hqabs.2
    change dist q (-(3 / 2)) ≤ 3 / 4
    rw [Real.dist_eq, abs_le]
    constructor <;> linarith

/-- Every annular lattice vector belongs to one of the two signed axial
retained gates. -/
theorem exists_sign_axialInnerBump_eq_one
    {N : ℕ} {k : Lattice3} (hN : 2 ≤ N)
    (hk : InSquarePancakeConeAnnulus N k) :
    ∃ sign : AxialSign,
      annularAxialInnerBump sign
        (squareDyadicNormalizedLatticeVector N k).2.2 = 1 := by
  obtain ⟨sign, hdist⟩ := exists_sign_axial_center_dist_le hN hk
  refine ⟨sign, ?_⟩
  exact (annularAxialInnerBump sign).one_of_mem_closedBall hdist

/-- Every pair of annular source/receiver modes is retained identically by
one of the four signed six-frequency charts. -/
theorem exists_sign_pair_annularStretchInner_eq_one
    {N : ℕ} {k l : Lattice3} (hN : 2 ≤ N)
    (hk : InSquarePancakeConeAnnulus N k)
    (hl : InSquarePancakeConeAnnulus N l) :
    ∃ sourceSign receiverSign : AxialSign,
      annularStretchInner sourceSign receiverSign
        (squareDyadicNormalizedLatticePair N k l) = 1 := by
  obtain ⟨sourceSign, hsourceAxial⟩ :=
    exists_sign_axial_center_dist_le hN hk
  obtain ⟨receiverSign, hreceiverAxial⟩ :=
    exists_sign_axial_center_dist_le hN hl
  refine ⟨sourceSign, receiverSign, ?_⟩
  have hktrans := normalized_transverse_abs_le_two hk.1
  have hltrans := normalized_transverse_abs_le_two hl.1
  have hNR : 0 < (N : ℝ) := by exact_mod_cast hk.1.1
  have hpair : annularPairInnerBump sourceSign receiverSign
      (squareDyadicNormalizedLatticePair N k l) = 1 := by
    apply (annularPairInnerBump sourceSign receiverSign).one_of_mem_closedBall
    change dist (squareDyadicNormalizedLatticePair N k l)
      (annularPairCenter sourceSign receiverSign) ≤ 9 / 4
    simp only [squareDyadicNormalizedLatticePair,
      squareDyadicNormalizedLatticeVector, annularPairCenter, Prod.dist_eq,
      max_le_iff]
    constructor
    · constructor
      · simpa [Real.dist_eq, abs_div, abs_of_pos hNR] using
          hktrans.1.trans (by norm_num : (2 : ℝ) ≤ 9 / 4)
      · constructor
        · simpa [Real.dist_eq, abs_div, abs_of_pos hNR] using
            hktrans.2.trans (by norm_num : (2 : ℝ) ≤ 9 / 4)
        · exact hsourceAxial.trans (by norm_num)
    · constructor
      · simpa [Real.dist_eq, abs_div, abs_of_pos hNR] using
          hltrans.1.trans (by norm_num : (2 : ℝ) ≤ 9 / 4)
      · constructor
        · simpa [Real.dist_eq, abs_div, abs_of_pos hNR] using
            hltrans.2.trans (by norm_num : (2 : ℝ) ≤ 9 / 4)
        · exact hreceiverAxial.trans (by norm_num)
  have hsource : annularAxialInnerBump sourceSign
      (squareDyadicNormalizedLatticeVector N k).2.2 = 1 :=
    (annularAxialInnerBump sourceSign).one_of_mem_closedBall hsourceAxial
  have hreceiver : annularAxialInnerBump receiverSign
      (squareDyadicNormalizedLatticeVector N l).2.2 = 1 :=
    (annularAxialInnerBump receiverSign).one_of_mem_closedBall hreceiverAxial
  rw [annularStretchInner, hpair]
  change (1 : ℝ) *
      annularAxialInnerBump sourceSign
        (squareDyadicNormalizedLatticeVector N k).2.2 *
      annularAxialInnerBump receiverSign
        (squareDyadicNormalizedLatticeVector N l).2.2 = 1
  rw [hsource, hreceiver]
  norm_num

/-! ## Coordinate-free normalized-chart coverage -/

/-- The elementary box forced by a normalized square-dyadic pancake annulus.
This formulation applies equally to lattice modes expressed in an arbitrary
frozen orthogonal frame. -/
def InNormalizedPancakeAnnulus (v : RealVec3) : Prop :=
  |v.1| ≤ 2 ∧ |v.2.1| ≤ 2 ∧ 3 / 4 ≤ |v.2.2| ∧ |v.2.2| ≤ 2

theorem exists_sign_center_dist_le_of_mem_normalizedAnnulus
    {v : RealVec3} (hv : InNormalizedPancakeAnnulus v) :
    ∃ sign : AxialSign, dist v.2.2 (axialChartCenter sign) ≤ 3 / 4 := by
  by_cases hz : 0 ≤ v.2.2
  · refine ⟨.positive, ?_⟩
    have hzlo : 3 / 4 ≤ v.2.2 := by
      simpa [abs_of_nonneg hz] using hv.2.2.1
    have hzhi : v.2.2 ≤ 2 := by
      simpa [abs_of_nonneg hz] using hv.2.2.2
    change dist v.2.2 (3 / 2) ≤ 3 / 4
    rw [Real.dist_eq, abs_le]
    constructor <;> linarith
  · refine ⟨.negative, ?_⟩
    have hzneg : v.2.2 < 0 := lt_of_not_ge hz
    have hzlo : 3 / 4 ≤ -v.2.2 := by
      simpa [abs_of_neg hzneg] using hv.2.2.1
    have hzhi : -v.2.2 ≤ 2 := by
      simpa [abs_of_neg hzneg] using hv.2.2.2
    change dist v.2.2 (-(3 / 2)) ≤ 3 / 4
    rw [Real.dist_eq, abs_le]
    constructor <;> linarith

theorem annularAxialInnerBump_opposite_eq_zero
    (sign : AxialSign) (z : ℝ)
    (hdist : dist z (axialChartCenter sign) ≤ 3 / 4) :
    annularAxialInnerBump sign.opposite z = 0 := by
  by_contra hne
  have hmem : z ∈ Function.support (annularAxialInnerBump sign.opposite) := hne
  rw [(annularAxialInnerBump sign.opposite).support_eq] at hmem
  have hopposite : dist z (axialChartCenter sign.opposite) < 1 := by
    simpa [annularAxialInnerBump] using hmem
  cases sign with
  | positive =>
      have hnear : |z - 3 / 2| ≤ 3 / 4 := by
        simpa [axialChartCenter, Real.dist_eq] using hdist
      have hfar : |z - (-(3 / 2))| < 1 := by
        simpa [AxialSign.opposite, axialChartCenter, Real.dist_eq] using hopposite
      have hnearBounds := abs_le.mp hnear
      have hfarBounds := abs_lt.mp hfar
      linarith
  | negative =>
      have hnear : |z - (-(3 / 2))| ≤ 3 / 4 := by
        simpa [axialChartCenter, Real.dist_eq] using hdist
      have hfar : |z - 3 / 2| < 1 := by
        simpa [AxialSign.opposite, axialChartCenter, Real.dist_eq] using hopposite
      have hnearBounds := abs_le.mp hnear
      have hfarBounds := abs_lt.mp hfar
      linarith
/-- Any pair in the normalized annular box is retained identically by one of
the four charts.  This is the form used after an arbitrary frozen rotation. -/
theorem exists_sign_pair_inner_eq_one_of_mem_normalizedAnnulus
    {u v : RealVec3} (hu : InNormalizedPancakeAnnulus u)
    (hv : InNormalizedPancakeAnnulus v) :
    ∃ sourceSign receiverSign : AxialSign,
      annularStretchInner sourceSign receiverSign (u, v) = 1 := by
  obtain ⟨sourceSign, hsourceAxial⟩ :=
    exists_sign_center_dist_le_of_mem_normalizedAnnulus hu
  obtain ⟨receiverSign, hreceiverAxial⟩ :=
    exists_sign_center_dist_le_of_mem_normalizedAnnulus hv
  refine ⟨sourceSign, receiverSign, ?_⟩
  have hpair : annularPairInnerBump sourceSign receiverSign (u, v) = 1 := by
    apply (annularPairInnerBump sourceSign receiverSign).one_of_mem_closedBall
    change dist (u, v) (annularPairCenter sourceSign receiverSign) ≤ 9 / 4
    simp only [annularPairCenter, Prod.dist_eq, max_le_iff]
    constructor
    · constructor
      · simpa [Real.dist_eq] using hu.1.trans (by norm_num : (2 : ℝ) ≤ 9 / 4)
      · constructor
        · simpa [Real.dist_eq] using hu.2.1.trans (by norm_num : (2 : ℝ) ≤ 9 / 4)
        · exact hsourceAxial.trans (by norm_num)
    · constructor
      · simpa [Real.dist_eq] using hv.1.trans (by norm_num : (2 : ℝ) ≤ 9 / 4)
      · constructor
        · simpa [Real.dist_eq] using hv.2.1.trans (by norm_num : (2 : ℝ) ≤ 9 / 4)
        · exact hreceiverAxial.trans (by norm_num)
  have hsource : annularAxialInnerBump sourceSign u.2.2 = 1 :=
    (annularAxialInnerBump sourceSign).one_of_mem_closedBall hsourceAxial
  have hreceiver : annularAxialInnerBump receiverSign v.2.2 = 1 :=
    (annularAxialInnerBump receiverSign).one_of_mem_closedBall hreceiverAxial
  rw [annularStretchInner, hpair, hsource, hreceiver]
  norm_num

/-- Explicit sum of the four signed retained cutoffs. -/
def annularFourChartInner (p : FrequencyPair) : ℝ :=
  annularStretchInner .positive .positive p +
  annularStretchInner .positive .negative p +
  annularStretchInner .negative .positive p +
  annularStretchInner .negative .negative p

/-- The four signed cutoffs form an exact partition on the normalized
pancake annulus. -/
theorem annularFourChartInner_eq_one_of_mem_normalizedAnnulus
    {u v : RealVec3} (hu : InNormalizedPancakeAnnulus u)
    (hv : InNormalizedPancakeAnnulus v) :
    annularFourChartInner (u, v) = 1 := by
  obtain ⟨sourceSign, hsourceDist⟩ :=
    exists_sign_center_dist_le_of_mem_normalizedAnnulus hu
  obtain ⟨receiverSign, hreceiverDist⟩ :=
    exists_sign_center_dist_le_of_mem_normalizedAnnulus hv
  have hsource : annularAxialInnerBump sourceSign u.2.2 = 1 :=
    (annularAxialInnerBump sourceSign).one_of_mem_closedBall hsourceDist
  have hsourceOpposite :
      annularAxialInnerBump sourceSign.opposite u.2.2 = 0 :=
    annularAxialInnerBump_opposite_eq_zero sourceSign u.2.2 hsourceDist
  have hreceiver : annularAxialInnerBump receiverSign v.2.2 = 1 :=
    (annularAxialInnerBump receiverSign).one_of_mem_closedBall hreceiverDist
  have hreceiverOpposite :
      annularAxialInnerBump receiverSign.opposite v.2.2 = 0 :=
    annularAxialInnerBump_opposite_eq_zero receiverSign v.2.2 hreceiverDist
  have hpair : annularPairInnerBump sourceSign receiverSign (u, v) = 1 := by
    apply (annularPairInnerBump sourceSign receiverSign).one_of_mem_closedBall
    change dist (u, v) (annularPairCenter sourceSign receiverSign) ≤ 9 / 4
    simp only [annularPairCenter, Prod.dist_eq, max_le_iff]
    constructor
    · constructor
      · simpa [Real.dist_eq] using hu.1.trans (by norm_num : (2 : ℝ) ≤ 9 / 4)
      · constructor
        · simpa [Real.dist_eq] using hu.2.1.trans (by norm_num : (2 : ℝ) ≤ 9 / 4)
        · exact hsourceDist.trans (by norm_num)
    · constructor
      · simpa [Real.dist_eq] using hv.1.trans (by norm_num : (2 : ℝ) ≤ 9 / 4)
      · constructor
        · simpa [Real.dist_eq] using hv.2.1.trans (by norm_num : (2 : ℝ) ≤ 9 / 4)
        · exact hreceiverDist.trans (by norm_num)
  cases sourceSign <;> cases receiverSign <;>
    simp [AxialSign.opposite] at hsourceOpposite hreceiverOpposite <;>
    simp [annularFourChartInner, annularStretchInner,
      hpair, hsource, hsourceOpposite, hreceiver, hreceiverOpposite]

theorem normalizedLatticeVector_mem_normalizedAnnulus
    {N : ℕ} {k : Lattice3} (hN : 2 ≤ N)
    (hk : InSquarePancakeConeAnnulus N k) :
    InNormalizedPancakeAnnulus
      (squareDyadicNormalizedLatticeVector N k) := by
  have htrans := normalized_transverse_abs_le_two hk.1
  have haxial := normalized_axial_abs_mem hN hk
  exact ⟨htrans.1, htrans.2, haxial.1, haxial.2⟩

end PancakeAnnularChartCutoff
end NavierStokes
end FluidDynamics
end Mettapedia
