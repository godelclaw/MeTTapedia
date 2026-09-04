import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeAnnularSectorProjector

/-!
# The physical square-dyadic pancake-sector projector

The four-chart multiplier is valid on a normalized rectangular annulus.  This
module defines the narrower physical microlocal sector: radial frequency in
`[N², 2 N²)` and squared angular aperture at most `1/N²`, after rotation into
an arbitrary oriented frame.  It proves that every mode in this genuine
shell-and-cone sector lies in the normalized annulus used by the multiplier.

Consequently the exact physical coherent-action formula applies to the
concrete finite Fourier shell-and-cone projections without a user-supplied
support hypothesis.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes
namespace PancakeSquareDyadicSectorProjector

open PeriodicFourierTriad
open PancakeBilinearPeriodization
open PancakeFiniteFourierBilinearTransfer
open PancakePeriodicCoherentSplit
open PancakeRealCoherentPairEstimate
open PancakeSmoothCoherentSymbol
open PancakeSmoothCoherentStretchSymbol
open PancakeFrameCovariance
open PancakeFrozenFrameKernelTransfer
open PancakePhysicalFrameKernelTransfer
open PancakeAnnularChartCutoff
open PancakeAnnularMultiplierAssembly
open PancakeAnnularPhysicalFrameTransfer
open PancakeAnnularSectorProjector

/-- Coordinates of an integer Fourier mode after rotation into the chosen
oriented frame. -/
def orientedFrameWavevectorCoordinates
    (F : OrientedFrameEquiv) (k : Wavevector) : RealVec3 :=
  let ξ := orientedFrameEuclideanLinearIsometryEquiv F
    (euclideanWavevectorOfWavevector k)
  (ξ 0, ξ 1, ξ 2)

/-- Square-dyadic normalization of real frame coordinates. -/
def squareDyadicNormalizeReal (N : ℕ) (v : RealVec3) : RealVec3 :=
  (v.1 / N, v.2.1 / N, v.2.2 / (N ^ 2))

theorem orientedFrameSquareDyadicNormalizedMode_eq
    (F : OrientedFrameEquiv) (N : ℕ) (k : Wavevector) :
    orientedFrameSquareDyadicNormalizedMode F N k =
      squareDyadicNormalizeReal N (orientedFrameWavevectorCoordinates F k) := by
  rfl

/-- The real shell-and-cone predicate underlying the square-dyadic pancake
sector.  Its radial frequency is in `[N², 2 N²)`, and its squared transverse
aperture is at most `1/N²`. -/
def InRealSquarePancakeConeAnnulus (N : ℕ) (v : RealVec3) : Prop :=
  0 < N ∧
  0 < normSq v ∧
  (N : ℝ) ^ 4 ≤ normSq v ∧
  normSq v < 4 * (N : ℝ) ^ 4 ∧
  (N : ℝ) ^ 2 * (v.1 ^ 2 + v.2.1 ^ 2) ≤ normSq v

/-- The aperture condition places at least three quarters of the squared
radial mass in the axial coordinate. -/
theorem three_mul_normSq_le_four_mul_axial_sq
    {N : ℕ} {v : RealVec3} (hN : 2 ≤ N)
    (hv : InRealSquarePancakeConeAnnulus N v) :
    3 * normSq v ≤ 4 * v.2.2 ^ 2 := by
  obtain ⟨x, y, z⟩ := v
  have hN2 : (4 : ℝ) ≤ (N : ℝ) ^ 2 := by
    have hNR : (2 : ℝ) ≤ N := by exact_mod_cast hN
    nlinarith
  have htrans : 0 ≤ x ^ 2 + y ^ 2 := by positivity
  have hscale : 0 ≤ ((N : ℝ) ^ 2 - 4) * (x ^ 2 + y ^ 2) :=
    mul_nonneg (by linarith) htrans
  rcases hv with ⟨_hNpos, _hnorm, _hinner, _houter, hcone⟩
  simp only [normSq, dot] at hcone ⊢
  nlinarith

/-- The true shell-and-cone geometry forces both normalized transverse
coordinates into `[-2,2]`. -/
theorem normalized_transverse_abs_le_two
    {N : ℕ} {v : RealVec3}
    (hv : InRealSquarePancakeConeAnnulus N v) :
    |(squareDyadicNormalizeReal N v).1| ≤ 2 ∧
      |(squareDyadicNormalizeReal N v).2.1| ≤ 2 := by
  obtain ⟨x, y, z⟩ := v
  rcases hv with ⟨hN, _hnorm, _hinner, houter, hcone⟩
  have hNR : 0 < (N : ℝ) := by exact_mod_cast hN
  have hN2R : 0 < (N : ℝ) ^ 2 := sq_pos_of_pos hNR
  have hxprod : (N : ℝ) ^ 2 * x ^ 2 <
      (N : ℝ) ^ 2 * (4 * (N : ℝ) ^ 2) := by
    simp only [normSq, dot] at houter hcone
    nlinarith [sq_nonneg y]
  have hyprod : (N : ℝ) ^ 2 * y ^ 2 <
      (N : ℝ) ^ 2 * (4 * (N : ℝ) ^ 2) := by
    simp only [normSq, dot] at houter hcone
    nlinarith [sq_nonneg x]
  have hx2 : x ^ 2 < 4 * (N : ℝ) ^ 2 :=
    lt_of_mul_lt_mul_left (by simpa [mul_assoc] using hxprod) hN2R.le
  have hy2 : y ^ 2 < 4 * (N : ℝ) ^ 2 :=
    lt_of_mul_lt_mul_left (by simpa [mul_assoc] using hyprod) hN2R.le
  have hxlo : -(2 * (N : ℝ)) ≤ x := by nlinarith
  have hxhi : x ≤ 2 * (N : ℝ) := by nlinarith
  have hylo : -(2 * (N : ℝ)) ≤ y := by nlinarith
  have hyhi : y ≤ 2 * (N : ℝ) := by nlinarith
  change |(x : ℝ) / N| ≤ 2 ∧ |(y : ℝ) / N| ≤ 2
  constructor <;> rw [abs_div, abs_of_pos hNR, div_le_iff₀ hNR]
  · rw [abs_le]
    constructor <;> nlinarith
  · rw [abs_le]
    constructor <;> nlinarith

/-- On the true shell-and-cone annulus the normalized axial magnitude lies
in `[3/4,2]`. -/
theorem normalized_axial_abs_mem
    {N : ℕ} {v : RealVec3} (hNlarge : 2 ≤ N)
    (hv : InRealSquarePancakeConeAnnulus N v) :
    (3 : ℝ) / 4 ≤ |(squareDyadicNormalizeReal N v).2.2| ∧
      |(squareDyadicNormalizeReal N v).2.2| ≤ 2 := by
  obtain ⟨x, y, z⟩ := v
  have hN : 0 < N := lt_of_lt_of_le (by norm_num) hNlarge
  have hNR : 0 < (N : ℝ) := by exact_mod_cast hN
  have hN2R : 0 < (N : ℝ) ^ 2 := by positivity
  have haxial := three_mul_normSq_le_four_mul_axial_sq hNlarge hv
  have hinner := hv.2.2.1
  have houter := hv.2.2.2.1
  have hlowerR : 9 * (N : ℝ) ^ 4 ≤ 16 * z ^ 2 := by
    simp only [normSq, dot] at haxial hinner
    nlinarith
  have hupperR : z ^ 2 ≤ 4 * (N : ℝ) ^ 4 := by
    simp only [normSq, dot] at houter
    nlinarith [sq_nonneg x, sq_nonneg y]
  have hlowerSq : (3 * (N : ℝ) ^ 2) ^ 2 ≤ (4 * z) ^ 2 := by
    nlinarith
  have hupperSq : z ^ 2 ≤ (2 * (N : ℝ) ^ 2) ^ 2 := by
    nlinarith
  have hlowerAbs := sq_le_sq.mp hlowerSq
  have hupperAbs := sq_le_sq.mp hupperSq
  have hN2nonneg : 0 ≤ (N : ℝ) ^ 2 := hN2R.le
  have hlower : 3 * (N : ℝ) ^ 2 ≤ 4 * |z| := by
    simpa [abs_mul, abs_of_nonneg hN2nonneg] using hlowerAbs
  have hupper : |z| ≤ 2 * (N : ℝ) ^ 2 := by
    simpa [abs_mul, abs_of_nonneg hN2nonneg] using hupperAbs
  change (3 : ℝ) / 4 ≤ |z / (N ^ 2)| ∧ |z / (N ^ 2)| ≤ 2
  rw [abs_div, abs_of_pos hN2R]
  constructor
  · exact (le_div_iff₀ hN2R).2 (by nlinarith)
  · exact (div_le_iff₀ hN2R).2 hupper

/-- The genuine radial-shell and cone conditions imply the normalized
annulus conditions used by the assembled four-chart multiplier. -/
theorem normalized_mem_of_mem_realSquarePancakeConeAnnulus
    {N : ℕ} {v : RealVec3} (hN : 2 ≤ N)
    (hv : InRealSquarePancakeConeAnnulus N v) :
    InNormalizedPancakeAnnulus (squareDyadicNormalizeReal N v) := by
  exact ⟨(normalized_transverse_abs_le_two hv).1,
    (normalized_transverse_abs_le_two hv).2,
    (normalized_axial_abs_mem hN hv).1,
    (normalized_axial_abs_mem hN hv).2⟩

/-- A periodic mode belongs to the physical square-dyadic pancake annulus
when its frame coordinates obey the genuine shell-and-cone predicate. -/
def InOrientedSquarePancakeConeAnnulus
    (F : OrientedFrameEquiv) (N : ℕ) (k : Wavevector) : Prop :=
  InRealSquarePancakeConeAnnulus N
    (orientedFrameWavevectorCoordinates F k)

theorem normalizedMode_mem_of_mem_orientedSquarePancakeConeAnnulus
    (F : OrientedFrameEquiv) {N : ℕ} (hN : 2 ≤ N) (k : Wavevector)
    (hk : InOrientedSquarePancakeConeAnnulus F N k) :
    InNormalizedPancakeAnnulus
      (orientedFrameSquareDyadicNormalizedMode F N k) := by
  rw [orientedFrameSquareDyadicNormalizedMode_eq]
  exact normalized_mem_of_mem_realSquarePancakeConeAnnulus hN hk

/-- Concrete finite set of modes in the physical rotated square-dyadic
pancake shell. -/
def squareDyadicPancakeSectorModes (F : OrientedFrameEquiv) (N : ℕ)
    (support : Finset Wavevector) : Finset Wavevector := by
  classical
  exact support.filter fun k ↦ InOrientedSquarePancakeConeAnnulus F N k

theorem mem_squareDyadicPancakeSectorModes_iff
    (F : OrientedFrameEquiv) (N : ℕ) (support : Finset Wavevector)
    (k : Wavevector) :
    k ∈ squareDyadicPancakeSectorModes F N support ↔
      k ∈ support ∧ InOrientedSquarePancakeConeAnnulus F N k := by
  simp [squareDyadicPancakeSectorModes]

/-- The physical square-dyadic pancake sector is a subset of the enclosing
annular selector used by the kernel theorem. -/
theorem squareDyadicPancakeSectorModes_subset_annularSectorModes
    (F : OrientedFrameEquiv) {N : ℕ} (hN : 2 ≤ N)
    (support : Finset Wavevector) :
    squareDyadicPancakeSectorModes F N support ⊆
      annularSectorModes F N support := by
  intro k hk
  rw [mem_annularSectorModes_iff]
  exact ⟨(mem_squareDyadicPancakeSectorModes_iff F N support k).mp hk |>.1,
    normalizedMode_mem_of_mem_orientedSquarePancakeConeAnnulus F hN k
      ((mem_squareDyadicPancakeSectorModes_iff F N support k).mp hk |>.2)⟩

/-- Concrete sharp finite-Fourier projection to the genuine rotated
square-dyadic pancake shell. -/
def squareDyadicPancakeSectorProjection
    (F : OrientedFrameEquiv) (N : ℕ)
    (support : Finset Wavevector) (omega : FourierVelocity) :
    BilinearSpatialTorus → ComplexVec3 :=
  finiteFourierReconstruction
    (squareDyadicPancakeSectorModes F N support) omega

/-- The exact physical coherent formula on the genuine finite shell-and-cone
projections, with every annular support premise proved from their definition. -/
theorem physicalAnnularAction_on_squareDyadicPancakeSectorProjections_eq_coherent
    (F : OrientedFrameEquiv) {N : ℕ} (hN : 2 ≤ N)
    (s t : Finset Wavevector) (omega eta : FourierVelocity)
    (x : BilinearSpatialTorus) :
    physicalOrientedFrameAnnularSquareDyadicKernelAction F N
        (squareDyadicPancakeSectorProjection F N s omega)
        (squareDyadicPancakeSectorProjection F N t eta) x =
      orientedFrameInverseComplexLinearMap F
        (∑ k ∈ squareDyadicPancakeSectorModes F N s,
          ∑ l ∈ squareDyadicPancakeSectorModes F N t,
          (UnitAddTorus.mFourier k x * UnitAddTorus.mFourier l x) •
            (((((1 : ℝ) / N) : ℂ)) •
              coherentProjectedNormalizedStretch ((1 : ℝ) / N)
                (frozenFrameSquareDyadicFrequencyPairChart
                  (orientedFrameFrequencyPairLinearIsometryEquiv F) N k l)
                (orientedFrameComplexLinearMap F (omega k))
                (orientedFrameComplexLinearMap F (eta l)))) := by
  apply physicalOrientedFrameAnnularSquareDyadicKernelAction_eq_coherent
    F hN
  intro k hk l hl
  rw [frozenFrameSquareDyadicFrequencyPairChart_orientedFrame F
    (lt_of_lt_of_le (by norm_num) hN)]
  exact ⟨
    normalizedMode_mem_of_mem_orientedSquarePancakeConeAnnulus F hN k
      ((mem_squareDyadicPancakeSectorModes_iff F N s k).mp hk |>.2),
    normalizedMode_mem_of_mem_orientedSquarePancakeConeAnnulus F hN l
      ((mem_squareDyadicPancakeSectorModes_iff F N t l).mp hl |>.2)⟩

end PancakeSquareDyadicSectorProjector
end NavierStokes
end FluidDynamics
end Mettapedia
