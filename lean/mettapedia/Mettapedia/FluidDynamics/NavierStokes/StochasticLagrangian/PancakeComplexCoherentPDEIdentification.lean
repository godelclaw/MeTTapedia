import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeComplexMisalignmentExpansion

/-!
# Identification of the annular symbol with complex PDE stretching

The annular multiplier is written using a polynomial normalized stretching
symbol and complex coherent-line coefficients.  This module defines the
complexified Biot--Savart stretching operator at arbitrary real frequencies
and proves that the aperture factor times the normalized annular symbol is
exactly that PDE operator applied to the two coherent projections.

This is the extensional bridge between the kernel-controlled term and the
coherent--coherent term in the exact four-term misalignment expansion.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes
namespace PancakeComplexCoherentPDEIdentification

open scoped BigOperators
open PeriodicFourierTriad
open PancakeBilinearPeriodization
open PancakePeriodicCoherentSplit
open PancakeRealCoherentPairEstimate
open PancakeCoherentStretchFactorization
open PancakeFrameCovariance
open PancakeSmoothCoherentSymbol
open PancakeSmoothCoherentStretchSymbol
open PancakeFiniteFourierBilinearTransfer
open PancakeAnnularChartCutoff
open PancakeAnnularMultiplierAssembly
open PancakeFrozenFrameKernelTransfer
open PancakePhysicalFrameKernelTransfer
open PancakeAnnularPhysicalFrameTransfer
open PancakeAnnularSectorProjector
open PancakeSquareDyadicSectorProjector

/-- Complexification of a real frequency. -/
def complexFrequency (k : RealVec3) : ComplexVec3 :=
  realVec3ToComplexVec3 k

/-- Complex-bilinear coordinate dot product. -/
def complexBilinearDot (u v : ComplexVec3) : ℂ :=
  ∑ i : Fin 3, u i * v i

/-- Complex-bilinear coordinate cross product. -/
def complexBilinearCross (u v : ComplexVec3) : ComplexVec3 :=
  ![u 1 * v 2 - u 2 * v 1,
    u 2 * v 0 - u 0 * v 2,
    u 0 * v 1 - u 1 * v 0]

/-- Complexified Biot--Savart amplitude at an arbitrary real frequency. -/
def realFrequencyComplexBiotSavart
    (k : RealVec3) (w : ComplexVec3) : ComplexVec3 :=
  (1 / (normSq k : ℂ)) • complexBilinearCross (complexFrequency k) w

/-- Complexified symmetric vorticity-stretching amplitude at an arbitrary
real source frequency. -/
def realFrequencyComplexStretch
    (source : RealVec3) (u v : ComplexVec3) : ComplexVec3 :=
  let velocity := realFrequencyComplexBiotSavart source u
  (1 / 2 : ℂ) •
    (complexBilinearDot velocity v • complexFrequency source +
      complexBilinearDot (complexFrequency source) v • velocity)

/-- Complex coherent-line projection in the real frequency chart. -/
def complexCoherentChartProject
    (k : RealVec3) (u : ComplexVec3) : ComplexVec3 :=
  complexCoherentChartCoeff k u • realVec3ToComplexVec3 (coherentW k)

theorem realVec3ToComplexVec3_smul (c : ℝ) (w : RealVec3) :
    realVec3ToComplexVec3 (smul c w) =
      (c : ℂ) • realVec3ToComplexVec3 w := by
  obtain ⟨x, y, z⟩ := w
  ext i
  fin_cases i <;> simp [realVec3ToComplexVec3, smul]

theorem complexBilinearCross_smul_right
    (u v : ComplexVec3) (c : ℂ) :
    complexBilinearCross u (c • v) =
      c • complexBilinearCross u v := by
  ext i
  fin_cases i <;> simp [complexBilinearCross] <;> ring

theorem complexBilinearDot_smul_left
    (u v : ComplexVec3) (c : ℂ) :
    complexBilinearDot (c • u) v = c * complexBilinearDot u v := by
  unfold complexBilinearDot
  simp_rw [Pi.smul_apply]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _hi
  ring

theorem complexBilinearDot_smul_right
    (u v : ComplexVec3) (c : ℂ) :
    complexBilinearDot u (c • v) = c * complexBilinearDot u v := by
  unfold complexBilinearDot
  simp_rw [Pi.smul_apply]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _hi
  ring

theorem realFrequencyComplexBiotSavart_smul
    (k : RealVec3) (u : ComplexVec3) (c : ℂ) :
    realFrequencyComplexBiotSavart k (c • u) =
      c • realFrequencyComplexBiotSavart k u := by
  unfold realFrequencyComplexBiotSavart
  rw [complexBilinearCross_smul_right]
  ext i
  simp [Pi.smul_apply]
  ring

/-- Complex stretching is bilinear in both amplitudes. -/
theorem realFrequencyComplexStretch_smul_smul
    (k : RealVec3) (u v : ComplexVec3) (a b : ℂ) :
    realFrequencyComplexStretch k (a • u) (b • v) =
      (a * b) • realFrequencyComplexStretch k u v := by
  unfold realFrequencyComplexStretch
  rw [realFrequencyComplexBiotSavart_smul]
  dsimp only
  rw [complexBilinearDot_smul_left,
    complexBilinearDot_smul_right,
    complexBilinearDot_smul_right]
  ext i
  simp [Pi.smul_apply, Pi.add_apply]
  ring

/-- Complexification commutes exactly with the real Biot--Savart stretching
formula. -/
theorem realFrequencyComplexStretch_realVec3ToComplexVec3
    (k u v : RealVec3) :
    realFrequencyComplexStretch k
        (realVec3ToComplexVec3 u) (realVec3ToComplexVec3 v) =
      realVec3ToComplexVec3 (stretchAmp k u v) := by
  obtain ⟨kx, ky, kz⟩ := k
  obtain ⟨ux, uy, uz⟩ := u
  obtain ⟨vx, vy, vz⟩ := v
  ext i
  fin_cases i <;>
    simp [realFrequencyComplexStretch, realFrequencyComplexBiotSavart,
      complexBilinearCross, complexBilinearDot, complexFrequency,
      realVec3ToComplexVec3, stretchAmp, biotSavartAmp, cross, dot,
      normSq, smul, add, Fin.sum_univ_three]

/-- **Complex PDE factorization.**  The exact aperture factor multiplying the
normalized coherent symbol is the full complexified Biot--Savart stretching
of the two coherent projections. -/
theorem realFrequencyComplexStretch_coherentProjects_eq_aperture_smul
    (delta : ℝ) (p : FrequencyPair) (u v : ComplexVec3)
    (hsourceAxial : p.1.2.2 ≠ 0) :
    realFrequencyComplexStretch (sourceFrequency delta p)
        (complexCoherentChartProject (sourceFrequency delta p) u)
        (complexCoherentChartProject (receiverFrequency delta p) v) =
      (delta : ℂ) • coherentProjectedNormalizedStretch delta p u v := by
  let a : ℂ := complexCoherentChartCoeff (sourceFrequency delta p) u
  let b : ℂ := complexCoherentChartCoeff (receiverFrequency delta p) v
  rw [show complexCoherentChartProject (sourceFrequency delta p) u =
      a • realVec3ToComplexVec3 (coherentW (sourceFrequency delta p)) from rfl,
    show complexCoherentChartProject (receiverFrequency delta p) v =
      b • realVec3ToComplexVec3 (coherentW (receiverFrequency delta p)) from rfl,
    realFrequencyComplexStretch_smul_smul,
    realFrequencyComplexStretch_realVec3ToComplexVec3]
  have hreal := stretchAmp_coherent_scaled_eq_delta_smul delta
    p.1.1 p.1.2.1 p.1.2.2 p.2.1 p.2.2.1 p.2.2.2 hsourceAxial
  rw [sourceFrequency, receiverFrequency, hreal,
    realVec3ToComplexVec3_smul]
  unfold coherentProjectedNormalizedStretch normalizedStretch a b
  ext i
  simp [Pi.smul_apply]
  ring

/-- Membership in the normalized annulus makes the axial nonvanishing
premise of the complex PDE factorization automatic. -/
theorem aperture_smul_coherentProjectedNormalizedStretch_eq_complexStretch
    (delta : ℝ) (p : FrequencyPair) (u v : ComplexVec3)
    (hsource : InNormalizedPancakeAnnulus p.1) :
    (delta : ℂ) • coherentProjectedNormalizedStretch delta p u v =
      realFrequencyComplexStretch (sourceFrequency delta p)
        (complexCoherentChartProject (sourceFrequency delta p) u)
        (complexCoherentChartProject (receiverFrequency delta p) v) := by
  symm
  apply realFrequencyComplexStretch_coherentProjects_eq_aperture_smul
  intro hz
  have hpositive := hsource.2.2.1
  rw [hz, abs_zero] at hpositive
  norm_num at hpositive

/-- **Exact physical PDE formula on the genuine square-dyadic sector.**
The kernel-controlled summand is written directly as complexified
Biot--Savart stretching of the two coherent chart projections. -/
theorem physicalAnnularAction_on_squareDyadicSector_eq_complexPDE
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
            realFrequencyComplexStretch
              (sourceFrequency ((1 : ℝ) / N)
                (frozenFrameSquareDyadicFrequencyPairChart
                  (orientedFrameFrequencyPairLinearIsometryEquiv F) N k l))
              (complexCoherentChartProject
                (sourceFrequency ((1 : ℝ) / N)
                  (frozenFrameSquareDyadicFrequencyPairChart
                    (orientedFrameFrequencyPairLinearIsometryEquiv F) N k l))
                (orientedFrameComplexLinearMap F (omega k)))
              (complexCoherentChartProject
                (receiverFrequency ((1 : ℝ) / N)
                  (frozenFrameSquareDyadicFrequencyPairChart
                    (orientedFrameFrequencyPairLinearIsometryEquiv F) N k l))
                (orientedFrameComplexLinearMap F (eta l)))) := by
  rw [physicalAnnularAction_on_squareDyadicPancakeSectorProjections_eq_coherent
    F hN]
  apply congrArg (orientedFrameInverseComplexLinearMap F)
  apply Finset.sum_congr rfl
  intro k hk
  apply Finset.sum_congr rfl
  intro l hl
  have hp : frozenFrameSquareDyadicFrequencyPairChart
      (orientedFrameFrequencyPairLinearIsometryEquiv F) N k l =
      (orientedFrameSquareDyadicNormalizedMode F N k,
        orientedFrameSquareDyadicNormalizedMode F N l) :=
    frozenFrameSquareDyadicFrequencyPairChart_orientedFrame F
      (lt_of_lt_of_le (by norm_num) hN) k l
  have hsource : InNormalizedPancakeAnnulus
      (frozenFrameSquareDyadicFrequencyPairChart
        (orientedFrameFrequencyPairLinearIsometryEquiv F) N k l).1 := by
    rw [hp]
    exact normalizedMode_mem_of_mem_orientedSquarePancakeConeAnnulus F hN k
      ((mem_squareDyadicPancakeSectorModes_iff F N s k).mp hk |>.2)
  have hid := aperture_smul_coherentProjectedNormalizedStretch_eq_complexStretch
    ((1 : ℝ) / N)
    (frozenFrameSquareDyadicFrequencyPairChart
      (orientedFrameFrequencyPairLinearIsometryEquiv F) N k l)
    (orientedFrameComplexLinearMap F (omega k))
    (orientedFrameComplexLinearMap F (eta l)) hsource
  exact_mod_cast congrArg
    (fun z : ComplexVec3 ↦
      (UnitAddTorus.mFourier k x * UnitAddTorus.mFourier l x) • z) hid

end PancakeComplexCoherentPDEIdentification
end NavierStokes
end FluidDynamics
end Mettapedia
