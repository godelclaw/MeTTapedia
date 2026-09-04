import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeComplexCoherentPDEIdentification
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.MisalignmentRefinedPin

/-!
# Exact physical coherent/misaligned splitting on a pancake sector

This module joins the exact complex interaction expansion to the annular
kernel theorem.  At a frozen oriented frame and square-dyadic scale, the full
finite Fourier Biot--Savart stretching sum over the genuine pancake sector is
exactly the physical annular coherent-kernel action plus the physical image
of the three terms containing at least one misalignment factor.

The norm split is therefore concrete, and the coherent share inherits the
cardinality-free `C/N` kernel bound.  No abstract scalar `split_le` or
`coherent_le` premise is used in these finite-field statements.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes
namespace PancakePhysicalMisalignmentSplit

open scoped BigOperators
open scoped RealInnerProductSpace
open PeriodicFourierTriad
open PancakeBilinearPeriodization
open PancakePeriodicCoherentSplit
open PancakeRealCoherentPairEstimate
open PancakeSmoothCoherentSymbol
open PancakeSmoothCoherentStretchSymbol
open PancakeFrameCovariance
open PancakeFrozenFrameKernelTransfer
open PancakePhysicalFrameKernelTransfer
open PancakeAnnularPhysicalFrameTransfer
open PancakeAnnularSectorProjector
open PancakeSquareDyadicSectorProjector
open PancakeStrainAxialFrame
open PancakeComplexCoherentPDEIdentification

local notation "R3" => EuclideanSpace ℝ (Fin 3)

/-- Misalignment remainder of the complex coherent-line projection at an
arbitrary real frequency. -/
def complexMisalignmentChartComponent
    (k : RealVec3) (u : ComplexVec3) : ComplexVec3 :=
  u - complexCoherentChartProject k u

theorem complexCoherentChartProject_add_misalignment
    (k : RealVec3) (u : ComplexVec3) :
    complexCoherentChartProject k u +
      complexMisalignmentChartComponent k u = u := by
  simp [complexMisalignmentChartComponent]

theorem complexBilinearCross_add_right
    (u v w : ComplexVec3) :
    complexBilinearCross u (v + w) =
      complexBilinearCross u v + complexBilinearCross u w := by
  ext i
  fin_cases i <;> simp [complexBilinearCross, Pi.add_apply] <;> ring

theorem realFrequencyComplexBiotSavart_add
    (k : RealVec3) (u v : ComplexVec3) :
    realFrequencyComplexBiotSavart k (u + v) =
      realFrequencyComplexBiotSavart k u +
        realFrequencyComplexBiotSavart k v := by
  unfold realFrequencyComplexBiotSavart
  rw [complexBilinearCross_add_right]
  ext i
  simp [Pi.add_apply, Pi.smul_apply]
  ring

theorem realFrequencyComplexStretch_add_source
    (k : RealVec3) (u₁ u₂ v : ComplexVec3) :
    realFrequencyComplexStretch k (u₁ + u₂) v =
      realFrequencyComplexStretch k u₁ v +
        realFrequencyComplexStretch k u₂ v := by
  ext i
  fin_cases i <;>
    simp [realFrequencyComplexStretch, realFrequencyComplexBiotSavart_add,
      complexBilinearDot, Pi.add_apply, Fin.sum_univ_three] <;> ring

theorem realFrequencyComplexStretch_add_receiver
    (k : RealVec3) (u v₁ v₂ : ComplexVec3) :
    realFrequencyComplexStretch k u (v₁ + v₂) =
      realFrequencyComplexStretch k u v₁ +
        realFrequencyComplexStretch k u v₂ := by
  ext i
  fin_cases i <;>
    simp [realFrequencyComplexStretch, complexBilinearDot,
      Pi.add_apply, Fin.sum_univ_three] <;> ring

/-- The three real-frequency complex stretching terms which carry at least
one misalignment component. -/
def realFrequencyMisalignmentStretch
    (source receiver : RealVec3) (u v : ComplexVec3) : ComplexVec3 :=
  realFrequencyComplexStretch source
      (complexCoherentChartProject source u)
      (complexMisalignmentChartComponent receiver v) +
    realFrequencyComplexStretch source
      (complexMisalignmentChartComponent source u)
      (complexCoherentChartProject receiver v) +
    realFrequencyComplexStretch source
      (complexMisalignmentChartComponent source u)
      (complexMisalignmentChartComponent receiver v)

/-- Exact real-frequency coherent/misaligned expansion. -/
theorem realFrequencyComplexStretch_eq_coherent_add_misalignment
    (source receiver : RealVec3) (u v : ComplexVec3) :
    realFrequencyComplexStretch source u v =
      realFrequencyComplexStretch source
          (complexCoherentChartProject source u)
          (complexCoherentChartProject receiver v) +
        realFrequencyMisalignmentStretch source receiver u v := by
  calc
    realFrequencyComplexStretch source u v =
        realFrequencyComplexStretch source
          (complexCoherentChartProject source u +
            complexMisalignmentChartComponent source u)
          (complexCoherentChartProject receiver v +
            complexMisalignmentChartComponent receiver v) := by
      rw [complexCoherentChartProject_add_misalignment,
        complexCoherentChartProject_add_misalignment]
    _ = _ := by
      rw [realFrequencyComplexStretch_add_source,
        realFrequencyComplexStretch_add_receiver,
        realFrequencyComplexStretch_add_receiver]
      unfold realFrequencyMisalignmentStretch
      abel

/-- Full normalized complex stretching sum in one frozen frame, restricted
to the genuine square-dyadic pancake sector. -/
def finiteFramePancakeStretchingSum
    (F : OrientedFrameEquiv) (N : ℕ)
    (s t : Finset Wavevector) (omega eta : FourierVelocity)
    (x : BilinearSpatialTorus) : ComplexVec3 :=
  ∑ k ∈ squareDyadicPancakeSectorModes F N s,
    ∑ l ∈ squareDyadicPancakeSectorModes F N t,
    let p := frozenFrameSquareDyadicFrequencyPairChart
      (orientedFrameFrequencyPairLinearIsometryEquiv F) N k l
    (UnitAddTorus.mFourier k x * UnitAddTorus.mFourier l x) •
      realFrequencyComplexStretch
        (sourceFrequency ((1 : ℝ) / N) p)
        (orientedFrameComplexLinearMap F (omega k))
        (orientedFrameComplexLinearMap F (eta l))

/-- Coherent--coherent part of the same frozen-frame sector sum. -/
def finiteFrameCoherentPancakeStretchingSum
    (F : OrientedFrameEquiv) (N : ℕ)
    (s t : Finset Wavevector) (omega eta : FourierVelocity)
    (x : BilinearSpatialTorus) : ComplexVec3 :=
  ∑ k ∈ squareDyadicPancakeSectorModes F N s,
    ∑ l ∈ squareDyadicPancakeSectorModes F N t,
    let p := frozenFrameSquareDyadicFrequencyPairChart
      (orientedFrameFrequencyPairLinearIsometryEquiv F) N k l
    let source := sourceFrequency ((1 : ℝ) / N) p
    let receiver := receiverFrequency ((1 : ℝ) / N) p
    (UnitAddTorus.mFourier k x * UnitAddTorus.mFourier l x) •
      realFrequencyComplexStretch source
        (complexCoherentChartProject source
          (orientedFrameComplexLinearMap F (omega k)))
        (complexCoherentChartProject receiver
          (orientedFrameComplexLinearMap F (eta l)))

/-- Three-term misalignment remainder of the frozen-frame sector sum. -/
def finiteFrameMisalignmentPancakeStretchingSum
    (F : OrientedFrameEquiv) (N : ℕ)
    (s t : Finset Wavevector) (omega eta : FourierVelocity)
    (x : BilinearSpatialTorus) : ComplexVec3 :=
  ∑ k ∈ squareDyadicPancakeSectorModes F N s,
    ∑ l ∈ squareDyadicPancakeSectorModes F N t,
    let p := frozenFrameSquareDyadicFrequencyPairChart
      (orientedFrameFrequencyPairLinearIsometryEquiv F) N k l
    (UnitAddTorus.mFourier k x * UnitAddTorus.mFourier l x) •
      realFrequencyMisalignmentStretch
        (sourceFrequency ((1 : ℝ) / N) p)
        (receiverFrequency ((1 : ℝ) / N) p)
        (orientedFrameComplexLinearMap F (omega k))
        (orientedFrameComplexLinearMap F (eta l))

theorem finiteFramePancakeStretchingSum_eq_coherent_add_misalignment
    (F : OrientedFrameEquiv) (N : ℕ)
    (s t : Finset Wavevector) (omega eta : FourierVelocity)
    (x : BilinearSpatialTorus) :
    finiteFramePancakeStretchingSum F N s t omega eta x =
      finiteFrameCoherentPancakeStretchingSum F N s t omega eta x +
        finiteFrameMisalignmentPancakeStretchingSum
          F N s t omega eta x := by
  unfold finiteFramePancakeStretchingSum
    finiteFrameCoherentPancakeStretchingSum
    finiteFrameMisalignmentPancakeStretchingSum
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _hk
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro l _hl
  dsimp only
  rw [realFrequencyComplexStretch_eq_coherent_add_misalignment,
    smul_add]

/-- Physical image of the full finite sector stretching sum. -/
def physicalFiniteFramePancakeStretchingSum
    (F : OrientedFrameEquiv) (N : ℕ)
    (s t : Finset Wavevector) (omega eta : FourierVelocity)
    (x : BilinearSpatialTorus) : ComplexVec3 :=
  orientedFrameInverseComplexLinearMap F
    (finiteFramePancakeStretchingSum F N s t omega eta x)

/-- Physical image of the three-term misalignment remainder. -/
def physicalFiniteFrameMisalignmentPancakeStretchingSum
    (F : OrientedFrameEquiv) (N : ℕ)
    (s t : Finset Wavevector) (omega eta : FourierVelocity)
    (x : BilinearSpatialTorus) : ComplexVec3 :=
  orientedFrameInverseComplexLinearMap F
    (finiteFrameMisalignmentPancakeStretchingSum F N s t omega eta x)

theorem physicalAnnularKernelAction_eq_finiteFrameCoherentSum
    (F : OrientedFrameEquiv) {N : ℕ} (hN : 2 ≤ N)
    (s t : Finset Wavevector) (omega eta : FourierVelocity)
    (x : BilinearSpatialTorus) :
    physicalOrientedFrameAnnularSquareDyadicKernelAction F N
        (squareDyadicPancakeSectorProjection F N s omega)
        (squareDyadicPancakeSectorProjection F N t eta) x =
      orientedFrameInverseComplexLinearMap F
        (finiteFrameCoherentPancakeStretchingSum
          F N s t omega eta x) := by
  simpa [finiteFrameCoherentPancakeStretchingSum] using
    physicalAnnularAction_on_squareDyadicSector_eq_complexPDE
      F hN s t omega eta x

/-- **Exact physical split.**  Full sector stretching equals the annular
coherent kernel action plus precisely the three-term misalignment remainder. -/
theorem physicalFiniteFramePancakeStretchingSum_eq_kernel_add_misalignment
    (F : OrientedFrameEquiv) {N : ℕ} (hN : 2 ≤ N)
    (s t : Finset Wavevector) (omega eta : FourierVelocity)
    (x : BilinearSpatialTorus) :
    physicalFiniteFramePancakeStretchingSum F N s t omega eta x =
      physicalOrientedFrameAnnularSquareDyadicKernelAction F N
          (squareDyadicPancakeSectorProjection F N s omega)
          (squareDyadicPancakeSectorProjection F N t eta) x +
        physicalFiniteFrameMisalignmentPancakeStretchingSum
          F N s t omega eta x := by
  unfold physicalFiniteFramePancakeStretchingSum
    physicalFiniteFrameMisalignmentPancakeStretchingSum
  rw [finiteFramePancakeStretchingSum_eq_coherent_add_misalignment,
    map_add, ← physicalAnnularKernelAction_eq_finiteFrameCoherentSum F hN]

/-- Concrete physical norm form of `split_le`. -/
theorem norm_physicalFiniteFramePancakeStretchingSum_le
    (F : OrientedFrameEquiv) {N : ℕ} (hN : 2 ≤ N)
    (s t : Finset Wavevector) (omega eta : FourierVelocity)
    (x : BilinearSpatialTorus) :
    ‖physicalFiniteFramePancakeStretchingSum F N s t omega eta x‖ ≤
      ‖physicalOrientedFrameAnnularSquareDyadicKernelAction F N
          (squareDyadicPancakeSectorProjection F N s omega)
          (squareDyadicPancakeSectorProjection F N t eta) x‖ +
        ‖physicalFiniteFrameMisalignmentPancakeStretchingSum
          F N s t omega eta x‖ := by
  rw [physicalFiniteFramePancakeStretchingSum_eq_kernel_add_misalignment
    F hN]
  exact norm_add_le _ _

/-- **Frequency-uniform finite-field transfer.**  The concrete coherent share
has its cardinality-free `C/N` bound, leaving only the exact three-term
misalignment remainder. -/
theorem exists_uniform_physicalPancakeSplit_bilinear_bound :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (F : OrientedFrameEquiv) (N : ℕ), 2 ≤ N →
      ∀ (s t : Finset Wavevector) (omega eta : FourierVelocity)
        (x : BilinearSpatialTorus) (M P : ℝ),
        (∀ y, ‖squareDyadicPancakeSectorProjection F N s omega y‖ ≤ M) →
        (∀ y, ‖squareDyadicPancakeSectorProjection F N t eta y‖ ≤ P) →
        ‖physicalFiniteFramePancakeStretchingSum
            F N s t omega eta x‖ ≤
          243 * (C / N) * M * P +
            ‖physicalFiniteFrameMisalignmentPancakeStretchingSum
              F N s t omega eta x‖ := by
  rcases exists_uniform_physicalOrientedFrameAnnularSquareDyadic_bilinear_bound
    with ⟨C, hC, hkernel⟩
  refine ⟨C, hC, ?_⟩
  intro F N hN s t omega eta x M P homega heta
  have hcoherent := hkernel F N hN
    (squareDyadicPancakeSectorProjection F N s omega)
    (squareDyadicPancakeSectorProjection F N t eta)
    x M P
    (continuous_finiteFourierReconstruction _ _)
    (continuous_finiteFourierReconstruction _ _)
    homega heta
  exact (norm_physicalFiniteFramePancakeStretchingSum_le
    F hN s t omega eta x).trans (add_le_add hcoherent (le_refl _))

/-! ## The split in the frame constructed from the strain -/

/-- The exact physical split at the pointwise frame whose axis is the most
compressive eigenvector of the supplied symmetric strain field.  In
particular, no frame or axial direction is supplied independently of the
strain. -/
theorem strainFrame_physicalFinitePancakeStretchingSum_eq_kernel_add_misalignment
    (S : BilinearSpatialTorus → R3 →L[ℝ] R3)
    (hSsymm : ∀ x u v, inner ℝ u (S x v) = inner ℝ (S x u) v)
    {N : ℕ} (hN : 2 ≤ N)
    (s t : Finset Wavevector) (omega eta : FourierVelocity)
    (x : BilinearSpatialTorus) :
    physicalFiniteFramePancakeStretchingSum
        (compressiveAxialFrameField S hSsymm x) N s t omega eta x =
      physicalOrientedFrameAnnularSquareDyadicKernelAction
          (compressiveAxialFrameField S hSsymm x) N
          (squareDyadicPancakeSectorProjection
            (compressiveAxialFrameField S hSsymm x) N s omega)
          (squareDyadicPancakeSectorProjection
            (compressiveAxialFrameField S hSsymm x) N t eta) x +
        physicalFiniteFrameMisalignmentPancakeStretchingSum
          (compressiveAxialFrameField S hSsymm x) N s t omega eta x :=
  physicalFiniteFramePancakeStretchingSum_eq_kernel_add_misalignment
    (compressiveAxialFrameField S hSsymm x) hN s t omega eta x

/-- Cardinality-free `C/N` control of the coherent part in the pointwise
compressive strain frame, with the exact misalignment remainder exposed. -/
theorem exists_uniform_strainFramePhysicalPancakeSplit_bilinear_bound :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (S : BilinearSpatialTorus → R3 →L[ℝ] R3)
        (hSsymm : ∀ x u v, inner ℝ u (S x v) = inner ℝ (S x u) v)
        (N : ℕ), 2 ≤ N →
      ∀ (s t : Finset Wavevector) (omega eta : FourierVelocity)
        (x : BilinearSpatialTorus) (M P : ℝ),
        (∀ y, ‖squareDyadicPancakeSectorProjection
          (compressiveAxialFrameField S hSsymm x) N s omega y‖ ≤ M) →
        (∀ y, ‖squareDyadicPancakeSectorProjection
          (compressiveAxialFrameField S hSsymm x) N t eta y‖ ≤ P) →
        ‖physicalFiniteFramePancakeStretchingSum
            (compressiveAxialFrameField S hSsymm x)
            N s t omega eta x‖ ≤
          243 * (C / N) * M * P +
            ‖physicalFiniteFrameMisalignmentPancakeStretchingSum
              (compressiveAxialFrameField S hSsymm x)
              N s t omega eta x‖ := by
  rcases exists_uniform_physicalPancakeSplit_bilinear_bound with
    ⟨C, hC, hbound⟩
  refine ⟨C, hC, ?_⟩
  intro S hSsymm N hN s t omega eta x M P homega heta
  exact hbound (compressiveAxialFrameField S hSsymm x) N hN
    s t omega eta x M P homega heta

end PancakePhysicalMisalignmentSplit
end NavierStokes
end FluidDynamics
end Mettapedia
