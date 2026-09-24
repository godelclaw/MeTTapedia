import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakePeriodicVorticityEquation

/-!
# Reality of the hard square-dyadic pancake block

The square-dyadic pancake selector depends only on squared radial and frame
coordinates.  It is therefore closed under `k ↦ -k`.  A real periodic
vorticity field has conjugate-symmetric Fourier coefficients, so the selected
finite reconstruction is itself real-valued.

This file proves both statements.  Consequently the coordinatewise-real-part
block used by the direction law agrees with the full complex reconstruction
embedded from real Euclidean space; taking real part loses no information for
physical Fourier data.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes
namespace PancakeBlockReality

open scoped BigOperators ComplexConjugate
open PeriodicFourierTriad
open PancakeConeDirectionDichotomy
open PancakeRealCoherentPairEstimate
open PancakeBilinearPeriodization
open PancakeFrameCovariance
open PancakePhysicalFrameKernelTransfer
open PancakeAnnularSectorProjector
open PancakeSquareDyadicSectorProjector
open PancakeArbitraryDataBlocks
open PancakePeriodicCoherentSplit
open PancakeTransverseEnergyFreezing
open PancakeDyadicDirectionEvolution
open PancakePeriodicComplexStretch
open PancakePeriodicVorticityEquation

/-! ## Negation symmetry of the selector -/

theorem euclideanWavevectorOfWavevector_neg (k : Wavevector) :
    euclideanWavevectorOfWavevector (-k) =
      -euclideanWavevectorOfWavevector k := by
  apply WithLp.ofLp_injective 2
  funext i
  fin_cases i <;>
    simp [euclideanWavevectorOfWavevector]

theorem orientedFrameWavevectorCoordinates_neg
    (F : OrientedFrameEquiv) (k : Wavevector) :
    orientedFrameWavevectorCoordinates F (-k) =
      -orientedFrameWavevectorCoordinates F k := by
  unfold orientedFrameWavevectorCoordinates
  rw [euclideanWavevectorOfWavevector_neg, map_neg]
  rfl

theorem inRealSquarePancakeConeAnnulus_neg_iff
    (N : ℕ) (v : RealVec3) :
    InRealSquarePancakeConeAnnulus N (-v) ↔
      InRealSquarePancakeConeAnnulus N v := by
  obtain ⟨x, y, z⟩ := v
  simp [InRealSquarePancakeConeAnnulus,
    PancakeRealCoherentPairEstimate.normSq,
    PancakeRealCoherentPairEstimate.dot]

theorem inOrientedSquarePancakeConeAnnulus_neg_iff
    (F : OrientedFrameEquiv) (N : ℕ) (k : Wavevector) :
    InOrientedSquarePancakeConeAnnulus F N (-k) ↔
      InOrientedSquarePancakeConeAnnulus F N k := by
  unfold InOrientedSquarePancakeConeAnnulus
  rw [orientedFrameWavevectorCoordinates_neg,
    inRealSquarePancakeConeAnnulus_neg_iff]

theorem modeSquareNat_neg (k : Wavevector) :
    modeSquareNat (-k) = modeSquareNat k := by
  unfold modeSquareNat
  apply Finset.sum_congr rfl
  intro i hi
  simp

/-! ## Conjugate symmetry of the unit-torus coefficient symbols -/

/-- Coordinatewise conjugation of a Fourier vector coefficient. -/
def coefficientConjugate (w : VelocityCoefficient) : VelocityCoefficient :=
  fun i ↦ conj (w i)

@[simp]
theorem coefficientConjugate_apply (w : VelocityCoefficient) (i : Fin 3) :
    coefficientConjugate w i = conj (w i) := by
  rfl

@[simp]
theorem coefficientConjugate_add (u v : VelocityCoefficient) :
    coefficientConjugate (u + v) =
      coefficientConjugate u + coefficientConjugate v := by
  ext i
  simp [coefficientConjugate]

@[simp]
theorem coefficientConjugate_neg (u : VelocityCoefficient) :
    coefficientConjugate (-u) = -coefficientConjugate u := by
  ext i
  simp [coefficientConjugate]

@[simp]
theorem coefficientConjugate_smul (a : ℂ) (u : VelocityCoefficient) :
    coefficientConjugate (a • u) =
      conj a • coefficientConjugate u := by
  ext i
  simp [coefficientConjugate, map_mul]

@[simp]
theorem coefficientConjugate_wavevectorCoefficient (k : Wavevector) :
    coefficientConjugate (wavevectorCoefficient k) =
      wavevectorCoefficient k := by
  ext i
  simp [coefficientConjugate, wavevectorCoefficient]

theorem wavevectorCoefficient_neg (k : Wavevector) :
    wavevectorCoefficient (-k) = -wavevectorCoefficient k := by
  ext i
  simp [wavevectorCoefficient]

theorem modeSquare_neg (k : Wavevector) :
    modeSquare (-k) = modeSquare k := by
  simp [modeSquare]

theorem coefficientDot_conjugate
    (u v : VelocityCoefficient) :
    coefficientDot (coefficientConjugate u) (coefficientConjugate v) =
      conj (coefficientDot u v) := by
  unfold coefficientDot
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  simp [coefficientConjugate, map_mul]

theorem modeDot_neg_conjugate (k : Wavevector) (v : VelocityCoefficient) :
    modeDot (-k) (coefficientConjugate v) =
      -conj (modeDot k v) := by
  unfold modeDot
  rw [map_sum]
  simp only [Pi.neg_apply, Int.cast_neg, coefficientConjugate_apply,
    neg_mul, Finset.sum_neg_distrib, neg_inj]
  apply Finset.sum_congr rfl
  intro i hi
  simp [map_mul]

theorem complexBiotSavartAmp_neg_conjugate
    (k : Wavevector) (w : VelocityCoefficient) :
    complexBiotSavartAmp (-k) (coefficientConjugate w) =
      -coefficientConjugate (complexBiotSavartAmp k w) := by
  ext i
  fin_cases i <;>
    simp [coefficientConjugate, complexBiotSavartAmp, coefficientCross,
      wavevectorCoefficient, modeSquare, Fin.sum_univ_three, map_mul,
      map_inv₀] <;>
    ring

theorem unitTorusBiotSavartAmp_neg_conjugate
    (k : Wavevector) (w : VelocityCoefficient) :
    unitTorusBiotSavartAmp (-k) (coefficientConjugate w) =
      coefficientConjugate (unitTorusBiotSavartAmp k w) := by
  unfold unitTorusBiotSavartAmp
  rw [complexBiotSavartAmp_neg_conjugate, smul_neg,
    coefficientConjugate_smul]
  have hphase :
      conj (-(unitTorusDerivativePhase)⁻¹) =
        unitTorusDerivativePhase⁻¹ := by
    simp [unitTorusDerivativePhase, map_inv₀]
    simp only [starRingEnd_apply, star_ofNat]
  rw [hphase]
  simp

theorem unitTorusStrainStretchAmp_neg_conjugate
    (source : Wavevector) (wSource wReceiver : VelocityCoefficient) :
    unitTorusStrainStretchAmp (-source)
        (coefficientConjugate wSource) (coefficientConjugate wReceiver) =
      coefficientConjugate
        (unitTorusStrainStretchAmp source wSource wReceiver) := by
  unfold unitTorusStrainStretchAmp
  dsimp only
  rw [unitTorusBiotSavartAmp_neg_conjugate,
    coefficientDot_conjugate, modeDot_neg_conjugate,
    wavevectorCoefficient_neg, coefficientConjugate_smul,
    coefficientConjugate_add, coefficientConjugate_smul,
    coefficientConjugate_wavevectorCoefficient,
    coefficientConjugate_smul]
  ext i
  simp only [Pi.smul_apply, Pi.add_apply, Pi.neg_apply,
    coefficientConjugate_apply]
  simp [unitTorusDerivativePhase, map_mul]
  simp only [starRingEnd_apply, star_ofNat]
  simp
  ring

theorem unitTorusNegativeTransportAmp_neg_conjugate
    (source receiver : Wavevector)
    (wSource wReceiver : VelocityCoefficient) :
    unitTorusNegativeTransportAmp (-source) (-receiver)
        (coefficientConjugate wSource) (coefficientConjugate wReceiver) =
      coefficientConjugate
        (unitTorusNegativeTransportAmp source receiver wSource wReceiver) := by
  unfold unitTorusNegativeTransportAmp
  rw [unitTorusBiotSavartAmp_neg_conjugate,
    modeDot_neg_conjugate, coefficientConjugate_smul]
  ext i
  simp only [Pi.smul_apply, coefficientConjugate_apply]
  simp [unitTorusDerivativePhase, map_mul]
  simp only [starRingEnd_apply, star_ofNat]
  simp

theorem unitTorusViscousVorticityCoeff_neg_conjugate
    (nu : ℝ) (omega : FourierVelocity)
    (hreal : ∀ k, omega (-k) = coefficientConjugate (omega k))
    (q : Wavevector) :
    unitTorusViscousVorticityCoeff nu omega (-q) =
      coefficientConjugate (unitTorusViscousVorticityCoeff nu omega q) := by
  unfold unitTorusViscousVorticityCoeff
  rw [hreal, modeSquare_neg,
    coefficientConjugate_smul]
  congr 1
  simp [unitTorusDerivativePhase, modeSquare, Fin.sum_univ_three, map_mul]
  simp only [starRingEnd_apply, star_ofNat]
  simp

/-! ## Conjugate symmetry of finite convolution fields -/

/-- Generic conjugate-symmetry theorem for a finite convolution whose two
supports are closed under negation and whose interaction symbol respects
simultaneous frequency negation. -/
theorem finitePairConvolution_neg_conjugate
    (sourceModes receiverModes : Finset Wavevector)
    (hsource : ∀ k, -k ∈ sourceModes ↔ k ∈ sourceModes)
    (hreceiver : ∀ k, -k ∈ receiverModes ↔ k ∈ receiverModes)
    (K : Wavevector → Wavevector → VelocityCoefficient)
    (hK : ∀ r s, K (-r) (-s) = coefficientConjugate (K r s))
    (q : Wavevector) :
    (∑ sr ∈ (sourceModes ×ˢ receiverModes).filter
        (fun sr ↦ sr.1 + sr.2 = -q), K sr.1 sr.2) =
      coefficientConjugate
        (∑ sr ∈ (sourceModes ×ˢ receiverModes).filter
          (fun sr ↦ sr.1 + sr.2 = q), K sr.1 sr.2) := by
  classical
  ext i
  simp only [Finset.sum_apply, coefficientConjugate_apply]
  change
    (∑ sr ∈ (sourceModes ×ˢ receiverModes).filter
        (fun sr ↦ sr.1 + sr.2 = -q), K sr.1 sr.2 i) =
      (starRingEnd ℂ)
        (∑ sr ∈ (sourceModes ×ˢ receiverModes).filter
          (fun sr ↦ sr.1 + sr.2 = q), K sr.1 sr.2 i)
  rw [map_sum]
  exact Finset.sum_bij
    (fun sr _hsr ↦ (-sr.1, -sr.2))
    (fun sr hsr ↦ by
      rcases Finset.mem_filter.mp hsr with ⟨hpair, hadd⟩
      rcases Finset.mem_product.mp hpair with ⟨hsrc, hrec⟩
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_product.mpr
        ⟨(hsource sr.1).mpr hsrc, (hreceiver sr.2).mpr hrec⟩, ?_⟩
      have hneg := congrArg Neg.neg hadd
      simpa [add_comm] using hneg)
    (fun a _ha b _hb hab ↦ by
      apply Prod.ext
      · simpa using congrArg Prod.fst hab
      · simpa using congrArg Prod.snd hab)
    (fun b hb ↦ by
      rcases Finset.mem_filter.mp hb with ⟨hpair, hadd⟩
      rcases Finset.mem_product.mp hpair with ⟨hsrc, hrec⟩
      refine ⟨(-b.1, -b.2), ?_, by simp⟩
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_product.mpr
        ⟨(hsource b.1).mpr hsrc, (hreceiver b.2).mpr hrec⟩, ?_⟩
      have hneg := congrArg Neg.neg hadd
      simpa [add_comm] using hneg)
    (fun sr _hsr ↦ by
      have hsymbol := congrFun (hK (-sr.1) (-sr.2)) i
      simpa only [neg_neg, coefficientConjugate_apply,
        starRingEnd_apply] using hsymbol)

theorem finiteUnitTorusStretchingCoeff_neg_conjugate
    (sourceModes receiverModes : Finset Wavevector)
    (hsource : ∀ k, -k ∈ sourceModes ↔ k ∈ sourceModes)
    (hreceiver : ∀ k, -k ∈ receiverModes ↔ k ∈ receiverModes)
    (omega eta : FourierVelocity)
    (homega : ∀ k, omega (-k) = coefficientConjugate (omega k))
    (heta : ∀ k, eta (-k) = coefficientConjugate (eta k))
    (q : Wavevector) :
    finiteUnitTorusStretchingCoeff
        sourceModes receiverModes omega eta (-q) =
      coefficientConjugate
        (finiteUnitTorusStretchingCoeff
          sourceModes receiverModes omega eta q) := by
  unfold finiteUnitTorusStretchingCoeff
  exact finitePairConvolution_neg_conjugate
    sourceModes receiverModes hsource hreceiver
    (fun r s ↦ unitTorusStrainStretchAmp r (omega r) (eta s))
    (fun r s ↦ by
      rw [homega, heta]
      exact unitTorusStrainStretchAmp_neg_conjugate
        r (omega r) (eta s)) q

theorem finiteUnitTorusNegativeTransportCoeff_neg_conjugate
    (sourceModes receiverModes : Finset Wavevector)
    (hsource : ∀ k, -k ∈ sourceModes ↔ k ∈ sourceModes)
    (hreceiver : ∀ k, -k ∈ receiverModes ↔ k ∈ receiverModes)
    (omega eta : FourierVelocity)
    (homega : ∀ k, omega (-k) = coefficientConjugate (omega k))
    (heta : ∀ k, eta (-k) = coefficientConjugate (eta k))
    (q : Wavevector) :
    finiteUnitTorusNegativeTransportCoeff
        sourceModes receiverModes omega eta (-q) =
      coefficientConjugate
        (finiteUnitTorusNegativeTransportCoeff
          sourceModes receiverModes omega eta q) := by
  unfold finiteUnitTorusNegativeTransportCoeff
  exact finitePairConvolution_neg_conjugate
    sourceModes receiverModes hsource hreceiver
    (fun r s ↦
      unitTorusNegativeTransportAmp r s (omega r) (eta s))
    (fun r s ↦ by
      rw [homega, heta]
      exact unitTorusNegativeTransportAmp_neg_conjugate
        r s (omega r) (eta s)) q

/-- The complete finite unit-torus vorticity RHS preserves the real Fourier
subspace. -/
theorem finiteUnitTorusVorticityRHS_neg_conjugate
    (sourceModes receiverModes : Finset Wavevector)
    (hsource : ∀ k, -k ∈ sourceModes ↔ k ∈ sourceModes)
    (hreceiver : ∀ k, -k ∈ receiverModes ↔ k ∈ receiverModes)
    (omega eta : FourierVelocity)
    (homega : ∀ k, omega (-k) = coefficientConjugate (omega k))
    (heta : ∀ k, eta (-k) = coefficientConjugate (eta k))
    (nu : ℝ) (q : Wavevector) :
    finiteUnitTorusVorticityRHS
        sourceModes receiverModes omega eta nu (-q) =
      coefficientConjugate
        (finiteUnitTorusVorticityRHS
          sourceModes receiverModes omega eta nu q) := by
  unfold finiteUnitTorusVorticityRHS finiteUnitTorusNonstretchingCoeff
  rw [finiteUnitTorusStretchingCoeff_neg_conjugate
      sourceModes receiverModes hsource hreceiver omega eta homega heta,
    finiteUnitTorusNegativeTransportCoeff_neg_conjugate
      sourceModes receiverModes hsource hreceiver omega eta homega heta,
    unitTorusViscousVorticityCoeff_neg_conjugate nu eta heta]
  rw [← coefficientConjugate_add, ← coefficientConjugate_add]

theorem mem_squareDyadicShellModes_neg_iff (N : ℕ) (k : Wavevector) :
    -k ∈ squareDyadicShellModes N ↔ k ∈ squareDyadicShellModes N := by
  rw [mem_squareDyadicShellModes_iff, mem_squareDyadicShellModes_iff,
    modeSquareNat_neg]

/-- The actual hard pancake mode set is closed under Fourier conjugation. -/
theorem mem_squareDyadicPancakeModes_neg_iff
    (F : OrientedFrameEquiv) (N : ℕ) (k : Wavevector) :
    -k ∈ squareDyadicPancakeModes F N ↔
      k ∈ squareDyadicPancakeModes F N := by
  rw [mem_squareDyadicPancakeModes_iff,
    mem_squareDyadicPancakeModes_iff,
    mem_squareDyadicShellModes_neg_iff,
    inOrientedSquarePancakeConeAnnulus_neg_iff]

/-! ## A generic real finite Fourier reconstruction -/

/-- A negation-closed finite Fourier set reconstructs a real field whenever
its coefficients obey the physical conjugate symmetry. -/
theorem finiteFourierReconstruction_conj_eq_self_of_neg_closed
    (s : Finset Wavevector) (omega : FourierVelocity)
    (hs : ∀ k, -k ∈ s ↔ k ∈ s)
    (hreal : ∀ k, omega (-k) = fun i ↦ conj (omega k i))
    (x : UnitAddTorus (Fin 3)) :
    (fun i ↦ conj (finiteFourierReconstruction s omega x i)) =
      finiteFourierReconstruction s omega x := by
  classical
  ext i
  unfold finiteFourierReconstruction
  simp only [Finset.sum_apply]
  change (starRingEnd ℂ)
      (∑ k ∈ s, UnitAddTorus.mFourier k x * omega k i) =
    ∑ k ∈ s, UnitAddTorus.mFourier k x * omega k i
  rw [map_sum]
  have hconj :
      (∑ k ∈ s,
          (starRingEnd ℂ) (UnitAddTorus.mFourier k x * omega k i)) =
        ∑ k ∈ s,
          UnitAddTorus.mFourier (-k) x * omega (-k) i := by
    apply Finset.sum_congr rfl
    intro k hk
    rw [map_mul]
    simp only [starRingEnd_apply]
    rw [UnitAddTorus.mFourier_neg, hreal]
    rfl
  rw [hconj]
  exact Finset.sum_bij (fun k _hk ↦ -k)
    (fun k hk ↦ (hs k).mpr hk)
    (fun a _ha b _hb hab ↦ by
      simpa using congrArg Neg.neg hab)
    (fun b hb ↦ ⟨-b, (hs b).mpr hb, by simp⟩)
    (fun k _hk ↦ by simp)

/-- Every coordinate of such a reconstruction has zero imaginary part. -/
theorem finiteFourierReconstruction_im_eq_zero_of_neg_closed
    (s : Finset Wavevector) (omega : FourierVelocity)
    (hs : ∀ k, -k ∈ s ↔ k ∈ s)
    (hreal : ∀ k, omega (-k) = fun i ↦ conj (omega k i))
    (x : UnitAddTorus (Fin 3)) (i : Fin 3) :
    (finiteFourierReconstruction s omega x i).im = 0 := by
  have hself := congrFun
    (finiteFourierReconstruction_conj_eq_self_of_neg_closed
      s omega hs hreal x) i
  have him := congrArg Complex.im hself
  simp only [Complex.conj_im] at him
  linarith

/-! ## Specialization to the actual hard pancake block -/

/-- A physical conjugate-symmetric Fourier field has a genuinely real hard
square-dyadic pancake reconstruction. -/
theorem squareDyadicPancakeBlock_conj_eq_self
    (F : OrientedFrameEquiv) (N : ℕ) (omega : FourierVelocity)
    (hreal : ∀ k, omega (-k) = fun i ↦ conj (omega k i))
    (x : BilinearSpatialTorus) :
    (fun i ↦ conj (squareDyadicPancakeBlock F N omega x i)) =
      squareDyadicPancakeBlock F N omega x := by
  exact finiteFourierReconstruction_conj_eq_self_of_neg_closed
    (squareDyadicPancakeModes F N) omega
    (mem_squareDyadicPancakeModes_neg_iff F N) hreal x

theorem squareDyadicPancakeBlock_im_eq_zero
    (F : OrientedFrameEquiv) (N : ℕ) (omega : FourierVelocity)
    (hreal : ∀ k, omega (-k) = fun i ↦ conj (omega k i))
    (x : BilinearSpatialTorus) (i : Fin 3) :
    (squareDyadicPancakeBlock F N omega x i).im = 0 := by
  exact finiteFourierReconstruction_im_eq_zero_of_neg_closed
    (squareDyadicPancakeModes F N) omega
    (mem_squareDyadicPancakeModes_neg_iff F N) hreal x i

/-- Taking coordinatewise real part of the physical hard block loses no
information: complexifying it returns the original reconstruction. -/
theorem ofReal_squareDyadicPancakeRealBlock_eq
    (F : OrientedFrameEquiv) (N : ℕ) (omega : FourierVelocity)
    (hreal : ∀ k, omega (-k) = fun i ↦ conj (omega k i))
    (x : BilinearSpatialTorus) :
    (fun i ↦ ((squareDyadicPancakeRealBlock F N omega x i : ℝ) : ℂ)) =
      squareDyadicPancakeBlock F N omega x := by
  ext i
  apply Complex.ext
  · rfl
  · simp [squareDyadicPancakeBlock_im_eq_zero F N omega hreal x i]

end PancakeBlockReality
end NavierStokes
end FluidDynamics
end Mettapedia
