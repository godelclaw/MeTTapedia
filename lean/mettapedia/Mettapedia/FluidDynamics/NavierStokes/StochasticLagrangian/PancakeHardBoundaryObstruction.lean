import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeMovingBlockEvolution

/-!
# A low--high crossing of the actual hard pancake boundary

At scale `N²`, the unit shift `(-1,0,0)` moves `(N+1,0,N²)` into the
square-dyadic pancake cone at `(N,0,N²)`.  Both vorticity amplitudes may be
the unit vector `(0,1,0)`, transverse to their respective frequencies.  The
physical transport symbol is then `-N²` times that vector, and the physical
stretching symbol is zero.  Thus bulk material cancellation alone does not
give a scale-independent bound for this incoming bilinear interaction.

This is an instantaneous bilinear obstruction.  It does not refute a
time-integrated Navier--Stokes estimate or account for viscous damping.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PancakeHardBoundaryObstruction

open scoped BigOperators
open PeriodicFourierTriad PancakePeriodicComplexStretch
open PancakePeriodicVorticityEquation PancakeMaterialTransportCommutator
open PancakeFrameCovariance PancakeSquareDyadicSectorProjector
open PancakeArbitraryDataBlocks PancakeFrozenFrameKernelTransfer

def crossingSource : Wavevector := ![-1, 0, 0]
def crossingReceiver (N : ℕ) : Wavevector := ![(N : ℤ) + 1, 0, (N : ℤ) ^ 2]
def crossingOutput (N : ℕ) : Wavevector := ![(N : ℤ), 0, (N : ℤ) ^ 2]
def crossingPolarization : VelocityCoefficient := ![0, 1, 0]

theorem crossing_add (N : ℕ) :
    crossingSource + crossingReceiver N = crossingOutput N := by
  ext i
  fin_cases i <;> simp [crossingSource, crossingReceiver, crossingOutput]

theorem crossing_transverse (N : ℕ) :
    modeDot crossingSource crossingPolarization = 0 ∧
      modeDot (crossingReceiver N) crossingPolarization = 0 := by
  simp [modeDot, crossingSource, crossingReceiver, crossingPolarization,
    Fin.sum_univ_three]

theorem crossingPolarization_norm : ‖crossingPolarization‖ = 1 := by
  apply le_antisymm
  · apply (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)).2
    intro i
    fin_cases i <;> norm_num [crossingPolarization]
  · simpa [crossingPolarization] using
      (norm_le_pi_norm crossingPolarization (1 : Fin 3))

theorem crossing_transport (N : ℕ) :
    unitTorusNegativeTransportAmp crossingSource (crossingReceiver N)
        crossingPolarization crossingPolarization =
      (-(N : ℂ) ^ 2) • crossingPolarization := by
  rw [unitTorusNegativeTransportAmp_eq]
  ext i
  fin_cases i <;>
    simp [modeDot, complexBiotSavartAmp, modeSquare, coefficientCross,
      wavevectorCoefficient, crossingSource, crossingReceiver,
      crossingPolarization, Fin.sum_univ_three]

theorem crossing_stretch :
    unitTorusStrainStretchAmp crossingSource
        crossingPolarization crossingPolarization = 0 := by
  rw [unitTorusStrainStretchAmp_eq_neg_complexStretchAmp]
  ext i
  fin_cases i <;>
    norm_num [complexStretchAmp, complexBiotSavartAmp, modeSquare,
      coefficientCross, coefficientDot, modeDot, wavevectorCoefficient,
      crossingSource, crossingPolarization, Fin.sum_univ_three, Matrix.cons_val_two]

theorem identityFrame_wavevectorCoordinates (k : Wavevector) :
    orientedFrameWavevectorCoordinates identityFrame k =
      ((k 0 : ℝ), (k 1 : ℝ), (k 2 : ℝ)) := by
  rfl

theorem crossingOutput_in_cone {N : ℕ} (hN : 2 ≤ N) :
    InOrientedSquarePancakeConeAnnulus identityFrame N (crossingOutput N) := by
  have hn : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hn2 : (4 : ℝ) ≤ (N : ℝ) ^ 2 := by nlinarith
  have hn4 : (N : ℝ) ^ 2 ≤ (N : ℝ) ^ 4 := by
    nlinarith [sq_nonneg ((N : ℝ) ^ 2 - 1)]
  unfold InOrientedSquarePancakeConeAnnulus
  rw [identityFrame_wavevectorCoordinates]
  norm_num [InRealSquarePancakeConeAnnulus, crossingOutput,
    PancakeRealCoherentPairEstimate.normSq, PancakeRealCoherentPairEstimate.dot,
    Matrix.cons_val_two]
  constructor
  · omega
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor <;> nlinarith

theorem crossingReceiver_not_in_cone {N : ℕ} (hN : 2 ≤ N) :
    ¬ InOrientedSquarePancakeConeAnnulus identityFrame N (crossingReceiver N) := by
  have hn : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hn2 : (4 : ℝ) ≤ (N : ℝ) ^ 2 := by nlinarith
  have hn3 : (8 : ℝ) ≤ (N : ℝ) ^ 3 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hn) (sub_nonneg.mpr hn2)]
  intro h
  have hc := h.2.2.2.2
  rw [identityFrame_wavevectorCoordinates] at hc
  norm_num [crossingReceiver, PancakeRealCoherentPairEstimate.normSq,
    PancakeRealCoherentPairEstimate.dot, Matrix.cons_val_two] at hc
  nlinarith [mul_nonneg (sub_nonneg.mpr hn2) (show (0 : ℝ) ≤ N by positivity)]

theorem crossingOutput_mem_pancake {N : ℕ} (hN : 2 ≤ N) :
    crossingOutput N ∈ squareDyadicPancakeModes identityFrame N := by
  rw [mem_squareDyadicPancakeModes_iff]
  refine ⟨?_, crossingOutput_in_cone hN⟩
  rw [mem_squareDyadicShellModes_iff]
  have hsq : modeSquareNat (crossingOutput N) = N ^ 2 + N ^ 4 := by
    norm_num [modeSquareNat, crossingOutput, Fin.sum_univ_three,
      Matrix.cons_val_two, Int.natAbs_pow]
    ring
  rw [hsq]
  have hn2 : 4 ≤ N ^ 2 := by nlinarith
  have hn4 : N ^ 2 ≤ N ^ 4 := by nlinarith [sq_nonneg (N ^ 2 : ℤ)]
  constructor <;> nlinarith

theorem crossingReceiver_not_mem_pancake {N : ℕ} (hN : 2 ≤ N) :
    crossingReceiver N ∉ squareDyadicPancakeModes identityFrame N := by
  intro h
  exact crossingReceiver_not_in_cone hN
    ((mem_squareDyadicPancakeModes_iff _ _ _).mp h).2

/-- The exact incoming coefficient in the existing material commutator,
using the actual hard square-dyadic pancake block. -/
theorem crossing_material_boundary {N : ℕ} (hN : 2 ≤ N) :
    finiteMaterialNonlinearBoundaryCoeff {crossingSource} {crossingReceiver N}
        (squareDyadicPancakeModes identityFrame N)
        (fun _ ↦ crossingPolarization) (fun _ ↦ crossingPolarization)
        (crossingOutput N) =
      (-(N : ℂ) ^ 2) • crossingPolarization := by
  classical
  rw [finiteMaterialNonlinearBoundaryCoeff_eq,
    if_pos (crossingOutput_mem_pancake hN)]
  have hout : receiverModesOutside {crossingReceiver N}
      (squareDyadicPancakeModes identityFrame N) = {crossingReceiver N} := by
    simp [receiverModesOutside, crossingReceiver_not_mem_pancake hN]
  rw [hout, finiteUnitTorusNegativeTransportCoeff_eq_doubleSum,
    finiteUnitTorusStretchingCoeff_eq_doubleSum]
  simp [crossing_add, crossing_transport, crossing_stretch]

theorem crossing_material_boundary_norm {N : ℕ} (hN : 2 ≤ N) :
    ‖finiteMaterialNonlinearBoundaryCoeff {crossingSource} {crossingReceiver N}
        (squareDyadicPancakeModes identityFrame N)
        (fun _ ↦ crossingPolarization) (fun _ ↦ crossingPolarization)
        (crossingOutput N)‖ = (N : ℝ) ^ 2 := by
  rw [crossing_material_boundary hN, norm_smul, crossingPolarization_norm]
  simp

/-- Adding conjugate partner modes leaves this output unchanged.  Each
input is therefore realizable as a real trigonometric polynomial. -/
theorem real_crossing_material_boundary {N : ℕ} (hN : 2 ≤ N) :
    finiteMaterialNonlinearBoundaryCoeff
        {crossingSource, -crossingSource}
        {crossingReceiver N, -crossingReceiver N}
        (squareDyadicPancakeModes identityFrame N)
        (fun _ ↦ crossingPolarization) (fun _ ↦ crossingPolarization)
        (crossingOutput N) =
      (-(N : ℂ) ^ 2) • crossingPolarization := by
  classical
  have hn : (0 : ℤ) < (N : ℤ) ^ 2 := by
    have : (0 : ℤ) < N := by exact_mod_cast (show 0 < N by omega)
    positivity
  have hr : crossingReceiver N ≠ -crossingReceiver N := by
    intro he
    have hz := congrFun he 2
    norm_num [crossingReceiver, Matrix.cons_val_two] at hz
    omega
  have hs : crossingSource ≠ -crossingSource := by
    intro he
    have hx := congrFun he 0
    norm_num [crossingSource] at hx
  have hnr : -crossingReceiver N ∉ squareDyadicPancakeModes identityFrame N := by
    rw [PancakeBlockReality.mem_squareDyadicPancakeModes_neg_iff]
    exact crossingReceiver_not_mem_pancake hN
  have hout : receiverModesOutside {crossingReceiver N, -crossingReceiver N}
      (squareDyadicPancakeModes identityFrame N) =
      {crossingReceiver N, -crossingReceiver N} := by
    simp [receiverModesOutside, crossingReceiver_not_mem_pancake hN, hnr]
  have hbad₁ : crossingSource + -crossingReceiver N ≠ crossingOutput N := by
    intro he
    have hz := congrFun he 2
    norm_num [crossingSource, crossingReceiver, crossingOutput,
      Matrix.cons_val_two] at hz
    omega
  have hbad₂ : -crossingSource + crossingReceiver N ≠ crossingOutput N := by
    intro he
    have hx := congrFun he 0
    norm_num [crossingSource, crossingReceiver, crossingOutput] at hx
    omega
  have hbad₃ : -crossingSource + -crossingReceiver N ≠ crossingOutput N := by
    intro he
    have hz := congrFun he 2
    norm_num [crossingSource, crossingReceiver, crossingOutput,
      Matrix.cons_val_two] at hz
    omega
  rw [finiteMaterialNonlinearBoundaryCoeff_eq,
    if_pos (crossingOutput_mem_pancake hN), hout,
    finiteUnitTorusNegativeTransportCoeff_eq_doubleSum,
    finiteUnitTorusStretchingCoeff_eq_doubleSum]
  simp [hs, hr, crossing_add, hbad₁, hbad₂, hbad₃,
    crossing_transport, crossing_stretch]

/-- Even for transverse unit amplitudes, this material boundary coefficient
has no instantaneous scale-independent bilinear bound. -/
theorem no_uniform_crossing_material_boundary_bound :
    ¬ ∃ C : ℝ, ∀ N : ℕ, 2 ≤ N →
      ‖finiteMaterialNonlinearBoundaryCoeff {crossingSource} {crossingReceiver N}
          (squareDyadicPancakeModes identityFrame N)
          (fun _ ↦ crossingPolarization) (fun _ ↦ crossingPolarization)
          (crossingOutput N)‖ ≤ C * ‖crossingPolarization‖ ^ 2 := by
  rintro ⟨C, hC⟩
  obtain ⟨N, hN⟩ := exists_nat_gt (max C 2)
  have hn : (2 : ℝ) < N := (le_max_right C 2).trans_lt hN
  have hnat : 2 ≤ N := by exact_mod_cast hn.le
  have hc := hC N hnat
  rw [crossing_material_boundary_norm hnat, crossingPolarization_norm] at hc
  have hcn : C < N := (le_max_left C 2).trans_lt hN
  nlinarith

end Mettapedia.FluidDynamics.NavierStokes.PancakeHardBoundaryObstruction
