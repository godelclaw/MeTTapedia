import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.FourierEllipticProductCoefficients
import Mettapedia.Analysis.FiniteCoefficientEnergy

/-!
# Elliptic product energy paid by spatial pressure bounds

The constants count only the three spatial coordinates, never Fourier
modes. Integer-frequency cutoff energies retain the unit-torus
derivative normalization described by `coordinateMultiplier`.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.FourierEllipticProductEnergy

open scoped BigOperators
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeMisalignmentEnergyBridge
open PancakeFiniteFourierLocalization PancakeQuadraticFourierSupport
open FourierPressureEllipticCommutator FourierEllipticProductCoefficients FourierProductEnergy
open FourierPressureLocalization
open Mettapedia.Analysis.FiniteMultiplierLocalization

local notation "T3" => UnitAddTorus (Fin 3)
local notation "R3" => EuclideanSpace ℝ (Fin 3)

def coordinateEnergy (P : Finset Wavevector) (c : Wavevector → ℂ) : ℝ :=
  ∑ j : Fin 3, scalarEnergy P (coordinateMultiplier c j)

def secondCoordinateEnergy (P : Finset Wavevector) (c : Wavevector → ℂ) : ℝ :=
  ∑ i : Fin 3, ∑ j : Fin 3, scalarEnergy P (secondCoordinateMultiplier c i j)

theorem laplaceEnergy_le (P : Finset Wavevector) (c : Wavevector → ℂ) :
    scalarEnergy P (laplaceMultiplier c) ≤ 3 * secondCoordinateEnergy P c := by
  have h := scalarEnergy_sum_le P Finset.univ (fun j : Fin 3 ↦ secondCoordinateMultiplier c j j)
  simp only [← laplaceMultiplier_eq_sum, Finset.card_univ, Fintype.card_fin, Nat.cast_ofNat] at h
  apply h.trans
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 3)
  apply Finset.sum_le_sum
  intro i _
  exact Finset.single_le_sum (fun j _ ↦ scalarEnergy_nonneg P _) (Finset.mem_univ i)

theorem scalarCoefficient_energy_le (P K : Finset Wavevector) (c phi : Wavevector → ℂ)
    (B0 B1 : ℝ) (h0 : ∀ x : T3, ‖finiteScalarFourierReconstruction K phi x‖ ≤ B0)
    (h1 : ∀ j : Fin 3, ∀ x : T3, ‖finiteScalarFourierReconstruction K (coordinateMultiplier phi j) x‖ ≤ B1) :
    scalarEnergy (finiteCutoffOutputModes P K) (ellipticScalarCoefficient P K c phi) ≤
      24 * B1 ^ 2 * coordinateEnergy P c + 6 * B0 ^ 2 * secondCoordinateEnergy P c := by
  let Q := finiteCutoffOutputModes P K
  let d := fun j : Fin 3 ↦ scalarConvolution P K (coordinateMultiplier c j) (coordinateMultiplier phi j)
  have hd : scalarEnergy Q (fun q ↦ ∑ j : Fin 3, d j q) ≤ 3 * B1 ^ 2 * coordinateEnergy P c := by
    have hs := scalarEnergy_sum_le Q Finset.univ d
    simp only [Finset.card_univ, Fintype.card_fin, Nat.cast_ofNat] at hs
    have hb := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) ↦
      scalarEnergy_convolution_le P K (coordinateMultiplier c j) (coordinateMultiplier phi j) B1 (h1 j))
    rw [← Finset.mul_sum] at hb
    exact hs.trans (by dsimp [coordinateEnergy]; nlinarith only [hb])
  have hL := (scalarEnergy_convolution_le P K (laplaceMultiplier c) phi B0 h0).trans
    (mul_le_mul_of_nonneg_left (laplaceEnergy_le P c) (sq_nonneg B0))
  have ha := scalarEnergy_add_le Q (fun q ↦ (2 : ℂ) * ∑ j : Fin 3, d j q)
    (scalarConvolution P K (laplaceMultiplier c) phi)
  rw [scalarEnergy_const_mul] at ha
  norm_num only [Complex.norm_ofNat, Nat.reducePow] at ha
  have hid : ellipticScalarCoefficient P K c phi =
      fun q ↦ (2 : ℂ) * (∑ j : Fin 3, d j q) + scalarConvolution P K (laplaceMultiplier c) phi q := by
    funext q
    exact scalarCoefficient_eq_products P K c phi q
  rw [hid]
  nlinarith only [ha, hd, hL]

theorem tensorCoefficient_energy_le (P K : Finset Wavevector) (c phi : Wavevector → ℂ)
    (B0 B1 : ℝ) (h0 : ∀ x : T3, ‖finiteScalarFourierReconstruction K phi x‖ ≤ B0)
    (h1 : ∀ j : Fin 3, ∀ x : T3, ‖finiteScalarFourierReconstruction K (coordinateMultiplier phi j) x‖ ≤ B1)
    (i j : Fin 3) :
    scalarEnergy (finiteCutoffOutputModes P K) (fun q ↦ tensorCoefficient P K c phi q i j) ≤
      3 * (B1 ^ 2 * scalarEnergy P (coordinateMultiplier c i) +
        B1 ^ 2 * scalarEnergy P (coordinateMultiplier c j) +
        B0 ^ 2 * scalarEnergy P (secondCoordinateMultiplier c i j)) := by
  have hid : (fun q ↦ tensorCoefficient P K c phi q i j) = fun q ↦
      scalarConvolution P K (coordinateMultiplier c i) (coordinateMultiplier phi j) q +
      scalarConvolution P K (coordinateMultiplier c j) (coordinateMultiplier phi i) q +
      scalarConvolution P K (secondCoordinateMultiplier c i j) phi q :=
    funext (fun q ↦ tensorCoefficient_eq_products P K c phi q i j)
  rw [hid]
  exact (scalarEnergy_add_add_le _ _ _ _).trans
    (mul_le_mul_of_nonneg_left
      (add_le_add (add_le_add
        (scalarEnergy_convolution_le P K _ _ B1 (h1 j))
        (scalarEnergy_convolution_le P K _ _ B1 (h1 i)))
        (scalarEnergy_convolution_le P K _ _ B0 h0)) (by norm_num))

theorem vectorCoefficient_energy_le (P K : Finset Wavevector) (c phi : Wavevector → ℂ)
    (e : R3) (he : ‖e‖ = 1) (B0 B1 : ℝ)
    (h0 : ∀ x : T3, ‖finiteScalarFourierReconstruction K phi x‖ ≤ B0)
    (h1 : ∀ j : Fin 3, ∀ x : T3, ‖finiteScalarFourierReconstruction K (coordinateMultiplier phi j) x‖ ≤ B1) :
    vectorEnergy (finiteCutoffOutputModes P K) (ellipticVectorCoefficient P K c phi e) ≤
      72 * B1 ^ 2 * coordinateEnergy P c + 12 * B0 ^ 2 * secondCoordinateEnergy P c := by
  have h := Finset.sum_le_sum (fun q (_ : q ∈ finiteCutoffOutputModes P K) ↦
    norm_vectorCoefficient_sq_le_tensor P K c phi e he q)
  rw [← Finset.mul_sum, Finset.sum_comm] at h
  simp_rw [Finset.sum_comm (s := finiteCutoffOutputModes P K)] at h
  have ht := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin 3))) ↦
    Finset.sum_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin 3))) ↦
      tensorCoefficient_energy_le P K c phi B0 B1 h0 h1 i j))
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_ofNat] at ht
  change vectorEnergy _ _ ≤ 4 * (∑ i : Fin 3, ∑ j : Fin 3,
    scalarEnergy (finiteCutoffOutputModes P K) (fun q ↦ tensorCoefficient P K c phi q i j)) at h
  dsimp [coordinateEnergy, secondCoordinateEnergy]
  nlinarith only [h, ht]

theorem tiltCommutatorEnergy_le (c : FourierCoeff (Fin 3)) (chi : Wavevector → ℂ)
    (K : Finset Wavevector) (u : FourierVelocity) (e : R3) (he : ‖e‖ = 1) (B0 B1 : ℝ)
    (h0 : ∀ x : T3, ‖finiteScalarFourierReconstruction K (potentialAmplitude chi u) x‖ ≤ B0)
    (h1 : ∀ j : Fin 3, ∀ x : T3,
      ‖finiteScalarFourierReconstruction K (coordinateMultiplier (potentialAmplitude chi u) j) x‖ ≤ B1) :
    tiltCommutatorEnergy c chi K u e ≤
      192 * B1 ^ 2 * coordinateEnergy c.support c +
        36 * B0 ^ 2 * secondCoordinateEnergy c.support c := by
  have h := tiltCommutatorEnergy_le_elliptic_products c chi K u e he
  have hs := scalarCoefficient_energy_le c.support K c (potentialAmplitude chi u) B0 B1 h0 h1
  have hv := vectorCoefficient_energy_le c.support K c (potentialAmplitude chi u) e he B0 B1 h0 h1
  linarith only [h, hs, hv]

end Mettapedia.FluidDynamics.NavierStokes.FourierEllipticProductEnergy
