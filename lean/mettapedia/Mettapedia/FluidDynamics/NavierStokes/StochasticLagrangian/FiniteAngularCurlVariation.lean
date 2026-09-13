import Mettapedia.Analysis.AngularCurlEvolution
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.FiniteVorticityMixedJets
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.FilteredProjectionMean
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.FiniteBandAngularEnergy

/-!
# Finite-filter variation of the actual angular cost

The input variation is kept as a coefficient field. In particular, the
variation of a filtered solution must be the filtered full RHS, not an
assumed closed equation for the retained modes.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.FiniteAngularCurlVariation

open scoped RealInnerProductSpace
open Mettapedia.Analysis
open PeriodicFourierTriad PancakeGalerkinKineticEnergy PancakeInfiniteFourierDerivative
open PancakePeriodicVorticityEquation LocalLowDiffusionBudget LocalSpatialVorticityJets
open LocalVorticityEighthMoment LocalAngularCurlBudget FourierFiniteSupport
open FiniteVorticityMixedJets
local notation "T3" => UnitAddTorus (Fin 3)

theorem hasDerivAt_fullCurlGradient (P : Finset Wavevector) (u : ℝ → FourierVelocity)
    (hs : ∀ τ q, q ∉ P → u τ q = 0) (v : FourierVelocity) (hv : ∀ q, q ∉ P → v q = 0)
    (j : Fin 3) (t : ℝ) (x : T3)
    (hd : ∀ q ∈ P, ∀ i, HasDerivAt (fun τ ↦ u τ q i) (v q i) t) :
    HasDerivAt (fun τ ↦ fullCurlGradient (u τ) j x) (fullCurlGradient v j x) t := by
  have h := FiniteVorticityVariation.hasDerivAt_fullVorticity P
    (fun τ ↦ indexedDerivativeCoeff id j (u τ))
    (fun τ ↦ derivative_eq_zero P _ (hs τ) j) (indexedDerivativeCoeff id j v) t x
    (fun q hq i ↦ by
      simpa only [indexedDerivativeCoeff, Pi.smul_apply, smul_eq_mul, id_eq] using
        (hd q hq i).const_mul (unitTorusDerivativePhase * (q j : ℂ)))
  rw [FilteredProjectionMean.restrictVelocity_eq_self P _ (derivative_eq_zero P v hv j)] at h
  have he : (fun τ ↦ fullVorticity (indexedDerivativeCoeff id j (u τ)) x) =
      (fun τ ↦ fullCurlGradient (u τ) j x) := by
    funext τ
    exact congrFun (fullVorticity_derivative P _ (hs τ) j) x
  rw [he, fullVorticity_derivative P v hv j] at h
  exact h

def densityRate (u v : FourierVelocity) (x : T3) : ℝ :=
  AngularCurlDecomposition.angularCurlDensityRate (fullVorticity u x) (fun j ↦ fullCurlGradient u j x)
    (fullVorticity v x) (fun j ↦ fullCurlGradient v j x)

def correctedDensity (κ : ℝ) (u : FourierVelocity) (x : T3) : ℝ :=
  LocalVorticityEighthMoment.energy u x / 8 - 3 / κ * angularCurlDensity u x

def correctedDensityRate (κ : ℝ) (u v : FourierVelocity) (x : T3) : ℝ :=
  ‖fullVorticity u x‖ ^ 6 * ⟪fullVorticity u x, fullVorticity v x⟫ - 3 / κ * densityRate u v x

theorem fullCurlGradient_restrictVelocity (P : Finset Wavevector) (u : FourierVelocity) (j : Fin 3) :
    fullCurlGradient (FiniteVorticityVariation.restrictVelocity P u) j =
      fullVorticity (FiniteVorticityVariation.restrictVelocity P (indexedDerivativeCoeff id j u)) := by
  rw [← fullVorticity_derivative P _ (FiniteVorticityVariation.restrictVelocity_eq_zero P u) j]
  congr 1
  ext q i
  simp [indexedDerivativeCoeff, FiniteVorticityVariation.restrictVelocity,
    PancakeFilteredStrainDynamics.filteredVelocity]
  ring

theorem correctedDensityRate_restrict_add (κ : ℝ) (P : Finset Wavevector)
    (u v w : FourierVelocity) (x : T3) :
    correctedDensityRate κ u (FiniteVorticityVariation.restrictVelocity P (v + w)) x =
      correctedDensityRate κ u (FiniteVorticityVariation.restrictVelocity P v) x +
        correctedDensityRate κ u (FiniteVorticityVariation.restrictVelocity P w) x := by
  have hd (j : Fin 3) : indexedDerivativeCoeff id j (v + w) =
      indexedDerivativeCoeff id j v + indexedDerivativeCoeff id j w := by
    ext q i
    simp [indexedDerivativeCoeff, mul_add]
  simp only [correctedDensityRate, densityRate, fullCurlGradient_restrictVelocity,
    FiniteVorticityVariation.fullVorticity_restrictVelocity, hd,
    FiniteVorticityVariation.spatialVorticity_add, AngularCurlDecomposition.angularCurlDensityRate_add,
    inner_add_right]
  ring

theorem hasDerivAt_correctedDensity (κ : ℝ) (P : Finset Wavevector) (u : ℝ → FourierVelocity)
    (hs : ∀ τ q, q ∉ P → u τ q = 0) (v : FourierVelocity) (hv : ∀ q, q ∉ P → v q = 0)
    (t : ℝ) (x : T3) (hd : ∀ q ∈ P, ∀ i, HasDerivAt (fun τ ↦ u τ q i) (v q i) t) :
    HasDerivAt (fun τ ↦ correctedDensity κ (u τ) x) (correctedDensityRate κ (u t) v x) t := by
  have ha := FiniteVorticityVariation.hasDerivAt_fullVorticity P u hs v t x hd
  rw [FilteredProjectionMean.restrictVelocity_eq_self P v hv] at ha
  have hD := fun j ↦ hasDerivAt_fullCurlGradient P u hs v hv j t x hd
  have hK := AngularCurlDecomposition.hasDerivAt_angularCurlDensity ha hD
  have h := ((ha.norm_sq.fun_pow 4).div_const 8).sub (hK.const_mul (3 / κ))
  apply h.congr_deriv
  norm_num only [Nat.cast_ofNat, Nat.reduceSub, ← pow_mul, Nat.reduceMul]
  unfold correctedDensityRate densityRate
  ring

section Continuity

variable {Y : Type*} [TopologicalSpace Y]

theorem continuous_fullCurlGradient (P : Finset Wavevector) (u : Y → FourierVelocity)
    (hs : ∀ y q, q ∉ P → u y q = 0)
    (hu : ∀ q ∈ P, ∀ i, Continuous (fun y ↦ u y q i)) (j : Fin 3) :
    Continuous (fun z : Y × T3 ↦ fullCurlGradient (u z.1) j z.2) := by
  have h := FilteredProjectionMean.continuous_fullVorticity P (fun y ↦ indexedDerivativeCoeff id j (u y))
    (fun y ↦ derivative_eq_zero P _ (hs y) j)
    (fun q hq i ↦ (hu q hq i).const_mul (unitTorusDerivativePhase * (q j : ℂ)))
  have he : (fun z : Y × T3 ↦ fullVorticity (indexedDerivativeCoeff id j (u z.1)) z.2) =
      (fun z : Y × T3 ↦ fullCurlGradient (u z.1) j z.2) := by
    funext z
    exact congrFun (fullVorticity_derivative P _ (hs z.1) j) z.2
  exact he ▸ h

theorem continuous_correctedDensity (κ : ℝ) (P : Finset Wavevector) (u : Y → FourierVelocity)
    (hs : ∀ y q, q ∉ P → u y q = 0)
    (hu : ∀ q ∈ P, ∀ i, Continuous (fun y ↦ u y q i)) :
    Continuous (fun z : Y × T3 ↦ correctedDensity κ (u z.1) z.2) := by
  have ha := FilteredProjectionMean.continuous_fullVorticity P u hs hu
  have hD := continuous_fullCurlGradient P u hs hu
  have hK := AngularCurlDecomposition.continuous_angularCurlDensity _ _ ha hD
  exact (((ha.norm.pow 2).pow 4).div_const 8).sub (hK.const_mul (3 / κ))

theorem continuous_correctedDensityRate (κ : ℝ) (P : Finset Wavevector) (u v : Y → FourierVelocity)
    (hs : ∀ y q, q ∉ P → u y q = 0) (ht : ∀ y q, q ∉ P → v y q = 0)
    (hu : ∀ q ∈ P, ∀ i, Continuous (fun y ↦ u y q i))
    (hv : ∀ q ∈ P, ∀ i, Continuous (fun y ↦ v y q i)) :
    Continuous (fun z : Y × T3 ↦ correctedDensityRate κ (u z.1) (v z.1) z.2) := by
  have ha := FilteredProjectionMean.continuous_fullVorticity P u hs hu
  have hb := FilteredProjectionMean.continuous_fullVorticity P v ht hv
  have hD := continuous_fullCurlGradient P u hs hu
  have hE := continuous_fullCurlGradient P v ht hv
  have hK := AngularCurlDecomposition.continuous_angularCurlDensityRate _ _ _ _ ha hb hD hE
  exact ((ha.norm.pow 6).mul (ha.inner hb)).sub (hK.const_mul (3 / κ))

end Continuity

end Mettapedia.FluidDynamics.NavierStokes.FiniteAngularCurlVariation
