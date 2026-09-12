import Mettapedia.Analysis.PeriodicRadialRiesz
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.VorticityRegularizedQuadratic

/-!
# The radial kernel acting on the full vorticity

The new radial construction has its own Fourier weights. Its convolution
with the actual vorticity is identified through the full curl series and
the checked Riesz-to-strain contraction. No old annular kernel is silently
substituted, and no uniform unweighted kernel mass is assumed.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.VorticityRadialQuadratic

open MeasureTheory PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeCurlOutputTail
open PancakeBlockReality PancakeGalerkinKineticEnergy LocalLowDiffusionBudget
open VorticityStretchingKernel VorticityRegularizedConvolution VorticityRegularizedQuadratic
open PancakePeriodicComplexStretch PancakePeriodicVorticityEquation ComplexPressurePair
open Mettapedia.Analysis EuclideanCrossProduct
open scoped RealInnerProductSpace Matrix
local notation "T3" => UnitAddTorus (Fin 3)
local notation "R3" => EuclideanSpace ℝ (Fin 3)
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

theorem hasSum_entry_convolution (u : FourierVelocity) (hu : Summable (fourierMoment 1 u))
    (hr : ∀ k, u (-k) = coefficientConjugate (u k))
    (i j l : Fin 3) (N : ℕ) (x : T3) :
    HasSum (fun k : Wavevector ↦
      ((RadialRieszRegularization.weight N (UnitTorusLattice.frequency k) *
        AnnularRieszKernel.rieszEntry i j (UnitTorusLattice.frequency k) : ℝ) : ℂ) *
        UnitAddTorus.mFourier k x * fourierCurl u k l)
      ((∫ h : T3, (PeriodicRadialRiesz.entry N i j h).re * fullVorticity u (x - h) l : ℝ) : ℂ) := by
  have h := UnitTorusIntegrableConvolution.hasSum_convolution
    (fun h ↦ ((PeriodicRadialRiesz.entry N i j h).re : ℂ))
    (PeriodicRadialRiesz.integrable_entry N i j).re.ofReal
    (curlComponent u l) (fun k ↦ fourierCurl u k l) (hasSum_curlComponent u hu l) x
  simp only [PeriodicRadialRiesz.mFourierCoeff_re_entry, curlComponent_apply u hu hr,
    ← Complex.ofReal_mul, _root_.integral_complex_ofReal] at h
  exact h

def quadraticStretch (N : ℕ) (u : FourierVelocity) (x : T3) (a : R3) : ℝ :=
  ∫ h : T3, ⟪cross a (fullVorticity u (x - h)), PeriodicRadialRiesz.tensor N h a⟫

theorem inner_cross_tensor (N : ℕ) (h : T3) (a b : R3) :
    ⟪cross a b, PeriodicRadialRiesz.tensor N h a⟫ =
      ∑ i : Fin 3, ∑ j : Fin 3, ∑ l : Fin 3,
        crossEntryWeight a i j l * (PeriodicRadialRiesz.entry N i j h).re * b l := by
  simp only [EuclideanSpace.inner_eq_star_dotProduct, star_trivial, dotProduct,
    PeriodicRadialRiesz.tensor_apply_component]
  simpa only [mul_comm] using cross_entry_contraction a b (fun i j ↦ (PeriodicRadialRiesz.entry N i j h).re)

theorem integrable_entry_vorticity (N : ℕ) (u : FourierVelocity)
    (hu : Summable (fourierMoment 1 u)) (x : T3) (i j l : Fin 3) :
    Integrable (fun h : T3 ↦ (PeriodicRadialRiesz.entry N i j h).re * fullVorticity u (x - h) l) := by
  let f : C(T3, ℝ) := ⟨fun h ↦ fullVorticity u (x - h) l, by
    have hw := continuous_fullVorticity u hu
    fun_prop⟩
  exact IntegrableKernelPairing.integrable_mul volume _
    (PeriodicRadialRiesz.integrable_entry N i j).re f

theorem quadraticStretch_eq_entries (N : ℕ) (u : FourierVelocity)
    (hu : Summable (fourierMoment 1 u)) (x : T3) (a : R3) :
    quadraticStretch N u x a = ∑ i : Fin 3, ∑ j : Fin 3, ∑ l : Fin 3,
      crossEntryWeight a i j l * ∫ h : T3,
        (PeriodicRadialRiesz.entry N i j h).re * fullVorticity u (x - h) l := by
  unfold quadraticStretch
  simp_rw [inner_cross_tensor, mul_assoc]
  rw [integral_finsetSum _ (fun i _ ↦ integrable_finsetSum _ (fun j _ ↦
    integrable_finsetSum _ (fun l _ ↦ (integrable_entry_vorticity N u hu x i j l).const_mul _)))]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_finsetSum _ (fun j _ ↦ integrable_finsetSum _ (fun l _ ↦
    (integrable_entry_vorticity N u hu x i j l).const_mul _))]
  apply Finset.sum_congr rfl
  intro j _
  rw [integral_finsetSum _ (fun l _ ↦ (integrable_entry_vorticity N u hu x i j l).const_mul _)]
  simp only [integral_const_mul]

theorem hasSum_quadraticStretch (N : ℕ) (u : FourierVelocity)
    (hu : Summable (fourierMoment 1 u))
    (hr : ∀ k, u (-k) = coefficientConjugate (u k))
    (hd : ∀ k, modeDot k (u k) = 0) (x : T3) (a : R3) :
    HasSum (fun k : Wavevector ↦ (RadialRieszRegularization.weight N (UnitTorusLattice.frequency k) : ℂ) *
      UnitAddTorus.mFourier k x *
        coefficientDot (realCoefficient a) ((PancakeFourierPressureStrain.strainCoeff u k).mulVec
          (realCoefficient a))) (quadraticStretch N u x a : ℂ) := by
  have hs := hasSum_sum (s := (Finset.univ : Finset (Fin 3))) (fun i _ ↦
    hasSum_sum (s := (Finset.univ : Finset (Fin 3))) (fun j _ ↦
      hasSum_sum (s := (Finset.univ : Finset (Fin 3))) (fun l _ ↦
        (hasSum_entry_convolution u hu hr i j l N x).mul_left (crossEntryWeight a i j l : ℂ))))
  have he : (quadraticStretch N u x a : ℂ) =
      ∑ i : Fin 3, ∑ j : Fin 3, ∑ l : Fin 3, (crossEntryWeight a i j l : ℂ) *
        ((∫ h : T3, (PeriodicRadialRiesz.entry N i j h).re * fullVorticity u (x - h) l : ℝ) : ℂ) := by
    rw [quadraticStretch_eq_entries N u hu x a]
    push_cast
    rfl
  rw [he]
  apply hs.congr_fun
  intro k
  rw [← strainStretch_fourierCurl k u (realCoefficient a) (hd k), ← symbol_cross_entry_contraction]
  simp only [Finset.mul_sum, Complex.ofReal_mul]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro l _
  ring

end Mettapedia.FluidDynamics.NavierStokes.VorticityRadialQuadratic
