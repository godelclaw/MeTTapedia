import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.VorticityRegularizedConvolution

/-! # Coordinate contraction of the regularized kernel with signed stretching -/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.VorticityRegularizedQuadratic

open MeasureTheory PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeCurlOutputTail
open PancakeBlockReality PancakeGalerkinKineticEnergy LocalLowDiffusionBudget
open VorticityStretchingKernel VorticityRegularizedConvolution
open PancakePeriodicComplexStretch PancakePeriodicVorticityEquation
open ComplexPressurePair
open FourierPressureCommutator
open Mettapedia.Analysis EuclideanCrossProduct
open scoped RealInnerProductSpace Matrix
local notation "T3" => UnitAddTorus (Fin 3)
local notation "R3" => EuclideanSpace ℝ (Fin 3)
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

def crossEntryWeight (a : R3) (i j l : Fin 3) : ℝ :=
  (cross a (EuclideanSpace.single l 1)) i * a j

theorem cross_entry_contraction (a b : R3) (M : Fin 3 → Fin 3 → ℝ) :
    (∑ i : Fin 3, (cross a b) i * ∑ j : Fin 3, M i j * a j) =
      ∑ i : Fin 3, ∑ j : Fin 3, ∑ l : Fin 3, crossEntryWeight a i j l * M i j * b l := by
  simp [Fin.sum_univ_three, crossEntryWeight, cross, crossProduct, Pi.single_apply]
  ring

theorem inner_cross_kernel (N : ℕ) (h : T3) (a b : R3) :
    ⟪cross a b, PeriodicRieszOperator.kernel N h a⟫ =
      ∑ i : Fin 3, ∑ j : Fin 3, ∑ l : Fin 3,
        crossEntryWeight a i j l * PeriodicRieszOperator.entryKernel i j N h * b l := by
  simp only [EuclideanSpace.inner_eq_star_dotProduct, star_trivial, dotProduct,
    PeriodicRieszOperator.kernel_apply_component]
  simpa only [mul_comm] using cross_entry_contraction a b (fun i j ↦ PeriodicRieszOperator.entryKernel i j N h)

theorem symbol_cross_entry_contraction (k : Wavevector) (a : R3) (v : VelocityCoefficient) :
    (∑ i : Fin 3, ∑ j : Fin 3, ∑ l : Fin 3,
      ((crossEntryWeight a i j l * AnnularRieszKernel.rieszEntry i j
        (UnitTorusLattice.frequency k) : ℝ) : ℂ) * v l) =
      coefficientDot (realCoefficient a) (unitTorusStrainStretchAmp k v (realCoefficient a)) := by
  rw [← coefficientDot_quadraticSymbol]
  simp [Fin.sum_univ_three, crossEntryWeight, cross, crossProduct, Pi.single_apply,
    quadraticSymbol, projectionSymbol_apply, realCoefficient, coefficientDot,
    AnnularRieszKernel.rieszEntry, UnitTorusLattice.frequency, realFrequency,
    EuclideanSpace.inner_eq_star_dotProduct, dotProduct]
  ring

def quadraticStretch (N : ℕ) (u : FourierVelocity) (x : T3) (a : R3) : ℝ :=
  ∫ h : T3, ⟪cross a (fullVorticity u (x - h)), PeriodicRieszOperator.kernel N h a⟫

theorem integrable_entry_vorticity (N : ℕ) (u : FourierVelocity)
    (hu : Summable (fourierMoment 1 u)) (x : T3) (i j l : Fin 3) :
    Integrable (fun h : T3 ↦ PeriodicRieszOperator.entryKernel i j N h * fullVorticity u (x - h) l) := by
  let f : C(T3, ℝ) := ⟨fun h ↦ fullVorticity u (x - h) l, by
    have hw := continuous_fullVorticity u hu
    fun_prop⟩
  exact IntegrableKernelPairing.integrable_mul volume _
    (PeriodicRieszOperator.integrable_entryKernel i j N) f

theorem quadraticStretch_eq_entries (N : ℕ) (u : FourierVelocity)
    (hu : Summable (fourierMoment 1 u)) (x : T3) (a : R3) :
    quadraticStretch N u x a = ∑ i : Fin 3, ∑ j : Fin 3, ∑ l : Fin 3,
      crossEntryWeight a i j l * ∫ h : T3,
        PeriodicRieszOperator.entryKernel i j N h * fullVorticity u (x - h) l := by
  unfold quadraticStretch
  simp_rw [inner_cross_kernel, mul_assoc]
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
    HasSum (fun k : Wavevector ↦ (AnnularRieszKernel.weight N (UnitTorusLattice.frequency k) : ℂ) *
      UnitAddTorus.mFourier k x *
        coefficientDot (realCoefficient a) ((PancakeFourierPressureStrain.strainCoeff u k).mulVec
          (realCoefficient a))) (quadraticStretch N u x a : ℂ) := by
  have hs := hasSum_sum (s := (Finset.univ : Finset (Fin 3))) (fun i _ ↦
    hasSum_sum (s := (Finset.univ : Finset (Fin 3))) (fun j _ ↦
      hasSum_sum (s := (Finset.univ : Finset (Fin 3))) (fun l _ ↦
        (hasSum_entry_convolution u hu hr i j l N x).mul_left (crossEntryWeight a i j l : ℂ))))
  have he : (quadraticStretch N u x a : ℂ) =
      ∑ i : Fin 3, ∑ j : Fin 3, ∑ l : Fin 3, (crossEntryWeight a i j l : ℂ) *
        ((∫ h : T3, PeriodicRieszOperator.entryKernel i j N h * fullVorticity u (x - h) l : ℝ) : ℂ) := by
    rw [quadraticStretch_eq_entries N u hu x a]
    push_cast
    rfl
  rw [he]
  apply hs.congr_fun
  intro k
  rw [← strainStretch_fourierCurl k u (realCoefficient a) (hd k),
    ← symbol_cross_entry_contraction]
  simp only [Finset.mul_sum, Complex.ofReal_mul]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro l _
  ring

end Mettapedia.FluidDynamics.NavierStokes.VorticityRegularizedQuadratic
