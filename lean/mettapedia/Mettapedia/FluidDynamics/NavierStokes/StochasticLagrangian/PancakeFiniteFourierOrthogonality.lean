import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakePhysicalNonlinearReconstruction

/-!
# Orthogonality of disjoint finite Fourier outputs

Disjoint coefficient supports have zero complex cross integral. If the
first reconstruction is real, this also proves orthogonality of the
actual real vector fields. No reality assumption on the second finite
output set is necessary.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PancakeFiniteFourierOrthogonality

open MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeMisalignmentEnergyBridge
open PancakeDyadicDirectionEvolution PancakeTransverseEnergyFreezing PancakeBlockReality

local notation "T3" => UnitAddTorus (Fin 3)

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

theorem integral_scalar_cross_disjoint (s t : Finset Wavevector) (a b : Wavevector → ℂ)
    (hd : Disjoint s t) :
    (∫ x : T3, conj (finiteScalarFourierReconstruction s a x) * finiteScalarFourierReconstruction t b x) = 0 := by
  classical
  let F := fun k l (x : T3) ↦ (conj (a k) * b l) *
    (UnitAddTorus.mFourier l x * conj (UnitAddTorus.mFourier k x))
  have hi : ∀ k l, Integrable (F k l) := by
    intro k l
    have hc : Continuous (F k l) := by dsimp [F]; fun_prop
    exact hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have he : ∀ x : T3, conj (finiteScalarFourierReconstruction s a x) * finiteScalarFourierReconstruction t b x =
      ∑ k ∈ s, ∑ l ∈ t, F k l x := by
    intro x
    simp only [finiteScalarFourierReconstruction, map_sum, map_mul, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro l _
    dsimp [F]
    ring
  simp only [he]
  rw [integral_finsetSum s (fun k _ ↦ integrable_finsetSum t (fun l _ ↦ hi k l))]
  apply Finset.sum_eq_zero
  intro k hk
  rw [integral_finsetSum t (fun l _ ↦ hi k l)]
  apply Finset.sum_eq_zero
  intro l hl
  have hkl : k ≠ l := fun h ↦ Finset.disjoint_left.mp hd hk (h ▸ hl)
  simp only [F, integral_const_mul, integral_mFourier_mul_conj_mFourier, if_neg hkl, mul_zero]

theorem integral_real_scalar_cross_disjoint (s t : Finset Wavevector) (a b : Wavevector → ℂ)
    (hd : Disjoint s t) (hr : ∀ x : T3, (finiteScalarFourierReconstruction s a x).im = 0) :
    (∫ x : T3, (finiteScalarFourierReconstruction s a x).re * (finiteScalarFourierReconstruction t b x).re) = 0 := by
  have hc : Continuous (fun x : T3 ↦ conj (finiteScalarFourierReconstruction s a x) *
      finiteScalarFourierReconstruction t b x) := by
    exact (continuous_finiteScalarFourierReconstruction s a).star.mul
      (continuous_finiteScalarFourierReconstruction t b)
  have hi := hc.integrable_of_hasCompactSupport (μ := volume) (HasCompactSupport.of_compactSpace _)
  calc
    _ = ∫ x : T3, (conj (finiteScalarFourierReconstruction s a x) * finiteScalarFourierReconstruction t b x).re := by
      apply integral_congr_ae
      filter_upwards [] with x
      simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im, hr, neg_zero, zero_mul, sub_zero]
    _ = (∫ x : T3, conj (finiteScalarFourierReconstruction s a x) * finiteScalarFourierReconstruction t b x).re :=
      integral_re hi
    _ = 0 := by rw [integral_scalar_cross_disjoint s t a b hd]; rfl

theorem integral_real_vector_inner_disjoint (s t : Finset Wavevector) (a b : FourierVelocity)
    (hd : Disjoint s t) (hr : ∀ x : T3, ∀ i : Fin 3, (finiteFourierReconstruction s a x i).im = 0) :
    (∫ x : T3, ⟪complexRealPartEuclidean (finiteFourierReconstruction s a x),
      complexRealPartEuclidean (finiteFourierReconstruction t b x)⟫) = 0 := by
  have he : ∀ x : T3, ⟪complexRealPartEuclidean (finiteFourierReconstruction s a x),
      complexRealPartEuclidean (finiteFourierReconstruction t b x)⟫ =
        ∑ i : Fin 3, (finiteScalarFourierReconstruction s (fun q ↦ a q i) x).re *
          (finiteScalarFourierReconstruction t (fun q ↦ b q i) x).re := by
    intro x
    change (∑ i : Fin 3, (finiteFourierReconstruction t b x i).re *
      (finiteFourierReconstruction s a x i).re) = _
    simp only [finiteFourierReconstruction_component, mul_comm]
  simp only [he]
  have hi : ∀ i : Fin 3, Integrable (fun x : T3 ↦
      (finiteScalarFourierReconstruction s (fun q ↦ a q i) x).re *
        (finiteScalarFourierReconstruction t (fun q ↦ b q i) x).re) := by
    intro i
    have hc : Continuous (fun x : T3 ↦
        (finiteScalarFourierReconstruction s (fun q ↦ a q i) x).re *
          (finiteScalarFourierReconstruction t (fun q ↦ b q i) x).re) :=
      (Complex.continuous_re.comp (continuous_finiteScalarFourierReconstruction s (fun q ↦ a q i))).mul
        (Complex.continuous_re.comp (continuous_finiteScalarFourierReconstruction t (fun q ↦ b q i)))
    exact hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  rw [integral_finsetSum Finset.univ (fun i _ ↦ hi i)]
  apply Finset.sum_eq_zero
  intro i _
  apply integral_real_scalar_cross_disjoint s t _ _ hd
  intro x
  simpa only [finiteFourierReconstruction_component] using hr x i

end Mettapedia.FluidDynamics.NavierStokes.PancakeFiniteFourierOrthogonality
