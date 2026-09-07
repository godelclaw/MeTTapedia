import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeBoundaryEnergy

/-!
# Orthogonality for the complete frozen-operator boundary sum

Cross terms between any retained localized field and any exterior localized
field vanish after arbitrary constant real operators. Thus the actual sum
of weighted exterior fields, not merely their separate energies, is an
orthogonal component of the frozen localized field.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PancakeWeightedBoundaryAssembly

open MeasureTheory
open scoped RealInnerProductSpace
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeTransverseEnergyFreezing
open PancakeDyadicDirectionEvolution PancakeFiniteFourierLocalization PancakeRealFourierProjection
open PancakeLocalizedProjectionBoundary PancakeQuadraticFourierSupport
open PancakeQuadraticProjectionLocalization PancakeBoundaryEnergy

local notation "T3" => UnitAddTorus (Fin 3)
local notation "R3" => EuclideanSpace ℝ (Fin 3)

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

theorem integral_operator_cross_boundary_zero (P Q modes : Finset Wavevector)
    (c d : Wavevector → ℂ) (w v : FourierVelocity) (A B : R3 →L[ℝ] R3)
    (hs : ∀ q, -q ∈ modes ↔ q ∈ modes) :
    (∫ x : T3, ⟪A (localizedRetainedField P modes c w x), B (localizedBoundaryField Q modes d v x)⟫) = 0 := by
  have he : ∀ x : T3, ⟪A (localizedRetainedField P modes c w x), B (localizedBoundaryField Q modes d v x)⟫ =
      ⟪(B.adjoint.comp A) (localizedRetainedField P modes c w x), localizedBoundaryField Q modes d v x⟫ :=
    fun x ↦ (B.adjoint_inner_left (localizedBoundaryField Q modes d v x) (A (localizedRetainedField P modes c w x))).symm
  simp only [he]
  exact integral_constant_operator_disjoint_neg_closed modes (finiteCutoffOutputModes Q modes \ modes)
    (finiteCutoffConvolutionCoeff P modes c w) (finiteCutoffConvolutionCoeff Q modes d v) (B.adjoint.comp A)
    (Finset.disjoint_left.mpr (fun q hq ho ↦ (Finset.mem_sdiff.mp ho).2 hq)) hs

def frozenLocalizedField {ι : Type*} [Fintype ι] (c : ι → FourierCoeff (Fin 3))
    (A : ι → R3 →L[ℝ] R3) (modes : Finset Wavevector) (w : FourierVelocity) (x : T3) : R3 :=
  ∑ i : ι, quadraticWeight (c i) x • A i (complexRealPartEuclidean (finiteFourierReconstruction modes w x))

def assembledRetainedField {ι : Type*} [Fintype ι] (c : ι → FourierCoeff (Fin 3))
    (A : ι → R3 →L[ℝ] R3) (modes : Finset Wavevector) (w : FourierVelocity) (x : T3) : R3 :=
  ∑ i : ι, A i (localizedRetainedField (quadraticFourierCoeff (c i)).support modes (quadraticFourierCoeff (c i)) w x)

def assembledBoundaryField {ι : Type*} [Fintype ι] (c : ι → FourierCoeff (Fin 3))
    (A : ι → R3 →L[ℝ] R3) (modes : Finset Wavevector) (w : FourierVelocity) (x : T3) : R3 :=
  ∑ i : ι, A i (quadraticBoundaryField (c i) modes w x)

theorem continuous_frozenLocalizedField {ι : Type*} [Fintype ι] (c : ι → FourierCoeff (Fin 3))
    (A : ι → R3 →L[ℝ] R3) (modes : Finset Wavevector) (w : FourierVelocity) :
    Continuous (frozenLocalizedField c A modes w) :=
  continuous_finsetSum _ (fun i _ ↦ (continuous_quadraticWeight (c i)).smul ((A i).continuous.comp
    (complexRealPartEuclideanCLM.continuous.comp (continuous_finiteFourierReconstruction _ _))))

theorem continuous_assembledRetainedField {ι : Type*} [Fintype ι] (c : ι → FourierCoeff (Fin 3))
    (A : ι → R3 →L[ℝ] R3) (modes : Finset Wavevector) (w : FourierVelocity) :
    Continuous (assembledRetainedField c A modes w) :=
  continuous_finsetSum _ (fun i _ ↦ (A i).continuous.comp
    (continuous_localizedRetainedField (quadraticFourierCoeff (c i)).support modes (quadraticFourierCoeff (c i)) w))

theorem continuous_assembledBoundaryField {ι : Type*} [Fintype ι] (c : ι → FourierCoeff (Fin 3))
    (A : ι → R3 →L[ℝ] R3) (modes : Finset Wavevector) (w : FourierVelocity) :
    Continuous (assembledBoundaryField c A modes w) :=
  continuous_finsetSum _ (fun i _ ↦ (A i).continuous.comp
    (continuous_localizedBoundaryField (quadraticFourierCoeff (c i)).support modes (quadraticFourierCoeff (c i)) w))

theorem frozenLocalizedField_split {ι : Type*} [Fintype ι] (c : ι → FourierCoeff (Fin 3))
    (A : ι → R3 →L[ℝ] R3) (modes : Finset Wavevector) (w : FourierVelocity) (x : T3) :
    frozenLocalizedField c A modes w x = assembledRetainedField c A modes w x + assembledBoundaryField c A modes w x := by
  unfold frozenLocalizedField assembledRetainedField assembledBoundaryField
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  have h := real_localized_split (quadraticFourierCoeff (c i)).support modes (quadraticFourierCoeff (c i)) w x
    (by rw [scalarReconstruction_quadratic]; rfl)
  rw [scalarReconstruction_quadratic] at h
  simpa only [map_smul, map_add, Complex.ofReal_re, localizedRetainedField, quadraticBoundaryField]
    using congrArg (A i) h

theorem integral_assembled_inner_zero {ι : Type*} [Fintype ι] (c : ι → FourierCoeff (Fin 3))
    (A : ι → R3 →L[ℝ] R3) (modes : Finset Wavevector) (w : FourierVelocity)
    (hs : ∀ q, -q ∈ modes ↔ q ∈ modes) :
    (∫ x : T3, ⟪assembledRetainedField c A modes w x, assembledBoundaryField c A modes w x⟫) = 0 := by
  let F := fun (i j : ι) (x : T3) ↦
    ⟪A i (localizedRetainedField (quadraticFourierCoeff (c i)).support modes (quadraticFourierCoeff (c i)) w x),
      A j (quadraticBoundaryField (c j) modes w x)⟫
  have hi : ∀ i j, Integrable (F i j) := by
    intro i j
    have hc : Continuous (F i j) :=
      ((A i).continuous.comp (continuous_localizedRetainedField (quadraticFourierCoeff (c i)).support modes
        (quadraticFourierCoeff (c i)) w)).inner
      ((A j).continuous.comp (continuous_localizedBoundaryField (quadraticFourierCoeff (c j)).support modes
        (quadraticFourierCoeff (c j)) w))
    exact hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  simp only [assembledRetainedField, assembledBoundaryField, sum_inner, inner_sum]
  change (∫ x : T3, ∑ j : ι, ∑ i : ι, F i j x) = 0
  have he : (fun x : T3 ↦ ∑ j : ι, ∑ i : ι, F i j x) =
      (fun x : T3 ↦ ∑ i : ι, ∑ j : ι, F i j x) := by
    funext x
    exact Finset.sum_comm
  rw [he, integral_finsetSum Finset.univ (fun i _ ↦ integrable_finsetSum Finset.univ (fun j _ ↦ hi i j))]
  apply Finset.sum_eq_zero
  intro i _
  rw [integral_finsetSum Finset.univ (fun j _ ↦ hi i j)]
  apply Finset.sum_eq_zero
  intro j _
  exact integral_operator_cross_boundary_zero (quadraticFourierCoeff (c i)).support (quadraticFourierCoeff (c j)).support
    modes (quadraticFourierCoeff (c i)) (quadraticFourierCoeff (c j)) w w (A i) (A j) hs

theorem integral_assembled_energy_split {ι : Type*} [Fintype ι] (c : ι → FourierCoeff (Fin 3))
    (A : ι → R3 →L[ℝ] R3) (modes : Finset Wavevector) (w : FourierVelocity)
    (hs : ∀ q, -q ∈ modes ↔ q ∈ modes) :
    (∫ x : T3, ‖frozenLocalizedField c A modes w x‖ ^ 2) =
      (∫ x : T3, ‖assembledRetainedField c A modes w x‖ ^ 2) +
      ∫ x : T3, ‖assembledBoundaryField c A modes w x‖ ^ 2 := by
  have hR := continuous_assembledRetainedField c A modes w
  have hB := continuous_assembledBoundaryField c A modes w
  have hIc : Continuous (fun x : T3 ↦ ⟪assembledRetainedField c A modes w x, assembledBoundaryField c A modes w x⟫) := hR.inner hB
  have hRs := (hR.norm.pow 2).integrable_of_hasCompactSupport (μ := volume) (HasCompactSupport.of_compactSpace _)
  have hBs := (hB.norm.pow 2).integrable_of_hasCompactSupport (μ := volume) (HasCompactSupport.of_compactSpace _)
  have hI := hIc.integrable_of_hasCompactSupport (μ := volume) (HasCompactSupport.of_compactSpace _)
  have hRI : Integrable (fun x : T3 ↦ ‖assembledRetainedField c A modes w x‖ ^ 2 +
      2 * ⟪assembledRetainedField c A modes w x, assembledBoundaryField c A modes w x⟫) := hRs.add (hI.const_mul 2)
  simp only [frozenLocalizedField_split, norm_add_sq_real]
  rw [integral_add hRI hBs, integral_add hRs (hI.const_mul 2), integral_const_mul,
    integral_assembled_inner_zero c A modes w hs, mul_zero, add_zero]

theorem integral_assembled_boundary_energy_le {ι : Type*} [Fintype ι] (c : ι → FourierCoeff (Fin 3))
    (A : ι → R3 →L[ℝ] R3) (modes : Finset Wavevector) (w : FourierVelocity)
    (hs : ∀ q, -q ∈ modes ↔ q ∈ modes) :
    (∫ x : T3, ‖assembledBoundaryField c A modes w x‖ ^ 2) ≤
      ∫ x : T3, ‖frozenLocalizedField c A modes w x‖ ^ 2 := by
  rw [integral_assembled_energy_split c A modes w hs]
  exact le_add_of_nonneg_left (integral_nonneg (fun _ ↦ sq_nonneg _))

end Mettapedia.FluidDynamics.NavierStokes.PancakeWeightedBoundaryAssembly
