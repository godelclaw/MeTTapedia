import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeMaterialProjectorTangent

/-!
# Localized energy on the physical retained Fourier Hilbert space

The abstract common-domain identity is specialized to the actual finite
Fourier transport and Laplacian matrices. The carrier contains all three
complex components, not just divergence-free fields; the transport operator
acts on this ambient space. Conjugate symmetry of its source supplies its
skew-adjoint identity.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PancakeFiniteLocalizedEvolution

open scoped BigOperators ComplexConjugate RealInnerProductSpace
open Matrix
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakePeriodicComplexStretch
open PancakePeriodicVorticityEquation PancakeBlockReality PancakeSignedTransportEnergy
open PancakeFrequencyProjectorCommutator
open PancakeViscousMisalignmentAbsorption
open PancakeLocalizedQuadraticEnergy PancakeGalerkinKineticEnergy PancakeGalerkinVorticityBridge
open PancakeMaterialProjectorTangent

abbrev FiniteField (modes : Finset Wavevector) := EuclideanSpace ℂ (modes × Fin 3)

def restrictCoefficients (modes : Finset Wavevector) (w : FourierVelocity) : FiniteField modes :=
  WithLp.toLp 2 (fun p ↦ w p.1 p.2)

def extendCoefficients (modes : Finset Wavevector) (v : FiniteField modes) : FourierVelocity :=
  fun q i ↦ if h : q ∈ modes then v (⟨q, h⟩, i) else 0

@[simp] theorem extendCoefficients_mem (modes : Finset Wavevector) (v : FiniteField modes)
    (q : modes) (i : Fin 3) : extendCoefficients modes v q i = v (q, i) := by
  simp [extendCoefficients]

@[simp] theorem restrictCoefficients_apply (modes : Finset Wavevector) (w : FourierVelocity)
    (q : modes) (i : Fin 3) : restrictCoefficients modes w (q, i) = w q i := rfl

theorem restrict_extend (modes : Finset Wavevector) (v : FiniteField modes) :
    restrictCoefficients modes (extendCoefficients modes v) = v := by
  ext p
  exact extendCoefficients_mem modes v p.1 p.2

theorem finiteField_real_inner (modes : Finset Wavevector) (v w : FiniteField modes) :
    ⟪v, w⟫ = (inner ℂ v w).re := by
  simp [PiLp.inner_apply, Complex.inner]

theorem inner_restrictCoefficients (modes : Finset Wavevector) (v w : FourierVelocity) :
    ⟪restrictCoefficients modes v, restrictCoefficients modes w⟫ =
      ∑ q ∈ modes, (coefficientHermitian (v q) (w q)).re := by
  simp [PiLp.inner_apply, restrictCoefficients, Fintype.sum_prod_type,
    coefficientHermitian, Complex.inner, mul_comm, Complex.re_sum]
  exact Finset.sum_attach modes (fun q ↦ ∑ i : Fin 3,
    ((v q i).re * (w q i).re + (v q i).im * (w q i).im))

theorem norm_restrictCoefficients_sq (modes : Finset Wavevector) (w : FourierVelocity) :
    ‖restrictCoefficients modes w‖ ^ 2 = fullEnergy modes w := by
  simp [EuclideanSpace.norm_sq_eq, restrictCoefficients, Fintype.sum_prod_type,
    fullEnergy, coefficientEnergy, Complex.normSq_eq_norm_sq]
  exact Finset.sum_attach modes (fun q ↦ ∑ i : Fin 3, ‖w q i‖ ^ 2)

/-- Matrix of positive advection, the negative of the existing physical
right-hand-side transport matrix, acting identically on vector components. -/
def advectionMatrix (sources modes : Finset Wavevector) (omega : FourierVelocity) :
    Matrix (modes × Fin 3) (modes × Fin 3) ℂ :=
  fun q l ↦ if q.2 = l.2 then -transportMatrix sources omega q.1 l.1 else 0

def advection (sources modes : Finset Wavevector) (omega : FourierVelocity) :
    FiniteField modes →ₗ[ℂ] FiniteField modes := (advectionMatrix sources modes omega).toEuclideanLin

theorem advectionMatrix_skew (sources modes : Finset Wavevector) (omega : FourierVelocity)
    (hs : ∀ k, -k ∈ sources ↔ k ∈ sources)
    (hr : ∀ k, omega (-k) = coefficientConjugate (omega k)) :
    (advectionMatrix sources modes omega).conjTranspose = -advectionMatrix sources modes omega := by
  ext q l
  change conj (if l.2 = q.2 then -transportMatrix sources omega l.1 q.1 else 0) =
    -(if q.2 = l.2 then -transportMatrix sources omega q.1 l.1 else 0)
  by_cases hi : q.2 = l.2
  · rw [if_pos hi, if_pos hi.symm, transportMatrix_skew sources omega hs hr q.1 l.1]
    simp
  · simp [hi, Ne.symm hi]

theorem advection_skew_inner (sources modes : Finset Wavevector) (omega : FourierVelocity)
    (hs : ∀ k, -k ∈ sources ↔ k ∈ sources)
    (hr : ∀ k, omega (-k) = coefficientConjugate (omega k))
    (v w : FiniteField modes) :
    ⟪advection sources modes omega v, w⟫ = -⟪v, advection sources modes omega w⟫ := by
  have ha : (advection sources modes omega).adjoint = -advection sources modes omega := by
    rw [advection, ← Matrix.toEuclideanLin_conjTranspose_eq_adjoint,
      advectionMatrix_skew sources modes omega hs hr, map_neg]
  have h := (advection sources modes omega).adjoint_inner_right v w
  rw [ha] at h
  have he := congrArg Complex.re h
  simpa only [finiteField_real_inner, LinearMap.neg_apply, inner_neg_right, Complex.neg_re] using he.symm

/-- The same physical operator as a real continuous linear map on the
finite coefficient Hilbert space. No additional projection is inserted. -/
def realAdvection (sources modes : Finset Wavevector) (omega : FourierVelocity) :
    FiniteField modes →L[ℝ] FiniteField modes :=
  ((advection sources modes omega).restrictScalars ℝ).toContinuousLinearMap

@[simp] theorem realAdvection_apply (sources modes : Finset Wavevector) (omega : FourierVelocity)
    (v : FiniteField modes) : realAdvection sources modes omega v = advection sources modes omega v := rfl

theorem realAdvection_adjoint (sources modes : Finset Wavevector) (omega : FourierVelocity)
    (hs : ∀ k, -k ∈ sources ↔ k ∈ sources)
    (hr : ∀ k, omega (-k) = coefficientConjugate (omega k)) :
    (realAdvection sources modes omega).adjoint = -realAdvection sources modes omega := by
  symm
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
  intro v w
  simp only [_root_.neg_apply, inner_neg_left, realAdvection_apply]
  change -⟪advection sources modes omega v, w⟫ = ⟪v, advection sources modes omega w⟫
  have h := advection_skew_inner sources modes omega hs hr v w
  linarith

theorem advection_apply (sources modes : Finset Wavevector) (omega : FourierVelocity)
    (v : FiniteField modes) (q : modes) (i : Fin 3) :
    advection sources modes omega v (q, i) =
      -finiteUnitTorusNegativeTransportCoeff sources modes omega (extendCoefficients modes v) q i := by
  classical
  change (∑ l : modes × Fin 3, advectionMatrix sources modes omega (q, i) l * v l) = _
  rw [Fintype.sum_prod_type, finiteTransport_eq_matrix]
  simp only [advectionMatrix, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  simp only [ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true,
    neg_mul, ← Finset.sum_neg_distrib]
  rw [← Finset.sum_coe_sort modes]
  apply Finset.sum_congr rfl
  intro l hl
  rw [extendCoefficients_mem]

/-- The physical Laplacian in the unit-torus normalization. -/
def laplacianMatrix (modes : Finset Wavevector) : Matrix (modes × Fin 3) (modes × Fin 3) ℂ :=
  Matrix.diagonal (fun q ↦ unitTorusDerivativePhase ^ 2 * modeSquare q.1)

def laplacian (modes : Finset Wavevector) : FiniteField modes →ₗ[ℂ] FiniteField modes :=
  (laplacianMatrix modes).toEuclideanLin

theorem laplacian_apply (modes : Finset Wavevector) (v : FiniteField modes)
    (q : modes) (i : Fin 3) :
    laplacian modes v (q, i) = unitTorusViscousVorticityCoeff 1 (extendCoefficients modes v) q i := by
  classical
  change (laplacianMatrix modes *ᵥ WithLp.ofLp v) (q, i) = _
  simp [laplacianMatrix, Matrix.mulVec, dotProduct, Matrix.diagonal_apply,
    unitTorusViscousVorticityCoeff]

theorem laplacianMatrix_selfAdjoint (modes : Finset Wavevector) :
    (laplacianMatrix modes).conjTranspose = laplacianMatrix modes := by
  classical
  simp [laplacianMatrix, Matrix.diagonal_conjTranspose, unitTorusDerivativePhase, modeSquare]

theorem laplacian_symmetric_inner (modes : Finset Wavevector) (v w : FiniteField modes) :
    ⟪laplacian modes v, w⟫ = ⟪v, laplacian modes w⟫ := by
  have ha : (laplacian modes).adjoint = laplacian modes := by
    rw [laplacian, ← Matrix.toEuclideanLin_conjTranspose_eq_adjoint, laplacianMatrix_selfAdjoint]
  have h := (laplacian modes).adjoint_inner_right v w
  rw [ha] at h
  simpa only [finiteField_real_inner] using congrArg Complex.re h.symm

theorem transport_receiver_congr (sources modes : Finset Wavevector)
    (omega eta zeta : FourierVelocity) (q : Wavevector)
    (he : ∀ l ∈ modes, eta l = zeta l) :
    finiteUnitTorusNegativeTransportCoeff sources modes omega eta q =
      finiteUnitTorusNegativeTransportCoeff sources modes omega zeta q := by
  simp only [finiteTransport_eq_matrix]
  apply Finset.sum_congr rfl
  intro l hl
  rw [he l hl]

theorem extend_restrict_mem (modes : Finset Wavevector) (eta : FourierVelocity)
    (q : Wavevector) (hq : q ∈ modes) :
    extendCoefficients modes (restrictCoefficients modes eta) q = eta q := by
  ext i
  simp [extendCoefficients, hq, restrictCoefficients]

theorem advection_restrict (sources modes : Finset Wavevector) (omega eta : FourierVelocity) :
    advection sources modes omega (restrictCoefficients modes eta) =
      -restrictCoefficients modes (finiteUnitTorusNegativeTransportCoeff sources modes omega eta) := by
  ext p
  rw [advection_apply]
  rw [transport_receiver_congr sources modes omega
    (extendCoefficients modes (restrictCoefficients modes eta)) eta p.1 (extend_restrict_mem modes eta)]
  rfl

theorem vorticityRHS_restrict (sources modes : Finset Wavevector) (omega eta : FourierVelocity)
    (nu : ℝ) :
    restrictCoefficients modes (finiteUnitTorusVorticityRHS sources modes omega eta nu) =
      -advection sources modes omega (restrictCoefficients modes eta) +
        restrictCoefficients modes (finiteUnitTorusStretchingCoeff sources modes omega eta) +
        nu • laplacian modes (restrictCoefficients modes eta) := by
  rw [advection_restrict, neg_neg]
  ext p
  change finiteUnitTorusVorticityRHS sources modes omega eta nu p.1 p.2 =
    finiteUnitTorusNegativeTransportCoeff sources modes omega eta p.1 p.2 +
      finiteUnitTorusStretchingCoeff sources modes omega eta p.1 p.2 +
        (nu : ℂ) * laplacian modes (restrictCoefficients modes eta) p
  rw [laplacian_apply]
  simp only [finiteUnitTorusVorticityRHS, finiteUnitTorusNonstretchingCoeff,
    Pi.add_apply, unitTorusViscousVorticityCoeff, Pi.smul_apply, smul_eq_mul,
    extend_restrict_mem modes eta p.1 p.1.property, Complex.ofReal_one, one_mul]
  ring

theorem hasDerivAt_restrictCoefficients (modes : Finset Wavevector)
    (omega : ℝ → FourierVelocity) (omegaDot : FourierVelocity) (t : ℝ)
    (he : ∀ q ∈ modes, ∀ i, HasDerivAt (fun tau ↦ omega tau q i) (omegaDot q i) t) :
    HasDerivAt (fun tau ↦ restrictCoefficients modes (omega tau))
      (restrictCoefficients modes omegaDot) t := by
  have h : HasDerivAt (fun tau (p : modes × Fin 3) ↦ omega tau p.1 p.2)
      (fun p ↦ omegaDot p.1 p.2) t :=
    hasDerivAt_pi.mpr (fun p ↦ he p.1 p.1.property p.2)
  exact (PiLp.continuousLinearEquiv 2 ℝ (fun _ : modes × Fin 3 ↦ ℂ)).symm.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt t h

/-- The moving-localized energy identity on the actual physical velocity
coefficient path. No separate abstract transport or vorticity equation is
assumed. The localizer and projector paths remain explicit inputs. -/
theorem hasDerivAt_sandwichEnergy_of_velocityRHS
    (modes : Finset Wavevector) (u : ℝ → FourierVelocity) (nu t : ℝ)
    (C P : ℝ → FiniteField modes →L[ℝ] FiniteField modes)
    (Cdot Pdot : FiniteField modes →L[ℝ] FiniteField modes)
    (hk : ∀ k ∈ modes, frequencyVec k ≠ 0)
    (hs : ∀ k, -k ∈ modes ↔ k ∈ modes)
    (hr : ∀ k, u t (-k) = coefficientConjugate (u t k))
    (hu : ∀ k ∈ modes, modeDot k (u t k) = 0)
    (he : ∀ q ∈ modes, ∀ i,
      HasDerivAt (fun tau ↦ u tau q i) (velocityRHS modes (u t) nu q i) t)
    (hC : HasDerivAt C Cdot t) (hP : HasDerivAt P Pdot t) (hPs : IsSelfAdjoint (P t)) :
    let omega := fourierCurl (u t)
    let v := fun tau ↦ restrictCoefficients modes (fourierCurl (u tau))
    let A := sandwich (C t) (P t)
    let B := advection modes modes omega
    let D := laplacian modes
    let stretch := restrictCoefficients modes (finiteUnitTorusStretchingCoeff modes modes omega omega)
    HasDerivAt (fun tau ↦ localizedEnergy (sandwich (C tau) (P tau)) (v tau))
      (sandwichMotionRate (C t) Cdot (P t) Pdot (v t) +
        ⟪v t, B (A (v t)) - A (B (v t))⟫ + 2 * ⟪A (v t), stretch⟫ +
        nu * ⟪v t, A (D (v t)) + D (A (v t))⟫) t := by
  dsimp only
  have hv := hasDerivAt_restrictCoefficients modes (fun tau ↦ fourierCurl (u tau))
    (finiteUnitTorusVorticityRHS modes modes (fourierCurl (u t)) (fourierCurl (u t)) nu) t
    (fun q hq i ↦ hasDerivAt_vorticity_of_velocityRHS modes u nu t q hk hu (he q hq) i)
  rw [vorticityRHS_restrict] at hv
  exact hasDerivAt_sandwichEnergy_evolution C P Cdot Pdot
    (fun tau ↦ restrictCoefficients modes (fourierCurl (u tau)))
    (advection modes modes (fourierCurl (u t))) (laplacian modes)
    (restrictCoefficients modes
      (finiteUnitTorusStretchingCoeff modes modes (fourierCurl (u t)) (fourierCurl (u t))))
    nu t Set.univ (Set.mem_univ _) (Set.mem_univ _) hC hP hPs hv
    (fun x _ y _ ↦ advection_skew_inner modes modes (fourierCurl (u t)) hs (fourierCurl_real (u t) hr) x y)
    (fun x _ y _ ↦ laplacian_symmetric_inner modes x y)

/-- Material-rate form of the physical moving-localized energy identity.
The unestimated terms are explicitly `Cdot + [B,C]`, `Pdot + [B,P]`,
physical stretching, and the noncommuting diffusion anticommutator. -/
theorem hasDerivAt_materialEnergy_of_velocityRHS
    (modes : Finset Wavevector) (u : ℝ → FourierVelocity) (nu t : ℝ)
    (C P : ℝ → FiniteField modes →L[ℝ] FiniteField modes)
    (Cdot Pdot : FiniteField modes →L[ℝ] FiniteField modes)
    (hk : ∀ k ∈ modes, frequencyVec k ≠ 0)
    (hs : ∀ k, -k ∈ modes ↔ k ∈ modes)
    (hr : ∀ k, u t (-k) = coefficientConjugate (u t k))
    (hu : ∀ k ∈ modes, modeDot k (u t k) = 0)
    (he : ∀ q ∈ modes, ∀ i,
      HasDerivAt (fun tau ↦ u tau q i) (velocityRHS modes (u t) nu q i) t)
    (hC : HasDerivAt C Cdot t) (hP : HasDerivAt P Pdot t) (hPs : IsSelfAdjoint (P t)) :
    let omega := fourierCurl (u t)
    let v := fun tau ↦ restrictCoefficients modes (fourierCurl (u tau))
    let A := sandwich (C t) (P t)
    let B := advection modes modes omega
    let D := laplacian modes
    let stretch := restrictCoefficients modes (finiteUnitTorusStretchingCoeff modes modes omega omega)
    HasDerivAt (fun tau ↦ localizedEnergy (sandwich (C tau) (P tau)) (v tau))
      (materialMotionRate (C t) Cdot (P t) Pdot B (v t) +
        2 * ⟪A (v t), stretch⟫ + nu * ⟪v t, A (D (v t)) + D (A (v t))⟫) t := by
  have h := hasDerivAt_sandwichEnergy_of_velocityRHS modes u nu t C P Cdot Pdot hk hs hr hu he hC hP hPs
  dsimp only at h ⊢
  rw [sandwichMotionRate_add_transport (C t) Cdot (P t) Pdot
    (advection modes modes (fourierCurl (u t))) (restrictCoefficients modes (fourierCurl (u t)))
    Set.univ (Set.mem_univ _) (Set.mem_univ _) (Set.mem_univ _) (Set.mem_univ _) hPs
    (fun x _ y _ ↦ advection_skew_inner modes modes (fourierCurl (u t)) hs
      (fourierCurl_real (u t) hr) x y)] at h
  exact h

/-- The off-diagonal frame-motion bound uses the actual physical
advection operator. Its squared material rate is the remaining explicit
coherent cost, not an assumed integrable quantity. -/
theorem physical_material_projector_motion_budget
    (sources modes : Finset Wavevector) (omega : FourierVelocity)
    (C Cdot : FiniteField modes →L[ℝ] FiniteField modes)
    (P : ℝ → FiniteField modes →L[ℝ] FiniteField modes)
    (Pdot : FiniteField modes →L[ℝ] FiniteField modes)
    (t : ℝ) (w : FiniteField modes) (rho : ℝ) (hrho : 0 < rho)
    (hs : ∀ k, -k ∈ sources ↔ k ∈ sources)
    (hr : ∀ k, omega (-k) = coefficientConjugate (omega k))
    (hd : HasDerivAt P Pdot t) (hp : ∀ tau, P tau * P tau = P tau)
    (hP : ∀ tau, IsSelfAdjoint (P tau)) :
    let B := realAdvection sources modes omega
    |materialMotionRate C Cdot (P t) Pdot B w -
      2 * ⟪P t (C w), Cdot w + B (C w) - C (B w)⟫| ≤
        rho * ‖(1 - P t) (C w)‖ ^ 2 +
          ‖materialProjectorRate (P t) Pdot B‖ ^ 2 / rho * ‖P t (C w)‖ ^ 2 := by
  exact material_projector_motion_budget C Cdot P Pdot (realAdvection sources modes omega)
    t w rho hrho hd hp hP (realAdvection_adjoint sources modes omega hs hr)

end Mettapedia.FluidDynamics.NavierStokes.PancakeFiniteLocalizedEvolution
