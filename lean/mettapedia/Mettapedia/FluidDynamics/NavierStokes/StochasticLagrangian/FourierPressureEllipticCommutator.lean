import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PressureTiltEllipticIdentity
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.FourierProductEnergy

/-!
# The pressure commutator as elliptic product errors

The exact decomposition uses the real-symmetrized pressure potential.
It retains mixed first derivatives and cutoff second derivatives, even
when the convolution output is zero. No coefficient-count estimate is
used to obtain the identity.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.FourierPressureEllipticCommutator

open scoped BigOperators ComplexConjugate RealInnerProductSpace
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeFrequencyProjectorCommutator
open PancakeFiniteFourierLocalization PancakeAnisotropyDepletion
open FourierPressureCommutator FourierPressureTraceSymbol FourierPressureLocalization PressureTiltSymbol
open FourierPressureTiltEnergy PancakeQuadraticFourierSupport
open PressureTiltEllipticIdentity Mettapedia.Analysis.FiniteMultiplierLocalization

local notation "R3" => EuclideanSpace ℝ (Fin 3)
local notation "C3" => EuclideanSpace ℂ (Fin 3)

def potentialAmplitude (chi : Wavevector → ℂ) (u : FourierVelocity) (q : Wavevector) : ℂ :=
  (pressureAmplitude chi u q + conj (pressureAmplitude chi u (-q))) / 2

theorem realTraceAmplitude_eq (chi : Wavevector → ℂ) (u : FourierVelocity) (q : Wavevector) :
    realTraceAmplitude chi u q = potentialAmplitude chi u q * (‖realFrequency q‖ ^ 2 : ℝ) := by
  simp only [realTraceAmplitude, traceAmplitude, potentialAmplitude, realFrequency_neg,
    norm_neg, map_mul, Complex.conj_ofReal]
  ring

theorem complexifyVector_add (v w : R3) : complexifyVector (v + w) = complexifyVector v + complexifyVector w := by
  ext i
  simp [complexifyVector, coefficientVec]

theorem complexifyVector_smul (r : ℝ) (v : R3) :
    complexifyVector (r • v) = (r : ℂ) • complexifyVector v := by
  ext i
  simp [complexifyVector, coefficientVec]

def ellipticScalarKernel (p k : Wavevector) : ℝ :=
  2 * ⟪realFrequency p, realFrequency k⟫ + ‖realFrequency p‖ ^ 2

def ellipticVectorKernel (e : R3) (p k : Wavevector) : R3 :=
  ⟪realFrequency k, e⟫ • lineRemainder e (realFrequency p) +
    ⟪realFrequency p, e⟫ • lineRemainder e (realFrequency k) +
    ⟪realFrequency p, e⟫ • lineRemainder e (realFrequency p)

theorem trace_mul_symbol_difference (chi : Wavevector → ℂ) (u : FourierVelocity)
    (e : R3) (p k : Wavevector) :
    realTraceAmplitude chi u k • (complexTiltSymbol e k - complexTiltSymbol e (p + k)) =
      potentialAmplitude chi u k •
        ((ellipticScalarKernel p k : ℂ) • complexTiltSymbol e (p + k) -
          complexifyVector (ellipticVectorKernel e p k)) := by
  have h := congrArg complexifyVector
    (norm_sq_smul_tiltSymbol_sub e (realFrequency p) (realFrequency k))
  simp only [complexifyVector_sub, complexifyVector_smul, ← realFrequency_add] at h
  rw [realTraceAmplitude_eq, mul_smul]
  congr 1

def ellipticScalarCoefficient (P K : Finset Wavevector) (c phi : Wavevector → ℂ)
    (q : Wavevector) : ℂ :=
  ∑ pk ∈ P ×ˢ K with pk.1 + pk.2 = q, c pk.1 * phi pk.2 * (ellipticScalarKernel pk.1 pk.2 : ℝ)

def ellipticVectorCoefficient (P K : Finset Wavevector) (c phi : Wavevector → ℂ)
    (e : R3) (q : Wavevector) : C3 :=
  ∑ pk ∈ P ×ˢ K with pk.1 + pk.2 = q,
    (c pk.1 * phi pk.2) • complexifyVector (ellipticVectorKernel e pk.1 pk.2)

theorem commutatorCoefficient_eq (P K : Finset Wavevector) (c : Wavevector → ℂ)
    (chi : Wavevector → ℂ) (u : FourierVelocity) (e : R3) (q : Wavevector) :
    commutatorCoefficient P K c (realTraceAmplitude chi u) (complexTiltSymbol e) q =
      ellipticScalarCoefficient P K c (potentialAmplitude chi u) q • complexTiltSymbol e q -
        ellipticVectorCoefficient P K c (potentialAmplitude chi u) e q := by
  unfold commutatorCoefficient ellipticScalarCoefficient ellipticVectorCoefficient
  rw [Finset.sum_smul, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro pk hpk
  rw [mul_smul, trace_mul_symbol_difference, smul_sub, smul_smul, mul_smul]
  rw [(Finset.mem_filter.mp hpk).2]
  module

theorem tiltCommutatorEnergy_le_elliptic_products (c : FourierCoeff (Fin 3))
    (chi : Wavevector → ℂ) (K : Finset Wavevector) (u : FourierVelocity)
    (e : R3) (he : ‖e‖ = 1) :
    tiltCommutatorEnergy c chi K u e ≤
      2 * scalarEnergy (finiteCutoffOutputModes c.support K)
        (ellipticScalarCoefficient c.support K c (potentialAmplitude chi u)) +
      2 * vectorEnergy (finiteCutoffOutputModes c.support K)
        (ellipticVectorCoefficient c.support K c (potentialAmplitude chi u) e) := by
  unfold tiltCommutatorEnergy scalarEnergy vectorEnergy
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro q _
  rw [commutatorCoefficient_eq]
  have hm : ‖complexTiltSymbol e q‖ ≤ 1 := by
    rw [complexTiltSymbol, norm_complexifyVector]
    exact norm_tiltSymbol_le_one e _ he
  have hmul := mul_le_mul_of_nonneg_left hm
    (norm_nonneg (ellipticScalarCoefficient c.support K c (potentialAmplitude chi u) q))
  have hn := norm_sub_le
    (ellipticScalarCoefficient c.support K c (potentialAmplitude chi u) q • complexTiltSymbol e q)
    (ellipticVectorCoefficient c.support K c (potentialAmplitude chi u) e q)
  rw [norm_smul] at hn
  simp only [mul_one] at hmul
  have hs := pow_le_pow_left₀ (norm_nonneg _) (hn.trans (add_le_add hmul le_rfl)) 2
  nlinarith only [hs,
    sq_nonneg (‖ellipticScalarCoefficient c.support K c (potentialAmplitude chi u) q‖ -
      ‖ellipticVectorCoefficient c.support K c (potentialAmplitude chi u) e q‖)]

end Mettapedia.FluidDynamics.NavierStokes.FourierPressureEllipticCommutator
