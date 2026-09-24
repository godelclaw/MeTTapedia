import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.FiniteCutoffAlgebra

/-!
# Exact localization of both pressure inputs

The output is multiplied by both cutoffs, and the two inputs by one cutoff
each. The difference telescopes into two one-input commutators. In the second
commutator the original second input is shifted, while the already localized
first input is only the receiver. No zero-mean or divergence-free property is
asserted for either localized field.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PressureTwoInputLocalization

open scoped BigOperators
open PeriodicFourierTriad PancakeFiniteFourierLocalization PancakeFrequencyProjectorCommutator
open ComplexPressureConvolution PressureBilinearLocalization FiniteCutoffAlgebra
open Mettapedia.Analysis.FiniteMultiplierLocalization

local notation "R3" => EuclideanSpace ℝ (Fin 3)
local notation "C3" => EuclideanSpace ℂ (Fin 3)

def doublyLocalizedOutput (e : R3) (A D P K : Finset Wavevector)
    (c d : Wavevector → ℂ) (w v : FourierVelocity) : Wavevector → C3 :=
  vectorConvolution A (finiteCutoffOutputModes D (finiteCutoffOutputModes P K)) c
    (localizedOutput e D P K d w v)

def localizedInputs (e : R3) (A D P K : Finset Wavevector)
    (c d : Wavevector → ℂ) (w v : FourierVelocity) : Wavevector → C3 :=
  pairConvolution e (finiteCutoffOutputModes D P) (finiteCutoffOutputModes A K)
    (finiteCutoffConvolutionCoeff D P d w) (finiteCutoffConvolutionCoeff A K c v)

def twoInputCommutator (e : R3) (A D P K : Finset Wavevector)
    (c d : Wavevector → ℂ) (w v : FourierVelocity) (q : Wavevector) : C3 :=
  vectorConvolution A (finiteCutoffOutputModes D (finiteCutoffOutputModes P K)) c
      (PressureBilinearLocalization.commutatorCoefficient e D P K d w v) q +
    PressureBilinearLocalization.commutatorCoefficient e A K (finiteCutoffOutputModes D P)
      c v (finiteCutoffConvolutionCoeff D P d w) q

theorem doublyLocalizedOutput_sub_localizedInputs (e : R3) (A D P K : Finset Wavevector)
    (c d : Wavevector → ℂ) (w v : FourierVelocity) (q : Wavevector) :
    doublyLocalizedOutput e A D P K c d w v q - localizedInputs e A D P K c d w v q =
      twoInputCommutator e A D P K c d w v q := by
  have hd : localizedOutput e D P K d w v - localizedSource e D P K d w v =
      PressureBilinearLocalization.commutatorCoefficient e D P K d w v :=
    funext (localizedOutput_sub_localizedSource e D P K d w v)
  have hs : localizedOutput e A K (finiteCutoffOutputModes D P) c v
        (finiteCutoffConvolutionCoeff D P d w) =
      vectorConvolution A (finiteCutoffOutputModes D (finiteCutoffOutputModes P K)) c
        (localizedSource e D P K d w v) := by
    unfold localizedOutput localizedSource
    rw [finiteCutoffOutputModes_comm K, finiteCutoffOutputModes_assoc]
    congr 1
    funext r
    exact pairConvolution_swap e K (finiteCutoffOutputModes D P) v _ r
  have hb : localizedSource e A K (finiteCutoffOutputModes D P) c v
        (finiteCutoffConvolutionCoeff D P d w) q = localizedInputs e A D P K c d w v q :=
    pairConvolution_swap e (finiteCutoffOutputModes A K) (finiteCutoffOutputModes D P) _ _ q
  rw [twoInputCommutator, ← hd, vectorConvolution_sub,
    ← localizedOutput_sub_localizedSource e A K (finiteCutoffOutputModes D P), hs, hb]
  unfold doublyLocalizedOutput
  abel

end Mettapedia.FluidDynamics.NavierStokes.PressureTwoInputLocalization
