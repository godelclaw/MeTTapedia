import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeDyadicDirectionEvolution
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeComplexMisalignmentExpansion
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeFiniteFourierLocalization

/-!
# Collected Fourier stretching coefficients for the dyadic direction law

The exact complex stretching interaction was already summed as a physical
finite Fourier polynomial indexed by source/receiver pairs.  The dyadic
direction law, however, consumes a coefficient field indexed by the output
frequency.  This module collects the pair sum over fibers of
`source + receiver`, and proves that reconstructing the collected coefficients
is exactly the original stretching polynomial.

This supplies the canonical proposed-stretching field in the two-channel
direction residual.  The remaining equation term is then
`omegaDot - stretchingCoeff`, while the second term is the difference between
projecting these stretching coefficients and stretching the projected block.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes
namespace PancakeFourierStretchingEvolution

open scoped BigOperators RealInnerProductSpace
open PeriodicFourierTriad
open PancakePeriodicCoherentSplit
open PancakeComplexMisalignmentExpansion
open PancakeFiniteFourierLocalization
open PancakeArbitraryDataBlocks
open PancakeFrameCovariance
open PancakeBilinearPeriodization
open PancakeDyadicDirectionEvolution
open DirectionEvolutionTilting

local notation "R3" => EuclideanSpace ℝ (Fin 3)

/-- Fourier coefficient obtained by collecting every retained stretching
interaction whose input frequencies add to `q`. -/
def finiteComplexStretchingConvolutionCoeff
    (sourceModes receiverModes : Finset Wavevector)
    (omega eta : FourierVelocity) (q : Wavevector) : VelocityCoefficient :=
  ∑ sr ∈ sourceModes ×ˢ receiverModes with sr.1 + sr.2 = q,
    PancakePeriodicComplexStretch.complexStretchAmp sr.1
      (omega sr.1) (eta sr.2)

/-- Collecting equal output frequencies and then reconstructing gives exactly
the pair-indexed finite complex stretching polynomial. -/
theorem finiteFourierReconstruction_stretchingConvolutionCoeff
    (sourceModes receiverModes : Finset Wavevector)
    (omega eta : FourierVelocity) :
    finiteFourierReconstruction
        (finiteCutoffOutputModes sourceModes receiverModes)
        (finiteComplexStretchingConvolutionCoeff
          sourceModes receiverModes omega eta) =
      finiteComplexStretchingSum sourceModes receiverModes omega eta := by
  classical
  funext x
  let pairs := sourceModes ×ˢ receiverModes
  let output := finiteCutoffOutputModes sourceModes receiverModes
  let addPair : Wavevector × Wavevector → Wavevector :=
    fun sr ↦ sr.1 + sr.2
  have hmaps : ∀ sr ∈ pairs, addPair sr ∈ output := by
    intro sr hsr
    rcases Finset.mem_product.mp hsr with ⟨hsource, hreceiver⟩
    exact (mem_finiteCutoffOutputModes_iff
      sourceModes receiverModes (addPair sr)).mpr
        ⟨sr.1, hsource, sr.2, hreceiver, rfl⟩
  change
    (∑ q ∈ output,
      UnitAddTorus.mFourier q x •
        ∑ sr ∈ pairs with addPair sr = q,
          PancakePeriodicComplexStretch.complexStretchAmp sr.1
            (omega sr.1) (eta sr.2)) =
      ∑ source ∈ sourceModes, ∑ receiver ∈ receiverModes,
        interactionPhase source receiver x •
          PancakePeriodicComplexStretch.complexStretchAmp source
            (omega source) (eta receiver)
  calc
    _ = ∑ q ∈ output, ∑ sr ∈ pairs with addPair sr = q,
        UnitAddTorus.mFourier (addPair sr) x •
          PancakePeriodicComplexStretch.complexStretchAmp sr.1
            (omega sr.1) (eta sr.2) := by
      apply Finset.sum_congr rfl
      intro q hq
      rw [Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro sr hsr
      have hadd : addPair sr = q := (Finset.mem_filter.mp hsr).2
      rw [hadd]
    _ = ∑ sr ∈ pairs,
        UnitAddTorus.mFourier (addPair sr) x •
          PancakePeriodicComplexStretch.complexStretchAmp sr.1
            (omega sr.1) (eta sr.2) := by
      exact Finset.sum_fiberwise_of_maps_to hmaps
        (fun sr : Wavevector × Wavevector ↦
          (UnitAddTorus.mFourier (addPair sr) x •
            PancakePeriodicComplexStretch.complexStretchAmp sr.1
              (omega sr.1) (eta sr.2) : VelocityCoefficient))
    _ = _ := by
      rw [Finset.sum_product]
      apply Finset.sum_congr rfl
      intro source hsource
      apply Finset.sum_congr rfl
      intro receiver hreceiver
      rw [UnitAddTorus.mFourier_add]
      rfl

/-- Exact two-channel residual after choosing the collected finite stretching
coefficients as the proposed stretching field. -/
theorem dyadicPancakeDirectionResidual_eq_finiteStretchingEvolution_add_projectionDefect
    (S : R3 →L[ℝ] R3) (F : OrientedFrameEquiv) (N : ℕ)
    (sourceModes receiverModes : Finset Wavevector)
    (omega eta omegaDot : FourierVelocity) (r : ℝ) (xi : R3)
    (x : BilinearSpatialTorus) :
    dyadicPancakeDirectionResidual S F N omegaDot r xi x =
      dyadicPancakeEvolutionRemainder F N omegaDot
          (finiteComplexStretchingConvolutionCoeff
            sourceModes receiverModes omega eta) x +
        dyadicPancakeStretchingProjectionDefect S F N
          (finiteComplexStretchingConvolutionCoeff
            sourceModes receiverModes omega eta) r xi x := by
  exact
    dyadicPancakeDirectionResidual_eq_evolutionRemainder_add_projectionDefect
      S F N omegaDot
        (finiteComplexStretchingConvolutionCoeff
          sourceModes receiverModes omega eta) r xi x

/-- Direction evolution of the actual hard block with the full finite
stretching convolution selected as its stretching channel. -/
theorem dyadicPancakeDirectionDerivative_eq_finiteStretchingChannels
    (S : R3 →L[ℝ] R3) (F : OrientedFrameEquiv) (N : ℕ)
    (sourceModes receiverModes : Finset Wavevector)
    {omegaPath : ℝ → FourierVelocity}
    (omega eta omegaDot : FourierVelocity) (x : BilinearSpatialTorus)
    {r : ℝ → ℝ} {xi : ℝ → R3}
    {xiDot : R3} {radialRate t : ℝ}
    (hcoeff : ∀ k ∈ squareDyadicPancakeModes F N, ∀ i,
      HasDerivAt (fun τ ↦ omegaPath τ k i) (omegaDot k i) t)
    (hr : HasDerivAt r radialRate t)
    (hxi : HasDerivAt xi xiDot t)
    (hfactor :
      (fun τ ↦ squareDyadicPancakeRealBlock F N (omegaPath τ) x) =
        fun τ ↦ r τ • xi τ)
    (hunit : ∀ τ, ⟪xi τ, xi τ⟫ = 1)
    (hrne : r t ≠ 0) :
    xiDot = transverseComponent (xi t) (S (xi t)) +
      (r t)⁻¹ • transverseComponent (xi t)
        (dyadicPancakeEvolutionRemainder F N omegaDot
          (finiteComplexStretchingConvolutionCoeff
            sourceModes receiverModes omega eta) x) +
      (r t)⁻¹ • transverseComponent (xi t)
        (dyadicPancakeStretchingProjectionDefect S F N
          (finiteComplexStretchingConvolutionCoeff
            sourceModes receiverModes omega eta)
          (r t) (xi t) x) := by
  exact
    dyadicPancakeDirectionDerivative_eq_strain_add_evolutionRemainder_add_projectionDefect
      S F N omegaDot
        (finiteComplexStretchingConvolutionCoeff
          sourceModes receiverModes omega eta)
      x hcoeff hr hxi hfactor hunit hrne

end PancakeFourierStretchingEvolution
end NavierStokes
end FluidDynamics
end Mettapedia

