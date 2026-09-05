import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeBlockReality

/-!
# Material transport and the hard pancake projector

At a fixed spatial point, the differentiated pancake block contains the full
projected transport term.  Along a fluid trajectory, differentiation of the
observation point adds `(u · grad)(P_B omega)`.  The two bulk transport terms
cancel except when an interaction moves its receiver frequency across the
boundary of the hard mode set `B`.

This file proves that cancellation at the exact finite Fourier coefficient
level.  It identifies the material transport commutator with incoming pairs
when the output lies in `B`, and with minus the outgoing pairs when the output
lies outside `B`.  The remaining analytic task is to estimate this boundary
transfer, not the unprojected advection term.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes
namespace PancakeMaterialTransportCommutator

open scoped BigOperators
open PeriodicFourierTriad
open PancakePeriodicComplexStretch
open PancakePeriodicVorticityEquation

/-- Receiver modes inside the hard output block. -/
def receiverModesInside
    (receiverModes blockModes : Finset Wavevector) : Finset Wavevector :=
  receiverModes.filter fun k ↦ k ∈ blockModes

/-- Receiver modes outside the hard output block. -/
def receiverModesOutside
    (receiverModes blockModes : Finset Wavevector) : Finset Wavevector :=
  receiverModes.filter fun k ↦ k ∉ blockModes

/-- The collected transport coefficient written as the equivalent ordered
double sum. -/
theorem finiteUnitTorusNegativeTransportCoeff_eq_doubleSum
    (sourceModes receiverModes : Finset Wavevector)
    (omega eta : FourierVelocity) (q : Wavevector) :
    finiteUnitTorusNegativeTransportCoeff
        sourceModes receiverModes omega eta q =
      ∑ source ∈ sourceModes, ∑ receiver ∈ receiverModes,
        if source + receiver = q then
          unitTorusNegativeTransportAmp source receiver
            (omega source) (eta receiver)
        else 0 := by
  classical
  unfold finiteUnitTorusNegativeTransportCoeff
  rw [Finset.sum_filter, Finset.sum_product]

/-- The full receiver convolution splits exactly into inside and outside
receiver frequencies. -/
theorem finiteUnitTorusNegativeTransportCoeff_eq_inside_add_outside
    (sourceModes receiverModes blockModes : Finset Wavevector)
    (omega eta : FourierVelocity) (q : Wavevector) :
    finiteUnitTorusNegativeTransportCoeff
        sourceModes receiverModes omega eta q =
      finiteUnitTorusNegativeTransportCoeff sourceModes
          (receiverModesInside receiverModes blockModes) omega eta q +
        finiteUnitTorusNegativeTransportCoeff sourceModes
          (receiverModesOutside receiverModes blockModes) omega eta q := by
  classical
  rw [finiteUnitTorusNegativeTransportCoeff_eq_doubleSum,
    finiteUnitTorusNegativeTransportCoeff_eq_doubleSum,
    finiteUnitTorusNegativeTransportCoeff_eq_doubleSum,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro source hsource
  rw [receiverModesInside, receiverModesOutside,
    ← Finset.sum_filter_add_sum_filter_not receiverModes
      (fun receiver ↦ receiver ∈ blockModes)]

/-- Fourier coefficient of
`P_B[-(u · grad) eta] + (u · grad)(P_B eta)`.

The second term is the negative of the right-hand-side transport symbol on
receivers already in `B`. -/
def finiteMaterialTransportCommutatorCoeff
    (sourceModes receiverModes blockModes : Finset Wavevector)
    (omega eta : FourierVelocity) (q : Wavevector) : VelocityCoefficient :=
  (if q ∈ blockModes then
      finiteUnitTorusNegativeTransportCoeff
        sourceModes receiverModes omega eta q
    else 0) -
  finiteUnitTorusNegativeTransportCoeff sourceModes
    (receiverModesInside receiverModes blockModes) omega eta q

/-- Inside the hard block, only interactions arriving from receiver
frequencies outside the block survive material transport cancellation. -/
theorem finiteMaterialTransportCommutatorCoeff_eq_incoming
    (sourceModes receiverModes blockModes : Finset Wavevector)
    (omega eta : FourierVelocity) {q : Wavevector}
    (hq : q ∈ blockModes) :
    finiteMaterialTransportCommutatorCoeff
        sourceModes receiverModes blockModes omega eta q =
      finiteUnitTorusNegativeTransportCoeff sourceModes
        (receiverModesOutside receiverModes blockModes) omega eta q := by
  unfold finiteMaterialTransportCommutatorCoeff
  rw [if_pos hq,
    finiteUnitTorusNegativeTransportCoeff_eq_inside_add_outside
      sourceModes receiverModes blockModes omega eta q]
  abel

/-- Outside the hard block, the commutator is minus the interactions leaving
from receiver frequencies inside the block. -/
theorem finiteMaterialTransportCommutatorCoeff_eq_neg_outgoing
    (sourceModes receiverModes blockModes : Finset Wavevector)
    (omega eta : FourierVelocity) {q : Wavevector}
    (hq : q ∉ blockModes) :
    finiteMaterialTransportCommutatorCoeff
        sourceModes receiverModes blockModes omega eta q =
      -finiteUnitTorusNegativeTransportCoeff sourceModes
        (receiverModesInside receiverModes blockModes) omega eta q := by
  simp [finiteMaterialTransportCommutatorCoeff, hq]

/-- Pointwise two-sided boundary-transfer description of the material
transport commutator. -/
theorem finiteMaterialTransportCommutatorCoeff_eq_boundaryCrossing
    (sourceModes receiverModes blockModes : Finset Wavevector)
    (omega eta : FourierVelocity) (q : Wavevector) :
    finiteMaterialTransportCommutatorCoeff
        sourceModes receiverModes blockModes omega eta q =
      if q ∈ blockModes then
        finiteUnitTorusNegativeTransportCoeff sourceModes
          (receiverModesOutside receiverModes blockModes) omega eta q
      else
        -finiteUnitTorusNegativeTransportCoeff sourceModes
          (receiverModesInside receiverModes blockModes) omega eta q := by
  by_cases hq : q ∈ blockModes
  · rw [if_pos hq]
    exact finiteMaterialTransportCommutatorCoeff_eq_incoming
      sourceModes receiverModes blockModes omega eta hq
  · rw [if_neg hq]
    exact finiteMaterialTransportCommutatorCoeff_eq_neg_outgoing
      sourceModes receiverModes blockModes omega eta hq

end PancakeMaterialTransportCommutator
end NavierStokes
end FluidDynamics
end Mettapedia
