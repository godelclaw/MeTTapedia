import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeStrainAxialFrame
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakePeriodicComplexStretch

/-!
# Exact coherent/misaligned expansion of complex Fourier stretching

The coefficient split into coherent and misaligned parts is already exact.
This module pushes that split through the actual complex-bilinear
Biot--Savart stretching symbol.  Each source/receiver interaction becomes a
coherent--coherent term and exactly three terms carrying at least one
misalignment factor.

The equality is then summed over arbitrary finite source and receiver mode
sets, including the torus Fourier phases.  The resulting norm inequality is
the concrete finite-Fourier form of the abstract `split_le` field in
`CoherentMisalignmentSplitData`.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes
namespace PancakeComplexMisalignmentExpansion

open scoped BigOperators
open PeriodicFourierTriad
open PancakePeriodicCoherentSplit
open PancakePeriodicComplexStretch

/-- The complex Biot--Savart symbol is additive in its vorticity amplitude. -/
theorem complexBiotSavartAmp_add (k : Wavevector)
    (u v : VelocityCoefficient) :
    complexBiotSavartAmp k (u + v) =
      complexBiotSavartAmp k u + complexBiotSavartAmp k v := by
  ext i
  fin_cases i <;>
    simp [complexBiotSavartAmp, coefficientCross,
      wavevectorCoefficient, Pi.add_apply] <;> ring

/-- Additivity of stretching in the source-vorticity amplitude. -/
theorem complexStretchAmp_add_source (k : Wavevector)
    (u₁ u₂ v : VelocityCoefficient) :
    complexStretchAmp k (u₁ + u₂) v =
      complexStretchAmp k u₁ v + complexStretchAmp k u₂ v := by
  ext i
  fin_cases i <;>
    simp [complexStretchAmp, complexBiotSavartAmp_add,
      coefficientDot, modeDot, Pi.add_apply, Fin.sum_univ_three] <;> ring

/-- Additivity of stretching in the receiver-vorticity amplitude. -/
theorem complexStretchAmp_add_receiver (k : Wavevector)
    (u v₁ v₂ : VelocityCoefficient) :
    complexStretchAmp k u (v₁ + v₂) =
      complexStretchAmp k u v₁ + complexStretchAmp k u v₂ := by
  ext i
  fin_cases i <;>
    simp [complexStretchAmp, coefficientDot, modeDot,
      Pi.add_apply, Fin.sum_univ_three] <;> ring

theorem complexStretchAmp_zero_source (k : Wavevector)
    (v : VelocityCoefficient) :
    complexStretchAmp k 0 v = 0 := by
  have h := complexStretchAmp_add_source k 0 0 v
  simpa using h

theorem complexStretchAmp_zero_receiver (k : Wavevector)
    (u : VelocityCoefficient) :
    complexStretchAmp k u 0 = 0 := by
  have h := complexStretchAmp_add_receiver k u 0 0
  simpa using h

/-- The part of one interaction carrying no misalignment factor. -/
def coherentCoherentStretchAmp (source receiver : Wavevector)
    (u v : VelocityCoefficient) : VelocityCoefficient :=
  complexStretchAmp source
    (coherentComponent source u) (coherentComponent receiver v)

/-- The sum of the three parts of one interaction carrying at least one
misalignment factor. -/
def misalignmentStretchAmp (source receiver : Wavevector)
    (u v : VelocityCoefficient) : VelocityCoefficient :=
  complexStretchAmp source
      (coherentComponent source u) (misalignmentComponent receiver v) +
    complexStretchAmp source
      (misalignmentComponent source u) (coherentComponent receiver v) +
    complexStretchAmp source
      (misalignmentComponent source u) (misalignmentComponent receiver v)

/-- **Exact four-term coherent/misaligned interaction expansion.** -/
theorem complexStretchAmp_eq_coherent_add_misalignment
    (source receiver : Wavevector) (u v : VelocityCoefficient) :
    complexStretchAmp source u v =
      coherentCoherentStretchAmp source receiver u v +
        misalignmentStretchAmp source receiver u v := by
  calc
    complexStretchAmp source u v =
        complexStretchAmp source
          (coherentComponent source u + misalignmentComponent source u)
          (coherentComponent receiver v +
            misalignmentComponent receiver v) := by
      rw [coherentComponent_add_misalignmentComponent,
        coherentComponent_add_misalignmentComponent]
    _ = coherentCoherentStretchAmp source receiver u v +
        misalignmentStretchAmp source receiver u v := by
      rw [complexStretchAmp_add_source,
        complexStretchAmp_add_receiver,
        complexStretchAmp_add_receiver]
      unfold coherentCoherentStretchAmp misalignmentStretchAmp
      abel

/-- Torus phase of one bilinear source/receiver interaction. -/
def interactionPhase (source receiver : Wavevector)
    (x : UnitAddTorus (Fin 3)) : ℂ :=
  UnitAddTorus.mFourier source x * UnitAddTorus.mFourier receiver x

/-- Full finite complex stretching sum. -/
def finiteComplexStretchingSum
    (sourceModes receiverModes : Finset Wavevector)
    (omega eta : FourierVelocity) (x : UnitAddTorus (Fin 3)) :
    VelocityCoefficient :=
  ∑ source ∈ sourceModes, ∑ receiver ∈ receiverModes,
    interactionPhase source receiver x •
      complexStretchAmp source (omega source) (eta receiver)

/-- Coherent--coherent part of the finite stretching sum. -/
def finiteCoherentStretchingSum
    (sourceModes receiverModes : Finset Wavevector)
    (omega eta : FourierVelocity) (x : UnitAddTorus (Fin 3)) :
    VelocityCoefficient :=
  ∑ source ∈ sourceModes, ∑ receiver ∈ receiverModes,
    interactionPhase source receiver x •
      coherentCoherentStretchAmp source receiver
        (omega source) (eta receiver)

/-- The three misalignment-bearing parts of the finite stretching sum. -/
def finiteMisalignmentStretchingSum
    (sourceModes receiverModes : Finset Wavevector)
    (omega eta : FourierVelocity) (x : UnitAddTorus (Fin 3)) :
    VelocityCoefficient :=
  ∑ source ∈ sourceModes, ∑ receiver ∈ receiverModes,
    interactionPhase source receiver x •
      misalignmentStretchAmp source receiver
        (omega source) (eta receiver)

/-- **Exact finite-Fourier coherent/misaligned splitting identity.** -/
theorem finiteComplexStretchingSum_eq_coherent_add_misalignment
    (sourceModes receiverModes : Finset Wavevector)
    (omega eta : FourierVelocity) (x : UnitAddTorus (Fin 3)) :
    finiteComplexStretchingSum sourceModes receiverModes omega eta x =
      finiteCoherentStretchingSum sourceModes receiverModes omega eta x +
        finiteMisalignmentStretchingSum
          sourceModes receiverModes omega eta x := by
  unfold finiteComplexStretchingSum finiteCoherentStretchingSum
    finiteMisalignmentStretchingSum
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro source _hsource
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro receiver _hreceiver
  rw [complexStretchAmp_eq_coherent_add_misalignment source receiver,
    smul_add]

/-- Concrete finite-Fourier `split_le`: the norm of full stretching is
dominated by its coherent and misalignment shares. -/
theorem norm_finiteComplexStretchingSum_le_coherent_add_misalignment
    (sourceModes receiverModes : Finset Wavevector)
    (omega eta : FourierVelocity) (x : UnitAddTorus (Fin 3)) :
    ‖finiteComplexStretchingSum sourceModes receiverModes omega eta x‖ ≤
      ‖finiteCoherentStretchingSum sourceModes receiverModes omega eta x‖ +
        ‖finiteMisalignmentStretchingSum
          sourceModes receiverModes omega eta x‖ := by
  rw [finiteComplexStretchingSum_eq_coherent_add_misalignment]
  exact norm_add_le _ _

/-- If both coefficients are already coherent and both projection
denominators are nonzero, the entire misalignment interaction vanishes. -/
theorem misalignmentStretchAmp_eq_zero_of_coherent
    (source receiver : Wavevector) (a b : ℂ)
    (hsource : coherentDenominator source ≠ 0)
    (hreceiver : coherentDenominator receiver ≠ 0) :
    misalignmentStretchAmp source receiver
      (a • periodicCoherentMode source)
      (b • periodicCoherentMode receiver) = 0 := by
  rw [misalignmentStretchAmp,
    misalignmentComponent_smul_periodicCoherentMode_eq_zero a hsource,
    misalignmentComponent_smul_periodicCoherentMode_eq_zero b hreceiver]
  simp [complexStretchAmp_zero_source, complexStretchAmp_zero_receiver]

end PancakeComplexMisalignmentExpansion
end NavierStokes
end FluidDynamics
end Mettapedia
