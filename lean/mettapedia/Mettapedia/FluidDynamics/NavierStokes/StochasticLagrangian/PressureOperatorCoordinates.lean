import Mettapedia.Analysis.EuclideanBilinearCoordinates
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PressureBilinearOperator

/-!
# Real-basis entries determine the complex pressure operator

The complex-bilinear pressure operator is reconstructed exactly from the
real pressure entries on coordinate vectors. No phase restriction on the
eventual complex inputs is imposed.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PressureOperatorCoordinates

open Mettapedia.Analysis.EuclideanBilinearCoordinates
open PeriodicFourierTriad PancakeFrequencyProjectorCommutator ComplexPressurePair
open PressureBilinearOperator FourierPressureCommutator

local notation "R3" => EuclideanSpace ℝ (Fin 3)
local notation "C3" => EuclideanSpace ℂ (Fin 3)

theorem ofLp_single_eq_realCoefficient (j : Fin 3) :
    WithLp.ofLp (EuclideanSpace.single j (1 : ℂ)) =
      realCoefficient (EuclideanSpace.single j (1 : ℝ)) := by
  ext i
  by_cases h : i = j <;> simp [realCoefficient, h]

theorem entry_pressurePairOperator (e : R3) (he : ‖e‖ = 1) (k p : Wavevector) (i j l : Fin 3) :
    entry (pressurePairOperator e he k p) i j l =
      ((CoherentPressurePair.tiltPair e (realFrequency k) (realFrequency p)
        (EuclideanSpace.single j 1) (EuclideanSpace.single l 1) i : ℝ) : ℂ) := by
  rw [entry, pressurePairOperator_apply, ofLp_single_eq_realCoefficient,
    ofLp_single_eq_realCoefficient, tiltPair_real]
  rfl

theorem reconstruct_pressurePairOperator (e : R3) (he : ‖e‖ = 1) (k p : Wavevector) :
    reconstruct (fun i j l ↦
      ((CoherentPressurePair.tiltPair e (realFrequency k) (realFrequency p)
        (EuclideanSpace.single j 1) (EuclideanSpace.single l 1) i : ℝ) : ℂ)) =
      pressurePairOperator e he k p := by
  simp_rw [← entry_pressurePairOperator e he k p]
  exact reconstruct_entry _

end Mettapedia.FluidDynamics.NavierStokes.PressureOperatorCoordinates
