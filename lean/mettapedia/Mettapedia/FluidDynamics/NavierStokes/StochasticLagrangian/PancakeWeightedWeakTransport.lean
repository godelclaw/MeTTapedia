import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeWeakIncompressibleTransport

/-!
# Signed weighted transport for locally Lipschitz periodic scalars

All transport rates below are actual coordinate derivatives. Product
differentiation and incompressibility move a derivative from the transported
scalar onto the weight. In particular, the transport contribution need not
be estimated by squaring the derivative of the transported field.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PancakeWeightedWeakTransport

open MeasureTheory
open PancakeWeakIncompressibleTransport PancakePeriodicWeakDerivative PancakeHaarTransportRate
open PancakeFourierMaterialPaths PancakeFourierTranslationCurve PancakeLocallyLipschitzEnergy

local notation "T3" => UnitAddTorus (Fin 3)
local notation "X3" => Fin 3 → ℝ

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

theorem coordinateTransport_add_const (f : T3 → ℝ) (c : ℝ) (v : Fin 3 → T3 → ℝ) (x : T3) :
    coordinateTransport (fun y ↦ f y + c) v x = coordinateTransport f v x := by
  simp only [coordinateTransport, shiftRate, deriv_add_const]

theorem ae_coordinateTransport_mul (f g : T3 → ℝ) (v : Fin 3 → T3 → ℝ)
    (hf : Continuous f) (hg : Continuous g)
    (hfL : LocallyLipschitz (fun r : X3 ↦ f (torusPoint r)))
    (hgL : LocallyLipschitz (fun r : X3 ↦ g (torusPoint r))) :
    ∀ᵐ x : T3, coordinateTransport (fun y ↦ f y * g y) v x =
      coordinateTransport f v x * g x + f x * coordinateTransport g v x := by
  have hdiff : ∀ᵐ x : T3, ∀ j : Fin 3,
      DifferentiableAt ℝ (fun h ↦ f (x + coordinateShift j h)) 0 ∧
      DifferentiableAt ℝ (fun h ↦ g (x + coordinateShift j h)) 0 :=
    ae_all_iff.mpr (fun j ↦ (ae_coordinate_differentiable f j hf hfL).and
      (ae_coordinate_differentiable g j hg hgL))
  filter_upwards [hdiff] with x hx
  unfold coordinateTransport
  simp_rw [shiftRate_mul f g _ x (coordinateShift_zero _) (hx _).1 (hx _).2]
  simp only [add_mul, Finset.sum_add_distrib, Finset.sum_mul, Finset.mul_sum]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro j _ <;> ring

section Incompressible

variable (v : Fin 3 → T3 → ℝ)
  (hv : ∀ j, Continuous (v j))
  (hvL : ∀ j, LocallyLipschitz (fun r : X3 ↦ v j (torusPoint r)))
  (hdiv : ∀ᵐ x : T3, coordinateDivergence v x = 0)

include hv hvL hdiv

theorem integrable_transport_times (f g : T3 → ℝ)
    (hf : Continuous f) (hg : Continuous g)
    (hfL : LocallyLipschitz (fun r : X3 ↦ f (torusPoint r))) :
    Integrable (fun x ↦ coordinateTransport f v x * g x) :=
  integrable_mul_continuous _ g
    (integral_coordinateTransport_zero f v hf hv hfL hvL hdiv).1 hg

theorem integral_transport_mul (f g : T3 → ℝ)
    (hf : Continuous f) (hg : Continuous g)
    (hfL : LocallyLipschitz (fun r : X3 ↦ f (torusPoint r)))
    (hgL : LocallyLipschitz (fun r : X3 ↦ g (torusPoint r))) :
    (∫ x : T3, coordinateTransport f v x * g x) =
      -(∫ x : T3, f x * coordinateTransport g v x) := by
  have hfgL := locallyLipschitz_mul_real _ _ hfL hgL
  have hz := (integral_coordinateTransport_zero (fun x ↦ f x * g x) v
    (hf.mul hg) hv hfgL hvL hdiv).2
  have hIf := integrable_transport_times v hv hvL hdiv f g hf hg hfL
  have hIg : Integrable (fun x ↦ f x * coordinateTransport g v x) := by
    simpa only [mul_comm] using integrable_transport_times v hv hvL hdiv g f hg hf hgL
  rw [integral_congr_ae (ae_coordinateTransport_mul f g v hf hg hfL hgL), integral_add hIf hIg] at hz
  linarith

/-- The weighted signed product identity. The right side differentiates
only the weight k; neither transported scalar derivative is squared. -/
theorem integral_weighted_transport (k f g : T3 → ℝ)
    (hk : Continuous k) (hf : Continuous f) (hg : Continuous g)
    (hkL : LocallyLipschitz (fun r : X3 ↦ k (torusPoint r)))
    (hfL : LocallyLipschitz (fun r : X3 ↦ f (torusPoint r)))
    (hgL : LocallyLipschitz (fun r : X3 ↦ g (torusPoint r))) :
    (∫ x : T3, k x * f x * coordinateTransport g v x) +
      (∫ x : T3, k x * g x * coordinateTransport f v x) =
      -(∫ x : T3, coordinateTransport k v x * f x * g x) := by
  have hki := integrable_transport_times v hv hvL hdiv k (fun x ↦ f x * g x) hk (hf.mul hg) hkL
  have hfi := integrable_transport_times v hv hvL hdiv f (fun x ↦ k x * g x) hf (hk.mul hg) hfL
  have hkfL := locallyLipschitz_mul_real _ _ hkL hfL
  have hparts := integral_transport_mul v hv hvL hdiv (fun x ↦ k x * f x) g
    (hk.mul hf) hg hkfL hgL
  have heq : (∫ x : T3, coordinateTransport (fun y ↦ k y * f y) v x * g x) =
      (∫ x : T3, coordinateTransport k v x * (f x * g x)) +
      (∫ x : T3, coordinateTransport f v x * (k x * g x)) := by
    rw [← integral_add hki hfi]
    apply integral_congr_ae
    filter_upwards [ae_coordinateTransport_mul k f v hk hf hkL hfL] with x hx
    rw [hx]
    ring
  rw [heq] at hparts
  have hfcomm : (∫ x : T3, coordinateTransport f v x * (k x * g x)) =
      ∫ x : T3, k x * g x * coordinateTransport f v x := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun x ↦ by ring)
  rw [hfcomm] at hparts
  simp_rw [← mul_assoc] at hparts
  linarith

end Incompressible

end Mettapedia.FluidDynamics.NavierStokes.PancakeWeightedWeakTransport
