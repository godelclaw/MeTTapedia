import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalAnnularWeightDifferentiability
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalAnnularSourcePathChainRule

/-!
# Identification of the spatial material rate with the explicit PDE rate

Straight curves tangent to the instantaneous full velocity suffice to apply
the vorticity equation. The cutoff chain rule includes its threshold and
equal-amplitude contacts wherever its material derivative exists. Joint
spacetime differentiability supplies this hypothesis almost everywhere;
no measure-preserving flow is assumed.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.LocalAnnularExplicitRate

open scoped Topology
open MeasureTheory Set
open PeriodicFourierTriad PancakeHigherDerivativeMoments PancakeLocalInfiniteVelocity
open PancakeCurlOutputTail
open PancakeLocalMaterialTrajectories LocalLowDiffusionBudget
open Mettapedia.Analysis SignedCrossKernel UnitTorusProductTransport
open UnitTorusWeakDerivative UnitTorusMaterialBalance
open LocalAnnularMeanBalance LocalAnnularWeightDifferentiability
open LocalAnnularSourcePathChainRule

local notation "T3" => UnitAddTorus (Fin 3)
local notation "T6" => UnitAddTorus (Fin 3 ⊕ Fin 3)
local notation "X3" => Fin 3 → ℝ
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

def explicitRate (n N : ℕ) (L nu : ℝ) (u : FourierVelocity) (x : T6) : ℝ :=
  (1 / 2 : ℝ) * materialHighAmplitudeRate n N L u nu (leftPoint x) (rightPoint x)
    (fun j ↦ LocalMeanAlignmentBalance.velocity u (leftPoint x) j)
    (fun j ↦ LocalMeanAlignmentBalance.velocity u (rightPoint x) j)

variable {nu T B : ℝ} {u₀ : FourierVelocity}
  (s : LocalInfiniteVelocitySolution nu u₀ T B)

def tangentPath (t : ℝ) (r : X3) (τ : ℝ) : X3 :=
  fun j ↦ r j + (τ - t) * liftedVelocity s t r j

theorem tangentPath_self (t : ℝ) (r : X3) : tangentPath s t r t = r := by
  ext j
  simp [tangentPath]

theorem hasDerivAt_tangentPath (t : ℝ) (r : X3) :
    HasDerivAt (tangentPath s t r) (liftedVelocity s t (tangentPath s t r t)) t := by
  rw [tangentPath_self]
  apply hasDerivAt_pi.mpr
  intro j
  simpa only [tangentPath, id_eq, one_mul] using
    (((hasDerivAt_id t).sub_const t).mul_const (liftedVelocity s t r j)).const_add (r j)

theorem liftedVelocity_eq (t : ℝ) (r : X3) :
    liftedVelocity s t r = fun j ↦ LocalMeanAlignmentBalance.velocity
      (s.coefficients t) (torusPoint r) j := rfl

theorem leftPoint_frozenShift (t : ℝ) (x : T6) (r : X3)
    (hr : torusPoint r = leftPoint x) (h : ℝ) :
    leftPoint (x + materialShift (productVelocity (s.coefficients t) x) h) =
      torusPoint (tangentPath s t r (t + h)) := by
  change leftPoint (x + materialShift (productVelocity (s.coefficients t) x) h) =
    torusPoint (fun j ↦ r j + (t + h - t) * liftedVelocity s t r j)
  rw [add_sub_cancel_left, torusPoint_line, liftedVelocity_eq, hr]
  rfl

theorem rightPoint_frozenShift (t : ℝ) (x : T6) (r : X3)
    (hr : torusPoint r = rightPoint x) (h : ℝ) :
    rightPoint (x + materialShift (productVelocity (s.coefficients t) x) h) =
      torusPoint (tangentPath s t r (t + h)) := by
  change rightPoint (x + materialShift (productVelocity (s.coefficients t) x) h) =
    torusPoint (fun j ↦ r j + (t + h - t) * liftedVelocity s t r j)
  rw [add_sub_cancel_left, torusPoint_line, liftedVelocity_eq, hr]
  rfl

variable (a b : ℝ) (hab : a ≤ b) (hI : Icc a b ⊆ Ioo (0 : ℝ) T)
  (g : Wavevector → ℝ) (hg : ∀ q, 0 ≤ g q) (hSum : Summable g)
  (hu : ∀ τ ∈ Icc (0 : ℝ) T, ∀ q, fourierMoment 3 (s.coefficients τ) q ≤ g q)

include hab hI hg hSum hu in
theorem frozenMaterialRate_eq_of_differentiable (n N : ℕ) (L : ℝ) (hL : 0 < L)
    (t : ℝ) (ht : t ∈ Ioo a b) (x : T6)
    (hd : DifferentiableAt ℝ (frozenWeight L s.coefficients t x) 0) :
    frozenMaterialRate (n + 1) N L s.coefficients t x =
      explicitRate n N L nu (s.coefficients t) x := by
  obtain ⟨r, hr, _⟩ := torusPoint_bounded_rep (leftPoint x)
  obtain ⟨q, hq, _⟩ := torusPoint_bounded_rep (rightPoint x)
  let X := tangentPath s t r
  let Y := tangentPath s t q
  have hX : HasDerivAt X (liftedVelocity s t (X t)) t := hasDerivAt_tangentPath s t r
  have hY : HasDerivAt Y (liftedVelocity s t (Y t)) t := hasDerivAt_tangentPath s t q
  have hleft (h : ℝ) := leftPoint_frozenShift s t x r hr h
  have hright (h : ℝ) := rightPoint_frozenShift s t x q hq h
  have hweight (τ : ℝ) : frozenWeight L s.coefficients t x (τ - t) =
      1 - lowAmplitudeWeight L
        (fullVorticity (s.coefficients τ) (torusPoint (X τ)))
        (fullVorticity (s.coefficients τ) (torusPoint (Y τ))) := by
    unfold frozenWeight amplitudeWeight
    rw [hleft, hright]
    simp only [add_sub_cancel, X, Y]
  have hdt : DifferentiableAt ℝ (fun τ ↦ 1 - lowAmplitudeWeight L
      (fullVorticity (s.coefficients τ) (torusPoint (X τ)))
      (fullVorticity (s.coefficients τ) (torusPoint (Y τ)))) t := by
    have hd0 : DifferentiableAt ℝ (frozenWeight L s.coefficients t x) (t - t) := by
      simpa only [sub_self] using hd
    have hd' := hd0.comp (f := fun τ : ℝ ↦ τ - t) t
      (show DifferentiableAt ℝ (fun τ : ℝ ↦ τ - t) t by fun_prop)
    simpa only [Function.comp_def, hweight, sub_self] using hd'
  have hx := LocalVorticityTangency.hasDerivAt_fullVorticity_path
    s g hg hSum hu a b hab hI X t ht hX
  have hy := LocalVorticityTangency.hasDerivAt_fullVorticity_path
    s g hg hSum hu a b hab hI Y t ht hY
  have hp := (hasDerivAt_highAmplitudeWeight_of_differentiable hx hy hL hdt).mul
    (LocalAnnularStretchEvolution.hasDerivAt_pairedStretch_path
      s g hg hSum hu a b hab hI X Y t ht hX hY n N)
  have hp' := (hp.const_mul (1 / 2 : ℝ)).comp_of_eq 0
    ((hasDerivAt_id (0 : ℝ)).const_add t) (by simp)
  have htorus : PancakeFourierMaterialPaths.torusPoint = (torusPoint : X3 → T3) := rfl
  have hf : HasDerivAt (fun h ↦ density (n + 1) N L (s.coefficients (t + h))
      (x + materialShift (productVelocity (s.coefficients t) x) h))
      (explicitRate n N L nu (s.coefficients t) x) 0 := by
    simpa only [htorus, Function.comp_def, Pi.mul_apply, id_eq,
      density, highAmplitudeStretch, hleft, hright,
      X, Y, tangentPath_self, add_zero, mul_one, explicitRate, materialHighAmplitudeRate,
      liftedVelocity_eq, hr, hq] using hp'
  exact hf.deriv

include hab hI hg hSum hu in
theorem ae_ae_frozenMaterialRate_eq (n N : ℕ) (L : ℝ) (hL : 0 < L) :
    ∀ᵐ t : ℝ, t ∈ Ioo a b → ∀ᵐ x : T6,
      frozenMaterialRate (n + 1) N L s.coefficients t x =
        explicitRate n N L nu (s.coefficients t) x := by
  filter_upwards [ae_ae_differentiableAt_frozenWeight s a b hab hI g hg hSum hu L hL]
    with t hd ht
  exact (hd ht).mono (fun x hx ↦ frozenMaterialRate_eq_of_differentiable
    s a b hab hI g hg hSum hu n N L hL t ht x hx)

end Mettapedia.FluidDynamics.NavierStokes.LocalAnnularExplicitRate
