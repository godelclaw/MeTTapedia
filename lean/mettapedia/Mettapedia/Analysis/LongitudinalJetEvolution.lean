import Mettapedia.Analysis.AngularCurlEvolution

/-!
# Material commutator cancellation for a longitudinal derivative

Contracting the transported first jet with the advected vector cancels
the velocity-gradient transport commutator. The velocity Hessian and
the viscous cross derivative remain. These are jet identities; their
application to a PDE requires actual derivatives and the actual equation.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.Analysis.LongitudinalJetEvolution

open scoped RealInnerProductSpace
local notation "R3" => EuclideanSpace ℝ (Fin 3)

def longitudinal (a : R3) (D : Fin 3 → R3) : R3 := ∑ j, a j • D j

def rate (a : R3) (D : Fin 3 → R3) (da : R3) (dD : Fin 3 → R3) : R3 :=
  (∑ j, da j • D j) + ∑ j, a j • dD j

def stretchingJet (a : R3) (D U : Fin 3 → R3) (H : Fin 3 → Fin 3 → R3) (j : Fin 3) : R3 :=
  (∑ k, D j k • U k) + (∑ k, a k • H k j) - ∑ k, U j k • D k

def velocityCurvature (a : R3) (H : Fin 3 → Fin 3 → R3) : R3 :=
  ∑ j, ∑ k, (a j * a k) • H k j

theorem continuous_longitudinal {X : Type*} [TopologicalSpace X]
    {a : X → R3} {D : X → Fin 3 → R3}
    (ha : Continuous a) (hD : ∀ j, Continuous (fun x ↦ D x j)) :
    Continuous (fun x ↦ longitudinal (a x) (D x)) :=
  continuous_finsetSum _ (fun j _ ↦
    ((EuclideanSpace.proj j).continuous.comp ha).smul (hD j))

theorem continuous_rate {X : Type*} [TopologicalSpace X]
    {a da : X → R3} {D dD : X → Fin 3 → R3}
    (ha : Continuous a) (hD : ∀ j, Continuous (fun x ↦ D x j))
    (hda : Continuous da) (hdD : ∀ j, Continuous (fun x ↦ dD x j)) :
    Continuous (fun x ↦ rate (a x) (D x) (da x) (dD x)) :=
  (continuous_longitudinal hda hD).add (continuous_longitudinal ha hdD)

theorem hasDerivAt_longitudinal {a : ℝ → R3} {D : ℝ → Fin 3 → R3}
    {da : R3} {dD : Fin 3 → R3} {t : ℝ}
    (ha : HasDerivAt a da t) (hD : ∀ j, HasDerivAt (fun τ ↦ D τ j) (dD j) t) :
    HasDerivAt (fun τ ↦ longitudinal (a τ) (D τ)) (rate (a t) (D t) da dD) t := by
  have haj (j : Fin 3) : HasDerivAt (fun τ ↦ a τ j) (da j) t := by
    simpa [EuclideanSpace.inner_single_left] using
      (hasDerivAt_const t (EuclideanSpace.single j (1 : ℝ))).inner ℝ ha
  have h (j : Fin 3) := (haj j).smul (hD j)
  have hh := HasDerivAt.fun_sum (u := Finset.univ) (fun j _ ↦ h j)
  simpa only [longitudinal, rate, Function.comp_def, Pi.smul_apply',
    Finset.sum_add_distrib, add_comm] using hh

theorem hasDerivAt_rate {a da : ℝ → R3} {D dD : ℝ → Fin 3 → R3}
    {dda : R3} {ddD : Fin 3 → R3} {t : ℝ}
    (ha : HasDerivAt a (da t) t)
    (hD : ∀ j, HasDerivAt (fun τ ↦ D τ j) (dD t j) t)
    (hda : HasDerivAt da dda t)
    (hdD : ∀ j, HasDerivAt (fun τ ↦ dD τ j) (ddD j) t) :
    HasDerivAt (fun τ ↦ rate (a τ) (D τ) (da τ) (dD τ))
      (rate (a t) (D t) dda ddD + 2 • longitudinal (da t) (dD t)) t := by
  have h := (hasDerivAt_longitudinal hda hD).add (hasDerivAt_longitudinal ha hdD)
  have he : rate (da t) (D t) dda (dD t) + rate (a t) (dD t) (da t) ddD =
      rate (a t) (D t) dda ddD + 2 • longitudinal (da t) (dD t) := by
    simp only [rate, longitudinal]
    module
  rw [he] at h
  exact h

theorem rate_stretching (a : R3) (D U : Fin 3 → R3) (H : Fin 3 → Fin 3 → R3) :
    rate a D (longitudinal a U) (stretchingJet a D U H) =
      longitudinal (longitudinal a D) U + velocityCurvature a H := by
  simp only [rate, longitudinal, stretchingJet, velocityCurvature, Fin.sum_univ_three,
    PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  module

theorem rate_add (a : R3) (D : Fin 3 → R3) (v w : R3) (V W : Fin 3 → R3) :
    rate a D (v + w) (fun j ↦ V j + W j) = rate a D v V + rate a D w W := by
  simp only [rate, Fin.sum_univ_three, PiLp.add_apply]
  module

theorem rate_smul (a : R3) (D : Fin 3 → R3) (v : R3) (V : Fin 3 → R3) (c : ℝ) :
    rate a D (c • v) (fun j ↦ c • V j) = c • rate a D v V := by
  simp only [rate, Fin.sum_univ_three, PiLp.smul_apply, smul_eq_mul]
  module

def diffusionCross (D : Fin 3 → R3) (E : Fin 3 → Fin 3 → R3) : R3 :=
  ∑ k, ∑ j, D k j • E j k

theorem rate_sub_laplacian (ν : ℝ) (a : R3) (D U : Fin 3 → R3)
    (H E : Fin 3 → Fin 3 → R3) (L : R3) (LD : Fin 3 → R3) :
    rate a D (longitudinal a U + ν • L) (fun j ↦ stretchingJet a D U H j + ν • LD j) -
      ν • (rate a D L LD + 2 • diffusionCross D E) =
        longitudinal (longitudinal a D) U + velocityCurvature a H -
          (2 * ν) • diffusionCross D E := by
  rw [rate_add, rate_smul, rate_stretching]
  module

end Mettapedia.Analysis.LongitudinalJetEvolution
