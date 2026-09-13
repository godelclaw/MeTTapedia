import Mettapedia.Analysis.UnitTorusDivergenceFreeTransport
import Mathlib.Analysis.InnerProductSpace.Calculus

/-! # Skew pairing of actual incompressible transport on a unit torus -/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.Analysis.UnitTorusTransportPairing

open scoped RealInnerProductSpace
open MeasureTheory
variable {d E : Type*} [Fintype d] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
local notation "T" => UnitAddTorus d
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

theorem integral_inner_transport (f g : T → E) (df dg : d → T → E)
    (b db : d → T → ℝ) (shift : d → ℝ → T)
    (hf : Continuous f) (hg : Continuous g)
    (hdf : ∀ j, Continuous (df j)) (hdg : ∀ j, Continuous (dg j))
    (hb : ∀ j, Continuous (b j)) (hdb : ∀ j, Continuous (db j))
    (hs : ∀ j, Continuous (shift j)) (hs0 : ∀ j, shift j 0 = 0)
    (hf' : ∀ j x h, HasDerivAt (fun t ↦ f (x + shift j t)) (df j (x + shift j h)) h)
    (hg' : ∀ j x h, HasDerivAt (fun t ↦ g (x + shift j t)) (dg j (x + shift j h)) h)
    (hb' : ∀ j x h, HasDerivAt (fun t ↦ b j (x + shift j t)) (db j (x + shift j h)) h)
    (hdiv : ∀ x, ∑ j, db j x = 0) :
    (∫ x : T, ⟪f x, ∑ j, b j x • dg j x⟫) =
      -(∫ x : T, ⟪∑ j, b j x • df j x, g x⟫) := by
  have hz := UnitTorusContinuousRate.integral_sum_mul_rate_eq_zero
    (fun x ↦ ⟪f x, g x⟫) (fun j x ↦ ⟪df j x, g x⟫ + ⟪f x, dg j x⟫)
    b db shift (hf.inner hg) (fun j ↦ ((hdf j).inner hg).add (hf.inner (hdg j)))
    hb hdb hs hs0 (fun j x h ↦ by
      simpa only [add_comm] using (hf' j x h).inner ℝ (hg' j x h)) hb' hdiv
  have hd : Continuous (fun x ↦ ∑ j, b j x • df j x) :=
    continuous_finsetSum _ (fun j _ ↦ (hb j).smul (hdf j))
  have he : Continuous (fun x ↦ ∑ j, b j x • dg j x) :=
    continuous_finsetSum _ (fun j _ ↦ (hb j).smul (hdg j))
  have hi : Integrable (fun x : T ↦ ⟪∑ j, b j x • df j x, g x⟫) :=
    (hd.inner hg).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hj : Integrable (fun x : T ↦ ⟪f x, ∑ j, b j x • dg j x⟫) :=
    (hf.inner he).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hp (x : T) : (∑ j, b j x * (⟪df j x, g x⟫ + ⟪f x, dg j x⟫)) =
      ⟪∑ j, b j x • df j x, g x⟫ + ⟪f x, ∑ j, b j x • dg j x⟫ := by
    simp only [sum_inner, inner_sum, real_inner_smul_left, real_inner_smul_right,
      mul_add, Finset.sum_add_distrib]
  simp_rw [hp] at hz
  rw [integral_add hi hj] at hz
  linarith

theorem integral_inner_rate (f g df dg : T → E) (shift : ℝ → T)
    (hf : Continuous f) (hg : Continuous g) (hdf : Continuous df) (hdg : Continuous dg)
    (hs : Continuous shift) (hs0 : shift 0 = 0)
    (hf' : ∀ x h, HasDerivAt (fun t ↦ f (x + shift t)) (df (x + shift h)) h)
    (hg' : ∀ x h, HasDerivAt (fun t ↦ g (x + shift t)) (dg (x + shift h)) h) :
    (∫ x : T, ⟪f x, dg x⟫) = -(∫ x : T, ⟪df x, g x⟫) := by
  have hz := UnitTorusContinuousRate.integral_rate_eq_zero (fun x ↦ ⟪f x, g x⟫)
    (fun x ↦ ⟪f x, dg x⟫ + ⟪df x, g x⟫) shift (hf.inner hg)
    ((hf.inner hdg).add (hdf.inner hg)) hs hs0
    (fun x h ↦ (hf' x h).inner ℝ (hg' x h))
  have hi : Integrable (fun x : T ↦ ⟪f x, dg x⟫) :=
    (hf.inner hdg).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hj : Integrable (fun x : T ↦ ⟪df x, g x⟫) :=
    (hdf.inner hg).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  rw [integral_add hi hj] at hz
  linarith

end Mettapedia.Analysis.UnitTorusTransportPairing
