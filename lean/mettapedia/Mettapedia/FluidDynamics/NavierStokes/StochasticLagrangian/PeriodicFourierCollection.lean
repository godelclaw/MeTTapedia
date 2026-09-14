import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PeriodicProjectedTensorJet

/-!
# Collecting repeated Fourier frequencies without changing the field

Absolutely summable indexed coefficients can be grouped by output frequency.
This supplies canonical lattice coefficients for the pair- and triple-indexed
products used by the physical flux. In particular, equal outputs are summed
before Parseval, rather than treated as orthogonal interaction labels.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PeriodicFourierCollection

open scoped ComplexConjugate
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakePeriodicComplexStretch
open PancakeInfiniteFourierDerivative PancakeBlockReality PancakeFourierTranslationCurve
open PancakeInfiniteFourierTime
open PancakeDyadicDirectionEvolution PeriodicProjectedTensorJet

variable {ι : Type*}

def collect (freq : ι → Wavevector) (a : ι → VelocityCoefficient) : FourierVelocity :=
  fun q ↦ ∑' p : freq ⁻¹' {q}, a p

theorem norm_collect_le (freq : ι → Wavevector) (a : ι → VelocityCoefficient)
    (ha : Summable (fun p ↦ ‖a p‖)) (q : Wavevector) :
    ‖collect freq a q‖ ≤ ∑' p : freq ⁻¹' {q}, ‖a p‖ :=
  norm_tsum_le_tsum_norm (ha.subtype _)

theorem summable_norm_collect (freq : ι → Wavevector) (a : ι → VelocityCoefficient)
    (ha : Summable (fun p ↦ ‖a p‖)) : Summable (fun q ↦ ‖collect freq a q‖) :=
  (ha.hasSum.tsum_fiberwise freq).summable.of_nonneg_of_le
    (fun _ ↦ norm_nonneg _) (norm_collect_le freq a ha)

theorem fullFourierField_collect (freq : ι → Wavevector) (a : ι → VelocityCoefficient)
    (ha : Summable (fun p ↦ ‖a p‖)) :
    fullFourierField id (collect freq a) = fullFourierField freq a := by
  have h := (summable_modeField freq a ha).hasSum.tsum_fiberwise freq
  have he (q : Wavevector) :
      (∑' p : freq ⁻¹' {q}, modeField (freq p) (a p)) = modeField q (collect freq a q) := by
    have hf (p : freq ⁻¹' {q}) : freq p = q := p.property
    simp_rw [hf]
    exact ((modeFieldCLM q).map_tsum (ha.subtype _).of_norm).symm
  simp only [he] at h
  exact h.tsum_eq

theorem indexedRealField_collect (freq : ι → Wavevector) (a : ι → VelocityCoefficient)
    (ha : Summable (fun p ↦ ‖a p‖)) :
    indexedRealField id (collect freq a) = indexedRealField freq a := by
  simp only [indexedRealField, fullFourierField_collect freq a ha]

/-- For finitely supported inputs, collection is an exact finite sum. -/
theorem collect_eq_sum [DecidableEq ι] (freq : ι → Wavevector)
    (a : ι → VelocityCoefficient) (s : Finset ι)
    (hs : ∀ p, p ∉ s → a p = 0) (q : Wavevector) :
    collect freq a q = ∑ p ∈ s, if freq p = q then a p else 0 := by
  classical
  unfold collect
  rw [tsum_subtype]
  calc
    _ = ∑ p ∈ s, (freq ⁻¹' {q}).indicator a p :=
      tsum_eq_sum (fun p hp ↦ by simp [Set.indicator, hs p hp])
    _ = _ := by simp only [Set.indicator, Set.mem_preimage, Set.mem_singleton_iff]

theorem collect_eq_zero_of_not_mem_image [DecidableEq ι] (freq : ι → Wavevector)
    (a : ι → VelocityCoefficient) (s : Finset ι)
    (hs : ∀ p, p ∉ s → a p = 0) (q : Wavevector) (hq : q ∉ s.image freq) :
    collect freq a q = 0 := by
  classical
  rw [collect_eq_sum freq a s hs q]
  apply Finset.sum_eq_zero
  intro p hp
  have hn : freq p ≠ q := by
    intro he
    exact hq (Finset.mem_image.mpr ⟨p, hp, he⟩)
  simp only [if_neg hn]

def negateFiber [AddCommGroup ι] (freq : ι → Wavevector)
    (hf : ∀ p, freq (-p) = -freq p) (q : Wavevector) :
    (freq ⁻¹' {q}) ≃ (freq ⁻¹' {-q}) where
  toFun p := ⟨-p.val, by change freq (-p.val) = -q; rw [hf, p.property]⟩
  invFun p := ⟨-p.val, by change freq (-p.val) = q; rw [hf, p.property, neg_neg]⟩
  left_inv p := by apply Subtype.ext; simp
  right_inv p := by apply Subtype.ext; simp

theorem collect_reality [AddCommGroup ι] (freq : ι → Wavevector)
    (hf : ∀ p, freq (-p) = -freq p) (a : ι → VelocityCoefficient)
    (ha : Summable (fun p ↦ ‖a p‖))
    (hr : ∀ p, a (-p) = coefficientConjugate (a p)) (q : Wavevector) :
    collect freq a (-q) = coefficientConjugate (collect freq a q) := by
  have he := (negateFiber freq hf q).tsum_eq (fun p : freq ⁻¹' {-q} ↦ a p)
  change (∑' p : freq ⁻¹' {q}, a (-p.val)) = collect freq a (-q) at he
  rw [← he]
  have hinj : Function.Injective (fun p : freq ⁻¹' {q} ↦ -p.val) := by
    intro p r h
    exact Subtype.ext (neg_injective h)
  have hn := (ha.comp_injective hinj).of_norm
  ext i
  rw [tsum_apply hn]
  simp only [hr, coefficientConjugate_apply, collect]
  rw [tsum_apply (ha.subtype _).of_norm, Complex.conj_tsum]

end Mettapedia.FluidDynamics.NavierStokes.PeriodicFourierCollection
