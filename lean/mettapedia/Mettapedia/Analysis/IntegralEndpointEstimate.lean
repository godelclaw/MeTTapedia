import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.Order.OrderClosed

/-!
# Extending an integral estimate to interval endpoints

Continuity extends an inequality proved only for strictly interior pairs
of times to an estimate from the initial endpoint at every time of the
closed interval. No sign assumption on the integrands is required.
-/

set_option autoImplicit false
noncomputable section

namespace intervalIntegral

open MeasureTheory Set

theorem endpoint_estimate_of_interior {A Z R : ℝ → ℝ} {T C : ℝ} (hT : 0 < T)
    (hA : ContinuousOn A (Icc 0 T)) (hZ : ContinuousOn Z (Icc 0 T))
    (hR : ContinuousOn R (Icc 0 T))
    (h : ∀ a b : ℝ, 0 < a → a < b → b < T →
      A b + (∫ t in a..b, Z t) ≤ A a + C + ∫ t in a..b, R t) :
    ∀ b ∈ Icc (0 : ℝ) T,
      A b + (∫ t in (0 : ℝ)..b, Z t) ≤ A 0 + C + ∫ t in (0 : ℝ)..b, R t := by
  have hZI : IntegrableOn Z (uIcc 0 T) := by
    simpa only [uIcc_of_le hT.le] using hZ.integrableOn_Icc
  have hRI : IntegrableOn R (uIcc 0 T) := by
    simpa only [uIcc_of_le hT.le] using hR.integrableOn_Icc
  have hZp : ContinuousOn (fun b ↦ ∫ t in (0 : ℝ)..b, Z t) (Icc 0 T) := by
    simpa only [uIcc_of_le hT.le] using continuousOn_primitive_interval hZI
  have hRp : ContinuousOn (fun b ↦ ∫ t in (0 : ℝ)..b, R t) (Icc 0 T) := by
    simpa only [uIcc_of_le hT.le] using continuousOn_primitive_interval hRI
  have hinner (b : ℝ) (hb : b ∈ Ioo (0 : ℝ) T) :
      A b + (∫ t in (0 : ℝ)..b, Z t) ≤ A 0 + C + ∫ t in (0 : ℝ)..b, R t := by
    have hsub : Icc (0 : ℝ) b ⊆ Icc (0 : ℝ) T := fun _ ht ↦ ⟨ht.1, ht.2.trans hb.2.le⟩
    have hZIb : IntegrableOn Z (uIcc 0 b) := by
      simpa only [uIcc_of_le hb.1.le] using (hZ.mono hsub).integrableOn_Icc
    have hRIb : IntegrableOn R (uIcc 0 b) := by
      simpa only [uIcc_of_le hb.1.le] using (hR.mono hsub).integrableOn_Icc
    have hZl : ContinuousOn (fun a ↦ ∫ t in a..b, Z t) (Icc 0 b) := by
      simpa only [uIcc_of_le hb.1.le] using continuousOn_primitive_interval_left hZIb
    have hRl : ContinuousOn (fun a ↦ ∫ t in a..b, R t) (Icc 0 b) := by
      simpa only [uIcc_of_le hb.1.le] using continuousOn_primitive_interval_left hRIb
    have hcl : closure (Ioo (0 : ℝ) b) = Icc (0 : ℝ) b := closure_Ioo hb.1.ne
    exact le_on_closure (fun a ha ↦ h a b ha.1 ha.2 hb.2)
      (hcl ▸ continuousOn_const.add hZl)
      (hcl ▸ ((hA.mono hsub).add continuousOn_const).add hRl)
      (hcl ▸ (show (0 : ℝ) ∈ Icc 0 b from ⟨le_rfl, hb.1.le⟩))
  have hcl : closure (Ioo (0 : ℝ) T) = Icc (0 : ℝ) T := closure_Ioo hT.ne
  intro b hb
  exact le_on_closure hinner (hcl ▸ hA.add hZp)
    (hcl ▸ continuousOn_const.add hRp) (hcl ▸ hb)

end intervalIntegral
