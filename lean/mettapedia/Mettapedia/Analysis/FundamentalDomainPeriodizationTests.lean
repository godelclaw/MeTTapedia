import Mettapedia.Analysis.FundamentalDomainPeriodization

/-! Unit-weight and zero-kernel regressions for generic periodization. -/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.Analysis.FundamentalDomainPeriodizationTests

open MeasureTheory FundamentalDomainPeriodization
open scoped ENNReal

variable {G α E : Type*} [AddGroup G] [Countable G] [AddAction G α]
  [MeasurableSpace α] [MeasurableConstVAdd G α]
  {μ : Measure α} [VAddInvariantMeasure G α μ]
  [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]

example {s : Set α} (hfund : IsAddFundamentalDomain G s μ) (K : α → E) (hK : Measurable K) :
    (∫⁻ x in s, ‖addPeriodization (G := G) K x‖ₑ ∂μ) ≤ ∫⁻ x, ‖K x‖ₑ ∂μ := by
  simpa using setLIntegral_weight_mul_enorm_addPeriodization_le hfund K hK (fun _ ↦ 1)
    measurable_const (fun _ _ ↦ rfl)

example (x : α) : addPeriodization (G := G) (fun _ : α ↦ (0 : E)) x = 0 := by
  simp [addPeriodization]

end Mettapedia.Analysis.FundamentalDomainPeriodizationTests

#print axioms Mettapedia.Analysis.FundamentalDomainPeriodization.measurable_addPeriodization
#print axioms Mettapedia.Analysis.FundamentalDomainPeriodization.addPeriodization_vadd
#print axioms Mettapedia.Analysis.FundamentalDomainPeriodization.setLIntegral_enorm_addPeriodization_le
#print axioms Mettapedia.Analysis.FundamentalDomainPeriodization.integrableOn_addPeriodization
#print axioms Mettapedia.Analysis.FundamentalDomainPeriodization.setIntegral_character_smul_addPeriodization_eq
#print axioms Mettapedia.Analysis.FundamentalDomainPeriodization.setLIntegral_weight_mul_enorm_addPeriodization_le
