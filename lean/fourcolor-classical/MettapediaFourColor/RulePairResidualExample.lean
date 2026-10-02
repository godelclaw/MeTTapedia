import MettapediaFourColor.RulePairResidual
import MettapediaFourColor.RulePairBudgetExample

/-! The degree-five budget example also consumes the rerooted reduction
pattern. This certifies local geometry, not minimality of the finite graph. -/

namespace FourColor.RulePairResidualExample

open RulePairExample

theorem five_sender_mixed : ∃ e : graph.Dart, RulePairDiamond.MixedAt rotation e := by
  obtain ⟨hl, hr, _, hf, ho, hs, _⟩ := RulePairBudgetExample.observations
  have shared := RulePairBudget.shared_candidates RulePairBudgetExample.root hl hr
  exact RulePairResidual.right_mixed_of_check _ hr hs (shared ▸ hf) ho

end FourColor.RulePairResidualExample
