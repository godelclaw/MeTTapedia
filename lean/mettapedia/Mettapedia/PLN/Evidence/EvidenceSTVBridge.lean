import Mettapedia.PLN.RuleFamilies.FirstOrder.PLNDeduction
import Mettapedia.PLN.TruthValues.PLNDistributional
import Mettapedia.PLN.Evidence.BinaryEvidence

/-!
# Binary evidence read as a simple truth value

`evidenceToSTV κ e` is the `(strength, confidence)` record of `PLNDeduction.STV`
read from binary evidence: strength `n⁺ / (n⁺ + n⁻)` and confidence
`(n⁺ + n⁻) / (n⁺ + n⁻ + κ)`, as real numbers in `[0, 1]`.
-/

noncomputable section

namespace Mettapedia.PLN.Evidence.EvidenceSTVBridge

open Mettapedia.PLN.RuleFamilies.FirstOrder
open scoped ENNReal

/-- Binary evidence read as a simple truth value, with prior weight `κ`. -/
def evidenceToSTV (κ : ℝ≥0∞) (e : BinaryEvidence) : PLNDeduction.STV where
  strength := PLNDeduction.clamp01 ((BinaryEvidence.toStrength e).toReal)
  confidence := PLNDeduction.clamp01 ((BinaryEvidence.toConfidence κ e).toReal)
  strength_nonneg := PLNDeduction.clamp01_nonneg _
  strength_le_one := PLNDeduction.clamp01_le_one _
  confidence_nonneg := PLNDeduction.clamp01_nonneg _
  confidence_le_one := PLNDeduction.clamp01_le_one _

end Mettapedia.PLN.Evidence.EvidenceSTVBridge
