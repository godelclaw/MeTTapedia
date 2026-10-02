import MettapediaFourColor.ExtraChargeReduction
import MettapediaFourColor.ChainBoundaryGeometry

/-! Both branches of the extra-rule closing law occur in the retained
162-vertex triangulation. Complete source readings are checked first;
the shared geometric theorem then supplies the two reduction patterns. -/

namespace FourColor.ExtraChargeExample

open ChainBoundaryExample
open Mettapedia.GraphTheory.FourColor SimpleGraphDartRotation

local instance (r : Fin 84) : NeZero (NearLinearRuleData.size r) :=
  ⟨by have := (NearLinearRuleData.headers r).1; omega⟩

def chainImages : NearLinearRuleData.Vertex 5 → Fin 162 := ![0,44,45,42,103]
def mixedImages : NearLinearRuleData.Vertex 5 → Fin 162 := ![138,65,62,25,137]

set_option maxHeartbeats 0 in
-- Check all source edges, prescribed degrees and cyclic turns.
theorem chain_fits : RuleMatcher.Fits rotation 5 chainImages := by decide +kernel

set_option maxHeartbeats 0 in
-- Check all source edges, prescribed degrees and cyclic turns.
theorem mixed_fits : RuleMatcher.Fits rotation 5 mixedImages := by decide +kernel

def chainSource : NearLinearCharge.Occurrence rotation 5 :=
  RuleMatcher.occurrenceOfFits rotation chainImages chain_fits

def mixedSource : NearLinearCharge.Occurrence rotation 5 :=
  RuleMatcher.occurrenceOfFits rotation mixedImages mixed_fits

def chainRoot : graph.Dart := ExtraChargeReduction.outerRoot rotation chainSource

/-- The general closure supplies the complete consecutive chain word. -/
theorem chain_word : ∀ n : Fin 4,
    graph.degree (ChainFanRecognition.walk rotation chainRoot n.val).snd =
      ChainFanRecognition.word n :=
  ExtraChargeReduction.word_of_six rotation cyclic triangular chainSource
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- The other outer degree consumes the same proof of the missing triangle. -/
theorem mixed_pattern : RulePairDiamond.MixedAt rotation
    (ExtraChargeReduction.sharedRoot rotation mixedSource) :=
  ExtraChargeReduction.mixed_of_five rotation cyclic triangular mixedSource
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

def chainReading : ChainCoreReading.Reading rotation :=
  ChainFanRecognition.reading rotation triangular chainRoot (by decide +kernel) chain_word

set_option maxHeartbeats 0 in
-- The full core is induced in this finite example.
theorem chain_induced : ∀ i j, graph.Adj (chainReading.map i) (chainReading.map j) →
    ChainCoreReading.core.Adj i j := by decide +kernel

/-- The constructed word is consumed by the existing complete boundary builder. -/
def chainOccurrence : NearLinearChainOccurrence.Occurrence rotation :=
  ChainCoreOccurrence.occurrence chainReading triangular cyclic chain_induced

end FourColor.ExtraChargeExample
