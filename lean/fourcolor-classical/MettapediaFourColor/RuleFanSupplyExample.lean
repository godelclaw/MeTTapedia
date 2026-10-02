import MettapediaFourColor.ActualRuleFanSupply
import MettapediaFourColor.ChainBoundaryGeometry

/-! All three branches occur with the actual source rules in one retained
triangular rotation. These are nonempty geometric examples, not minimal
counterexamples. The chain branches also construct their complete ports. -/

namespace FourColor.RuleFanSupplyExample

open ChainBoundaryExample
open Mettapedia.GraphTheory.FourColor SimpleGraphDartRotation

set_option maxRecDepth 65536

local instance (r : Fin 84) : NeZero (NearLinearRuleData.size r) :=
  ⟨by have := (NearLinearRuleData.headers r).1; omega⟩

def root : Fin 3 → graph.Dart := ![
  ⟨(59, 26), by decide +kernel⟩,
  ⟨(122, 76), by decide +kernel⟩,
  ⟨(94, 159), by decide +kernel⟩]

def leftImages : Fin 3 → NearLinearRuleData.Vertex 2 → Fin 162 :=
  ![![59, 26, 128], ![122, 76, 33], ![94, 159, 37]]

def rightImages : Fin 3 → NearLinearRuleData.Vertex 4 → Fin 162 :=
  ![![59, 26, 58, 3], ![122, 76, 124, 121], ![94, 159, 95, 10]]

theorem left_candidate (k : Fin 3) :
    RuleMatcher.candidate rotation 2 (root k) = leftImages k := by
  funext i
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem right_candidate (k : Fin 3) :
    RuleMatcher.candidate rotation 4 (root k) = rightImages k := by
  funext i
  fin_cases k <;> fin_cases i <;> decide +kernel

/-- Each instance satisfies every adjacency, degree and cyclic rule constraint. -/
theorem observations (k : Fin 3) :
    RuleMatcher.check rotation 2 (root k) = true ∧
    RuleMatcher.check rotation 4 (root k) = true ∧
    graph.degree (root k).fst = 6 ∧
    graph.degree (RuleMatcher.candidate rotation 4 (root k) 2) = 5 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold RuleMatcher.check
    rw [left_candidate]
    fin_cases k <;> decide +kernel
  · unfold RuleMatcher.check
    rw [right_candidate]
    fin_cases k <;> decide +kernel
  · fin_cases k <;> decide +kernel
  · rw [right_candidate]
    fin_cases k <;> decide +kernel

theorem free_degrees (k : Fin 3) :
    graph.degree (RuleFanSupply.firstFree rotation (root k)) = (![5, 6, 6] : Fin 3 → ℕ) k ∧
    graph.degree (RuleFanSupply.secondFree rotation (root k)) = (![6, 5, 6] : Fin 3 → ℕ) k := by
  fin_cases k <;> decide +kernel

theorem fixed (k : Fin 3) : RuleFanSupply.Fixed rotation (root k) :=
  RuleFanSupply.fixed_of_checks rotation cyclic (root k) (observations k).1
    (observations k).2.1 (observations k).2.2.1 (observations k).2.2.2

theorem diamond : RulePairDiamond.MixedAt rotation (RuleFanSupply.start rotation (root 0)).symm :=
  RuleFanSupply.mixed rotation triangular (root 0) (fixed 0) (free_degrees 0).1

theorem eight_word : ∀ n : Fin 4,
    graph.degree (ChainFanRecognition.walk rotation
      (RuleFanSupply.start rotation (root 1)) n.val).snd =
      ChainFanRecognition.word n :=
  RuleFanSupply.eight_word rotation (root 1) (fixed 1) (free_degrees 1).1 (free_degrees 1).2

theorem nine_word : ∀ n : Fin 4,
    graph.degree (ChainFanRecognition.walk rotation
      (RuleFanSupply.start rotation (root 2)) n.val).snd =
      ExtendedChainCore.word n :=
  RuleFanSupply.nine_word rotation (root 2) (fixed 2) (free_degrees 2).1 (free_degrees 2).2

def eightReading : ChainCoreReading.Reading rotation :=
  ChainFanRecognition.reading rotation triangular (RuleFanSupply.start rotation (root 1))
    (by decide +kernel) eight_word

def nineReading : ExtendedChainCore.Reading rotation :=
  ExtendedChainCore.of_word triangular (RuleFanSupply.start rotation (root 2))
    (by decide +kernel) nine_word

theorem eight_induced : ∀ i j, graph.Adj (eightReading.map i) (eightReading.map j) →
    ThreeTriangleFan.core.Adj i j := by decide +kernel

theorem nine_induced : ∀ i j, graph.Adj (nineReading.map i) (nineReading.map j) →
    ThreeTriangleFan.core.Adj i j := by decide +kernel

def eightOccurrence : NearLinearChainOccurrence.Occurrence rotation :=
  ChainCoreOccurrence.occurrence eightReading triangular cyclic eight_induced

def nineOccurrence : ExtendedChainOccurrence.Occurrence rotation :=
  ExtendedChainRecognition.occurrence nineReading triangular cyclic nine_induced

end FourColor.RuleFanSupplyExample
