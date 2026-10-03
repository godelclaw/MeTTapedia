import MettapediaFourColor.JointTripodRuleSupply
import MettapediaFourColor.ChainBoundaryGeometry

/-! Three joint matches in an existing triangular rotation reconstruct the
entire tripod boundary. This finite example is not a minimal counterexample;
it witnesses the geometric reduction guard, not universal flat coverage. -/

namespace FourColor.JointTripodRuleExample

open Mettapedia.GraphTheory.FourColor SimpleGraphDartRotation
open ChainBoundaryExample NearLinearCharge

set_option maxRecDepth 65536

local instance (r : Fin 84) : NeZero (NearLinearRuleData.size r) :=
  ⟨by have := (NearLinearRuleData.headers r).1; omega⟩

def root : graph.Dart := ⟨(20, 47), by decide +kernel⟩
def adjacent : graph.Dart := (rotation.vertexRotation root.symm).symm

def capImages : NearLinearRuleData.Vertex 3 → Fin 162 := ![20,47,105,113]
def leftImages : NearLinearRuleData.Vertex 1 → Fin 162 := ![20,47,51]
def rightImages : NearLinearRuleData.Vertex 2 → Fin 162 := ![105,47,12]

set_option maxHeartbeats 0 in
-- Check every source edge, degree constraint and cyclic turn.
theorem cap_fits : RuleMatcher.Fits rotation 3 capImages := by decide +kernel

set_option maxHeartbeats 0 in
-- Check every source edge, degree constraint and cyclic turn.
theorem left_fits : RuleMatcher.Fits rotation 1 leftImages := by decide +kernel

set_option maxHeartbeats 0 in
-- Check every source edge, degree constraint and cyclic turn.
theorem right_fits : RuleMatcher.Fits rotation 2 rightImages := by decide +kernel

def cap : Occurrence rotation 3 :=
  RuleMatcher.occurrenceOfFits rotation capImages cap_fits
def left : Occurrence rotation 1 :=
  RuleMatcher.occurrenceOfFits rotation leftImages left_fits
def right : Occurrence rotation 2 :=
  RuleMatcher.occurrenceOfFits rotation rightImages right_fits

/-- Rooted matching, all degrees and the shared intermediate sender are checked. -/
theorem observations :
    RuleMatcher.check rotation 1 root = true ∧
    RuleMatcher.check rotation 3 root = true ∧
    RuleMatcher.check rotation 2 adjacent = true ∧
    graph.degree root.fst = 6 ∧ graph.degree root.snd = 7 ∧
    graph.degree adjacent.fst = 6 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (RuleMatcher.check_iff rotation root).mpr ⟨left, rfl, rfl⟩
  · exact (RuleMatcher.check_iff rotation root).mpr ⟨cap, rfl, rfl⟩
  · exact (RuleMatcher.check_iff rotation adjacent).mpr
      ⟨right, by decide +kernel, by decide +kernel⟩
  all_goals decide +kernel

theorem align_left_source : left.vertex 0 = cap.vertex 0 := by decide +kernel
theorem align_left_target : left.vertex 1 = cap.vertex 1 := by decide +kernel
theorem align_right_source : right.vertex 0 = cap.vertex 2 := by decide +kernel
theorem align_right_target : right.vertex 1 = cap.vertex 1 := by decide +kernel

def reading : FourTriangleCore.Reading 1 rotation :=
  JointTripodRuleSupply.reading rotation cap left right
    align_left_source align_left_target align_right_source align_right_target triangular

theorem degrees : ∀ i, graph.degree (reading.map i) = FourTriangleCore.degree 1 i :=
  JointTripodRuleSupply.degrees rotation cap left right
    align_left_source align_left_target align_right_source align_right_target triangular
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem core_images : ∀ i, reading.map i =
    (![113,105,20,47,51,12] : Fin 6 → Fin 162) i := by decide +kernel

theorem injective : Function.Injective reading.map := by decide +kernel

theorem induced : ∀ i j, graph.Adj (reading.map i) (reading.map j) →
    (FourTriangleCore.core 1).Adj i j := by decide +kernel

/-- The ten exterior ports are constructed from these same rule witnesses. -/
def occurrence : FourTriangleOccurrence.Occurrence 1 rotation :=
  FourTriangleCompletedOccurrence.occurrence 1 reading degrees triangular cyclic injective induced

end FourColor.JointTripodRuleExample
