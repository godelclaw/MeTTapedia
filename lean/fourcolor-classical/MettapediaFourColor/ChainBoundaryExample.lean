import MettapediaFourColor.ChainBoundaryGeometry

/-! Continue an actual charge view to a chain crossing both original
radius-two boundaries. Flatness, sphericality and absence of other local
cores are checked separately by the program audit. -/

namespace FourColor.ChainBoundaryExample

open Mettapedia.GraphTheory.FourColor SimpleGraphDartRotation
open ChainCoreReading LocalCoverageAssembly

set_option maxRecDepth 65536
set_option maxHeartbeats 0

def start : graph.Dart := ⟨(7, 81), by decide +kernel⟩

theorem center_degree : graph.degree start.fst = 6 := by decide +kernel

theorem neighbor_word : ∀ n : Fin 4,
    graph.degree (ChainFanRecognition.walk rotation start n.val).snd =
      ChainFanRecognition.word n := by decide +kernel

def reading : Reading rotation :=
  ChainFanRecognition.reading rotation triangular start center_degree neighbor_word

theorem core_images : ∀ i : Fin 5, reading.map i = (![79, 7, 78, 77, 81] : Fin 5 → Fin 162) i :=
  by decide +kernel

theorem induced : ∀ i j, graph.Adj (reading.map i) (reading.map j) → core.Adj i j :=
  by decide +kernel

def occurrence : NearLinearChainOccurrence.Occurrence rotation :=
  ChainCoreOccurrence.occurrence reading triangular cyclic induced

/-- The recognition centre is reached through actual edges, without a
separately supplied occurrence or choices of boundary images. -/
theorem center_near : reading.map 1 ∈ closedBall graph 112 2 := by
  let q : graph.Walk (81 : Fin 162) (7 : Fin 162) := .cons (by decide +kernel) .nil
  let p : graph.Walk (112 : Fin 162) (7 : Fin 162) := .cons (by decide +kernel) q
  have h := p.edist_le
  change graph.edist 112 7 ≤ 2
  simpa [p, q] using h

/-- Every reconstructed port stays in the enlarged view. -/
theorem complete_patch_near (v : Fin 13) :
    ChainCoreCompletion.vertex reading v ∈ closedBall graph 112 4 :=
  ball_recenter graph center_near (ChainCoreCompletion.vertex_near reading v)

/-- The fourth observed neighbour lies beyond both original radius-two balls. -/
theorem crosses_both_boundaries :
    (79 : Fin 162) ∉ closedBall graph 112 2 ∧
    (79 : Fin 162) ∉ closedBall graph 16 2 := by
  have far (c : Fin 162) (hne : c ≠ 79) (hn : ¬ graph.Adj c 79)
      (hc : ¬ ∃ w, graph.Adj c w ∧ graph.Adj 79 w) :
      (79 : Fin 162) ∉ closedBall graph c 2 := by
    intro h
    change graph.edist c 79 ≤ 2 at h
    have notOne : ¬ graph.edist c 79 ≤ 1 := by
      rw [SimpleGraph.edist_le_one_iff_adj_or_eq]
      exact not_or_intro hn hne
    have two : graph.edist c 79 = 2 := by
      exact le_antisymm h (ENat.natCast_add_one_le_iff.mpr (lt_of_not_ge notOne))
    exact hc (SimpleGraph.edist_eq_two_iff.mp two).2.2
  constructor <;> apply far <;> decide +kernel

local instance (r : Fin 84) : NeZero (NearLinearRuleData.size r) :=
  ⟨by have := (NearLinearRuleData.headers r).1; omega⟩

/-- The rule supplies the first three neighbours of the same chain. -/
def rule : RuleChainRecognition.View rotation where
  vertex := ![81, 112, 77, 7, 78]
  edge := by
    change ∀ i j : Fin 5, j.val + 1 ∈ NearLinearRuleData.neighbors 6 i →
      (![81, 112, 77, 7, 78] j : Fin 162) ∈ star (![81, 112, 77, 7, 78] i)
    decide +kernel
  degree := by decide +kernel
  turn := by decide +kernel

theorem rule_guards :
    graph.degree (rule.vertex 0) = 5 ∧ graph.degree (rule.vertex 2) = 6 ∧
    graph.degree (rule.vertex 3) = 6 ∧
    graph.degree (RuleChainRecognition.continuation rule) = 5 := by decide +kernel

def continued_reading : Reading rotation :=
  RuleChainRecognition.reading triangular rule rule_guards.1 rule_guards.2.1
    rule_guards.2.2.1 rule_guards.2.2.2

/-- The charge view and the direct degree-word view choose identical
vertices, including the observation beyond the original boundary. -/
theorem continued_core : ∀ i : Fin 5, continued_reading.map i = reading.map i := by
  decide +kernel

theorem continued_patch_near (v : Fin 13) :
    ChainCoreCompletion.vertex continued_reading v ∈ closedBall graph 112 4 :=
  RuleChainRecognition.complete_patch_near triangular rule rule_guards.1
    rule_guards.2.1 rule_guards.2.2.1 rule_guards.2.2.2 v

end FourColor.ChainBoundaryExample
