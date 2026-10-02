import MettapediaFourColor.ChainFanRecognition
import MettapediaFourColor.RuleMatcher

/-!
# Continue a charge-rule reading across its observation boundary

The reflected fourth discharging rule retains three successive neighbours
of its outer vertex. When their degrees are 5,6,5 and the outer degree is
six, one further degree-five observation completes the proved chain word.
The complete reconstructed patch lies within radius four of the receiver.
The actual minimal-map consumer excludes that continuation through the
existing strict reduction and reconstruction; no new repair table is used.
-/

namespace FourColor.RuleChainRecognition

open Mettapedia.GraphTheory.FourColor SimpleGraphDartRotation
open NearLinearRuleData NearLinearCharge ExceptionalOverlap LocalCoverageAssembly

local instance (r : Fin 84) : NeZero (size r) :=
  ⟨by have := (headers r).1; omega⟩

variable {V : Type*} {G : SimpleGraph V} [G.LocallyFinite] {rotation : Data G}

abbrev View (rotation : Data G) := Occurrence rotation (6 : Fin 84)

def start (y : View rotation) : G.Dart :=
  ⟨(y.vertex 3, y.vertex 0), y.edge 3 0 (by decide +kernel)⟩

def tip (y : View rotation) : G.Dart :=
  ⟨(y.vertex 3, y.vertex 4), y.edge 3 4 (by decide +kernel)⟩

/-- The next actual vertex is retained, rather than replaced by an
independent possibility for its colour or degree. -/
def continuation (y : View rotation) : V :=
  (rotation.vertexRotation (tip y)).snd

theorem step_one (y : View rotation) :
    rotation.vertexRotation (start y) =
      ⟨(y.vertex 3, y.vertex 2), y.edge 3 2 (by decide +kernel)⟩ :=
  y.turn 3 0 2 (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem step_two (y : View rotation) :
    rotation.vertexRotation (rotation.vertexRotation (start y)) = tip y := by
  rw [step_one]
  exact y.turn 3 2 4 (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem neighbor_word (y : View rotation)
    (sender : G.degree (y.vertex 0) = 5)
    (shared : G.degree (y.vertex 2) = 6)
    (next : G.degree (continuation y) = 5) :
    ∀ n : Fin 4, G.degree (ChainFanRecognition.walk rotation (start y) n.val).snd =
      ChainFanRecognition.word n := by
  have five : G.degree (y.vertex 4) = 5 := by
    have h := y.degree 4
    rw [show lower 6 4 = 5 from by decide +kernel,
      show upper 6 4 = 5 from by decide +kernel] at h
    omega
  intro n
  fin_cases n
  · exact sender
  · change G.degree (rotation.vertexRotation (start y)).snd = 6
    rw [step_one]
    exact shared
  · change G.degree (rotation.vertexRotation (rotation.vertexRotation (start y))).snd = 5
    rw [step_two]
    exact five
  · change G.degree (rotation.vertexRotation
      (rotation.vertexRotation (rotation.vertexRotation (start y)))).snd = 5
    rw [step_two]
    exact next

def reading (tri : Triangular rotation) (y : View rotation)
    (sender : G.degree (y.vertex 0) = 5)
    (shared : G.degree (y.vertex 2) = 6)
    (outer : G.degree (y.vertex 3) = 6)
    (next : G.degree (continuation y) = 5) : ChainCoreReading.Reading rotation :=
  ChainFanRecognition.reading rotation tri (start y) outer (neighbor_word y sender shared next)

/-- The extra observation lies within one further step of the radius-two rule view. -/
theorem continuation_near (y : View rotation) :
    continuation y ∈ closedBall G (y.vertex 1) 3 := by
  have outer : y.vertex 3 ∈ closedBall G (y.vertex 1) 2 :=
    y.vertex_near 1 (by decide +kernel) 3
  apply ball_recenter G (b := 1) outer
  have first : (rotation.vertexRotation (tip y)).fst = y.vertex 3 :=
    rotation.vertexRotation_fst (tip y)
  let p : G.Walk (y.vertex 3) (continuation y) :=
    .cons (by simpa only [first, continuation] using
      (rotation.vertexRotation (tip y)).adj) .nil
  simpa [closedBall, p] using p.edist_le

/-- The same retained rule witness bounds all reconstructed ports. -/
theorem complete_patch_near (tri : Triangular rotation) (y : View rotation)
    (sender : G.degree (y.vertex 0) = 5)
    (shared : G.degree (y.vertex 2) = 6)
    (outer : G.degree (y.vertex 3) = 6)
    (next : G.degree (continuation y) = 5) (v : Fin 13) :
    ChainCoreCompletion.vertex (reading tri y sender shared outer next) v ∈
      closedBall G (y.vertex 1) 4 := by
  have near : (reading tri y sender shared outer next).map 1 ∈
      closedBall G (y.vertex 1) 2 := by
    change y.vertex 3 ∈ closedBall G (y.vertex 1) 2
    exact y.vertex_near 1 (by decide +kernel) 3
  exact ball_recenter G near (ChainCoreCompletion.vertex_near _ v)

noncomputable section
variable {W : Type*} [Fintype W] [DecidableEq W]
  {H : SimpleGraph W} [DecidableRel H.Adj] (original : Data H)
  (minimal : GoertzelV24TwoEdgeCutMinimality.GraphBackedVertexMinimalTaitCounterexample original)

/-- This boundary branch is excluded by an actual smaller-map colouring
and reconstruction. Zero charge is not needed for this local exclusion. -/
theorem not_continuation_five
    (y : View (MinimalExceptionalEmbedding.rotation original minimal))
    (sender : (MinimalExceptionalEmbedding.graph original minimal).degree (y.vertex 0) = 5)
    (shared : (MinimalExceptionalEmbedding.graph original minimal).degree (y.vertex 2) = 6)
    (outer : (MinimalExceptionalEmbedding.graph original minimal).degree (y.vertex 3) = 6) :
    (MinimalExceptionalEmbedding.graph original minimal).degree (continuation y) ≠ 5 := by
  intro next
  exact ActualChainRecognition.not_in_minimal original minimal
    (reading (MinimalExceptionalEmbedding.triangular original minimal) y sender shared outer next)

end
end FourColor.RuleChainRecognition
