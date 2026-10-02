import MettapediaFourColor.RuleFanCharge
import MettapediaFourColor.ActualRuleFanSupply

/-!
# A flat second centre forces a third, adjacent centre

In the shared rule fan, suppose the first free neighbour is a flat seven
and the other free neighbour is five. The signed fan budget forces the
seven to have a high-degree neighbour. The actual minimal map's facial
triangle theorem excludes the original receiver as that neighbour.
This is a non-return result for one explicit overlap, not a termination
theorem for arbitrary walks of centres.
-/

namespace FourColor.ActualRuleFanCharge

open Mettapedia.GraphTheory.FourColor SimpleGraphDartRotation
open GoertzelV24TwoEdgeCutMinimality
open ActualRulePairDiamond (graph rotation)
open RuleFanSupply
open ChainFanRecognition (walk walk_fst walk_next)

noncomputable section
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]
  (original : Data G) (minimal : GraphBackedVertexMinimalTaitCounterexample original)

local instance (r : Fin 84) : NeZero (NearLinearRuleData.size r) :=
  ⟨by have := (NearLinearRuleData.headers r).1; omega⟩

/-- A chord from the receiver to the opposite free position would form
a nonfacial triangle. The actual minimal-map theorem excludes it. -/
theorem opposite_not_adjacent (d : (graph original minimal).Dart)
    (fixed : Fixed (rotation original minimal) d)
    (high : 7 ≤ (graph original minimal).degree d.snd)
    (seven : (graph original minimal).degree (firstFree (rotation original minimal) d) = 7)
    (five : (graph original minimal).degree (secondFree (rotation original minimal) d) = 5) :
    ¬ (graph original minimal).Adj d.snd (firstFree (rotation original minimal) d) := by
  let e := walk (rotation original minimal) d 3
  have es : e.fst = d.fst := walk_fst _ _ _
  have adjacent : (graph original minimal).Adj d.fst e.snd := by simpa only [es] using e.adj
  intro chord
  rcases MinimalExceptionalEmbedding.triangle_facial original minimal d.adj chord adjacent.symm with
    first | second
  · obtain ⟨_, he, step⟩ := first
    have ee : (⟨(d.fst, firstFree (rotation original minimal) d), he⟩ :
        (graph original minimal).Dart) = e := by
      apply SimpleGraph.Dart.ext
      exact Prod.ext es.symm rfl
    rw [ee] at step
    have eq : (rotation original minimal).vertexRotation d = e := step
    have deg := congrArg (fun x : (graph original minimal).Dart =>
      (graph original minimal).degree x.snd) eq
    have firstFive := fixed.first
    change (graph original minimal).degree
      ((rotation original minimal).vertexRotation d).snd = 5 at firstFive
    change (graph original minimal).degree e.snd = 7 at seven
    omega
  · obtain ⟨he, _, step⟩ := second
    have ee : (⟨(d.fst, firstFree (rotation original minimal) d), he⟩ :
        (graph original minimal).Dart) = e := by
      apply SimpleGraph.Dart.ext
      exact Prod.ext es.symm rfl
    rw [ee] at step
    have eq : (rotation original minimal).vertexRotation e = d := step
    have deg := congrArg (fun x : (graph original minimal).Dart =>
      (graph original minimal).degree x.snd) eq
    change (graph original minimal).degree
      ((rotation original minimal).vertexRotation (walk (rotation original minimal) d 3)).snd =
        (graph original minimal).degree d.snd at deg
    rw [walk_next] at deg
    change (graph original minimal).degree (walk (rotation original minimal) d 4).snd =
      (graph original minimal).degree d.snd at deg
    change (graph original minimal).degree (walk (rotation original minimal) d 4).snd = 5 at five
    omega

/-- Exact rules and flatness force a third centre, adjacent to the second
and distinct from the original one. Every retained observation is local. -/
theorem third_center (d : (graph original minimal).Dart)
    (left : RuleMatcher.check (rotation original minimal) 2 d = true)
    (right : RuleMatcher.check (rotation original minimal) 4 d = true)
    (six : (graph original minimal).degree d.fst = 6)
    (shared : (graph original minimal).degree
      (RuleMatcher.candidate (rotation original minimal) 4 d 2) = 5)
    (seven : (graph original minimal).degree (firstFree (rotation original minimal) d) = 7)
    (five : (graph original minimal).degree (secondFree (rotation original minimal) d) = 5)
    (flat : NearLinearCharge.finalCharge (rotation original minimal)
      (firstFree (rotation original minimal) d) = 0) :
    ∃ w, w ≠ d.snd ∧ w ≠ firstFree (rotation original minimal) d ∧
      (graph original minimal).Adj (firstFree (rotation original minimal) d) w ∧
      w ∈ LocalCoverageAssembly.closedBall (graph original minimal) d.snd 3 ∧
      7 ≤ (graph original minimal).degree w := by
  have fixed := fixed_of_checks (rotation original minimal)
    (MinimalExceptionalEmbedding.cyclic original minimal) d left right six shared
  let e := walk (rotation original minimal) d 3
  have es : e.fst = d.fst := walk_fst _ _ _
  have wing := RuleFanCharge.wings_at_first_free d fixed five
  obtain ⟨w, adj, highw⟩ := RuleFanCharge.flat_has_high_neighbor
    (MinimalExceptionalEmbedding.cyclic original minimal)
    (MinimalExceptionalEmbedding.triangular original minimal) e wing seven flat (by
      intro v hv
      exact ActualRuleFanSupply.degree_five original minimal ⟨(v,e.snd),hv.symm⟩)
  have high : 7 ≤ (graph original minimal).degree d.snd := by
    obtain ⟨x, xs, xt⟩ := (RuleMatcher.check_iff (rotation original minimal) d).mp left
    have h := (x.degree 1).1
    rw [show NearLinearRuleData.lower 2 1 = 7 from by decide +kernel] at h
    exact xt ▸ h
  have notadj := opposite_not_adjacent original minimal d fixed high seven five
  refine ⟨w, ?_, adj.ne.symm, adj, ?_, highw⟩
  · intro eq; subst w
    exact notadj adj.symm
  · have sw : (graph original minimal).Adj d.fst e.snd := by simpa only [es] using e.adj
    let path : (graph original minimal).Walk d.snd w :=
      .cons d.adj.symm (.cons sw (.cons adj .nil))
    simpa [LocalCoverageAssembly.closedBall, path] using path.edist_le

end
end FourColor.ActualRuleFanCharge
