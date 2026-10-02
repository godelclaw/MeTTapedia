import MettapediaFourColor.RulePairBudget

/-! The five-valent second sender exposes a mixed diamond on a different
edge of the retained right rule. Its two flanks are prescribed actual turns;
no independent occurrence search or new colouring certificate is required. -/

namespace FourColor.RulePairResidual

open Mettapedia.GraphTheory.FourColor SimpleGraphDartRotation
open NearLinearRuleData NearLinearCharge RuleMatcher RulePairDiamond

local instance (r : Fin 84) : NeZero (size r) :=
  ⟨by have := (headers r).1; omega⟩

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}
  [DecidableRel G.Adj] [G.LocallyFinite] {rotation : Data G}

/-- Reroot the right reading at the shared vertex and its remaining corner. -/
def rightEdge (y : Right rotation) : G.Dart :=
  ⟨(y.vertex 2, y.vertex 3), y.edge 2 3 (by decide +kernel)⟩

omit [DecidableEq V] [DecidableRel G.Adj] in
/-- The right rule already specifies both flanks of the rerooted edge. -/
theorem right_flanks (y : Right rotation) (sender : G.degree (y.vertex 0) = 5) :
    G.degree (rotation.vertexRotation (rightEdge y)).snd = 5 ∧
    G.degree (rotation.vertexRotation.symm (rightEdge y)).snd = 5 := by
  have hn : rotation.vertexRotation (rightEdge y) =
      ⟨(y.vertex 2, y.vertex 4), y.edge 2 4 (by decide +kernel)⟩ :=
    y.turn 2 3 4 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  have hp : rotation.vertexRotation.symm (rightEdge y) =
      ⟨(y.vertex 2, y.vertex 0), y.edge 2 0 (by decide +kernel)⟩ := by
    apply rotation.vertexRotation.injective
    rw [Equiv.apply_symm_apply]
    exact (y.turn 2 0 3 (by decide +kernel) (by decide +kernel) (by decide +kernel)).symm
  have h := y.degree 4
  rw [show lower 5 4 = 5 from by decide +kernel,
    show upper 5 4 = 5 from by decide +kernel] at h
  constructor
  · rw [hn]
    change G.degree (y.vertex 4) = 5
    omega
  · rw [hp]
    exact sender

omit [DecidableEq V] [DecidableRel G.Adj] in
/-- One full right reading supplies a mixed diamond under these three
degree observations. Cyclic closure has already done its work upstream. -/
theorem right_mixed (y : Right rotation)
    (sender : G.degree (y.vertex 0) = 5)
    (shared : G.degree (y.vertex 2) = 5)
    (outer : G.degree (y.vertex 3) = 6) : MixedAt rotation (rightEdge y) := by
  obtain ⟨hn, hp⟩ := right_flanks y sender
  exact ⟨shared, outer, hn, hp⟩

theorem right_mixed_of_check (d : G.Dart) (right : check rotation 5 d = true)
    (sender : G.degree d.fst = 5)
    (shared : G.degree (candidate rotation 5 d 2) = 5)
    (outer : G.degree (candidate rotation 5 d 3) = 6) :
    ∃ e : G.Dart, MixedAt rotation e := by
  obtain ⟨y, ys, yt⟩ := (check_iff rotation d).mp right
  refine ⟨rightEdge y, right_mixed y (ys ▸ sender) ?_ ?_⟩
  · rwa [candidate_eq rotation d y ys yt] at shared
  · rwa [candidate_eq rotation d y ys yt] at outer

end FourColor.RulePairResidual
