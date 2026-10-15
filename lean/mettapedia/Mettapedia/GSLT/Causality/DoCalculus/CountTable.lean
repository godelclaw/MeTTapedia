import Mettapedia.GSLT.Causality.DoCalculus.ReviseRule

/-!
# Four graphs: counts, a point or an interval, one experimental pool

Smoking and the door graph are identified, so the interventional state is a
point read off the adjustment counts, and one experimental `true` revises
that point. The bow and the child-bow are hedges: the revision rule does not
fire, the interventional value is the credal interval, and an experimental
`true` pooled with each model's own interventional counts leaves the two
models apart.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Causality.DoCalculus

open Mettapedia.Logic.EvidenceStateInsufficiency
open scoped ENNReal

/-- Smoking: observational `⟨9, 3⟩`, front-door point `⟨3, 2⟩`, pooled with
one experimental success to `⟨4, 2⟩`. -/
theorem smoking_count_row :
    identify smokeGraph 2 smokeEnum {Smoke.u} {Smoke.c} smokeS (∅ : Finset Smoke) =
        .doFree frontDoorExpr ∧
      smokeObsCounts = ⟨9, 3⟩ ∧
      frontDoorCounts = ⟨3, 2⟩ ∧
      (poolInterventional frontDoorState true).observational = ⟨9, 3⟩ ∧
      (poolInterventional frontDoorState true).interventional = ⟨4, 2⟩ := by
  have hlic := front_door_identify_count_licence true
  refine ⟨hlic.1, smokeObsCounts_canonical, frontDoorCounts_canonical, ?_, ?_⟩
  · rw [hlic.2.2.2.2, smokeObsCounts_canonical]
  · rw [hlic.2.2.2.1, frontDoorCounts_canonical]
    decide

/-- Door: observational `⟨8, 1⟩`, back-door point `⟨1, 1⟩`, pooled with one
experimental success to `⟨2, 1⟩`. -/
theorem door_count_row :
    identify doorGraph 2 doorEnum (∅ : Finset Door) doorY doorX (∅ : Finset Door) =
        .doFree (backDoorShape doorX doorY doorZ) ∧
      doorObsCounts = ⟨8, 1⟩ ∧
      backDoorCounts = ⟨1, 1⟩ ∧
      (poolInterventional backDoorState true).observational = ⟨8, 1⟩ ∧
      (poolInterventional backDoorState true).interventional = ⟨2, 1⟩ := by
  have hlic := back_door_identify_count_licence true
  refine ⟨hlic.1, doorObsCounts_canonical, backDoorCounts_canonical, ?_, ?_⟩
  · rw [hlic.2.2.2.2, doorObsCounts_canonical]
  · rw [hlic.2.2.2.1, backDoorCounts_canonical]
    decide

/-- Bow: the revision rule stays shut, the interval is `[1/2, 1]`, and one
experimental success pooled with each model stays `⟨2, 0⟩` or `⟨2, 1⟩`. -/
theorem bow_count_row :
    identificationDischarged bowGraph 2 bowEnum {Bow.u} {Bow.y} {Bow.x}
        (∅ : Finset Bow) = false ∧
      bowObsCounts = ⟨1, 0⟩ ∧
      bowCredal.lower = 1 / 2 ∧
      bowCredal.upper = 1 ∧
      bowModel1Counts.revise true = ⟨2, 0⟩ ∧
      bowModel2Counts.revise true = ⟨2, 1⟩ ∧
      bowModel1Counts.revise true ≠ bowModel2Counts.revise true ∧
      bowDoMass bowCPT1 true = 1 ∧
      bowDoMass bowCPT2 true = (2 : ℝ≥0∞)⁻¹ := by
  refine ⟨revise_rule_misses_bow, bow_observed_cells.2.2, bow_credal_endpoints.1,
    bow_credal_endpoints.2, ?_, ?_, ?_, bow_do_model1, bow_do_model2⟩
  · decide
  · decide
  · decide

/-! ## Child bow: `identify` returns the hedge -/

def childBowEnum : List ChildBow :=
  [ChildBow.u, ChildBow.x, ChildBow.y, ChildBow.d]

theorem child_bow_parents_fail :
    parentsIn childBowGraph {ChildBow.x} (∅ : Finset ChildBow) (∅ : Finset ChildBow) =
      false := by
  decide

theorem child_bow_delete_fail :
    deleteOK childBowGraph {ChildBow.y} {ChildBow.x} (∅ : Finset ChildBow) = false := by
  decide

theorem child_bow_no_front_mediator :
    findVertex childBowEnum (fun v =>
      outsideQuery {ChildBow.u} {ChildBow.y} {ChildBow.x} v &&
        frontDoorReady childBowGraph {ChildBow.x} {v} {ChildBow.y}) = none := by
  decide

theorem child_bow_no_napkin :
    findNapkin childBowGraph childBowEnum {ChildBow.u} {ChildBow.y} {ChildBow.x} = none := by
  decide

theorem child_bow_no_back_covariate :
    findVertex childBowEnum (fun v =>
      outsideQuery {ChildBow.u} {ChildBow.y} {ChildBow.x} v &&
        backDoorReady childBowGraph {ChildBow.x} {v} {ChildBow.y}) = none := by
  decide

theorem child_bow_misses_forward :
    missesForward childBowGraph {ChildBow.x}
      ({ChildBow.y} ∪ (∅ : Finset ChildBow)) = false := by
  decide

theorem child_bow_pair_vertices :
    ((bowPair childBowGraph childBowEnum {ChildBow.u} {ChildBow.y} {ChildBow.x}).map
      fun hit => (hit.y, hit.x)) = some (ChildBow.y, ChildBow.x) := by
  decide

/-- ID returns the child-bow hedge: trunk `{Y}`, canopy `{Y, X}`. -/
theorem child_bow_id_returns_hedge :
    match identify childBowGraph 2 childBowEnum {ChildBow.u} {ChildBow.y} {ChildBow.x}
        (∅ : Finset ChildBow) with
    | .hedge witness =>
        witness.trunk = {ChildBow.y} ∧ witness.canopy = {ChildBow.y, ChildBow.x}
    | .doFree _ => False := by
  have hparents :
      ¬ parentsIn childBowGraph {ChildBow.x} (∅ : Finset ChildBow) (∅ : Finset ChildBow) =
          true := by
    simp [child_bow_parents_fail]
  have hdelete :
      ¬ deleteOK childBowGraph {ChildBow.y} {ChildBow.x} (∅ : Finset ChildBow) = true := by
    simp [child_bow_delete_fail]
  have hx : ChildBow.x ∈ ({ChildBow.x} : Finset ChildBow) := by simp
  have hyout : ChildBow.y ∉ ({ChildBow.x} : Finset ChildBow) := by simp
  have hcompute :
      identify childBowGraph 2 childBowEnum {ChildBow.u} {ChildBow.y} {ChildBow.x}
          (∅ : Finset ChildBow) =
        .hedge (hedgeOfPair ChildBow.y ChildBow.x {ChildBow.x} hx hyout) := by
    unfold identify
    split
    · rename_i hzero
      cases hzero
    · rw [if_neg hparents, if_neg hdelete, if_pos (rfl : (∅ : Finset ChildBow) = ∅)]
      rw [child_bow_no_front_mediator, child_bow_no_napkin, child_bow_no_back_covariate]
      have hmiss :
          ¬ missesForward childBowGraph {ChildBow.x}
              ({ChildBow.y} ∪ (∅ : Finset ChildBow)) = true := by
        rw [child_bow_misses_forward]
        decide
      rw [if_neg hmiss]
      cases hpair : bowPair childBowGraph childBowEnum {ChildBow.u} {ChildBow.y}
          {ChildBow.x} with
      | none =>
          have hdata := child_bow_pair_vertices
          simp [hpair] at hdata
      | some hit =>
          have hdata := child_bow_pair_vertices
          simp [hpair] at hdata
          rcases hdata with ⟨hy, hxhit⟩
          dsimp
          simp [hy, hxhit, hedgeOfPair]
  rw [hcompute]
  unfold hedgeOfPair
  constructor <;> rfl

theorem child_bow_revision_does_not_fire :
    identificationDischarged childBowGraph 2 childBowEnum {ChildBow.u} {ChildBow.y}
        {ChildBow.x} (∅ : Finset ChildBow) = false := by
  have hhedge := child_bow_id_returns_hedge
  cases hrun : identify childBowGraph 2 childBowEnum {ChildBow.u} {ChildBow.y}
      {ChildBow.x} (∅ : Finset ChildBow) with
  | doFree _ =>
      simp [hrun] at hhedge
  | hedge _ =>
      simp [identificationDischarged, hrun]

/-- Child bow: the same interval and the same split after one experimental
success, and the revision rule does not fire. -/
theorem child_bow_count_row :
    identificationDischarged childBowGraph 2 childBowEnum {ChildBow.u} {ChildBow.y}
        {ChildBow.x} (∅ : Finset ChildBow) = false ∧
      childBowObsCounts = ⟨1, 0⟩ ∧
      childBowCredal.lower = 1 / 2 ∧
      childBowCredal.upper = 1 ∧
      childBowModel1Counts.revise true = ⟨2, 0⟩ ∧
      childBowModel2Counts.revise true = ⟨2, 1⟩ ∧
      childBowModel1Counts.revise true ≠ childBowModel2Counts.revise true ∧
      childBowDoMass childBowCPT1 true = 1 ∧
      childBowDoMass childBowCPT2 true = (2 : ℝ≥0∞)⁻¹ := by
  refine ⟨child_bow_revision_does_not_fire, child_bow_credal_endpoints.2.2,
    child_bow_credal_endpoints.1, child_bow_credal_endpoints.2.1, ?_, ?_, ?_,
    childBow_do_model1, childBow_do_model2⟩
  · decide
  · decide
  · decide

end Mettapedia.GSLT.Causality.DoCalculus
