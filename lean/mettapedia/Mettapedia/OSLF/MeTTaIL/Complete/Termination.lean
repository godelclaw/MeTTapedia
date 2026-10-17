import Mettapedia.OSLF.MeTTaIL.Complete.Classes
import Mettapedia.OSLF.MeTTaIL.GeneralEquationReverseBounds
import Mettapedia.OSLF.MeTTaIL.StructuralDescentPlan

/-!
# The search modulo equations finishes

`Classes` explores the source's equality class and runs a deepening lane per job of every member.
This module shows that, for a plan whose rules and equation premises descend structurally, the
search is complete after finitely many rounds, so a state with no step is eventually certified to
have none.

The argument has three parts.

- **Members settle.** Representatives are distinct members of the class and only ever grow. A
  finite class therefore stops growing (`reps_settle`).
- **Every lane finishes.** Rule lanes are bounded by the focus size (`DeepRoot.eventually_complete`);
  equation lanes by the left side's weight under the capture (`EquationJob.lane_eventually_complete`).
- **Fair rounds.** Every lane gets one unit of work per round, so once members have settled, a
  bounded number of further rounds finishes them all.

- `eventually_complete`: with a finite class, the search is complete after finitely many rounds;
- `compiled_eventually_complete`: every accepted compiled plan has finite classes at well-sorted
  sources (`GeneralEquationReverseBounds.compiled_equivalence_universe_iff`);
- `equationFree_eventually_complete`: without equations, a class is its source.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.Complete.Classes

open _root_.Mettapedia.OSLF.MeTTaIL.Syntax GeneralExecutionAdmission

variable (plan : Plan) (bound : List TypeExpr) (expected : TypeExpr)

/-! ## Representatives are distinct members -/

/-- No two representatives share a pattern. -/
def Distinct (reps : List Rep) : Prop := (reps.map Rep.pattern).Nodup

theorem addDiscoveries_distinct (born : Nat) :
    ∀ (found : List Event) (reps : List Rep), Distinct reps → Distinct (addDiscoveries born reps found) := by
  intro found
  induction found with
  | nil => intro reps distinct; exact distinct
  | cons event rest ih =>
    intro reps distinct
    cases event with
    | firing _ => exact ih reps distinct
    | discovery pattern conversions =>
      simp only [addDiscoveries]
      split
      · exact ih reps distinct
      · rename_i absent
        apply ih
        unfold Distinct at distinct ⊢
        rw [List.map_append, List.map_singleton]
        apply List.nodup_append.mpr
        refine ⟨distinct, List.nodup_singleton _, ?_⟩
        intro first inReps second inSingle same
        rw [List.mem_singleton] at inSingle
        subst inSingle same
        obtain ⟨rep, member, rfl⟩ := List.mem_map.mp inReps
        exact absent (List.any_eq_true.mpr ⟨rep, member, by simp⟩)

variable (source : Pattern)

theorem runAt_distinct (work : Nat) : Distinct (runAt plan bound expected source work).reps := by
  induction work with
  | zero => simp [runAt, rounds, begin, Distinct]
  | succ work ih =>
    simp only [runAt, rounds_succ, round_reps]
    exact addDiscoveries_distinct _ _ _ ih

theorem runAt_reps_prefix (work extra : Nat) :
    (runAt plan bound expected source work).reps <+: (runAt plan bound expected source (work + extra)).reps := by
  induction extra with
  | zero => exact List.prefix_refl _
  | succ extra ih =>
    simp only [runAt, ← Nat.add_assoc, rounds_succ, round_reps]
    exact ih.trans (addDiscoveries_prefix _ _ _)

/-- Every representative is a member of the source's class. -/
theorem rep_equivalent {work : Nat} {rep : Rep} (member : rep ∈ (runAt plan bound expected source work).reps) :
    Relation.EqvGen (GeneralOccurrenceSemantics.Equation plan bound expected) source rep.pattern :=
  GeneralOccurrenceSemantics.ConversionPath.equivalent plan bound expected
    ((rounds_reached plan bound expected source work).valid rep member)

/-! ## Members settle -/

/-- A growing list of bounded length stops growing. -/
theorem settle_of_bounded {α : Type} (lists : Nat → List α) (grows : ∀ work extra, lists work <+: lists (work + extra))
    (limit : Nat) (bounded : ∀ work, (lists work).length ≤ limit) :
    ∃ settled, ∀ work, settled ≤ work → lists work = lists settled := by
  suffices measure : ∀ gap start, limit - (lists start).length = gap →
      ∃ settled, ∀ work, settled ≤ work → lists work = lists settled from measure _ 0 rfl
  intro gap
  induction gap using Nat.strong_induction_on with
  | _ gap ih =>
    intro start measured
    by_cases stays : ∀ work, start ≤ work → (lists work).length = (lists start).length
    · refine ⟨start, fun work after => ?_⟩
      obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le after
      exact ((grows start extra).eq_of_length (stays _ after).symm).symm
    · obtain ⟨work, rest⟩ := not_forall.mp stays
      obtain ⟨after, changed⟩ := Classical.not_imp.mp rest
      obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le after
      have longer : (lists start).length < (lists (start + extra)).length :=
        lt_of_le_of_ne (grows start extra).length_le (Ne.symm changed)
      have within := bounded (start + extra)
      exact ih _ (by omega) (start + extra) rfl

/-- **Members settle**, when the class is finite. -/
theorem reps_settle {carrier : List Pattern}
    (finite : ∀ pattern, Relation.EqvGen (GeneralOccurrenceSemantics.Equation plan bound expected) source pattern →
      pattern ∈ carrier) :
    ∃ settled, ∀ work, settled ≤ work →
      (runAt plan bound expected source work).reps = (runAt plan bound expected source settled).reps := by
  apply settle_of_bounded (fun work => (runAt plan bound expected source work).reps)
    (runAt_reps_prefix plan bound expected source) carrier.length
  intro work
  have within : ∀ pattern ∈ (runAt plan bound expected source work).reps.map Rep.pattern, pattern ∈ carrier := by
    intro pattern member
    obtain ⟨rep, inReps, rfl⟩ := List.mem_map.mp member
    exact finite _ (rep_equivalent plan bound expected source inReps)
  have length := ((runAt_distinct plan bound expected source work).subperm within).length_le
  simpa only [List.length_map] using length

/-! ## Every lane finishes -/

/-- The plan's rules descend structurally, and so does every equation's premise list. -/
def Descends : Prop :=
  StructuralDescent.checkEnvironment (GeneralPlanEnvironment.environment plan) = true ∧
    ∀ equation ∈ plan.equations, StructuralDescent.checkPremises equation.rule equation.binding.spec 0
      equation.rule.premises = true

/-- The equation of a lane is one of the plan's. -/
theorem lane_equation {term : Pattern} {lane : EquationJob.Lane}
    (present : lane ∈ EquationJob.lanes plan bound expected term) : lane.job.equation ∈ plan.equations := by
  obtain ⟨_, job, _, _⟩ := (EquationJob.mem_lanes plan bound expected).mp present
  exact List.fst_mem_of_mem_zipIdx ((GeneralEquationJobs.jobs_iff _ _ _ _ _).mp job).1

theorem key_eventually_complete (descends : Descends plan) {owner : Rep} {key : Key}
    (inLanes : key ∈ lanesOf plan bound expected owner) :
    ∃ work, (Deep.run (family plan key) work (Deep.start (family plan key))).complete = true := by
  cases key with
  | rule rep job => exact DeepRoot.eventually_complete (Step.request plan job) descends.1
  | forward rep lane =>
    have same : rep = owner := lanesOf_rep plan bound expected inLanes
    subst same
    have present := mem_lanesOf_forward plan bound expected inLanes
    exact EquationJob.lane_eventually_complete plan bound expected present descends.1
      (descends.2 _ (lane_equation plan bound expected present))
  | backward rep candidate lane =>
    have same : rep = owner := lanesOf_rep plan bound expected inLanes
    subst same
    have present := mem_lanesOf_backward plan bound expected inLanes
    exact EquationJob.lane_eventually_complete plan bound expected present descends.1
      (descends.2 _ (lane_equation plan bound expected present))

theorem keys_eventually_complete (descends : Descends plan) :
    ∀ keys : List Key, (∀ key ∈ keys, ∃ rep, key ∈ lanesOf plan bound expected rep) →
      ∃ work, ∀ key ∈ keys, ∀ later, work ≤ later →
        (Deep.run (family plan key) later (Deep.start (family plan key))).complete = true := by
  intro keys
  induction keys with
  | nil => intro _; exact ⟨0, by simp⟩
  | cons key rest ih =>
    intro lanes
    obtain ⟨rep, inLanes⟩ := lanes key List.mem_cons_self
    obtain ⟨first, done⟩ := key_eventually_complete plan bound expected descends inLanes
    obtain ⟨others, restDone⟩ := ih (fun other member => lanes other (List.mem_cons_of_mem _ member))
    refine ⟨max first others, ?_⟩
    intro other member later after
    rcases List.mem_cons.mp member with rfl | inRest
    · exact Deep.complete_mono (family plan other) done (le_of_max_le_left after)
    · exact restDone other inRest later (le_of_max_le_right after)

/-! ## The search finishes -/

/-- **The search finishes.** For a plan whose rules and equation premises descend, a source with a
finite equality class has a complete search after finitely many rounds. -/
theorem eventually_complete (descends : Descends plan) {carrier : List Pattern}
    (finite : ∀ pattern, Relation.EqvGen (GeneralOccurrenceSemantics.Equation plan bound expected) source pattern →
      pattern ∈ carrier) :
    ∃ work, complete plan (runAt plan bound expected source work) = true := by
  obtain ⟨settled, stable⟩ := reps_settle plan bound expected source finite
  let keys := (runAt plan bound expected source settled).reps.flatMap (lanesOf plan bound expected)
  obtain ⟨extra, done⟩ := keys_eventually_complete plan bound expected descends keys (by
    intro key member
    obtain ⟨rep, _, inLanes⟩ := List.mem_flatMap.mp member
    exact ⟨rep, inLanes⟩)
  refine ⟨settled + extra, List.all_eq_true.mpr ?_⟩
  intro entry member
  obtain ⟨repMember, inLanes, current⟩ := (rounds_reached plan bound expected source (settled + extra)).entries entry member
  have same := stable (settled + extra) (Nat.le_add_right _ _)
  have settledMember : entry.1.rep ∈ (runAt plan bound expected source settled).reps := by
    rw [← same]; exact repMember
  have born : entry.1.rep.born ≤ settled := by
    have early := (rounds_reached plan bound expected source settled).born _ settledMember
    rwa [runAt_round] at early
  have key : entry.1 ∈ keys := List.mem_flatMap.mpr ⟨_, settledMember, inLanes⟩
  rw [current]
  apply done entry.1 key
  have round := runAt_round plan bound expected source (settled + extra)
  simp only [runAt] at round
  rw [round]
  omega

/-- **Accepted compiled plans finish** at well-sorted sources, when their rules and equation
premises descend. -/
theorem compiled_eventually_complete {snapshot : Snapshot} {permissions : Permissions}
    (accepted : (compile snapshot permissions).complete = true) (descends : Descends (compile snapshot permissions))
    (sorted : Mettapedia.GSLT.LanguageDef.WellSorted.OpenPatternWellSorted snapshot.language snapshot.free bound expected source) :
    ∃ work, complete (compile snapshot permissions) (runAt (compile snapshot permissions) bound expected source work) = true :=
  eventually_complete (compile snapshot permissions) bound expected source descends
    (carrier := Framework.GeneralFiniteTermUniverse.sourceUniverse snapshot.language snapshot.free bound expected source [])
    (fun _ related =>
      (GeneralEquationReverseBounds.compiled_equivalence_universe_iff (root := source) [] accepted related).mp
        (Framework.GeneralFiniteTermUniverse.sourceUniverse_contains_source _ _ _ _ _ [] sorted))

/-- Without equations, a class is its source alone. -/
theorem equivalent_eq_of_no_equations (empty : plan.equations = []) {first second : Pattern}
    (related : Relation.EqvGen (GeneralOccurrenceSemantics.Equation plan bound expected) first second) : first = second := by
  induction related with
  | rel _ _ step =>
    obtain ⟨receipt, completion, _⟩ := step
    obtain ⟨licensed, _⟩ := completion
    have member := List.fst_mem_of_mem_zipIdx licensed.1
    rw [empty] at member
    cases member
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ first second => exact first.trans second

/-- **Equation-free plans finish** when their rules descend. -/
theorem equationFree_eventually_complete (empty : plan.equations = [])
    (admitted : StructuralDescent.checkEnvironment (GeneralPlanEnvironment.environment plan) = true) :
    ∃ work, complete plan (runAt plan bound expected source work) = true :=
  eventually_complete plan bound expected source ⟨admitted, by simp [empty]⟩ (carrier := [source])
    (fun _ related => by rw [← equivalent_eq_of_no_equations plan bound expected empty related]; simp)

/-! ## Finite classes beyond accepted compiled plans -/

section Universe

open Framework.GeneralFiniteTermUniverse GeneralEquationReverseBounds PatternTreeSize
open Mettapedia.GSLT.LanguageDef.WellSorted

/-- Equality classes stay in the source universe for any plan whose equations are compiled from its
snapshot and balanced. Unlike `compiled_equivalence_universe_iff`, nothing else about the plan's
acceptance is assumed. -/
theorem universe_iff_of_compiled_equations {permissions : Permissions}
    (compiled : ∀ equation ∈ plan.equations, equation ∈ (compile plan.snapshot permissions).equations)
    (checked : Predecessors.equationsChecked plan = true) {root first second : Pattern}
    (related : Relation.EqvGen (GeneralOccurrenceSemantics.Equation plan bound expected) first second) :
    first ∈ sourceUniverse plan.snapshot.language plan.snapshot.free bound expected root [] ↔
      second ∈ sourceUniverse plan.snapshot.language plan.snapshot.free bound expected root [] := by
  induction related with
  | rel first second step =>
    obtain ⟨receipt, complete, rfl⟩ := step
    have declared : receipt.job.equation ∈ plan.equations := List.fst_mem_of_mem_zipIdx complete.job.1
    have schema := List.all_eq_true.mp checked _ declared
    have fromSnapshot := compiled _ declared
    constructor
    · intro member
      exact complete.universe_closed schema (GeneralEquationJobs.compiled_equation_template fromSnapshot root []) member
    · intro member
      have targetSmall := (typedUniverse_sound _ _ _ _ _ _ _ _ member).1
      have targetSupport := sourceUniverse_supported _ _ _ _ _ _ _ member
      have sourceSupport := completion_reverse_supported complete schema
        (compiled_left_template fromSnapshot root []) targetSupport
      have same := completion_nodes complete schema
      have small : nodes first ≤ nodes root := same ▸ targetSmall
      have sourceTyped : OpenPatternWellSorted plan.snapshot.language plan.snapshot.free bound expected first :=
        (GeneralPlanEnvironment.typing_iff _ bound expected first).mp complete.sourceTyped
      apply typedUniverse_complete _ _ _ _ _ _ _ _ sourceTyped small sourceSupport
      exact scoped_indices _ _ bound.length (nodes root) small sourceTyped.2.2.2
        (fun arity occurs => arity_le_maximum _ arity (sourceSupport.2.2 arity occurs))
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ first second => exact first.trans second

/-- **Plans with compiled, balanced equations finish** at well-sorted sources, when their rules and
equation premises descend. -/
theorem compiledEquations_eventually_complete {permissions : Permissions}
    (compiled : ∀ equation ∈ plan.equations, equation ∈ (compile plan.snapshot permissions).equations)
    (checked : Predecessors.equationsChecked plan = true) (descends : Descends plan)
    (sorted : OpenPatternWellSorted plan.snapshot.language plan.snapshot.free bound expected source) :
    ∃ work, complete plan (runAt plan bound expected source work) = true :=
  eventually_complete plan bound expected source descends
    (carrier := sourceUniverse plan.snapshot.language plan.snapshot.free bound expected source [])
    (fun _ related => (universe_iff_of_compiled_equations plan bound expected compiled checked (root := source) related).mp
      (sourceUniverse_contains_source _ _ _ _ _ [] sorted))

/-- **Descent-refined plans finish** (`StructuralDescent.Plan.compile`, which drops the
stratification obligation), when their equations are balanced and their rules and equation premises
descend. -/
theorem refined_eventually_complete {snapshot : Snapshot} {permissions : Permissions}
    (checked : Predecessors.equationsChecked (StructuralDescent.Plan.compile snapshot permissions) = true)
    (descends : Descends (StructuralDescent.Plan.compile snapshot permissions))
    (sorted : OpenPatternWellSorted snapshot.language snapshot.free bound expected source) :
    ∃ work, complete (StructuralDescent.Plan.compile snapshot permissions)
      (runAt (StructuralDescent.Plan.compile snapshot permissions) bound expected source work) = true := by
  have sameSnapshot : (StructuralDescent.Plan.compile snapshot permissions).snapshot = snapshot :=
    (StructuralDescent.Plan.snapshot_preserved _).trans rfl
  apply compiledEquations_eventually_complete _ bound expected source (permissions := permissions) _ checked descends
    (by rw [sameSnapshot]; exact sorted)
  intro equation member
  rw [sameSnapshot]
  simpa [StructuralDescent.Plan.compile, StructuralDescent.Plan.equations_preserved] using member

end Universe

end Mettapedia.OSLF.MeTTaIL.Complete.Classes
