import Mettapedia.OSLF.NativeTypes.Consumers.MM2Batch
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.PathSystems

/-!
# MM2 batch publication through the front door

A matching checkpoint advances by any grant: a grant that does not reach completion pauses at a later checkpoint, and
one that does commits the publication. The grants are unbounded, but past completion they all commit the same
publication, since a completed resumption stays completed. So when a checkpoint completes within a grant `bound`
(`CompletesBy`), its successors are listed exactly by the grants up to the bound (`successorsUpTo`,
`transition_iff`), and every checkpoint it pauses at completes within the same bound (`completesBy_afterPause`).
Configurations carry proofs, so the front door asks the system by its paths (`PathSystems`):

- **the generated publication type is the front door's `◇(inRelation "published")`** at the configuration
  (`inhabits_iff_frontDoor`), for the observation "the store is the target and the residual is committed".
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.OSLF.NativeTypes.Consumers.MM2Batch

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK
open Mettapedia.GSLT.LanguageDef
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis
open Mettapedia.GSLT.LanguageDef.ProgrammableSpaceMM2Resumable (Checkpoint Residual)
open Mettapedia.OSLF.NativeTypes.GeneratedLogic
open Mettapedia.OSLF.NativeTypes.GeneratedLogic.PathSystems

/-! ## Completion persists -/

/-- **A checkpoint completes within a grant.** -/
def CompletesBy (checkpoint : Checkpoint) (bound : ℕ) : Prop :=
  ∃ spent result, checkpoint.resume bound = (spent, .done result)

/-- Whether a checkpoint completes within a grant. -/
def completesBy (checkpoint : Checkpoint) (bound : ℕ) : Bool :=
  match checkpoint.resume bound with
  | (_, .done _) => true
  | (_, .paused _) => false

theorem completesBy_iff (checkpoint : Checkpoint) (bound : ℕ) :
    completesBy checkpoint bound = true ↔ CompletesBy checkpoint bound := by
  unfold completesBy CompletesBy
  rcases checkpoint.resume bound with ⟨spent, outcome⟩
  cases outcome <;> simp

theorem resume_add (checkpoint : Checkpoint) (first later : ℕ) :
    checkpoint.resume (first + later) =
      Mettapedia.Machines.Cursor.resume _ _ (fun _ _ => 1) later (checkpoint.resume first) := by
  unfold Checkpoint.resume
  exact Mettapedia.Machines.Cursor.resume_add _ _ _ first later _

/-- **A completed resumption stays completed.** -/
theorem resume_of_done {checkpoint : Checkpoint} {grant spent : ℕ}
    {result : ProgrammableSpaceMM2Resumable.FinishedFor checkpoint.before checkpoint.request}
    (done : checkpoint.resume grant = (spent, .done result)) (more : ℕ) :
    checkpoint.resume (grant + more) = (spent, .done result) := by
  rw [resume_add, done]
  rfl

theorem resume_le_of_completes {checkpoint : Checkpoint} {bound grant : ℕ} (completes : CompletesBy checkpoint bound)
    (above : bound ≤ grant) : checkpoint.resume grant = checkpoint.resume bound := by
  obtain ⟨spent, result, done⟩ := completes
  obtain ⟨more, rfl⟩ := Nat.exists_eq_add_of_le above
  rw [resume_of_done done more, done]

/-- **A checkpoint paused at completes within the same bound.** -/
theorem completesBy_afterPause {checkpoint : Checkpoint} {bound grant spent : ℕ}
    {packet : ProgrammableSpaceMM2Resumable.PacketFor checkpoint.before checkpoint.request}
    (paused : checkpoint.resume grant = (spent, .paused packet)) (completes : CompletesBy checkpoint bound) :
    CompletesBy (checkpoint.afterPause grant spent packet paused) bound := by
  obtain ⟨doneSpent, result, done⟩ := completes
  refine ⟨doneSpent, result, ?_⟩
  rw [Checkpoint.pause_then_resume, Nat.add_comm, resume_of_done done]

/-! ## The successors, listed -/

/-- **The step a grant takes** from a checkpoint. -/
def stepAt (profile : Profile) (checkpoint : Checkpoint) (grant : ℕ) : Configuration :=
  match paused : checkpoint.resume grant with
  | (spent, .paused packet) => (checkpoint.before, .matching (checkpoint.afterPause grant spent packet paused))
  | (_, .done result) =>
    (finalize profile checkpoint.before checkpoint.request result.2.1,
      .committed ⟨checkpoint.request, checkpoint.before, result.2.1⟩)

theorem stepAt_paused (profile : Profile) {checkpoint : Checkpoint} {grant spent : ℕ}
    {packet : ProgrammableSpaceMM2Resumable.PacketFor checkpoint.before checkpoint.request}
    (paused : checkpoint.resume grant = (spent, .paused packet)) :
    stepAt profile checkpoint grant = (checkpoint.before, .matching (checkpoint.afterPause grant spent packet paused)) := by
  unfold stepAt
  split
  · rename_i spent' packet' paused'
    have same := paused'.symm.trans paused
    simp only [Prod.mk.injEq] at same
    obtain ⟨rfl, same⟩ := same
    cases same
    rfl
  · rename_i result paused'
    have same := paused'.symm.trans paused
    simp at same

theorem stepAt_done (profile : Profile) {checkpoint : Checkpoint} {grant spent : ℕ}
    {result : ProgrammableSpaceMM2Resumable.FinishedFor checkpoint.before checkpoint.request}
    (done : checkpoint.resume grant = (spent, .done result)) :
    stepAt profile checkpoint grant =
      (finalize profile checkpoint.before checkpoint.request result.2.1,
        .committed ⟨checkpoint.request, checkpoint.before, result.2.1⟩) := by
  unfold stepAt
  split
  · rename_i spent' packet paused
    have same := paused.symm.trans done
    simp at same
  · rename_i spent' result' done'
    have same := done'.symm.trans done
    simp only [Prod.mk.injEq] at same
    obtain ⟨-, same⟩ := same
    cases same
    rfl

/-- **The successors of a configuration, by the grants up to a bound**: none for a committed one, and for a matching
one whose store is the captured one and whose directive is the selected one, the step of each grant. -/
def successorsUpTo (profile : Profile) (scope : ProgrammableSpaceMM2.Scope) (bound : ℕ) :
    Configuration → List Configuration
  | (store, .matching checkpoint) =>
    if store = checkpoint.before ∧ selectedDirective scope checkpoint.before = some checkpoint.request.directive then
      (List.range (bound + 1)).map (stepAt profile checkpoint)
    else []
  | (_, .committed _) => []

theorem selected_iff (scope : ProgrammableSpaceMM2.Scope) (checkpoint : Checkpoint) :
    selectedDirective scope checkpoint.before = some checkpoint.request.directive ↔
      MM2MatchingBatch.SelectedFor scope checkpoint.before checkpoint.request.directive :=
  selectedDirective_exact scope checkpoint.before checkpoint.request.directive

/-- The grant past which nothing new happens: a grant beyond the bound takes the step of the bound. -/
theorem stepAt_le_of_completes (profile : Profile) {checkpoint : Checkpoint} {bound grant : ℕ}
    (completes : CompletesBy checkpoint bound) (above : bound ≤ grant) :
    stepAt profile checkpoint grant = stepAt profile checkpoint bound := by
  obtain ⟨spent, result, done⟩ := completes
  rw [stepAt_done profile done, stepAt_done profile ((resume_le_of_completes ⟨spent, result, done⟩ above).trans done)]

/-- **The listed successors are exactly the steps** of a matching configuration whose checkpoint completes within the
bound. -/
theorem transition_iff (profile : Profile) (scope : ProgrammableSpaceMM2.Scope) {bound : ℕ} {store : List Atom}
    {checkpoint : Checkpoint} (completes : CompletesBy checkpoint bound) (next : Configuration) :
    Transition profile scope (store, .matching checkpoint) next ↔
      next ∈ successorsUpTo profile scope bound (store, .matching checkpoint) := by
  have listed : ∀ (selected : MM2MatchingBatch.SelectedFor scope checkpoint.before checkpoint.request.directive)
      (grant : ℕ), stepAt profile checkpoint grant ∈ successorsUpTo profile scope bound (checkpoint.before, .matching checkpoint) := by
    intro selected grant
    dsimp only [successorsUpTo]
    rw [if_pos (⟨rfl, (selected_iff scope checkpoint).mpr selected⟩ :
      checkpoint.before = checkpoint.before ∧ _)]
    simp only [List.mem_map, List.mem_range]
    rcases Nat.lt_or_ge grant (bound + 1) with below | above
    · exact ⟨grant, below, rfl⟩
    · exact ⟨bound, Nat.lt_succ_self bound, (stepAt_le_of_completes profile completes (by omega)).symm⟩
  constructor
  · rintro ⟨receipt, step⟩
    cases profile with
    | sinkMajor =>
      change ProgrammableSpaceMM2Resumable.Advance scope store (.matching checkpoint) receipt next.1 next.2 at step
      obtain ⟨first, second⟩ := next
      cases step with
      | pause _ grant spent packet selected paused =>
        rw [← stepAt_paused .sinkMajor paused]
        exact listed selected grant
      | commit _ grant spent result selected done =>
        have found := listed selected grant
        rw [stepAt_done .sinkMajor done] at found
        exact found
    | rowMajor =>
      change ProgrammableSpaceMM2RowMajorResumable.Advance scope store (.matching checkpoint) receipt next.1 next.2 at step
      obtain ⟨first, second⟩ := next
      cases step with
      | pause _ grant spent packet selected paused =>
        rw [← stepAt_paused .rowMajor paused]
        exact listed selected grant
      | commit _ grant spent result selected done =>
        have found := listed selected grant
        rw [stepAt_done .rowMajor done] at found
        exact found
  · intro member
    simp only [successorsUpTo] at member
    split at member
    · rename_i condition
      obtain ⟨rfl, selected⟩ := condition
      have selectedFor := (selected_iff scope checkpoint).mp selected
      obtain ⟨grant, -, rfl⟩ := List.mem_map.mp member
      rcases resumed : checkpoint.resume grant with ⟨spent, outcome⟩
      cases outcome with
      | paused packet =>
        rw [stepAt_paused profile resumed]
        cases profile with
        | sinkMajor => exact ⟨_, .pause checkpoint grant spent packet selectedFor resumed⟩
        | rowMajor => exact ⟨_, .pause checkpoint grant spent packet selectedFor resumed⟩
      | done result =>
        rw [stepAt_done profile resumed]
        cases profile with
        | sinkMajor => exact ⟨_, .commit checkpoint grant spent result selectedFor resumed⟩
        | rowMajor => exact ⟨_, .commit checkpoint grant spent result selectedFor resumed⟩
    · simp at member

/-! ## At the front door -/

/-- The store is the target and the residual is committed. -/
def published (target : List Atom) (configuration : Configuration) : Bool :=
  decide (configuration.1 = target) &&
    match configuration.2 with
    | .committed _ => true
    | .matching _ => false

theorem published_iff (target : List Atom) (configuration : Configuration) :
    published target configuration = true ↔ committedStore target configuration := by
  obtain ⟨store, residual⟩ := configuration
  cases residual <;> simp [published, committedStore]

/-- **A configuration's publications, as a listed system**, observed by `published`. -/
def system (profile : Profile) (scope : ProgrammableSpaceMM2.Scope) (target : List Atom) (bound : ℕ) :
    Listed Configuration where
  successors := successorsUpTo profile scope bound
  observations name configuration := name == "published" && published target configuration

/-- **The generated publication type is the front door's `◇(inRelation "published")`** at a matching configuration
whose checkpoint completes within the bound. -/
theorem inhabits_iff_frontDoor (profile : Profile) (scope : ProgrammableSpaceMM2.Scope) (target : List Atom)
    {bound : ℕ} {store : List Atom} {checkpoint : Checkpoint} (completes : CompletesBy checkpoint bound) :
    Inhabits profile scope target (store, .matching checkpoint) ↔
      ((system profile scope target bound).unfolded (store, .matching checkpoint)).observed.reading.sat Env.closed
        (.possibly .any (.inRelation "published")) (pathPattern []) := by
  rw [Listed.sat_possibly_observe_iff]
  change gsltDiamond (theory profile scope) (saturatePredicate (theory profile scope) (committedStore target)).1
    (store, .matching checkpoint) ↔ _
  rw [gsltDiamond_spec]
  constructor
  · rintro ⟨next, step, representative, equivalent, observed⟩
    have same : next = representative := equivalent
    subst same
    refine ⟨next, (transition_iff profile scope completes next).mp step, ?_⟩
    simp only [system, beq_self_eq_true, Bool.true_and]
    exact (published_iff target next).mpr observed
  · rintro ⟨next, member, observed⟩
    simp only [system, beq_self_eq_true, Bool.true_and] at observed
    exact ⟨next, (transition_iff profile scope completes next).mpr member, next, rfl, (published_iff target next).mp observed⟩

end Mettapedia.OSLF.NativeTypes.Consumers.MM2Batch
