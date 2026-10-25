import Mettapedia.OSLF.MeTTaIL.CollectionOccurrenceInstallation

/-!
# Retained source-job matchers and exact allocation installation accounts

Every lane retains the actual licensed job, matcher state and work history.
Only the newly published answer suffix enters allocation preparation. The
account records complete allocations, including occurrence and nested traces,
and does not restart earlier continuations when another answer arrives.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.CollectionOccurrenceMatcher

open _root_.Mettapedia.OSLF.MeTTaIL.Syntax
open CollectionOccurrenceHandoff CollectionOccurrenceBatch

variable {plan : GeneralExecutionAdmission.Plan} {bound : List TypeExpr}
    {expected : TypeExpr} {source : Pattern}

abbrev Published (job : Job) (work : Nat) (answer : RecursiveCollectionMachine.Answer) : Prop :=
  answer ∈ (RecursiveCollectionMachine.run job.request work
    (RecursiveCollectionMachine.start job.request)).answers

/-- Work and membership establish validity. They do not become another
allocation identity: the job and complete matching trace supply that data. -/
theorem allocate_work_irrelevant (job : Job) (licensed : job.Valid plan bound expected source)
    (first extra : Nat) (answer : RecursiveCollectionMachine.Answer)
    (earlier : Published job first answer) (later : Published job extra answer) (depth : Nat) :
    allocate? job licensed first answer earlier depth = allocate? job licensed extra answer later depth := rfl

/-- The local static obligations suffice to install every published match.
Preparation cannot silently drop a valid recursive allocation. No firing,
premise result or source-coverage assertion is assumed. -/
theorem allocate_published_exists (job : Job) (licensed : job.Valid plan bound expected source)
    (work depth : Nat) (answer : RecursiveCollectionMachine.Answer)
    (published : Published job work answer)
    (admitted : RuleBinding.admittedFor job.origin.declaration.rule job.origin.declaration.binding.spec = true)
    (sorted : Mettapedia.GSLT.LanguageDef.WellSorted.OpenPatternWellSorted
      (GeneralPlanEnvironment.environment plan).language (GeneralPlanEnvironment.environment plan).free
      job.variant.site.focusBound job.variant.site.focusType job.variant.site.focus) :
    ∃ allocation : Allocation plan bound expected source,
      allocate? job licensed work answer published depth = some allocation ∧
        allocation.job = job ∧ allocation.answer = answer := by
  have checked := Mettapedia.GSLT.LanguageDef.WellSorted.checkOpenPatternWellSorted_complete sorted
  unfold CollectionOccurrenceBatch.allocate?
  split
  · rename_i missing
    obtain ⟨prepared, computed, _⟩ := RecursiveCollectionHandoff.prepare_published job.request work published
    rw [missing] at computed
    cases computed
  · rename_i prepared made
    dsimp only
    split
    · rename_i missing
      simp only [CollectionOccurrenceContinuation.request?, admitted, checked, ↓reduceDIte] at missing
      cases missing
    · rename_i request issued
      exact ⟨_, rfl, rfl, rfl⟩

def collect (job : Job) (licensed : job.Valid plan bound expected source) (work depth : Nat) :
    (answers : List RecursiveCollectionMachine.Answer) →
    (∀ answer ∈ answers, Published job work answer) → List (Allocation plan bound expected source)
  | [], _ => []
  | answer :: answers, published =>
    (allocate? job licensed work answer (published answer List.mem_cons_self) depth).toList ++
      collect job licensed work depth answers
        (fun next member => published next (List.mem_cons_of_mem _ member))

theorem collect_work_irrelevant (job : Job) (licensed : job.Valid plan bound expected source)
    (first extra depth : Nat) (answers : List RecursiveCollectionMachine.Answer)
    (earlier : ∀ answer ∈ answers, Published job first answer)
    (later : ∀ answer ∈ answers, Published job extra answer) :
    collect job licensed first depth answers earlier = collect job licensed extra depth answers later := by
  induction answers with
  | nil => rfl
  | cons answer answers ih =>
    simp only [collect]
    rw [allocate_work_irrelevant job licensed first extra answer _ _ depth]
    exact congrArg (_ ++ ·) (ih _ _)

theorem collect_append (job : Job) (licensed : job.Valid plan bound expected source)
    (work depth : Nat) (first extra : List RecursiveCollectionMachine.Answer)
    (published : ∀ answer ∈ first ++ extra, Published job work answer) :
    collect job licensed work depth (first ++ extra) published =
      collect job licensed work depth first
          (fun answer member => published answer (List.mem_append_left _ member)) ++
        collect job licensed work depth extra
          (fun answer member => published answer (List.mem_append_right _ member)) := by
  induction first with
  | nil => rfl
  | cons answer answers ih =>
    simpa only [List.cons_append, collect, List.append_assoc] using
      congrArg (_ ++ ·) (ih _)

structure Lane (plan : GeneralExecutionAdmission.Plan) (bound : List TypeExpr)
    (expected : TypeExpr) (source : Pattern) where
  job : Job
  licensed : job.Valid plan bound expected source
  spent : Nat
  state : RecursiveCollectionMachine.State
  reached : state = RecursiveCollectionMachine.run job.request spent
    (RecursiveCollectionMachine.start job.request)

def Lane.begin (job : Job) (licensed : job.Valid plan bound expected source) :
    Lane plan bound expected source :=
  ⟨job, licensed, 0, RecursiveCollectionMachine.start job.request, rfl⟩

abbrev Lane.resume (work : Nat) (lane : Lane plan bound expected source) :
    Lane plan bound expected source :=
  ⟨lane.job, lane.licensed, lane.spent + work,
    RecursiveCollectionMachine.run lane.job.request work lane.state,
    by rw [lane.reached, RecursiveCollectionMachine.run_add]⟩

theorem Lane.resume_add (first extra : Nat) (lane : Lane plan bound expected source) :
    lane.resume (first + extra) = (lane.resume first).resume extra := by
  cases lane
  simp only [Lane.resume, Nat.add_assoc, RecursiveCollectionMachine.run_add]

theorem Lane.answers_prefix (lane : Lane plan bound expected source) (work : Nat) :
    lane.state.answers <+: (lane.resume work).state.answers :=
  RecursiveCollectionMachine.run_answers_prefix lane.job.request work lane.state

def Lane.fresh (lane : Lane plan bound expected source) : List RecursiveCollectionMachine.Answer :=
  (lane.resume 1).state.answers.drop lane.state.answers.length

theorem Lane.fresh_balance (lane : Lane plan bound expected source) :
    lane.state.answers ++ lane.fresh = (lane.resume 1).state.answers := by
  have grown := lane.answers_prefix 1
  unfold Lane.fresh
  calc
    _ = (lane.resume 1).state.answers.take lane.state.answers.length ++
        (lane.resume 1).state.answers.drop lane.state.answers.length :=
      congrArg (fun front => front ++ (lane.resume 1).state.answers.drop lane.state.answers.length)
        (List.prefix_iff_eq_take.mp grown)
    _ = _ := List.take_append_drop _ _

theorem Lane.published (lane : Lane plan bound expected source)
    (answer : RecursiveCollectionMachine.Answer) (member : answer ∈ lane.state.answers) :
    Published lane.job lane.spent answer := by
  unfold Published
  rw [← lane.reached]
  exact member

def Lane.account (depth : Nat) (lane : Lane plan bound expected source) :
    List (Allocation plan bound expected source) :=
  collect lane.job lane.licensed lane.spent depth lane.state.answers lane.published

def Lane.allocations (depth : Nat) (lane : Lane plan bound expected source) :
    List (Allocation plan bound expected source) :=
  collect lane.job lane.licensed (lane.spent + 1) depth lane.fresh
    (fun answer member => (lane.resume 1).published answer (List.mem_of_mem_drop member))

/-- Preparation of the new suffix and the previous complete allocation
account exactly partition the resumed account, including equal-valued
occurrences and all nested allocation decisions. -/
theorem Lane.allocation_balance (depth : Nat) (lane : Lane plan bound expected source) :
    lane.account depth ++ lane.allocations depth = (lane.resume 1).account depth := by
  have published : ∀ answer ∈ lane.state.answers ++ lane.fresh,
      Published lane.job (lane.spent + 1) answer := by
    intro answer member
    apply (lane.resume 1).published
    rw [← lane.fresh_balance]
    exact member
  have split := collect_append lane.job lane.licensed (lane.spent + 1) depth
    lane.state.answers lane.fresh published
  have previous := collect_work_irrelevant lane.job lane.licensed lane.spent (lane.spent + 1)
    depth lane.state.answers lane.published
    (fun answer member => published answer (List.mem_append_left _ member))
  unfold Lane.account Lane.allocations
  rw [previous, ← split]
  congr 1
  exact lane.fresh_balance

def lanes (plan : GeneralExecutionAdmission.Plan) (bound : List TypeExpr)
    (expected : TypeExpr) (source : Pattern) : List (Lane plan bound expected source) :=
  (jobs plan bound expected source).attach.map fun selected =>
    Lane.begin selected.val ((jobs_exact ..).mp selected.property)

end Mettapedia.OSLF.MeTTaIL.CollectionOccurrenceMatcher
