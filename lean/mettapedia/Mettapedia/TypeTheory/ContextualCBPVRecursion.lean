import Mettapedia.TypeTheory.ContextualCBPVZero

/-!
# Recursion in contextual CBPV: budget approximants and fair first answers

The contextual programs (`Program`, `ProgramZ`) are finite trees, so a
recursive definition cannot be one of them. This module gives recursion its
meaning as a chain of approximants indexed by a budget, and states what a
fair first-answer observer is.

* `RProg` is `ProgramZ` with one more operation, `call key next`: run the
  named definition `defs key` and continue with `next` on its answer.
* `approx defs n` unfolds calls up to nesting depth `n` along every path. A
  call left over at the budget becomes a **frontier** leaf, `pure none`: the
  `incomplete` field of a budgeted observation (`incompleteAt`).
* Each approximant refines the one before (`approx_refines_succ`): only
  frontier leaves change. Hence a completed world, once observed, stays
  observed at every larger budget (`completed_mono`).
* `Observed defs t s` is the set of completed worlds at some budget: the
  occurrences the unbounded program answers. A budgeted observation with no
  incomplete world is closed: every larger budget observes the same worlds
  (`complete_of_not_incompleteAt`), so it is the whole observation
  (`observed_eq_of_not_incompleteAt`).
* A first-answer observer is **fair** (`FairOnce`) when it answers a member of
  `Observed` whenever `Observed` is non-empty, and only members.
* The least-budget observer `onceLeast` is fair (`onceLeast_fair`), and so is
  its executable form, iterative deepening on the budget (`deepening_sound`,
  `deepening_complete`).
* Depth-first search is not fair. On `loop n = loop (n+1) ∪ answer n`, the
  shape of `tests/prime` and the controller benchmark `once_recursive_first`,
  depth-first search answers nothing at any fuel (`dfs_loop_none`) although
  the observed set holds `answer 0` (`loop_observed`); a queue-ordered search
  answers it within five steps (`bfs_loop`).
* A queue-ordered search, which serves the oldest pending alternative first,
  is fair on every program (`bfs_fair`): each answer it gives is an observed
  occurrence, and it answers whenever the program has one. `Leads` is a path
  of search steps to an answer; such paths are exactly the completed worlds
  of the approximants (`leads_of_mem_approx`, `mem_approx_of_leads`).

Recursion, zero answers and isolated worlds compose: `ProgramZ.runWorldsAt`
observes every approximant. Call-by-need cells and the surface syntax are not
part of this module.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.ContextualCBPV.Recursion

open Mettapedia.GSLT.Dynamics.ContextualEffectHandlers
open Mettapedia.TypeTheory.ContextualCBPV

/-! ## Programs with recursive calls -/

/-- Contextual programs with zero answers and calls to named definitions. -/
inductive RProg (Key State Answer Intent : Type) where
  | pure (answer : Answer)
  | zero
  | choose (left right : RProg Key State Answer Intent)
  | read (next : State → RProg Key State Answer Intent)
  | write (state : State) (next : RProg Key State Answer Intent)
  | intent (request : Intent) (next : RProg Key State Answer Intent)
  | call (key : Key) (next : Answer → RProg Key State Answer Intent)

namespace RProg

variable {Key State Answer Intent : Type}

/-- Sequencing: the continuation runs on each answer. -/
def bind : RProg Key State Answer Intent → (Answer → RProg Key State Answer Intent) →
    RProg Key State Answer Intent
  | .pure answer, k => k answer
  | .zero, _ => .zero
  | .choose left right, k => .choose (bind left k) (bind right k)
  | .read next, k => .read fun state => bind (next state) k
  | .write state next, k => .write state (bind next k)
  | .intent request next, k => .intent request (bind next k)
  | .call key next, k => .call key fun answer => bind (next answer) k

end RProg

/-! ## Budget approximants -/

variable {Key State Answer Intent : Type}

/-- The frontier leaf: a call not unfolded within the budget. -/
def frontier : ProgramZ State (Option Answer) Intent := .pure none

/-- One budget level: the program's own operations are kept, and each call is
answered by `prev` applied to its unfolding. -/
def step (defs : Key → RProg Key State Answer Intent)
    (prev : RProg Key State Answer Intent → ProgramZ State (Option Answer) Intent) :
    RProg Key State Answer Intent → ProgramZ State (Option Answer) Intent
  | .pure answer => .pure (some answer)
  | .zero => .zero
  | .choose left right => .choose (step defs prev left) (step defs prev right)
  | .read next => .read fun state => step defs prev (next state)
  | .write state next => .write state (step defs prev next)
  | .intent request next => .intent request (step defs prev next)
  | .call key next => prev ((defs key).bind next)

/-- The approximant at budget `n`: calls unfolded to nesting depth `n` on every
path, the deeper ones left as frontier. -/
def approx (defs : Key → RProg Key State Answer Intent) :
    Nat → RProg Key State Answer Intent → ProgramZ State (Option Answer) Intent
  | 0 => step defs fun _ => frontier
  | n + 1 => step defs (approx defs n)

/-! ## Refinement: only frontier leaves change -/

/-- `Refines p q`: `q` is `p` with some frontier leaves replaced by programs. -/
inductive Refines : ProgramZ State (Option Answer) Intent →
    ProgramZ State (Option Answer) Intent → Prop
  | frontier (later : ProgramZ State (Option Answer) Intent) :
      Refines (.pure none) later
  | pure (answer : Option Answer) : Refines (.pure answer) (.pure answer)
  | zero : Refines .zero .zero
  | choose {left right left' right' : ProgramZ State (Option Answer) Intent} :
      Refines left left' → Refines right right' →
        Refines (.choose left right) (.choose left' right')
  | read {next next' : State → ProgramZ State (Option Answer) Intent} :
      (∀ state, Refines (next state) (next' state)) → Refines (.read next) (.read next')
  | write (state : State) {next next' : ProgramZ State (Option Answer) Intent} :
      Refines next next' → Refines (.write state next) (.write state next')
  | intent (request : Intent) {next next' : ProgramZ State (Option Answer) Intent} :
      Refines next next' → Refines (.intent request next) (.intent request next')

/-- A budget level refines pointwise when its call answers do. -/
theorem step_refines (defs : Key → RProg Key State Answer Intent)
    {prev prev' : RProg Key State Answer Intent → ProgramZ State (Option Answer) Intent}
    (h : ∀ program, Refines (prev program) (prev' program)) :
    ∀ program, Refines (step defs prev program) (step defs prev' program) := by
  intro program
  induction program with
  | pure answer => exact .pure (some answer)
  | zero => exact .zero
  | choose left right leftIH rightIH => exact .choose leftIH rightIH
  | read next ih => exact .read ih
  | write state next ih => exact .write state ih
  | intent request next ih => exact .intent request ih
  | call key next _ => exact h _

/-- **Each approximant refines the one before.** -/
theorem approx_refines_succ (defs : Key → RProg Key State Answer Intent) :
    ∀ n program, Refines (approx defs n program) (approx defs (n + 1) program) := by
  intro n
  induction n with
  | zero => exact step_refines defs fun _ => .frontier _
  | succ n ih => exact step_refines defs ih

/-! ## Completed worlds persist -/

/-- A completed world: its answer is not the frontier. -/
def Completed (world : WorldResult State (Option Answer) Intent) : Prop :=
  world.answer.isSome

/-- Refinement keeps every completed world, with its branch path, state and
intents. -/
theorem Refines.completed {program later : ProgramZ State (Option Answer) Intent}
    (h : Refines program later) :
    ∀ state branch world, world ∈ ProgramZ.runWorldsAt program state branch →
      Completed world → world ∈ ProgramZ.runWorldsAt later state branch := by
  induction h with
  | frontier later =>
      intro state branch world member done
      simp only [ProgramZ.runWorldsAt, List.mem_singleton] at member
      subst member
      simp [Completed] at done
  | pure answer =>
      intro state branch world member _
      exact member
  | zero =>
      intro state branch world member _
      exact member
  | choose _ _ leftIH rightIH =>
      intro state branch world member done
      simp only [ProgramZ.runWorldsAt, List.mem_append] at member ⊢
      rcases member with member | member
      · exact Or.inl (leftIH state _ world member done)
      · exact Or.inr (rightIH state _ world member done)
  | read _ ih =>
      intro state branch world member done
      exact ih state state branch world member done
  | write written _ ih =>
      intro _ branch world member done
      exact ih written branch world member done
  | intent request _ ih =>
      intro state branch world member done
      simp only [ProgramZ.runWorldsAt, List.mem_map] at member ⊢
      obtain ⟨inner, innerMember, rfl⟩ := member
      exact ⟨inner, ih state branch inner innerMember done, rfl⟩

/-- **A completed world observed at one budget is observed at every larger
budget.** -/
theorem completed_mono (defs : Key → RProg Key State Answer Intent)
    (program : RProg Key State Answer Intent) (state : State) (branch : BranchTrace)
    (world : WorldResult State (Option Answer) Intent) (done : Completed world) :
    ∀ n k, world ∈ ProgramZ.runWorldsAt (approx defs n program) state branch →
      world ∈ ProgramZ.runWorldsAt (approx defs (n + k) program) state branch := by
  intro n k
  induction k with
  | zero => exact id
  | succ k ih =>
      intro member
      exact (approx_refines_succ defs (n + k) program).completed state branch world
        (ih member) done

/-! ## The observed occurrences and the incomplete field -/

/-- The completed worlds of the program at some budget: the occurrences the
unbounded program answers, each with its branch path, state and intents. -/
def Observed (defs : Key → RProg Key State Answer Intent)
    (program : RProg Key State Answer Intent) (state : State) :
    Set (WorldResult State (Option Answer) Intent) :=
  {world | Completed world ∧
    ∃ n, world ∈ ProgramZ.runWorldsAt (approx defs n program) state []}

/-- The budgeted observation at `n` is incomplete: a frontier leaf remains. -/
def incompleteAt (defs : Key → RProg Key State Answer Intent)
    (program : RProg Key State Answer Intent) (state : State) (n : Nat) : Prop :=
  ∃ world ∈ ProgramZ.runWorldsAt (approx defs n program) state [], world.answer = none

/-- Refinement changes nothing on a run that meets no frontier leaf. -/
theorem Refines.runWorldsAt_eq {program later : ProgramZ State (Option Answer) Intent}
    (h : Refines program later) :
    ∀ state branch,
      (∀ world ∈ ProgramZ.runWorldsAt program state branch, world.answer ≠ none) →
        ProgramZ.runWorldsAt later state branch = ProgramZ.runWorldsAt program state branch := by
  induction h with
  | frontier later =>
      intro state branch noFrontier
      exact absurd rfl
        (noFrontier { branch := branch, answer := none, state := state, intents := [] }
          (by simp [ProgramZ.runWorldsAt]))
  | pure answer => intro _ _ _; rfl
  | zero => intro _ _ _; rfl
  | choose _ _ leftIH rightIH =>
      intro state branch noFrontier
      simp only [ProgramZ.runWorldsAt] at noFrontier ⊢
      rw [leftIH state _ fun world member => noFrontier world (List.mem_append_left _ member),
        rightIH state _ fun world member => noFrontier world (List.mem_append_right _ member)]
  | read _ ih =>
      intro state branch noFrontier
      exact ih state state branch noFrontier
  | write written _ ih =>
      intro _ branch noFrontier
      exact ih written branch noFrontier
  | intent request _ ih =>
      intro state branch noFrontier
      simp only [ProgramZ.runWorldsAt] at noFrontier ⊢
      rw [ih state branch fun world member hnone =>
        noFrontier { world with intents := request :: world.intents }
          (List.mem_map_of_mem (f := fun result =>
            { result with intents := request :: result.intents }) member) hnone]

/-- **A budgeted observation with no incomplete world is closed**: every larger
budget observes exactly the same worlds, so the observation at `n` is the whole
observation. -/
theorem complete_of_not_incompleteAt (defs : Key → RProg Key State Answer Intent)
    (program : RProg Key State Answer Intent) (state : State) (n : Nat)
    (closed : ¬ incompleteAt defs program state n) :
    ∀ k, ProgramZ.runWorldsAt (approx defs (n + k) program) state [] =
      ProgramZ.runWorldsAt (approx defs n program) state [] := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih =>
      have noFrontier : ∀ world ∈ ProgramZ.runWorldsAt (approx defs (n + k) program) state [],
          world.answer ≠ none := by
        intro world member hnone
        exact closed ⟨world, ih ▸ member, hnone⟩
      rw [← ih]
      exact (approx_refines_succ defs (n + k) program).runWorldsAt_eq state [] noFrontier

theorem observed_eq_of_not_incompleteAt (defs : Key → RProg Key State Answer Intent)
    (program : RProg Key State Answer Intent) (state : State) (n : Nat)
    (closed : ¬ incompleteAt defs program state n) :
    Observed defs program state =
      {world | Completed world ∧
        world ∈ ProgramZ.runWorldsAt (approx defs n program) state []} := by
  ext world
  constructor
  · rintro ⟨done, m, member⟩
    refine ⟨done, ?_⟩
    rcases Nat.le_total m n with hle | hle
    · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hle
      exact completed_mono defs program state [] world done m k member
    · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hle
      rwa [complete_of_not_incompleteAt defs program state n closed k] at member
  · rintro ⟨done, member⟩
    exact ⟨done, n, member⟩

/-! ## Fair first answers -/

/-- A first-answer observer is fair when it answers only observed occurrences
and answers one whenever the program has any. -/
def FairOnce (defs : Key → RProg Key State Answer Intent)
    (observer : RProg Key State Answer Intent → State →
      Option (WorldResult State (Option Answer) Intent)) : Prop :=
  ∀ program state,
    (∀ world, observer program state = some world → world ∈ Observed defs program state) ∧
    ((Observed defs program state).Nonempty → ∃ world, observer program state = some world)

/-- The first completed world of the approximant at budget `n`, if any. -/
def firstCompletedAt (defs : Key → RProg Key State Answer Intent)
    (program : RProg Key State Answer Intent) (state : State) (n : Nat) :
    Option (WorldResult State (Option Answer) Intent) :=
  (ProgramZ.runWorldsAt (approx defs n program) state []).find? fun world =>
    world.answer.isSome

theorem firstCompletedAt_sound (defs : Key → RProg Key State Answer Intent)
    (program : RProg Key State Answer Intent) (state : State) (n : Nat)
    (world : WorldResult State (Option Answer) Intent)
    (h : firstCompletedAt defs program state n = some world) :
    world ∈ Observed defs program state := by
  have hmem := List.mem_of_find?_eq_some h
  have hdone := List.find?_some h
  exact ⟨by simpa [Completed] using hdone, n, hmem⟩

theorem firstCompletedAt_isSome (defs : Key → RProg Key State Answer Intent)
    (program : RProg Key State Answer Intent) (state : State) (n : Nat)
    (world : WorldResult State (Option Answer) Intent)
    (member : world ∈ ProgramZ.runWorldsAt (approx defs n program) state [])
    (done : Completed world) :
    (firstCompletedAt defs program state n).isSome := by
  unfold firstCompletedAt
  rw [List.find?_isSome]
  exact ⟨world, member, by simpa [Completed] using done⟩

/-- Some budget has a completed world exactly when the program answers. -/
theorem observed_nonempty_iff (defs : Key → RProg Key State Answer Intent)
    (program : RProg Key State Answer Intent) (state : State) :
    (Observed defs program state).Nonempty ↔
      ∃ n, (firstCompletedAt defs program state n).isSome := by
  constructor
  · rintro ⟨world, done, n, member⟩
    exact ⟨n, firstCompletedAt_isSome defs program state n world member done⟩
  · rintro ⟨n, hsome⟩
    obtain ⟨world, hworld⟩ := Option.isSome_iff_exists.mp hsome
    exact ⟨world, firstCompletedAt_sound defs program state n world hworld⟩

/-- The least-budget observer: the first completed world at the least budget
that has one. -/
noncomputable def onceLeast (defs : Key → RProg Key State Answer Intent)
    (program : RProg Key State Answer Intent) (state : State) :
    Option (WorldResult State (Option Answer) Intent) := by
  classical
  exact if h : ∃ n, (firstCompletedAt defs program state n).isSome then
    firstCompletedAt defs program state (Nat.find h) else none

/-- **The least-budget observer is fair.** -/
theorem onceLeast_fair (defs : Key → RProg Key State Answer Intent) :
    FairOnce defs (onceLeast defs) := by
  classical
  intro program state
  constructor
  · intro world hworld
    unfold onceLeast at hworld
    split at hworld
    · exact firstCompletedAt_sound defs program state _ world hworld
    · exact absurd hworld (by simp)
  · intro hne
    have h := (observed_nonempty_iff defs program state).mp hne
    unfold onceLeast
    rw [dif_pos h]
    exact Option.isSome_iff_exists.mp (Nat.find_spec h)

/-- Iterative deepening: the least budget up to `bound` with a completed world. -/
def deepening (defs : Key → RProg Key State Answer Intent)
    (program : RProg Key State Answer Intent) (state : State) :
    Nat → Option (WorldResult State (Option Answer) Intent)
  | 0 => firstCompletedAt defs program state 0
  | bound + 1 =>
      match deepening defs program state bound with
      | some world => some world
      | none => firstCompletedAt defs program state (bound + 1)

/-- Iterative deepening answers only observed occurrences. -/
theorem deepening_sound (defs : Key → RProg Key State Answer Intent)
    (program : RProg Key State Answer Intent) (state : State) :
    ∀ bound world, deepening defs program state bound = some world →
      world ∈ Observed defs program state := by
  intro bound
  induction bound with
  | zero =>
      intro world h
      exact firstCompletedAt_sound defs program state 0 world h
  | succ bound ih =>
      intro world h
      simp only [deepening] at h
      split at h
      · next found hfound => exact ih world (hfound.trans h)
      · exact firstCompletedAt_sound defs program state (bound + 1) world h

/-- Once a budget answers, every larger bound answers. -/
theorem deepening_isSome_mono (defs : Key → RProg Key State Answer Intent)
    (program : RProg Key State Answer Intent) (state : State) :
    ∀ bound k, (deepening defs program state bound).isSome →
      (deepening defs program state (bound + k)).isSome := by
  intro bound k
  induction k with
  | zero => exact id
  | succ k ih =>
      intro h
      have h' := ih h
      show (deepening defs program state (bound + k + 1)).isSome
      simp only [deepening]
      split
      · rfl
      · next hnone => simp [hnone] at h'

/-- **Iterative deepening is complete**: when the program answers, some bound
answers. With `deepening_sound`, it is a fair first-answer search. -/
theorem deepening_complete (defs : Key → RProg Key State Answer Intent)
    (program : RProg Key State Answer Intent) (state : State)
    (hne : (Observed defs program state).Nonempty) :
    ∃ bound world, deepening defs program state bound = some world := by
  obtain ⟨n, hn⟩ := (observed_nonempty_iff defs program state).mp hne
  have hsome : (deepening defs program state n).isSome := by
    cases n with
    | zero => simpa [deepening] using hn
    | succ n =>
        simp only [deepening]
        split
        · rfl
        · exact hn
  exact ⟨n, Option.isSome_iff_exists.mp hsome⟩

/-! ## Depth-first search is not fair -/

/-- Depth-first search over a stack of alternatives: the leftmost first, a call
unfolded in place. `fuel` bounds the number of steps. -/
def dfs (defs : Key → RProg Key State Answer Intent) :
    Nat → List (RProg Key State Answer Intent × State × BranchTrace) →
      Option (Answer × State × BranchTrace)
  | 0, _ => none
  | _ + 1, [] => none
  | fuel + 1, (program, state, branch) :: rest =>
      match program with
      | .pure answer => some (answer, state, branch)
      | .zero => dfs defs fuel rest
      | .choose left right =>
          dfs defs fuel ((left, state, false :: branch) :: (right, state, true :: branch) :: rest)
      | .read next => dfs defs fuel ((next state, state, branch) :: rest)
      | .write written next => dfs defs fuel ((next, written, branch) :: rest)
      | .intent _ next => dfs defs fuel ((next, state, branch) :: rest)
      | .call key next => dfs defs fuel (((defs key).bind next, state, branch) :: rest)

/-- Breadth-first search over a queue of alternatives: every alternative and
every unfolded call joins the back of the queue, so each pending alternative is
served after finitely many steps. -/
def bfs (defs : Key → RProg Key State Answer Intent) :
    Nat → List (RProg Key State Answer Intent × State × BranchTrace) →
      Option (Answer × State × BranchTrace)
  | 0, _ => none
  | _ + 1, [] => none
  | fuel + 1, (program, state, branch) :: rest =>
      match program with
      | .pure answer => some (answer, state, branch)
      | .zero => bfs defs fuel rest
      | .choose left right =>
          bfs defs fuel (rest ++ [(left, state, false :: branch), (right, state, true :: branch)])
      | .read next => bfs defs fuel (rest ++ [(next state, state, branch)])
      | .write written next => bfs defs fuel (rest ++ [(next, written, branch)])
      | .intent _ next => bfs defs fuel (rest ++ [(next, state, branch)])
      | .call key next => bfs defs fuel (rest ++ [((defs key).bind next, state, branch)])

/-- `loop n = loop (n+1) ∪ answer n`: two equations, the recursive one first. -/
def loopDefs : Nat → RProg Nat Unit Nat Unit :=
  fun n => .choose (.call (n + 1) .pure) (.pure n)

/-- The query `(loop 0)`. -/
def loopQuery : RProg Nat Unit Nat Unit := .call 0 .pure

/-- The program answers `answer 0` at budget 1, on the right branch. -/
theorem loop_observed :
    ({ branch := [true], answer := some 0, state := (), intents := [] } :
      WorldResult Unit (Option Nat) Unit) ∈ Observed loopDefs loopQuery () := by
  refine ⟨rfl, 1, ?_⟩
  have worlds : ProgramZ.runWorldsAt (approx loopDefs 1 loopQuery) () [] =
      [{ branch := [false], answer := none, state := (), intents := [] },
       { branch := [true], answer := some 0, state := (), intents := [] }] := rfl
  rw [worlds]
  exact List.mem_cons_of_mem _ (List.mem_singleton_self _)

/-- **Depth-first search answers nothing on `(loop 0)`, at any fuel**, although
the program has an answer (`loop_observed`). -/
theorem dfs_loop_none :
    ∀ fuel k (branch : BranchTrace)
      (rest : List (RProg Nat Unit Nat Unit × Unit × BranchTrace)),
      dfs loopDefs fuel ((.call k .pure, (), branch) :: rest) = none := by
  intro fuel
  induction fuel using Nat.strong_induction_on with
  | _ fuel ih =>
      intro k branch rest
      match fuel with
      | 0 => rfl
      | 1 => rfl
      | fuel + 2 =>
          show dfs loopDefs fuel
              ((.call (k + 1) (fun answer => (RProg.pure answer).bind .pure), (), false :: branch) ::
                (RProg.bind (.pure k) .pure, (), true :: branch) :: rest) = none
          exact ih fuel (by omega) (k + 1) (false :: branch) _

theorem dfs_loopQuery_none (fuel : Nat) : dfs loopDefs fuel [(loopQuery, (), [])] = none :=
  dfs_loop_none fuel 0 [] []

/-- A queue-ordered search answers `answer 0` within five steps. -/
theorem bfs_loop : bfs loopDefs 5 [(loopQuery, (), [])] = some (0, (), [true]) := by
  decide

/-- **Depth-first search is not a fair first-answer search**: `loopQuery` has
an observed occurrence, and depth-first search answers nothing at any fuel. -/
theorem dfs_not_fair :
    (Observed loopDefs loopQuery ()).Nonempty ∧
      ∀ fuel, dfs loopDefs fuel [(loopQuery, (), [])] = none :=
  ⟨⟨_, loop_observed⟩, dfs_loopQuery_none⟩

/-! ## A queue-ordered search is fair -/

/-- `Leads defs program state branch answer state' branch' n`: the searches
above reach `answer` from `program` in `n` steps (a call unfolded, a choice
taken, a read, a write or an intent passed), ending in state `state'` with
branch trace `branch'`. -/
inductive Leads (defs : Key → RProg Key State Answer Intent) :
    RProg Key State Answer Intent → State → BranchTrace →
      Answer → State → BranchTrace → Nat → Prop
  | pure (answer : Answer) (state : State) (branch : BranchTrace) :
      Leads defs (.pure answer) state branch answer state branch 0
  | left {left right : RProg Key State Answer Intent} {state state' : State}
      {branch branch' : BranchTrace} {answer : Answer} {n : Nat} :
      Leads defs left state (false :: branch) answer state' branch' n →
        Leads defs (.choose left right) state branch answer state' branch' (n + 1)
  | right {left right : RProg Key State Answer Intent} {state state' : State}
      {branch branch' : BranchTrace} {answer : Answer} {n : Nat} :
      Leads defs right state (true :: branch) answer state' branch' n →
        Leads defs (.choose left right) state branch answer state' branch' (n + 1)
  | read {next : State → RProg Key State Answer Intent} {state state' : State}
      {branch branch' : BranchTrace} {answer : Answer} {n : Nat} :
      Leads defs (next state) state branch answer state' branch' n →
        Leads defs (.read next) state branch answer state' branch' (n + 1)
  | write {written : State} {next : RProg Key State Answer Intent} {state state' : State}
      {branch branch' : BranchTrace} {answer : Answer} {n : Nat} :
      Leads defs next written branch answer state' branch' n →
        Leads defs (.write written next) state branch answer state' branch' (n + 1)
  | intent {request : Intent} {next : RProg Key State Answer Intent} {state state' : State}
      {branch branch' : BranchTrace} {answer : Answer} {n : Nat} :
      Leads defs next state branch answer state' branch' n →
        Leads defs (.intent request next) state branch answer state' branch' (n + 1)
  | call {key : Key} {next : Answer → RProg Key State Answer Intent} {state state' : State}
      {branch branch' : BranchTrace} {answer : Answer} {n : Nat} :
      Leads defs ((defs key).bind next) state branch answer state' branch' n →
        Leads defs (.call key next) state branch answer state' branch' (n + 1)

/-- A completed world of one budget level leads to its answer when every
completed world of the level below does. -/
theorem leads_of_mem_step (defs : Key → RProg Key State Answer Intent)
    {prev : RProg Key State Answer Intent → ProgramZ State (Option Answer) Intent}
    (hprev : ∀ program state branch (world : WorldResult State (Option Answer) Intent)
      answer, world ∈ ProgramZ.runWorldsAt (prev program) state branch →
        world.answer = some answer →
        ∃ n, Leads defs program state branch answer world.state world.branch n) :
    ∀ (program : RProg Key State Answer Intent) state branch
      (world : WorldResult State (Option Answer) Intent) answer,
      world ∈ ProgramZ.runWorldsAt (step defs prev program) state branch →
      world.answer = some answer →
      ∃ n, Leads defs program state branch answer world.state world.branch n := by
  intro program
  induction program with
  | pure value =>
      intro state branch world answer member hanswer
      simp only [step, ProgramZ.runWorldsAt, List.mem_singleton] at member
      subst member
      simp only [Option.some.injEq] at hanswer
      subst hanswer
      exact ⟨0, .pure _ _ _⟩
  | zero =>
      intro state branch world answer member _
      simp [step] at member
  | choose left right leftIH rightIH =>
      intro state branch world answer member hanswer
      simp only [step, ProgramZ.runWorldsAt, List.mem_append] at member
      rcases member with member | member
      · obtain ⟨n, h⟩ := leftIH state _ world answer member hanswer
        exact ⟨n + 1, .left h⟩
      · obtain ⟨n, h⟩ := rightIH state _ world answer member hanswer
        exact ⟨n + 1, .right h⟩
  | read next ih =>
      intro state branch world answer member hanswer
      obtain ⟨n, h⟩ := ih state state branch world answer member hanswer
      exact ⟨n + 1, .read h⟩
  | write written next ih =>
      intro state branch world answer member hanswer
      obtain ⟨n, h⟩ := ih written branch world answer member hanswer
      exact ⟨n + 1, .write h⟩
  | intent request next ih =>
      intro state branch world answer member hanswer
      simp only [step, ProgramZ.runWorldsAt, List.mem_map] at member
      obtain ⟨inner, innerMember, rfl⟩ := member
      obtain ⟨n, h⟩ := ih state branch inner answer innerMember hanswer
      exact ⟨n + 1, .intent h⟩
  | call key next _ =>
      intro state branch world answer member hanswer
      obtain ⟨n, h⟩ := hprev _ state branch world answer member hanswer
      exact ⟨n + 1, .call h⟩

/-- A completed world of an approximant leads to its answer. -/
theorem leads_of_mem_approx (defs : Key → RProg Key State Answer Intent) :
    ∀ n (program : RProg Key State Answer Intent) state branch
      (world : WorldResult State (Option Answer) Intent) answer,
      world ∈ ProgramZ.runWorldsAt (approx defs n program) state branch →
      world.answer = some answer →
      ∃ m, Leads defs program state branch answer world.state world.branch m := by
  intro n
  induction n with
  | zero =>
      refine leads_of_mem_step defs ?_
      intro program state branch world answer member hanswer
      simp only [frontier, ProgramZ.runWorldsAt, List.mem_singleton] at member
      subst member
      simp at hanswer
  | succ n ih => exact leads_of_mem_step defs ih

/-- A path to an answer in `n` steps is a completed world of the approximant
at budget `n`. -/
theorem mem_approx_of_leads (defs : Key → RProg Key State Answer Intent)
    {program : RProg Key State Answer Intent} {state state' : State}
    {branch branch' : BranchTrace} {answer : Answer} {n : Nat}
    (h : Leads defs program state branch answer state' branch' n) :
    ∃ world ∈ ProgramZ.runWorldsAt (approx defs n program) state branch,
      world.answer = some answer ∧ world.state = state' ∧ world.branch = branch' := by
  induction h with
  | pure answer state branch =>
      exact ⟨{ branch := branch, answer := some answer, state := state, intents := [] },
        by simp [approx, step, ProgramZ.runWorldsAt], rfl, rfl, rfl⟩
  | @left left right state state' branch branch' answer n _ ih =>
      obtain ⟨world, member, hanswer, hstate, hbranch⟩ := ih
      have done : Completed world := by simp [Completed, hanswer]
      have later := completed_mono defs left state (false :: branch) world done n 1 member
      refine ⟨world, ?_, hanswer, hstate, hbranch⟩
      show world ∈ ProgramZ.runWorldsAt (approx defs (n + 1) left) state (false :: branch) ++
        ProgramZ.runWorldsAt (approx defs (n + 1) right) state (true :: branch)
      exact List.mem_append_left _ later
  | @right left right state state' branch branch' answer n _ ih =>
      obtain ⟨world, member, hanswer, hstate, hbranch⟩ := ih
      have done : Completed world := by simp [Completed, hanswer]
      have later := completed_mono defs right state (true :: branch) world done n 1 member
      refine ⟨world, ?_, hanswer, hstate, hbranch⟩
      show world ∈ ProgramZ.runWorldsAt (approx defs (n + 1) left) state (false :: branch) ++
        ProgramZ.runWorldsAt (approx defs (n + 1) right) state (true :: branch)
      exact List.mem_append_right _ later
  | @read next state state' branch branch' answer n _ ih =>
      obtain ⟨world, member, hanswer, hstate, hbranch⟩ := ih
      have done : Completed world := by simp [Completed, hanswer]
      exact ⟨world, completed_mono defs (next state) state branch world done n 1 member,
        hanswer, hstate, hbranch⟩
  | @write written next state state' branch branch' answer n _ ih =>
      obtain ⟨world, member, hanswer, hstate, hbranch⟩ := ih
      have done : Completed world := by simp [Completed, hanswer]
      exact ⟨world, completed_mono defs next written branch world done n 1 member,
        hanswer, hstate, hbranch⟩
  | @intent request next state state' branch branch' answer n _ ih =>
      obtain ⟨world, member, hanswer, hstate, hbranch⟩ := ih
      have done : Completed world := by simp [Completed, hanswer]
      have later := completed_mono defs next state branch world done n 1 member
      refine ⟨{ world with intents := request :: world.intents }, ?_, hanswer, hstate, hbranch⟩
      show { world with intents := request :: world.intents } ∈
        (ProgramZ.runWorldsAt (approx defs (n + 1) next) state branch).map fun result =>
          { result with intents := request :: result.intents }
      exact List.mem_map_of_mem later
  | call _ ih => exact ih

/-- Every answer of the queue-ordered search is reached from an item of its
queue. -/
theorem bfs_leads (defs : Key → RProg Key State Answer Intent) :
    ∀ fuel (queue : List (RProg Key State Answer Intent × State × BranchTrace))
      answer state' branch',
      bfs defs fuel queue = some (answer, state', branch') →
      ∃ item ∈ queue, ∃ n, Leads defs item.1 item.2.1 item.2.2 answer state' branch' n := by
  intro fuel
  induction fuel with
  | zero => intro queue answer state' branch' h; simp [bfs] at h
  | succ fuel ih =>
      intro queue answer state' branch' h
      match queue with
      | [] => simp [bfs] at h
      | (program, state, branch) :: rest =>
          cases program with
          | pure value =>
              simp only [bfs, Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl, rfl⟩ := h
              exact ⟨_, List.mem_cons_self .., 0, .pure _ _ _⟩
          | zero =>
              simp only [bfs] at h
              obtain ⟨item, member, n, lead⟩ := ih rest answer state' branch' h
              exact ⟨item, List.mem_cons_of_mem _ member, n, lead⟩
          | choose left right =>
              simp only [bfs] at h
              obtain ⟨item, member, n, lead⟩ := ih _ answer state' branch' h
              simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at member
              rcases member with member | rfl | rfl
              · exact ⟨item, List.mem_cons_of_mem _ member, n, lead⟩
              · exact ⟨_, List.mem_cons_self .., n + 1, .left lead⟩
              · exact ⟨_, List.mem_cons_self .., n + 1, .right lead⟩
          | read next =>
              simp only [bfs] at h
              obtain ⟨item, member, n, lead⟩ := ih _ answer state' branch' h
              simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at member
              rcases member with member | rfl
              · exact ⟨item, List.mem_cons_of_mem _ member, n, lead⟩
              · exact ⟨_, List.mem_cons_self .., n + 1, .read lead⟩
          | write written next =>
              simp only [bfs] at h
              obtain ⟨item, member, n, lead⟩ := ih _ answer state' branch' h
              simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at member
              rcases member with member | rfl
              · exact ⟨item, List.mem_cons_of_mem _ member, n, lead⟩
              · exact ⟨_, List.mem_cons_self .., n + 1, .write lead⟩
          | intent request next =>
              simp only [bfs] at h
              obtain ⟨item, member, n, lead⟩ := ih _ answer state' branch' h
              simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at member
              rcases member with member | rfl
              · exact ⟨item, List.mem_cons_of_mem _ member, n, lead⟩
              · exact ⟨_, List.mem_cons_self .., n + 1, .intent lead⟩
          | call key next =>
              simp only [bfs] at h
              obtain ⟨item, member, n, lead⟩ := ih _ answer state' branch' h
              simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at member
              rcases member with member | rfl
              · exact ⟨item, List.mem_cons_of_mem _ member, n, lead⟩
              · exact ⟨_, List.mem_cons_self .., n + 1, .call lead⟩

/-- **The queue-ordered search answers whenever an item of its queue leads to
an answer**: every item ahead of that one is served in finitely many steps,
and each step of the path puts its next item at the back of the queue. -/
theorem bfs_complete_queue (defs : Key → RProg Key State Answer Intent) :
    ∀ n (pre post : List (RProg Key State Answer Intent × State × BranchTrace))
      (program : RProg Key State Answer Intent) state branch answer state' branch',
      Leads defs program state branch answer state' branch' n →
      ∃ fuel, (bfs defs fuel (pre ++ (program, state, branch) :: post)).isSome := by
  intro n
  induction n with
  | zero =>
      intro pre
      induction pre with
      | nil =>
          intro post program state branch answer state' branch' lead
          cases lead
          exact ⟨1, by simp [bfs]⟩
      | cons item pre ih =>
          intro post program state branch answer state' branch' lead
          obtain ⟨front, front_state, front_branch⟩ := item
          cases front with
          | pure value => exact ⟨1, by simp [bfs]⟩
          | zero =>
              obtain ⟨fuel, h⟩ := ih post program state branch answer state' branch' lead
              exact ⟨fuel + 1, by simpa [bfs] using h⟩
          | choose left right =>
              obtain ⟨fuel, h⟩ := ih (post ++ [(left, front_state, false :: front_branch),
                (right, front_state, true :: front_branch)]) program state branch answer
                state' branch' lead
              exact ⟨fuel + 1, by simpa [bfs] using h⟩
          | read next =>
              obtain ⟨fuel, h⟩ := ih (post ++ [(next front_state, front_state, front_branch)])
                program state branch answer state' branch' lead
              exact ⟨fuel + 1, by simpa [bfs] using h⟩
          | write written next =>
              obtain ⟨fuel, h⟩ := ih (post ++ [(next, written, front_branch)])
                program state branch answer state' branch' lead
              exact ⟨fuel + 1, by simpa [bfs] using h⟩
          | intent request next =>
              obtain ⟨fuel, h⟩ := ih (post ++ [(next, front_state, front_branch)])
                program state branch answer state' branch' lead
              exact ⟨fuel + 1, by simpa [bfs] using h⟩
          | call key next =>
              obtain ⟨fuel, h⟩ := ih (post ++ [((defs key).bind next, front_state, front_branch)])
                program state branch answer state' branch' lead
              exact ⟨fuel + 1, by simpa [bfs] using h⟩
  | succ n outer =>
      intro pre
      induction pre with
      | nil =>
          intro post program state branch answer state' branch' lead
          cases lead with
          | @left left right _ _ _ _ _ _ child =>
              obtain ⟨fuel, h⟩ := outer post [(right, state, true :: branch)] left state
                (false :: branch) answer state' branch' child
              exact ⟨fuel + 1, by simpa [bfs] using h⟩
          | @right left right _ _ _ _ _ _ child =>
              obtain ⟨fuel, h⟩ := outer (post ++ [(left, state, false :: branch)]) [] right
                state (true :: branch) answer state' branch' child
              exact ⟨fuel + 1, by simpa [bfs] using h⟩
          | @read next _ _ _ _ _ _ child =>
              obtain ⟨fuel, h⟩ := outer post [] (next state) state branch answer state'
                branch' child
              exact ⟨fuel + 1, by simpa [bfs] using h⟩
          | @write written next _ _ _ _ _ _ child =>
              obtain ⟨fuel, h⟩ := outer post [] next written branch answer state' branch' child
              exact ⟨fuel + 1, by simpa [bfs] using h⟩
          | @intent request next _ _ _ _ _ _ child =>
              obtain ⟨fuel, h⟩ := outer post [] next state branch answer state' branch' child
              exact ⟨fuel + 1, by simpa [bfs] using h⟩
          | @call key next _ _ _ _ _ _ child =>
              obtain ⟨fuel, h⟩ := outer post [] ((defs key).bind next) state branch answer
                state' branch' child
              exact ⟨fuel + 1, by simpa [bfs] using h⟩
      | cons item pre ih =>
          intro post program state branch answer state' branch' lead
          obtain ⟨front, front_state, front_branch⟩ := item
          cases front with
          | pure value => exact ⟨1, by simp [bfs]⟩
          | zero =>
              obtain ⟨fuel, h⟩ := ih post program state branch answer state' branch' lead
              exact ⟨fuel + 1, by simpa [bfs] using h⟩
          | choose left right =>
              obtain ⟨fuel, h⟩ := ih (post ++ [(left, front_state, false :: front_branch),
                (right, front_state, true :: front_branch)]) program state branch answer
                state' branch' lead
              exact ⟨fuel + 1, by simpa [bfs] using h⟩
          | read next =>
              obtain ⟨fuel, h⟩ := ih (post ++ [(next front_state, front_state, front_branch)])
                program state branch answer state' branch' lead
              exact ⟨fuel + 1, by simpa [bfs] using h⟩
          | write written next =>
              obtain ⟨fuel, h⟩ := ih (post ++ [(next, written, front_branch)])
                program state branch answer state' branch' lead
              exact ⟨fuel + 1, by simpa [bfs] using h⟩
          | intent request next =>
              obtain ⟨fuel, h⟩ := ih (post ++ [(next, front_state, front_branch)])
                program state branch answer state' branch' lead
              exact ⟨fuel + 1, by simpa [bfs] using h⟩
          | call key next =>
              obtain ⟨fuel, h⟩ := ih (post ++ [((defs key).bind next, front_state, front_branch)])
                program state branch answer state' branch' lead
              exact ⟨fuel + 1, by simpa [bfs] using h⟩

/-- **A queue-ordered search is a fair first-answer search**: each answer it
gives is an observed occurrence, with its branch path and final state, and it
answers whenever the program has an observed occurrence. The queue serves the
oldest pending alternative first, as the recurrent-oldest selection does. -/
theorem bfs_fair (defs : Key → RProg Key State Answer Intent)
    (program : RProg Key State Answer Intent) (state : State) :
    (∀ fuel answer state' branch',
      bfs defs fuel [(program, state, [])] = some (answer, state', branch') →
      ∃ world ∈ Observed defs program state,
        world.answer = some answer ∧ world.state = state' ∧ world.branch = branch') ∧
    ((Observed defs program state).Nonempty →
      ∃ fuel, (bfs defs fuel [(program, state, [])]).isSome) := by
  constructor
  · intro fuel answer state' branch' h
    obtain ⟨item, member, n, lead⟩ := bfs_leads defs fuel _ answer state' branch' h
    simp only [List.mem_singleton] at member
    subst member
    obtain ⟨world, worldMember, hanswer, hstate, hbranch⟩ := mem_approx_of_leads defs lead
    exact ⟨world, ⟨by simp [Completed, hanswer], n, worldMember⟩, hanswer, hstate, hbranch⟩
  · rintro ⟨world, done, n, member⟩
    obtain ⟨answer, hanswer⟩ := Option.isSome_iff_exists.mp done
    obtain ⟨m, lead⟩ := leads_of_mem_approx defs n program state [] world answer member hanswer
    exact bfs_complete_queue defs m [] [] program state [] answer world.state world.branch lead

end Mettapedia.TypeTheory.ContextualCBPV.Recursion
