import Mathlib.Data.List.Perm.Basic
import Mathlib.Tactic

/-!
# Observing a run whose identity acquisitions may be refused

A refused frame-identity acquisition fails the operation that asked for it, and
that operation's caller may take the failure for an ordinary one: backtrack, or
continue another way. A query run therefore records the refusal count when it
begins. Before it yields an answer and when a step fails, it compares the
count; once it has moved, the run ends cut short by capacity, and its
observation is reported incomplete instead of as an exact answer bag
(`petta_machine_identities_exhausted`, `PETTA_MACHINE_STEP_CAPACITY`). A quiet
acquisition, whose caller has a complete fallback, refuses without counting.

The model is a depth-first machine over a search tree. Each acquisition names
how it continues when the identity is minted and when it is refused; which
attempts are refused is an arbitrary oracle. `Search.answers` is the meaning
with identities to spare.

* `refusal_is_incomplete`: a counted refusal during the run makes the run
  incomplete.
* `no_answer_after_refusal`: every answer is yielded while the count is still
  the one the run began with.
* `quiet_refusal_neutral`: when the fallback of every quiet acquisition has the
  answers of its continuation, a complete run yields the answers of the search,
  as a multiset; with no refusal at all it yields them in order.
* Controls: a machine that does not compare the count publishes a complete,
  different answer multiset after a refusal it took for a failure, or absorbed
  on another path; a quiet fallback that drops answers changes them too.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.RefusalObservation

universe u

variable {Answer : Type u}

/-- A search: an answer, a failure, ordered alternatives, or an operation that
needs a frame identity. `acquire counted next refused` continues with `next`
once the identity is minted; when it is refused, the operation fails and its
caller continues with `refused`. Only a counted acquisition moves the count. -/
inductive Search (Answer : Type u)
  | answer : Answer → Search Answer
  | fail : Search Answer
  | choice : Search Answer → Search Answer → Search Answer
  | acquire : Bool → Search Answer → Search Answer → Search Answer
  deriving DecidableEq

/-- The answers of a search with identities to spare, in order. -/
def Search.answers : Search Answer → List Answer
  | .answer a => [a]
  | .fail => []
  | .choice first second => first.answers ++ second.answers
  | .acquire _ next _ => next.answers

def Search.size : Search Answer → Nat
  | .answer _ => 1
  | .fail => 1
  | .choice first second => first.size + second.size + 1
  | .acquire _ next refused => next.size + refused.size + 1

/-- The alternatives still to try, the acquisitions attempted, and the refusal
count. -/
structure Config (Answer : Type u) where
  goals : List (Search Answer)
  attempts : Nat
  refusals : Nat

def weight (goals : List (Search Answer)) : Nat := (goals.map Search.size).sum

/-- What one step does: yield an answer, move silently, run out of
alternatives, or end for want of identities. -/
inductive Outcome (Answer : Type u)
  | answer : Answer → Config Answer → Outcome Answer
  | silent : Config Answer → Outcome Answer
  | exhausted : Outcome Answer
  | capacity : Outcome Answer

/-- One step. `refuses` says which attempts are refused; `guarded` says whether
the machine compares the count with `start` before an answer and after a
failure. -/
def step (refuses : Nat → Bool) (guarded : Bool) (start : Nat) (c : Config Answer) :
    Outcome Answer :=
  match c.goals with
  | [] => .exhausted
  | .answer a :: rest =>
    if guarded ∧ c.refusals ≠ start then .capacity else .answer a { c with goals := rest }
  | .fail :: rest =>
    if guarded ∧ c.refusals ≠ start then .capacity else .silent { c with goals := rest }
  | .choice first second :: rest => .silent { c with goals := first :: second :: rest }
  | .acquire counted next refused :: rest =>
    if refuses c.attempts then
      .silent ⟨refused :: rest, c.attempts + 1, c.refusals + if counted then 1 else 0⟩
    else .silent ⟨next :: rest, c.attempts + 1, c.refusals⟩

/-- A run: the answers yielded with the count at each, whether it ran out of
alternatives, and its final attempts and count. -/
structure Result (Answer : Type u) where
  yields : List (Answer × Nat)
  completed : Bool
  attempts : Nat
  refusals : Nat

def runFuel (refuses : Nat → Bool) (guarded : Bool) (start : Nat) :
    Nat → Config Answer → Result Answer
  | 0, c => ⟨[], false, c.attempts, c.refusals⟩
  | fuel + 1, c =>
    match step refuses guarded start c with
    | .exhausted => ⟨[], true, c.attempts, c.refusals⟩
    | .capacity => ⟨[], false, c.attempts, c.refusals⟩
    | .answer a next =>
      let rest := runFuel refuses guarded start fuel next
      ⟨(a, c.refusals) :: rest.yields, rest.completed, rest.attempts, rest.refusals⟩
    | .silent next => runFuel refuses guarded start fuel next

/-- A run to its end: every step consumes weight, so this much fuel suffices. -/
def run (refuses : Nat → Bool) (guarded : Bool) (start : Nat) (c : Config Answer) :
    Result Answer :=
  runFuel refuses guarded start (weight c.goals + 1) c

/-- What the run reports: its answers, when it ran out of alternatives, or that
it was cut short. -/
inductive Observation (Answer : Type u)
  | exact : List Answer → Observation Answer
  | incomplete : Observation Answer
  deriving DecidableEq

/-- The observation of a search run from a count of `start`. -/
def observe (refuses : Nat → Bool) (guarded : Bool) (start : Nat) (s : Search Answer) :
    Observation Answer :=
  let result := run refuses guarded start ⟨[s], 0, start⟩
  if result.completed then .exact (result.yields.map Prod.fst) else .incomplete

/-! ## Running to the end -/

theorem size_pos (s : Search Answer) : 0 < s.size := by
  cases s <;> simp [Search.size]

theorem step_weight {refuses : Nat → Bool} {guarded : Bool} {start : Nat} {c : Config Answer} :
    (∀ a next, step refuses guarded start c = .answer a next →
      weight next.goals < weight c.goals) ∧
    (∀ next, step refuses guarded start c = .silent next →
      weight next.goals < weight c.goals) := by
  unfold step
  rcases c with ⟨goals, attempts, refusals⟩
  cases goals with
  | nil => simp
  | cons g rest =>
    cases g with
    | answer a =>
      dsimp only
      split_ifs <;> simp [weight, Search.size]
    | fail =>
      dsimp only
      split_ifs <;> simp [weight, Search.size]
    | choice first second =>
      simp only [Outcome.silent.injEq, reduceCtorEq, IsEmpty.forall_iff, implies_true,
        forall_eq', true_and, weight, List.map_cons, List.sum_cons, Search.size]
      omega
    | acquire counted next refused =>
      dsimp only
      split_ifs <;> simp [weight, Search.size]

theorem runFuel_enough {refuses : Nat → Bool} {guarded : Bool} {start : Nat} :
    ∀ (fuel fuel' : Nat) (c : Config Answer), weight c.goals < fuel → weight c.goals < fuel' →
      runFuel refuses guarded start fuel c = runFuel refuses guarded start fuel' c := by
  intro fuel
  induction fuel with
  | zero => intro _ _ low; omega
  | succ fuel ih =>
    intro fuel' c enough enough'
    obtain ⟨fuel', rfl⟩ : ∃ f, fuel' = f + 1 := ⟨fuel' - 1, by omega⟩
    simp only [runFuel]
    have weights := step_weight (refuses := refuses) (guarded := guarded) (start := start) (c := c)
    split
    · rfl
    · rfl
    · rename_i a next stepped
      have := weights.1 a next stepped
      rw [ih fuel' next (by omega) (by omega)]
    · rename_i next stepped
      have := weights.2 next stepped
      exact ih fuel' next (by omega) (by omega)

/-- The run's recursive equation. -/
theorem run_eq (refuses : Nat → Bool) (guarded : Bool) (start : Nat) (c : Config Answer) :
    run refuses guarded start c =
      match step refuses guarded start c with
      | .exhausted => ⟨[], true, c.attempts, c.refusals⟩
      | .capacity => ⟨[], false, c.attempts, c.refusals⟩
      | .answer a next =>
        ⟨(a, c.refusals) :: (run refuses guarded start next).yields,
          (run refuses guarded start next).completed, (run refuses guarded start next).attempts,
          (run refuses guarded start next).refusals⟩
      | .silent next => run refuses guarded start next := by
  have weights := step_weight (refuses := refuses) (guarded := guarded) (start := start) (c := c)
  rw [run, runFuel.eq_2]
  split
  · rfl
  · rfl
  · rename_i a next stepped
    have := weights.1 a next stepped
    rw [run, runFuel_enough (weight c.goals) (weight next.goals + 1) next (by omega) (by omega)]
  · rename_i next stepped
    have := weights.2 next stepped
    rw [run]
    exact runFuel_enough _ _ next (by omega) (by omega)

/-- First one run, then, if it ran out of alternatives, another from where it
stopped. -/
def Result.andThen (first : Result Answer) (next : Nat → Nat → Result Answer) :
    Result Answer :=
  if first.completed then
    ⟨first.yields ++ (next first.attempts first.refusals).yields,
      (next first.attempts first.refusals).completed,
      (next first.attempts first.refusals).attempts,
      (next first.attempts first.refusals).refusals⟩
  else first

/-- The machine is depth-first: running a stack is running its first part,
then the rest. -/
theorem run_append (refuses : Nat → Bool) (guarded : Bool) (start : Nat) :
    ∀ (n : Nat) (goals rest : List (Search Answer)) (attempts refusals : Nat),
      weight goals < n →
      run refuses guarded start ⟨goals ++ rest, attempts, refusals⟩ =
        (run refuses guarded start ⟨goals, attempts, refusals⟩).andThen
          fun attempts' refusals' => run refuses guarded start ⟨rest, attempts', refusals'⟩ := by
  intro n
  induction n with
  | zero => intro _ _ _ _ low; omega
  | succ n ih =>
    intro goals rest attempts refusals small
    cases goals with
    | nil =>
      rw [List.nil_append]
      conv_rhs => rw [run_eq]
      simp [step, Result.andThen]
    | cons g more =>
      rw [run_eq, run_eq (c := ⟨g :: more, attempts, refusals⟩)]
      have sizes : g.size + weight more = weight (g :: more) := by
        simp [weight]
      have bound := small
      simp only [weight, List.map_cons, List.sum_cons] at bound
      cases g with
      | answer a =>
        simp only [Search.size] at bound
        simp only [List.cons_append, step]
        split_ifs with guard
        · simp [Result.andThen]
        · have := ih more rest attempts refusals (by unfold weight; omega)
          simp only [this, Result.andThen]
          split_ifs <;> simp
      | fail =>
        simp only [Search.size] at bound
        simp only [List.cons_append, step]
        split_ifs with guard
        · simp [Result.andThen]
        · exact ih more rest attempts refusals (by unfold weight; omega)
      | choice first second =>
        simp only [Search.size] at bound
        simp only [List.cons_append, step]
        have := ih (first :: second :: more) rest attempts refusals
          (by simp only [weight, List.map_cons, List.sum_cons]; omega)
        simpa using this
      | acquire counted next refused =>
        simp only [Search.size] at bound
        simp only [List.cons_append, step]
        by_cases refusedHere : refuses attempts = true
        · rw [if_pos refusedHere, if_pos refusedHere]
          have := ih (refused :: more) rest (attempts + 1)
            (refusals + if counted then 1 else 0)
            (by simp only [weight, List.map_cons, List.sum_cons]; omega)
          simpa using this
        · rw [if_neg refusedHere, if_neg refusedHere]
          have := ih (next :: more) rest (attempts + 1) refusals
            (by simp only [weight, List.map_cons, List.sum_cons]; omega)
          simpa using this

theorem run_cons (refuses : Nat → Bool) (guarded : Bool) (start : Nat) (g : Search Answer)
    (rest : List (Search Answer)) (attempts refusals : Nat) :
    run refuses guarded start ⟨g :: rest, attempts, refusals⟩ =
      (run refuses guarded start ⟨[g], attempts, refusals⟩).andThen
        fun attempts' refusals' => run refuses guarded start ⟨rest, attempts', refusals'⟩ :=
  run_append refuses guarded start _ [g] rest attempts refusals (Nat.lt_succ_self _)

theorem run_nil (refuses : Nat → Bool) (guarded : Bool) (start attempts refusals : Nat) :
    run refuses guarded start (⟨[], attempts, refusals⟩ : Config Answer) =
      ⟨[], true, attempts, refusals⟩ := by
  rw [run_eq]; rfl

theorem run_answer (refuses : Nat → Bool) (guarded : Bool) (start : Nat) (a : Answer)
    (attempts refusals : Nat) :
    run refuses guarded start ⟨[.answer a], attempts, refusals⟩ =
      if guarded = true ∧ refusals ≠ start then ⟨[], false, attempts, refusals⟩
      else ⟨[(a, refusals)], true, attempts, refusals⟩ := by
  rw [run_eq]
  simp only [step]
  split_ifs <;> simp [run_nil]

theorem run_fail (refuses : Nat → Bool) (guarded : Bool) (start attempts refusals : Nat) :
    run refuses guarded start (⟨[.fail], attempts, refusals⟩ : Config Answer) =
      if guarded = true ∧ refusals ≠ start then ⟨[], false, attempts, refusals⟩
      else ⟨[], true, attempts, refusals⟩ := by
  rw [run_eq]
  simp only [step]
  split_ifs <;> simp [run_nil]

theorem run_choice (refuses : Nat → Bool) (guarded : Bool) (start : Nat)
    (first second : Search Answer) (attempts refusals : Nat) :
    run refuses guarded start ⟨[.choice first second], attempts, refusals⟩ =
      (run refuses guarded start ⟨[first], attempts, refusals⟩).andThen
        fun attempts' refusals' => run refuses guarded start ⟨[second], attempts', refusals'⟩ := by
  rw [run_eq]
  exact run_cons refuses guarded start first [second] attempts refusals

theorem run_acquire (refuses : Nat → Bool) (guarded : Bool) (start : Nat) (counted : Bool)
    (next refused : Search Answer) (attempts refusals : Nat) :
    run refuses guarded start ⟨[.acquire counted next refused], attempts, refusals⟩ =
      if refuses attempts then
        run refuses guarded start ⟨[refused], attempts + 1, refusals + if counted then 1 else 0⟩
      else run refuses guarded start ⟨[next], attempts + 1, refusals⟩ := by
  rw [run_eq]
  simp only [step]
  split_ifs <;> rfl

theorem andThen_completed (first : Result Answer) (next : Nat → Nat → Result Answer) :
    (first.andThen next).completed = true ↔
      first.completed = true ∧ (next first.attempts first.refusals).completed = true := by
  unfold Result.andThen
  split_ifs with done <;> simp [done]

theorem andThen_of_completed {first : Result Answer} (next : Nat → Nat → Result Answer)
    (done : first.completed = true) :
    (first.andThen next).yields = first.yields ++ (next first.attempts first.refusals).yields ∧
      (first.andThen next).refusals = (next first.attempts first.refusals).refusals := by
  unfold Result.andThen
  rw [if_pos done]
  exact ⟨rfl, rfl⟩

/-! ## The count never decreases, and a moved count stops the run -/

/-- An answer step keeps the count and, when guarded, happens only at the count
the run began with. -/
theorem step_answer {refuses : Nat → Bool} {guarded : Bool} {start : Nat}
    {c : Config Answer} {a : Answer} {next : Config Answer}
    (stepped : step refuses guarded start c = .answer a next) :
    next.refusals = c.refusals ∧ (guarded = true → c.refusals = start) := by
  rcases c with ⟨goals, attempts, refusals⟩
  cases goals with
  | nil => simp [step] at stepped
  | cons g rest =>
    cases g with
    | answer b =>
      simp only [step] at stepped
      split_ifs at stepped with guard
      cases stepped
      refine ⟨rfl, fun guarded => ?_⟩
      subst guarded
      simp only [true_and, ne_eq, not_not] at guard
      exact guard
    | fail =>
      simp only [step] at stepped
      split_ifs at stepped
    | choice first second => simp [step] at stepped
    | acquire counted next refused =>
      simp only [step] at stepped
      split_ifs at stepped

/-- A silent step never lowers the count. -/
theorem step_silent {refuses : Nat → Bool} {guarded : Bool} {start : Nat}
    {c next : Config Answer} (stepped : step refuses guarded start c = .silent next) :
    c.refusals ≤ next.refusals := by
  rcases c with ⟨goals, attempts, refusals⟩
  cases goals with
  | nil => simp [step] at stepped
  | cons g rest =>
    cases g with
    | answer b =>
      simp only [step] at stepped
      split_ifs at stepped
    | fail =>
      simp only [step] at stepped
      split_ifs at stepped
      cases stepped
      exact Nat.le_refl _
    | choice first second =>
      simp only [step] at stepped
      cases stepped
      exact Nat.le_refl _
    | acquire counted next refused =>
      simp only [step] at stepped
      split_ifs at stepped <;> cases stepped <;> dsimp only <;> omega

theorem run_refusals_monotone (refuses : Nat → Bool) (guarded : Bool) (start : Nat) :
    ∀ (n : Nat) (c : Config Answer), weight c.goals < n →
      c.refusals ≤ (run refuses guarded start c).refusals := by
  intro n
  induction n with
  | zero => intro _ low; omega
  | succ n ih =>
    intro c small
    have weights := step_weight (refuses := refuses) (guarded := guarded) (start := start) (c := c)
    rw [run_eq]
    split
    · exact Nat.le_refl _
    · exact Nat.le_refl _
    · rename_i a next stepped
      have less := weights.1 a next stepped
      rw [← (step_answer stepped).1]
      exact ih next (by omega)
    · rename_i next stepped
      have less := weights.2 next stepped
      exact (step_silent stepped).trans (ih next (by omega))

/-- Once the count has moved, a guarded machine yields nothing more and ends
cut short: every path reaches an answer or a failure, where it compares. -/
theorem moved_count_stops (refuses : Nat → Bool) (start : Nat) :
    ∀ (n : Nat) (c : Config Answer), weight c.goals < n → start < c.refusals → c.goals ≠ [] →
      (run refuses true start c).yields = [] ∧ (run refuses true start c).completed = false := by
  intro n
  induction n with
  | zero => intro _ low; omega
  | succ n ih =>
    intro c small moved nonempty
    rcases c with ⟨goals, attempts, refusals⟩
    cases goals with
    | nil => exact absurd rfl nonempty
    | cons g rest =>
      dsimp only at moved small
      have bound := small
      simp only [weight, List.map_cons, List.sum_cons] at bound
      rw [run_eq]
      cases g with
      | answer a =>
        simp only [step]
        split_ifs with guard
        · exact ⟨rfl, rfl⟩
        · simp only [true_and, ne_eq, not_not] at guard
          omega
      | fail =>
        simp only [step]
        split_ifs with guard
        · exact ⟨rfl, rfl⟩
        · simp only [true_and, ne_eq, not_not] at guard
          omega
      | choice first second =>
        simp only [Search.size] at bound
        simp only [step]
        exact ih ⟨first :: second :: rest, attempts, refusals⟩
          (by simp only [weight, List.map_cons, List.sum_cons]; omega) moved (by simp)
      | acquire counted next refused =>
        simp only [Search.size] at bound
        simp only [step]
        by_cases refusedHere : refuses attempts = true
        · rw [if_pos refusedHere]
          exact ih ⟨refused :: rest, attempts + 1, refusals + if counted then 1 else 0⟩
            (by simp only [weight, List.map_cons, List.sum_cons]; omega)
            (by dsimp only; split_ifs <;> omega) (by simp)
        · rw [if_neg refusedHere]
          exact ih ⟨next :: rest, attempts + 1, refusals⟩
            (by simp only [weight, List.map_cons, List.sum_cons]; omega) moved (by simp)

/-! ## What a guarded run reports -/

/-- Every answer a guarded run yields is yielded while the count is still the
one it began with: none follows a counted refusal. -/
theorem no_answer_after_refusal (refuses : Nat → Bool) (start : Nat) :
    ∀ (n : Nat) (c : Config Answer), weight c.goals < n →
      ∀ y ∈ (run refuses true start c).yields, y.2 = start := by
  intro n
  induction n with
  | zero => intro _ low; omega
  | succ n ih =>
    intro c small y member
    have weights := step_weight (refuses := refuses) (guarded := true) (start := start) (c := c)
    rw [run_eq] at member
    split at member
    · simp at member
    · simp at member
    · rename_i a next stepped
      have less := weights.1 a next stepped
      rcases List.mem_cons.mp member with rfl | later
      · exact (step_answer stepped).2 rfl
      · exact ih next (by omega) y later
    · rename_i next stepped
      exact ih next (by have := weights.2 next stepped; omega) y member

/-- A guarded run that runs out of alternatives ends with the count it began
with. -/
theorem completed_unmoved (refuses : Nat → Bool) (start : Nat) :
    ∀ (s : Search Answer) (attempts : Nat),
      (run refuses true start ⟨[s], attempts, start⟩).completed = true →
      (run refuses true start ⟨[s], attempts, start⟩).refusals = start := by
  intro s
  induction s with
  | answer a =>
    intro attempts _
    rw [run_answer, if_neg (by simp)]
  | fail =>
    intro attempts _
    rw [run_fail, if_neg (by simp)]
  | choice first second firstIh secondIh =>
    intro attempts done
    rw [run_choice] at done ⊢
    obtain ⟨firstDone, secondDone⟩ := (andThen_completed _ _).mp done
    have firstSame := firstIh attempts firstDone
    rw [(andThen_of_completed _ firstDone).2]
    rw [firstSame] at secondDone ⊢
    exact secondIh _ secondDone
  | acquire counted next refused nextIh refusedIh =>
    intro attempts done
    rw [run_acquire] at done ⊢
    by_cases refusedHere : refuses attempts = true
    · rw [if_pos refusedHere] at done ⊢
      cases counted
      · rw [if_neg Bool.false_ne_true, Nat.add_zero] at done ⊢
        exact refusedIh (attempts + 1) done
      · rw [if_pos rfl] at done
        have := (moved_count_stops refuses start _ ⟨[refused], attempts + 1, start + 1⟩
          (Nat.lt_succ_self _) (by dsimp only; omega) (by simp)).2
        rw [this] at done
        exact absurd done Bool.false_ne_true
    · rw [if_neg refusedHere] at done ⊢
      exact nextIh (attempts + 1) done

/-- A counted refusal during a guarded run makes it incomplete. -/
theorem refusal_is_incomplete (refuses : Nat → Bool) (start : Nat) (s : Search Answer)
    (attempts : Nat) (refused : start < (run refuses true start ⟨[s], attempts, start⟩).refusals) :
    (run refuses true start ⟨[s], attempts, start⟩).completed = false := by
  cases done : (run refuses true start ⟨[s], attempts, start⟩).completed with
  | false => rfl
  | true =>
    have := completed_unmoved refuses start s attempts done
    omega

/-- Every quiet acquisition's fallback has the answers of its continuation. -/
def Neutral : Search Answer → Prop
  | .answer _ => True
  | .fail => True
  | .choice first second => Neutral first ∧ Neutral second
  | .acquire counted next refused =>
    Neutral next ∧ Neutral refused ∧ (counted = false → refused.answers.Perm next.answers)

/-- With neutral quiet fallbacks, a guarded run that runs out of alternatives
yields the search's answers, as a multiset. -/
theorem quiet_refusal_neutral (refuses : Nat → Bool) (start : Nat) :
    ∀ (s : Search Answer) (attempts : Nat), Neutral s →
      (run refuses true start ⟨[s], attempts, start⟩).completed = true →
      ((run refuses true start ⟨[s], attempts, start⟩).yields.map Prod.fst).Perm s.answers := by
  intro s
  induction s with
  | answer a =>
    intro attempts _ _
    rw [run_answer, if_neg (by simp)]
    simp [Search.answers]
  | fail =>
    intro attempts _ _
    rw [run_fail, if_neg (by simp)]
    simp [Search.answers]
  | choice first second firstIh secondIh =>
    intro attempts neutral done
    rw [run_choice] at done ⊢
    obtain ⟨firstDone, secondDone⟩ := (andThen_completed _ _).mp done
    have firstSame := completed_unmoved refuses start first attempts firstDone
    rw [(andThen_of_completed _ firstDone).1, List.map_append, Search.answers]
    rw [firstSame] at secondDone ⊢
    exact (firstIh attempts neutral.1 firstDone).append (secondIh _ neutral.2 secondDone)
  | acquire counted next refused nextIh refusedIh =>
    intro attempts neutral done
    obtain ⟨nextNeutral, refusedNeutral, fallback⟩ := neutral
    rw [run_acquire] at done ⊢
    by_cases refusedHere : refuses attempts = true
    · rw [if_pos refusedHere] at done ⊢
      cases counted
      · rw [if_neg Bool.false_ne_true, Nat.add_zero] at done ⊢
        exact (refusedIh (attempts + 1) refusedNeutral done).trans (fallback rfl)
      · rw [if_pos rfl] at done
        have := (moved_count_stops refuses start _ ⟨[refused], attempts + 1, start + 1⟩
          (Nat.lt_succ_self _) (by dsimp only; omega) (by simp)).2
        rw [this] at done
        exact absurd done Bool.false_ne_true
    · rw [if_neg refusedHere] at done ⊢
      exact nextIh (attempts + 1) nextNeutral done

/-- An exact observation of a guarded run, with neutral quiet fallbacks, is the
search's answer multiset; one that a counted refusal touched is never exact. -/
theorem observation_sound (refuses : Nat → Bool) (start : Nat) (s : Search Answer)
    (neutral : Neutral s) :
    (∀ answers, observe refuses true start s = .exact answers → answers.Perm s.answers) ∧
      (start < (run refuses true start ⟨[s], 0, start⟩).refusals →
        observe refuses true start s = .incomplete) := by
  constructor
  · intro answers observed
    unfold observe at observed
    dsimp only at observed
    split_ifs at observed with done
    · cases observed
      exact quiet_refusal_neutral refuses start s 0 neutral done
  · intro moved
    unfold observe
    dsimp only
    rw [refusal_is_incomplete refuses start s 0 moved]
    rfl

/-- With identities to spare, both machines yield the search's answers in
order. -/
theorem unrefused_exact (guarded : Bool) (start : Nat) :
    ∀ (s : Search Answer) (attempts : Nat),
      (run (fun _ => false) guarded start ⟨[s], attempts, start⟩).completed = true ∧
        (run (fun _ => false) guarded start ⟨[s], attempts, start⟩).yields.map Prod.fst =
          s.answers ∧
        (run (fun _ => false) guarded start ⟨[s], attempts, start⟩).refusals = start := by
  intro s
  induction s with
  | answer a =>
    intro attempts
    rw [run_answer, if_neg (by simp)]
    simp [Search.answers]
  | fail =>
    intro attempts
    rw [run_fail, if_neg (by simp)]
    simp [Search.answers]
  | choice first second firstIh secondIh =>
    intro attempts
    rw [run_choice]
    obtain ⟨firstDone, firstAnswers, firstSame⟩ := firstIh attempts
    obtain ⟨yields, refusals⟩ := andThen_of_completed
      (fun attempts' refusals' =>
        run (fun _ => false) guarded start ⟨[second], attempts', refusals'⟩) firstDone
    rw [firstSame] at yields refusals
    obtain ⟨secondDone, secondAnswers, secondSame⟩ := secondIh
      (run (fun _ => false) guarded start ⟨[first], attempts, start⟩).attempts
    refine ⟨(andThen_completed _ _).mpr ⟨firstDone, by rw [firstSame]; exact secondDone⟩, ?_, ?_⟩
    · rw [yields, List.map_append, firstAnswers, secondAnswers]
      rfl
    · rw [refusals, secondSame]
  | acquire counted next refused nextIh _ =>
    intro attempts
    rw [run_acquire, if_neg (by simp)]
    obtain ⟨nextDone, nextAnswers, nextSame⟩ := nextIh (attempts + 1)
    exact ⟨nextDone, nextAnswers, nextSame⟩

theorem unrefused_observe (guarded : Bool) (start : Nat) (s : Search Answer) :
    observe (fun _ => false) guarded start s = .exact s.answers := by
  unfold observe
  obtain ⟨done, answers, _⟩ := unrefused_exact (Answer := Answer) guarded start s 0
  dsimp only
  rw [if_pos done, answers]

/-! ## Controls -/

namespace Controls

/-- The first acquisition is refused. -/
def firstRefused (attempt : Nat) : Bool := attempt == 0

/-- A counted acquisition whose refusal fails its branch, before another
answer. -/
def failingBranch : Search Nat := .choice (.acquire true (.answer 1) .fail) (.answer 2)

/-- Taking the refusal for an ordinary failure publishes a complete, different
answer multiset; comparing the count reports the run incomplete. -/
theorem defect_changes_answers :
    failingBranch.answers = [1, 2] ∧
      observe firstRefused false 0 failingBranch = .exact [2] ∧
      ¬ [2].Perm failingBranch.answers ∧
      observe firstRefused true 0 failingBranch = .incomplete := by
  refine ⟨rfl, by decide, ?_, by decide⟩
  intro perm
  have := perm.length_eq
  simp [failingBranch, Search.answers] at this

/-- A counted refusal absorbed on another path: the caller continues with a
different answer instead of failing. The unguarded machine publishes it; the
guarded one catches the moved count at that answer. -/
def absorbedBranch : Search Nat := .choice (.acquire true (.answer 1) (.answer 3)) (.answer 2)

theorem absorbed_refusal_caught :
    observe firstRefused false 0 absorbedBranch = .exact [3, 2] ∧
      ¬ [3, 2].Perm absorbedBranch.answers ∧
      observe firstRefused true 0 absorbedBranch = .incomplete := by
  refine ⟨by decide, ?_, by decide⟩
  intro perm
  have := perm.mem_iff (a := 3)
  simp [absorbedBranch, Search.answers] at this

/-- A quiet refusal with a neutral fallback leaves the observation exact. -/
def quietBranch : Search Nat := .choice (.acquire false (.answer 1) (.answer 1)) (.answer 2)

theorem quiet_neutral_exact :
    Neutral quietBranch ∧ observe firstRefused true 0 quietBranch = .exact [1, 2] ∧
      (run firstRefused true 0 ⟨[quietBranch], 0, 0⟩).refusals = 0 := by
  refine ⟨⟨⟨trivial, trivial, fun _ => List.Perm.refl _⟩, trivial⟩, by decide, by decide⟩

/-- The neutrality premise is needed: a quiet fallback that drops the answer
gives an exact but wrong observation. -/
def droppingBranch : Search Nat := .choice (.acquire false (.answer 1) .fail) (.answer 2)

theorem quiet_fallback_must_be_neutral :
    ¬ Neutral droppingBranch ∧ observe firstRefused true 0 droppingBranch = .exact [2] ∧
      ¬ [2].Perm droppingBranch.answers := by
  refine ⟨?_, by decide, ?_⟩
  · rintro ⟨⟨_, _, fallback⟩, _⟩
    have := (fallback rfl).length_eq
    simp [Search.answers] at this
  · intro perm
    have := perm.length_eq
    simp [droppingBranch, Search.answers] at this

/-- Answers yielded before the refusal stay yielded by the machine; the
observation, being incomplete, does not publish them as a bag. -/
def lateRefusal : Search Nat := .choice (.answer 1) (.acquire true (.answer 2) .fail)

theorem earlier_answers_not_exact :
    (run firstRefused true 0 ⟨[lateRefusal], 0, 0⟩).yields = [(1, 0)] ∧
      observe firstRefused true 0 lateRefusal = .incomplete := by
  constructor <;> decide

end Controls

end Mettapedia.Machines.RefusalObservation
