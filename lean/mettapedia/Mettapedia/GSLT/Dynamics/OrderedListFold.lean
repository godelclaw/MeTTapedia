import Mettapedia.GSLT.Core.GSLT
import Mathlib.Data.List.Basic

/-!
# Small-step execution of an ordered list fold

The machine consumes one entry per transition and retains its accumulator.
Completion agrees with the independent `List.foldl` evaluator. Every complete
path has exactly one transition per entry and one finalization transition.
No commutativity or associativity of the supplied operation is assumed.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Dynamics.OrderedListFold

open Mettapedia.GSLT

variable {Item Acc : Type}

inductive State (Item Acc : Type*) where
  | active (remaining : List Item) (accumulator : Acc)
  | done (result : Acc)

inductive Step (operation : Acc → Item → Acc) : State Item Acc → State Item Acc → Prop where
  | consume (entry : Item) (rest : List Item) (accumulator : Acc) :
      Step operation (.active (entry :: rest) accumulator)
        (.active rest (operation accumulator entry))
  | finish (accumulator : Acc) : Step operation (.active [] accumulator) (.done accumulator)

/-- The step relation has no result premise or whole-fold oracle. -/
def theory (operation : Acc → Item → Acc) : GSLT where
  Term := State Item Acc
  equations := ⟨Eq, ⟨Eq.refl, Eq.symm, Eq.trans⟩⟩
  rewrites := Step operation
  rewrites_resp_left := by
    intro source source' target equal step
    subst source'
    exact ⟨target, step, rfl⟩
  rewrites_resp_right := by
    intro source target target' step equal
    subst target'
    exact step

def step? (operation : Acc → Item → Acc) : State Item Acc → Option (State Item Acc)
  | .active (entry :: rest) accumulator => some (.active rest (operation accumulator entry))
  | .active [] accumulator => some (.done accumulator)
  | .done _ => none

theorem step?_eq_some_iff (operation : Acc → Item → Acc) (source target : State Item Acc) :
    step? operation source = some target ↔ Step operation source target := by
  constructor
  · intro executed
    cases source with
    | active remaining accumulator =>
        cases remaining <;> simp only [step?, Option.some.injEq] at executed
        all_goals subst target; constructor
    | done _ => simp [step?] at executed
  · intro transition
    cases transition <;> rfl

theorem step_deterministic (operation : Acc → Item → Acc)
    {source first second : State Item Acc}
    (one : Step operation source first) (two : Step operation source second) : first = second := by
  exact Option.some.inj
    ((step?_eq_some_iff operation source first).2 one |>.symm.trans
      ((step?_eq_some_iff operation source second).2 two))

/-- Completing a residual state uses the independently defined list fold. -/
def completion (operation : Acc → Item → Acc) : State Item Acc → Acc
  | .active remaining accumulator => remaining.foldl operation accumulator
  | .done result => result

theorem step_preserves_completion (operation : Acc → Item → Acc)
    {source target : State Item Acc} (step : Step operation source target) :
    completion operation source = completion operation target := by
  cases step <;> rfl

/-- Rank counts remaining entry visits plus the finalization transition. -/
def rank : State Item Acc → Nat
  | .active remaining _ => remaining.length + 1
  | .done _ => 0

theorem step_rank (operation : Acc → Item → Acc)
    {source target : State Item Acc} (step : Step operation source target) :
    rank source = rank target + 1 := by
  cases step <;> simp [rank]

def runPath (operation : Acc → Item → Acc) :
    (remaining : List Item) → (accumulator : Acc) →
    (theory operation).RewritePath (.active remaining accumulator)
      (.done (remaining.foldl operation accumulator))
  | [], accumulator => .cons (.finish accumulator) (.nil _)
  | entry :: rest, accumulator =>
      .cons (.consume entry rest accumulator) (runPath operation rest (operation accumulator entry))

/-- Every path, including a partial one, accounts for all consumed work. -/
theorem path_rank (operation : Acc → Item → Acc)
    {source target : State Item Acc} (path : (theory operation).RewritePath source target) :
    rank source = path.length + rank target := by
  exact GSLT.RewritePath.rec
    (S := theory operation)
    (motive := fun source target path => rank source = path.length + rank target)
    (fun _ => by simp [GSLT.RewritePath.length])
    (fun step rest inductionHypothesis => by
      rw [step_rank operation step, inductionHypothesis]
      simp [GSLT.RewritePath.length, Nat.add_comm, Nat.add_left_comm]) path

theorem path_completion (operation : Acc → Item → Acc)
    {source target : State Item Acc} (path : (theory operation).RewritePath source target) :
    completion operation source = completion operation target := by
  exact GSLT.RewritePath.rec
    (S := theory operation)
    (motive := fun source target _ => completion operation source = completion operation target)
    (fun _ => rfl)
    (fun step _ inductionHypothesis =>
      (step_preserves_completion operation step).trans inductionHypothesis) path

/-- No alternative result or extra complete-path length is licensed by the
operational relation, regardless of which path was supplied. -/
theorem complete_path (operation : Acc → Item → Acc)
    (entries : List Item) (initial result : Acc)
    (path : (theory operation).RewritePath (.active entries initial) (.done result)) :
    result = entries.foldl operation initial ∧ path.length = entries.length + 1 := by
  refine ⟨(path_completion operation path).symm, ?_⟩
  simpa [rank] using (path_rank operation path).symm

theorem done_normal (operation : Acc → Item → Acc) (result : Acc) :
    (theory operation).IsNormalForm (.done result) := by
  rintro ⟨target, step⟩
  cases step

/-- Splitting the input preserves the sequential fold, including its order. -/
theorem chunk_result (operation : Acc → Item → Acc) (first second : List Item) (initial : Acc) :
    (first ++ second).foldl operation initial =
      second.foldl operation (first.foldl operation initial) := List.foldl_append

namespace Controls

/-- Associative chunking does not justify reordering an arbitrary operation. -/
theorem reordering_changes_result :
    ([1, 2] : List Nat).foldl (fun total entry => 10 * total + entry) 0 = 12 ∧
      ([2, 1] : List Nat).foldl (fun total entry => 10 * total + entry) 0 = 21 := by
  decide

/-- Repeated input occurrences each produce their own transition. -/
theorem duplicate_entries_are_visited :
    (runPath (Nat.add) [1, 1] 0).length = 3 := by
  exact (complete_path Nat.add [1, 1] 0 2 (runPath Nat.add [1, 1] 0)).2

end Controls

end Mettapedia.GSLT.Dynamics.OrderedListFold
