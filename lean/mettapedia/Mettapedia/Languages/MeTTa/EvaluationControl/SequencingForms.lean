import Mettapedia.Languages.MeTTa.OSLFCore.Atom
import Mathlib.Data.List.Basic

/-!
# Sequencing forms: `do`, `progn` and `let*`

A block runs statements in order. A statement either binds the answer of a
computation to a name, or runs a computation and discards its answer.

* `runDo` reads a block as nested binds in any monad. `do_is_letStar` proves
  that it is exactly `let*` whose binders are a variable (for a binding) or a
  wildcard (for a discarded statement), in every monad with failure. So `do`
  adds no semantics of its own over `let*`; `progn` is the block whose
  statements are all discarded.
* What can make a block differ is not the sugar but four choices made beside
  it, each separated here by a two-line witness in the bag monad of answers:
  - `unitPattern_drops_branch`: a discarded statement written as the pattern
    `()` drops the branch when the statement answers anything other than the
    empty expression (a printing operation that answers `true`);
  - `committed_ne_bag`: keeping only the first answer of each statement
    (committed choice) differs from binding every answer;
    `committed_eq_bag_of_deterministic` shows they agree when every statement
    has at most one answer;
  - `lexical_ne_unify`: rebinding a name shadows under lexical scope and
    constrains under logic-variable scope; `lexical_eq_unify_of_fresh` shows
    they agree when the name is fresh;
  - `progn_multiplies`: a discarded statement with two answers runs the rest
    of the block twice.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.EvaluationControl.SequencingForms

open Mettapedia.Languages.MeTTa.OSLFCore (Atom GroundedValue)

/-! ## Blocks over any monad -/

/-- A statement over the values bound so far (newest first). -/
inductive Stmt (m : Type → Type) (α : Type) where
  /-- Bind the statement's answer: `(<- $x e)`. -/
  | bind (k : List α → m α)
  /-- Run the statement and discard its answer. -/
  | exec (k : List α → m α)

/-- A block as nested binds. -/
def runDo {m : Type → Type} [Monad m] {α β : Type} :
    List (Stmt m α) → (List α → m β) → List α → m β
  | [], ret, env => ret env
  | .bind k :: rest, ret, env => k env >>= fun v => runDo rest ret (v :: env)
  | .exec k :: rest, ret, env => k env >>= fun _ => runDo rest ret env

/-- A binder of `let*`: a pattern that may bind values or fail. -/
abbrev Pat (α : Type) := α → Option (List α)

/-- `let*`: each binding runs its computation and matches every answer against
its pattern; a failed match fails the branch. -/
def letStar {m : Type → Type} [AlternativeMonad m] {α β : Type} :
    List (Pat α × (List α → m α)) → (List α → m β) → List α → m β
  | [], ret, env => ret env
  | (p, k) :: rest, ret, env =>
      k env >>= fun v =>
        match p v with
        | some bound => letStar rest ret (bound ++ env)
        | none => failure

/-- The variable pattern binds every answer. -/
def patVar {α : Type} : Pat α := fun v => some [v]

/-- The wildcard pattern matches every answer and binds nothing. -/
def patWild {α : Type} : Pat α := fun _ => some []

/-- The binding `let*` uses for each statement of a block. -/
def Stmt.toBinding {m : Type → Type} {α : Type} : Stmt m α → Pat α × (List α → m α)
  | .bind k => (patVar, k)
  | .exec k => (patWild, k)

/-- `do` is `let*` with variable and wildcard binders, in every monad with
failure. -/
theorem do_is_letStar {m : Type → Type} [AlternativeMonad m] {α β : Type}
    (stmts : List (Stmt m α)) (ret : List α → m β) (env : List α) :
    runDo stmts ret env = letStar (stmts.map Stmt.toBinding) ret env := by
  induction stmts generalizing env with
  | nil => rfl
  | cons s rest ih =>
      cases s with
      | bind k =>
          simp only [runDo, List.map_cons, Stmt.toBinding, letStar, patVar, List.singleton_append]
          congr 1
          funext v
          exact ih (v :: env)
      | exec k =>
          simp only [runDo, List.map_cons, Stmt.toBinding, letStar, patWild, List.nil_append]
          congr 1
          funext v
          exact ih env

/-- `progn`: every statement discarded, the last expression answers. -/
def progn {m : Type → Type} [Monad m] {α β : Type}
    (stmts : List (List α → m α)) (last : List α → m β) : m β :=
  runDo (stmts.map Stmt.exec) last []

/-! ## Witnesses in the bag monad of answers -/

def sym (s : String) : Atom := .symbol s

def num (n : Int) : Atom := .grounded (.int n)

/-- The empty expression `()`, the unit answer of an effect in HE. -/
def unit : Atom := .expression []

/-- The pattern `()`: it matches only the empty expression. -/
def patUnit : Pat Atom := fun v => if v = unit then some [] else none

/-- An effect statement that answers `true`, as a printing operation does in
PeTTa, and one that answers `()`, as in HE. -/
def answersTrue : List Atom → List Atom := fun _ => [sym "true"]
def answersUnit : List Atom → List Atom := fun _ => [unit]

def done : List Atom → List Atom := fun _ => [sym "done"]

/-- Written with the pattern `()`, a statement whose answer is `true` drops the
branch; discarded, it does not. -/
theorem unitPattern_drops_branch :
    letStar [(patUnit, answersTrue)] done [] = [] ∧
      runDo [Stmt.exec answersTrue] done [] = [sym "done"] ∧
      letStar [(patUnit, answersUnit)] done [] = [sym "done"] := by
  decide

/-- A discarded statement with two answers runs the rest of the block twice. -/
theorem progn_multiplies :
    progn [fun _ => [num 1, num 2]] (fun _ => [num 5]) = [num 5, num 5] := by
  decide

/-- Committed choice: each statement keeps only its first answer. -/
def runDoCommitted {α β : Type} : List (Stmt List α) → (List α → List β) → List α → List β
  | [], ret, env => ret env
  | .bind k :: rest, ret, env => (k env).take 1 >>= fun v => runDoCommitted rest ret (v :: env)
  | .exec k :: rest, ret, env => (k env).take 1 >>= fun _ => runDoCommitted rest ret env

theorem committed_ne_bag :
    runDoCommitted [Stmt.exec fun _ => [num 1, num 2]] (fun _ => [num 5]) [] = [num 5] ∧
      runDo [Stmt.exec fun _ => [num 1, num 2]] (fun _ => [num 5]) [] = [num 5, num 5] := by
  decide

/-- A statement is deterministic when it has at most one answer in every
environment. -/
def Stmt.Deterministic {α : Type} : Stmt List α → Prop
  | .bind k => ∀ env, (k env).length ≤ 1
  | .exec k => ∀ env, (k env).length ≤ 1

theorem take_one_of_length_le {α : Type} {l : List α} (h : l.length ≤ 1) : l.take 1 = l := by
  match l, h with
  | [], _ => rfl
  | [_], _ => rfl

/-- Committed choice agrees with the bag reading on deterministic statements. -/
theorem committed_eq_bag_of_deterministic {α β : Type} (stmts : List (Stmt List α))
    (h : ∀ s ∈ stmts, s.Deterministic) (ret : List α → List β) (env : List α) :
    runDoCommitted stmts ret env = runDo stmts ret env := by
  induction stmts generalizing env with
  | nil => rfl
  | cons s rest ih =>
      have hrest : ∀ t ∈ rest, t.Deterministic := fun t ht => h t (by simp [ht])
      have hs := h s (by simp)
      cases s with
      | bind k =>
          simp only [runDoCommitted, runDo, take_one_of_length_le (hs env)]
          congr 1
          funext v
          exact ih hrest (v :: env)
      | exec k =>
          simp only [runDoCommitted, runDo, take_one_of_length_le (hs env)]
          congr 1
          funext v
          exact ih hrest env

/-! ## Scope: lexical shadowing against logic-variable binding -/

/-- Named environments of numbers. -/
abbrev Env := List (String × Int)

/-- Lexical `let`: the new binding shadows any binding of the same name. -/
def letLex (x : String) (v : Int) (k : Env → List Int) (env : Env) : List Int :=
  k ((x, v) :: env)

/-- Logic-variable `let`: a name already bound constrains the new value. -/
def letUnify (x : String) (v : Int) (k : Env → List Int) (env : Env) : List Int :=
  match env.lookup x with
  | some w => if w = v then k env else []
  | none => k ((x, v) :: env)

/-- The value of a name, or no answer. -/
def get (x : String) (env : Env) : List Int := (env.lookup x).toList

/-- `(let $x 1 (let $x (+ $x 1) $x))` in each scope rule. -/
def rebindLex : List Int :=
  letLex "x" 1 (fun env => (get "x" env).flatMap fun v => letLex "x" (v + 1) (get "x") env) []

def rebindUnify : List Int :=
  letUnify "x" 1 (fun env => (get "x" env).flatMap fun v => letUnify "x" (v + 1) (get "x") env) []

/-- Rebinding answers `2` under lexical scope and nothing under logic-variable
scope. -/
theorem lexical_ne_unify : rebindLex = [2] ∧ rebindUnify = [] := by
  decide

/-- On a fresh name the two rules agree. -/
theorem lexical_eq_unify_of_fresh (x : String) (v : Int) (k : Env → List Int) (env : Env)
    (fresh : env.lookup x = none) : letUnify x v k env = letLex x v k env := by
  simp [letUnify, letLex, fresh]

end Mettapedia.Languages.MeTTa.EvaluationControl.SequencingForms
