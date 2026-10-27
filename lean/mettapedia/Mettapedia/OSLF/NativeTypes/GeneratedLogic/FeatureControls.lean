import Mettapedia.OSLF.NativeTypes.GeneratedLogic.Search

/-!
# Controls: premises and collections at the front door

Small languages with no equations, decided at the front door by exploration and closed regions, for features no other
control exercises:

- **Universally quantified premises** (`checks`): a vector of items steps to `Done` when every item is `ok`. At `[A, A]`
  and at `[]` it does (`all_ok_fires`, `empty_fires`); at `[A, B]` it does not (`one_bad_stuck`).
- **Vectors** (`swaps`): `[x, y] ⇒ [y, x]` turns `[A, B]` into `[B, A]` and back (`swap_returns`); a vector of three
  items does not match (`three_stuck`).
- **Freshness premises on closed terms** (`fresh`): a name that no metavariable binds is fresh in every closed term, so
  `Lit(X) ⇒ Done if z # X` fires (`literal_fresh_fires`). A metavariable bound to a closed term names no variable, so
  `Meta(X, Y) ⇒ Done if X # Y` never fires (`bound_fresh_stuck`).
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.GeneratedLogic.FeatureControls

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine (RelationEnv)

def item (label : String) : GrammarRule := { label := label, category := "Item", params := [], syntaxPattern := [] }
def constant (label : String) : Pattern := .apply label []
def vector (items : List Pattern) : Pattern := .collection .vec items none

def a : Pattern := constant "A"
def b : Pattern := constant "B"
def done : Pattern := constant "Done"

def doneRule : GrammarRule := { label := "Done", category := "Batch", params := [], syntaxPattern := [] }
def batchRule : GrammarRule :=
  { label := "Items", category := "Batch", params := [.simple "items" (.collection .vec (.base "Item"))],
    syntaxPattern := [] }

def steps : Formula 0 := .possibly .any .top
def reaches (target : Pattern) : Formula 0 := .possibly .any (.is target)

/-! ## Universally quantified premises -/

/-- `[...items] ⇒ Done if every x in items is ok`. -/
def allOkRule : RewriteRule :=
  { name := "AllOk", typeContext := [("items", .collection .vec (.base "Item"))],
    premises := [.forAll "items" "x" (.relationQuery "ok" [.fvar "x"])],
    left := .collection .vec [] (some "items"), right := done, bindings := none }

def checks : LanguageDef :=
  { name := "Checks", types := ["Item", "Batch"], terms := [item "A", item "B", doneRule, batchRule], equations := [],
    rewrites := [allOkRule] }

/-- `A` is ok, and nothing else is. -/
def okEnv : RelationEnv := ⟨fun relation arguments => if relation = "ok" ∧ arguments = [a] then [[a]] else []⟩

theorem all_ok_fires_answer : ask okEnv [] checks 2 (reaches done) (vector [a, a]) none 3 = .proved (.exploration 3) := by
  decide +kernel

/-- **Every item of `[A, A]` is ok, so it steps to `Done`.** -/
theorem all_ok_fires : (referenceStructure okEnv checks).sat Env.closed (reaches done) (vector [a, a]) :=
  ask_proved all_ok_fires_answer

theorem empty_fires_answer : ask okEnv [] checks 2 (reaches done) (vector []) none 3 = .proved (.exploration 3) := by
  decide +kernel

/-- **The empty vector steps to `Done`**: the premise holds of no item vacuously. -/
theorem empty_fires : (referenceStructure okEnv checks).sat Env.closed (reaches done) (vector []) :=
  ask_proved empty_fires_answer

theorem one_bad_stuck_answer : ask okEnv [] checks 2 steps (vector [a, b]) none 3 = .refuted (.closedRegion 3) := by
  decide +kernel

/-- **`B` is not ok, so `[A, B]` has no step.** -/
theorem one_bad_stuck : ¬ (referenceStructure okEnv checks).sat Env.closed steps (vector [a, b]) :=
  ask_refuted one_bad_stuck_answer

/-! ## Vectors -/

/-- `[x, y] ⇒ [y, x]`. -/
def swapRule : RewriteRule :=
  { name := "Swap", typeContext := [("x", .base "Item"), ("y", .base "Item")], premises := [],
    left := .collection .vec [.fvar "x", .fvar "y"] none, right := .collection .vec [.fvar "y", .fvar "x"] none,
    bindings := none }

def swaps : LanguageDef :=
  { name := "Swaps", types := ["Item", "Batch"], terms := [item "A", item "B", batchRule], equations := [],
    rewrites := [swapRule] }

/-- Steps to the target, from where a step returns. -/
def returns (target : Pattern) (start : Pattern) : Formula 0 := .possibly .any (.and (.is target) (reaches start))

theorem swap_returns_answer :
    ask RelationEnv.empty [] swaps 2 (returns (vector [b, a]) (vector [a, b])) (vector [a, b]) none 3 =
      .proved (.exploration 3) := by
  decide +kernel

/-- **`[A, B]` swaps to `[B, A]`, which swaps back.** -/
theorem swap_returns :
    (referenceStructure RelationEnv.empty swaps).sat Env.closed (returns (vector [b, a]) (vector [a, b])) (vector [a, b]) :=
  ask_proved swap_returns_answer

theorem three_stuck_answer : ask RelationEnv.empty [] swaps 2 steps (vector [a, b, a]) none 3 = .refuted (.closedRegion 3) := by
  decide +kernel

/-- **A vector of three items does not match `[x, y]`.** -/
theorem three_stuck : ¬ (referenceStructure RelationEnv.empty swaps).sat Env.closed steps (vector [a, b, a]) :=
  ask_refuted three_stuck_answer

/-! ## Freshness premises on closed terms -/

def tag (label : String) (arity : ℕ) : GrammarRule :=
  { label := label, category := "Batch", params := (List.range arity).map fun i => .simple s!"p{i}" (.base "Item"),
    syntaxPattern := [] }

/-- `Lit(X) ⇒ Done if z # X`: `z` is a name no metavariable binds. -/
def literalRule : RewriteRule :=
  { name := "Literal", typeContext := [("X", .base "Item")], premises := [.freshness ⟨"z", .fvar "X"⟩],
    left := .apply "Lit" [.fvar "X"], right := done, bindings := none }

/-- `Meta(X, Y) ⇒ Done if X # Y`: `X` is a metavariable. -/
def boundRule : RewriteRule :=
  { name := "Bound", typeContext := [("X", .base "Item"), ("Y", .base "Item")], premises := [.freshness ⟨"X", .fvar "Y"⟩],
    left := .apply "Meta" [.fvar "X", .fvar "Y"], right := done, bindings := none }

def fresh : LanguageDef :=
  { name := "Fresh", types := ["Item", "Batch"], terms := [item "A", item "B", doneRule, tag "Lit" 1, tag "Meta" 2],
    equations := [], rewrites := [literalRule, boundRule] }

theorem literal_fresh_fires_answer :
    ask RelationEnv.empty [] fresh 2 (reaches done) (.apply "Lit" [a]) none 3 = .proved (.exploration 3) := by
  decide +kernel

/-- **A name no metavariable binds is fresh in a closed term**, so `Lit(A)` steps to `Done`. -/
theorem literal_fresh_fires : (referenceStructure RelationEnv.empty fresh).sat Env.closed (reaches done) (.apply "Lit" [a]) :=
  ask_proved literal_fresh_fires_answer

theorem bound_fresh_stuck_answer :
    ask RelationEnv.empty [] fresh 2 steps (.apply "Meta" [a, b]) none 3 = .refuted (.closedRegion 3) := by
  decide +kernel

/-- **A metavariable bound to a closed term names no variable**, so `Meta(A, B)` has no step. -/
theorem bound_fresh_stuck : ¬ (referenceStructure RelationEnv.empty fresh).sat Env.closed steps (.apply "Meta" [a, b]) :=
  ask_refuted bound_fresh_stuck_answer

end Mettapedia.OSLF.NativeTypes.GeneratedLogic.FeatureControls
