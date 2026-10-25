import Mettapedia.OSLF.NativeTypes.GeneratedLogic.Search
import Mettapedia.OSLF.Framework.TinyMLInstance
import Mettapedia.OSLF.Framework.LambdaInstance

/-!
# Controls: the tree's λ-calculus and TinyML through the front door

Two authored languages of the tree, both without equations, asked through the front door as they are
written. Both fire their rules at the root, and both substitute under binders.

**The λ-calculus** (`lambdaCalc`, β at the root):
- `(λx. x) (λy. y)` steps, to `λy. y`, which has no step (`identity_applied`).
- `Ω = (λx. x x) (λx. x x)` steps to itself, so every run goes on forever (`omega_diverges`): a closed region of
  one term with a step to itself proves it.
- `(λx. λy. x) Ω` steps once, to `λy. Ω`, and stops: β fires only at the root, so the argument `Ω` is never
  run (`constant_discards`).

**TinyML** (`tinyML`, call by value with Booleans, pairs and thunks):
- a conditional on `true` takes its first branch (`if_true`);
- forcing a thunk steps to its body, not to the body's value, which comes one step later (`force_thunk`);
- the first projection of a pair returns its first component, which has no step (`fst_pair`);
- a conditional on a function is stuck, and is not a value (`if_on_function_stuck`): a type error, seen as a
  behaviour.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.GeneratedLogic.InstanceControls

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine (RelationEnv)

/-! ## Asking -/

section Asking

variable (language : LanguageDef)

/-- The front door proves the formula. -/
def proves (formula : Formula 0) (term : Pattern) (rounds : ℕ) : Bool :=
  match ask RelationEnv.empty [] language 2 formula term none rounds with
  | .proved _ => true
  | _ => false

/-- The front door refutes the formula. -/
def refutes (formula : Formula 0) (term : Pattern) (rounds : ℕ) : Bool :=
  match ask RelationEnv.empty [] language 2 formula term none rounds with
  | .refuted _ => true
  | _ => false

variable {language}

theorem proves_sound {formula : Formula 0} {term : Pattern} {rounds : ℕ}
    (proved : proves language formula term rounds = true) :
    (referenceStructure RelationEnv.empty language).sat Env.closed formula term := by
  unfold proves at proved
  split at proved
  · exact ask_proved ‹_›
  · cases proved

theorem refutes_sound {formula : Formula 0} {term : Pattern} {rounds : ℕ}
    (refuted : refutes language formula term rounds = true) :
    ¬ (referenceStructure RelationEnv.empty language).sat Env.closed formula term := by
  unfold refutes at refuted
  split at refuted
  · exact ask_refuted ‹_›
  · cases refuted

end Asking

def steps : Formula 0 := .possibly .any .top

/-- Steps, and every step ends at `result`, which has no step. -/
def endsAt (result : Pattern) : Formula 0 :=
  .and (.possibly .any .top) (.necessarily .any (.and (.is result) (.necessarily .any .bot)))

/-- Every run goes on forever. -/
def forever : Formula 0 := .nu (.and (.possibly .any .top) (.necessarily .any (.var 0)))

/-! ## The λ-calculus -/

abbrev Lambda := referenceStructure RelationEnv.empty Mettapedia.OSLF.Framework.LambdaInstance.lambdaCalc

def lam (body : Pattern) : Pattern := .apply "Lam" [.lambda none body]
def app (function argument : Pattern) : Pattern := .apply "App" [function, argument]

def identity : Pattern := lam (.bvar 0)
def selfApply : Pattern := lam (app (.bvar 0) (.bvar 0))
def omega : Pattern := app selfApply selfApply
def constant : Pattern := lam (lam (.bvar 1))

/-- **`(λx. x) (λy. y)` steps to `λy. y`, which has no step.** -/
theorem identity_applied : Lambda.sat Env.closed (endsAt identity) (app identity identity) :=
  proves_sound (rounds := 4) (by decide +kernel)

/-- **Every run from `Ω` goes on forever.** -/
theorem omega_diverges : Lambda.sat Env.closed forever omega :=
  proves_sound (rounds := 4) (by decide +kernel)

/-- **`(λx. λy. x) Ω` steps to `λy. Ω` and stops**: the argument is never run. -/
theorem constant_discards : Lambda.sat Env.closed (endsAt (lam omega)) (app constant omega) :=
  proves_sound (rounds := 6) (by decide +kernel)

/-! ## TinyML -/

abbrev TinyML := referenceStructure RelationEnv.empty Mettapedia.OSLF.Framework.TinyMLInstance.tinyML

def inject (value : Pattern) : Pattern := .apply "Inject" [value]
def yes : Pattern := .apply "BoolT" []
def no : Pattern := .apply "BoolF" []

/-- **A conditional on `true` takes its first branch.** -/
theorem if_true : TinyML.sat Env.closed (endsAt (inject no)) (.apply "If" [inject yes, inject no, inject yes]) :=
  proves_sound (rounds := 4) (by decide +kernel)

def thunkBody : Pattern := .apply "If" [inject yes, inject yes, inject no]

/-- **Forcing a thunk steps to its body** and not to the body's value, which comes one step later. -/
theorem force_thunk :
    TinyML.sat Env.closed (.possibly .any (.is thunkBody)) (inject (.apply "Thunk" [thunkBody])) ∧
      ¬ TinyML.sat Env.closed (endsAt (inject yes)) (inject (.apply "Thunk" [thunkBody])) ∧
      TinyML.sat Env.closed (.possibly .any (endsAt (inject yes))) (inject (.apply "Thunk" [thunkBody])) :=
  ⟨proves_sound (rounds := 6) (by decide +kernel), refutes_sound (rounds := 6) (by decide +kernel),
    proves_sound (rounds := 6) (by decide +kernel)⟩

/-- **The first projection of a pair returns its first component.** -/
theorem fst_pair : TinyML.sat Env.closed (endsAt (inject yes)) (.apply "Fst" [inject (.apply "PairV" [yes, no])]) :=
  proves_sound (rounds := 4) (by decide +kernel)

/-- **A conditional on a function is stuck.** -/
theorem if_on_function_stuck :
    ¬ TinyML.sat Env.closed steps
      (.apply "If" [inject (.apply "Lam" [.lambda none (inject (.bvar 0))]), inject yes, inject no]) :=
  refutes_sound (rounds := 8) (by decide +kernel)

end Mettapedia.OSLF.NativeTypes.GeneratedLogic.InstanceControls
