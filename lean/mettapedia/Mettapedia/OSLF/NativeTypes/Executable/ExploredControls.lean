import Mettapedia.OSLF.NativeTypes.Executable.ExploredCompiled
import Mettapedia.OSLF.MeTTaIL.Complete.Controls

/-!
# Controls: verdicts on the explorer of compiled languages

A traffic light cycles red, green, yellow, and may break at yellow. Each language is compiled to a
plan and explored from red. The verdicts are decided on the settled exploration and mean the
property of the plan's steps (`verdict_proved`, `verdict_refuted`).

- With the fault: the light may deadlock, may break, has a path that is green infinitely often,
  does not break on every path, and a broken light never moves.
- Without the fault: the light never deadlocks and cannot break.
- No verdict: a past modality, a non-positive fixed point, an exploration given too little work,
  and too small an allowance for the checker.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Executable.Explored.Controls

open Mettapedia.OSLF.MeTTaIL.Syntax Mettapedia.OSLF.MeTTaIL.GeneralExecutionAdmission
open Mettapedia.OSLF.NativeTypes.Semantics.ModalFormula
open Mettapedia.Logic.ModalMuCalculus
open Compiled

private def light : TypeExpr := .base "Light"

def constant (label : String) : GrammarRule where
  label := label
  category := "Light"
  params := []
  syntaxPattern := [.terminal label]

def change (name source target : String) : RewriteRule where
  name := name
  typeContext := []
  premises := []
  left := .apply source []
  right := .apply target []

def cycle : List RewriteRule :=
  [change "Go" "Red" "Green", change "Slow" "Green" "Yellow", change "Stop" "Yellow" "Red"]

def language (rewrites : List RewriteRule) : LanguageDef where
  name := "TrafficLight"
  types := ["Light"]
  terms := [constant "Red", constant "Green", constant "Yellow", constant "Broken"]
  equations := []
  rewrites := rewrites

/-- The light that may break at yellow. -/
def faulty : Plan :=
  Mettapedia.OSLF.MeTTaIL.Complete.Controls.rootPlan (language (cycle ++ [change "Fail" "Yellow" "Broken"]))

/-- The light without the fault. -/
def sound : Plan := Mettapedia.OSLF.MeTTaIL.Complete.Controls.rootPlan (language cycle)

def red : Pattern := .apply "Red" []

theorem faulty_equation_free : faulty.equations = [] := by
  unfold faulty Mettapedia.OSLF.MeTTaIL.Complete.Controls.rootPlan
  rw [Mettapedia.OSLF.MeTTaIL.StructuralDescent.Plan.compile,
    Mettapedia.OSLF.MeTTaIL.StructuralDescent.Plan.equations_preserved]
  rfl
theorem sound_equation_free : sound.equations = [] := by
  unfold sound Mettapedia.OSLF.MeTTaIL.Complete.Controls.rootPlan
  rw [Mettapedia.OSLF.MeTTaIL.StructuralDescent.Plan.compile,
    Mettapedia.OSLF.MeTTaIL.StructuralDescent.Plan.equations_preserved]
  rfl

/-- Two atoms: broken, green. -/
def atomsOf (plan : Plan) (empty : plan.equations = []) : Atoms (theory plan [] light).equations 2 :=
  equationFreeAtoms (plan := plan) (bound := []) (expected := light) empty
    (fun (index : Fin 2) state => match index with
      | 0 => state == .apply "Broken" []
      | _ => state == .apply "Green" [])

/-! ## Formulas over the atoms broken (0) and green (1) -/

/-- Every reachable state has a successor. -/
def neverDeadlocks : Formula Traversal 2 := .nu (.conj (.diamond .future .tt) (.box .future (.var 0)))

/-- Some path reaches a broken light. -/
def mayBreak : Formula Traversal 2 := .mu (.disj (.var 1) (.diamond .future (.var 0)))

/-- Some path is green infinitely often. -/
def greenInfinitelyOften : Formula Traversal 2 :=
  .nu (.mu (.disj (.conj (.var 3) (.diamond .future (.var 1))) (.diamond .future (.var 0))))

/-- Every path reaches a broken light. -/
def mustBreak : Formula Traversal 2 :=
  .mu (.disj (.var 1) (.conj (.diamond .future .tt) (.box .future (.var 0))))

/-- A broken light never moves, wherever it is reached. -/
def brokenIsStill : Formula Traversal 2 :=
  .nu (.conj (.disj (.neg (.var 1)) (.box .future .ff)) (.box .future (.var 0)))

/-- Has a predecessor: a past modality. -/
def hasPredecessor : Formula Traversal 2 := .diamond .past .tt

/-- Not positive: a least fixed point of its own negation. -/
def paradox : Formula Traversal 2 := .mu (.neg (.var 0))

def ask (plan : Plan) (empty : plan.equations = []) (formula : Formula Traversal 2)
    (work : Nat := 200) (budget : Nat := 100000) : Verdict :=
  verdict plan [] light id red work formula (atomsOf plan empty) budget

/-! ## The faulty light -/

#guard ask faulty faulty_equation_free neverDeadlocks == .refuted
#guard ask faulty faulty_equation_free mayBreak == .proved
#guard ask faulty faulty_equation_free greenInfinitelyOften == .proved
#guard ask faulty faulty_equation_free mustBreak == .refuted
#guard ask faulty faulty_equation_free brokenIsStill == .proved

/-! ## The sound light -/

#guard ask sound sound_equation_free neverDeadlocks == .proved
#guard ask sound sound_equation_free mayBreak == .refuted
#guard ask sound sound_equation_free greenInfinitelyOften == .proved
#guard ask sound sound_equation_free mustBreak == .refuted

/-! ## No verdict -/

#guard ask faulty faulty_equation_free hasPredecessor == .unknown .pastModality
#guard ask faulty faulty_equation_free paradox == .unknown .notPositive
#guard ask faulty faulty_equation_free neverDeadlocks (work := 0) == .unknown .unsettled
#guard ask faulty faulty_equation_free neverDeadlocks (budget := 0) == .unknown .allowance

/-! ## What the verdicts mean -/

/-- The obligations for an equation-free plan with no abstraction. -/
theorem faulty_checked : Mettapedia.OSLF.MeTTaIL.Complete.Predecessors.equationsChecked faulty = true := by
  rw [Mettapedia.OSLF.MeTTaIL.Complete.Predecessors.equationsChecked, faulty_equation_free]
  rfl

/-- A refuted `neverDeadlocks` means a reachable deadlock of the plan's steps. -/
theorem faulty_deadlocks (read : ask faulty faulty_equation_free neverDeadlocks = .refuted) :
    ¬ satisfies (transitionSystem (Mettapedia.OSLF.Framework.GSLTTypeSynthesis.gsltSpan (theory faulty [] light)))
      (atomsOf faulty faulty_equation_free).meaning neverDeadlocks red :=
  verdict_refuted faulty_checked (Abstraction.plain faulty [] light) trivial (by unfold ask at read; exact read)

end Mettapedia.OSLF.NativeTypes.Executable.Explored.Controls
