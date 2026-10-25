import Mettapedia.OSLF.NativeTypes.GeneratedLogic.Finite
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.Controls

/-!
# Controls: deciding generated formulas on finite structures

- **A cycle** `0 → 1 → 2 → 0` with goal `2`: the goal is reachable (`μX. goal ∨ ◇X`) and there is an
  infinite run (`νX. ◇X`); not every run ends (`μX. □X` fails).
- **A dead end** `0 → 1`: every run ends (`μX. □X`), and there is no infinite run (`νX. ◇X` fails).
- **A certificate decided by evaluation.** The two-element abstraction of `tiny` from `Controls`, as a
  finite structure. The evaluator decides that its element "cannot fire" is stuck. The homomorphism
  carries the verdict back to every term of `tiny` whose root is neither `Out` nor `Par`. The verdict at
  "may fire" is negative, and the abstraction claims nothing there.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.GeneratedLogic.FiniteControls

open Mettapedia.OSLF.MeTTaIL.Syntax
open Formula NativeStructure
open Mettapedia.OSLF.NativeTypes.GeneratedLogic.Controls (Tiny tiny_step mayFire mayFire_of_step)

/-- A finite structure whose steps are given by a function, every step under every label, and whose
only type is `goal`. -/
def ofSteps {Carrier : Type} [DecidableEq Carrier] (elements : List Carrier) (complete : ∀ element, element ∈ elements)
    (step : Carrier → Carrier → Bool) (goal : Carrier → Bool) : FiniteStructure Carrier where
  elements := elements
  complete := complete
  step source _ target := step source target
  built _ _ _ := false
  split _ _ _ _ := false
  empty _ _ := false
  single _ _ _ := false
  body _ _ := false
  multiBody _ _ _ := false
  bound _ _ := false
  typed element type := type == .base "Goal" && goal element
  named _ _ := false
  same first second := decide (first = second)
  apply inner _ := inner

def goalType : TypeExpr := .base "Goal"

/-- Some run reaches the goal. -/
def reachesGoal : Formula 0 := .mu (.or (.typed goalType) (.possibly .any (.var 0)))

/-- Some run is infinite. -/
def infiniteRun : Formula 0 := .nu (.possibly .any (.var 0))

/-- Every run ends. -/
def runsEnd : Formula 0 := .mu (.necessarily .any (.var 0))

/-! ## A cycle -/

def cycle : FiniteStructure (Fin 3) :=
  ofSteps [0, 1, 2] (by decide) (fun source target => target = source + 1) (· = 2)

theorem cycle_reaches_goal : cycle.native.sat Env.closed reachesGoal 0 :=
  (cycle.check_iff reachesGoal 0).mp (by decide)

theorem cycle_runs_forever : cycle.native.sat Env.closed infiniteRun 0 :=
  (cycle.check_iff infiniteRun 0).mp (by decide)

theorem cycle_runs_do_not_end : ¬ cycle.native.sat Env.closed runsEnd 0 :=
  fun holds => absurd ((cycle.check_iff runsEnd 0).mpr holds) (by decide)

/-! ## A dead end -/

def deadEnd : FiniteStructure (Fin 2) :=
  ofSteps [0, 1] (by decide) (fun source target => source = 0 && target = 1) (fun _ => false)

theorem deadEnd_runs_end : deadEnd.native.sat Env.closed runsEnd 0 :=
  (deadEnd.check_iff runsEnd 0).mp (by decide)

theorem deadEnd_no_infinite_run : ¬ deadEnd.native.sat Env.closed infiniteRun 0 :=
  fun holds => absurd ((deadEnd.check_iff infiniteRun 0).mpr holds) (by decide)

theorem deadEnd_misses_goal : ¬ deadEnd.native.sat Env.closed reachesGoal 0 :=
  fun holds => absurd ((deadEnd.check_iff reachesGoal 0).mpr holds) (by decide)

/-! ## A certificate decided by evaluation -/

/-- The two-element abstraction of `tiny`: whether a rule can fire at the root. Only terms that may
fire step; every shape, type and name is allowed. -/
def fireFinite : FiniteStructure Bool where
  elements := [false, true]
  complete := by decide
  step source _ _ := source
  built _ _ _ := true
  split _ _ _ _ := true
  empty _ _ := true
  single _ _ _ := true
  body _ _ := true
  multiBody _ _ _ := true
  bound _ _ := true
  typed _ _ := true
  named _ _ := true
  same first second := decide (first = second)
  apply inner _ := inner

/-- The abstraction is a homomorphism from `tiny`'s structure. -/
def fireFiniteHom : Hom Tiny fireFinite.native where
  map := mayFire
  step := mayFire_of_step
  built := fun _ => rfl
  split := fun _ => rfl
  empty := fun _ => rfl
  single := fun _ => rfl
  body := fun _ => rfl
  multiBody := fun _ => rfl
  bound := fun _ => rfl
  typed := fun _ => rfl
  named := fun _ => rfl

/-- **The evaluator decides the certificate's verdict**: "cannot fire" is stuck. -/
theorem cannot_fire_stuck : fireFinite.check (.necessarily .any .bot) false = true := by decide

/-- "May fire" is not stuck in the abstraction, so the certificate claims nothing there. -/
theorem may_fire_not_stuck : fireFinite.check (.necessarily .any .bot) true = false := by decide

/-- **The verdict carried back**: every term of `tiny` whose root is neither `Out` nor `Par` is stuck. -/
theorem stuck_of_not_mayFire {term : Pattern} (cannot : mayFire term = false) :
    Tiny.sat Env.closed (.necessarily .any .bot) term :=
  fireFiniteHom.sat_of_hom_universal (.necessarily .any .bot) rfl (sourceEnv := Env.closed)
    (targetEnv := Env.closed) (fun index => index.elim0) term
    (by rw [show fireFiniteHom.map term = false from cannot]; exact (fireFinite.check_iff _ _).mp cannot_fire_stuck)

end Mettapedia.OSLF.NativeTypes.GeneratedLogic.FiniteControls
