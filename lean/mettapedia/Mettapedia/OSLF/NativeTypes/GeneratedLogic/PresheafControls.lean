import Mettapedia.OSLF.NativeTypes.GeneratedLogic.JudgmentControls

/-!
# Controls: where the presheaf reading agrees with the classical one, and where it parts

In the language `coins` (sides `H` and `T`, `Toss` stepping to either side), at the context `x : Side`:

- **agreement on negative formulas**: `x : Side ⊢ x : □⊥` is judged at the front door and forced
  (`stuck_forced`);
- **agreement at the closed stage**: `Toss` forces `◇H` at the terminal stage, and `H` does not (`toss_forced`,
  `heads_not_forced`), as the front door's classical verdicts say, and as higher-order logic says (`toss_denotes`);
- **disjunction parts**: `x : Side ⊢ x : H ∨ T` holds at every valuation, and neither side is forced at the stage
  (`side_not_forced`);
- **excluded middle parts**: `x : Side ⊢ x : H ∨ ¬H` holds, and is not forced (`middle_not_forced`);
- **the universal former parts even at a closed term**: `Toss` satisfies `□(H ∨ T)` classically, and does not force it
  at the terminal stage, since the generic side `x` is a successor of `Toss` at the stage `x : Side`
  (`toss_not_forced`).
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.GeneratedLogic.PresheafControls

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine (RelationEnv)
open JudgmentControls

abbrev site : Site Pattern := contextSite Coins

theorem coins_free : coins.isEquationFree = true := by decide

/-- The fibre of sides. -/
def sideFibre : Fibre Coins side := constantFibre RelationEnv.empty coins (formsReading none) "Side" (by decide) coins_free

theorem side_values {value : Pattern} (closedValue : ClosedValue value) (typedValue : Coins.typed value side) :
    value = heads ∨ value = tails := by
  have member := sideFibre.complete value closedValue typedValue
  have values : sideFibre.values = [heads, tails] := by decide
  rw [values] at member
  simpa using member

theorem tails_value : ClosedValue tails ∧ Coins.typed tails side := sideFibre.sound tails (by decide)

/-- Two terms the language tells apart. -/
theorem not_named {first second : Pattern} (different : first ≠ second) : ¬ Coins.named first second :=
  fun named => different ((objectEquivalent_iff_eq_of_isEquationFree coins_free).mp named.2)

theorem named_self (term : Pattern) (object : IsObject term) : Coins.named term term := ⟨object, Relation.EqvGen.refl _⟩

/-! ## The stage `x : Side` -/

def sideContext : Context := [("x", side)]

theorem pick_valuation {value : Pattern} (closedValue : ClosedValue value) (typedValue : Coins.typed value side) :
    Valuation Coins sideContext (pick value) := by
  refine ⟨fun entry member => ?_, fun name outside => ?_⟩
  · rcases List.mem_singleton.mp member with rfl
    exact ⟨closedValue, typedValue⟩
  · have different : name ≠ "x" := fun same => outside (by simp [sideContext, Context.names, same])
    simp only [pick, different, if_false]

def sideStage : site.Stage := ⟨sideContext, pick heads, pick_valuation heads_value.1 heads_value.2⟩

def headsPoint : site.Point sideStage := ⟨pick heads, pick_valuation heads_value.1 heads_value.2⟩
def tailsPoint : site.Point sideStage := ⟨pick tails, pick_valuation tails_value.1 tails_value.2⟩

theorem instancesAt_x (point : site.Point sideStage) : instancesAt Coins sideStage x point = point.1 "x" := rfl

theorem pick_x (value : Pattern) : pick value "x" = value := by simp [pick]

/-- The value of `x` at a point is a side. -/
theorem point_side (point : site.Point sideStage) : point.1 "x" = heads ∨ point.1 "x" = tails :=
  side_values (point.2.1 ("x", side) (List.mem_singleton_self _)).1 (point.2.1 ("x", side) (List.mem_singleton_self _)).2

/-! ## Agreement -/

/-- No step. -/
def stuck : Formula 0 := .necessarily .any .bot

theorem stuck_answer : judge sideContext stuck x = .proved (.instances 2) := by decide +kernel

/-- **On a negative formula the readings agree**: `x : Side ⊢ x : □⊥` is forced at the stage. -/
theorem stuck_forced : ForcesOpen Coins sideStage stuck x :=
  (forcesOpen_iff_of_negative (by decide) sideStage x).mpr (askOpen_proved stuck_answer)

theorem toss_heads_answer : ask RelationEnv.empty [] coins 2 (stepsTo heads) toss none 4 = .proved (.exploration 4) := by
  decide +kernel

theorem heads_heads_answer : ask RelationEnv.empty [] coins 2 (stepsTo heads) heads none 4 = .refuted (.closedRegion 4) := by
  decide +kernel

/-- **At the closed stage the readings agree on a settled formula**: `Toss` forces `◇H`. -/
theorem toss_forced : Coins.forces site (fun index => index.elim0) site.terminal (stepsTo heads) (fun _ => toss) := by
  have env : (fun index : Fin 0 => index.elim0 : Fin 0 → site.Sets) = fun index => site.lift (Env.closed index) :=
    funext fun index => index.elim0
  rw [env, Coins.forces_terminal_iff site (stepsTo heads) (by decide)]
  exact ask_proved toss_heads_answer

/-- **And `H` does not force it.** -/
theorem heads_not_forced : ¬ Coins.forces site (fun index => index.elim0) site.terminal (stepsTo heads) (fun _ => heads) := by
  have env : (fun index : Fin 0 => index.elim0 : Fin 0 → site.Sets) = fun index => site.lift (Env.closed index) :=
    funext fun index => index.elim0
  rw [env, Coins.forces_terminal_iff site (stepsTo heads) (by decide)]
  exact ask_refuted heads_heads_answer

/-- **Higher-order logic says the same**: the translation of `◇H` holds at `Toss` in the standard model. -/
theorem toss_denotes :
    ((HigherOrder.standardModel Coins).denote (HigherOrder.translate (stepsTo heads))
      (Mettapedia.OSLF.Framework.NativeBasis.nowhere (HigherOrder.presentation Coins)) (ULift.up toss)).down :=
  (Coins.forces_terminal_iff_denote site (by decide) toss).mp toss_forced

/-! ## Disagreement -/

/-- **Disjunction parts**: `x : Side ⊢ x : H ∨ T` holds at every valuation, and neither side is forced at the stage. -/
theorem side_not_forced : ¬ ForcesOpen Coins sideStage isSide x := by
  rintro (forcedHeads | forcedTails)
  · have named := forcedHeads tailsPoint
    rw [instancesAt_x] at named
    exact not_named (by decide) named
  · have named := forcedTails headsPoint
    rw [instancesAt_x] at named
    exact not_named (by decide) named

/-- `H ∨ ¬H`. -/
def middle : Formula 0 := .or (.is heads) (.isNot heads)

theorem middle_answer : judge sideContext middle x = .proved (.instances 2) := by decide +kernel

theorem middle_judged : OpenHolds Coins sideContext middle x := askOpen_proved middle_answer

/-- **Excluded middle parts**: `x : Side ⊢ x : H ∨ ¬H` holds, and is not forced: `x` is not `H` at every point, and is
`H` at some later stage. -/
theorem middle_not_forced : ¬ ForcesOpen Coins sideStage middle x := by
  rintro (forcedHeads | refutedHeads)
  · have named := forcedHeads tailsPoint
    rw [instancesAt_x] at named
    exact not_named (by decide) named
  · exact refutedHeads site.terminal (fun _ => headsPoint) (site.global sideStage headsPoint)
      fun _ => named_self heads rfl

/-- `□(H ∨ T)`. -/
def alwaysSide : Formula 0 := .necessarily .any isSide

theorem toss_always_answer : ask RelationEnv.empty [] coins 2 alwaysSide toss none 4 = .proved (.closedRegion 4) := by
  decide +kernel

/-- `Toss` satisfies `□(H ∨ T)` classically. -/
theorem toss_always : Coins.sat Env.closed alwaysSide toss := ask_proved toss_always_answer

theorem toss_steps_to {value : Pattern} (answered : ask RelationEnv.empty [] coins 2 (stepsTo value) toss none 4 =
    .proved (.exploration 4)) : Coins.step toss .any value := by
  obtain ⟨next, step, named⟩ := ask_proved answered
  rwa [← (objectEquivalent_iff_eq_of_isEquationFree coins_free).mp named.2]

theorem toss_tails_answer : ask RelationEnv.empty [] coins 2 (stepsTo tails) toss none 4 = .proved (.exploration 4) := by
  decide +kernel

/-- The point of the terminal stage. -/
def terminalPoint : site.Point site.terminal := ⟨Pattern.fvar, valuation_nil Coins⟩

theorem to_terminal : (fun _ => terminalPoint) ∈ site.Arrow sideStage site.terminal := by
  refine ⟨Pattern.fvar, ?_, ?_⟩
  · intro entry member
    exact absurd member List.not_mem_nil
  · intro point
    funext name
    simp [terminalPoint, restrictTo, Context.names, site, contextSite]

/-- **The universal former parts even at a closed term**: `Toss` does not force `□(H ∨ T)` at the terminal stage. The
generic side `x` is a successor of `Toss` at the stage `x : Side`, and it forces neither `H` nor `T` there. -/
theorem toss_not_forced : ¬ Coins.forces site (fun index => index.elim0) site.terminal alwaysSide (fun _ => toss) := by
  intro forced
  refine side_not_forced (forced sideStage _ to_terminal (instancesAt Coins sideStage x)
    (instancesAt_mem Coins (by decide)) fun point => ?_)
  rw [instancesAt_x]
  rcases point_side point with same | same <;> rw [same]
  · exact toss_steps_to toss_heads_answer
  · exact toss_steps_to toss_tails_answer

end Mettapedia.OSLF.NativeTypes.GeneratedLogic.PresheafControls
