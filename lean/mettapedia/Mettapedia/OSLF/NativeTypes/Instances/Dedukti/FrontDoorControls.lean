import Mettapedia.OSLF.NativeTypes.Instances.Dedukti.FrontDoor
import Mettapedia.GSLT.Dedukti.PeanoFiber

/-!
# Controls: Peano arithmetic in the λΠ-calculus modulo, at the front door

The theory of `plus` on unary numerals (`peanoTheory`: `plus x 0 ⟶ x`, `plus x (succ y) ⟶ succ (plus x y)`) is
presented by its two rules, which are linear with headed algebraic left sides. Asked at the encodings of closed terms
through the front door, with the kernel evaluating the answers:

- the numeral `2` has no step (a closed region of one term), and the evaluator finds no step either;
- `2 + 3` has a step (the region it reaches), and the evaluator finds one;
- `2 + 3` reaches `5`, and `5` has no step (a closed region of the whole computation).
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Instances.Dedukti.Controls

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine (RelationEnv)
open Mettapedia.OSLF.NativeTypes.GeneratedLogic
open Mettapedia.GSLT.Dedukti
open Mettapedia.GSLT.Dedukti.Language (Presents encode dkLanguage)
open Mettapedia.GSLT.Dedukti.PeanoFiber (peanoTheory peanoRules numeral plus)
open Mettapedia.GSLT.LanguageDef.LF (WellScoped)

def names : List String := ["zero", "succ", "plus"]

theorem presents : Presents peanoTheory peanoRules where
  undefined _ := rfl
  rule_iff _ := Iff.rfl
  leftAlgebraic := by decide
  rightDetermined := by decide

theorem linear : ∀ rule ∈ peanoRules, (patternVars rule.lhs).Nodup := by decide

theorem numeral_closed : ∀ n, WellScoped 0 (numeral n)
  | 0 => .con
  | n + 1 => .app .con (numeral_closed n)

theorem sum_closed : WellScoped 0 (plus (numeral 2) (numeral 3)) :=
  .app (.app .con (numeral_closed 2)) (numeral_closed 3)

/-- The front door's answer, read as written, with premise fuel enough for the congruences to reach the depth of
these terms. -/
def answer (formula : Formula 0) (term : Pattern) (rounds : ℕ) : Answer :=
  ask RelationEnv.empty [] (dkLanguage names peanoRules) 8 formula term none rounds

def stuck : Formula 0 := .necessarily .any .bot
def steps : Formula 0 := .possibly .any .top

/-- Reaches a term with no step that is this term. -/
def endsAt (result : Pattern) : Formula 0 :=
  .mu (.or (.and (.is result) (.necessarily .any .bot)) (.possibly .any (.var 0)))

theorem two_stuck_answer : answer stuck (encode (numeral 2)) 8 = .proved (.closedRegion 8) := by decide +kernel

/-- **`2` is normal**, by a closed region at the front door. -/
theorem two_normal : Mettapedia.Logic.Relation.IsNormal (Step peanoTheory) (numeral 2) :=
  (sat_normal_iff (names := names) presents (numeral_closed 2)).mp (ask_proved two_stuck_answer)

/-- **The evaluator agrees**: it finds no step from `2`. -/
theorem two_evaluator : stepOnce [] peanoRules (numeral 2) = none :=
  ask_normal_proved presents linear (numeral_closed 2) two_stuck_answer

theorem sum_steps_answer : answer steps (encode (plus (numeral 2) (numeral 3))) 8 = .proved (.exploration 8) := by
  decide +kernel

/-- **`2 + 3` steps.** -/
theorem sum_steps : ∃ next, Step peanoTheory (plus (numeral 2) (numeral 3)) next :=
  (sat_steps_iff (names := names) presents sum_closed).mp (ask_proved sum_steps_answer)

theorem sum_not_stuck_answer : answer stuck (encode (plus (numeral 2) (numeral 3))) 8 = .refuted (.exploration 8) := by
  decide +kernel

/-- **The evaluator agrees**: it finds a step from `2 + 3`. -/
theorem sum_evaluator : stepOnce [] peanoRules (plus (numeral 2) (numeral 3)) ≠ none :=
  ask_normal_refuted presents linear sum_closed sum_not_stuck_answer

theorem sum_ends_answer :
    answer (endsAt (encode (numeral 5))) (encode (plus (numeral 2) (numeral 3))) 8 = .proved (.closedRegion 8) := by
  decide +kernel

/-- **`2 + 3` reaches `5`, which has no step**, by a closed region of the whole computation. -/
theorem sum_ends :
    (Dk names peanoRules).sat Env.closed (endsAt (encode (numeral 5))) (encode (plus (numeral 2) (numeral 3))) :=
  ask_proved sum_ends_answer

end Mettapedia.OSLF.NativeTypes.Instances.Dedukti.Controls
