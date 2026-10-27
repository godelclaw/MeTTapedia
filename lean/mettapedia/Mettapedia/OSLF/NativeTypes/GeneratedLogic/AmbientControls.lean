import Mettapedia.OSLF.NativeTypes.GeneratedLogic.AmbientCanonicalForms
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.Search

/-!
# Controls: mobile ambients through the front door, modulo their laws

The tree's mobile ambients (`ambientCalc`), asked through the front door with their canonical forms
(`AmbientForms.forms`): the typed reading of the laws of parallel composition, steps listed at the padded form.
Names are `a`, `b` and `c`.

- `a[in b.0] | b[0]` enters and ends at `b[a[0]]` (`enter_ends`). In the normal form, `a`'s content is the capability
  alone, with no bag around it; the step is listed at the padded form. Without the canonical forms the front door
  leaves the question open (`enter_open_without_forms`).
- It does not end at `a[b[0]]` (`enter_not_reversed`).
- `b[a[out b.0]]` leaves and ends at `a[0] | b[0]` (`exit_ends`).
- `open a.0 | a[0]` dissolves the ambient and ends at `0` (`open_ends`).
- Inside an ambient, beside inactions and nested compositions: `c[a[in b.0 | 0] | (b[0] | 0)]` ends at `c[b[a[0]]]`
  (`nested_enter_ends`).
- Entering needs the named sibling: `a[in b.0] | c[0]` has no step (`wrong_sibling_stuck`), and neither has
  `a[in b.0]` alone (`alone_stuck`).
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.GeneratedLogic.AmbientControls

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine (RelationEnv)
open Mettapedia.Languages.ProcessCalculi.Ambient.Mobile (ambientCalc)

abbrev Ambients := referenceStructure RelationEnv.empty ambientCalc AlgebraTyped.reading

/-- The front door, with the canonical forms at the fuel. The fuel bounds the depth of nested ambients and
compositions at which steps are listed. -/
def answer (formula : Formula 0) (term : Pattern) (rounds : ℕ) : Answer :=
  ask RelationEnv.empty [] ambientCalc 6 formula term none rounds (some (AmbientForms.forms 6))

theorem answer_proved {formula : Formula 0} {term : Pattern} {rounds : ℕ} {evidence : Evidence}
    (answered : answer formula term rounds = .proved evidence) : Ambients.sat Env.closed formula term :=
  ask_proved_in (formsFor_formsReading _) answered

theorem answer_refuted {formula : Formula 0} {term : Pattern} {rounds : ℕ} {evidence : Evidence}
    (answered : answer formula term rounds = .refuted evidence) : ¬ Ambients.sat Env.closed formula term :=
  ask_refuted_in (formsFor_formsReading _) answered

def steps : Formula 0 := .possibly .any .top

/-- Steps, and every step ends at `result`, which has no step. -/
def endsAt (result : Pattern) : Formula 0 :=
  .and (.possibly .any .top) (.necessarily .any (.and (.is result) (.necessarily .any .bot)))

def zero : Pattern := .apply "AZero" []
def par (items : List Pattern) : Pattern := .collection .hashBag items none
def amb (name content : Pattern) : Pattern := .apply "AAmb" [name, content]
def enter (name process : Pattern) : Pattern := .apply "AIn" [name, process]
def leave (name process : Pattern) : Pattern := .apply "AOut" [name, process]
def dissolve (name process : Pattern) : Pattern := .apply "AOpen" [name, process]

def a : Pattern := .apply "NBase" []
def b : Pattern := .apply "NNext" [a]
def c : Pattern := .apply "NNext" [b]

/-! ## Entering -/

theorem enter_ends_answer :
    answer (endsAt (amb b (amb a zero))) (par [amb a (enter b zero), amb b zero]) 3 =
      .proved (.canonicalRegion 3) := by
  decide +kernel

/-- **`a[in b.0] | b[0]` enters and ends at `b[a[0]]`.** -/
theorem enter_ends : Ambients.sat Env.closed (endsAt (amb b (amb a zero))) (par [amb a (enter b zero), amb b zero]) :=
  answer_proved enter_ends_answer

/-- **Without the canonical forms the front door leaves it open.** -/
theorem enter_open_without_forms :
    ask RelationEnv.empty [] ambientCalc 6 (endsAt (amb b (amb a zero))) (par [amb a (enter b zero), amb b zero])
      none 3 = .unknown 3 := by
  decide +kernel

theorem enter_not_reversed_answer :
    answer (endsAt (amb a (amb b zero))) (par [amb a (enter b zero), amb b zero]) 3 =
      .refuted (.canonicalRegion 3) := by
  decide +kernel

/-- **It does not end at `a[b[0]]`.** -/
theorem enter_not_reversed :
    ¬ Ambients.sat Env.closed (endsAt (amb a (amb b zero))) (par [amb a (enter b zero), amb b zero]) :=
  answer_refuted enter_not_reversed_answer

/-! ## Leaving and opening -/

theorem exit_ends_answer :
    answer (endsAt (par [amb a zero, amb b zero])) (amb b (amb a (leave b zero))) 3 = .proved (.canonicalRegion 3) := by
  decide +kernel

/-- **`b[a[out b.0]]` leaves and ends at `a[0] | b[0]`.** -/
theorem exit_ends : Ambients.sat Env.closed (endsAt (par [amb a zero, amb b zero])) (amb b (amb a (leave b zero))) :=
  answer_proved exit_ends_answer

theorem open_ends_answer :
    answer (endsAt zero) (par [dissolve a zero, amb a zero]) 3 = .proved (.canonicalRegion 3) := by
  decide +kernel

/-- **`open a.0 | a[0]` dissolves the ambient and ends at `0`.** -/
theorem open_ends : Ambients.sat Env.closed (endsAt zero) (par [dissolve a zero, amb a zero]) :=
  answer_proved open_ends_answer

/-! ## Under an ambient, modulo the laws -/

theorem nested_enter_ends_answer :
    answer (endsAt (amb c (amb b (amb a zero))))
      (amb c (par [amb a (par [enter b zero, zero]), par [amb b zero, zero]])) 3 = .proved (.canonicalRegion 3) := by
  decide +kernel

/-- **`c[a[in b.0 | 0] | (b[0] | 0)]` ends at `c[b[a[0]]]`.** -/
theorem nested_enter_ends :
    Ambients.sat Env.closed (endsAt (amb c (amb b (amb a zero))))
      (amb c (par [amb a (par [enter b zero, zero]), par [amb b zero, zero]])) :=
  answer_proved nested_enter_ends_answer

/-! ## No step -/

theorem wrong_sibling_stuck_answer :
    answer steps (par [amb a (enter b zero), amb c zero]) 3 = .refuted (.canonicalRegion 3) := by
  decide +kernel

/-- **Entering needs the named sibling**: `a[in b.0] | c[0]` has no step. -/
theorem wrong_sibling_stuck : ¬ Ambients.sat Env.closed steps (par [amb a (enter b zero), amb c zero]) :=
  answer_refuted wrong_sibling_stuck_answer

theorem alone_stuck_answer : answer steps (amb a (enter b zero)) 3 = .refuted (.canonicalRegion 3) := by
  decide +kernel

/-- **`a[in b.0]` alone has no step.** -/
theorem alone_stuck : ¬ Ambients.sat Env.closed steps (amb a (enter b zero)) :=
  answer_refuted alone_stuck_answer

end Mettapedia.OSLF.NativeTypes.GeneratedLogic.AmbientControls
