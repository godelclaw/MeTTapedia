import Mettapedia.OSLF.NativeTypes.GeneratedLogic.GroundSetParts

/-!
# Controls: splits of ground sets

The pair pool of `GroundSetReadings` reads its sets modulo the set laws: `{A, B, ...rest} ⇒ {C, ...rest}` consumes or
keeps each of `A` and `B`. A set splits into any two sets whose union it is, so its parts may share members. Closed
parts regions decide these splits, with the parts of each covering.

- `{A, B}` splits into `{A, B}` and `{A}` (`ab_overlapping_split`): the parts share `A`. A bag cannot split so.
- Both parts of some split of `{A, B}` fire (`ab_both_parts_fire`): the whole set, twice.
- Not every split of `{A, B}` has a first part that fires (`ab_not_every_first_fires`), but every split has a first part
  that fires or a second part that is not empty (`ab_fires_or_second_nonempty`).
- `{A, B}` steps to a set that splits into `{A}` and `{C}` (`ab_steps_to_split`).
- The front door with the parts decider proves the overlapping split (`ask_ab_overlapping_split`) and refutes the
  every-split (`ask_ab_not_every_first_fires`).
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.GeneratedLogic.SetReadings

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine (RelationEnv)

theorem pair_parts_true {formula : Formula 0} {term : Pattern} (rounds : ℕ) (fragment : formula.behaviouralParts = true)
    (decided : decideParts RelationEnv.empty pairPool 2 BagForms.sortBags (atomSet pairPool "Atom") setPresentations
      (groundParts pairPool_ground) formula term rounds = some true) :
    (referenceStructure RelationEnv.empty pairPool).sat Env.closed formula term :=
  (decideParts_sound (canonical pairPool_ground) (coherent pairPool_ground 2) fragment decided).mp rfl

theorem pair_parts_false {formula : Formula 0} {term : Pattern} (rounds : ℕ) (fragment : formula.behaviouralParts = true)
    (decided : decideParts RelationEnv.empty pairPool 2 BagForms.sortBags (atomSet pairPool "Atom") setPresentations
      (groundParts pairPool_ground) formula term rounds = some false) :
    ¬ (referenceStructure RelationEnv.empty pairPool).sat Env.closed formula term := fun holds =>
  Bool.false_ne_true ((decideParts_sound (canonical pairPool_ground) (coherent pairPool_ground 2) fragment
    decided).mpr holds)

/-- `{A}`. -/
def justA : Pattern := set [token "A"]

/-- `{C}`. -/
def justC : Pattern := set [token "C"]

/-- Fires. -/
def fires : Formula 0 := .possibly .any .top

/-- Splits into `{A, B}` and `{A}`. -/
def overlappingSplit : Formula 0 := .split .hashSet (.is bothAB) (.is justA)

/-- Some split has two parts that fire. -/
def bothPartsFire : Formula 0 := .split .hashSet fires fires

/-- Every split has a first part that fires. -/
def everyFirstFires : Formula 0 := .everySplit .hashSet fires .bot

/-- Every split has a first part that fires or a second part that is not empty. -/
def firesOrSecondNonEmpty : Formula 0 := .everySplit .hashSet fires (.nonEmpty .hashSet)

/-- Steps to a set that splits into `{A}` and `{C}`. -/
def stepsToSplitAC : Formula 0 := .possibly .any (.split .hashSet (.is justA) (.is justC))

/-- **`{A, B}` splits into `{A, B}` and `{A}`.** -/
theorem ab_overlapping_split : (referenceStructure RelationEnv.empty pairPool).sat Env.closed overlappingSplit bothAB :=
  pair_parts_true 2 rfl (by decide +kernel)

/-- **Both parts of some split of `{A, B}` fire.** -/
theorem ab_both_parts_fire : (referenceStructure RelationEnv.empty pairPool).sat Env.closed bothPartsFire bothAB :=
  pair_parts_true 2 rfl (by decide +kernel)

/-- **Not every split of `{A, B}` has a first part that fires.** -/
theorem ab_not_every_first_fires :
    ¬ (referenceStructure RelationEnv.empty pairPool).sat Env.closed everyFirstFires bothAB :=
  pair_parts_false 2 rfl (by decide +kernel)

/-- **Every split of `{A, B}` has a first part that fires or a second part that is not empty.** -/
theorem ab_fires_or_second_nonempty :
    (referenceStructure RelationEnv.empty pairPool).sat Env.closed firesOrSecondNonEmpty bothAB :=
  pair_parts_true 2 rfl (by decide +kernel)

/-- **`{A, B}` steps to a set that splits into `{A}` and `{C}`.** -/
theorem ab_steps_to_split : (referenceStructure RelationEnv.empty pairPool).sat Env.closed stepsToSplitAC bothAB :=
  pair_parts_true 2 rfl (by decide +kernel)

/-! ### At the front door -/

theorem ask_ab_overlapping_split_answer :
    askWith RelationEnv.empty pairSignature pairPool 2 overlappingSplit bothAB (groundPartsDecider pairPool_ground 2 2)
      none 2 (some pairForms) = .proved .decided := by
  decide +kernel

/-- **The front door with the parts decider proves the overlapping split.** -/
theorem ask_ab_overlapping_split :
    (referenceStructure RelationEnv.empty pairPool).sat Env.closed overlappingSplit bothAB :=
  askWith_proved (by rfl) ask_ab_overlapping_split_answer

theorem ask_ab_not_every_first_fires_answer :
    askWith RelationEnv.empty pairSignature pairPool 2 everyFirstFires bothAB (groundPartsDecider pairPool_ground 2 2)
      none 2 (some pairForms) = .refuted .decided := by
  decide +kernel

/-- **And refutes the every-split.** -/
theorem ask_ab_not_every_first_fires :
    ¬ (referenceStructure RelationEnv.empty pairPool).sat Env.closed everyFirstFires bothAB :=
  askWith_refuted (by rfl) ask_ab_not_every_first_fires_answer

end Mettapedia.OSLF.NativeTypes.GeneratedLogic.SetReadings
