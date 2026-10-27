import Mettapedia.OSLF.NativeTypes.GeneratedLogic.FrontDoorParts
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.BagCanonicalParts
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.PetriControls

/-!
# Controls: splits of markings

The Petri net of `PetriControls` reads its markings modulo the bag laws, so a marking splits into any two
sub-markings. Its canonical forms sort every bag, and the parts of a sorted marking are listed by dealing its tokens
into two (`BagForms.parts`). Closed parts regions then decide splits, and the front door proves and refutes them.

- `{A, B}` splits into `{A}` and `{B}`, and so does `{B, A}` (`ab_splits`, `ba_splits`).
- `{A, B, D}` has a part that fires beside a non-empty part (`abd_part_fires`); `{A, D}` has none (`ad_no_part_fires`).
- Every part of `{C, C}` fires or is empty (`cc_every_part`); `{A, C}` has a part, `{A}`, that does neither
  (`ac_not_every_part`).
- `{A, B}` steps to a marking that splits into `{C}` and `{D}` (`ab_steps_to_split`).
- The front door with the parts decider proves the split of `{A, B, D}` and refutes that of `{A, D}`
  (`ask_abd_part_fires`, `ask_ad_no_part_fires`); without it the question stays open (`ask_abd_open_without_parts`),
  since a canonical region holds a marking's successors and not its parts.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.GeneratedLogic.PetriControls

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine (RelationEnv)

/-- The parts of markings, listed. -/
def petriParts : PartsListing RelationEnv.empty petriCore BagForms.sortBags (BagForms.domain petriCore) :=
  BagForms.parts petri_no_equations petri_no_algebra

theorem parts_true {formula : Formula 0} {term : Pattern} (rounds : ℕ) (fragment : formula.behaviouralParts = true)
    (decided : decideParts RelationEnv.empty petriCore 2 BagForms.sortBags (BagForms.domain petriCore) List.singleton
      petriParts formula term rounds = some true) :
    Petri.sat Env.closed formula term :=
  (decideParts_sound (BagForms.canonical petri_no_equations petri_no_algebra)
    (BagForms.coherent petri_no_equations petri_no_algebra petri_guarded 2) fragment decided).mp rfl

theorem parts_false {formula : Formula 0} {term : Pattern} (rounds : ℕ) (fragment : formula.behaviouralParts = true)
    (decided : decideParts RelationEnv.empty petriCore 2 BagForms.sortBags (BagForms.domain petriCore) List.singleton
      petriParts formula term rounds = some false) :
    ¬ Petri.sat Env.closed formula term := fun holds =>
  Bool.false_ne_true ((decideParts_sound (BagForms.canonical petri_no_equations petri_no_algebra)
    (BagForms.coherent petri_no_equations petri_no_algebra petri_guarded 2) fragment decided).mpr holds)

def abd : Pattern := marking [token "A", token "B", token "D"]
def cc : Pattern := marking [token "C", token "C"]
def ac : Pattern := marking [token "A", token "C"]

/-- Splits into `{A}` and `{B}`. -/
def splitsAB : Formula 0 := .split .hashBag (.is (marking [token "A"])) (.is (marking [token "B"]))

/-- Some part fires beside a non-empty part. -/
def partFires : Formula 0 := .split .hashBag steps (.nonEmpty .hashBag)

/-- Every part fires or is empty. -/
def everyPartFiresOrEmpty : Formula 0 := .everySplit .hashBag (.or steps (.empty .hashBag)) .bot

/-- Steps to a marking that splits into `{C}` and `{D}`. -/
def stepsToSplitCD : Formula 0 :=
  .possibly .any (.split .hashBag (.is (marking [token "C"])) (.is (marking [token "D"])))

/-- **`{A, B}` splits into `{A}` and `{B}`.** -/
theorem ab_splits : Petri.sat Env.closed splitsAB ab := parts_true 3 rfl (by decide +kernel)

/-- **So does `{B, A}`.** -/
theorem ba_splits : Petri.sat Env.closed splitsAB ba := parts_true 3 rfl (by decide +kernel)

/-- **`{A, B, D}` has a part that fires beside a non-empty part**: `{A, B}` and `{D}`. -/
theorem abd_part_fires : Petri.sat Env.closed partFires abd := parts_true 3 rfl (by decide +kernel)

/-- **`{A, D}` has none.** -/
theorem ad_no_part_fires : ¬ Petri.sat Env.closed partFires ad := parts_false 3 rfl (by decide +kernel)

/-- **Every part of `{C, C}` fires or is empty.** -/
theorem cc_every_part : Petri.sat Env.closed everyPartFiresOrEmpty cc := parts_true 3 rfl (by decide +kernel)

/-- **`{A, C}` has a part that does neither**: `{A}`. -/
theorem ac_not_every_part : ¬ Petri.sat Env.closed everyPartFiresOrEmpty ac := parts_false 3 rfl (by decide +kernel)

/-- **`{A, B}` steps to a marking that splits into `{C}` and `{D}`.** -/
theorem ab_steps_to_split : Petri.sat Env.closed stepsToSplitCD ab := parts_true 3 rfl (by decide +kernel)

/-! ### At the front door -/

/-- The parts decider for markings. -/
def petriPartsDecider : Decider RelationEnv.empty petriCore :=
  partsDecider (fuel := 2) (presentations := List.singleton) (BagForms.canonical petri_no_equations petri_no_algebra)
    (BagForms.coherent petri_no_equations petri_no_algebra petri_guarded 2) petriParts 3

theorem ask_abd_part_fires_answer :
    askWith RelationEnv.empty petriSignature petriCore 2 partFires abd petriPartsDecider none 2 (some petriForms) =
      .proved .decided := by
  decide +kernel

/-- **The front door with the parts decider proves that a part of `{A, B, D}` fires.** -/
theorem ask_abd_part_fires : Petri.sat Env.closed partFires abd := askWith_proved (by rfl) ask_abd_part_fires_answer

theorem ask_ad_no_part_fires_answer :
    askWith RelationEnv.empty petriSignature petriCore 2 partFires ad petriPartsDecider none 2 (some petriForms) =
      .refuted .decided := by
  decide +kernel

/-- **And refutes it for `{A, D}`.** -/
theorem ask_ad_no_part_fires : ¬ Petri.sat Env.closed partFires ad := askWith_refuted (by rfl) ask_ad_no_part_fires_answer

/-- **Without the parts decider the front door leaves the split open.** -/
theorem ask_abd_open_without_parts :
    ask RelationEnv.empty petriSignature petriCore 2 partFires abd none 2 (some petriForms) = .unknown 2 := by
  decide +kernel

end Mettapedia.OSLF.NativeTypes.GeneratedLogic.PetriControls
