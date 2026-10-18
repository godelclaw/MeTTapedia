import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Range
import Mathlib.Logic.Function.Basic

/-!
# Current pins, supersession and unavailable reads

Distinct appended pins admit arbitrarily large retained collections. Replacing
the current value of an agent-chosen topic avoids growth for that topic; it
does not bound the number of topics or erase archival versions. There is no
global capacity limit or mandatory review schedule in this model.
-/

namespace Mettapedia.CogArch.Memory.PinSupersession

def appendTrace : Nat → Finset Nat
  | 0 => ∅
  | n + 1 => insert n (appendTrace n)

theorem appendTrace_eq_range (n : Nat) : appendTrace n = Finset.range n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [appendTrace, ih, Finset.range_add_one]

theorem distinct_pin_history_has_no_uniform_bound (bound : Nat) :
    ∃ steps, bound < (appendTrace steps).card := by
  exact ⟨bound + 1, by simp [appendTrace_eq_range]⟩

theorem fresh_pin_increases_count {pins : Finset Nat} {pin : Nat} (fresh : pin ∉ pins) :
    (insert pin pins).card = pins.card + 1 := Finset.card_insert_of_notMem fresh

variable {Topic Body : Type*} [DecidableEq Topic]

abbrev Current (Topic Body : Type*) := Topic → Option Body

def replace (current : Current Topic Body) (topic : Topic) (body : Body) : Current Topic Body :=
  Function.update current topic (some body)

def active (topics : Finset Topic) (current : Current Topic Body) : Finset Topic :=
  topics.filter fun topic => (current topic).isSome

theorem replace_current (current : Current Topic Body) (topic : Topic) (body : Body) :
    replace current topic body topic = some body := by simp [replace]

theorem replace_preserves_other (current : Current Topic Body) (topic other : Topic)
    (body : Body) (different : other ≠ topic) :
    replace current topic body other = current other := by simp [replace, different]

theorem replace_twice (current : Current Topic Body) (topic : Topic) (a b : Body) :
    replace (replace current topic a) topic b = replace current topic b := by
  simp [replace]

omit [DecidableEq Topic] in
/-- The bound is the chosen topic set, not a fixed runtime cap. -/
theorem active_count_le_topics (topics : Finset Topic) (current : Current Topic Body) :
    (active topics current).card ≤ topics.card := Finset.card_filter_le _ _

theorem superseding_does_not_grow_current (topics : Finset Topic)
    (current : Current Topic Body) (topic : Topic) (body : Body)
    (already : (current topic).isSome = true) :
    active topics (replace current topic body) = active topics current := by
  ext other
  simp only [active, Finset.mem_filter]
  by_cases same : other = topic
  · subst other
    simp [replace, already]
  · simp [replace, same]

/-- Only an actual read (including an actually empty file) supplies a base
for read-modify-write. Unavailability must not be interpreted as empty. -/
def prepareAppend (observed : Option (List Body)) (body : Body) : Option (List Body) :=
  observed.map fun previous => previous ++ [body]

theorem unavailable_read_has_no_write (body : Body) :
    prepareAppend none body = none := rfl

theorem observed_empty_can_be_initialized (body : Body) :
    prepareAppend (some []) body = some [body] := rfl

theorem prepared_append_preserves_previous (previous : List Body) (body : Body) :
    prepareAppend (some previous) body = some (previous ++ [body]) := rfl

/-- The read-failure-as-empty policy loses old content if replacement is then
allowed. This is a conditional failure scenario, not evidence of a live loss. -/
theorem read_failure_as_empty_can_lose_pins :
    let previous : List Nat := [1, 2]
    let unavailable : Option (List Nat) := none
    let replacement := unavailable.getD [] ++ [3]
    1 ∈ previous ∧ 1 ∉ replacement := by decide

end Mettapedia.CogArch.Memory.PinSupersession
