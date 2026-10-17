import Mettapedia.OSLF.NativeTypes.SortProfiles.Slots
import Mathlib.Data.Finset.Powerset

open Mettapedia.OSLF.Framework

/-!
# Site interfaces: index, rely and ambient variables

A generated site factors an authored rewrite source as a one-hole context
around a focus. Its metavariables fall into three classes:

* index variables, shared by the focus and the context; they stay fixed outside
  the generated modality;
* rely variables, supplied by the context alone; the modality discharges them;
* ambient variables, needed by the focus or by the target but not supplied by
  the context; they are ordinary parameters and not axes of the cube.

The local cube of a site has one slot per index variable, one per rely variable
and one for the target. `Slots.modalFamily` records the rely slots and the
output only; the two slot counts differ by exactly the number of index
variables (`slotCount_eq_family`). A site whose focus shares no variable with its
context (the beta site of the lambda calculus) has the same count in both.

A based signature choice is a set of profiles containing the all-star profile.
With `k` slots there are `2 ^ (2 ^ k - 1)` of them (`basedChoices_card`): eight
for the two product slots of the lambda calculus, one hundred and twenty-eight
for a receive site with an index channel, a rely message and a target.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.SortProfiles.SiteInterfaces

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.Framework.RedexPosition (fvarNames)
open Mettapedia.OSLF.Framework.ModalHypercube (HSort)
open Mettapedia.OSLF.NativeTypes.Generation.Occurrences

/-- Variables shared by the focus and its context. -/
def indexNames (site : Site) : List String :=
  ((fvarNames site.focus).filter fun name => (contextNames site.context).contains name).eraseDups

/-- Variables of the target that the source does not mention. -/
def targetOnlyNames (site : Site) : List String :=
  ((fvarNames site.rule.right).filter fun name => !(fvarNames site.rule.left).contains name).eraseDups

/-- Parameters of the focus or the target that the context does not supply. -/
def ambientNames (site : Site) : List String :=
  (site.hiddenNames ++ targetOnlyNames site).eraseDups

theorem index_names_spec (site : Site) (name : String) :
    name ∈ indexNames site ↔ name ∈ fvarNames site.focus ∧ name ∈ contextNames site.context := by
  simp [indexNames, List.mem_filter]

theorem target_only_names_spec (site : Site) (name : String) :
    name ∈ targetOnlyNames site ↔
      name ∈ fvarNames site.rule.right ∧ name ∉ fvarNames site.rule.left := by
  simp [targetOnlyNames, List.mem_filter]

theorem ambient_names_spec (site : Site) (name : String) :
    name ∈ ambientNames site ↔ name ∈ site.hiddenNames ∨ name ∈ targetOnlyNames site := by
  simp [ambientNames]

/-- Every context variable is an index variable or a rely variable. -/
theorem context_name_split (site : Site) (name : String) :
    name ∈ contextNames site.context ↔ name ∈ indexNames site ∨ name ∈ site.relyNames := by
  rw [index_names_spec, rely_names_spec]
  by_cases focus : name ∈ fvarNames site.focus <;> simp [focus]

theorem index_not_rely {site : Site} {name : String} (index : name ∈ indexNames site) :
    name ∉ site.relyNames := by
  rw [rely_names_spec]
  exact fun rely => rely.2 ((index_names_spec _ _).mp index).1

/-- Every focus variable is an index variable or a hidden (ambient) variable. -/
theorem focus_name_split (site : Site) (name : String) :
    name ∈ fvarNames site.focus ↔ name ∈ indexNames site ∨ name ∈ site.hiddenNames := by
  rw [index_names_spec, hidden_names_spec]
  by_cases context : name ∈ contextNames site.context <;> simp [context]

theorem index_not_hidden {site : Site} {name : String} (index : name ∈ indexNames site) :
    name ∉ site.hiddenNames := by
  rw [hidden_names_spec]
  exact fun hidden => hidden.2 ((index_names_spec _ _).mp index).2

/-- One slot per index variable, one per rely variable, one for the target. -/
def slotCount (site : Site) : Nat := (indexNames site).length + site.relyNames.length + 1

/-- The interface adds the index slots to the rely-and-output family. -/
theorem slotCount_eq_family (language : LanguageDef) (site : Site) :
    slotCount site = (indexNames site).length + (Slots.modalFamily language site).slotCount := by
  rw [Slots.modal_slot_count, slotCount, Nat.add_assoc]

theorem slotCount_eq_family_of_no_index (language : LanguageDef) (site : Site)
    (none : indexNames site = []) :
    slotCount site = (Slots.modalFamily language site).slotCount := by
  rw [slotCount_eq_family, none, List.length_nil, Nat.zero_add]

/-! ## Signature choices -/

/-- The all-star profile: the origin of a local cube. -/
def origin (slots : Nat) : Fin slots → HSort := fun _ => .star

/-- A based signature choice is any set of profiles containing the origin. -/
def basedChoices (slots : Nat) : Finset (Finset (Fin slots → HSort)) :=
  (Finset.univ : Finset (Fin slots → HSort)).powerset.filter fun choice => origin slots ∈ choice

theorem mem_basedChoices (slots : Nat) (choice : Finset (Fin slots → HSort)) :
    choice ∈ basedChoices slots ↔ origin slots ∈ choice := by
  simp [basedChoices]

/-- Based choices are the non-origin profiles chosen freely. -/
theorem basedChoices_eq_image (slots : Nat) :
    basedChoices slots =
      ((Finset.univ : Finset (Fin slots → HSort)).erase (origin slots)).powerset.image
        (insert (origin slots)) := by
  ext choice
  rw [mem_basedChoices, Finset.mem_image]
  constructor
  · intro based
    refine ⟨choice.erase (origin slots), ?_, Finset.insert_erase based⟩
    rw [Finset.mem_powerset]
    exact Finset.erase_subset_erase _ (Finset.subset_univ _)
  · rintro ⟨rest, _, rfl⟩
    exact Finset.mem_insert_self _ _

theorem basedChoices_card (slots : Nat) :
    (basedChoices slots).card = 2 ^ (2 ^ slots - 1) := by
  rw [basedChoices_eq_image, Finset.card_image_of_injOn, Finset.card_powerset,
    Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fun,
    HSort.card, Fintype.card_fin]
  intro first firstMember second secondMember equal
  have firstOut : origin slots ∉ first := fun member =>
    (Finset.mem_erase.mp (Finset.mem_powerset.mp firstMember member)).1 rfl
  have secondOut : origin slots ∉ second := fun member =>
    (Finset.mem_erase.mp (Finset.mem_powerset.mp secondMember member)).1 rfl
  have equal' : insert (origin slots) first = insert (origin slots) second := equal
  rw [← Finset.erase_insert firstOut, ← Finset.erase_insert secondOut, equal']

/-- The lambda cube: two product slots give eight based choices. -/
theorem lambda_cube_count : (basedChoices 2).card = 8 := by
  rw [basedChoices_card]; rfl

/-- A receive site with one index, one rely and a target: `2 ^ 7` choices. -/
theorem receive_cube_count : (basedChoices 3).card = 128 := by
  rw [basedChoices_card]; rfl

end Mettapedia.OSLF.NativeTypes.SortProfiles.SiteInterfaces
