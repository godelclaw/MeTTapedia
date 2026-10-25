import Mathlib.Data.List.GetD
import Mathlib.Tactic

/-!
# Local candidates in a composed occurrence view

An overlay presents a frozen inherited prefix followed by its local rows.
Native candidate indexes address local storage. Matching reads that local row;
publication translates its coordinate by the inherited prefix length.

The same candidate list, including order, repeated coordinates and out-of-range
entries, produces the same observations through the two lawful realizations.
The negative controls distinguish a local coordinate from a composed one, even
when they happen to select rows with equal values. Candidate completeness,
source ownership and snapshot construction are separate native obligations.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.OverlayCandidateCoordinates

variable {Row : Type*}

def visible (base : List Row) (inherited : Nat) (localRows : List Row) : List Row :=
  base.take inherited ++ localRows

def publishLocal (inheritedRows : List Row) (index : Nat) : Nat := inheritedRows.length + index

theorem read_published_local (inheritedRows localRows : List Row) (index : Nat) :
    (inheritedRows ++ localRows)[publishLocal inheritedRows index]? = localRows[index]? := by
  unfold publishLocal
  rw [List.getElem?_append_right (by omega)]
  simp

theorem read_visible_local (base : List Row) (inherited : Nat)
    (localRows : List Row) (index : Nat) :
    (visible base inherited localRows)[(base.take inherited).length + index]? =
      localRows[index]? := by
  exact read_published_local (base.take inherited) localRows index

/-- The authoritative matcher observes a row and its published occurrence. -/
def selectLocal (accepts : Row → Bool) (inheritedRows localRows : List Row)
    (candidates : List Nat) : List (Nat × Row) :=
  candidates.filterMap fun index => localRows[index]?.bind fun row =>
    if accepts row then some (publishLocal inheritedRows index, row) else none

/-- A reference which reads the composed view after translating the coordinate. -/
def selectComposed (accepts : Row → Bool) (inheritedRows localRows : List Row)
    (candidates : List Nat) : List (Nat × Row) :=
  candidates.filterMap fun index =>
    (inheritedRows ++ localRows)[publishLocal inheritedRows index]?.bind fun row =>
      if accepts row then some (publishLocal inheritedRows index, row) else none

theorem selected_observations (accepts : Row → Bool) (inheritedRows localRows : List Row)
    (candidates : List Nat) :
    selectLocal accepts inheritedRows localRows candidates =
      selectComposed accepts inheritedRows localRows candidates := by
  simp only [selectLocal, selectComposed, read_published_local]

theorem selected_append (accepts : Row → Bool) (inheritedRows localRows : List Row)
    (first second : List Nat) :
    selectLocal accepts inheritedRows localRows (first ++ second) =
      selectLocal accepts inheritedRows localRows first ++
        selectLocal accepts inheritedRows localRows second := by
  simp [selectLocal]

theorem inherited_tail_irrelevant (accepts : Row → Bool)
    (base tail : List Row) (inherited : Nat) (bounded : inherited ≤ base.length)
    (localRows : List Row) (candidates : List Nat) :
    selectLocal accepts ((base ++ tail).take inherited) localRows candidates =
      selectLocal accepts (base.take inherited) localRows candidates := by
  rw [List.take_append_of_le_length bounded]

/-- Changing offset values cannot make two offset occurrence coordinates equal. -/
theorem publication_injective (inheritedRows : List Row) {left right : Nat} :
    publishLocal inheritedRows left = publishLocal inheritedRows right ↔ left = right := by
  simp [publishLocal]

theorem translated_local_is_not_inherited (inheritedRows : List Row) (offset : Nat)
    {inherited : Nat} (inside : inherited < inheritedRows.length) :
    publishLocal inheritedRows offset ≠ inherited := by
  unfold publishLocal
  omega

theorem out_of_range_stays_absent (inheritedRows localRows : List Row)
    {index : Nat} (outside : localRows.length ≤ index) :
    (inheritedRows ++ localRows)[publishLocal inheritedRows index]? = none := by
  rw [read_published_local]
  exact List.getElem?_eq_none outside

namespace Controls

def wrongLocalRead (inheritedRows localRows : List Nat) (index : Nat) : Option Nat :=
  (inheritedRows ++ localRows)[index]?

theorem untranslated_coordinate_changes_row :
    wrongLocalRead [20] [10] 0 = some 20 ∧
    ([10] : List Nat)[0]? = some 10 := by decide

theorem equal_values_do_not_identify_occurrences :
    wrongLocalRead [10] [10] 0 = some 10 ∧
    publishLocal [10] 0 = 1 ∧ publishLocal [10] 0 ≠ 0 := by decide

theorem duplicate_candidates_remain_duplicate_occurrences :
    selectLocal (fun _ => true) [20] [10, 10] [1, 0, 1, 5] =
      [(2, 10), (1, 10), (2, 10)] := by decide

theorem matcher_retains_authority :
    selectLocal (fun row => row == 10) [30] [20, 10, 20] [0, 1, 2] =
      [(2, 10)] := by decide

end Controls

/-! A derived candidate view and the public iterator may enumerate the same
occurrences differently. A bijection changes coordinates; equal integer
positions alone do not establish that they name the same occurrence. -/
namespace ReorderedView

def readPublic {count : Nat} (rows : Fin count → Row)
    (order : Equiv.Perm (Fin count)) (index : Fin count) : Row :=
  rows (order index)

theorem translated_read {count : Nat} (rows : Fin count → Row)
    (order : Equiv.Perm (Fin count)) (candidate : Fin count) :
    readPublic rows order (order.symm candidate) = rows candidate := by
  simp [readPublic]

def selectCandidates {count : Nat} (rows : Fin count → Row)
    (accepts : Row → Bool) (candidates : List (Fin count)) : List (Fin count × Row) :=
  candidates.filterMap fun index =>
    if accepts (rows index) then some (index, rows index) else none

def selectTranslated {count : Nat} (rows : Fin count → Row)
    (order : Equiv.Perm (Fin count)) (accepts : Row → Bool)
    (candidates : List (Fin count)) : List (Fin count × Row) :=
  candidates.filterMap fun index =>
    let row := readPublic rows order (order.symm index)
    if accepts row then some (index, row) else none

theorem ordered_observations {count : Nat} (rows : Fin count → Row)
    (order : Equiv.Perm (Fin count)) (accepts : Row → Bool)
    (candidates : List (Fin count)) :
    selectTranslated rows order accepts candidates =
      selectCandidates rows accepts candidates := by
  simp only [selectTranslated, translated_read, selectCandidates]

theorem coordinate_translation_injective {count : Nat}
    (order : Equiv.Perm (Fin count)) : Function.Injective order.symm :=
  order.symm.injective

theorem selection_preserves_split {count : Nat} (rows : Fin count → Row)
    (accepts : Row → Bool) (first second : List (Fin count)) :
    selectCandidates rows accepts (first ++ second) =
      selectCandidates rows accepts first ++ selectCandidates rows accepts second := by
  simp [selectCandidates]

theorem untranslated_read_can_reject_valid_candidate :
    let rows : Fin 2 → Nat := fun index => if index = 0 then 10 else 20
    let order := Equiv.swap (0 : Fin 2) 1
    rows 0 = 10 ∧ readPublic rows order 0 = 20 ∧
      readPublic rows order (order.symm 0) = 10 := by decide

theorem duplicate_observations_survive_reordering :
    selectTranslated (fun index : Fin 2 => if index = 0 then 10 else 20)
      (Equiv.swap 0 1) (fun row => row == 10) [0, 1, 0] = [(0, 10), (0, 10)] := by
  decide

end ReorderedView

end Mettapedia.Machines.OverlayCandidateCoordinates
