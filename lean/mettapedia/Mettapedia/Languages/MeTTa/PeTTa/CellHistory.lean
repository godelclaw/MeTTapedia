import Mettapedia.Languages.MeTTa.PeTTa.NamedSpaces

/-!
# Latest-value observation of an ordered state-cell history

An append-only private row space can represent PeTTa's named replacement
cells when clients observe only the latest value at each key. The construction
selects the final matching row, independently of the function-update store.
Its append law then realizes the existing `NamedSpaces.Store.putCell`.

This is a representation law for the value observer. It does not equate row
allocation, history exposure, uninitialized-cell faults or the execution of
an authored adapter. Those require their own qualified execution connection.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.CellHistory

open NamedSpaces (Store)

universe uValue uSpace
variable {Value : Type uValue} {Space : Type uSpace}

abbrev History (Value : Type uValue) := List (String × Value)

def values (history : History Value) (name : String) : List Value :=
  history.filterMap fun entry => if entry.1 = name then some entry.2 else none

def read (history : History Value) (name : String) : Option Value :=
  (values history name).getLast?

@[simp] theorem values_append (first second : History Value) (name : String) :
    values (first ++ second) name = values first name ++ values second name := by
  simp [values, List.filterMap_append]

@[simp] theorem read_empty (name : String) : read ([] : History Value) name = none := rfl

theorem read_append_entry (history : History Value) (name key : String) (value : Value) :
    read (history ++ [(key, value)]) name =
      if name = key then some value else read history name := by
  by_cases same : name = key
  · subst key
    simp [read, values, List.filterMap_append]
  · have other : key ≠ name := Ne.symm same
    simp [read, values, List.filterMap_append, same, other]

theorem read_append_update (history : History Value) (key : String) (value : Value) :
    read (history ++ [(key, value)]) = Function.update (read history) key (some value) := by
  funext name
  rw [read_append_entry]
  by_cases same : name = key <;> simp [Function.update, same]

@[simp] theorem read_written (history : History Value) (key : String) (value : Value) :
    read (history ++ [(key, value)]) key = some value := by
  simp [read_append_entry]

theorem read_other (history : History Value) (key name : String) (value : Value)
    (different : name ≠ key) :
    read (history ++ [(key, value)]) name = read history name := by
  simp [read_append_entry, different]

/-- Realize cells in the existing store, retaining its core and all allocated
spaces. No second store or state transition is introduced. -/
def install (history : History Value) (state : Store Space Value) : Store Space Value :=
  { state with cells := read history }

theorem install_append (history : History Value) (state : Store Space Value)
    (key : String) (value : Value) :
    install (history ++ [(key, value)]) state = (install history state).putCell key value := by
  simp only [install, Store.putCell, read_append_update]

theorem read_as_last_index (history : History Value) (name : String) :
    read history name = (values history name)[(values history name).length - 1]? :=
  List.getLast?_eq_getElem?

theorem written_cell_present (history : History Value) (key : String) (value : Value) :
    ∃ index : Nat, (values (history ++ [(key, value)]) key)[index]? = some value := by
  refine ⟨(values history key).length, ?_⟩
  simp [values, List.filterMap_append]

/-- Latest-value agreement deliberately does not identify full histories. -/
theorem same_values_different_histories :
    read [("session", 1), ("session", 2)] = read [("session", 2)] ∧
    ([("session", 1), ("session", 2)] : History Nat) ≠ [("session", 2)] := by
  constructor
  · funext name
    by_cases same : name = "session"
    · subst name
      rfl
    · simp [read, values, Ne.symm same]
  · decide

end Mettapedia.Languages.MeTTa.PeTTa.CellHistory
