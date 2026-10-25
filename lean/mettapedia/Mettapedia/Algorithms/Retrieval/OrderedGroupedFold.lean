import Mettapedia.Algorithms.Retrieval.GroupedFold

/-!
Ordered keyed aggregation with a concrete first-occurrence list state.
Block consumption preserves the complete list, not just per-key values.
The update function is arbitrary: no associativity or commutativity is used.
This is an algorithmic observation law, separate from native implementation
qualification.
-/

namespace Mettapedia.Algorithms.Retrieval.OrderedGroupedFold

variable {K R V : Type*} [DecidableEq K]

/-- Update the first matching key, or append a newly encountered key. -/
def write (step : R → V → R) (initial : K → R)
    (state : List (K × R)) (key : K) (value : V) : List (K × R) :=
  match state with
  | [] => [(key, step (initial key) value)]
  | (stored, accumulator) :: rest =>
      if key = stored then (stored, step accumulator value) :: rest
      else (stored, accumulator) :: write step initial rest key value

/-- The first stored value, or the declared initial value for an absent key. -/
def observe (initial : K → R) (state : List (K × R)) (query : K) : R :=
  match state with
  | [] => initial query
  | (key, value) :: rest =>
      if query = key then value else observe initial rest query

theorem observe_write (step : R → V → R) (initial : K → R)
    (state : List (K × R)) (key : K) (value : V) (query : K) :
    observe initial (write step initial state key value) query =
      if query = key then step (observe initial state query) value
      else observe initial state query := by
  induction state with
  | nil =>
      by_cases same : query = key <;> simp [write, observe, same]
  | cons entry rest ih =>
      rcases entry with ⟨stored, accumulator⟩
      by_cases first : key = stored <;>
        by_cases queried : query = stored <;>
          by_cases same : query = key <;>
            simp_all [write, observe]

theorem observe_write_function (step : R → V → R) (initial : K → R)
    (state : List (K × R)) (key : K) (value : V) :
    (fun query => observe initial (write step initial state key value) query) =
      Function.update (fun query => observe initial state query) key
        (step (observe initial state key) value) := by
  funext query
  by_cases same : query = key <;> simp [observe_write, same]

/-- Consume occurrences in their input order, retaining first-key order. -/
def grouped (step : R → V → R) (initial : K → R)
    (state : List (K × R)) (entries : List (K × V)) : List (K × R) :=
  entries.foldl (fun state entry => write step initial state entry.1 entry.2) state

/-- Consume blocks without constructing their flattened occurrence list. -/
def groupedBlocks (step : R → V → R) (initial : K → R)
    (state : List (K × R)) (blocks : List (List (K × V))) : List (K × R) :=
  blocks.foldl (fun state block => grouped step initial state block) state

/-- Storage order changes only on a key's first occurrence. Updating a
previously encountered group never moves it to the end. -/
theorem keys_write (step : R → V → R) (initial : K → R)
    (state : List (K × R)) (key : K) (value : V) :
    (write step initial state key value).map Prod.fst =
      if key ∈ state.map Prod.fst then state.map Prod.fst
      else state.map Prod.fst ++ [key] := by
  induction state with
  | nil => simp [write]
  | cons entry rest ih =>
      rcases entry with ⟨stored, accumulator⟩
      by_cases same : key = stored
      · simp [write, same]
      · by_cases found : key ∈ rest.map Prod.fst <;>
          simp [write, same, ih, found]

/-- A streaming grouped fold retains exactly the first-encounter key scan,
independently of the accumulator arithmetic and without sorting keys. -/
theorem keys_grouped (step : R → V → R) (initial : K → R)
    (state : List (K × R)) (entries : List (K × V)) :
    (grouped step initial state entries).map Prod.fst =
      entries.foldl (fun keys entry =>
        if entry.1 ∈ keys then keys else keys ++ [entry.1]) (state.map Prod.fst) := by
  induction entries generalizing state with
  | nil => rfl
  | cons entry rest ih =>
      simp only [grouped, List.foldl_cons] at *
      rw [ih, keys_write]

theorem groupedBlocks_eq_flatten (step : R → V → R) (initial : K → R)
    (state : List (K × R)) (blocks : List (List (K × V))) :
    groupedBlocks step initial state blocks =
      grouped step initial state blocks.flatten := by
  induction blocks generalizing state with
  | nil => rfl
  | cons block rest ih =>
      simpa [groupedBlocks, grouped, List.foldl_append] using
        ih (state := grouped step initial state block)

/-- Forgetting ordered storage agrees with the existing keyed-value model. -/
theorem observe_grouped (step : R → V → R) (initial : K → R)
    (state : List (K × R)) (entries : List (K × V)) :
    (fun query => observe initial (grouped step initial state entries) query) =
      GroupedFold.grouped step (fun query => observe initial state query) entries := by
  induction entries generalizing state with
  | nil => rfl
  | cons entry rest ih =>
      simpa [grouped, GroupedFold.grouped, observe_write_function] using
        ih (state := write step initial state entry.1 entry.2)

theorem observe_groupedBlocks (step : R → V → R) (initial : K → R)
    (state : List (K × R)) (blocks : List (List (K × V))) :
    (fun query => observe initial (groupedBlocks step initial state blocks) query) =
      GroupedFold.groupedBlocks step (fun query => observe initial state query) blocks := by
  rw [groupedBlocks_eq_flatten, GroupedFold.groupedBlocks_eq_flatten]
  exact observe_grouped step initial state blocks.flatten

/-- Stream original events into groups selected by a pure projection. The
step receives the original event, not just its projected identity. -/
def groupedBy (project : V → K) (step : R → V → R) (initial : K → R)
    (state : List (K × R)) (events : List V) : List (K × R) :=
  events.foldl (fun state event => write step initial state (project event) event) state

theorem groupedBy_eq_rekeyed (project : V → K) (step : R → V → R)
    (initial : K → R) (state : List (K × R)) (events : List V) :
    groupedBy project step initial state events =
      grouped step initial state (events.map (fun event => (project event, event))) := by
  simp [groupedBy, grouped, List.foldl_map]

/-- Projected groups retain exactly the original event subsequence for each
key, including collisions of different source identities and repeated events. -/
theorem observe_groupedBy (project : V → K) (step : R → V → R)
    (initial : K → R) (state : List (K × R)) (events : List V) (key : K) :
    observe initial (groupedBy project step initial state events) key =
      events.foldl (fun acc event => if project event = key then step acc event else acc)
        (observe initial state key) := by
  rw [groupedBy_eq_rekeyed]
  have h := congrFun (observe_grouped step initial state
    (events.map (fun event => (project event, event)))) key
  rw [h, GroupedFold.observe_grouped]
  simp [List.foldl_map]

theorem keys_groupedBy (project : V → K) (step : R → V → R)
    (initial : K → R) (state : List (K × R)) (events : List V) :
    (groupedBy project step initial state events).map Prod.fst =
      events.foldl (fun keys event =>
        if project event ∈ keys then keys else keys ++ [project event]) (state.map Prod.fst) := by
  rw [groupedBy_eq_rekeyed, keys_grouped]
  simp [List.foldl_map]

example : groupedBy (fun (n : Nat) => n / 2) (fun history n => history ++ [n])
    (fun _ => []) [] [3, 0, 2, 3] = [(1, [3, 2, 3]), (0, [0])] := by
  decide +kernel

example : groupedBy (fun (n : Nat) => n / 2) (fun (total : Nat) n => total * 10 + n)
    (fun _ => 0) [] [3, 2] ≠
      groupedBy (fun (n : Nat) => n / 2) (fun (total : Nat) n => total * 10 + n)
        (fun _ => 0) [] [2, 3] := by
  decide +kernel

example : grouped (fun (total : Int) value => total + value) (fun (_ : Bool) => 0)
    [] [(false, 2), (true, 8), (false, 5)] = [(false, 7), (true, 8)] := by
  decide +kernel

example : groupedBlocks (fun (total : Int) value => total * 10 + value)
    (fun (_ : Bool) => 0) [] [[(false, 2)], [], [(false, 5)]] = [(false, 25)] := by
  decide +kernel

example : grouped (fun (total : Int) value => total * 10 + value)
    (fun (_ : Bool) => 0) [] [(false, 5), (false, 2)] ≠ [(false, 25)] := by
  decide +kernel

example : grouped (fun (total : Int) value => total + value) (fun (_ : Bool) => 0)
    [] [(false, 0)] ≠ [] := by
  decide +kernel

example : grouped (fun (total : Int) value => total + value) (fun (_ : Bool) => 0)
    [] [(true, 8), (false, 2)] ≠ [(false, 2), (true, 8)] := by
  decide +kernel

#print axioms groupedBlocks_eq_flatten
#print axioms keys_write
#print axioms keys_grouped
#print axioms observe_grouped
#print axioms observe_groupedBlocks
#print axioms observe_groupedBy
#print axioms keys_groupedBy

section IndependentAccumulators

variable {Event Left Right : Type*}

/-- One event traversal with independent accumulators, possibly of different
types. Neither accumulator observes the other's intermediate state. -/
def foldProduct (left : Left → Event → Left) (right : Right → Event → Right)
    (initial : Left × Right) (events : List Event) : Left × Right :=
  events.foldl (fun state event => (left state.1 event, right state.2 event)) initial

/-- Fold fusion preserves each original sequence of steps, even when those
steps are non-associative (for example a specified floating-point schedule). -/
theorem foldProduct_eq_separate (left : Left → Event → Left)
    (right : Right → Event → Right) (initial : Left × Right) (events : List Event) :
    foldProduct left right initial events =
      (events.foldl left initial.1, events.foldl right initial.2) := by
  induction events generalizing initial with
  | nil => rfl
  | cons event rest ih =>
      simpa only [foldProduct, List.foldl_cons] using
        ih (left initial.1 event, right initial.2 event)

/-- Each signal may select a different subsequence of the shared stream.
Skipping an event in one lane does not reorder that lane's contributions. -/
theorem foldProduct_select_eq_separate (left : Left → Event → Left)
    (right : Right → Event → Right) (keepLeft keepRight : Event → Bool)
    (initial : Left × Right) (events : List Event) :
    foldProduct (fun acc event => if keepLeft event then left acc event else acc)
      (fun acc event => if keepRight event then right acc event else acc) initial events =
      ((events.filter keepLeft).foldl left initial.1,
       (events.filter keepRight).foldl right initial.2) := by
  simp only [foldProduct_eq_separate, List.foldl_filter]

/-- Keyed folds can share input traversal without forgetting the first-key
order or reassociating either group's updates. -/
theorem grouped_product_eq_separate
    (left : Left → V → Left) (right : Right → V → Right)
    (initialLeft : K → Left) (initialRight : K → Right)
    (stateLeft : List (K × Left)) (stateRight : List (K × Right))
    (events : List (K × V)) :
    foldProduct
      (fun state entry => write left initialLeft state entry.1 entry.2)
      (fun state entry => write right initialRight state entry.1 entry.2)
      (stateLeft, stateRight) events =
      (grouped left initialLeft stateLeft events,
       grouped right initialRight stateRight events) :=
  foldProduct_eq_separate _ _ _ _

example : foldProduct (fun (total : Nat) value => total * 10 + value)
    (fun (history : List Nat) value => history ++ [value]) (0, []) [2, 5] =
      (25, [2, 5]) := by decide +kernel

example : foldProduct (fun (total : Nat) value => total * 10 + value)
    (fun (count : Nat) _ => count + 1) (0, 0) [5, 2] ≠ (25, 2) := by
  decide +kernel

#print axioms foldProduct_eq_separate
#print axioms foldProduct_select_eq_separate
#print axioms grouped_product_eq_separate

end IndependentAccumulators

end Mettapedia.Algorithms.Retrieval.OrderedGroupedFold
