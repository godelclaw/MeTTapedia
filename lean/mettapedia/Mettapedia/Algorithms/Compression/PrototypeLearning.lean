import Mettapedia.Algorithms.Compression.CostedArtifact

/-!
# Ordered prototype reconstruction and bounded deterministic fitting

Rows retain optional coordinates; a missing row request creates missing support,
not numerical zeroes. Every present request is bounds checked, including when
the declared row width is zero. The selection laws describe logical traversal,
not physical tensor storage or a refinement proof for the C implementation.

The fitting laws use arbitrary ordered scores and arbitrary partial updates.
They do not assume associative floating addition or claim that Lloyd updates
find a global optimum. Acceptance remains the original task's fixed predicate.
-/

set_option autoImplicit false

namespace Mettapedia.Algorithms.Compression.PrototypeLearning

variable {α : Type*}

def selectRow (width : Nat) (rows : List (List (Option α))) :
    Option Nat → Option (List (Option α))
  | none => some (List.replicate width none)
  | some index => rows[index]?

def gatherRows (width : Nat) (rows : List (List (Option α))) :
    List (Option Nat) → Option (List (List (Option α)))
  | [] => some []
  | request :: rest => do
      let first ← selectRow width rows request
      let later ← gatherRows width rows rest
      pure (first :: later)

theorem gatherRows_length (width : Nat) (rows : List (List (Option α)))
    (requests : List (Option Nat)) (result : List (List (Option α)))
    (found : gatherRows width rows requests = some result) : result.length = requests.length := by
  induction requests generalizing result with
  | nil => simp [gatherRows] at found; subst result; rfl
  | cons request rest ih =>
      cases first : selectRow width rows request with
      | none => simp [gatherRows, first] at found
      | some row =>
          cases later : gatherRows width rows rest with
          | none => simp [gatherRows, first, later] at found
          | some tail =>
              simp [gatherRows, first, later] at found
              subst result
              simpa using congrArg Nat.succ (ih tail later)

theorem gatherRows_get (width : Nat) (rows : List (List (Option α)))
    (requests : List (Option Nat)) (result : List (List (Option α)))
    (found : gatherRows width rows requests = some result) (position : Nat) :
    result[position]? = (requests[position]?).bind (selectRow width rows) := by
  induction requests generalizing result position with
  | nil => simp [gatherRows] at found; subst result; simp
  | cons request rest ih =>
      cases first : selectRow width rows request with
      | none => simp [gatherRows, first] at found
      | some row =>
          cases later : gatherRows width rows rest with
          | none => simp [gatherRows, first, later] at found
          | some tail =>
              simp [gatherRows, first, later] at found
              subst result
              cases position with
              | zero => simp [first]
              | succ position => simpa using ih tail later position

theorem present_request_preserves_row (width : Nat) (rows : List (List (Option α)))
    (requests : List (Option Nat)) (result : List (List (Option α)))
    (found : gatherRows width rows requests = some result) (position index : Nat)
    (request : requests[position]? = some (some index)) : result[position]? = rows[index]? := by
  rw [gatherRows_get width rows requests result found position, request]
  rfl

theorem absent_request_preserves_absence (width : Nat) (rows : List (List (Option α)))
    (requests : List (Option Nat)) (result : List (List (Option α)))
    (found : gatherRows width rows requests = some result) (position : Nat)
    (request : requests[position]? = some none) :
    result[position]? = some (List.replicate width none) := by
  rw [gatherRows_get width rows requests result found position, request]
  rfl

theorem repeated_requests_keep_positions (width : Nat) (rows : List (List (Option α)))
    (requests : List (Option Nat)) (result : List (List (Option α)))
    (found : gatherRows width rows requests = some result) (first second : Nat)
    (same : requests[first]? = requests[second]?) : result[first]? = result[second]? := by
  rw [gatherRows_get width rows requests result found first,
      gatherRows_get width rows requests result found second, same]

theorem gatherRows_append (width : Nat) (rows : List (List (Option α)))
    (first second : List (Option Nat)) :
    gatherRows width rows (first ++ second) = (do
      let before ← gatherRows width rows first
      let after ← gatherRows width rows second
      pure (before ++ after)) := by
  induction first with
  | nil => simp [gatherRows]
  | cons request rest ih =>
      simp only [List.cons_append, gatherRows, ih]
      cases selected : selectRow width rows request <;> simp
      case some row =>
        cases before : gatherRows width rows rest <;> simp
        case some tail =>
          cases after : gatherRows width rows second <;> simp

theorem zero_width_still_checks_bounds (rows : List (List (Option α))) (index : Nat)
    (missing : rows[index]? = none) : gatherRows 0 rows [some index] = none := by
  simp [gatherRows, selectRow, missing]

section Ranked

variable {Score : Type*} [LinearOrder Score]

def choose (score : α → Score) (previous candidate : α) : α :=
  if score candidate < score previous then candidate else previous

theorem choose_tie_keeps_first (score : α → Score) (first second : α)
    (tie : score second = score first) : choose score first second = first := by
  simp [choose, tie]

theorem choose_le_previous (score : α → Score) (previous candidate : α) :
    score (choose score previous candidate) ≤ score previous := by
  unfold choose
  split
  · exact le_of_lt ‹_›
  · exact le_refl _

theorem choose_le_candidate (score : α → Score) (previous candidate : α) :
    score (choose score previous candidate) ≤ score candidate := by
  unfold choose
  split
  · exact le_refl _
  · exact le_of_not_gt ‹_›

def best (score : α → Score) : α → List α → α
  | previous, [] => previous
  | previous, candidate :: rest => best score (choose score previous candidate) rest

theorem best_le_previous (score : α → Score) (previous : α) (candidates : List α) :
    score (best score previous candidates) ≤ score previous := by
  induction candidates generalizing previous with
  | nil => exact le_refl _
  | cons candidate rest ih => exact (ih _).trans (choose_le_previous score previous candidate)

theorem best_le_member (score : α → Score) (previous : α) (candidates : List α)
    (candidate : α) (member : candidate ∈ candidates) :
    score (best score previous candidates) ≤ score candidate := by
  induction candidates generalizing previous with
  | nil => simp at member
  | cons first rest ih =>
      rcases List.mem_cons.mp member with rfl | later
      · exact (best_le_previous score (choose score previous candidate) rest).trans
          (choose_le_candidate score previous candidate)
      · exact ih _ later

end Ranked

def advance (step : α → Option α) : Nat → α → Option α
  | 0, value => some value
  | count + 1, value => (step value).bind (advance step count)

theorem advance_stable (step : α → Option α) (value : α)
    (stable : step value = some value) (count : Nat) : advance step count value = some value := by
  induction count with
  | zero => rfl
  | succ count ih => simp [advance, stable, ih]

theorem stable_has_no_later_cost_gain {Artifact : Type} (step : α → Option α)
    (value : α) (stable : step value = some value) (count : Nat)
    (encode : α → Artifact) (valid : Artifact → Bool) (cost : Artifact → Nat) :
    (advance step count value).map
      (fun next => CostedArtifact.accept valid cost (encode value) (encode next)) = some none := by
  rw [advance_stable step value stable count]
  simp only [Option.map_some]
  exact congrArg some (CostedArtifact.no_gain_refused valid cost _ _ (Nat.le_refl _))

namespace Controls

theorem duplicate_and_missing_rows :
    gatherRows 2 [[some 7, none], [none, some 9]] [some 1, none, some 1, some 0] =
      some [[none, some 9], [none, none], [none, some 9], [some 7, none]] := by decide

theorem row_order_is_not_a_bag :
    gatherRows 1 [[some 3], [some 8]] [some 1, some 0] ≠
      gatherRows 1 [[some 3], [some 8]] [some 0, some 1] := by decide

theorem empty_coordinates_do_not_admit_a_bad_row :
    gatherRows (α := Nat) 0 [[], []] [some 2] = none := by decide

theorem equal_distance_keeps_the_first_index :
    best Prod.snd (0, 4) [(1, 4), (2, 9)] = ((0, 4) : Nat × Nat) := by decide

end Controls

end Mettapedia.Algorithms.Compression.PrototypeLearning
