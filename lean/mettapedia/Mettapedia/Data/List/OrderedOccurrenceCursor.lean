import Mathlib.Data.List.Basic
import Mathlib.Data.List.Induction
import Mathlib.Data.List.Enum

/-!
# Ordered occurrence cursors

An ordered space is observed as occurrences rather than as a set of values.
Occurrence identity keeps equal payloads distinct.  A broad-query cursor owns
the matching occurrence sequence visible when it is captured.  Later space
mutation therefore cannot append a new alternative, remove a pending one, or
reorder duplicates in that cursor.

The contract is deliberately independent of a storage representation.  A
runtime may realize the captured sequence with a flat snapshot, persistent
chunks, or a revision-pinned occurrence log, provided `drain_exact` holds.
-/

namespace Mettapedia.Data.List.OrderedOccurrenceCursor

structure Occurrence (α : Type*) where
  identity : Nat
  value : α
deriving DecidableEq, Repr

abbrev OrderedSpace (α : Type*) := List (Occurrence α)

/-- The captured sequence is retained for auditing; `remaining` is its
unconsumed suffix. -/
structure Cursor (α : Type*) where
  captured : List (Occurrence α)
  remaining : List (Occurrence α)
deriving Repr

namespace Cursor

def capture (accept : Occurrence α → Bool)
    (space : OrderedSpace α) : Cursor α :=
  let visible := space.filter accept
  { captured := visible, remaining := visible }

def step : Cursor α → Option (Occurrence α × Cursor α)
  | ⟨_, []⟩ => none
  | ⟨captured, occurrence :: rest⟩ =>
      some (occurrence, ⟨captured, rest⟩)

def drain (cursor : Cursor α) : List (Occurrence α) :=
  cursor.remaining

@[simp] theorem drain_eq_remaining (cursor : Cursor α) :
    cursor.drain = cursor.remaining := rfl

@[simp] theorem drain_capture_exact
    (accept : Occurrence α → Bool) (space : OrderedSpace α) :
    (capture accept space).drain = space.filter accept := by
  simp [capture]

@[simp] theorem captured_capture_exact
    (accept : Occurrence α → Bool) (space : OrderedSpace α) :
    (capture accept space).captured = space.filter accept := rfl

theorem step_preserves_capture
    {cursor next : Cursor α} {occurrence : Occurrence α}
    (stepped : cursor.step = some (occurrence, next)) :
    next.captured = cursor.captured := by
  cases cursor with
  | mk captured remaining =>
      cases remaining with
      | nil => simp [step] at stepped
      | cons head tail =>
          simp only [step, Option.some.injEq, Prod.mk.injEq] at stepped
          rcases stepped with ⟨rfl, rfl⟩
          rfl

theorem step_decomposes_observation
    {cursor next : Cursor α} {occurrence : Occurrence α}
    (stepped : cursor.step = some (occurrence, next)) :
    cursor.drain = occurrence :: next.drain := by
  cases cursor with
  | mk captured remaining =>
      cases remaining with
      | nil => simp [step] at stepped
      | cons head tail =>
          simp only [step, Option.some.injEq, Prod.mk.injEq] at stepped
          rcases stepped with ⟨rfl, rfl⟩
          rfl

end Cursor

/-- A cursor remains tied to its capture-time sequence across an arbitrary
later space state. -/
def StableAcross (cursor : Cursor α)
    (accept : Occurrence α → Bool) (before _after : OrderedSpace α) : Prop :=
  cursor.drain = before.filter accept

/-- A realization of an ordered broad-query cursor.  Exact list equality is
stronger than set or bag equality: it retains order, multiplicity, and the
identity of every occurrence.  Stability quantifies over an arbitrary later
space state, expressing logical-update isolation rather than a particular
mutation algorithm. -/
structure Contract
    (captureImpl : (Occurrence α → Bool) → OrderedSpace α → Cursor α) : Prop where
  drain_exact : ∀ accept space,
    (captureImpl accept space).drain = space.filter accept
  stable_after_change : ∀ accept before after,
    StableAcross (captureImpl accept before) accept before after

theorem capture_contract : Contract (@Cursor.capture α) where
  drain_exact := Cursor.drain_capture_exact
  stable_after_change := by
    intro accept before _after
    exact Cursor.drain_capture_exact accept before

def appendOccurrence (space : OrderedSpace α)
    (occurrence : Occurrence α) : OrderedSpace α :=
  space ++ [occurrence]

def removeFirstIdentity (identity : Nat) : OrderedSpace α → OrderedSpace α
  | [] => []
  | occurrence :: rest =>
      if occurrence.identity = identity then rest
      else occurrence :: removeFirstIdentity identity rest

theorem append_after_capture_invisible
    (accept : Occurrence α → Bool) (before : OrderedSpace α)
    (added : Occurrence α) :
    StableAcross (Cursor.capture accept before) accept before
      (appendOccurrence before added) := by
  exact Contract.stable_after_change capture_contract
    accept before (appendOccurrence before added)

theorem removal_after_capture_invisible
    (accept : Occurrence α → Bool) (before : OrderedSpace α)
    (identity : Nat) :
    StableAcross (Cursor.capture accept before) accept before
      (removeFirstIdentity identity before) := by
  exact Contract.stable_after_change capture_contract
    accept before (removeFirstIdentity identity before)

theorem values_preserve_order_and_multiplicity
    (accept : Occurrence α → Bool) (space : OrderedSpace α) :
    ((Cursor.capture accept space).drain.map Occurrence.value) =
      (space.filter accept).map Occurrence.value := by
  rw [Cursor.drain_capture_exact]

namespace Positions

/-- The logical row observation uses source coordinates, before any candidate
selection. Equal values at different coordinates remain separate rows. -/
def visible (keep : Nat → Bool) (rows : List α) : List α :=
  (rows.zipIdx.filter fun row => keep row.2).map Prod.fst

def rankBefore (keep : Nat → Bool) (position : Nat) : Nat :=
  ((List.range position).filter keep).length

/-- Project a sparse frontier without replacing its original coordinates by
candidate-list positions. Surviving coordinates become visible row ranks. -/
def project (keep : Nat → Bool) (indexed : List (α × Nat)) : List (α × Nat) :=
  indexed.filterMap fun row =>
    if keep row.2 then some (row.1, rankBefore keep row.2) else none

theorem visible_length (keep : Nat → Bool) (rows : List α) :
    (visible keep rows).length = rankBefore keep rows.length := by
  unfold visible rankBefore
  rw [List.length_map]
  have coordinates :
      ((rows.zipIdx.map Prod.snd).filter keep).length =
        (rows.zipIdx.filter fun row => keep row.2).length := by
    rw [List.filter_map, List.length_map]
    rfl
  rw [← coordinates, List.zipIdx_map_snd, ← List.range_eq_range']

/-- Coordinate translation agrees with independently filtering full rows and
only then enumerating the resulting logical observation. -/
theorem project_zipIdx (keep : Nat → Bool) (rows : List α) :
    project keep rows.zipIdx = (visible keep rows).zipIdx := by
  induction rows using List.reverseRecOn with
  | nil => rfl
  | append_singleton rows row ih =>
      cases retained : keep rows.length with
      | false =>
          simpa [project, visible, List.zipIdx_append, retained] using ih
      | true =>
          have rank : rankBefore keep rows.length =
              (rows.zipIdx.filter fun entry => keep entry.2).length := by
            simpa only [visible, List.length_map] using (visible_length keep rows).symm
          simpa [project, visible, List.zipIdx_append, retained, rank] using
            congrArg (fun before => before ++ [(row, rankBefore keep rows.length)]) ih

/-- A selected physical row and its visible rank name the same payload.
The logical observation is constructed independently by filtering full rows. -/
theorem visible_at_rank (keep : Nat → Bool) (rows : List α)
    (position : Nat) (value : α) (found : rows[position]? = some value)
    (retained : keep position = true) :
    (visible keep rows)[rankBefore keep position]? = some value := by
  obtain ⟨bound, equal⟩ := List.getElem?_eq_some_iff.mp found
  have zippedBound : position < rows.zipIdx.length := by simpa using bound
  have source : (value, position) ∈ rows.zipIdx := by
    have zipped : rows.zipIdx[position]'zippedBound = (value, position) := by
      simpa [List.getElem_zipIdx] using congrArg (fun x => (x, position)) equal
    rw [← zipped]
    exact List.getElem_mem (by simpa using bound)
  have selected : (value, rankBefore keep position) ∈ project keep rows.zipIdx := by
    apply List.mem_filterMap.mpr
    exact ⟨(value, position), source, by simp [retained]⟩
  rw [project_zipIdx] at selected
  obtain ⟨index, indexBound, pair⟩ := List.exists_mem_zipIdx'.mp
    (show ∃ entry ∈ (visible keep rows).zipIdx,
      entry = (value, rankBefore keep position) from ⟨_, selected, rfl⟩)
  have same : index = rankBefore keep position := (Prod.ext_iff.mp pair).2
  subst index
  exact List.getElem?_eq_some_iff.mpr ⟨indexBound, (Prod.ext_iff.mp pair).1⟩

/-- Payload filtering can be performed by an index before positional
projection, provided that the source coordinates remain attached. -/
theorem project_filter (keep : Nat → Bool) (candidate : α → Bool)
    (indexed : List (α × Nat)) :
    project keep (indexed.filter fun row => candidate row.1) =
      (project keep indexed).filter fun row => candidate row.1 := by
  induction indexed with
  | nil => rfl
  | cons row rest ih =>
      simp only [project] at ih
      cases accepted : candidate row.1 <;> cases retained : keep row.2 <;>
        simp [project, accepted, retained, ih]

theorem project_candidates (keep : Nat → Bool) (candidate : α → Bool) (rows : List α) :
    project keep (rows.zipIdx.filter fun row => candidate row.1) =
      ((visible keep rows).zipIdx.filter fun row => candidate row.1) := by
  rw [project_filter, project_zipIdx]

/-- Prefix admission tests original row coordinates, including when unrelated
rows have already been omitted from a sparse candidate frontier. -/
theorem zipIdx_filter_prefix (rows : List α) (ceiling start : Nat) :
    ((rows.zipIdx start).filter fun row => decide (row.2 < start + ceiling)) =
      (rows.take ceiling).zipIdx start := by
  induction ceiling generalizing rows start with
  | zero =>
      simp only [List.take_zero, List.zipIdx_nil]
      apply List.filter_eq_nil_iff.mpr
      intro row member
      have lower := List.le_snd_of_mem_zipIdx member
      simpa only [Nat.add_zero, decide_eq_true_eq] using Nat.not_lt.mpr lower
  | succ ceiling ih =>
      cases rows with
      | nil => simp
      | cons row rest =>
          have first : start < start + (ceiling + 1) := by omega
          simp only [List.zipIdx_cons, List.filter_cons, first, decide_true,
            ↓reduceIte, List.take_succ_cons]
          have shifted : start + (ceiling + 1) = (start + 1) + ceiling := by omega
          rw [shifted]
          exact congrArg (List.cons (row, start)) (ih rest (start + 1))

theorem zipIdx_filter_suffix (rows : List α) (lower start : Nat) :
    ((rows.zipIdx start).filter fun row => decide (start + lower ≤ row.2)) =
      (rows.drop lower).zipIdx (start + lower) := by
  induction lower generalizing rows start with
  | zero =>
      simp only [Nat.add_zero, List.drop_zero]
      apply List.filter_eq_self.mpr
      intro row member
      exact of_decide_eq_true (by simpa using List.le_snd_of_mem_zipIdx member)
  | succ lower ih =>
      cases rows with
      | nil => simp
      | cons row rest =>
          have first : ¬start + (lower + 1) ≤ start := by omega
          simp only [List.zipIdx_cons, List.filter_cons, first, decide_false,
            List.drop_succ_cons]
          have shifted : start + (lower + 1) = (start + 1) + lower := by omega
          rw [shifted]
          exact ih rest (start + 1)

end Positions

namespace Delivery

def Valid (keep : Nat → Bool) (rows : List α) (pending : List Nat) : Prop :=
  ∀ position ∈ pending, ∃ value, rows[position]? = some value ∧ keep position = true

/-- Separate selection and read: recover the payload at its logical rank. -/
def indirect (keep : Nat → Bool) (rows : List α) :
    List Nat → Option ((Nat × α) × List Nat)
  | [] => none
  | position :: rest => ((Positions.visible keep rows)[Positions.rankBefore keep position]?).map
      (fun value => ((Positions.rankBefore keep position, value), rest))

/-- The cursor already selected this physical occurrence. Its direct read
keeps the same logical coordinate and exact residual frontier. -/
def fused (keep : Nat → Bool) (rows : List α) :
    List Nat → Option ((Nat × α) × List Nat)
  | [] => none
  | position :: rest => rows[position]?.map
      (fun value => ((Positions.rankBefore keep position, value), rest))

theorem fused_refines (keep : Nat → Bool) (rows : List α) (pending : List Nat)
    (valid : Valid keep rows pending) :
    fused keep rows pending = indirect keep rows pending := by
  cases pending with
  | nil => rfl
  | cons position rest =>
      obtain ⟨value, found, retained⟩ := valid position (by simp)
      simp [fused, indirect, found, Positions.visible_at_rank keep rows position value found retained]

theorem duplicate_occurrences_keep_coordinates :
    fused (fun p => p != 1) ([7, 99, 7] : List Nat) [0, 2] =
      some ((0, 7), [2]) ∧
    fused (fun p => p != 1) ([7, 99, 7] : List Nat) [2] =
      some ((1, 7), []) := by decide

theorem logical_coordinate_is_not_physical :
    let rows := [7, 99, 7]
    rows[Positions.rankBefore (fun p => p != 1) 2]? = some 99 ∧
      (fused (fun p => p != 1) rows [2]).map (fun result => result.1.2) = some 7 := by
  decide

/-- A preparatory contraction, implemented independently of the logical
view's indexed filter. It retains order and duplicate payloads. -/
def compactFrom (keep : Nat → Bool) : Nat → List α → List α
  | _, [] => []
  | position, row :: rest =>
      if keep position then row :: compactFrom keep (position + 1) rest
      else compactFrom keep (position + 1) rest

private theorem compactFrom_indexed (keep : Nat → Bool) (rows : List α) (start : Nat) :
    compactFrom keep start rows =
      ((rows.zipIdx start).filter fun row => keep row.2).map Prod.fst := by
  induction rows generalizing start with
  | nil => rfl
  | cons row rest ih =>
      cases kept : keep start <;> simp [compactFrom, List.zipIdx_cons, kept, ih]

def captureAfterPreparation (keep : Nat → Bool) (rows : List α) : Nat × List α :=
  let prepared := compactFrom keep 0 rows
  (prepared.length, prepared)

theorem prepared_capture_refines (keep : Nat → Bool) (rows : List α) :
    (captureAfterPreparation keep rows).2 = Positions.visible keep rows ∧
    (captureAfterPreparation keep rows).1 = (Positions.visible keep rows).length := by
  have prepared : compactFrom keep 0 rows = Positions.visible keep rows :=
    compactFrom_indexed keep rows 0
  simp [captureAfterPreparation, prepared]

theorem early_ceiling_can_refuse_fresh_cursor :
    let rows := [7, 99, 7]
    let prepared := compactFrom (fun p => p != 1) 0 rows
    rows.length > prepared.length ∧
    (captureAfterPreparation (fun p => p != 1) rows).1 = prepared.length ∧
    prepared = [7, 7] := by decide

end Delivery

namespace Canaries

def firstSeven : Occurrence Nat := ⟨0, 7⟩
def secondSeven : Occurrence Nat := ⟨1, 7⟩
def nine : Occurrence Nat := ⟨2, 9⟩
def acceptAll (_ : Occurrence Nat) : Bool := true

/-- Equal values remain two ordered occurrences. -/
theorem duplicate_values_remain_distinct_occurrences :
    (Cursor.capture acceptAll [firstSeven, secondSeven]).drain =
      [firstSeven, secondSeven] := by
  rfl

/-- A cursor captured before an append cannot see the appended occurrence. -/
theorem captured_cursor_does_not_see_append :
    (Cursor.capture acceptAll [firstSeven]).drain = [firstSeven] ∧
      (Cursor.capture acceptAll
        (appendOccurrence [firstSeven] nine)).drain = [firstSeven, nine] := by
  constructor <;> rfl

/-- Reading the live list again is not a logical-update cursor: an append
changes its observation. -/
theorem live_read_is_not_append_stable :
    (List.filter acceptAll [firstSeven]) ≠
      List.filter acceptAll (appendOccurrence [firstSeven] nine) := by
  decide

/-- A positional live read is also invalidated by removal before its current
position; the retained cursor still owns the pending occurrence. -/
theorem live_position_is_not_removal_stable :
    ([firstSeven, nine].drop 1) ≠
      (removeFirstIdentity firstSeven.identity [firstSeven, nine]).drop 1 := by
  decide

end Canaries

#print axioms Cursor.drain_capture_exact
#print axioms Cursor.step_preserves_capture
#print axioms Cursor.step_decomposes_observation
#print axioms capture_contract
#print axioms append_after_capture_invisible
#print axioms removal_after_capture_invisible
#print axioms values_preserve_order_and_multiplicity
#print axioms Positions.visible_length
#print axioms Positions.project_zipIdx
#print axioms Positions.visible_at_rank
#print axioms Delivery.fused_refines
#print axioms Delivery.duplicate_occurrences_keep_coordinates
#print axioms Delivery.logical_coordinate_is_not_physical
#print axioms Delivery.prepared_capture_refines
#print axioms Delivery.early_ceiling_can_refuse_fresh_cursor
#print axioms Positions.project_candidates
#print axioms Positions.zipIdx_filter_prefix
#print axioms Positions.zipIdx_filter_suffix
#print axioms Canaries.duplicate_values_remain_distinct_occurrences
#print axioms Canaries.live_read_is_not_append_stable
#print axioms Canaries.live_position_is_not_removal_stable

end Mettapedia.Data.List.OrderedOccurrenceCursor
