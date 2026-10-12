import Mettapedia.Machines.Cursor.SuffixForwarding

/-!
# Forwarded table stores

The native table machine keeps, for each table, a vector of its own answers
and at most one edge: the answers of a complete child follow the first
`split` own answers, rebased to the table's input. A reader walks a stack of
frames; reading past the own answers of a complete table into a final edge
replaces that table's frame. Ordinary set tables keep one membership index
along a chain of forwarding tables, and each table owns the positions below
its extent.

* `Table.seq` is the delivered sequence. `drain` reads exactly the denoted
  sequence of a frame stack, and a table is read in `Table.size` steps; for a
  chain whose root alone is read this is linear (`chain_size`).
* `Index.appendAll` installs an edge. When the child owns the index's last
  position and the parent's own answers avoid the child's, the extended index
  describes the parent and still describes the child (`install_describes`).
* `mergeRound` merges a generator round in which a tail call forwarded a
  complete child. It delivers exactly the flat replay merge, whether the edge
  is installed or its answers are added as own answers (`mergeRound_seq`).

The round's answers at the marker are the child's answers unchanged. That is
what the native admission establishes: the call is the generator's last
action, its destination is the generator's unbound answer variable, no
delayed goal or type obligation waits on it, and both inputs are ground. Here
it is a premise, not a theorem about the machine.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.Cursor.ForwardedTableStore

universe u v
variable {Value : Type u}

/-- A table: its own answers, and possibly a complete child whose answers it
delivers after its first `split` own answers. -/
inductive Table (Value : Type u) where
  | flat (own : List Value) (complete : Bool)
  | forward (own : List Value) (split : Nat) (child : Table Value) (complete : Bool)
  deriving DecidableEq

namespace Table

def complete : Table Value → Bool
  | flat _ complete => complete
  | forward _ _ _ complete => complete

/-- The delivered answer sequence. -/
def seq : Table Value → List Value
  | flat own _ => own
  | forward own split child _ => own.take split ++ child.seq ++ own.drop split

/-- Reader steps: one per own answer, one to leave each table and one to enter
each edge. -/
def size : Table Value → Nat
  | flat own _ => own.length + 1
  | forward own _ child _ => own.length + child.size + 2

/-- The maintained answer count: own answers plus the child's count. A count
observer of a complete table reads it in place of the answers. -/
def total : Table Value → Nat
  | flat own _ => own.length
  | forward own _ child _ => own.length + child.total

/-- Every edge follows existing own answers. -/
inductive Valid : Table Value → Prop
  | flat (own : List Value) (complete : Bool) : Valid (flat own complete)
  | forward (own : List Value) (split : Nat) (child : Table Value) (complete : Bool) :
      split ≤ own.length → Valid child → Valid (forward own split child complete)

theorem total_eq_length (table : Table Value) (valid : table.Valid) :
    table.total = table.seq.length := by
  induction valid with
  | flat own complete => rfl
  | forward own split child complete within _ ih =>
      simp only [total, seq, List.length_append, List.length_take, List.length_drop, ih]
      omega

end Table

/-! ## The reader -/

/-- A reader frame: the table, its next own answer, and whether its edge has
been entered. -/
structure Frame (Value : Type u) where
  table : Table Value
  next : Nat
  taken : Bool

namespace Frame

/-- What a frame has still to deliver. -/
def rest : Frame Value → List Value
  | ⟨.flat own _, next, _⟩ => own.drop next
  | ⟨.forward own split child _, next, false⟩ =>
      (own.take split).drop next ++ child.seq ++ own.drop split
  | ⟨.forward own _ _ _, next, true⟩ => own.drop next

def measure : Frame Value → Nat
  | ⟨.flat own _, next, _⟩ => own.length - next + 1
  | ⟨.forward own _ child _, next, false⟩ => own.length - next + child.size + 2
  | ⟨.forward own _ _ _, next, true⟩ => own.length - next + 1

inductive Valid : Frame Value → Prop
  | flat (own : List Value) (complete : Bool) (next : Nat) (taken : Bool) :
      Valid ⟨.flat own complete, next, taken⟩
  | pending (own : List Value) (split : Nat) (child : Table Value) (complete : Bool) (next : Nat) :
      split ≤ own.length → next ≤ split → child.Valid →
      Valid ⟨.forward own split child complete, next, false⟩
  | entered (own : List Value) (split : Nat) (child : Table Value) (complete : Bool) (next : Nat) :
      Valid ⟨.forward own split child complete, next, true⟩

end Frame

/-- One iteration of the native reader loop: a delivered value, a silent move
(leaving a table or entering an edge), or the end. -/
def step : List (Frame Value) → Option (Option Value × List (Frame Value))
  | [] => none
  | ⟨.flat own complete, next, taken⟩ :: rest =>
      if h : next < own.length then
        some (some own[next], ⟨.flat own complete, next + 1, taken⟩ :: rest)
      else some (none, rest)
  | ⟨.forward own split child complete, next, taken⟩ :: rest =>
      if taken = false ∧ next = split then
        if complete = true ∧ split = own.length then
          some (none, ⟨child, 0, false⟩ :: rest)
        else
          some (none, ⟨child, 0, false⟩ :: ⟨.forward own split child complete, next, true⟩ :: rest)
      else if h : next < own.length then
        some (some own[next], ⟨.forward own split child complete, next + 1, taken⟩ :: rest)
      else some (none, rest)

def rest (frames : List (Frame Value)) : List Value := (frames.map Frame.rest).flatten

def measure (frames : List (Frame Value)) : Nat := (frames.map Frame.measure).sum

theorem fresh_rest (table : Table Value) : Frame.rest ⟨table, 0, false⟩ = table.seq := by
  cases table <;> simp [Frame.rest, Table.seq]

theorem fresh_measure (table : Table Value) : Frame.measure ⟨table, 0, false⟩ = table.size := by
  cases table <;> simp [Frame.measure, Table.size]

theorem fresh_valid (table : Table Value) (valid : table.Valid) : Frame.Valid ⟨table, 0, false⟩ := by
  cases valid with
  | flat own complete => exact .flat own complete 0 false
  | forward own split child complete within childValid =>
      exact .pending own split child complete 0 within (Nat.zero_le _) childValid

theorem rest_cons (frame : Frame Value) (tail : List (Frame Value)) :
    rest (frame :: tail) = frame.rest ++ rest tail := by
  simp [rest]

theorem measure_cons (frame : Frame Value) (tail : List (Frame Value)) :
    measure (frame :: tail) = frame.measure + measure tail := by
  simp [measure]

/-! The reader's cases, one equation each. -/

theorem step_flat_yield (own : List Value) (complete : Bool) (next : Nat) (taken : Bool)
    (tail : List (Frame Value)) (h : next < own.length) :
    step (⟨.flat own complete, next, taken⟩ :: tail) =
      some (some own[next], ⟨.flat own complete, next + 1, taken⟩ :: tail) := by
  simp [step, h]

theorem step_flat_end (own : List Value) (complete : Bool) (next : Nat) (taken : Bool)
    (tail : List (Frame Value)) (h : ¬next < own.length) :
    step (⟨.flat own complete, next, taken⟩ :: tail) = some (none, tail) := by
  simp [step, h]

theorem step_edge_replace (own : List Value) (split : Nat) (child : Table Value) (complete : Bool)
    (tail : List (Frame Value)) (finished : complete = true) (ends : split = own.length) :
    step (⟨.forward own split child complete, split, false⟩ :: tail) =
      some (none, ⟨child, 0, false⟩ :: tail) := by
  simp [step, finished, ends]

theorem step_edge_push (own : List Value) (split : Nat) (child : Table Value) (complete : Bool)
    (tail : List (Frame Value)) (keeps : ¬(complete = true ∧ split = own.length)) :
    step (⟨.forward own split child complete, split, false⟩ :: tail) =
      some (none, ⟨child, 0, false⟩ :: ⟨.forward own split child complete, split, true⟩ :: tail) := by
  simp only [step, and_self, if_true, if_neg keeps]

theorem step_forward_yield (own : List Value) (split : Nat) (child : Table Value) (complete : Bool)
    (next : Nat) (taken : Bool) (tail : List (Frame Value))
    (noEdge : ¬(taken = false ∧ next = split)) (h : next < own.length) :
    step (⟨.forward own split child complete, next, taken⟩ :: tail) =
      some (some own[next], ⟨.forward own split child complete, next + 1, taken⟩ :: tail) := by
  simp only [step, if_neg noEdge, dif_pos h]

theorem step_forward_end (own : List Value) (split : Nat) (child : Table Value) (complete : Bool)
    (next : Nat) (taken : Bool) (tail : List (Frame Value))
    (noEdge : ¬(taken = false ∧ next = split)) (h : ¬next < own.length) :
    step (⟨.forward own split child complete, next, taken⟩ :: tail) = some (none, tail) := by
  simp only [step, if_neg noEdge, dif_neg h]

/-! What each frame denotes in those cases. -/

theorem rest_flat_yield (own : List Value) (complete : Bool) (next : Nat) (taken : Bool)
    (h : next < own.length) :
    Frame.rest ⟨.flat own complete, next, taken⟩ =
      own[next] :: Frame.rest ⟨.flat own complete, next + 1, taken⟩ := by
  simp only [Frame.rest]
  rw [List.drop_eq_getElem_cons h]

theorem rest_flat_end (own : List Value) (complete : Bool) (next : Nat) (taken : Bool)
    (h : ¬next < own.length) : Frame.rest ⟨.flat own complete, next, taken⟩ = [] := by
  simp [Frame.rest]; omega

theorem rest_edge (own : List Value) (split : Nat) (child : Table Value) (complete : Bool) :
    Frame.rest ⟨.forward own split child complete, split, false⟩ =
      child.seq ++ Frame.rest ⟨.forward own split child complete, split, true⟩ := by
  simp [Frame.rest]

theorem rest_entered_yield (own : List Value) (split : Nat) (child : Table Value) (complete : Bool)
    (next : Nat) (h : next < own.length) :
    Frame.rest ⟨.forward own split child complete, next, true⟩ =
      own[next] :: Frame.rest ⟨.forward own split child complete, next + 1, true⟩ := by
  simp only [Frame.rest]
  rw [List.drop_eq_getElem_cons h]

theorem rest_pending_yield (own : List Value) (split : Nat) (child : Table Value) (complete : Bool)
    (next : Nat) (before : next < split) (within : split ≤ own.length) :
    Frame.rest ⟨.forward own split child complete, next, false⟩ =
      own[next] :: Frame.rest ⟨.forward own split child complete, next + 1, false⟩ := by
  have inside : next < (own.take split).length := by simp; omega
  simp only [Frame.rest]
  rw [List.drop_eq_getElem_cons inside]
  simp [List.getElem_take]

/-- Each loop iteration preserves the denoted remainder, delivers its head
when it delivers, keeps the frames valid and strictly decreases the measure. -/
theorem step_spec (frames : List (Frame Value)) (valid : ∀ frame ∈ frames, frame.Valid) :
    match step frames with
    | none => rest frames = []
    | some (out, next) => (∀ frame ∈ next, frame.Valid) ∧ measure next < measure frames ∧
        rest frames = out.toList ++ rest next := by
  rcases frames with _ | ⟨⟨table, next, taken⟩, tail⟩
  · simp [step, rest]
  have tailValid : ∀ frame ∈ tail, frame.Valid :=
    fun frame mem => valid frame (List.mem_cons_of_mem _ mem)
  have headValid : Frame.Valid ⟨table, next, taken⟩ := valid _ (List.mem_cons_self ..)
  have consValid : ∀ (frame : Frame Value), frame.Valid → ∀ item ∈ frame :: tail, item.Valid := by
    intro frame frameValid item mem
    rcases List.mem_cons.mp mem with same | mem
    · subst same; exact frameValid
    · exact tailValid item mem
  cases table with
  | flat own complete =>
      by_cases h : next < own.length
      · rw [step_flat_yield own complete next taken tail h]
        refine ⟨consValid _ (.flat own complete (next + 1) taken), ?_, ?_⟩
        · simp only [measure_cons, Frame.measure]; omega
        · rw [rest_cons, rest_cons, rest_flat_yield own complete next taken h]; rfl
      · rw [step_flat_end own complete next taken tail h]
        refine ⟨tailValid, ?_, ?_⟩
        · simp only [measure_cons, Frame.measure]; omega
        · rw [rest_cons, rest_flat_end own complete next taken h]; rfl
  | forward own split child complete =>
      by_cases edge : taken = false ∧ next = split
      · obtain ⟨untaken, atSplit⟩ := edge
        subst untaken atSplit
        have childValid : child.Valid := by cases headValid; assumption
        have within : next ≤ own.length := by cases headValid; assumption
        by_cases ends : complete = true ∧ next = own.length
        · rw [step_edge_replace own next child complete tail ends.1 ends.2]
          refine ⟨consValid _ (fresh_valid child childValid), ?_, ?_⟩
          · rw [measure_cons, measure_cons, fresh_measure]
            simp only [Frame.measure]; omega
          · rw [rest_cons, rest_cons, rest_edge, fresh_rest]
            simp [Frame.rest, ends.2]
        · rw [step_edge_push own next child complete tail ends]
          refine ⟨?_, ?_, ?_⟩
          · intro item mem
            rcases List.mem_cons.mp mem with same | mem
            · subst same; exact fresh_valid child childValid
            · exact consValid _ (.entered own next child complete next) item mem
          · rw [measure_cons, measure_cons, measure_cons, fresh_measure]
            simp only [Frame.measure]; omega
          · rw [rest_cons, rest_cons, rest_cons, rest_edge, fresh_rest]
            simp
      · by_cases h : next < own.length
        · rw [step_forward_yield own split child complete next taken tail edge h]
          refine ⟨?_, ?_, ?_⟩
          · apply consValid
            cases taken with
            | true => exact .entered own split child complete (next + 1)
            | false =>
                cases headValid with
                | pending _ _ _ _ _ within before childValid =>
                    have : next ≠ split := fun same => edge ⟨rfl, same⟩
                    exact .pending own split child complete (next + 1) within (by omega) childValid
          · cases taken <;> simp only [measure_cons, Frame.measure] <;> omega
          · rw [rest_cons, rest_cons]
            cases taken with
            | true => rw [rest_entered_yield own split child complete next h]; rfl
            | false =>
                cases headValid with
                | pending _ _ _ _ _ within before _ =>
                    have : next ≠ split := fun same => edge ⟨rfl, same⟩
                    rw [rest_pending_yield own split child complete next (by omega) within]; rfl
        · rw [step_forward_end own split child complete next taken tail edge h]
          refine ⟨tailValid, ?_, ?_⟩
          · cases taken <;> simp only [measure_cons, Frame.measure] <;> omega
          · rw [rest_cons]
            cases taken with
            | true => simp [Frame.rest]; omega
            | false =>
                cases headValid with
                | pending _ _ _ _ _ within before _ =>
                    have : next ≠ split := fun same => edge ⟨rfl, same⟩
                    omega

/-- The native reader loop with a step allowance. -/
def drain : Nat → List (Frame Value) → List Value
  | 0, _ => []
  | fuel + 1, frames =>
      match step frames with
      | none => []
      | some (out, next) => out.toList ++ drain fuel next

/-- With as many steps as the measure, the reader delivers exactly what its
frames denote. -/
theorem drain_rest (fuel : Nat) (frames : List (Frame Value))
    (valid : ∀ frame ∈ frames, frame.Valid) (enough : measure frames ≤ fuel) :
    drain fuel frames = rest frames := by
  induction fuel generalizing frames with
  | zero =>
      cases frames with
      | nil => rfl
      | cons frame tail =>
          exfalso
          have positive : 0 < Frame.measure frame := by
            rcases frame with ⟨table, next, taken⟩
            cases table <;> cases taken <;> simp [Frame.measure]
          simp only [measure, List.map_cons, List.sum_cons] at enough
          omega
  | succ fuel ih =>
      have spec := step_spec frames valid
      simp only [drain]
      split
      · rename_i none_case
        rw [none_case] at spec
        exact spec.symm
      · rename_i out next some_case
        rw [some_case] at spec
        obtain ⟨nextValid, decreasing, unfolds⟩ := spec
        rw [unfolds, ih next nextValid (by omega)]

/-- Reading a table from its first answer delivers its whole sequence within
`Table.size` steps. -/
theorem read_table (table : Table Value) (valid : table.Valid) :
    drain table.size [⟨table, 0, false⟩] = table.seq := by
  rw [drain_rest table.size _ (by simpa using fresh_valid table valid)
    (by simp [measure, fresh_measure])]
  simp [rest, fresh_rest]

/-- A flat replay that has read `next` own answers, at most the edge's
position, continues as a frame at that position. -/
theorem resume_flat_reader (own : List Value) (split : Nat) (child : Table Value) (complete : Bool)
    (next : Nat) (before : next ≤ split) (within : split ≤ own.length) :
    Frame.rest ⟨.forward own split child complete, next, false⟩ =
      (Table.forward own split child complete).seq.drop next := by
  have short : next ≤ (own.take split).length := by simp; omega
  simp only [Frame.rest, Table.seq, List.append_assoc, List.drop_append_of_le_length short]

/-! ## Chains -/

/-- A chain of forwarding tables, root first: each table's own answer, then
its parent's table. -/
def chain : List Value → Table Value
  | [] => .flat [] true
  | value :: rest => .forward [value] 1 (chain rest) true

theorem chain_seq (values : List Value) : (chain values).seq = values := by
  induction values with
  | nil => rfl
  | cons value rest ih => simp [chain, Table.seq, ih]

theorem chain_valid (values : List Value) : (chain values).Valid := by
  induction values with
  | nil => exact .flat [] true
  | cons value rest ih => exact .forward [value] 1 _ true (by simp) ih

/-- Reading the root of a chain of `n` answers takes `3n + 1` reader steps. -/
theorem chain_size (values : List Value) : (chain values).size = 3 * values.length + 1 := by
  induction values with
  | nil => rfl
  | cons value rest ih => simp [chain, Table.size, ih]; ring

theorem read_chain (values : List Value) :
    drain (3 * values.length + 1) [⟨chain values, 0, false⟩] = values := by
  rw [← chain_size, read_table _ (chain_valid values), chain_seq]

/-! ## Rebased records

A forwarded table's records carry its own input with the child's payloads;
for one own payload this is the independent source program of the suffix
forwarding model. -/

theorem forward_single_source {Input : Type v} (backing : Array Value)
    (program : SuffixForwarding.Program Input Value) (child : Table Value) (complete : Bool)
    (payloads : child.seq = SharedFactor.values backing program.child) :
    ((Table.forward [program.own] 1 child complete).seq).map (fun value => (program.caller, value)) =
      SuffixForwarding.source backing program := by
  simp [Table.seq, SuffixForwarding.source, payloads]

/-! ## The membership index -/

/-- Each key's first position, and the next position to assign. -/
structure Index (Value : Type u) where
  first : Value → Option Nat
  next : Nat

namespace Index

/-- A table with this extent contains a value whose first position lies
below the extent. -/
def Member (index : Index Value) (extent : Nat) (value : Value) : Prop :=
  ∃ position, index.first value = some position ∧ position < extent

/-- The index describes `answers` at `extent`. -/
structure Describes (index : Index Value) (extent : Nat) (answers : List Value) : Prop where
  member_iff : ∀ value, index.Member extent value ↔ value ∈ answers
  extent_le : extent ≤ index.next
  bounded : ∀ value position, index.first value = some position → position < index.next

variable [DecidableEq Value]

def append (index : Index Value) (value : Value) : Index Value :=
  ⟨Function.update index.first value (some index.next), index.next + 1⟩

def appendAll (index : Index Value) : List Value → Index Value
  | [] => index
  | value :: rest => (index.append value).appendAll rest

theorem appendAll_next (index : Index Value) (values : List Value) :
    (index.appendAll values).next = index.next + values.length := by
  induction values generalizing index with
  | nil => rfl
  | cons value rest ih => simp [appendAll, ih, append]; omega

/-- A key absent from the index leaves every described table unchanged. -/
theorem append_keeps (index : Index Value) (extent : Nat) (answers : List Value)
    (value : Value) (describes : index.Describes extent answers) (absent : index.first value = none) :
    (index.append value).Describes extent answers := by
  refine ⟨fun key => ?_, ?_, ?_⟩
  · by_cases same : key = value
    · subst same
      constructor
      · rintro ⟨position, assigned, below⟩
        simp only [append, Function.update_self, Option.some.injEq] at assigned
        have := describes.extent_le
        omega
      · intro mem
        obtain ⟨position, found, _⟩ := (describes.member_iff key).mpr mem
        rw [absent] at found
        cases found
    · rw [← describes.member_iff key]
      simp only [Member, append, Function.update_of_ne same]
  · have := describes.extent_le
    simp only [append]
    omega
  · intro key position assigned
    by_cases same : key = value
    · subst same
      simp only [append, Function.update_self, Option.some.injEq] at assigned
      simp only [append]
      omega
    · simp only [append, Function.update_of_ne same] at assigned
      have := describes.bounded key position assigned
      simp only [append]
      omega

/-- The table owning the end gains the appended key at the new end. -/
theorem append_extends (index : Index Value) (top : List Value) (value : Value)
    (describes : index.Describes index.next top) :
    (index.append value).Describes (index.append value).next (top ++ [value]) := by
  refine ⟨fun key => ?_, le_refl _, ?_⟩
  · by_cases same : key = value
    · subst same
      simp only [Member, append, Function.update_self, Option.some.injEq, List.mem_append,
        List.mem_singleton, or_true, iff_true]
      exact ⟨index.next, rfl, Nat.lt_succ_self _⟩
    · simp only [Member, append, Function.update_of_ne same, List.mem_append,
        List.mem_singleton, same, or_false]
      rw [← describes.member_iff key]
      simp only [Member]
      constructor
      · rintro ⟨position, found, _⟩
        exact ⟨position, found, describes.bounded key position found⟩
      · rintro ⟨position, found, below⟩
        exact ⟨position, found, Nat.lt_succ_of_lt below⟩
  · intro key position assigned
    by_cases same : key = value
    · subst same
      simp only [append, Function.update_self, Option.some.injEq] at assigned
      simp only [append]
      omega
    · simp only [append, Function.update_of_ne same] at assigned
      have := describes.bounded key position assigned
      simp only [append]
      omega

omit [DecidableEq Value] in
/-- A described key has a position; a key avoiding the table owning the end
has none. -/
theorem absent_of_avoid (index : Index Value) (top : List Value) (value : Value)
    (describes : index.Describes index.next top) (avoid : value ∉ top) : index.first value = none := by
  cases found : index.first value with
  | none => rfl
  | some position =>
      exact absurd ((describes.member_iff value).mp
        ⟨position, found, describes.bounded value position found⟩) avoid

/-- Appending distinct keys that avoid the table owning the end extends that
table and leaves every table at a lower extent described. -/
theorem appendAll_describes (index : Index Value) (extent : Nat) (lower top own : List Value)
    (keeps : index.Describes extent lower) (owns : index.Describes index.next top)
    (distinct : own.Nodup) (avoid : ∀ value ∈ own, value ∉ top) :
    (index.appendAll own).Describes extent lower ∧
      (index.appendAll own).Describes (index.appendAll own).next (top ++ own) := by
  induction own generalizing index top with
  | nil => simpa [appendAll] using ⟨keeps, owns⟩
  | cons value rest ih =>
      have absent := absent_of_avoid index top value owns (avoid value (by simp))
      have restAvoid : ∀ key ∈ rest, key ∉ top ++ [value] := by
        intro key mem inside
        simp only [List.mem_append, List.mem_singleton] at inside
        rcases inside with inTop | same
        · exact avoid key (by simp [mem]) inTop
        · subst same; exact (List.nodup_cons.mp distinct).1 mem
      have step := ih (index.append value) (top ++ [value])
        (append_keeps index extent lower value keeps absent)
        (append_extends index top value owns) (List.nodup_cons.mp distinct).2 restAvoid
      simpa [appendAll, List.append_assoc] using step

/-- Installing an edge: the parent's own answers extend the child's index at
its end. When they are distinct and avoid the child's answers, the extended
index describes the parent's delivered set at the new end and still describes
the child at its extent. -/
theorem install_describes (index : Index Value) (child own : List Value)
    (describes : index.Describes index.next child) (distinct : own.Nodup)
    (avoid : ∀ value ∈ own, value ∉ child) :
    (index.appendAll own).Describes (index.appendAll own).next (child ++ own) ∧
      (index.appendAll own).Describes index.next child := by
  obtain ⟨keeps, extends_⟩ :=
    appendAll_describes index index.next child child own describes describes distinct avoid
  exact ⟨extends_, keeps⟩

end Index

/-! ## Merging a round with a forwarded edge -/

section Merge

variable [DecidableEq Value]

/-- The flat replay merge of an ordinary table: each value not yet present is
appended, in arrival order. -/
def flatMerge (answers : List Value) : List Value → List Value
  | [] => answers
  | value :: rest => flatMerge (if value ∈ answers then answers else answers ++ [value]) rest

theorem flatMerge_append (answers first second : List Value) :
    flatMerge answers (first ++ second) = flatMerge (flatMerge answers first) second := by
  induction first generalizing answers with
  | nil => rfl
  | cons value rest ih => simp only [List.cons_append, flatMerge, ih]

/-- Values that are distinct and new are appended unchanged. -/
theorem flatMerge_fresh (answers values : List Value) (distinct : values.Nodup)
    (fresh : ∀ value ∈ values, value ∉ answers) : flatMerge answers values = answers ++ values := by
  induction values generalizing answers with
  | nil => simp [flatMerge]
  | cons value rest ih =>
      have absent : value ∉ answers := fresh value (by simp)
      simp only [flatMerge, absent, if_false]
      rw [ih _ (List.nodup_cons.mp distinct).2]
      · simp
      · intro key mem inside
        simp only [List.mem_append, List.mem_singleton] at inside
        rcases inside with inAnswers | same
        · exact fresh key (by simp [mem]) inAnswers
        · subst same; exact (List.nodup_cons.mp distinct).1 mem

namespace Table

/-- Retains an own answer the table does not yet deliver. -/
def addOwn (table : Table Value) (value : Value) : Table Value :=
  if value ∈ table.seq then table
  else match table with
    | flat own complete => flat (own ++ [value]) complete
    | forward own split child complete => forward (own ++ [value]) split child complete

def addAll (table : Table Value) : List Value → Table Value
  | [] => table
  | value :: rest => (table.addOwn value).addAll rest

theorem addOwn_valid (table : Table Value) (value : Value) (valid : table.Valid) :
    (table.addOwn value).Valid := by
  unfold addOwn
  split
  · exact valid
  · cases valid with
    | flat own complete => exact .flat _ complete
    | forward own split child complete within childValid =>
        exact .forward _ split child complete (by simp; omega) childValid

theorem addOwn_seq (table : Table Value) (value : Value) (valid : table.Valid) :
    (table.addOwn value).seq = if value ∈ table.seq then table.seq else table.seq ++ [value] := by
  unfold addOwn
  split
  · rfl
  · cases valid with
    | flat own complete => simp [seq]
    | forward own split child complete within _ =>
        simp only [seq, List.take_append_of_le_length within,
          List.drop_append_of_le_length within, List.append_assoc]

theorem addAll_valid (table : Table Value) (values : List Value) (valid : table.Valid) :
    (table.addAll values).Valid := by
  induction values generalizing table with
  | nil => exact valid
  | cons value rest ih => exact ih _ (addOwn_valid table value valid)

/-- Adding answers one by one delivers the flat merge. -/
theorem addAll_seq (table : Table Value) (values : List Value) (valid : table.Valid) :
    (table.addAll values).seq = flatMerge table.seq values := by
  induction values generalizing table with
  | nil => rfl
  | cons value rest ih =>
      simp only [addAll, flatMerge]
      rw [ih _ (addOwn_valid table value valid), addOwn_seq table value valid]

/-- The edge a round forwarded. It is installed when the table has no edge,
the child is complete and no answer of the table is one of the child's; then
the child's answers follow the table's present own answers. Otherwise the
child's answers are added as own answers. -/
def forwardTo (table child : Table Value) : Table Value :=
  match table with
  | flat own complete =>
      if child.complete = true ∧ ∀ value ∈ own, value ∉ child.seq then
        forward own own.length child complete
      else table.addAll child.seq
  | forward .. => table.addAll child.seq

theorem forwardTo_valid (table child : Table Value) (valid : table.Valid) (childValid : child.Valid) :
    (table.forwardTo child).Valid := by
  cases table with
  | flat own complete =>
      simp only [forwardTo]
      by_cases admitted : child.complete = true ∧ ∀ value ∈ own, value ∉ child.seq
      · rw [if_pos admitted]
        exact .forward own own.length child complete (le_refl _) childValid
      · rw [if_neg admitted]
        exact addAll_valid _ _ valid
  | forward own split grandchild complete =>
      exact addAll_valid _ _ valid

/-- Forwarding delivers the flat merge of the child's answers, installed or
not, for a set table whose child delivers distinct answers. -/
theorem forwardTo_seq (table child : Table Value) (valid : table.Valid)
    (distinct : child.seq.Nodup) :
    (table.forwardTo child).seq = flatMerge table.seq child.seq := by
  cases table with
  | flat own complete =>
      simp only [forwardTo]
      by_cases admitted : child.complete = true ∧ ∀ value ∈ own, value ∉ child.seq
      · rw [if_pos admitted]
        show (forward own own.length child complete).seq = flatMerge own child.seq
        rw [flatMerge_fresh own child.seq distinct (fun value mem inOwn =>
          admitted.2 value inOwn mem)]
        simp [seq]
      · rw [if_neg admitted]
        exact addAll_seq _ _ valid
  | forward own split grandchild complete => exact addAll_seq _ _ valid

end Table

/-- A generator round: answers before a forwarded tail call, the forwarded
complete child, and answers after it. -/
def mergeRound (table : Table Value) (before : List Value) (child : Table Value)
    (after : List Value) : Table Value :=
  ((table.addAll before).forwardTo child).addAll after

/-- The forwarded merge delivers exactly the flat replay merge of the round in
which the child's answers stand at the marker. -/
theorem mergeRound_seq (table child : Table Value) (before after : List Value)
    (valid : table.Valid) (childValid : child.Valid) (distinct : child.seq.Nodup) :
    (mergeRound table before child after).seq =
      flatMerge table.seq (before ++ child.seq ++ after) := by
  have added := Table.addAll_valid table before valid
  unfold mergeRound
  rw [Table.addAll_seq _ _ (Table.forwardTo_valid _ child added childValid),
    Table.forwardTo_seq _ child added distinct, Table.addAll_seq _ _ valid,
    flatMerge_append, flatMerge_append]

end Merge

/-! ## Controls -/

/-- Concatenating overlapping answers duplicates one; the flat merge keeps it
once. Installing an edge therefore requires own answers to avoid the child's. -/
theorem overlap_needs_refusal :
    (Table.forward [0] 1 (Table.flat [0] true) true).seq = [0, 0] ∧
      flatMerge [0] [0] = ([0] : List Nat) := by decide

theorem overlap_refused :
    (Table.forwardTo (Table.flat [0] true) (Table.flat [0, 1] true)).seq = ([0, 1] : List Nat) := by
  decide

/-- A reader that replaced the frame of a table which later gains an own
answer misses it; a reader keeping the frame delivers it. Replacement is
therefore restricted to complete tables. -/
theorem replacement_needs_completion :
    drain 10 [⟨Table.flat [1] true, 0, false⟩] = [1] ∧
      drain 10 [⟨Table.flat [1] true, 0, false⟩,
        ⟨Table.forward [0, 2] 1 (Table.flat [1] true) false, 1, true⟩] = ([1, 2] : List Nat) := by
  decide

/-- A second table extending an index past another table's end would count
that table's own answer as its own: after a first parent appends `1` to the
child's index, a second parent appending `2` does not describe its answers
`[0, 2]`. -/
theorem shared_end_is_required :
    let child : Index Nat := ⟨fun key => if key = 0 then some 0 else none, 1⟩
    let second := (child.append 1).append 2
    ¬ second.Describes second.next [0, 2] := by
  intro child second describes
  have member : second.Member second.next 1 :=
    ⟨1, by simp [second, child, Index.append, Function.update], by simp [second, child, Index.append]⟩
  have := (describes.member_iff 1).mp member
  simp at this

/-- An admitted edge: the child's answers follow the table's own. -/
theorem install_control :
    Table.forwardTo (Table.flat [5] true) (Table.flat [6, 7] true) =
        Table.forward [5] 1 (Table.flat [6, 7] true) true ∧
      (Table.forwardTo (Table.flat [5] true) (Table.flat [6, 7] true)).seq = ([5, 6, 7] : List Nat) := by
  decide

/-- An incomplete child is expanded, never installed. -/
theorem incomplete_child_expanded :
    Table.forwardTo (Table.flat [5] true) (Table.flat [6, 7] false) =
      (Table.flat [5, 6, 7] true : Table Nat) := by
  decide

/-! ## The counting policy

A table without an edge counts its answers afresh at each merge while it is
small. At or above the threshold it is counted at most twice more, and then
keeps a persistent index, built once from its answers. Over any run the
counting work is the rounds' answers plus a constant per merge plus three
times the final size. -/

/-- A table's merge state: its size, counted merges at index size, and whether
it keeps an index. -/
structure MergeState where
  size : Nat
  counted : Nat
  indexed : Bool

/-- One merge of `round` answers that adds `added` of them: the new state
and the counting work. -/
def mergeStep (threshold : Nat) (state : MergeState) (round added : Nat) : MergeState × Nat :=
  if state.indexed then (⟨state.size + added, state.counted, true⟩, round)
  else if state.size + round < threshold then
    (⟨state.size + added, state.counted, false⟩, state.size + round)
  else if state.counted < 2 then
    (⟨state.size + added, state.counted + 1, false⟩, state.size + round)
  else (⟨state.size + added, state.counted, true⟩, state.size + round)

/-- A run of merges, each a round size and the answers it added. -/
def mergeRun (threshold : Nat) : MergeState → List (Nat × Nat) → MergeState × Nat
  | state, [] => (state, 0)
  | state, (round, added) :: rest =>
      let first := mergeStep threshold state round added
      let later := mergeRun threshold first.1 rest
      (later.1, first.2 + later.2)

theorem mergeRun_size (threshold : Nat) (state : MergeState) (rounds : List (Nat × Nat)) :
    (mergeRun threshold state rounds).1.size = state.size + (rounds.map Prod.snd).sum := by
  induction rounds generalizing state with
  | nil => simp [mergeRun]
  | cons merge rest ih =>
      rcases merge with ⟨round, added⟩
      simp only [mergeRun, List.map_cons, List.sum_cons]
      rw [ih]
      unfold mergeStep
      split <;> (try split) <;> (try split) <;> simp <;> omega

/-- Size-proportional countings still allowed: the counted merges left at
index size and the build, none once indexed. -/
def MergeState.budget (state : MergeState) : Nat :=
  if state.indexed then 0 else 3 - state.counted

theorem mergeRun_size_ge (threshold : Nat) (state : MergeState) (rounds : List (Nat × Nat)) :
    state.size ≤ (mergeRun threshold state rounds).1.size := by
  rw [mergeRun_size]; omega

theorem mergeStep_size_ge (threshold : Nat) (state : MergeState) (round added : Nat) :
    state.size ≤ (mergeStep threshold state round added).1.size := by
  unfold mergeStep
  split <;> (try split) <;> (try split) <;> simp

theorem mergeStep_valid (threshold : Nat) (state : MergeState) (round added : Nat)
    (valid : state.indexed = false → state.counted ≤ 2) :
    (mergeStep threshold state round added).1.indexed = false →
      (mergeStep threshold state round added).1.counted ≤ 2 := by
  unfold mergeStep
  by_cases indexed : state.indexed = true
  · simp [indexed]
  · have notIndexed : state.indexed = false := by simpa using indexed
    have counted := valid notIndexed
    by_cases small : state.size + round < threshold
    · simp [notIndexed, small, counted]
    · by_cases again : state.counted < 2
      · simp [notIndexed, small, again]; omega
      · simp [notIndexed, small, again]

/-- One merge spends at most its round and the threshold, plus one size per
budget unit it uses. -/
theorem mergeStep_key (threshold : Nat) (state : MergeState) (round added final : Nat)
    (valid : state.indexed = false → state.counted ≤ 2) (grow : state.size ≤ final) :
    (mergeStep threshold state round added).2 +
        (mergeStep threshold state round added).1.budget * final ≤
      round + threshold + state.budget * final := by
  unfold mergeStep MergeState.budget
  by_cases indexed : state.indexed = true
  · simp [indexed]
  · have notIndexed : state.indexed = false := by simpa using indexed
    have counted := valid notIndexed
    by_cases small : state.size + round < threshold
    · simp only [notIndexed, small, if_true, Bool.false_eq_true, if_false]
      generalize (3 - state.counted) * final = budget
      omega
    · have cases : state.counted = 0 ∨ state.counted = 1 ∨ state.counted = 2 := by omega
      rcases cases with zero | one | two
      · simp [notIndexed, small, zero]; omega
      · simp [notIndexed, small, one]; omega
      · simp [notIndexed, small, two]; omega

/-- The amortized bound: over any run, counting work is at most the rounds'
answers, the threshold per merge, and one final size per budget unit. -/
theorem mergeRun_work (threshold : Nat) (state : MergeState) (rounds : List (Nat × Nat))
    (valid : state.indexed = false → state.counted ≤ 2) :
    (mergeRun threshold state rounds).2 ≤
      (rounds.map Prod.fst).sum + threshold * rounds.length +
        state.budget * (mergeRun threshold state rounds).1.size := by
  induction rounds generalizing state with
  | nil => simp [mergeRun]
  | cons merge rest ih =>
      rcases merge with ⟨round, added⟩
      have later := ih (mergeStep threshold state round added).1
        (mergeStep_valid threshold state round added valid)
      have grow : state.size ≤
          (mergeRun threshold (mergeStep threshold state round added).1 rest).1.size :=
        le_trans (mergeStep_size_ge threshold state round added) (mergeRun_size_ge _ _ _)
      have key := mergeStep_key threshold state round added
        (mergeRun threshold (mergeStep threshold state round added).1 rest).1.size valid grow
      simp only [mergeRun, List.map_cons, List.sum_cons, List.length_cons]
      nlinarith [later, key]

/-- A table that keeps merging single answers past the threshold is counted
twice at that size and then indexed. -/
theorem counted_twice_then_indexed :
    (mergeRun 2 ⟨2, 0, false⟩ [(1, 1), (1, 1), (1, 1), (1, 1)]).1.indexed = true := by
  decide

end Mettapedia.Machines.Cursor.ForwardedTableStore
