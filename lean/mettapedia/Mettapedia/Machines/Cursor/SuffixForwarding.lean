import Mettapedia.Machines.Cursor.SharedFactor
import Mathlib.Data.List.Range
import Mathlib.Data.List.Nodup

/-!
# Checked admission of an adjacent shared suffix

The regional source program emits one own payload, then the complete payload
stream of one selected child. It performs no host action and no projection.
Admission checks actual backing bounds, completion and the adjacent payload.
The decoder is compared with that independent source program. Refusal retains
the pending program and consumer state; it does not restart a producer.

Dense chain payloads additionally have an exact constant-primitive membership
test. This avoids rebuilding an answer-count index for every suffix. General
tables require their own membership-index refinement, and source compilation
must establish that a clause belongs to this restricted regional program.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.Cursor.SuffixForwarding

open SharedFactor

universe u v
variable {Input : Type u} {Value : Type v}

structure Program (Input : Type u) (Value : Type v) where
  caller : Input
  own : Value
  child : View Input

/-- Independent ordinary answer records: the caller changes, the child's
payload order and every occurrence remain unchanged. -/
def source (backing : Array Value) (program : Program Input Value) : List (Input × Value) :=
  (program.caller, program.own) ::
    (values backing program.child).map (fun value => (program.caller, value))

def parent (program : Program Input Value) : View Input :=
  ⟨program.caller, program.child.start - 1, program.child.stop, true⟩

/-- A fixed number of scalar tests and one indexed payload comparison. The complete suffix
is never enumerated on the successful or refused admission path. -/
def admissible [DecidableEq Value] (backing : Array Value) (program : Program Input Value) : Bool :=
  decide (program.child.start ≤ program.child.stop) &&
    decide (program.child.stop = backing.size) && program.child.completed &&
    decide (0 < program.child.start) &&
    decide (backing[program.child.start - 1]? = some program.own)

def install [DecidableEq Value] (backing : Array Value) (program : Program Input Value) :
    Option (View Input) := if admissible backing program then some (parent program) else none

private def checkSequence : List (Bool × Nat) → Bool × Nat
  | [] => (true, 0)
  | (decision, charge) :: rest =>
      let later := checkSequence rest
      (decision && later.1, charge + later.2)

private theorem checkSequence_result (checks : List (Bool × Nat)) :
    (checkSequence checks).1 = (checks.map Prod.fst).all id := by
  induction checks with
  | nil => rfl
  | cons check rest ih =>
      rcases check with ⟨decision, charge⟩
      simp only [checkSequence, List.map_cons, List.all_cons, id_eq, ih]

private theorem checkSequence_work (checks : List (Bool × Nat)) :
    (checkSequence checks).2 ≤ (checks.map Prod.snd).sum := by
  induction checks with
  | nil => rfl
  | cons check rest ih =>
      rcases check with ⟨decision, charge⟩
      simp only [checkSequence, List.map_cons, List.sum_cons]
      exact Nat.add_le_add_left ih charge

/-- The counted validator executes bounded primitive checks; comparison
charges assume a bounded canonical payload key. Array lookup and comparison
are charged separately. Variable-size structural equality needs another price. -/
def checkWithWork [DecidableEq Value] (backing : Array Value) (program : Program Input Value) :
    Bool × Nat :=
  checkSequence [
    (decide (program.child.start ≤ program.child.stop), 1),
    (decide (program.child.stop = backing.size), 1),
    (program.child.completed, 1),
    (decide (0 < program.child.start), 1),
    (decide (backing[program.child.start - 1]? = some program.own), 2)]

theorem checkWithWork_result [DecidableEq Value] (backing : Array Value)
    (program : Program Input Value) : (checkWithWork backing program).1 = admissible backing program := by
  rw [checkWithWork, checkSequence_result]
  simp only [List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq,
    Bool.and_true, admissible, Bool.and_assoc]

theorem checkWithWork_bound [DecidableEq Value] (backing : Array Value)
    (program : Program Input Value) : (checkWithWork backing program).2 ≤ 6 := by
  exact checkSequence_work _

def installWithWork [DecidableEq Value] (backing : Array Value) (program : Program Input Value) :
    Option (View Input) × Nat :=
  let checked := checkWithWork backing program
  if checked.1 then (some (parent program), checked.2 + 4) else (none, checked.2)

theorem installWithWork_result [DecidableEq Value] (backing : Array Value)
    (program : Program Input Value) : (installWithWork backing program).1 = install backing program := by
  simp only [installWithWork, install, checkWithWork_result]
  split <;> rfl

theorem installWithWork_bound [DecidableEq Value] (backing : Array Value)
    (program : Program Input Value) : (installWithWork backing program).2 ≤ 10 := by
  have bound := checkWithWork_bound backing program
  dsimp only [installWithWork]
  split <;> dsimp only <;> omega

theorem admissible_iff [DecidableEq Value] (backing : Array Value) (program : Program Input Value) :
    admissible backing program = true ↔
      program.child.start ≤ program.child.stop ∧ program.child.stop = backing.size ∧
      program.child.completed = true ∧ 0 < program.child.start ∧
      backing[program.child.start - 1]? = some program.own := by
  simp [admissible, and_assoc]

theorem install_valid [DecidableEq Value] (backing : Array Value) (program : Program Input Value)
    (accepted : admissible backing program = true) : (parent program).Valid backing := by
  obtain ⟨ordered, terminal, _, positive, _⟩ := (admissible_iff backing program).mp accepted
  dsimp [View.Valid, parent]
  omega

/-- A successful checked install implements the independently specified
head-and-child rule, with the parent's caller and exact ordered occurrences. -/
theorem install_contents [DecidableEq Value] (backing : Array Value)
    (program : Program Input Value) (accepted : admissible backing program = true) :
    records backing (parent program) = source backing program := by
  obtain ⟨ordered, terminal, _, positive, payload⟩ := (admissible_iff backing program).mp accepted
  have inside : program.child.start - 1 < backing.toList.length := by
    simp only [Array.length_toList]
    omega
  have own : backing.toList[program.child.start - 1] = program.own := by
    simpa only [← Array.getElem?_toList, getElem?_pos backing.toList (program.child.start - 1) inside,
      Option.some.injEq] using payload
  have successor : program.child.start - 1 + 1 = program.child.start := by omega
  unfold records source
  rw [values_full_suffix backing (parent program) terminal,
    values_full_suffix backing program.child terminal]
  dsimp only [parent]
  rw [List.drop_eq_getElem_cons inside, successor, own, List.map_cons]

def admitOrRetain [DecidableEq Value] {clients : Nat} (state : State Input Value clients)
    (program : Program Input Value) : Option (View Input) × State Input Value clients :=
  (install state.backing program, state)

theorem refusal_retains_exact_residual [DecidableEq Value] {clients : Nat}
    (state : State Input Value clients) (program : Program Input Value)
    (refused : admissible state.backing program = false) :
    admitOrRetain state program = (none, state) := by
  simp [admitOrRetain, install, refused]

/-! ## Dense chain instance and membership index -/

def backing (size : Nat) : Array Nat := (List.range size).toArray

abbrev view (size caller : Nat) : View Nat := ⟨caller, caller, size, true⟩

/-- Independent ordered chain answers use ordinary list traversal. -/
def chainAnswers (size caller : Nat) : List (Nat × Nat) :=
  ((List.range size).drop caller).map (fun payload => (caller, payload))

theorem chain_contents (size caller : Nat) :
    records (backing size) (view size caller) = chainAnswers size caller := by
  simpa only [backing, view, chainAnswers, List.length_range] using
    suffix_contents (List.range size) caller caller

theorem chain_valid (size caller : Nat) (within : caller ≤ size) :
    (view size caller).Valid (backing size) := by
  simp [View.Valid, backing, within]

/-- The representation constructs only interval metadata. This expression
does not materialize every table's decoded answer list. -/
def views (size : Nat) : List (View Nat) := (List.range size).map (view size)

theorem views_count (size : Nat) : (views size).length = size := by simp [views]

theorem shared_payload_count (size : Nat) : (backing size).size = size := by simp [backing]

theorem every_view_decodes (size : Nat) :
    (views size).map (records (backing size)) =
      (List.range size).map (chainAnswers size) := by
  simp only [views, List.map_map, Function.comp_def, chain_contents]

/-- Dense keys index membership directly. This is an index theorem, not a
cost-free assumption about a generic set lookup. -/
def member (view : View Nat) (payload : Nat) : Bool :=
  decide (view.start ≤ payload ∧ payload < view.stop)

theorem chain_member_iff (size caller payload : Nat) (within : caller ≤ size) :
    member (view size caller) payload = true ↔
      payload ∈ values (backing size) (view size caller) := by
  rw [values_full_suffix _ _ (by simp [backing])]
  simp only [member, backing, List.toList_toArray]
  rw [decide_eq_true_eq]
  rw [List.range_eq_range', List.drop_range']
  simp only [Nat.mul_one, Nat.zero_add, List.mem_range', Nat.one_mul]
  constructor
  · rintro ⟨lower, upper⟩
    exact ⟨payload - caller, by omega, by omega⟩
  · rintro ⟨offset, upper, same⟩
    omega

def chainProgram (size caller : Nat) : Program Nat Nat :=
  ⟨caller, caller, view size (caller + 1)⟩

theorem chain_admitted (size caller : Nat) (within : caller < size) :
    install (backing size) (chainProgram size caller) = some (view size caller) := by
  have accepted : admissible (backing size) (chainProgram size caller) = true := by
    simp [admissible, chainProgram, view, backing, within, Nat.add_one_le_iff]
  simp only [install, accepted, if_true]
  rfl

theorem chain_disjoint (size caller : Nat) :
    member (view size (caller + 1)) caller = false := by
  simp [member]

/-- The dense chain stream is already duplicate-free. Set-table admission
therefore needs no deduplication pass over the child suffix. This property is
separate from the generic ordered-stream installation law. -/
theorem chain_answers_nodup (size caller : Nat) : (chainAnswers size caller).Nodup := by
  apply List.Nodup.map (fun _ _ same => congrArg Prod.snd same)
  exact List.nodup_range.drop

theorem chain_table_records_nodup (size caller : Nat) :
    (records (backing size) (view size caller)).Nodup := by
  rw [chain_contents]
  exact chain_answers_nodup size caller

theorem chain_rule (size caller : Nat) (within : caller < size) :
    chainAnswers size caller =
      (caller, caller) :: (chainAnswers size (caller + 1)).map (fun answer => (caller, answer.2)) := by
  unfold chainAnswers
  rw [List.drop_eq_getElem_cons (by simpa using within)]
  simp [List.getElem_range, List.map_map, Function.comp_def]

def allDeliveries : Nat → Nat
  | 0 => 0
  | size + 1 => (size + 1) + allDeliveries size

theorem allDeliveries_triangular (size : Nat) :
    2 * allDeliveries size = size * (size + 1) := by
  induction size with
  | zero => rfl
  | succ size ih => simp only [allDeliveries, Nat.mul_add, ih]; ring

/-- The recursive work count is the actual total output size of all source
suffixes, including the empty terminal table. -/
theorem allDeliveries_source (payloads : List Value) :
    allDeliveries payloads.length = (payloads.tails.map List.length).sum := by
  induction payloads with
  | nil => rfl
  | cons value rest ih => simp only [List.length_cons, allDeliveries, List.tails,
      List.map_cons, List.sum_cons, ih]

theorem root_length (size : Nat) : (chainAnswers size 0).length = size := by
  simp [chainAnswers]

theorem every_suffix_length (size caller : Nat) :
    (chainAnswers size caller).length = size - caller := by
  simp [chainAnswers]

/-! ## Falsifying controls -/

theorem incomplete_child_refused :
    install #[0, 1] (⟨7, 0, ⟨8, 1, 2, false⟩⟩ : Program Nat Nat) = none := by decide

theorem wrong_adjacent_payload_refused :
    install #[0, 1] (⟨7, 9, ⟨8, 1, 2, true⟩⟩ : Program Nat Nat) = none := by decide

theorem duplicate_payload_is_preserved :
    install #[7, 7] (⟨41, 7, ⟨99, 1, 2, true⟩⟩ : Program Nat Nat) =
      some ⟨41, 0, 2, true⟩ ∧
    records #[7, 7] (⟨41, 0, 2, true⟩ : View Nat) = [(41, 7), (41, 7)] := by decide

end Mettapedia.Machines.Cursor.SuffixForwarding
