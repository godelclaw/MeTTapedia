import Mettapedia.Machines.ConstraintPropagation

/-!
# Packed factor-range trails

A relational cursor keeps one current range per factor. At a variable level,
its incidence records save the parent ranges before any narrowing. Leaving
that level restores only those factors. Sorting the records and suspending
partway through narrowing do not change the restored parent.

These are laws of indexed writes and their saved values, including their
connection to the existing undo service. They do not by themselves prove
which row ranges the native intersection navigator should select.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Dynamics.RelationalRangeTrail

variable {Index Value : Type*} [DecidableEq Index]

/-- Forward indexed writes, as in the native factor-range loop. -/
def write (cells : Index → Value) : List (Index × Value) → Index → Value
  | [] => cells
  | entry :: rest => write (Function.update cells entry.1 entry.2) rest

/-- All parent values are saved before narrowing starts. -/
def capture (parent : Index → Value) (slots : List Index) : List (Index × Value) :=
  slots.map fun slot => (slot, parent slot)

theorem captured_lookup (parent current : Index → Value) (slots : List Index)
    (slot : Index) :
    write current (capture parent slots) slot =
      if slot ∈ slots then parent slot else current slot := by
  induction slots generalizing current with
  | nil => simp [capture, write]
  | cons first rest ih =>
      simp only [capture, List.map_cons, write] at ih ⊢
      rw [ih]
      by_cases later : slot ∈ rest
      · simp [later]
      · by_cases same : slot = first
        · subst slot
          simp [later]
        · simp [later, same]

theorem write_outside (current : Index → Value) (changes : List (Index × Value))
    (slot : Index) (outside : slot ∉ changes.map Prod.fst) :
    write current changes slot = current slot := by
  induction changes generalizing current with
  | nil => rfl
  | cons first rest ih =>
      simp only [List.map_cons, List.mem_cons, not_or] at outside
      simp only [write]
      rw [ih _ outside.2, Function.update_of_ne outside.1]

/-- A level restores its original parent even after an arbitrary subset of
its factors was narrowed, including a suspended prefix of the write loop. -/
theorem restore_after_narrowing (parent : Index → Value) (slots : List Index)
    (changes : List (Index × Value))
    (licensed : ∀ entry ∈ changes, entry.1 ∈ slots) :
    write (write parent changes) (capture parent slots) = parent := by
  funext slot
  rw [captured_lookup]
  by_cases present : slot ∈ slots
  · simp [present]
  · simp only [if_neg present]
    apply write_outside
    intro changed
    obtain ⟨entry, member, equal⟩ := List.mem_map.mp changed
    exact present (equal ▸ licensed entry member)

/-- Capturing the complete incidence list before a partial narrowing is
sufficient; no second snapshot is needed at a suspension boundary. -/
theorem restore_suspended_prefix (parent : Index → Value)
    (changes : List (Index × Value)) (budget : Nat) :
    write (write parent (changes.take budget))
      (capture parent (changes.map Prod.fst)) = parent := by
  apply restore_after_narrowing
  intro entry member
  exact List.mem_map.mpr ⟨entry, List.mem_of_mem_take member, rfl⟩

/-- Descendants restore their own changes before the parent's trail is
restored. Factors shared between the two levels retain the right parent. -/
theorem nested_restoration (parent : Index → Value)
    (outer inner : List (Index × Value)) :
    write
      (write (write (write parent outer) inner)
        (capture (write parent outer) (inner.map Prod.fst)))
      (capture parent (outer.map Prod.fst)) = parent := by
  rw [restore_after_narrowing (write parent outer) (inner.map Prod.fst) inner
    (fun entry member => List.mem_map.mpr ⟨entry, member, rfl⟩)]
  exact restore_after_narrowing parent (outer.map Prod.fst) outer
    (fun entry member => List.mem_map.mpr ⟨entry, member, rfl⟩)

/-- Restoring saved parent values depends on the touched cells, not the
key-dependent order of the native iterator records. -/
theorem restore_reordered (parent current : Index → Value)
    (left right : List Index) (permutation : left.Perm right) :
    write current (capture parent left) = write current (capture parent right) := by
  funext slot
  rw [captured_lookup, captured_lookup]
  simp only [permutation.mem_iff]

namespace UndoService

open Mettapedia.Machines.ConstraintPropagation

def embed (cells : Index → Value) : ServiceState Index Value Unit :=
  ⟨fun slot => some (cells slot), fun _ => [], []⟩

theorem restore_cell (cells : Index → Value) (slot : Index) (value : Value) :
    (Undo.value slot (some value)).apply (embed cells) =
      embed (Function.update cells slot value) := by
  change ServiceState.mk (Function.update (fun other => some (cells other)) slot (some value))
    (fun _ => []) [] = ServiceState.mk (fun other => some (Function.update cells slot value other))
      (fun _ => []) []
  congr 1
  funext other
  by_cases equal : other = slot <;> simp [equal]

/-- The native forward restoration loop is the existing service's rollback
of the reversed saved-value log. The service's other fields stay intact. -/
theorem rollback_reversed (current : Index → Value) (saved : List (Index × Value)) :
    rollback ((saved.map fun entry => Undo.value entry.1 (some entry.2)).reverse)
      (embed current) = embed (write current saved) := by
  induction saved generalizing current with
  | nil => rfl
  | cons first rest ih =>
      rw [List.map_cons, List.reverse_cons, rollback_append]
      change rollback ((rest.map fun entry => Undo.value entry.1 (some entry.2)).reverse)
        ((Undo.value first.1 (some first.2)).apply (embed current)) =
          embed (write (Function.update current first.1 first.2) rest)
      rw [restore_cell]
      exact ih _

end UndoService

structure Layout where
  header : Nat
  range : Nat
  iterator : Nat
  level : Nat

/-- The native allocation has one factor range, one iterator per incidence,
and one descriptor per variable. Empty iterator/level arrays keep one cell. -/
def bookmarkBytes (layout : Layout) (factors : Nat) (groups : List (List Index)) : Nat :=
  layout.header + layout.range * factors +
    layout.iterator * max groups.flatten.length 1 +
    layout.level * max groups.length 1

omit [DecidableEq Index] in
theorem bookmarkBytes_affine (layout : Layout) (factors : Nat)
    (groups : List (List Index)) :
    bookmarkBytes layout factors groups ≤
      layout.header + layout.range * factors +
        layout.iterator * (groups.flatten.length + 1) +
        layout.level * (groups.length + 1) := by
  have iterators : max groups.flatten.length 1 ≤ groups.flatten.length + 1 := by omega
  have levels : max groups.length 1 ≤ groups.length + 1 := by omega
  have iteratorBytes := Nat.mul_le_mul_left layout.iterator iterators
  have levelBytes := Nat.mul_le_mul_left layout.level levels
  dsimp [bookmarkBytes]
  omega

omit [DecidableEq Index] in
theorem incidence_bound (groups : List (List Index)) (degree : Nat)
    (bounded : ∀ group ∈ groups, group.length ≤ degree) :
    groups.flatten.length ≤ groups.length * degree := by
  induction groups with
  | nil => simp
  | cons group rest ih =>
      have first := bounded group (List.mem_cons_self)
      have remaining := ih (fun other member => bounded other (List.mem_cons_of_mem group member))
      simp only [List.flatten_cons, List.length_append, List.length_cons]
      rw [Nat.succ_mul]
      omega

omit [DecidableEq Index] in
/-- Bounded incidence degree gives a bookmark linear in factors and
variables. Relation rows and the shared prepared index are separate costs. -/
theorem bookmarkBytes_bounded_degree (layout : Layout) (factors : Nat)
    (groups : List (List Index)) (degree : Nat)
    (bounded : ∀ group ∈ groups, group.length ≤ degree) :
    bookmarkBytes layout factors groups ≤
      layout.header + layout.range * factors +
        layout.iterator * (groups.length * degree + 1) +
        layout.level * (groups.length + 1) := by
  have incidences := incidence_bound groups degree bounded
  have bytes := Nat.mul_le_mul_left layout.iterator (Nat.add_le_add_right incidences 1)
  exact (bookmarkBytes_affine layout factors groups).trans (by omega)

namespace Controls

def parent : Nat → Nat := fun slot => 10 + slot

theorem partial_narrowing_restores_untouched_and_touched_factors :
    write (write parent [(1, 21), (3, 23)]) (capture parent [1, 2, 3]) = parent := by
  apply restore_after_narrowing
  intro entry member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with equal | equal <;> subst entry <;> simp

/-- Forgetting the trail's saved range leaves a descendant's narrowed range
in the parent, excluding later sibling keys. -/
theorem omitted_restoration_loses_the_parent :
    write parent [(1, 21)] 1 ≠ parent 1 := by decide

theorem capturing_after_narrowing_is_wrong :
    let child := write parent [(1, 21)]
    write child (capture child [1]) 1 ≠ parent 1 := by decide

theorem restoring_only_the_child_keeps_the_outer_narrowing :
    let outer := write parent [(1, 21)]
    write (write outer [(1, 31)]) (capture outer [1]) 1 = 21 ∧
      write (write outer [(1, 31)]) (capture outer [1]) 1 ≠ parent 1 := by decide

theorem factor_matrices_fail_the_linear_doubling_control :
    32 * 33 > 2 * (16 * 17) := by decide

end Controls

end Mettapedia.GSLT.Dynamics.RelationalRangeTrail
