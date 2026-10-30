import Mettapedia.Algorithms.Compression.SourceFrame
import Mettapedia.Algorithms.Compression.DeferredArguments

/-!
# Source frames for lexical helper closures

Helper slots occupy a reserved prefix. Each helper's form-local variables are
rebased into a disjoint suffix before the generated factory is frozen into its
first-occurrence source inventory. The common source-frame codec reconstructs
that syntax, including repeated variable occurrences and quoted subtrees.

The unary MIL adapter receives already-entered values. Its ready and delayed
ports therefore denote the same incoming values even when the helper body has
effects, choice or failure. This does not admit arbitrary argument computations
as values, prove the source-role admission checker, or verify a C evaluator.
-/

set_option autoImplicit false

namespace Mettapedia.Algorithms.Compression.SourceClosureFrames

open SourceFrame

def rebase (offset : Nat) (source : Term Nat) : Term Nat :=
  rename (offset + ·) source

def unbase (offset index : Nat) : Option Nat :=
  if offset ≤ index then some (index - offset) else none

theorem restore_rebased (offset : Nat) (source : Term Nat) :
    restore (unbase offset) (rebase offset source) = some source := by
  have result := restore_rename (offset + ·) (unbase offset) id source (by
    intro value _
    simp [unbase])
  simpa only [rebase, rename_id] using result

theorem reserved_prefix_disjoint (count offset position helper : Nat)
    (reserved : helper < count) (afterPrefix : count ≤ offset) :
    offset + position ≠ helper := by omega

theorem rebased_alias_iff (offset left right : Nat) :
    offset + left = offset + right ↔ left = right := by omega

theorem separate_blocks (first second width position other : Nat)
    (inside : position < width) (ordered : first + width ≤ second) :
    first + position ≠ second + other := by omega

theorem rebased_occurrences (offset : Nat) (source : Term Nat) :
    occurrences (rebase offset source) = (occurrences source).map (offset + ·) :=
  occurrences_rename _ _

/-- Freezing removes unused generated names while preserving source identity
relationships. This concerns source variables, not alpha-equivalence of arbitrary
binding calculi or equality of the program's outputs. -/
theorem restore_canonical_rebased (offset : Nat) (source : Term Nat) :
    restore (fun index => (inventory (rebase offset source))[index]?)
      (freeze (rebase offset source)) = some (rebase offset source) :=
  restore_freeze _

theorem restore_canonical_fresh (offset : Nat) (source : Term Nat) (fresh : Nat → Nat) :
    restore (fun index => ((inventory (rebase offset source)).map fresh)[index]?)
      (freeze (rebase offset source)) = some (rename fresh (rebase offset source)) :=
  restore_fresh _ _

def port {m : Type → Type} [Monad m] {α : Type}
    (delayed : Bool) (value : α) : DeferredArguments.Argument m α :=
  if delayed then .delayed (fun _ => pure value) else .ready value

theorem read_port {m : Type → Type} [Monad m] {α : Type} (delayed : Bool) (value : α) :
    DeferredArguments.read (port (m := m) delayed value) = pure value := by
  cases delayed <;> rfl

def adapt {m : Type → Type} [Monad m] {α β : Type} {arity : Nat}
    (delayed : Fin arity → Bool) (values : Fin arity → α)
    (body : (Fin arity → m α) → m β) : m β := do
  let arguments ← ValueArguments.collect arity (fun index => pure (port (m := m) (delayed index) (values index)))
  body (fun index => DeferredArguments.read (arguments index))

theorem adapt_preserves {m : Type → Type} [Monad m] [LawfulMonad m] {α β : Type} {arity : Nat}
    (delayed : Fin arity → Bool) (values : Fin arity → α)
    (body : (Fin arity → m α) → m β) :
    adapt delayed values body = body (fun index => pure (values index)) := by
  simp only [adapt, ValueArguments.collect_pure, pure_bind, read_port]

namespace Controls

def aliased : Term Nat := .expr [.var 0, .var 1, .var 0]

theorem distinct_locals_survive_rebasing :
    occurrences (rebase 3 aliased) = [3, 4, 3] := by
  simp [rebased_occurrences, aliased, occurrences, occurrencesList]

theorem zero_offset_confuses_a_reserved_lookup :
    restore (fun index => (["helper", "local"] : List String)[index]?)
        (rebase 0 (.var 0)) = some (.var "helper") ∧
      restore (fun index => (["helper", "local"] : List String)[index]?)
        (rebase 1 (.var 0)) = some (.var "local") := by
  constructor <;> simp [rebase, rename, restore]

theorem malformed_inventory_cannot_restore_a_reference :
    restore (fun index => ([7] : List Nat)[index]?) (.var 1) = none := by rfl

theorem entered_adapter_preserves_duplicate_answers :
    adapt (fun _ : Fin 1 => true) (fun _ => 4)
      (fun arguments : (Fin 1 → List Nat) => do
        let value ← arguments 0
        [value, value + 1, value]) = [4, 5, 4] := by
  rw [adapt_preserves]
  rfl

theorem entered_adapter_preserves_body_effects :
    (adapt (fun _ : Fin 1 => true) (fun _ => 4)
      (fun arguments : Fin 1 → StateM Nat Nat => do
        let first ← arguments 0
        modify (· + 1)
        let second ← arguments 0
        pure (first + second))).run 0 = (8, 1) := by
  rw [adapt_preserves]
  rfl

theorem entered_adapter_preserves_failure :
    adapt (fun _ : Fin 1 => false) (fun _ => 4)
      (fun _ : Fin 1 → List Nat => ([] : List Nat)) = [] := by
  rw [adapt_preserves]

end Controls

#print axioms restore_rebased
#print axioms reserved_prefix_disjoint
#print axioms rebased_alias_iff
#print axioms separate_blocks
#print axioms rebased_occurrences
#print axioms restore_canonical_rebased
#print axioms restore_canonical_fresh
#print axioms read_port
#print axioms adapt_preserves
#print axioms Controls.distinct_locals_survive_rebasing
#print axioms Controls.zero_offset_confuses_a_reserved_lookup
#print axioms Controls.malformed_inventory_cannot_restore_a_reference
#print axioms Controls.entered_adapter_preserves_duplicate_answers
#print axioms Controls.entered_adapter_preserves_body_effects
#print axioms Controls.entered_adapter_preserves_failure

end Mettapedia.Algorithms.Compression.SourceClosureFrames
