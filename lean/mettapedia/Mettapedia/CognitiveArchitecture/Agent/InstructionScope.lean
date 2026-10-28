import Mathlib.Data.List.Basic

/-!
# Instruction inheritance by key

Scope layers are supplied nearest-first after ancestor validation. Resolving
one key keeps the provenance of its first definition; a nearer layer that
defines other keys does not erase inherited values. This is the pure policy
used by the agent instruction resolver. Filesystem discovery, parsing and
revision-consistent capture are separate obligations (see `ContextEpoch`).
-/

namespace Mettapedia.CognitiveArchitecture.Agent.InstructionScope

variable {Key Value Directory : Type*} [DecidableEq Key]

def lookup (key : Key) : List (Key × Value) → Option Value
  | [] => none
  | (name, value) :: rest => if key = name then some value else lookup key rest

structure Scope (Directory Key Value : Type*) where
  directory : Directory
  rules : List (Key × Value)

def resolve (key : Key) : List (Scope Directory Key Value) → Option (Directory × Value)
  | [] => none
  | layer :: outer =>
      match lookup key layer.rules with
      | some value => some (layer.directory, value)
      | none => resolve key outer

@[simp] theorem resolve_empty (key : Key) :
    resolve (Directory := Directory) (Value := Value) key [] = none := rfl

theorem nearest_definition (key : Key) (layer : Scope Directory Key Value)
    (outer : List (Scope Directory Key Value)) (value : Value)
    (defined : lookup key layer.rules = some value) :
    resolve key (layer :: outer) = some (layer.directory, value) := by
  simp [resolve, defined]

theorem missing_key_inherits (key : Key) (layer : Scope Directory Key Value)
    (outer : List (Scope Directory Key Value))
    (missing : lookup key layer.rules = none) :
    resolve key (layer :: outer) = resolve key outer := by
  simp [resolve, missing]

theorem outer_cannot_override (key : Key) (layer : Scope Directory Key Value)
    (first second : List (Scope Directory Key Value)) (value : Value)
    (defined : lookup key layer.rules = some value) :
    resolve key (layer :: first) = resolve key (layer :: second) := by
  simp [resolve, defined]

/-- Absence of a definition is distinct from a present value that itself
represents absence. A raw missing-value sentinel cannot replace this distinction. -/
theorem present_none_is_a_definition (key : Key) (directory : Directory)
    (outer : List (Scope Directory Key (Option Value))) :
    resolve key (⟨directory, [(key, none)]⟩ :: outer) = some (directory, none) := by
  simp [resolve, lookup]

/-- Extending the ancestor chain is a fallback, not a replacement of existing
per-key decisions. -/
theorem resolve_append (key : Key) (inner outer : List (Scope Directory Key Value)) :
    resolve key (inner ++ outer) =
      (resolve key inner).orElse (fun _ => resolve key outer) := by
  induction inner with
  | nil => rfl
  | cons layer rest ih =>
      cases found : lookup key layer.rules <;> simp [resolve, found, ih]

theorem extension_preserves_resolved (key : Key)
    (inner outer : List (Scope Directory Key Value)) (result : Directory × Value)
    (found : resolve key inner = some result) :
    resolve key (inner ++ outer) = some result := by
  rw [resolve_append, found]
  rfl

/-- Every successful result identifies its defining scope and certifies that
all nearer scopes lacked that key. No sibling or unlisted layer is consulted. -/
theorem resolution_provenance (key : Key)
    (layers : List (Scope Directory Key Value)) (directory : Directory) (value : Value)
    (found : resolve key layers = some (directory, value)) :
    ∃ nearer layer suffix,
      layers = nearer ++ layer :: suffix ∧
      (∀ prior ∈ nearer, lookup key prior.rules = none) ∧
      layer.directory = directory ∧ lookup key layer.rules = some value := by
  induction layers with
  | nil => simp [resolve] at found
  | cons layer rest ih =>
      cases defined : lookup key layer.rules with
      | some current =>
          have same : (layer.directory, current) = (directory, value) := by
            simpa [resolve, defined] using found
          exact ⟨[], layer, rest, rfl, by simp, congrArg Prod.fst same,
            defined.trans (congrArg some (congrArg Prod.snd same))⟩
      | none =>
          have inherited : resolve key rest = some (directory, value) := by
            simpa [resolve, defined] using found
          obtain ⟨nearer, source, suffix, split, absent, origin, rule⟩ := ih inherited
          refine ⟨layer :: nearer, source, suffix, by simp [split], ?_, origin, rule⟩
          intro prior present
          rcases List.mem_cons.mp present with same | tail
          · simpa [same] using defined
          · exact absent prior tail

/-- Replacing a whole outer record with the nearest record would lose an
unrelated inherited key. The per-key policy avoids that concrete failure. -/
example :
    let nearest : Scope Nat Nat Nat := ⟨1, [(0, 7)]⟩
    let root : Scope Nat Nat Nat := ⟨0, [(0, 8), (1, 9)]⟩
    resolve 1 [nearest] = none ∧ resolve 1 [nearest, root] = some (0, 9) := by
  decide

end Mettapedia.CognitiveArchitecture.Agent.InstructionScope
