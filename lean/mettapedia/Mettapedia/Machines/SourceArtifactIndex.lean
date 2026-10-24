import Mettapedia.Machines.MatchIndexProjection

/-!
# An invalidated head index for source artifacts

The index supplies negative evidence only. A present head still runs the
ordered authoritative predicate, which can check source identity, payloads
and provenance. Appending extends a complete index; replacing the catalog
clears it. Failed construction leaves the reference traversal available.

The cost result counts catalog entries examined after consulting the index.
It excludes index construction, hash probes and native allocation. The C
mutation hooks, index completeness flag and memory lifetimes remain separate
conformance obligations.
-/

set_option autoImplicit false
namespace Mettapedia.Machines.SourceArtifactIndex

structure Catalog (α : Type) where
  rows : List (Nat × α)
  heads : Option (List Nat)

def Valid {α : Type} (catalog : Catalog α) : Prop :=
  ∀ heads, catalog.heads = some heads →
    ∀ head, head ∈ catalog.rows.map Prod.fst → head ∈ heads

def replaceRows {α : Type} (catalog : Catalog α) (rows : List (Nat × α)) : Catalog α :=
  { catalog with rows := rows, heads := none }

def append {α : Type} (canExtend : Bool) (catalog : Catalog α)
    (row : Nat × α) : Catalog α :=
  { rows := catalog.rows ++ [row]
    heads := if canExtend then catalog.heads.map (· ++ [row.1]) else none }

def refresh {α : Type} (canAllocate : Bool) (catalog : Catalog α) : Catalog α :=
  match catalog.heads with
  | some _ => catalog
  | none =>
      if canAllocate then { catalog with heads := some (catalog.rows.map Prod.fst) }
      else catalog

def reference {α : Type} (rows : List (Nat × α)) (head : Nat)
    (accept : α → Bool) : List (Nat × α) :=
  rows.filter (fun row => decide (row.1 = head) && accept row.2)

def lookup {α : Type} (catalog : Catalog α) (head : Nat)
    (accept : α → Bool) : List (Nat × α) :=
  match catalog.heads with
  | none => reference catalog.rows head accept
  | some heads =>
      if head ∈ heads then reference catalog.rows head accept else []

theorem replaceRows_valid {α : Type} (catalog : Catalog α) (rows : List (Nat × α)) :
    Valid (replaceRows catalog rows) := by
  simp [Valid, replaceRows]

theorem append_valid {α : Type} (canExtend : Bool) (catalog : Catalog α)
    (row : Nat × α) (valid : Valid catalog) :
    Valid (append canExtend catalog row) := by
  cases canExtend with
  | false => simp [append, Valid]
  | true =>
      cases cached : catalog.heads with
      | none => simp [append, cached, Valid]
      | some heads =>
          intro extended observed head member
          have equal : extended = heads ++ [row.1] := by
            simpa [append, cached] using observed.symm
          rw [equal]
          have member' : head ∈ catalog.rows.map Prod.fst ∨ head = row.1 := by
            simpa [append] using member
          rcases member' with old | new
          · exact List.mem_append_left _ (valid heads cached head old)
          · simp [new]

theorem refresh_valid {α : Type} (canAllocate : Bool) (catalog : Catalog α)
    (valid : Valid catalog) : Valid (refresh canAllocate catalog) := by
  cases cached : catalog.heads with
  | some heads => simpa [refresh, cached] using valid
  | none =>
      cases canAllocate
      · simpa [refresh, cached] using valid
      · intro heads observed head member
        have equal : heads = catalog.rows.map Prod.fst := by
          simpa [refresh, cached] using observed.symm
        rw [equal]
        simpa [refresh, cached] using member

theorem absent_reference {α : Type} (rows : List (Nat × α)) (head : Nat)
    (accept : α → Bool) (absent : head ∉ rows.map Prod.fst) :
    reference rows head accept = [] := by
  apply List.filter_eq_nil_iff.mpr
  intro row member
  have different : row.1 ≠ head := by
    intro equal
    apply absent
    rw [← equal]
    exact List.mem_map_of_mem member
  simp [different]

theorem lookup_exact {α : Type} (catalog : Catalog α) (head : Nat)
    (accept : α → Bool) (valid : Valid catalog) :
    lookup catalog head accept = reference catalog.rows head accept := by
  cases cached : catalog.heads with
  | none => simp [lookup, cached]
  | some heads =>
      by_cases present : head ∈ heads
      · simp [lookup, cached, present]
      · have absent : head ∉ catalog.rows.map Prod.fst := by
          intro member
          exact present (valid heads cached head member)
        simp [lookup, cached, present, absent_reference _ _ _ absent]

theorem refresh_lookup_exact {α : Type} (canAllocate : Bool) (catalog : Catalog α)
    (head : Nat) (accept : α → Bool) (valid : Valid catalog) :
    lookup (refresh canAllocate catalog) head accept = reference catalog.rows head accept := by
  have checked := lookup_exact (refresh canAllocate catalog) head accept
    (refresh_valid canAllocate catalog valid)
  have rows : (refresh canAllocate catalog).rows = catalog.rows := by
    cases cached : catalog.heads <;> cases canAllocate <;> simp [refresh, cached]
  simpa [rows] using checked

theorem first_exact {α : Type} (catalog : Catalog α) (head : Nat)
    (accept : α → Bool) (valid : Valid catalog) :
    (lookup catalog head accept).head? = (reference catalog.rows head accept).head? := by
  rw [lookup_exact catalog head accept valid]

def catalogVisits {α : Type} (catalog : Catalog α) (head : Nat) : Nat :=
  match catalog.heads with
  | none => catalog.rows.length
  | some heads => if head ∈ heads then catalog.rows.length else 0

theorem visits_bounded {α : Type} (catalog : Catalog α) (head : Nat) :
    catalogVisits catalog head ≤ catalog.rows.length := by
  cases cached : catalog.heads with
  | none => simp [catalogVisits, cached]
  | some heads => by_cases present : head ∈ heads <;> simp [catalogVisits, cached, present]

theorem absent_visits_zero {α : Type} (catalog : Catalog α) (heads : List Nat)
    (head : Nat) (cached : catalog.heads = some heads) (absent : head ∉ heads) :
    catalogVisits catalog head = 0 := by
  simp [catalogVisits, cached, absent]

example : lookup (refresh true (⟨[(7, 1), (7, 2), (9, 3)], none⟩ : Catalog Nat))
    7 (fun _ => true) = [(7, 1), (7, 2)] := by decide

-- Publishing a new head invalidates an earlier negative observation.
example : lookup (refresh true (append true (⟨[(7, 1)], some [7]⟩ : Catalog Nat) (9, 2)))
    9 (fun _ => true) = [(9, 2)] := by decide

-- A matching head does not establish the payload's admission.
example : lookup (⟨[(7, 1)], some [7]⟩ : Catalog Nat)
    7 (fun value => decide (value = 2)) = [] := by decide

end Mettapedia.Machines.SourceArtifactIndex
