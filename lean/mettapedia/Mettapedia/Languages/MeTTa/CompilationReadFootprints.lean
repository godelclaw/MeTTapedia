import Mettapedia.Machines.ReadOnlyQueryAppend

/-!
# Named compilation reads under append-only program changes

Equation candidates and named type families read complete ordered buckets.
Wildcard equations and declarations affect every name. Subtyping remains a
global dependency. A compound declaration subject cannot match a symbol.
These are projection laws, not a native C compiler adequacy theorem: the C
compiler must establish that its captured names cover all compilation reads.
-/

namespace Mettapedia.Languages.MeTTa.CompilationReadFootprints

open Mettapedia.Machines.ReadOnlyQuery

inductive Subject (Name : Type) where
  | named (name : Name)
  | wildcard
  | compound
  deriving DecidableEq

inductive Row (Name Payload : Type) where
  | equation (head : Option Name) (body : Payload)
  | declaration (subject : Subject Name) (type : Payload)
  | subtype (edge : Payload)
  | data (value : Payload)
  deriving DecidableEq

def affects [DecidableEq Name] (name : Name) : Row Name Payload → Bool
  | .equation (some head) _ => decide (head = name)
  | .equation none _ => true
  | .declaration (.named subject) _ => decide (subject = name)
  | .declaration .wildcard _ => true
  | .declaration .compound _ => false
  | .subtype _ => true
  | .data _ => false

abbrev projection [DecidableEq Name] (rows : List (Row Name Payload)) (name : Name) :=
  Append.bucket affects rows name

theorem named_append_preserves_compilation_reads [DecidableEq Name]
    (before delta : List (Row Name Payload))
    (program : Program Name (List (Row Name Payload)) Result) (names : List Name)
    (covers : ∀ read ∈ (run (projection before) program).reads, read.1 ∈ names)
    (untouched : Append.misses affects names delta = true) :
    run (projection (before ++ delta)) program = run (projection before) program :=
  Append.run_append affects before delta program names covers untouched

namespace Controls

abbrev R := Row Nat Nat

def before : List R := [.equation (some 1) 10, .equation (some 1) 10,
  .declaration (.named 1) 20]

/-- The second read is absent. Its absence controls the returned result. -/
def query : Program Nat (List R) (List R) :=
  .read 1 fun equations => .read 2 fun negative => .pure (equations ++ negative)

theorem ordinary_disjoint_append_preserves_all_occurrences :
    run (projection (before ++ [.equation (some 3) 30,
      .declaration (.named 4) 40, .declaration .compound 50, .data 60])) query =
      run (projection before) query := by
  simp [projection, Append.bucket, affects, before, query, run]

theorem duplicate_equations_remain_duplicates :
    (run (projection before) query).answer =
      [.equation (some 1) 10, .equation (some 1) 10, .declaration (.named 1) 20] := by
  decide

theorem a_new_definition_changes_an_absence_read :
    (run (projection (before ++ [.equation (some 2) 70])) query).answer ≠
      (run (projection before) query).answer := by decide

theorem added_duplicate_is_not_reusable :
    Append.misses affects [1, 2] [(.equation (some 1) 10 : R)] = false := by decide

theorem wildcard_equation_is_not_disjoint :
    Append.misses affects [1, 2] [(.equation none 80 : R)] = false := by decide

theorem wildcard_declaration_is_not_disjoint :
    Append.misses affects [1, 2] [(.declaration .wildcard 90 : R)] = false := by decide

theorem subtyping_is_not_disjoint :
    Append.misses affects [1, 2] [(.subtype 100 : R)] = false := by decide

/-- An empty suffix does not certify that the old prefix survived. -/
theorem removal_requires_a_separate_prefix_check :
    Append.misses affects [1, 2] ([] : List R) = true ∧
      (run (projection ([] : List R)) query).answer ≠
        (run (projection before) query).answer := by decide

end Controls
end Mettapedia.Languages.MeTTa.CompilationReadFootprints
