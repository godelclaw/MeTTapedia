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

/-- Compilation either produces an executable artifact or a stable semantic
refusal. Resource exhaustion is intentionally outside this result type. -/
inductive CompilationDecision (Reason Output : Type) where
  | refused (reason : Reason)
  | admitted (output : Output)
  deriving DecidableEq

theorem named_append_preserves_compilation_reads [DecidableEq Name]
    (before delta : List (Row Name Payload))
    (program : Program Name (List (Row Name Payload)) Result) (names : List Name)
    (covers : ∀ read ∈ (run (projection before) program).reads, read.1 ∈ names)
    (untouched : Append.misses affects names delta = true) :
    run (projection (before ++ delta)) program = run (projection before) program :=
  Append.run_append affects before delta program names covers untouched

/-- A refused compilation is reusable under exactly the same read-footprint
law as an admitted compilation. Both the refusal and its complete ordered read
trace are preserved; this does not turn resource failure into refusal. -/
theorem named_append_preserves_refusal [DecidableEq Name]
    (before delta : List (Row Name Payload))
    (program : Program Name (List (Row Name Payload))
      (CompilationDecision Reason Output))
    (names : List Name)
    (covers : ∀ read ∈ (run (projection before) program).reads, read.1 ∈ names)
    (untouched : Append.misses affects names delta = true) (reason : Reason)
    (refused : (run (projection before) program).answer = .refused reason) :
    (run (projection (before ++ delta)) program).answer = .refused reason ∧
      (run (projection (before ++ delta)) program).reads =
        (run (projection before) program).reads := by
  have same := named_append_preserves_compilation_reads
    before delta program names covers untouched
  rw [same]
  exact ⟨refused, rfl⟩

/-- A costed exact validator for one already-selected dependency family.
It stops at the first relevant appended row; an entirely unrelated suffix is
read once from left to right. -/
def validateUnrelated : List Bool → Bool × Nat
  | [] => (true, 0)
  | relevant :: rest =>
      if relevant then (false, 1)
      else
        let checked := validateUnrelated rest
        (checked.1, checked.2 + 1)

theorem validateUnrelated_result (rows : List Bool) :
    (validateUnrelated rows).1 = rows.all (fun relevant => !relevant) := by
  induction rows with
  | nil => rfl
  | cons relevant rest ih =>
      simp only [validateUnrelated]
      cases relevant <;> simp [ih]

/-- The successful worst case performs exactly one inspection per appended
row. This is the upper-bound side of suffix validation. -/
theorem validateUnrelated_all_false_cost (count : Nat) :
    validateUnrelated (List.replicate count false) = (true, count) := by
  induction count with
  | zero => rfl
  | succ count ih =>
      rw [List.replicate_succ, validateUnrelated, ih]
      simp

/-- Every coordinate of an all-unrelated suffix can independently invalidate
reuse. Thus no coordinate is semantically redundant for an exact black-box
validator; together with `validateUnrelated_all_false_cost`, this gives the
linear row-inspection bound for this model. -/
theorem each_suffix_coordinate_is_decisive (before after : Nat) :
    (validateUnrelated
        (List.replicate before false ++ false :: List.replicate after false)).1 = true ∧
      (validateUnrelated
        (List.replicate before false ++ true :: List.replicate after false)).1 = false := by
  rw [validateUnrelated_result, validateUnrelated_result]
  simp

namespace Controls

abbrev R := Row Nat Nat

def before : List R := [.equation (some 1) 10, .equation (some 1) 10,
  .declaration (.named 1) 20]

/-- The second read is absent. Its absence controls the returned result. -/
def query : Program Nat (List R) (List R) :=
  .read 1 fun equations => .read 2 fun negative => .pure (equations ++ negative)

def refusalQuery : Program Nat (List R) (CompilationDecision String Nat) :=
  .read 2 fun rows =>
    .pure (if rows.isEmpty then .refused "relational pattern" else .admitted rows.length)

theorem unrelated_append_preserves_refusal :
    run (projection (before ++ [.equation (some 3) 30, .data 60])) refusalQuery =
      run (projection before) refusalQuery := by
  rfl

/-- A new row under the negatively read name reopens compilation. -/
theorem relevant_append_reopens_refusal :
    (run (projection before) refusalQuery).answer = .refused "relational pattern" ∧
      (run (projection (before ++ [.equation (some 2) 70])) refusalQuery).answer =
        .admitted 1 := by
  decide

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
