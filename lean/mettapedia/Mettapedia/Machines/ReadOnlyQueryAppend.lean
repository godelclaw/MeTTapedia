import Mettapedia.Machines.ReadOnlyQuery

/-!
# Validating an append against a pure query's read footprint

A store is an ordered list of rows. Each key selects an ordered bucket;
duplicate rows remain duplicate observations. An append that misses every
read key preserves the entire adaptive query, including its negative reads.
Only the new rows need inspection once the previous prefix is established.
Storage identity, preservation of that prefix and external semantic authority
are separate obligations of an implementation using this law.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.ReadOnlyQuery.Append

universe u v w
variable {Key : Type u} {Row : Type v} {Answer : Type w}

def bucket (selects : Key → Row → Bool) (rows : List Row) (key : Key) : List Row :=
  rows.filter (selects key)

/-- If old rows survive in order, equality of candidate counts establishes
equality of the complete selected family, including duplicate occurrences.
Rows may have been inserted between members of a composed store. -/
theorem bucket_eq_of_sublist_of_length_eq (selects : Key → Row → Bool)
    {before after : List Row} (preserved : before.Sublist after) (key : Key)
    (sameCount : (bucket selects before key).length =
      (bucket selects after key).length) :
    bucket selects after key = bucket selects before key := by
  exact ((preserved.filter (selects key)).eq_of_length sameCount).symm

/-- Candidate counts are a sufficient certificate for an adaptive query
only together with preservation of the old rows. Complete observations,
including the ordered read trace, are preserved. -/
theorem run_eq_of_sublist_of_bucket_lengths (selects : Key → Row → Bool)
    {before after : List Row} (preserved : before.Sublist after)
    (program : Program Key (List Row) Answer) (keys : List Key)
    (covers : ∀ read ∈ (run (bucket selects before) program).reads, read.1 ∈ keys)
    (sameCounts : ∀ key ∈ keys, (bucket selects before key).length =
      (bucket selects after key).length) :
    run (bucket selects after) program = run (bucket selects before) program := by
  apply run_eq_of_agrees
  intro read member
  rw [bucket_eq_of_sublist_of_length_eq selects preserved read.1
    (sameCounts read.1 (covers read member))]
  exact run_agrees (bucket selects before) program read member

example : bucket (fun (key row : Nat) => decide (key = row))
    [1, 2, 1, 3] 1 = [1, 1] := by decide

/-- Equal counts without a preserved prefix do not establish ordered answers. -/
example :
    (bucket (fun (_ : Unit) (_ : Nat) => true) [1, 2] ()).length =
      (bucket (fun (_ : Unit) (_ : Nat) => true) [2, 1] ()).length ∧
    bucket (fun (_ : Unit) (_ : Nat) => true) [1, 2] () ≠
      bucket (fun (_ : Unit) (_ : Nat) => true) [2, 1] () := by decide

/-- A duplicate selected row changes the candidate count even when answer
support is unchanged. -/
example :
    (bucket (fun (key row : Nat) => decide (key = row)) [1] 1).length ≠
      (bucket (fun (key row : Nat) => decide (key = row)) [1, 1] 1).length := by decide

/-- Check only the proposed suffix, against a conservative list of read keys. -/
def misses (selects : Key → Row → Bool) (keys : List Key) (delta : List Row) : Bool :=
  keys.all fun key => delta.all fun row => !selects key row

theorem misses_iff (selects : Key → Row → Bool) (keys : List Key) (delta : List Row) :
    misses selects keys delta = true ↔
      ∀ key ∈ keys, ∀ row ∈ delta, selects key row = false := by
  simp [misses]

theorem bucket_append (selects : Key → Row → Bool) (before delta : List Row)
    (keys : List Key) (untouched : misses selects keys delta = true)
    {key : Key} (read : key ∈ keys) :
    bucket selects (before ++ delta) key = bucket selects before key := by
  have empty : delta.filter (selects key) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro row member
    simp [(misses_iff selects keys delta).mp untouched key read row member]
  simp [bucket, List.filter_append, empty]

/-- A syntactic footprint may contain more names than the actual read trace.
It must also contain keys whose observed bucket was empty. -/
theorem agrees_append (selects : Key → Row → Bool) (before delta : List Row)
    (program : Program Key (List Row) Answer) (keys : List Key)
    (covers : ∀ read ∈ (run (bucket selects before) program).reads, read.1 ∈ keys)
    (untouched : misses selects keys delta = true) :
    Agrees (bucket selects (before ++ delta)) (run (bucket selects before) program).reads := by
  intro read member
  rw [bucket_append selects before delta keys untouched (covers read member)]
  exact run_agrees (bucket selects before) program read member

/-- The existing adaptive-query theorem supplies the complete observation
agreement; the suffix test does not execute the query again. -/
theorem run_append (selects : Key → Row → Bool) (before delta : List Row)
    (program : Program Key (List Row) Answer) (keys : List Key)
    (covers : ∀ read ∈ (run (bucket selects before) program).reads, read.1 ∈ keys)
    (untouched : misses selects keys delta = true) :
    run (bucket selects (before ++ delta)) program = run (bucket selects before) program :=
  run_eq_of_agrees _ _ program (agrees_append selects before delta program keys covers untouched)

/-- Successful successive suffix checks compose. A bookmark may advance
after each one; it need not scan earlier validated suffixes again. -/
theorem misses_append (selects : Key → Row → Bool) (keys : List Key)
    (first second : List Row) :
    misses selects keys (first ++ second) =
      (misses selects keys first && misses selects keys second) := by
  apply Bool.eq_iff_iff.mpr
  simp [misses_iff, List.mem_append, or_imp, forall_and]

/-- A certificate may compress repeated identical observations without
changing validation. Conflicting observations are retained as different pairs. -/
theorem checkReads_eraseDups [DecidableEq Key] [DecidableEq Row]
    (store : Key → Row) (reads : Reads Key Row) :
    checkReads store reads.eraseDups = checkReads store reads := by
  apply Bool.eq_iff_iff.mpr
  simp [checkReads_iff, Agrees]

/-- Revalidating a compressed certificate preserves the complete adaptive
query, not just its final answer or the existence of an answer. -/
theorem run_eq_of_compressed_check [DecidableEq Key] [DecidableEq Row]
    (before after : Key → Row) (program : Program Key Row Answer)
    (checked : checkReads after (run before program).reads.eraseDups = true) :
    run after program = run before program := by
  rw [checkReads_eraseDups] at checked
  exact run_eq_of_agrees before after program
    ((checkReads_iff after (run before program).reads).mp checked)

/-- A missing capability becoming present is a changed read, even when a
positive read elsewhere stays unchanged. -/
example : checkReads (fun (_ : Nat) => true) [(1, true), (2, false)].eraseDups = false := by
  decide

example : checkReads (fun (key : Nat) => decide (key = 1))
    [(1, true), (2, false), (1, true)].eraseDups = true := by decide

end Mettapedia.Machines.ReadOnlyQuery.Append
