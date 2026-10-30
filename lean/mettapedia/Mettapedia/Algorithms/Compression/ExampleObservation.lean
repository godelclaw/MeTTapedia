import Mettapedia.Algorithms.Compression.RelationalPruning
import Mettapedia.Algorithms.Compression.CostedArtifact
import Mettapedia.Algorithms.Compression.PortableValueWire

/-!
# Batched finite-example checking with complete encoded cost

Queries are evaluated in their declared occurrence order, including repeated
inputs and negative-only inputs. The functional mode observes one required
value, not answer multiplicity; relational mode observes required and forbidden
membership. Neither mode asserts universal program equivalence.

This joins the executable batch checks to the existing relational criterion.
The source-role/effect admission, native execution and payload validators are
separate implementation boundaries, not premises asserting the desired result.
-/

set_option autoImplicit false

namespace Mettapedia.Algorithms.Compression.ExampleObservation

open RelationalPruning

variable {Input Output : Type} [DecidableEq Output]

def positiveCheck (functional : Bool) : List Output → List (List Output) → Bool
  | [], [] => true
  | expected :: rest, answers :: later =>
      (if functional then !answers.isEmpty && answers.all (fun value => decide (value = expected))
       else decide (expected ∈ answers)) && positiveCheck functional rest later
  | _, _ => false

def negativeCheck : List Output → List (List Output) → Bool
  | [], [] => true
  | forbidden :: rest, answers :: later =>
      !decide (forbidden ∈ answers) && negativeCheck rest later
  | _, _ => false

theorem functional_row_iff (expected : Output) (answers : List Output) :
    (!answers.isEmpty && answers.all (fun value => decide (value = expected))) = true ↔
      expected ∈ answers ∧ ∀ value ∈ answers, value = expected := by
  cases answers with
  | nil => simp
  | cons first rest =>
      simp only [List.isEmpty_cons, Bool.not_false, Bool.true_and, List.all_eq_true,
        decide_eq_true_eq, List.mem_cons, forall_eq_or_imp]
      constructor
      · rintro ⟨rfl, tail⟩
        exact ⟨Or.inl rfl, rfl, tail⟩
      · rintro ⟨_, equal, tail⟩
        exact ⟨equal, tail⟩

theorem positive_batches_iff (functional : Bool) (rows : List (Input × Output))
    (run : Input → List Output) :
    positiveCheck functional (rows.map Prod.snd) (rows.map fun row => run row.1) = true ↔
      Covers rows run ∧ (functional = true → Agrees rows run) := by
  induction rows with
  | nil => simp [positiveCheck, Covers, Agrees]
  | cons row rest ih =>
      cases functional with
      | false => simp [positiveCheck, Covers, Agrees, ih]
      | true =>
          change ((!((run row.1).isEmpty) && (run row.1).all (fun value => decide (value = row.2))) &&
            positiveCheck true (rest.map Prod.snd) (rest.map fun item => run item.1)) = true ↔ _
          rw [Bool.and_eq_true, functional_row_iff, ih]
          simp [Covers, Agrees, and_assoc, and_left_comm]

theorem negative_batches_iff (rows : List (Input × Output)) (run : Input → List Output) :
    negativeCheck (rows.map Prod.snd) (rows.map fun row => run row.1) = true ↔ Avoids rows run := by
  induction rows with
  | nil => simp [negativeCheck, Avoids]
  | cons row rest ih => simp [negativeCheck, ih, Avoids]

def check (task : Examples Input Output) (run : Input → List Output) : Bool :=
  positiveCheck task.functional (task.positive.map Prod.snd) (task.positive.map fun row => run row.1) &&
    negativeCheck (task.negative.map Prod.snd) (task.negative.map fun row => run row.1)

theorem check_iff (task : Examples Input Output) (run : Input → List Output) :
    check task run = true ↔ Accepts task run := by
  simp only [check, Bool.and_eq_true, positive_batches_iff, negative_batches_iff, Accepts]
  tauto

theorem preserves_negative_only_queries (task : Examples Input Output) (run : Input → List Output)
    (accepted : check task run = true) (input : Input) (forbidden : Output)
    (declared : (input, forbidden) ∈ task.negative) : forbidden ∉ run input :=
  ((check_iff task run).mp accepted).2.1 _ declared

def artifactValid (task : Examples Input Output) (decode : PortableValueWire.Value → Option (Input → List Output))
    (original candidate : PortableValueWire.Value) : Bool :=
  match decode candidate with
  | none => decide (PortableValueWire.encode candidate = PortableValueWire.encode original)
  | some run => check task run

theorem accepted_program_satisfies_examples (task : Examples Input Output)
    (decode : PortableValueWire.Value → Option (Input → List Output))
    (original current candidate result : PortableValueWire.Value) (run : Input → List Output)
    (program : decode candidate = some run)
    (accepted : CostedArtifact.accept (artifactValid task decode original) PortableValueWire.byteLength
      current candidate = some result) :
    result = candidate ∧ Accepts task run ∧
      (PortableValueWire.encode candidate).length < (PortableValueWire.encode current).length := by
  obtain ⟨same, _, valid, smaller⟩ := CostedArtifact.accept_iff _ _ _ _ _ |>.mp accepted
  refine ⟨same, (check_iff task run).mp ?_, ?_⟩
  · simpa [artifactValid, program] using valid
  · rw [PortableValueWire.encoded_length, PortableValueWire.encoded_length]
    omega

/-! The actual language matching observer can be supplied without assuming
reflexivity, symmetry or transitivity. In particular this also describes a
nonreflexive exceptional scalar or a declared numerical comparison policy. -/

def positiveWith (same : Output → Output → Bool) (functional : Bool) :
    List Output → List (List Output) → Bool
  | [], [] => true
  | expected :: rest, answers :: later =>
      (if functional then !answers.isEmpty && answers.all (same expected)
       else answers.any (same expected)) && positiveWith same functional rest later
  | _, _ => false

def negativeWith (same : Output → Output → Bool) : List Output → List (List Output) → Bool
  | [], [] => true
  | forbidden :: rest, answers :: later =>
      !(answers.any (same forbidden)) && negativeWith same rest later
  | _, _ => false

def MatchesExamples (same : Output → Output → Bool) (task : Examples Input Output)
    (run : Input → List Output) : Prop :=
  (∀ row ∈ task.positive,
    if task.functional then run row.1 ≠ [] ∧ ∀ value ∈ run row.1, same row.2 value = true
    else ∃ value ∈ run row.1, same row.2 value = true) ∧
  (∀ row ∈ task.negative, ∀ value ∈ run row.1, same row.2 value = false)

omit [DecidableEq Output] in
theorem positiveWith_batches (same : Output → Output → Bool) (functional : Bool)
    (rows : List (Input × Output)) (run : Input → List Output) :
    positiveWith same functional (rows.map Prod.snd) (rows.map fun row => run row.1) = true ↔
      ∀ row ∈ rows,
        if functional then run row.1 ≠ [] ∧ ∀ value ∈ run row.1, same row.2 value = true
        else ∃ value ∈ run row.1, same row.2 value = true := by
  induction rows with
  | nil => simp [positiveWith]
  | cons row rest ih => cases functional <;> simp [positiveWith, ih, List.any_eq_true]

omit [DecidableEq Output] in
theorem negativeWith_batches (same : Output → Output → Bool)
    (rows : List (Input × Output)) (run : Input → List Output) :
    negativeWith same (rows.map Prod.snd) (rows.map fun row => run row.1) = true ↔
      ∀ row ∈ rows, ∀ value ∈ run row.1, same row.2 value = false := by
  induction rows with
  | nil => simp [negativeWith]
  | cons row rest ih => simp [negativeWith, ih, List.any_eq_false]

def checkWith (same : Output → Output → Bool) (task : Examples Input Output)
    (run : Input → List Output) : Bool :=
  positiveWith same task.functional (task.positive.map Prod.snd) (task.positive.map fun row => run row.1) &&
    negativeWith same (task.negative.map Prod.snd) (task.negative.map fun row => run row.1)

omit [DecidableEq Output] in
theorem checkWith_iff (same : Output → Output → Bool) (task : Examples Input Output)
    (run : Input → List Output) : checkWith same task run = true ↔ MatchesExamples same task run := by
  simp only [checkWith, Bool.and_eq_true, positiveWith_batches, negativeWith_batches, MatchesExamples]

def validWith (same : Output → Output → Bool) (task : Examples Input Output)
    (decode : PortableValueWire.Value → Option (Input → List Output))
    (original candidate : PortableValueWire.Value) : Bool :=
  match decode candidate with
  | none => decide (PortableValueWire.encode candidate = PortableValueWire.encode original)
  | some run => checkWith same task run

omit [DecidableEq Output] in
theorem accepted_program_matches_fixed_examples (same : Output → Output → Bool)
    (task : Examples Input Output) (decode : PortableValueWire.Value → Option (Input → List Output))
    (original current candidate result : PortableValueWire.Value) (run : Input → List Output)
    (program : decode candidate = some run)
    (accepted : CostedArtifact.accept (validWith same task decode original) PortableValueWire.byteLength
      current candidate = some result) :
    result = candidate ∧ MatchesExamples same task run ∧
      (PortableValueWire.encode candidate).length < (PortableValueWire.encode current).length := by
  obtain ⟨retained, _, valid, smaller⟩ := CostedArtifact.accept_iff _ _ _ _ _ |>.mp accepted
  refine ⟨retained, (checkWith_iff same task run).mp ?_, ?_⟩
  · simpa [validWith, program] using valid
  · rw [PortableValueWire.encoded_length, PortableValueWire.encoded_length]
    omega

namespace Controls

def relational : Examples Nat Nat := ⟨[(0, 1)], [(9, 7)], false⟩
def correct : Nat → List Nat := fun input => if input = 0 then [1, 1] else []
def leaking : Nat → List Nat := fun input => if input = 0 then [1] else [7]

theorem duplicate_answers_are_explicitly_allowed : check relational correct = true := by decide

theorem negative_only_query_rejects_the_leak :
    Covers relational.positive leaking ∧ check relational leaking = false := by
  constructor
  · simp [Covers, relational, leaking]
  · decide

theorem functional_extra_answer_rejected :
    positiveCheck true [1] [[1, 2]] = false ∧ positiveCheck false [1] [[1, 2]] = true := by decide

theorem missing_or_extra_query_rows_rejected :
    positiveCheck false [1] [] = false ∧ negativeCheck [1] [[], []] = false := by decide

theorem repeated_queries_remain_occurrences :
    ([0, 0, 1] : List Nat).map correct = [[1, 1], [1, 1], []] := by decide

theorem nonreflexive_matching_is_not_assumed :
    checkWith (fun _ _ : Nat => false) ⟨[(0, 1)], [], false⟩ (fun _ => [1]) = false := by decide

end Controls

#print axioms functional_row_iff
#print axioms positive_batches_iff
#print axioms negative_batches_iff
#print axioms check_iff
#print axioms preserves_negative_only_queries
#print axioms accepted_program_satisfies_examples
#print axioms positiveWith_batches
#print axioms negativeWith_batches
#print axioms checkWith_iff
#print axioms accepted_program_matches_fixed_examples
#print axioms Controls.duplicate_answers_are_explicitly_allowed
#print axioms Controls.negative_only_query_rejects_the_leak
#print axioms Controls.functional_extra_answer_rejected
#print axioms Controls.missing_or_extra_query_rows_rejected
#print axioms Controls.repeated_queries_remain_occurrences
#print axioms Controls.nonreflexive_matching_is_not_assumed

end Mettapedia.Algorithms.Compression.ExampleObservation
