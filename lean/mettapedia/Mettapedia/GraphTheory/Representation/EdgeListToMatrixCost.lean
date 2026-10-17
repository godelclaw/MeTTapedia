import Mettapedia.GraphTheory.Representation.EdgeListToMatrixGSLT
import Mettapedia.GraphTheory.Representation.CostModel
import Mettapedia.GSLT.Core.GSLTConstructions

/-!
# Resource accounts derived from detailed materialization events

The existing occurrence-wise matrix machine supplies every transition and
ordered execution below. A declared profile charges its `write` and `finish`
events; folding those authentic steps derives the complete account. The
standard GSLT writer lift retains the same intermediate states and order.

Charges describe the selected symbolic events. They do not identify a
symbolic symmetric update with physical cell writes, validate a mutable
implementation, or equate this account with a separately chosen dense
materialization schedule. Zero charges still permit nonempty execution.
-/

set_option autoImplicit false

namespace Mettapedia.GraphTheory.Representation.EdgeListToMatrixCost

open Mettapedia.GSLT
open Mettapedia.GraphTheory.Representation
open EdgeListToMatrixGSLT

/-- The source determines which authentic rule can fire. Terminal states
have no event; their default charge is never usable without a base step. -/
def eventCharge {n : Nat} (writeCharge finishCharge : Resources) :
    State n → Resources
  | .active (_ :: _) _ => writeCharge
  | .active [] _ => finishCharge
  | .done _ => Resources.zero

/-- Grade only actual write/finish transitions of the existing machine. -/
def spend (n : Nat) (writeCharge finishCharge : Resources) :
    (theory n).StepSpend Resources where
  graded source target cost :=
    Step source target ∧ cost = eventCharge writeCharge finishCharge source
  sound graded := graded.1
  resp_left := by
    intro source source' target cost equivalent graded
    change source = source' at equivalent
    subst source'
    exact ⟨target, graded, rfl⟩
  resp_right := by
    intro source target target' cost graded equivalent
    change target = target' at equivalent
    subst target'
    exact graded

/-- No actual event is omitted by the two-charge profile. -/
theorem spend_total (n : Nat) (writeCharge finishCharge : Resources) :
    (spend n writeCharge finishCharge).Total := by
  intro source target step
  exact ⟨eventCharge writeCharge finishCharge source, step, rfl⟩

abbrev writerTheory (n : Nat) (writeCharge finishCharge : Resources) : GSLT :=
  (theory n).spendLift (spend n writeCharge finishCharge)

/-- One lifted event is exactly one base event with its declared charge;
there are neither invented base steps nor alternative charges for a step. -/
theorem writer_step_iff {n : Nat} (writeCharge finishCharge : Resources)
    (source target : State n) (before after : Resources) :
    (writerTheory n writeCharge finishCharge).Step (source, before) (target, after) ↔
      Step source target ∧
        after = before.seq (eventCharge writeCharge finishCharge source) := by
  change (∃ grade, (Step source target ∧
      grade = eventCharge writeCharge finishCharge source) ∧ after = before * grade) ↔ _
  constructor
  · rintro ⟨grade, ⟨step, rfl⟩, accumulated⟩
    exact ⟨step, accumulated⟩
  · rintro ⟨step, accumulated⟩
    exact ⟨eventCharge writeCharge finishCharge source, ⟨step, rfl⟩, accumulated⟩

/-- Fold the actual ordered path, including its finalization occurrence. -/
def pathCharge {n : Nat} (writeCharge finishCharge : Resources) :
    {source target : State n} → (theory n).RewritePath source target → Resources
  | _, _, .nil _ => Resources.zero
  | source, _, .cons _ rest =>
      (eventCharge writeCharge finishCharge source).seq
        (pathCharge writeCharge finishCharge rest)

/-- Running accumulation follows the writer's left-to-right execution. -/
def finalAccount {n : Nat} (writeCharge finishCharge : Resources) :
    {source target : State n} → (theory n).RewritePath source target →
      Resources → Resources
  | _, _, .nil _, before => before
  | source, _, .cons _ rest, before =>
      finalAccount writeCharge finishCharge rest
        (before.seq (eventCharge writeCharge finishCharge source))

theorem finalAccount_eq {n : Nat} (writeCharge finishCharge : Resources)
    : {source target : State n} → (path : (theory n).RewritePath source target) →
      (before : Resources) →
      finalAccount writeCharge finishCharge path before =
        before.seq (pathCharge writeCharge finishCharge path)
  | _, _, .nil _, _ => by simp [finalAccount, pathCharge]
  | _, _, .cons _ rest, before => by
      simp only [finalAccount, pathCharge]
      rw [finalAccount_eq writeCharge finishCharge rest, Resources.seq_assoc]

/-- Lift the supplied path itself, rather than executing a second evaluator. -/
def liftPath {n : Nat} (writeCharge finishCharge : Resources) :
    {source target : State n} → (path : (theory n).RewritePath source target) →
      (before : Resources) →
      (writerTheory n writeCharge finishCharge).RewritePath
        (source, before) (target, finalAccount writeCharge finishCharge path before)
  | _, _, .nil state, before =>
      GSLT.RewritePath.nil (S := writerTheory n writeCharge finishCharge) (state, before)
  | source, _, @GSLT.RewritePath.cons _ _ middle _ step rest, before =>
      GSLT.RewritePath.cons (S := writerTheory n writeCharge finishCharge)
        (show (writerTheory n writeCharge finishCharge).Step (source, before)
            (middle, before.seq (eventCharge writeCharge finishCharge source)) from
          ⟨eventCharge writeCharge finishCharge source, ⟨step, rfl⟩, rfl⟩)
        (liftPath writeCharge finishCharge rest
          (before.seq (eventCharge writeCharge finishCharge source)))

/-- Writer erasure keeps every intermediate base state. -/
def erasePath {n : Nat} (writeCharge finishCharge : Resources) :
    {source target : (writerTheory n writeCharge finishCharge).Term} →
      (writerTheory n writeCharge finishCharge).RewritePath source target →
        (theory n).RewritePath source.1 target.1
  | _, _, .nil state => .nil state.1
  | _, _, .cons step rest =>
      .cons (GSLT.spendLift_erase_step (spend n writeCharge finishCharge) step)
        (erasePath writeCharge finishCharge rest)

/-- Conversely, every writer path has precisely the account obtained by
folding its erased actual events, rather than merely an arbitrary grade. -/
theorem erased_path_account {n : Nat} (writeCharge finishCharge : Resources) :
    {source target : (writerTheory n writeCharge finishCharge).Term} →
      (path : (writerTheory n writeCharge finishCharge).RewritePath source target) →
      target.2 = source.2.seq (pathCharge writeCharge finishCharge
        (erasePath writeCharge finishCharge path))
  | _, _, .nil _ => by simp [erasePath, pathCharge]
  | source, target, @GSLT.RewritePath.cons _ _ middle _ step rest => by
      have first : middle.2 = source.2.seq
          (eventCharge writeCharge finishCharge source.1) :=
        ((writer_step_iff writeCharge finishCharge source.1 middle.1 source.2 middle.2).mp step).2
      calc
        target.2 = middle.2.seq (pathCharge writeCharge finishCharge
            (erasePath writeCharge finishCharge rest)) :=
          erased_path_account writeCharge finishCharge rest
        _ = (source.2.seq (eventCharge writeCharge finishCharge source.1)).seq
            (pathCharge writeCharge finishCharge
              (erasePath writeCharge finishCharge rest)) := by rw [first]
        _ = source.2.seq (pathCharge writeCharge finishCharge
            (erasePath writeCharge finishCharge (.cons step rest))) := by
          change (source.2.seq (eventCharge writeCharge finishCharge source.1)).seq
              (pathCharge writeCharge finishCharge
                (erasePath writeCharge finishCharge rest)) =
            source.2.seq ((eventCharge writeCharge finishCharge source.1).seq
              (pathCharge writeCharge finishCharge
                (erasePath writeCharge finishCharge rest)))
          exact Resources.seq_assoc _ _ _

/-- Exact path equality preserves order and repeated events, not just endpoints. -/
theorem erase_liftPath {n : Nat} (writeCharge finishCharge : Resources)
    : {source target : State n} → (path : (theory n).RewritePath source target) →
      (before : Resources) →
      erasePath writeCharge finishCharge (liftPath writeCharge finishCharge path before) = path
  | _, _, .nil _, _ => rfl
  | source, _, .cons step rest, before => by
      change GSLT.RewritePath.cons (S := theory n) step
          (erasePath writeCharge finishCharge
            (liftPath writeCharge finishCharge rest
              (before.seq (eventCharge writeCharge finishCharge source)))) =
        GSLT.RewritePath.cons (S := theory n) step rest
      exact congrArg (GSLT.RewritePath.cons step)
        (erase_liftPath writeCharge finishCharge rest
          (before.seq (eventCharge writeCharge finishCharge source)))

@[simp] theorem liftPath_length {n : Nat} (writeCharge finishCharge : Resources)
    : {source target : State n} → (path : (theory n).RewritePath source target) →
      (before : Resources) →
      (liftPath writeCharge finishCharge path before).length = path.length
  | _, _, .nil _, _ => rfl
  | source, _, .cons _ rest, before => by
      change 1 + (liftPath writeCharge finishCharge rest
          (before.seq (eventCharge writeCharge finishCharge source))).length = 1 + rest.length
      exact congrArg (1 + ·) (liftPath_length writeCharge finishCharge rest
        (before.seq (eventCharge writeCharge finishCharge source)))

/-- Ordered states, including both endpoints, of an existing rewrite path. -/
def pathStates {system : GSLT} : {source target : system.Term} →
    system.RewritePath source target → List system.Term
  | _, _, .nil state => [state]
  | source, _, .cons _ rest => source :: pathStates rest

theorem liftPath_states {n : Nat} (writeCharge finishCharge : Resources)
    : {source target : State n} → (path : (theory n).RewritePath source target) →
      (before : Resources) →
      (pathStates (liftPath writeCharge finishCharge path before)).map Prod.fst =
        pathStates path
  | _, _, .nil _, _ => rfl
  | source, _, .cons _ rest, before => by
      change source :: (pathStates (liftPath writeCharge finishCharge rest
          (before.seq (eventCharge writeCharge finishCharge source)))).map Prod.fst =
        source :: pathStates rest
      exact congrArg (List.cons source) (liftPath_states writeCharge finishCharge rest
        (before.seq (eventCharge writeCharge finishCharge source)))

/-- The closed account is derived from all write and finish occurrences in
the actual pre-existing construction path. -/
theorem runPath_charge {n : Nat} (writeCharge finishCharge : Resources)
    (remaining : List (EdgeList.Edge n)) (matrix : AdjacencyMatrix.Rep n) :
    pathCharge writeCharge finishCharge (runPath remaining matrix) =
      (Resources.replicate remaining.length writeCharge).seq finishCharge := by
  induction remaining generalizing matrix with
  | nil => simp [runPath, pathCharge, eventCharge]
  | cons edge rest ih =>
      simp only [runPath, pathCharge, eventCharge, List.length_cons]
      change writeCharge.seq
          (pathCharge writeCharge finishCharge (runPath rest (insertOccurrence matrix edge))) = _
      rw [ih]
      have repetition : Resources.replicate (rest.length + 1) writeCharge =
          writeCharge.seq (Resources.replicate rest.length writeCharge) := by
        rw [Nat.add_comm, Resources.replicate_add, Resources.replicate_one]
      rw [repetition, Resources.seq_assoc]

/-- The actual charged execution from any accumulator has this exact endpoint. -/
theorem runPath_finalAccount {n : Nat} (writeCharge finishCharge : Resources)
    (remaining : List (EdgeList.Edge n)) (matrix : AdjacencyMatrix.Rep n)
    (before : Resources) :
    finalAccount writeCharge finishCharge (runPath remaining matrix) before =
      before.seq ((Resources.replicate remaining.length writeCharge).seq finishCharge) := by
  rw [finalAccount_eq, runPath_charge]

/-- The public result retains the account folded from authentic events. -/
def materializeAccounted {n : Nat} (writeCharge finishCharge : Resources)
    (graph : EdgeList.Rep n) : Accounted (AdjacencyMatrix.Rep n) :=
  ⟨materialize graph, pathCharge writeCharge finishCharge (materializePath graph)⟩

/-- Both the computed matrix and its entire resource vector are retained by
the existing equivalence to the standard Writer construction. -/
theorem materialize_writer {n : Nat} (writeCharge finishCharge : Resources)
    (graph : EdgeList.Rep n) :
    Accounted.writerEquiv (AdjacencyMatrix.Rep n)
        (materializeAccounted writeCharge finishCharge graph) =
      (Transformations.toMatrix (EdgeList.presentation n) graph,
        (Resources.replicate graph.entries.length writeCharge).seq finishCharge) := by
  apply Prod.ext
  · exact materialize_eq_refinement graph
  · exact runPath_charge writeCharge finishCharge graph.entries (AdjacencyMatrix.empty n)

/-- Denotation of the independently accounted terminal carrier is unchanged. -/
theorem materializeAccounted_value {n : Nat} (writeCharge finishCharge : Resources)
    (graph : EdgeList.Rep n) :
    (materializeAccounted writeCharge finishCharge graph).value =
      Transformations.toMatrix (EdgeList.presentation n) graph :=
  materialize_eq_refinement graph

/-- The public accounted result is the endpoint of a writer execution of the
actual construction, starting with an empty account. -/
def materializeWriterPath {n : Nat} (writeCharge finishCharge : Resources)
    (graph : EdgeList.Rep n) :
    (writerTheory n writeCharge finishCharge).RewritePath
      (initial graph, Resources.zero)
      (.done (materializeAccounted writeCharge finishCharge graph).value,
        (materializeAccounted writeCharge finishCharge graph).resources) := by
  simpa only [finalAccount_eq, Resources.zero_seq, materializeAccounted] using
    liftPath writeCharge finishCharge (materializePath graph) Resources.zero

/-- Unit symbolic time per event. Other resource coordinates remain zero. -/
def unitTime : Resources := { time := 1 }

/-- Unit event time agrees with the already proved number of actual steps. -/
theorem unitTime_count {n : Nat} (remaining : List (EdgeList.Edge n))
    (matrix : AdjacencyMatrix.Rep n) :
    (pathCharge unitTime unitTime (runPath remaining matrix)).time =
      (runPath remaining matrix).length := by
  rw [runPath_charge, runPath_length]
  simp [unitTime, Resources.seq, Resources.replicate]

/-- In particular, a graph with `m` authored occurrences takes `m + 1`
unit-time events, including finalization. -/
theorem materialize_unitTime {n : Nat} (graph : EdgeList.Rep n) :
    (materializeAccounted unitTime unitTime graph).resources.time =
      graph.entries.length + 1 := by
  change (pathCharge unitTime unitTime (runPath graph.entries
    (AdjacencyMatrix.empty n))).time = _
  rw [unitTime_count, runPath_length]

namespace Controls

/-- Repeating an edge changes occurrence structure, but not matrix content. -/
theorem duplicate_same_matrix {n : Nat} (edge : EdgeList.Edge n)
    (matrix : AdjacencyMatrix.Rep n) :
    buildFrom matrix [edge, edge] = buildFrom matrix [edge] := by
  apply matrix_ext
  funext source target
  simp [buildFrom_cell]

/-- The duplicate performs a second charged event even though its matrix
endpoint equals the one-occurrence endpoint. -/
theorem duplicate_more_time {n : Nat} (edge : EdgeList.Edge n)
    (writeCharge finishCharge : Resources) (positive : 0 < writeCharge.time) :
    (materializeAccounted writeCharge finishCharge ⟨[edge]⟩).value =
        (materializeAccounted writeCharge finishCharge ⟨[edge, edge]⟩).value ∧
      (materializeAccounted writeCharge finishCharge ⟨[edge]⟩).resources.time <
        (materializeAccounted writeCharge finishCharge ⟨[edge, edge]⟩).resources.time := by
  constructor
  · exact (duplicate_same_matrix edge (AdjacencyMatrix.empty n)).symm
  · change (pathCharge writeCharge finishCharge (runPath [edge]
        (AdjacencyMatrix.empty n))).time <
      (pathCharge writeCharge finishCharge (runPath [edge, edge]
        (AdjacencyMatrix.empty n))).time
    rw [runPath_charge, runPath_charge]
    simp only [List.length_cons, List.length_nil, Resources.seq, Resources.replicate]
    omega

/-- The complete vectors also differ whenever their time coordinates do. -/
theorem duplicate_different_accounts {n : Nat} (edge : EdgeList.Edge n)
    (writeCharge finishCharge : Resources) (positive : 0 < writeCharge.time) :
    (materializeAccounted writeCharge finishCharge ⟨[edge]⟩).resources ≠
      (materializeAccounted writeCharge finishCharge ⟨[edge, edge]⟩).resources := by
  intro equal
  have less := (duplicate_more_time edge writeCharge finishCharge positive).2
  rw [equal] at less
  exact (Nat.lt_irrefl _ less)

/-- Nonempty actual execution can have a zero selected account. Resource
profiles cannot, by themselves, detect whether execution occurred. -/
theorem zero_profile_nonempty {n : Nat} (remaining : List (EdgeList.Edge n))
    (matrix : AdjacencyMatrix.Rep n) :
    0 < (liftPath Resources.zero Resources.zero (runPath remaining matrix)
        Resources.zero).length ∧
      pathCharge Resources.zero Resources.zero (runPath remaining matrix) = Resources.zero := by
  constructor
  · rw [liftPath_length, runPath_length]
    omega
  · rw [runPath_charge]
    apply Resources.ext <;>
      simp [Resources.replicate, Resources.seq, Resources.zero]

/-- Deliberately incomplete accounting: only write occurrences receive a
grade. This is a StepSpend, but its missing finalization is observable. -/
def writesOnly (n : Nat) (writeCharge : Resources) :
    (theory n).StepSpend Resources where
  graded source target cost := ∃ edge rest matrix,
    source = .active (edge :: rest) matrix ∧
      target = .active rest (insertOccurrence matrix edge) ∧ cost = writeCharge
  sound := by
    rintro source target cost ⟨edge, rest, matrix, rfl, rfl, _⟩
    exact .write edge rest matrix
  resp_left := by
    intro source source' target cost equivalent graded
    change source = source' at equivalent
    subst source'
    exact ⟨target, graded, rfl⟩
  resp_right := by
    intro source target target' cost graded equivalent
    change target = target' at equivalent
    subst target'
    exact graded

/-- Soundness alone does not ensure every construction event has a grade. -/
theorem writesOnly_not_total (n : Nat) (writeCharge : Resources) :
    ¬ (writesOnly n writeCharge).Total := by
  intro total
  obtain ⟨cost, edge, rest, matrix, impossible, _⟩ :=
    total (.finish (AdjacencyMatrix.empty n))
  cases impossible

/-- A missing finish grade blocks the genuine base finalization in the
writer, regardless of the proposed ending account. -/
theorem writesOnly_blocks_finish {n : Nat} (writeCharge before after : Resources)
    (matrix : AdjacencyMatrix.Rep n) :
    (theory n).Step (.active [] matrix) (.done matrix) ∧
      ¬ ((theory n).spendLift (writesOnly n writeCharge)).Step
        (.active [] matrix, before) (.done matrix, after) := by
  constructor
  · exact .finish matrix
  · rintro ⟨cost, ⟨edge, rest, oldMatrix, impossible, _⟩, _⟩
    cases impossible

end Controls

end Mettapedia.GraphTheory.Representation.EdgeListToMatrixCost
