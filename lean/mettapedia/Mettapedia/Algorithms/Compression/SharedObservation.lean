import Mettapedia.Algorithms.Compression.CostedArtifact

/-! Operation-local sharing for a deterministic artifact decoder. Equality is
on the complete artifact, never on approximate observations. No observation
from a previous operation is trusted. The read counter records decoder
applications, not native allocations or evaluator transitions. -/

set_option autoImplicit false

namespace Mettapedia.Algorithms.Compression.SharedObservation

variable {Artifact Observation : Type} [DecidableEq Artifact]

structure Batch (Observation : Type) where
  source : Option Observation
  before : Option Observation
  after : Option Observation
  reads : Nat
  deriving DecidableEq, Repr

def separate (read : Artifact → Option Observation) (original current candidate : Artifact) :
    Batch Observation :=
  ⟨read original, read current, read candidate, 3⟩

def shared (read : Artifact → Option Observation) (original current candidate : Artifact) :
    Batch Observation :=
  let source := read original
  let before := if current = original then (source, 0) else (read current, 1)
  let after := if candidate = original then (source, 0)
    else if candidate = current then (before.1, 0) else (read candidate, 1)
  ⟨source, before.1, after.1, 1 + before.2 + after.2⟩

def values (batch : Batch Observation) :
    Option Observation × Option Observation × Option Observation :=
  (batch.source, batch.before, batch.after)

theorem shared_values (read : Artifact → Option Observation) (original current candidate : Artifact) :
    values (shared read original current candidate) = values (separate read original current candidate) := by
  by_cases sameCurrent : current = original
  · subst current
    by_cases sameCandidate : candidate = original
    · subst candidate
      simp [shared, separate, values]
    · simp [shared, separate, values, sameCandidate]
  · by_cases sameOriginal : candidate = original
    · subst candidate
      simp [shared, separate, values, sameCurrent]
    · by_cases sameCandidate : candidate = current
      · subst candidate
        simp [shared, separate, values, sameCurrent]
      · simp [shared, separate, values, sameCurrent, sameOriginal, sameCandidate]

theorem shared_reads_le_three (read : Artifact → Option Observation)
    (original current candidate : Artifact) :
    1 ≤ (shared read original current candidate).reads ∧
      (shared read original current candidate).reads ≤ 3 := by
  unfold shared
  split <;> split <;> simp_all
  split <;> simp_all

theorem all_equal_reads_once (read : Artifact → Option Observation) (original : Artifact) :
    (shared read original original original).reads = 1 := by simp [shared]

theorem original_current_equal_reads_twice (read : Artifact → Option Observation)
    (original candidate : Artifact) (different : candidate ≠ original) :
    (shared read original original candidate).reads = 2 := by simp [shared, different]

theorem all_distinct_reads_three (read : Artifact → Option Observation)
    (original current candidate : Artifact) (first : current ≠ original)
    (second : candidate ≠ original) (third : candidate ≠ current) :
    (shared read original current candidate).reads = 3 := by simp [shared, first, second, third]

inductive Decision (Artifact : Type) where
  | invalid
  | reconstruction
  | notSmaller
  | accepted (artifact : Artifact) (before after : Nat)
  deriving DecidableEq, Repr

def classify (policy : Observation → Observation → Bool) (cost : Artifact → Nat)
    (current candidate : Artifact)
    (observations : Option Observation × Option Observation × Option Observation) : Decision Artifact :=
  match observations with
  | (some source, some before, some after) =>
      if policy source before && policy source after then
        if cost candidate < cost current then .accepted candidate (cost current) (cost candidate)
        else .notSmaller
      else .reconstruction
  | _ => .invalid

def check (read : Artifact → Option Observation) (policy : Observation → Observation → Bool)
    (cost : Artifact → Nat) (original current candidate : Artifact) : Decision Artifact :=
  classify policy cost current candidate (values (separate read original current candidate))

def sharedCheck (read : Artifact → Option Observation) (policy : Observation → Observation → Bool)
    (cost : Artifact → Nat) (original current candidate : Artifact) : Decision Artifact :=
  classify policy cost current candidate (values (shared read original current candidate))

theorem sharedCheck_eq (read : Artifact → Option Observation) (policy : Observation → Observation → Bool)
    (cost : Artifact → Nat) (original current candidate : Artifact) :
    sharedCheck read policy cost original current candidate = check read policy cost original current candidate := by
  unfold sharedCheck check
  rw [shared_values]

def validFor (read : Artifact → Option Observation) (policy : Observation → Observation → Bool)
    (original artifact : Artifact) : Bool :=
  match read original, read artifact with
  | some source, some observed => policy source observed
  | _, _ => false

/-- The optimized decision realizes the existing fixed-task refinement
criterion. No symmetry or transitivity of the domain policy is required. -/
theorem shared_accept_iff (read : Artifact → Option Observation)
    (policy : Observation → Observation → Bool) (cost : Artifact → Nat)
    (original current candidate : Artifact) :
    sharedCheck read policy cost original current candidate =
        .accepted candidate (cost current) (cost candidate) ↔
      CostedArtifact.accept (validFor read policy original) cost current candidate = some candidate := by
  rw [sharedCheck_eq, CostedArtifact.accept_iff]
  cases source : read original <;> cases before : read current <;> cases after : read candidate <;>
    simp [check, values, separate, classify, validFor, source, before, after]
  split
  · split <;> simp_all
  · simp_all

/-- Both the current and proposed observations are compared with the original
task, even when the policy is not transitive. -/
theorem changed_original_policy_refused (read : Artifact → Option Observation)
    (policy : Observation → Observation → Bool) (cost : Artifact → Nat)
    (original current candidate : Artifact) (source before after : Observation)
    (readSource : read original = some source) (readBefore : read current = some before)
    (readAfter : read candidate = some after) (rejected : policy source after = false) :
    sharedCheck read policy cost original current candidate = .reconstruction := by
  rw [sharedCheck_eq]
  simp [check, values, separate, classify, readSource, readBefore, readAfter, rejected]

theorem accepted_complete_cost_decreases (read : Artifact → Option Observation)
    (policy : Observation → Observation → Bool) (cost : Artifact → Nat)
    (original current candidate result : Artifact) (before after : Nat)
    (accepted : sharedCheck read policy cost original current candidate = .accepted result before after) :
    result = candidate ∧ before = cost current ∧ after = cost candidate ∧ after < before := by
  rw [sharedCheck_eq] at accepted
  unfold check values separate classify at accepted
  split at accepted <;> try contradiction
  split at accepted <;> try contradiction
  split at accepted <;> try contradiction
  cases accepted
  exact ⟨rfl, rfl, rfl, by assumption⟩

end Mettapedia.Algorithms.Compression.SharedObservation
