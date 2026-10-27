import Mettapedia.Algorithms.Compression.FramedTree
import Mettapedia.Algorithms.Compression.CostedArtifact

/-!
# Acceptance using the complete encoded artifact

The artifact is the whole recursive record, including its catalogue,
definitions, arguments and residuals. A domain decoder supplies the task
observation, for example the operator environment paired with reconstructed
program occurrences. Every proposal is checked against the original observation.

The finite refinement algorithm selects the cheapest checked artifact among
the initial value and the supplied candidates. This is optimality over that
explicit finite region, not completeness of a template grammar or inverse search.
-/

namespace Mettapedia.Algorithms.Compression.WholeArtifact

open FramedTree

variable {Observation : Type} [DecidableEq Observation]

def validFor (read : Tree → Option Observation) (original candidate : Tree) : Bool :=
  match read original with
  | none => false
  | some observation => decide (read candidate = some observation)

abbrev accept (read : Tree → Option Observation) (original current candidate : Tree) : Option Tree :=
  CostedArtifact.accept (validFor read original) byteLength current candidate

theorem accept_iff (read : Tree → Option Observation) (original current candidate result : Tree) :
    accept read original current candidate = some result ↔
      result = candidate ∧ ∃ observation, read original = some observation ∧
        read current = some observation ∧ read candidate = some observation ∧
        byteLength candidate < byteLength current := by
  cases source : read original with
  | none => simp [accept, validFor, CostedArtifact.accept, source]
  | some observation =>
      simpa [accept, validFor, source] using
        CostedArtifact.accept_iff (validFor read original) byteLength current candidate result

abbrev step (read : Tree → Option Observation) (original current candidate : Tree) : Tree :=
  CostedArtifact.step (validFor read original) byteLength current candidate

theorem step_preserves (read : Tree → Option Observation) (original current candidate : Tree)
    (observation : Observation) (source : read original = some observation)
    (currentValid : read current = some observation) :
    read (step read original current candidate) = some observation ∧
      byteLength (step read original current candidate) ≤ byteLength current := by
  have result := CostedArtifact.step_preserves (validFor read original) byteLength current candidate
    (by simp [validFor, source, currentValid])
  exact ⟨by simpa [validFor, source] using result.1, result.2⟩

theorem accepted_bits_decrease (read : Tree → Option Observation)
    {original current candidate result : Tree}
    (checked : accept read original current candidate = some result) :
    (encode result).length < (encode current).length := by
  obtain ⟨rfl, _, _, _, _, smaller⟩ := (accept_iff read original current candidate result).mp checked
  rw [encoded_length, encoded_length]
  omega

theorem step_le_candidate (read : Tree → Option Observation)
    (original current candidate : Tree) (observation : Observation)
    (source : read original = some observation) (currentValid : read current = some observation)
    (candidateValid : read candidate = some observation) :
    byteLength (step read original current candidate) ≤ byteLength candidate := by
  exact CostedArtifact.step_le_candidate (validFor read original) byteLength current candidate
    (by simp [validFor, source, currentValid]) (by simp [validFor, source, candidateValid])

abbrev refine (read : Tree → Option Observation) (original : Tree) : Tree → List Tree → Tree :=
  CostedArtifact.refine (validFor read original) byteLength

theorem refine_append (read : Tree → Option Observation) (original current : Tree)
    (first second : List Tree) :
    refine read original current (first ++ second) =
      refine read original (refine read original current first) second := by
  exact CostedArtifact.refine_append (validFor read original) byteLength current first second

theorem refine_preserves (read : Tree → Option Observation) (original current : Tree)
    (candidates : List Tree) (observation : Observation)
    (source : read original = some observation) (currentValid : read current = some observation) :
    read (refine read original current candidates) = some observation ∧
      byteLength (refine read original current candidates) ≤ byteLength current := by
  have result := CostedArtifact.refine_preserves (validFor read original) byteLength current candidates
    (by simp [validFor, source, currentValid])
  exact ⟨by simpa [validFor, source] using result.1, result.2⟩

theorem refine_optimal_in_region (read : Tree → Option Observation) (original current : Tree)
    (candidates : List Tree) (observation : Observation)
    (source : read original = some observation) (currentValid : read current = some observation) :
    ∀ candidate ∈ candidates, read candidate = some observation →
      byteLength (refine read original current candidates) ≤ byteLength candidate := by
  intro candidate member valid
  exact CostedArtifact.refine_optimal_in_region (validFor read original) byteLength current candidates
    (by simp [validFor, source, currentValid]) candidate member (by simp [validFor, source, valid])

theorem changed_observation_refused (read : Tree → Option Observation)
    (original current candidate : Tree) (observation : Observation)
    (source : read original = some observation) (changed : read candidate ≠ some observation) :
    accept read original current candidate = none := by
  simp [accept, validFor, CostedArtifact.accept, source, changed]

theorem no_gain_refused (read : Tree → Option Observation)
    (original current candidate : Tree) (noGain : byteLength current ≤ byteLength candidate) :
    accept read original current candidate = none := by
  exact CostedArtifact.no_gain_refused (validFor read original) byteLength current candidate noGain

end Mettapedia.Algorithms.Compression.WholeArtifact
