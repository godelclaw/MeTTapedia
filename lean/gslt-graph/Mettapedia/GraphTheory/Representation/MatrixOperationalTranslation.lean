import Mettapedia.GraphTheory.Representation.MatrixBridge
import Mettapedia.GSLT.Core.IndexedOperational

/-!
# Operational contracts between graph lookup representations

The graph-matrix and raw-matrix lookup GSLTs have an exact local operational
translation. In contrast, linear scanning and one-cell lookup do not admit
a translation sending every scan step to one lookup step. Their proved
agreement on complete query answers remains valid; their primitive execution
granularities differ.
-/

namespace Mettapedia.GraphTheory.Representation.MatrixOperationalTranslation

open Mettapedia.GSLT
open Mettapedia.GSLT.IndexedOperational
open Mettapedia.GSLT.Core.ClosureCriteria
open MatrixBridge

/-- A graph-matrix query is hosted exactly by the raw Boolean matrix GSLT.
Target steps leaving an encoded state are reconstructed as source steps. -/
def embedding (n : Nat) :
    CoveredTranslation (AdjacencyMatrix.theory n) (matrixTheory n) where
  mapTerm := encodeState
  mapEquiv := by
    intro first second equal
    change first = second at equal
    exact congrArg encodeState equal
  cover :=
    { mapStep := encode_step
      liftStep := by
        intro source target step
        obtain ⟨represented, original, same⟩ :=
          (matrix_step_from_encoded_iff source target).mp step
        exact ⟨represented, original, same.symm⟩ }

theorem matrix_one_step_terminal (n : Nat) : OneStepTerminal (AdjacencyMatrix.theory n) where
  target_normal := by
    intro source target step
    cases step
    exact AdjacencyMatrix.answer_normal (n := n) _

/-- An absent path-edge query has two composable scanning transitions. -/
def scan_has_two_steps :
    ComposableStepWitness (LinearProbe.theory (@EdgeList.accepts 3)) where
  source := .scan (EdgeList.Canary.v0, EdgeList.Canary.v2) EdgeList.Canary.path3.entries
  middle := .scan (EdgeList.Canary.v0, EdgeList.Canary.v2)
    [⟨EdgeList.Canary.v1, EdgeList.Canary.v2⟩]
  target := .scan (EdgeList.Canary.v0, EdgeList.Canary.v2) []
  first := .skip (by decide)
  second := .skip (by decide)

/-- A change from scanning to one-cell lookup must use a weaker execution
contract than preserving every primitive step. This does not obstruct the
verified representation conversions or their colouring transport. -/
theorem no_scan_to_matrix_step_translation (n : Nat) :
    ¬ Nonempty (OperationalTranslation
      (LinearProbe.theory (@EdgeList.accepts 3)) (AdjacencyMatrix.theory n)) :=
  OperationalTranslation.no_translation_to_oneStepTerminal
    ⟨scan_has_two_steps⟩ (matrix_one_step_terminal n)

end Mettapedia.GraphTheory.Representation.MatrixOperationalTranslation
