import Mettapedia.GSLT.Dynamics.NaturalBackendAdmission
import Mettapedia.OSLF.NativeTypes.Instances.Natural.Authored

/-!
# Guarded word execution of the authored natural counter

The finite-word backend chooses an actual word result or an unbounded fallback.
Decoding that choice implements exactly the counter rule read from the module.
Finite executions cover precisely the authored counter states, and the existing
finite native query retains its infinite-path meaning for this implementation.

This is a Lean backend qualification. It does not identify Lean's word runtime
with CeTTa's C arithmetic or change the numeric policies of any MeTTa dialect.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Instances.Natural.Backend

open Mettapedia.GSLT.Dynamics.NaturalBackendAdmission
open Mettapedia.GSLT.LanguageDef.Examples
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.Logic.ModalMuCalculus
open Mettapedia.OSLF.NativeTypes.Semantics.ModalFormula
open Mettapedia.OSLF.NativeTypes.Semantics.SuccessorObservation
open Mettapedia.OSLF.NativeTypes.Decision
open Mettapedia.OSLF.NativeTypes.Executable
open Mettapedia.GSLT.LanguageDef.CertificateGSLT.MuCalculusBoundary
open Reference.Core (Outcome)

def advance (number : Nat) : Nat :=
  Sum.elim UInt64.toNat id (successorBackend.compile () number)

theorem advance_exact (number : Nat) : advance number = number + 1 :=
  successorBackend_exact number

def execute : Nat → Nat → Nat
  | 0, number => number
  | rounds + 1, number => execute rounds (advance number)

theorem execute_exact (rounds number : Nat) : execute rounds number = number + rounds := by
  induction rounds generalizing number with
  | zero => rfl
  | succ rounds ih =>
    simp only [execute, ih, advance_exact]
    omega

/-- Each implemented successor is exactly the source rule's only target. -/
theorem authored_step_iff (base : BasePremiseEvaluator) (number : Nat) (target : Pattern) :
    Step base Mettapedia.GSLT.LanguageDef.Examples.NativeNaturalCounter.language
      (NativeNaturalCounter.counter number) target ↔
    target = NativeNaturalCounter.counter (advance number) := by
  rw [advance_exact]
  exact NativeNaturalCounter.counter_step_target_iff base number target

theorem authored_finite_execution_iff (base : BasePremiseEvaluator)
    (number : Nat) (target : Pattern) :
    (Authored.theory base).MultiStep (NativeNaturalCounter.counter number) target ↔
      ∃ rounds, target = NativeNaturalCounter.counter (execute rounds number) := by
  simp only [execute_exact]
  exact Authored.finite_run_iff base number target

/-- The finite query describes the actual implemented successor, with its
checked word/fallback choice, for every natural input including overflow. -/
theorem check_buchi_iff (phases : Finset (Fin 2)) (budget number : Nat)
    (enough : FiniteMuCalculus.requiredBudget (State := Fin 2)
      (Formula.buchi Traversal.future) ≤ budget) :
    (Finite.check Counter.table (Formula.buchi .future) (fun _ => phases)
      budget (Counter.phase number)).map Outcome.answer = some (some true) ↔
    BuchiPath (transitionSystem (span advance)) .future
      (Counter.phase ⁻¹' (↑phases : Set (Fin 2))) number := by
  have commutes (value : Nat) : Counter.phase (advance value) = Counter.toggle (Counter.phase value) := by
    rw [advance_exact]
    exact (Counter.phase_successor value).symm
  exact (Finite.check_buchi_iff Counter.table phases budget (Counter.phase number) enough).trans
    (Semantics.SuccessorObservation.buchi_iff advance Counter.toggle Counter.phase
      commutes (↑phases : Set (Fin 2)) number)

theorem crosses_word_boundary : execute 2 (UInt64.size - 2) = UInt64.size := by
  rw [execute_exact]
  decide

theorem no_wrap_at_word_boundary : advance (UInt64.size - 1) ≠ 0 := by
  rw [advance_exact]
  decide

end Mettapedia.OSLF.NativeTypes.Instances.Natural.Backend
