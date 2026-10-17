import Mettapedia.Languages.MeTTa.EquationKernel.Certificate
import Mettapedia.Machines.ProductiveCoreAdapters
import Mettapedia.GSLT.Distinction.SimulationComposition

/-!
# Retained execution of equation certificates

The transition uses the existing reverse-table row checker. One transition
inspects one original row; refusal retains the last accepted table and the
entire refused suffix. The theory is the machine parameter, not a field
supplied by a checkpoint. The underlying judgment remains `Reaches` over the
stored equations; this does not assert HE or PeTTa evaluation semantics.
`Work` is raw execution data, not sealed authority. Sound publication below
uses the complete run from `start`; reusing an arbitrary cached table under
another theory requires validation and is not licensed by these theorems.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.EquationKernel.Execution

open Mettapedia.Languages.MeTTa.OSLFCore
open Mettapedia.Machines.ProductiveCoreAdapters
open Mettapedia.GSLT.Distinction.ProductiveBlocks

abbrev Table := List Claim × Nat
abbrev Work := RetainedFold.Work Row Table

def consume (program : List Atom) (table : Table) (row : Row) : Option Table :=
  (row.claimBy? program (revLookup table.1 table.2)).map fun claim =>
    (claim :: table.1, table.2 + 1)

theorem reference_eq (program : List Atom) (table : Table) (rows : List Row) :
    RetainedFold.reference (consume program) table rows = checkRowsRev program table.1 table.2 rows := by
  induction rows generalizing table with
  | nil => rfl
  | cons row rest ih =>
      cases result : row.claimBy? program (revLookup table.1 table.2) with
      | none => simp [RetainedFold.reference, consume, checkRowsRev, result]
      | some claim =>
          simp only [RetainedFold.reference, consume, result, Option.map_some, Option.bind_some,
            checkRowsRev]
          exact ih (claim :: table.1, table.2 + 1)

def start (certificate : Certificate) : Work := RetainedFold.start certificate.rows ([], 0)

def advance (program : List Atom) (budget : Nat) (work : Work) : Work :=
  RetainedFold.advance (consume program) budget work

def verdict (certificate : Certificate) (wanted : Claim) (work : Work) : Bool :=
  match work.result with
  | none => false
  | some table => decide (revLookup table.1 table.2 certificate.root = some wanted)

/-- A completed finite machine run checks precisely the existing certificate,
including unused rows and the final selected root. -/
theorem verdict_exact (program : List Atom) (certificate : Certificate) (wanted : Claim) :
    verdict certificate wanted (advance program certificate.rows.length (start certificate)) =
      check program certificate wanted := by
  unfold verdict advance start
  rw [RetainedFold.complete_exact, reference_eq]
  unfold EquationKernel.check
  cases checkRowsRev program [] 0 certificate.rows with
  | none => rfl
  | some table => cases table; rfl

theorem verdict_sound (program : List Atom) (certificate : Certificate) (wanted : Claim)
    (accepted : verdict certificate wanted
      (advance program certificate.rows.length (start certificate)) = true) :
    Reaches (spaceOf program) wanted.1 wanted.2 :=
  check_sound ((verdict_exact program certificate wanted).symm.trans accepted)

def object (program : List Atom) :
    ObservedMachine (Occurrence Work) Work Empty :=
  ObservedMachine.of (answerMachine (RetainedFold.core (consume program)))

/-- This bound prices calls of the native row worker and the finishing
transition. It leaves matching, substitution and reference traversal costs
to their existing accounts. -/
theorem machine_completes (program : List Atom) (certificate : Certificate) :
    ∃ fuel events report, fuel ≤ certificate.rows.length + 1 ∧
      (object program).machine.run fuel (start certificate) = (events, .finished report) ∧
      report.result = checkRowsRev program [] 0 certificate.rows := by
  obtain ⟨fuel, events, report, count, ran, result⟩ :=
    RetainedFold.machine_completes (consume program) certificate.rows ([], 0)
  exact ⟨fuel, events, report, count, ran, result.trans (reference_eq program ([], 0) certificate.rows)⟩

/-- Any actual finished run, followed by its native root inspection, has
the original certificate verdict. Raw cached tables alone grant no authority. -/
theorem finished_verdict (program : List Atom) (certificate : Certificate) (wanted : Claim)
    {fuel : Nat} {events : List (Occurrence Work)} {report : Work}
    (finished : (object program).machine.run fuel (start certificate) = (events, .finished report)) :
    verdict certificate wanted report = check program certificate wanted := by
  have result := RetainedFold.finished_result (consume program) certificate.rows ([], 0) finished
  unfold verdict
  rw [result, reference_eq]
  unfold EquationKernel.check
  cases checkRowsRev program [] 0 certificate.rows with
  | none => rfl
  | some table => cases table; rfl

theorem finished_sound (program : List Atom) (certificate : Certificate) (wanted : Claim)
    {fuel : Nat} {events : List (Occurrence Work)} {report : Work}
    (finished : (object program).machine.run fuel (start certificate) = (events, .finished report))
    (accepted : verdict certificate wanted report = true) :
    Reaches (spaceOf program) wanted.1 wanted.2 :=
  check_sound ((finished_verdict program certificate wanted finished).symm.trans accepted)

end Mettapedia.Languages.MeTTa.EquationKernel.Execution
