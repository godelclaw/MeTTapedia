import Mettapedia.Languages.MeTTa.EquationKernel.Certificate
import Mettapedia.Logic.DerivationGraph.CheckedCursor

/-!
# Equation evidence on the shared borrowed graph checker

Rows retain actual source/target Atoms, a supplied equation citation, site and
substitution. The existing `Row.Valid` is the local meaning; no evaluation,
matching search or new inference rule is introduced. A row's numeric premise
positions select its supplied local premise vector, whose entries are resolved
through original source addresses by the shared cursor.

The exact program is a type parameter of checked cursors and judgments. These
laws concern the unrestricted equation-reachability kernel, not HE or PeTTa
evaluation. Native ownership and a textual module decoder remain separate.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.EquationKernel.BorrowedProofCursor

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Logic.DerivationGraph

/-- An original local row instance, independently of its Boolean checker. -/
def rules (program : List Atom) (premises : List Claim) (conclusion : Claim) : Prop :=
  ∃ row, Row.Valid program premises row conclusion

abbrev ruleWitness (program : List Atom) : Mettapedia.Logic.RuleWitness (rules program) where
  W := Row
  isInstance row premises conclusion := decide (row.claim? program premises = some conclusion)
  sound row premises conclusion accepted :=
    ⟨row, (Row.claim?_exact program premises row conclusion).mp (of_decide_eq_true accepted)⟩
  complete premises conclusion valid := by
    obtain ⟨row, valid⟩ := valid
    exact ⟨row, decide_eq_true ((Row.claim?_exact program premises row conclusion).mpr valid)⟩

/-- The generic graph closure has the original equation-derivation meaning. -/
theorem derives_original {program : List Atom} {claim : Claim}
    (derived : Mettapedia.Logic.Derives (rules program) claim) :
    EquationKernel.Derives (spaceOf program) claim.1 claim.2 := by
  apply Mettapedia.Logic.Derives.least
    (fun claim => EquationKernel.Derives (spaceOf program) claim.1 claim.2) ?_ derived
  intro premises conclusion valid earlier
  obtain ⟨row, valid⟩ := valid
  exact valid.derives earlier

abbrev Source := BorrowedCursor.Store Claim Row Nat
abbrev Cursor (program : List Atom) (source : Source) :=
  BorrowedCursor.CheckedCursor (ruleWitness program) source

def begin (program : List Atom) (source : Source) : Cursor program source :=
  BorrowedCursor.CheckedCursor.begin (ruleWitness program) source

/-- Independent local row licensing at the actual addressed source. -/
def LicensedStep (program : List Atom) (source : Source)
    (before after : BorrowedCursor.State Claim) (address : Nat) : Prop :=
  before.revision = source.revision ∧ BorrowedCursor.indexAt before.checked address = none ∧
    ∃ node premises, source.read address = some node ∧
      BorrowedCursor.premiseValues before node.parents = some premises ∧
      Row.Valid program premises node.request node.conclusion ∧
      after = ⟨before.revision, (address, before.cache.size) :: before.checked,
        before.cache.push node.conclusion⟩

theorem step_exact (program : List Atom) (source : Source)
    (before after : BorrowedCursor.State Claim) (address : Nat) :
    BorrowedCursor.step (ruleWitness program) source before address = some after ↔
      LicensedStep program source before after address := by
  constructor
  · intro accepted
    obtain ⟨node, parents, read, resolved, replayed, checked, revision, cache⟩ :=
      BorrowedCursor.step_correspondence (ruleWitness program) source before after address accepted
    obtain ⟨premises, lookup, valid, _⟩ :=
      (Node.replay_eq_some_iff (ruleWitness program) before.cache after.cache
        ⟨node.conclusion, node.request, parents, node.origin⟩).mp replayed
    have current : before.revision = source.revision := by
      by_contra changed
      rw [BorrowedCursor.changed_revision_refused (ruleWitness program) source before address changed]
        at accepted
      cases accepted
    refine ⟨current, BorrowedCursor.step_fresh (ruleWitness program) source before after address accepted,
      node, premises, read, ?_, ?_, ?_⟩
    · exact (BorrowedCursor.premiseValues_resolved before resolved).trans lookup
    · exact (Row.claim?_exact program premises node.request node.conclusion).mp
        (of_decide_eq_true valid)
    · cases after
      simp_all
  · rintro ⟨current, fresh, node, premises, read, values, valid, rfl⟩
    have computed := (Row.claim?_exact program premises node.request node.conclusion).mpr valid
    simp [BorrowedCursor.step, current, fresh, read, values, ruleWitness, computed]

/-- Projected checked roots refer to the original program and exact Atom
judgment; projection never freshens its variables. -/
theorem checked_root_original {program : List Atom} {source : Source}
    (cursor : Cursor program source) (address : Nat) (claim : Claim)
    (found : BorrowedCursor.rootAt cursor.state address = some claim) :
    EquationKernel.Derives (spaceOf program) claim.1 claim.2 := by
  obtain ⟨schedule, checked⟩ := cursor.checkedPrefix
  exact derives_original (BorrowedCursor.root_derivable (ruleWitness program) source schedule
    cursor.state checked address claim found)

/-- The original certificate checker can independently validate every accepted
borrowed root. This existence theorem does not expand certificates at runtime. -/
theorem checked_root_has_certificate {program : List Atom} {source : Source}
    (cursor : Cursor program source) (address : Nat) (claim : Claim)
    (found : BorrowedCursor.rootAt cursor.state address = some claim) :
    ∃ certificate, check program certificate claim = true :=
  exists_check_of_reaches (checked_root_original cursor address claim found).reaches

namespace Controls

private def a : Atom := .symbol "a"
private def b : Atom := .symbol "b"
private def equation : Atom := Atom.equality a b
private def program : List Atom := [equation, equation]

private def source (copy : Nat) : Source :=
  ⟨7, fun address =>
    if address = 101 then some ⟨(a, a), .refl a, [], 101⟩
    else if address = 305 then some ⟨(a, b), .step 0 ⟨equation, copy⟩ [] [], [101], 305⟩
    else if address = 306 then some ⟨(a, a), .trans 0 1, [101, 101], 306⟩
    else none⟩

private def observe (theory : List Atom) (rows : Source) (schedule : List Nat)
    (root : Nat) : Option Claim :=
  (BorrowedCursor.run (ruleWitness theory) rows (BorrowedCursor.start rows) schedule).bind
    fun state => BorrowedCursor.rootAt state root

theorem actual_atoms_checked : observe program (source 0) [101, 305] 305 = some (a, b) := by
  decide

theorem second_equation_copy_checked :
    observe program (source 1) [101, 305] 305 = some (a, b) := by decide

theorem absent_equation_copy_refused : observe program (source 2) [101, 305] 305 = none := by
  decide

theorem changed_program_same_revision_refused :
    observe [] (source 0) [101, 305] 305 = none := by decide

theorem duplicate_premise_occurrences_kept :
    observe program (source 0) [101, 306] 306 = some (a, a) := by decide

theorem forward_source_refused : observe program (source 0) [305, 101] 305 = none := by
  decide

theorem missing_root_refused : observe program (source 0) [101] 305 = none := by decide

private def unrelatedWrite : Source :=
  { source 0 with
    revision := 8
    read := fun address => if address = 999 then some ⟨(b, b), .refl b, [], 999⟩
      else (source 0).read address }

private def changedCheckedRow : Source :=
  { source 0 with read := fun address =>
      if address = 101 then some ⟨(b, b), .refl b, [], 101⟩ else (source 0).read address }

private def firstCursor : Option (Cursor program (source 0)) :=
  (begin program (source 0)).advance [101]

private def validatedSuffix (updated : Source) : Option Claim := do
  let before ← firstCursor
  let checked ← before.revalidate updated
  let after ← checked.advance [305]
  BorrowedCursor.rootAt after.state 305

/-- Unrelated writes may change the coarse revision. The actual checked
prefix remains reusable, and the suffix runs against the new snapshot. -/
theorem unrelated_write_revalidates : validatedSuffix unrelatedWrite = some (a, b) := by
  decide

/-- Equal labels and revisions cannot hide a changed checked source row. -/
theorem changed_checked_row_same_revision_refused : validatedSuffix changedCheckedRow = none := by
  decide

theorem revalidation_preserves_existing_judgment :
    (do
      let before ← firstCursor
      let checked ← before.revalidate unrelatedWrite
      BorrowedCursor.rootAt checked.state 101) = some (a, a) := by decide

end Controls
end Mettapedia.Languages.MeTTa.EquationKernel.BorrowedProofCursor
