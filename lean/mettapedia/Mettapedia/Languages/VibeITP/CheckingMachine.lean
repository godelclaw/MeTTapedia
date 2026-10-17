import Mettapedia.Languages.VibeITP.Presentation.OSLFBridge
import Mettapedia.GSLT.LanguageDef.CertificateGSLTClassifyingCategory
import Mettapedia.GSLT.LanguageDef.CertificateGSLTBorrowedCursor
import Mettapedia.GSLT.LanguageDef.ModuleFormat.Portable

/-!
# Checking realizations of the VibeITP presentation

The independent source calculus and its semantic comparison remain upstream.
This adapter realizes their finite rule instances as shared proof graphs and
retained source-address checking, and loads their complete portable presentation.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.VibeITP.CheckingMachine

open _root_.CategoryTheory
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.Languages.VibeITP.Presentation
open Mettapedia.Languages.VibeITP.Spec

/-- Native theorem derivability is a closed arrow in the existing proof
category. This is a proof-structure comparison, independent of the checking
machine and its navigation representation. -/
theorem kernel_derives_iff_classifyingArrow {T : Theory} {n : Nat}
    (hosted : Hosted T n) (statement : Term) :
    Derives T statement ↔
      Nonempty ((⟨[]⟩ : CertificateGSLT.ClassifyingContext (kernelValidated T n)) ⟶
        ⟨[jThm (encTerm T.sig statement)]⟩) := by
  let comparison := CertificateGSLT.ClassifyingContext.closedDerivationEquiv
    (kernelValidated T n) (jThm (encTerm T.sig statement))
  constructor
  · intro original
    obtain ⟨article, accepted⟩ := (derives_iff_checkRaw hosted statement).mp original
    obtain ⟨proof⟩ := checkRaw_soundness accepted
    exact ⟨comparison proof⟩
  · rintro ⟨arrow⟩
    let proof := comparison.symm arrow
    exact (derives_iff_checkRaw hosted statement).mpr ⟨proof.erase, checkRaw_erase proof⟩

/-! ## The same kernel on the retained source-address checker -/

/-- The selected VibeITP theory, including its original auxiliary operation
judgments, uses the common machine without changing its source rule schemas.
The theory is the actual validated package, not a caller-supplied theory tag. -/
def kernelCheckingObject (T : Theory) (n : Nat)
    (source : CertificateGSLT.BorrowedCursor.Source) :=
  CertificateGSLT.BorrowedCursor.checkingObject (kernelValidated T n) source

/-- The complete selected kernel as portable module data. Both the term
language and the authored judgment/rule layer are retained. -/
def kernelModule (T : Theory) (n : Nat) : String :=
  ModuleFormat.Portable.renderCalculus (kernelValidated T n).val

/-- The actual verified text reader and original validator recover the exact
package used by the common checker, including the selected theory's premises. -/
theorem kernelModule_read (T : Theory) (n : Nat) :
    ModuleFormat.Portable.readValidatedCalculus? (kernelModule T n) =
      some (kernelValidated T n) :=
  ModuleFormat.Portable.readValidatedCalculus_renderCalculus _

/-- Coverage on common proof graphs is exactly the independent static VibeITP
judgment. This relates certificate representations; it does not extract an
efficient article from an erased proof of derivability. -/
theorem kernel_derives_iff_graph {T : Theory} {n : Nat}
    (hosted : Hosted T n) (statement : Term) :
    Derives T statement ↔
      ∃ (nodes : List (Mettapedia.Logic.DerivationGraph.Node Pattern
          (CertificateGSLT.BorrowedCursor.AdmittedInstance (kernelValidated T n)) Nat))
        (cache : Array Pattern) (root : Nat),
        Mettapedia.Logic.DerivationGraph.replay
          (CertificateGSLT.BorrowedCursor.presentation (kernelValidated T n)).ruleWitness nodes = some cache ∧
          cache[root]? = some (jThm (encTerm T.sig statement)) := by
  rw [derives_iff_checkRaw hosted statement]
  constructor
  · rintro ⟨article, accepted⟩
    exact (CertificateGSLT.BorrowedCursor.authored_source_and_graph
      ⟨kernelValidated T n⟩ _).2.mp (checkRaw_soundness accepted)
  · intro graph
    obtain ⟨derivation⟩ := (CertificateGSLT.BorrowedCursor.authored_source_and_graph
      ⟨kernelValidated T n⟩ _).2.mpr graph
    exact ⟨derivation.erase, checkRaw_erase derivation⟩

/-- A root retained by the actual common source-address worker proves the
independently specified VibeITP statement under precisely the selected theory. -/
theorem kernel_checked_root_derives {T : Theory} {n : Nat}
    (hosted : Hosted T n) (source : CertificateGSLT.BorrowedCursor.Source)
    (cursor : CertificateGSLT.BorrowedCursor.Cursor (kernelValidated T n) source)
    (address : Nat) (statement : Term)
    (found : Mettapedia.Logic.DerivationGraph.BorrowedCursor.rootAt cursor.state address =
      some (jThm (encTerm T.sig statement))) : Derives T statement := by
  obtain ⟨article, accepted⟩ := CertificateGSLT.BorrowedCursor.checked_root_has_source_certificate
    (kernelValidated T n) source cursor address _ found
  exact (derives_iff_checkRaw hosted statement).mpr ⟨article, accepted⟩

/-- A whole successful worker run checks all requested rows, including unused
ones. Refusal of a suffix and incomplete work do not publish success. -/
theorem kernel_finished_iff_licensed (T : Theory) (n : Nat)
    (source : CertificateGSLT.BorrowedCursor.Source)
    (cursor : CertificateGSLT.BorrowedCursor.Cursor (kernelValidated T n) source)
    (schedule : List Nat) :
    (∃ fuel events report, (kernelCheckingObject T n source).machine.run fuel
      (Mettapedia.Machines.Cursor.ProofChecking.start cursor schedule) =
        (events, .finished report) ∧ report.accepted = true) ↔
      ∃ after, CertificateGSLT.BorrowedCursor.LicensedRun
        (kernelValidated T n) source cursor.state schedule after :=
  CertificateGSLT.BorrowedCursor.finished_iff_licensed (kernelValidated T n) source cursor schedule

namespace CursorControls

private def source : CertificateGSLT.BorrowedCursor.Source :=
  ⟨0, fun address => if address = 0 then
    some ⟨0, ⟨⟨"vibe-psucc-1"⟩, []⟩, []⟩ else none⟩

private def completed (schedule : List Nat) : Option Bool :=
  Mettapedia.Machines.Cursor.ProofChecking.completedVerdict
    ((CertificateGSLT.BorrowedCursor.checkingObject kernelFixedValidated source).machine.run
      (schedule.length + 2) (Mettapedia.Machines.Cursor.ProofChecking.start
        (CertificateGSLT.BorrowedCursor.begin kernelFixedValidated source) schedule)).2

theorem original_auxiliary_rule_accepts : completed [0] = some true := by decide +kernel

theorem missing_source_row_refuses : completed [1] = some false := by decide +kernel

theorem bad_unused_suffix_refuses : completed [0, 1] = some false := by decide +kernel

theorem repeated_source_definition_refuses : completed [0, 0] = some false := by decide +kernel

def verdicts : List (String × Bool) :=
  [("VibeITP original auxiliary rule", decide (completed [0] = some true)),
   ("VibeITP missing source row", decide (completed [1] = some false)),
   ("VibeITP bad unused suffix", decide (completed [0, 1] = some false)),
   ("VibeITP repeated source definition", decide (completed [0, 0] = some false)),
   ("VibeITP portable kernel load", (ModuleFormat.Portable.readValidatedCalculus?
      (ModuleFormat.Portable.renderCalculus kernelFixedValidated.val)).isSome),
   ("malformed calculus module", (ModuleFormat.Portable.readValidatedCalculus?
      "(module:document malformed)").isNone)]

end CursorControls

end Mettapedia.Languages.VibeITP.CheckingMachine
