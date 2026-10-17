import Mettapedia.Languages.ProcessCalculi.RhoCalculus.NativeKernel
import Mettapedia.OSLF.NativeTypes.Certificates.FiniteTreeExecution

/-!
# Retained native rho inference checking

The raw occurrence machine retains rho's existing judgment and rule types.
Its COMM computation is the original semantic substitution operation.
Endpoint formation and ambient scope are checked separately at the request
boundary. The bounds count rho inference occurrences, not the internal cost
of semantic substitution, endpoint formation or structural equality.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.NativeExecution

open NativeEvidence
open Mettapedia.OSLF.NativeTypes.Certificates

local instance : DecidableEq presentation.Judgment := inferInstanceAs (DecidableEq Judgment)

def rawObject := TreeExecution.object (P := presentation)

def checkFormed (claim : NativeKernel.Claim) (proof : Proof) : Bool :=
  NativeKernel.checkAdmission claim.context claim.sort claim.judgment &&
    (TreeExecution.advance (TreeExecution.nodes proof)
      (TreeExecution.start proof claim.judgment)).accepted

theorem checkFormed_exact (claim : NativeKernel.Claim) (proof : Proof) :
    checkFormed claim proof = true ↔
      NativeKernel.Admission claim.context claim.sort claim.judgment ∧
        ∃ derivation : Derivation claim.judgment, Tree.erase derivation = proof := by
  simp only [checkFormed, TreeExecution.accepted_iff (P := presentation) proof claim.judgment, Bool.and_eq_true,
    NativeKernel.checkAdmission_exact, Tree.check_exact (P := presentation) proof claim.judgment]

theorem checkFormed_sound (claim : NativeKernel.Claim) (proof : Proof)
    (accepted : checkFormed claim proof = true) : NativeKernel.Meaning claim := by
  obtain ⟨admitted, derivation, _⟩ := (checkFormed_exact claim proof).mp accepted
  exact ⟨admitted, derivation_sound derivation⟩

theorem checkFormed_coverage (claim : NativeKernel.Claim) :
    (∃ proof, checkFormed claim proof = true) ↔ NativeKernel.Meaning claim := by
  constructor
  · rintro ⟨proof, accepted⟩
    exact checkFormed_sound claim proof accepted
  · rintro ⟨admitted, meaningful⟩
    obtain ⟨derivation⟩ := (meaning_iff_derivation claim.judgment).mp meaningful
    exact ⟨Tree.erase derivation,
      (checkFormed_exact claim _).mpr ⟨admitted, derivation, rfl⟩⟩

/-- The raw checker executes its own source rules, with ordered occurrences
and retained refusal. Formation is an additional request-boundary check. -/
theorem raw_machine_completes (proof : Proof) (claim : Judgment) :
    ∃ fuel events report, fuel ≤ TreeExecution.nodes proof + 1 ∧
      rawObject.machine.run fuel (TreeExecution.start proof claim) = (events, .finished report) ∧
      report.accepted = NativeEvidence.check claim proof :=
  TreeExecution.machine_completes proof claim

theorem raw_finished_exact (proof : Proof) (claim : Judgment) {fuel : Nat}
    {events : List (Mettapedia.Machines.ProductiveCoreAdapters.Occurrence (TreeExecution.Work presentation))}
    {report : TreeExecution.Work presentation}
    (finished : rawObject.machine.run fuel (TreeExecution.start proof claim) = (events, .finished report)) :
    report.accepted = NativeEvidence.check claim proof :=
  TreeExecution.finished_accepted (P := presentation) proof claim finished

theorem formed_finished_sound (claim : NativeKernel.Claim) (proof : Proof) {fuel : Nat}
    {events : List (Mettapedia.Machines.ProductiveCoreAdapters.Occurrence (TreeExecution.Work presentation))}
    {report : TreeExecution.Work presentation}
    (admitted : NativeKernel.checkAdmission claim.context claim.sort claim.judgment = true)
    (finished : rawObject.machine.run fuel (TreeExecution.start proof claim.judgment) = (events, .finished report))
    (accepted : report.accepted = true) : NativeKernel.Meaning claim :=
  ⟨(NativeKernel.checkAdmission_exact _ _ _).mp admitted,
    NativeEvidence.check_sound _ _ ((raw_finished_exact proof claim.judgment finished).symm.trans accepted)⟩

namespace Controls

theorem native_comm_accepted (channel payload body : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
    (rest : List Mettapedia.OSLF.MeTTaIL.Syntax.Pattern) :
    (TreeExecution.advance (TreeExecution.nodes (commProof channel payload body rest))
      (TreeExecution.start (commProof channel payload body rest)
        (conclusion (.comm channel payload body rest)))).accepted = true := by
  exact (TreeExecution.accepted_iff (P := presentation) (commProof channel payload body rest)
    (conclusion (.comm channel payload body rest))).trans
      (communicate_checked channel payload body rest)

theorem changed_goal_refused :
    (TreeExecution.advance (TreeExecution.nodes (NativeEvidence.Controls.singleton NativeEvidence.Controls.zero))
      (TreeExecution.start (NativeEvidence.Controls.singleton NativeEvidence.Controls.zero)
        (.step NativeEvidence.Controls.zero NativeEvidence.Controls.zero))).accepted = false := by decide

end Controls
end Mettapedia.Languages.ProcessCalculi.RhoCalculus.NativeExecution
