import Mettapedia.Logic.ProofSearch.FirstCertificateExecution
import Mettapedia.Logic.ProofSearch.FiniteCertificateExecutionControls

/-!
# First-certificate execution controls

The original independent checker refuses empty and zero-headed words, accepts
positive claims with a one-headed word and consumes each entire candidate.
Separate selector controls exercise accepted empty certificates and repeated
accepted fields, including retention of the first field's exact word.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Logic.ProofSearch.FirstCertificateExecution.Controls

open Turing
open Mettapedia.Logic.ProofSearch

attribute [local implicit_reducible] FiniteCertificateExecution.Controls.candidateMachine

def searchMachine (claim : Bool) : FinTM2 :=
  letI : Inhabited ((FiniteCertificateExecution.Controls.candidateMachine claim).Γ
      (FiniteCertificateExecution.Controls.candidateMachine claim).k₀) := inferInstanceAs (Inhabited Bool)
  letI : Fintype ((FiniteCertificateExecution.Controls.candidateMachine claim).Γ
      (FiniteCertificateExecution.Controls.candidateMachine claim).k₁) := inferInstanceAs (Fintype Bool)
  Checking.searchMachine (FiniteCertificateExecution.Controls.candidateMachine claim)
    (Equiv.refl Bool) (Equiv.refl Bool)

noncomputable def searchRun (claim : Bool) (bound : Nat) :=
  letI : Inhabited ((FiniteCertificateExecution.Controls.candidateMachine claim).Γ
      (FiniteCertificateExecution.Controls.candidateMachine claim).k₀) := inferInstanceAs (Inhabited Bool)
  letI : Fintype ((FiniteCertificateExecution.Controls.candidateMachine claim).Γ
      (FiniteCertificateExecution.Controls.candidateMachine claim).k₁) := inferInstanceAs (Fintype Bool)
  Checking.search_outputs (FiniteCertificateExecution.Controls.candidateMachine claim)
    (Equiv.refl Bool) (Equiv.refl Bool) FiniteCertificateExecution.Controls.checker claim
    FiniteCertificateExecution.Controls.candidateClock (FiniteCertificateExecution.Controls.candidateRun claim) bound

theorem first_one : CertificateBounds.boundedSearch FiniteCertificateExecution.Controls.checker true 1 = some [1] := rfl

theorem first_two : CertificateBounds.boundedSearch FiniteCertificateExecution.Controls.checker true 2 = some [1] := rfl

theorem first_three : CertificateBounds.boundedSearch FiniteCertificateExecution.Controls.checker true 3 = some [1] := rfl

theorem read_positive : Readout.certificate (Equiv.refl Bool) [.inr true, .inl true] = some [1] := rfl

theorem read_refused : Readout.certificate (Equiv.refl Bool) [.inr false] = none := rfl

theorem read_empty : Readout.certificate (Equiv.refl Bool) [.inr true] = some [] := rfl

theorem read_bad_tag : Readout.certificate (Equiv.refl Bool) [.inr true, .inr true] = none := rfl

def acceptedEmpty := Selection.outputs (Letter := Bool) (fun _ : Unit => []) (fun _ => true) [()]

def refusedEmpty := Selection.outputs (Letter := Bool) (fun _ : Unit => []) (fun _ => false) [()]

def retainedFirst := Selection.outputs (Letter := Bool) (fun value : List Bool × Bool => value.1)
  (fun value => value.2) [([false, false], false), ([true, false], true), ([true], true)]

theorem empty_distinct : Selection.result (Letter := Bool) (some []) ≠ Selection.result none := by decide

end Mettapedia.Logic.ProofSearch.FirstCertificateExecution.Controls
