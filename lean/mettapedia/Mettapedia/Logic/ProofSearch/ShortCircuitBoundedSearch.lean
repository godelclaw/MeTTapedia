import Mettapedia.Logic.ProofSearch.ShortCircuitCertificateExecution

/-!
# Physical bounded enumeration followed by early-stop certificate checking

The existing binary-word enumerator is joined to the early-stop checker caller.
The one-clock account charges the full enumerator and its physical output
handoff, then checker calls only through the first accepted word, then unread
input cleanup. Generating every bounded candidate still costs exponential work
in the depth parameter. No efficient proof-discovery or eager-generation
avoidance claim is made.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Mettapedia.Logic.ProofSearch.ShortCircuitBoundedSearch
open Turing StateTransition
open Mettapedia.Computability
open Mettapedia.GSLT.LanguageDef.KernelAuthority

variable {Claim : Type} (program : FinTM2)
  (inputAlphabet : program.Γ program.k₀ ≃ Bool)
  (outputAlphabet : program.Γ program.k₁ ≃ Bool)
  [Inhabited (program.Γ program.k₀)] [Fintype (program.Γ program.k₁)]

abbrev encode := FirstCertificateExecution.Checking.encodeCertificate program inputAlphabet

def decode (word : List (program.Γ program.k₀)) : List (Fin 2) :=
  word.map (finTwoEquiv.symm ∘ inputAlphabet)

omit [Inhabited (program.Γ program.k₀)] [Fintype (program.Γ program.k₁)] in
theorem decode_encode (word : List (Fin 2)) : decode program inputAlphabet (encode program inputAlphabet word) = word := by
  simp [decode, encode, FirstCertificateExecution.Checking.encodeCertificate,
    FiniteCertificateExecution.Checking.encodeCertificate, List.map_map, Function.comp_def]

omit [Inhabited (program.Γ program.k₀)] [Fintype (program.Γ program.k₁)] in
theorem encode_decode (word : List (program.Γ program.k₀)) : encode program inputAlphabet (decode program inputAlphabet word) = word := by
  simp [decode, encode, FirstCertificateExecution.Checking.encodeCertificate,
    FiniteCertificateExecution.Checking.encodeCertificate, List.map_map, Function.comp_def]

def caller : FinTM2 := ShortCircuitCertificateExecution.machine program outputAlphabet

def bridge : FiniteCertificateExecution.machine.Γ FiniteCertificateExecution.machine.k₁ ≃
    (caller program outputAlphabet).Γ (caller program outputAlphabet).k₀ :=
  Equiv.optionCongr inputAlphabet.symm

local instance : Fintype (FiniteCertificateExecution.machine.Γ FiniteCertificateExecution.machine.k₁) :=
  inferInstanceAs (Fintype (Option Bool))
local instance : Inhabited (FiniteCertificateExecution.machine.Γ FiniteCertificateExecution.machine.k₁) := ⟨none⟩

def machine : FinTM2 := StackMachineComposition.machine FiniteCertificateExecution.machine
  (caller program outputAlphabet) (bridge program inputAlphabet outputAlphabet)

def candidates (bound : Nat) : List (List (program.Γ program.k₀)) :=
  (CertificateBounds.wordsUpTo 2 bound).map (encode program inputAlphabet)

def accepts (checker : Checker Claim (List (Fin 2))) (claim : Claim)
    (word : List (program.Γ program.k₀)) : Bool := checker.check claim (decode program inputAlphabet word)

def clock (checker : Checker Claim (List (Fin 2))) (claim : Claim)
    (checkerClock : List (Fin 2) → Nat) (bound : Nat) : Nat :=
  FiniteCertificateExecution.enumerationTime bound +
    2 * (FiniteCertificateExecution.wire (FiniteCertificateExecution.words bound)).length +
    ShortCircuitCertificateExecution.searchClock program (accepts program inputAlphabet checker claim)
      (checkerClock ∘ decode program inputAlphabet) (candidates program inputAlphabet bound) + 2

theorem enumeration_frame (bound : Nat) :
    (FiniteCertificateExecution.wire (FiniteCertificateExecution.words bound)).map
      (bridge program inputAlphabet outputAlphabet) =
      ShortCircuitCertificateExecution.frame program (candidates program inputAlphabet bound) := by
  exact FirstCertificateExecution.Checking.enumeration_frame program inputAlphabet outputAlphabet bound

omit [Inhabited (program.Γ program.k₀)] [Fintype (program.Γ program.k₁)] in
theorem first_result (checker : Checker Claim (List (Fin 2))) (claim : Claim) (bound : Nat) :
    (candidates program inputAlphabet bound).find? (accepts program inputAlphabet checker claim) =
      (CertificateBounds.boundedSearch checker claim bound).map (encode program inputAlphabet) := by
  simp only [candidates, List.find?_map, accepts, Function.comp_def, decode_encode,
    CertificateBounds.boundedSearch, CertificateBounds.finiteSearch_eq_find?]

noncomputable def callerOutputs (checker : Checker Claim (List (Fin 2))) (claim : Claim)
    (checkerClock : List (Fin 2) → Nat)
    (runs : ∀ certificate, TM2OutputsInTime program (encode program inputAlphabet certificate)
      (some [outputAlphabet.symm (checker.check claim certificate)]) (checkerClock certificate)) (bound : Nat) :
    TM2OutputsInTime (caller program outputAlphabet)
      (ShortCircuitCertificateExecution.frame program (candidates program inputAlphabet bound))
      (some (FirstCertificateExecution.Selection.result
        ((CertificateBounds.boundedSearch checker claim bound).map (encode program inputAlphabet))))
      (ShortCircuitCertificateExecution.searchClock program (accepts program inputAlphabet checker claim)
        (checkerClock ∘ decode program inputAlphabet) (candidates program inputAlphabet bound)) := by
  have source : ∀ word, TM2OutputsInTime program word
      (some [outputAlphabet.symm (checker.check claim (decode program inputAlphabet word))])
      (checkerClock (decode program inputAlphabet word)) := by
    intro word
    simpa only [encode_decode] using runs (decode program inputAlphabet word)
  have checked := ShortCircuitCertificateExecution.searchOutputs program outputAlphabet
    (fun word => outputAlphabet.symm (checker.check claim (decode program inputAlphabet word)))
    (checkerClock ∘ decode program inputAlphabet) source (candidates program inputAlphabet bound)
  simp only [Function.comp_def, Equiv.apply_symm_apply] at checked
  rw [← first_result program inputAlphabet checker claim bound]
  exact checked

/-- One actual finite machine returns the original first accepted bounded
certificate. All enumeration and handoff work is charged, even on early success. -/
noncomputable def outputs (checker : Checker Claim (List (Fin 2))) (claim : Claim)
    (checkerClock : List (Fin 2) → Nat)
    (runs : ∀ certificate, TM2OutputsInTime program (encode program inputAlphabet certificate)
      (some [outputAlphabet.symm (checker.check claim certificate)]) (checkerClock certificate)) (bound : Nat) :
    TM2OutputsInTime (machine program inputAlphabet outputAlphabet) (List.replicate bound none)
      (some (FirstCertificateExecution.Selection.result
        ((CertificateBounds.boundedSearch checker claim bound).map (encode program inputAlphabet))))
      (clock program inputAlphabet checker claim checkerClock bound) := by
  have checked := callerOutputs program inputAlphabet outputAlphabet checker claim checkerClock runs bound
  rw [← enumeration_frame program inputAlphabet outputAlphabet bound] at checked
  have joined := StackMachineComposition.outputs FiniteCertificateExecution.machine
    (caller program outputAlphabet) (bridge program inputAlphabet outputAlphabet)
    _ _ _ _ _ (FiniteCertificateExecution.outputs bound) checked
  convert joined using 1
  all_goals first | rfl | (dsimp only [clock]; omega)

/-- Every completed execution agrees with the independent certificate readout,
not merely the designated compiled run. -/
theorem run_readout (checker : Checker Claim (List (Fin 2))) (claim : Claim)
    (checkerClock : List (Fin 2) → Nat)
    (runs : ∀ certificate, TM2OutputsInTime program (encode program inputAlphabet certificate)
      (some [outputAlphabet.symm (checker.check claim certificate)]) (checkerClock certificate))
    (bound : Nat) (wire : List (program.Γ program.k₀ ⊕ Bool))
    (executed : TM2Outputs (machine program inputAlphabet outputAlphabet) (List.replicate bound none) (some wire)) :
    FirstCertificateExecution.Readout.certificate inputAlphabet wire = CertificateBounds.boundedSearch checker claim bound := by
  have same := StackMachineComposition.outputs_unique executed
    (outputs program inputAlphabet outputAlphabet checker claim checkerClock runs bound).toTM2Outputs
  rw [same]
  change FirstCertificateExecution.Readout.certificate inputAlphabet
    (FirstCertificateExecution.Selection.result
      ((CertificateBounds.boundedSearch checker claim bound).map
        (fun certificate => (certificate.map finTwoEquiv).map inputAlphabet.symm))) = _
  simpa only [List.map_map] using
    FirstCertificateExecution.Readout.original_result inputAlphabet (CertificateBounds.boundedSearch checker claim bound)

/-- A certificate extracted from any completed run has passed the original
checker and inherits only that checker's explicitly supplied logical authority. -/
theorem run_accepted (checker : Checker Claim (List (Fin 2))) (meaning : Claim → Prop)
    (sound : checker.Sound meaning) (claim : Claim) (checkerClock : List (Fin 2) → Nat)
    (runs : ∀ certificate, TM2OutputsInTime program (encode program inputAlphabet certificate)
      (some [outputAlphabet.symm (checker.check claim certificate)]) (checkerClock certificate))
    (bound : Nat) (wire : List (program.Γ program.k₀ ⊕ Bool)) (certificate : List (Fin 2))
    (executed : TM2Outputs (machine program inputAlphabet outputAlphabet) (List.replicate bound none) (some wire))
    (decoded : FirstCertificateExecution.Readout.certificate inputAlphabet wire = some certificate) :
    certificate.length ≤ bound ∧ checker.check claim certificate = true ∧ meaning claim := by
  have observed := run_readout program inputAlphabet outputAlphabet checker claim checkerClock runs bound wire executed
  rw [decoded] at observed
  have accepted := CertificateBounds.boundedSearch_eq_some_sound checker claim bound observed.symm
  exact ⟨accepted.1, accepted.2, sound claim certificate accepted.2⟩

end Mettapedia.Logic.ProofSearch.ShortCircuitBoundedSearch
