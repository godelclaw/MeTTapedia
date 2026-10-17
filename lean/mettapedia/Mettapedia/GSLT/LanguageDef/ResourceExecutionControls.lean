import Mettapedia.GSLT.LanguageDef.ResourceExecution

/-!
# Executed acceptance and refusal controls

The finite control language has two claims and proves exactly `true`. Its
one-step checker and the two-pass identity compiler exercise the complete
translation/handoff/checking machine on both accepted and rejected packets.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ResourceTranslation.ExecutionControls

open SemanticEvidence Turing

def theory : TheoryFamily Unit where
  Signature := Unit
  signatureOf _ := ()
  Claim _ := Bool
  Scope _ b := b = true
  Meaning _ b := b = true
  scope_sound _ _ h := h

def authority : AuthorityContract theory where
  Certificate _ := Unit
  checker _ := ⟨fun (b : Bool) (_ : Unit) => b⟩
  scopeAuthority _ :=
    { sound := fun _ _ h => h
      complete := fun _ h => ⟨(), h⟩ }

def packet (b : Bool) : Packet authority := ⟨(), b, ()⟩

def encoding : Computability.Encoding (Packet authority) Bool where
  encode p := [p.2.1]
  decode
    | [b] => some (packet b)
    | _ => none
  decode_encode := by rintro ⟨⟨⟩, b, ⟨⟩⟩; rfl

/-- The original checker performs one actual halting step. -/
def implementation : CheckerExecution authority encoding where
  tm := idComputer Bool
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time _ := 1
  outputs _p :=
    { steps := 1
      evals_in_steps := rfl
      steps_le_m := le_rfl }
  finiteAlphabet _ := inferInstanceAs (Finite Bool)

noncomputable def compiler := OperationalTranslation.identity authority encoding

noncomputable def compiledChecker : CheckerExecution authority encoding :=
  CheckerExecution.via compiler Translation.exact_identity implementation

/-- Four copying steps, four handoff steps, one checker step. -/
theorem composed_bound (b : Bool) : compiledChecker.time (packet b) = 9 := by
  simp [compiledChecker, CheckerExecution.via_time, compiler,
    OperationalTranslation.identity, Translation.identity, Translation.packet,
    encoding, packet, implementation, HeterogeneousTheory.TheoryTranslation.identity]

noncomputable def accepted_run : TM2OutputsInTime compiledChecker.tm
    ((encoding.encode (packet true)).map compiledChecker.inputAlphabet.symm)
    (some ([true].map compiledChecker.outputAlphabet.symm)) 9 := by
  have run := compiledChecker.outputs (packet true)
  rw [composed_bound] at run
  exact run

/-- Rejection uses the same whole pipeline and the same clock. -/
noncomputable def refused_run : TM2OutputsInTime compiledChecker.tm
    ((encoding.encode (packet false)).map compiledChecker.inputAlphabet.symm)
    (some ([false].map compiledChecker.outputAlphabet.symm)) 9 := by
  have run := compiledChecker.outputs (packet false)
  rw [composed_bound] at run
  exact run

/-- Determinism excludes a spurious successful run for the refused claim. -/
theorem refused_has_no_accepting_run : IsEmpty (TM2Outputs compiledChecker.tm
    ((encoding.encode (packet false)).map compiledChecker.inputAlphabet.symm)
    (some ([true].map compiledChecker.outputAlphabet.symm))) := by
  refine ⟨fun run => ?_⟩
  have falseMeaning := compiledChecker.accepted_meaning (packet false) run
  change false = true at falseMeaning
  cases falseMeaning

end Mettapedia.GSLT.LanguageDef.ResourceTranslation.ExecutionControls
