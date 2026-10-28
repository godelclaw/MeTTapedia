import Mettapedia.GSLT.LanguageDef.CertificateGSLTOpenApplication
import Mettapedia.GSLT.LanguageDef.InferenceCettaWireFormat

/-!
# Open rule application through the established MeTTa carrier

The theory argument is an admitted calculus. The remaining arguments are
inspectable data in the existing physical wire format. Decoding never grants
authority: application checks the decoded template and ordered arguments.
The theorems here concern this codec and checker; qualification of a particular
native evaluator is a separate obligation.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.InferenceCettaWire

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.LanguageDef.CertificateGSLT

def checkOpenPacket (definition : ValidatedCalculusLanguageDef)
    (contextTerm goalTerm proofTerm : CettaTerm) : Bool :=
  match decodePatterns contextTerm, decodePattern goalTerm, decodeOpenProof proofTerm with
  | some context, some goal, some proof => checkOpenRaw definition context goal proof
  | _, _, _ => false

/-- No result means malformed data or refused evidence, never inequality. -/
def applyOpenPacket (definition : ValidatedCalculusLanguageDef)
    (premisesTerm ambientTerm goalTerm programTerm argumentsTerm : CettaTerm) :
    Option CettaTerm := do
  let premises ← decodePatterns premisesTerm
  let ambient ← decodePatterns ambientTerm
  let goal ← decodePattern goalTerm
  let program ← decodeOpenProof programTerm
  let arguments ← decodeOpenProofs argumentsTerm
  let result ← applyOpen? definition premises ambient goal program arguments
  pure (encodeOpenProof result)

@[simp] theorem checkOpenPacket_encode (definition : ValidatedCalculusLanguageDef)
    (context : List Pattern) (goal : Pattern) (proof : RawOpenProof) :
    checkOpenPacket definition (encodePatterns context) (encodePattern goal)
      (encodeOpenProof proof) = checkOpenRaw definition context goal proof := by
  simp [checkOpenPacket]

@[simp] theorem applyOpenPacket_encode (definition : ValidatedCalculusLanguageDef)
    (premises ambient : List Pattern) (goal : Pattern)
    (program : RawOpenProof) (arguments : List RawOpenProof) :
    applyOpenPacket definition (encodePatterns premises) (encodePatterns ambient)
      (encodePattern goal) (encodeOpenProof program) (encodeOpenProofs arguments) =
        (applyOpen? definition premises ambient goal program arguments).map encodeOpenProof := by
  simp [applyOpenPacket, Option.map_eq_bind]

theorem encodeOpenProof_injective : Function.Injective encodeOpenProof := by
  intro first second same
  have decoded := congrArg decodeOpenProof same
  simpa only [decodeOpenProof_encodeOpenProof, Option.some.injEq] using decoded

/-- This statement applies to every submitted physical packet, including
noncanonical packets that the decoder accepts. It retains each decoded input
and the exact evidence returned by actual premise filling. -/
theorem applyOpenPacket_exact (definition : ValidatedCalculusLanguageDef)
    {premisesTerm ambientTerm goalTerm programTerm argumentsTerm resultTerm : CettaTerm}
    (accepted : applyOpenPacket definition premisesTerm ambientTerm goalTerm
      programTerm argumentsTerm = some resultTerm) :
    ∃ premises ambient goal program arguments,
      decodePatterns premisesTerm = some premises ∧
      decodePatterns ambientTerm = some ambient ∧
      decodePattern goalTerm = some goal ∧
      decodeOpenProof programTerm = some program ∧
      decodeOpenProofs argumentsTerm = some arguments ∧
      ∃ rule : OpenDerivation definition premises goal,
        ∃ supplied : OpenDerivationList definition ambient premises,
          rule.eraseOpen = program ∧ supplied.eraseOpen = arguments ∧
            encodeOpenProof (rule.bind supplied).eraseOpen = resultTerm := by
  unfold applyOpenPacket at accepted
  cases hp : decodePatterns premisesTerm with
  | none => simp [hp] at accepted
  | some premises =>
    cases ha : decodePatterns ambientTerm with
    | none => simp [hp, ha] at accepted
    | some ambient =>
      cases hg : decodePattern goalTerm with
      | none => simp [hp, ha, hg] at accepted
      | some goal =>
        cases hr : decodeOpenProof programTerm with
        | none => simp [hp, ha, hg, hr] at accepted
        | some program =>
          cases hs : decodeOpenProofs argumentsTerm with
          | none => simp [hp, ha, hg, hr, hs] at accepted
          | some arguments =>
            cases result : applyOpen? definition premises ambient goal program arguments with
            | none => simp [hp, ha, hg, hr, hs, result] at accepted
            | some proof =>
              simp [hp, ha, hg, hr, hs, result] at accepted
              obtain ⟨rule, supplied, re, se, output⟩ := applyOpen?_exact result
              exact ⟨premises, ambient, goal, program, arguments, rfl, rfl, rfl, rfl, rfl,
                rule, supplied, re, se, by rw [output]; exact accepted⟩

theorem applyOpenPacket_checked (definition : ValidatedCalculusLanguageDef)
    {premisesTerm ambientTerm goalTerm programTerm argumentsTerm resultTerm : CettaTerm}
    (accepted : applyOpenPacket definition premisesTerm ambientTerm goalTerm
      programTerm argumentsTerm = some resultTerm) :
    checkOpenPacket definition ambientTerm goalTerm resultTerm = true := by
  obtain ⟨premises, ambient, goal, program, arguments, _, ha, hg, _, _,
    rule, supplied, _, _, output⟩ := applyOpenPacket_exact definition accepted
  rw [← output]
  simp only [checkOpenPacket, ha, hg, decodeOpenProof_encodeOpenProof]
  exact checkOpenRaw_erase (rule.bind supplied)

/-- The wire does not turn two occurrences of the same judgment into one. -/
theorem premise_positions_distinct (first second : Nat) (different : first ≠ second) :
    encodeOpenProof (.premise first) ≠ encodeOpenProof (.premise second) := by
  intro same
  exact different (RawOpenProof.premise.inj (encodeOpenProof_injective same))

#print axioms applyOpenPacket_exact
#print axioms applyOpenPacket_checked
#print axioms premise_positions_distinct

end Mettapedia.GSLT.LanguageDef.InferenceCettaWire
