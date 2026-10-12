import Mettapedia.GSLT.LanguageDef.BootstrapCell.ReplayCorrect
import Mettapedia.GSLT.LanguageDef.SemanticEvidence

/-!
# Stratified reflexive checker layers

A presentation of a calculus's replay rules checks claims about the lower
calculus at the next level. The checker preserves the exact submitted
certificate and accepts precisely the source-soundness claims it presents.
Different contract kinds and incorrect goals are refused.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.BootstrapCell

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.LanguageDef.KernelAuthority
open Mettapedia.GSLT.LanguageDef.SemanticEvidence

/-! ## The reflexive cell as a bootstrap layer -/

/-- A reflexive cell over a validated calculus: a validated presentation of
its replay rules. -/
structure ReflexiveCell (lower : ValidatedCalculusLanguageDef) where
  profile : CellProfile
  upper : ValidatedCalculusLanguageDef
  rulesEq : upper.1.rules = replayRules profile lower.1.rules

/-- Claims at every level are checking facts. -/
def CheckingClaim : Nat → Type := fun _ => Pattern × RawProof

/-- The meaning of a level-one claim about a validated calculus: its kind is
`sourceSound`, and a level-zero derivation of the goal erases to the
certificate. -/
def SourceSound (lower : ValidatedCalculusLanguageDef)
    (claim : LowerContract CheckingClaim 1) : Prop :=
  claim.kind = .sourceSound ∧
    ∃ derivation : Derivation lower claim.statement.1, derivation.erase = claim.statement.2

namespace ReflexiveCell

variable {lower : ValidatedCalculusLanguageDef} (cell : ReflexiveCell lower)

/-- The level-one checker: replay the certificate against the acceptance
judgment of the claimed fact; every other contract kind is rejected. -/
def checker : Checker (LowerContract CheckingClaim 1) RawProof where
  check claim certificate :=
    match claim.kind with
    | .sourceSound =>
        checkRaw cell.upper
          (acceptsJudgment cell.profile claim.statement.1
            (quoteProof cell.profile lower.1 claim.statement.2))
          certificate
    | _ => false

/-- A claim of another kind is rejected by every certificate. -/
theorem other_kind_rejected (claim : LowerContract CheckingClaim 1)
    (kindNe : claim.kind ≠ .sourceSound) (certificate : RawProof) :
    cell.checker.check claim certificate = false := by
  rcases claim with ⟨target, kind, statement⟩
  cases kind <;> first | exact absurd rfl kindNe | rfl

theorem checker_sound : cell.checker.Sound (SourceSound lower) := by
  intro claim certificate accepted
  by_cases kindEq : claim.kind = .sourceSound
  · rcases claim with ⟨target, kind, goal, rawCertificate⟩
    simp only at kindEq
    subst kindEq
    simp only [checker] at accepted
    refine ⟨rfl, ?_⟩
    obtain ⟨derivation⟩ := checkRaw_soundness accepted
    obtain ⟨found, foundAccepted, codeEq, _⟩ :=
      replay_sound cell.profile lower cell.upper cell.rulesEq (toDeriv derivation) goal _ rfl
    have same := quoteProof_injective cell.profile lower.1 _ _ codeEq
    subst same
    obtain ⟨replayDerivation, erased⟩ :=
      ReplaySignature.exists_deriv_of_replay _ _ foundAccepted
    exact ⟨ofDeriv replayDerivation, by
      rw [← erased, ← toDeriv_erase, toDeriv_ofDeriv]⟩
  · rw [cell.other_kind_rejected claim kindEq certificate] at accepted
    exact absurd accepted Bool.false_ne_true

theorem checker_complete : cell.checker.CertificateComplete (SourceSound lower) := by
  rintro ⟨target, kind, goal, rawCertificate⟩ ⟨kindEq, derivation, erased⟩
  simp only at kindEq
  subst kindEq
  refine ⟨replayProof cell.profile lower.1 rawCertificate, ?_⟩
  simp only [checker]
  rw [checkRaw_replayProof cell.profile lower cell.upper cell.rulesEq]
  have erased' : derivation.erase = rawCertificate := erased
  rw [← erased']
  exact checkRaw_erase derivation

/-- **The levelled cell.**  A reflexive cell is a bootstrap layer at host
level one whose checker is an exact authority for level-zero source
soundness. -/
def layer : BootstrapLayer CheckingClaim 1 where
  Certificate := RawProof
  Scope := SourceSound lower
  Meaning := SourceSound lower
  scope_sound := fun _ inScope => inScope
  checker := cell.checker
  scopeAuthority := ⟨cell.checker_sound, cell.checker_complete⟩

end ReflexiveCell

/-! ## Controls on the modus ponens package -/

section Controls

open Mettapedia.Languages.MeTTa.PrimeCandidates.MinimalCheckingPackage
open Mettapedia.GSLT.LanguageDef.BootstrapCell.Calibration

/-- The modus ponens cell as a reflexive cell. -/
def modusPonensReflexiveCell : ReflexiveCell mpValidated where
  profile := levelOne
  upper := modusPonensCellValidated
  rulesEq := modusPonensCell_rules

def sourceSoundClaim (goal : Pattern) (certificate : RawProof) :
    LowerContract CheckingClaim 1 where
  targetLevel := ⟨0, by decide⟩
  kind := .sourceSound
  statement := (goal, certificate)

/-- **Positive control.**  The level-one layer accepts the claim that the
package derives `P(B)` with its certificate. -/
theorem layer_accepts_modusPonens :
    modusPonensReflexiveCell.layer.checker.check (sourceSoundClaim mpBGoal mpProofB)
      (replayProof levelOne mpCache mpProofB) = true :=
  modusPonensCell_accepts

/-- **Negative control.**  No certificate makes the layer accept the wrong
goal. -/
theorem layer_rejects_wrong_goal (certificate : RawProof) :
    modusPonensReflexiveCell.layer.checker.check (sourceSoundClaim mpWrongGoal mpProofB)
      certificate = false := by
  cases accepted : modusPonensReflexiveCell.layer.checker.check
      (sourceSoundClaim mpWrongGoal mpProofB) certificate with
  | false => rfl
  | true =>
      obtain ⟨_, derivation, erased⟩ :=
        modusPonensReflexiveCell.checker_sound _ certificate accepted
      have checked := checkRaw_erase derivation
      change derivation.erase = mpProofB at erased
      rw [erased] at checked
      change checkRaw mpValidated mpWrongGoal mpProofB = true at checked
      rw [mpWrongGoal_rejected] at checked
      exact absurd checked Bool.false_ne_true

/-- **Negative control.**  The replay layer cannot certify a model-soundness
claim, even about a fact it accepts. -/
theorem layer_rejects_modelSound (certificate : RawProof) :
    modusPonensReflexiveCell.layer.checker.check
      { targetLevel := ⟨0, by decide⟩, kind := .modelSound, statement := (mpBGoal, mpProofB) }
      certificate = false :=
  modusPonensReflexiveCell.other_kind_rejected _ (by decide) certificate

end Controls

end Mettapedia.GSLT.LanguageDef.BootstrapCell
