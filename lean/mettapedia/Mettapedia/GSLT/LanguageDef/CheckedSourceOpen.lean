import Mettapedia.GSLT.LanguageDef.CheckedSource
import Mettapedia.GSLT.LanguageDef.CertificateGSLTOpenApplication

/-!
# Open rule programs retain the existing checked source package

The original source identity, assumption ledger and profiles travel with the
result. Validation and proof refusal remain different outcomes. Recorded
identity is not an authenticity oracle; source-specific adequacy and digest
verification remain the existing adapter obligations.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.CheckedSource

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.CertificateGSLT

def GSLTSource.applyOpen (source : GSLTSource) (premises ambient : List Pattern) (goal : Pattern)
    (program : RawOpenProof) (arguments : List RawOpenProof) :
    Except ValidationError (Option (GSLTSource × RawOpenProof)) := do
  let checked ← source.validate
  pure ((applyOpen? checked.definition premises ambient goal program arguments).map
    fun proof => (checked.source, proof))

/-- A successful reply retains the exact original source object and yields
the actual derivation formed by plugging the supplied premise programs. -/
theorem GSLTSource.applyOpen_exact {source returned : GSLTSource}
    {premises ambient : List Pattern} {goal : Pattern} {program result : RawOpenProof}
    {arguments : List RawOpenProof}
    (accepted : source.applyOpen premises ambient goal program arguments = .ok (some (returned, result))) :
    returned = source ∧
      ∃ checked : CheckedGSLT, source.validate = .ok checked ∧
        ∃ rule : OpenDerivation checked.definition premises goal,
          ∃ supplied : OpenDerivationList checked.definition ambient premises,
            rule.eraseOpen = program ∧ supplied.eraseOpen = arguments ∧
              (rule.bind supplied).eraseOpen = result := by
  cases validated : source.validate with
  | error problem => simp [GSLTSource.applyOpen, validated] at accepted
  | ok checked =>
      cases applied : applyOpen? checked.definition premises ambient goal program arguments with
      | none => simp [GSLTSource.applyOpen, validated, applied] at accepted
      | some proof =>
          simp [GSLTSource.applyOpen, validated, applied] at accepted
          obtain ⟨sourceEq, proofEq⟩ := accepted
          refine ⟨sourceEq.symm.trans (GSLTSource.validate_source_eq validated), checked, rfl, ?_⟩
          exact applyOpen?_exact (applied.trans (congrArg some proofEq))

theorem GSLTSource.applyOpen_preserves_identity {source returned : GSLTSource}
    {premises ambient : List Pattern} {goal : Pattern} {program result : RawOpenProof}
    {arguments : List RawOpenProof}
    (accepted : source.applyOpen premises ambient goal program arguments = .ok (some (returned, result))) :
    returned.identity = source.identity ∧ returned.assumptions = source.assumptions ∧
      returned.profiles = source.profiles ∧ returned.definition = source.definition := by
  have same := (GSLTSource.applyOpen_exact accepted).1
  subst returned
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem GSLTSource.invalid_source_refused {source : GSLTSource} {problem : ValidationError}
    (invalid : source.validate = .error problem)
    (premises ambient : List Pattern) (goal : Pattern) (program : RawOpenProof)
    (arguments : List RawOpenProof) :
    source.applyOpen premises ambient goal program arguments = .error problem := by
  simp [GSLTSource.applyOpen, invalid]

#print axioms GSLTSource.applyOpen_exact
#print axioms GSLTSource.applyOpen_preserves_identity

end Mettapedia.GSLT.LanguageDef.CheckedSource
