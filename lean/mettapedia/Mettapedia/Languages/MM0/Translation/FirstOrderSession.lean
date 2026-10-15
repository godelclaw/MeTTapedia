import Mettapedia.Languages.MM0.Translation.FirstOrderAdmission
import Mettapedia.Languages.MM0.Translation.FirstOrderCertificates
import Mettapedia.Languages.MM0.MeTTa.Session.SessionDriver
import Mettapedia.Languages.MeTTa.PeTTa.ConfigurationLanguageDef

/-!
# Typed object-logic certificates through the actual MeTTa MM0 session

The module's generated declarations earn admission from the empty theory.
A final public theorem is checked against that preceding theory, with its
original supplied witness. The existing session driver earns its own physical
table and cache premises. Its complete execution and judgment-generated GSLT
path accept exactly the independently checked typed source certificate.
No correctness premise about a preloaded table or frontend is assumed here.

The generated declarations include one MM0 definition for each definition of
the source language, and a certificate may contain conversion steps. The
statements for certificates without conversion steps are the special case.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MM0.Translation.FirstOrderSession

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.SortedFirstOrderRules
open Mettapedia.GSLT.LanguageDef.CertificateGSLT
open Mettapedia.GSLT.LanguageDef.SortedFirstOrderConversion
open Mettapedia.Languages.MeTTa.PeTTa
open Kernel FirstOrderRules FirstOrderAdmission

def goalSpecification (source : Presentation) (declaration : TheoremDecl) : List SpecificationEntry :=
  specification source ++ [.theoremDecl source.rules.length declaration]

def goalCommand (source : Presentation) (declaration : TheoremDecl) (witness : ProofWitness) :
    ProofDeclaration := ⟨.theoremDecl source.rules.length declaration [] witness, false⟩

def goalDeclarations (source : Presentation) (declaration : TheoremDecl) (witness : ProofWitness) :
    List ProofDeclaration := declarations source ++ [goalCommand source declaration witness]

theorem preceding_run (source : Presentation) (declaration : TheoremDecl) :
    SpecificationAdmission.run? ⟨{}, goalSpecification source declaration⟩ (declarations source) =
      some ⟨chronological source, [.theoremDecl source.rules.length declaration]⟩ := by
  apply (SpecificationAdmission.run_eq_some_iff _ _ _).mpr
  exact SpecificationAdmission.of_theory_run (admitted source) _

theorem goal_fresh (source : Presentation) :
    (chronological source).theoremSignature source.rules.length = none := by
  rw [chronological_theorems, source.theory_theoremSignature]
  simp

/-- Formation is proved separately from the supplied proof's acceptance. -/
theorem goal_verification_iff (source : Presentation) (declaration : TheoremDecl)
    (formed : TheoremDecl.Admissible source.theory.sortSignature source.theory.termSignature declaration)
    (witness : ProofWitness) :
    (SpecificationAdmission.verify? (goalSpecification source declaration)
      (goalDeclarations source declaration witness)).isSome = true ↔
      ProofWitness.Checks source.theory.termSignature source.theory.definitionSignature
        source.theory.theoremSignature declaration.arguments declaration.hypotheses witness declaration.conclusion := by
  have payload := (TheoremDecl.check_iff _ _ _).mpr formed
  have freshness := goal_fresh source
  rw [← ProofWitness.check_iff]
  cases checked : ProofWitness.check source.theory.termSignature source.theory.definitionSignature
      source.theory.theoremSignature declaration.arguments declaration.hypotheses witness
      declaration.conclusion <;>
    simp [SpecificationAdmission.verify?, goalDeclarations, SpecificationAdmission.run_append,
      preceding_run, SpecificationAdmission.run?, goalCommand, SpecificationAdmission.step?,
      SpecificationAdmission.pending?, SpecificationEntry.checkMatch, Theory.step?, Admission.check,
      chronological_sorts, chronological_terms, chronological_definitions, chronological_theorems,
      source.theory_theoremSignature, payload, Definition.checkDummySorts,
      Admission.proofContext, checked]

/-! ## Certificates with conversion steps

The session theorems are stated for certificates modulo the definitions.
The library's `RawOpenProof`, which has no conversion step, is the special
case; its four statements follow below. -/

/-- The source statement and every instance retain their declared sorts. A
certificate with conversion steps is accepted at the source exactly when its
compiled form is verified as the final public theorem after the generated
declarations, definitions included. -/
theorem source_certificateModulo_iff_verified {source : Presentation} {goal : Rule}
    {declaration : TheoremDecl}
    (compiled : Compiles source.syntaxSignature goal declaration)
    (formed : goal.WellFormed source.syntaxSignature.language source.judgmentSorts)
    (certificate : ModuloProof) :
    ChecksModulo source.rows source.syntaxSignature.language source.rules goal.variableTypes
      (goal.row.premises.map (numbered goal.row.vars)) certificate
      (numbered goal.row.vars goal.row.conclusion) ↔
    ∃ witness, FirstOrderCertificates.compileModulo? source
        (goal.row.premises.map (numbered goal.row.vars)) certificate = some witness ∧
      (SpecificationAdmission.verify? (goalSpecification source declaration)
        (goalDeclarations source declaration witness)).isSome = true := by
  rw [FirstOrderCertificates.checksModulo_iff_compiled compiled.contexts compiled.hypotheses
    compiled.conclusion]
  exact exists_congr fun witness => and_congr_right fun _ =>
    (goal_verification_iff source declaration
      (by rw [source.theory_termSignature]; exact Presentation.compiled_admitted compiled formed) witness).symm

/-- The actual retained PeTTa whole-run judgment implements the module backend. -/
theorem source_certificateModulo_iff_petta {source : Presentation} {goal : Rule}
    {declaration : TheoremDecl}
    (compiled : Compiles source.syntaxSignature goal declaration)
    (formed : goal.WellFormed source.syntaxSignature.language source.judgmentSorts)
    (certificate : ModuloProof) (before : Effects.State) :
    ChecksModulo source.rows source.syntaxSignature.language source.rules goal.variableTypes
      (goal.row.premises.map (numbered goal.row.vars)) certificate
      (numbered goal.row.vars goal.row.conclusion) ↔
    ∃ witness after, FirstOrderCertificates.compileModulo? source
        (goal.row.premises.map (numbered goal.row.vars)) certificate = some witness ∧
      DeclarativeSpec.Runs MeTTa.program
        (MeTTa.SessionDriver.ordinaryProtocolConfiguration before
          (goalSpecification source declaration) (goalDeclarations source declaration witness))
        (.complete after (List.replicate ((goalDeclarations source declaration witness).length + 2)
          (Effects.boolean true)) [] []) := by
  rw [source_certificateModulo_iff_verified compiled formed]
  constructor
  · rintro ⟨witness, translated, verified⟩
    obtain ⟨after, run⟩ := (MeTTa.SessionDriver.ordinary_protocol_judgment_iff before _ _).mpr verified
    exact ⟨witness, after, translated, run⟩
  · rintro ⟨witness, after, translated, run⟩
    exact ⟨witness, translated,
      (MeTTa.SessionDriver.ordinary_protocol_judgment_iff before _ _).mp ⟨after, run⟩⟩

/-- These paths belong to the single consolidated PeTTa operational GSLT. -/
theorem source_certificateModulo_iff_gslt {source : Presentation} {goal : Rule}
    {declaration : TheoremDecl}
    (compiled : Compiles source.syntaxSignature goal declaration)
    (formed : goal.WellFormed source.syntaxSignature.language source.judgmentSorts)
    (certificate : ModuloProof) (before : Effects.State) :
    ChecksModulo source.rows source.syntaxSignature.language source.rules goal.variableTypes
      (goal.row.premises.map (numbered goal.row.vars)) certificate
      (numbered goal.row.vars goal.row.conclusion) ↔
    ∃ witness after, FirstOrderCertificates.compileModulo? source
        (goal.row.premises.map (numbered goal.row.vars)) certificate = some witness ∧
      (Eval.theory MeTTa.program).MultiStep
        (MeTTa.SessionDriver.ordinaryProtocolConfiguration before
          (goalSpecification source declaration) (goalDeclarations source declaration witness))
        (Eval.finished after (List.replicate ((goalDeclarations source declaration witness).length + 2)
          (Effects.boolean true)) [] []) := by
  rw [source_certificateModulo_iff_verified compiled formed]
  constructor
  · rintro ⟨witness, translated, verified⟩
    obtain ⟨after, path⟩ := (MeTTa.SessionDriver.ordinary_protocol_gslt_iff before _ _).mpr verified
    exact ⟨witness, after, translated, path⟩
  · rintro ⟨witness, after, translated, path⟩
    exact ⟨witness, translated,
      (MeTTa.SessionDriver.ordinary_protocol_gslt_iff before _ _).mp ⟨after, path⟩⟩

/-- The same certificate executes through the authored configuration
LanguageDef. Loading the retained program derives all finite-store support
premises of its existing transition simulation. The target decode retains the
complete final store and ordered answer/input/output observation. -/
theorem source_certificateModulo_iff_languageDef {source : Presentation} {goal : Rule}
    {declaration : TheoremDecl}
    (compiled : Compiles source.syntaxSignature goal declaration)
    (formed : goal.WellFormed source.syntaxSignature.language source.judgmentSorts)
    (certificate : ModuloProof) :
    ChecksModulo source.rows source.syntaxSignature.language source.rules goal.variableTypes
      (goal.row.premises.map (numbered goal.row.vars)) certificate
      (numbered goal.row.vars goal.row.conclusion) ↔
    ∃ witness after target, FirstOrderCertificates.compileModulo? source
        (goal.row.premises.map (numbered goal.row.vars)) certificate = some witness ∧
      (Mettapedia.OSLF.Framework.TypeSynthesis.langGSLTUsing
        (ConfigurationLanguageDef.relationEnv MeTTa.program) ConfigurationLanguageDef.language).MultiStep
        (ConfigurationEncoding.encode
          (MeTTa.SessionDriver.ordinaryProtocolConfiguration (Effects.loaded MeTTa.program)
            (goalSpecification source declaration) (goalDeclarations source declaration witness)) []) target ∧
      ConfigurationEncoding.decode target = some (Eval.finished after
        (List.replicate ((goalDeclarations source declaration witness).length + 2)
          (Effects.boolean true)) [] []) := by
  constructor
  · intro checked
    obtain ⟨witness, after, translated, running⟩ :=
      (source_certificateModulo_iff_petta compiled formed certificate
        (Effects.loaded MeTTa.program)).mp checked
    obtain ⟨target, generated, decoded⟩ :=
      (ConfigurationLanguageDef.completed_derivation_iff_generated_path MeTTa.program _ []
        (Effects.loaded_empty_tail _) (by intro name absent; rfl) after _ [] []).mp running
    exact ⟨witness, after, target, translated, generated, decoded⟩
  · rintro ⟨witness, after, target, translated, generated, decoded⟩
    apply (source_certificateModulo_iff_petta compiled formed certificate
      (Effects.loaded MeTTa.program)).mpr
    refine ⟨witness, after, translated, ?_⟩
    exact (ConfigurationLanguageDef.completed_derivation_iff_generated_path MeTTa.program _ []
      (Effects.loaded_empty_tail _) (by intro name absent; rfl) after _ [] []).mpr
        ⟨target, generated, decoded⟩

/-! ## Certificates without conversion steps -/

/-- The case of `source_certificateModulo_iff_verified` at a certificate
without conversion steps. -/
theorem source_certificate_iff_verified {source : Presentation} {goal : Rule}
    {declaration : TheoremDecl}
    (compiled : Compiles source.syntaxSignature goal declaration)
    (formed : goal.WellFormed source.syntaxSignature.language source.judgmentSorts)
    (certificate : RawOpenProof) :
    Checks source.syntaxSignature.language source.rules goal.variableTypes
      (goal.row.premises.map (numbered goal.row.vars)) certificate
      (numbered goal.row.vars goal.row.conclusion) ↔
    ∃ witness, FirstOrderCertificates.compile? source certificate = some witness ∧
      (SpecificationAdmission.verify? (goalSpecification source declaration)
        (goalDeclarations source declaration witness)).isSome = true := by
  rw [← checksModulo_ofRaw_iff (rows := source.rows),
    source_certificateModulo_iff_verified compiled formed]
  simp only [FirstOrderCertificates.compileModulo?_ofRaw]

/-- The actual retained PeTTa whole-run judgment implements the module backend. -/
theorem source_certificate_iff_petta {source : Presentation} {goal : Rule}
    {declaration : TheoremDecl}
    (compiled : Compiles source.syntaxSignature goal declaration)
    (formed : goal.WellFormed source.syntaxSignature.language source.judgmentSorts)
    (certificate : RawOpenProof) (before : Effects.State) :
    Checks source.syntaxSignature.language source.rules goal.variableTypes
      (goal.row.premises.map (numbered goal.row.vars)) certificate
      (numbered goal.row.vars goal.row.conclusion) ↔
    ∃ witness after, FirstOrderCertificates.compile? source certificate = some witness ∧
      DeclarativeSpec.Runs MeTTa.program
        (MeTTa.SessionDriver.ordinaryProtocolConfiguration before
          (goalSpecification source declaration) (goalDeclarations source declaration witness))
        (.complete after (List.replicate ((goalDeclarations source declaration witness).length + 2)
          (Effects.boolean true)) [] []) := by
  rw [← checksModulo_ofRaw_iff (rows := source.rows),
    source_certificateModulo_iff_petta compiled formed _ before]
  simp only [FirstOrderCertificates.compileModulo?_ofRaw]

/-- These paths belong to the single consolidated PeTTa operational GSLT. -/
theorem source_certificate_iff_gslt {source : Presentation} {goal : Rule}
    {declaration : TheoremDecl}
    (compiled : Compiles source.syntaxSignature goal declaration)
    (formed : goal.WellFormed source.syntaxSignature.language source.judgmentSorts)
    (certificate : RawOpenProof) (before : Effects.State) :
    Checks source.syntaxSignature.language source.rules goal.variableTypes
      (goal.row.premises.map (numbered goal.row.vars)) certificate
      (numbered goal.row.vars goal.row.conclusion) ↔
    ∃ witness after, FirstOrderCertificates.compile? source certificate = some witness ∧
      (Eval.theory MeTTa.program).MultiStep
        (MeTTa.SessionDriver.ordinaryProtocolConfiguration before
          (goalSpecification source declaration) (goalDeclarations source declaration witness))
        (Eval.finished after (List.replicate ((goalDeclarations source declaration witness).length + 2)
          (Effects.boolean true)) [] []) := by
  rw [← checksModulo_ofRaw_iff (rows := source.rows),
    source_certificateModulo_iff_gslt compiled formed _ before]
  simp only [FirstOrderCertificates.compileModulo?_ofRaw]

/-- The same certificate executes through the authored configuration
LanguageDef. -/
theorem source_certificate_iff_languageDef {source : Presentation} {goal : Rule}
    {declaration : TheoremDecl}
    (compiled : Compiles source.syntaxSignature goal declaration)
    (formed : goal.WellFormed source.syntaxSignature.language source.judgmentSorts)
    (certificate : RawOpenProof) :
    Checks source.syntaxSignature.language source.rules goal.variableTypes
      (goal.row.premises.map (numbered goal.row.vars)) certificate
      (numbered goal.row.vars goal.row.conclusion) ↔
    ∃ witness after target, FirstOrderCertificates.compile? source certificate = some witness ∧
      (Mettapedia.OSLF.Framework.TypeSynthesis.langGSLTUsing
        (ConfigurationLanguageDef.relationEnv MeTTa.program) ConfigurationLanguageDef.language).MultiStep
        (ConfigurationEncoding.encode
          (MeTTa.SessionDriver.ordinaryProtocolConfiguration (Effects.loaded MeTTa.program)
            (goalSpecification source declaration) (goalDeclarations source declaration witness)) []) target ∧
      ConfigurationEncoding.decode target = some (Eval.finished after
        (List.replicate ((goalDeclarations source declaration witness).length + 2)
          (Effects.boolean true)) [] []) := by
  rw [← checksModulo_ofRaw_iff (rows := source.rows),
    source_certificateModulo_iff_languageDef compiled formed]
  simp only [FirstOrderCertificates.compileModulo?_ofRaw]

end Mettapedia.Languages.MM0.Translation.FirstOrderSession
