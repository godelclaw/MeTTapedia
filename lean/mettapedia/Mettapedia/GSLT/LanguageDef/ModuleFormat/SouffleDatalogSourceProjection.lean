import Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalogSourceReader
import Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalogProjectionAgreement

/-! Finite source certificates compose with the actual authored structural
compiler. The source reading and its complete input evidence remain available.
Native forest production, ambiguity selection, total target typing and semantic
literal interpretation are separate requirements. -/

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalog.SourceProjection

open Mettapedia.OSLF.MeTTaIL Syntax
open Mettapedia.GSLT.Parsing.ClassAwareParserPackCertificate (Certificate)
open ProgramProjection

def project? (input : List Nat) (certificate : Certificate) : Option Pattern := do
  let reading ← SourceReader.readProgramCertificate? input certificate
  Reference.projectProgram? reading.core

def projectText? (input : String) (certificate : Certificate) : Option Pattern :=
  project? (input.toList.map Char.toNat) certificate

theorem project?_exact (environment : Engine.RelationEnv) (input : List Nat)
    (certificate : Certificate) (target : Pattern) :
    project? input certificate = some target ↔
      ∃ reading, SourceReader.readProgramCertificate? input certificate = some reading ∧
        ReferenceStep.Step environment language (Program.call reading.core) target := by
  unfold project?
  cases read : SourceReader.readProgramCertificate? input certificate with
  | none => simp [Option.bind_eq_bind]
  | some reading =>
    simp only [Option.bind_eq_bind,Option.bind_some,Option.some.injEq]
    constructor
    · intro projected
      exact ⟨reading,rfl,(Program.reference_exact environment reading.core target).mpr projected⟩
    · rintro ⟨other,rfl,step⟩
      exact (Program.reference_exact environment _ target).mp step

/-- Successful compilation retains a checked reading of exactly the input,
not just an unlicensed constructor tree. -/
theorem source_readback (environment : Engine.RelationEnv) {input : List Nat}
    {certificate : Certificate} {target : Pattern} (compiled : project? input certificate = some target) :
    ∃ reading, SourceReader.readProgramCertificate? input certificate = some reading ∧
      CorePrinter.printScalars? SourceViews.profile.startSort reading.core = some input ∧
      ReferenceStep.Step environment language (Program.call reading.core) target := by
  obtain ⟨reading,read,step⟩ := (project?_exact environment input certificate target).mp compiled
  exact ⟨reading,read,reading.full_source,step⟩

theorem projectText?_exact (environment : Engine.RelationEnv) (input : String)
    (certificate : Certificate) (target : Pattern) :
    projectText? input certificate = some target ↔
      ∃ reading, SourceReader.readProgramCertificate? (input.toList.map Char.toNat) certificate = some reading ∧
        ReferenceStep.Step environment language (Program.call reading.core) target :=
  project?_exact environment _ certificate target

#print axioms project?_exact
#print axioms source_readback

end Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalog.SourceProjection
