import Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalogCSTToCore
import Mettapedia.GSLT.Parsing.ClassAwareParserPackOutput

/-! Checked finite ParserPack certificates reach the actual source grammar
and the composed Core. Compilation agreement is derived for this authored
grammar/profile, not supplied by a caller. Complete native forest production,
ambiguity selection and semantic ProgramData lowering remain separate joins. -/

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 8000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalog.SourceReader

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.Parsing
open LanguageDefSyntaxCompiler LanguageDefScalarSyntax PresentationExprSemantics
open ClassAwareParserPackCorrespondence ClassAwareParserPackCertificate

def literalReference (text : String) : String :=
  "literal:" ++ String.intercalate ":" (text.toList.map fun point => toString point.toNat)

def binding : Binding where
  literalRef := fun text => some (literalReference text)
  lexicalSortRef := SourceViews.profile.lexicalRule?
  categoryRef := ("category:" ++ ·)
  ruleRef := ("rule:" ++ ·)

def rules? : Option (List CompiledRule) := compileRules? binding SourceViews.grammar
def rules : List CompiledRule := rules?.get (by decide +kernel)

theorem rules_compiled : compileRules? binding SourceViews.grammar = some rules :=
  (Option.some_get _).symm

def plan? : Option CompiledParserPackPlan :=
  compileParserPackPlan? CorePrinter.literalScalars? SourceViews.profile rules

def plan : CompiledParserPackPlan := plan?.get (by decide +kernel)

theorem plan_compiled :
    compileParserPackPlan? CorePrinter.literalScalars? SourceViews.profile rules = some plan :=
  (Option.some_get _).symm

theorem agreement : ParserPackPlanAgreement CorePrinter.literalScalars? SourceViews.profile rules plan :=
  .of_compilation plan_compiled

theorem source_of_replay {input : List Nat} {certificate : Certificate}
    {sort : String} {start stop : Nat} {tree : CST}
    (replayed : Replays SourceViews.profile plan input certificate sort start stop tree) :
    Nonempty (DerivesAt CorePrinter.literalScalars? SourceViews.profile SourceViews.grammar input
      sort start stop tree) :=
  LanguageDefScalarSyntax.reflect rules_compiled (reflectSourcePlanDerivation agreement replayed.derivation)

structure Reading (input : List Nat) (sort : String) (start stop : Nat) where
  certificate : Certificate
  tree : CST
  replayed : Replays SourceViews.profile plan input certificate sort start stop tree
  source : Nonempty (DerivesAt CorePrinter.literalScalars? SourceViews.profile SourceViews.grammar input
    sort start stop tree)
  core : Pattern
  construction : CSTToCore.lower? sort tree = some core
  closed : ClosedTermWellSorted ScalarCore.language ⟨sort, by
    obtain ⟨witness⟩ := source
    exact SourceToCore.source_sort_declared witness⟩ core

def readCertificate? (input : List Nat) (sort : String) (start stop : Nat) (certificate : Certificate) :
    Option (Reading input sort start stop) := do
  let parsed ← ClassAwareParserPackReplay.replay SourceViews.profile plan input sort start stop certificate
  let source := source_of_replay parsed.2
  let term := CSTToCore.checkedTerm parsed.1 source
  some ⟨certificate, parsed.1, parsed.2, source, term.val,
    CSTToCore.checkedTerm_lower parsed.1 source, term.property⟩

theorem readCertificate?_isSome_iff (input : List Nat) (sort : String) (start stop : Nat)
    (certificate : Certificate) :
    (readCertificate? input sort start stop certificate).isSome = true ↔
      ∃ tree, Nonempty (Replays SourceViews.profile plan input certificate sort start stop tree) := by
  rw [← ClassAwareParserPackReplay.replay_isSome_iff]
  unfold readCertificate?
  cases ClassAwareParserPackReplay.replay SourceViews.profile plan input sort start stop certificate <;> rfl

theorem readCertificate?_certificate {input : List Nat} {sort : String} {start stop : Nat}
    {certificate : Certificate} {reading : Reading input sort start stop}
    (read : readCertificate? input sort start stop certificate = some reading) :
    reading.certificate = certificate := by
  unfold readCertificate? at read
  cases parsed : ClassAwareParserPackReplay.replay SourceViews.profile plan input sort start stop certificate with
  | none => simp [parsed] at read
  | some result =>
    simp only [parsed] at read
    cases Option.some.inj read
    rfl

theorem Reading.core_exact {input : List Nat} {sort : String} {start stop : Nat}
    (reading : Reading input sort start stop)
    (source : DerivesAt CorePrinter.literalScalars? SourceViews.profile SourceViews.grammar input
      sort start stop reading.tree) : reading.core = SourceToCore.reify source :=
  Option.some.inj (reading.construction.symm.trans (CSTToCore.lower_source source))

theorem Reading.full_source {input : List Nat} {sort : String} (reading : Reading input sort 0 input.length) :
    CorePrinter.printScalars? sort reading.core = some input := by
  obtain ⟨source⟩ := reading.source
  rw [reading.core_exact source]
  exact CorePrinter.full_scalars source

/-- Coverage names the precise source derivation and its certificate. It
does not assume that a native forest happened to retain that certificate. -/
theorem source_has_reading {input : List Nat} {sort : String} {start stop : Nat} {tree : CST}
    (source : DerivesAt CorePrinter.literalScalars? SourceViews.profile SourceViews.grammar input
      sort start stop tree) :
    ∃ (certificate : Certificate) (reading : Reading input sort start stop),
      readCertificate? input sort start stop certificate = some reading ∧
      reading.tree = tree ∧ reading.core = SourceToCore.reify source := by
  obtain ⟨sourcePlan⟩ := LanguageDefScalarSyntax.preserve rules_compiled source
  let target := preserveSourcePlanDerivation agreement sourcePlan
  let certificate := Certificate.ofDerivation target
  have replayed := Replays.ofDerivation target
  obtain ⟨reading, read⟩ := Option.isSome_iff_exists.mp
    ((readCertificate?_isSome_iff input sort start stop certificate).mpr ⟨tree, ⟨replayed⟩⟩)
  have certificateExact := readCertificate?_certificate read
  have actual : Replays SourceViews.profile plan input certificate sort start stop reading.tree := by
    simpa only [certificateExact] using reading.replayed
  have sameTree := ClassAwareParserPackOutput.output_unique actual replayed
  refine ⟨certificate, reading, read, sameTree, ?_⟩
  have built := reading.construction
  rw [sameTree, CSTToCore.lower_source source] at built
  exact (Option.some.inj built).symm

def readProgramCertificate? (input : List Nat) (certificate : Certificate) :
    Option (Reading input SourceViews.profile.startSort 0 input.length) :=
  readCertificate? input SourceViews.profile.startSort 0 input.length certificate

#print axioms rules_compiled
#print axioms plan_compiled
#print axioms source_of_replay
#print axioms readCertificate?_isSome_iff
#print axioms Reading.core_exact
#print axioms Reading.full_source
#print axioms source_has_reading

end Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalog.SourceReader
