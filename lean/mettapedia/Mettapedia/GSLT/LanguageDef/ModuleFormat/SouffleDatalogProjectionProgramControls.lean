import Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalogProjectionNativeAdmission
import Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalogSourceProjection
import Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalogSourceReaderControls

/-! Whole structural compilation controls include a checked ordinary source
reading, grouped declarations, ordered duplicate statements and conditional
clause syntax. These controls do not execute Datalog inference or comparisons. -/

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 8000000
set_option cbv.maxSteps 500000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalog.ProgramProjection.Native.ProgramControls

open Mettapedia.OSLF.MeTTaIL Syntax

def spec := Admission.programSpec

def trivia : Pattern := .apply "dl-src:trivia-empty" []
def identifier (point : Fin (16 ^ 6)) : Pattern := .apply "dl-src:identifier-one"
  [ScalarCore.wordLeaf ⟨0,by decide +kernel⟩ point]
def name (point : Fin (16 ^ 6)) : Pattern := .apply "dl-src:qualified-name-one" [identifier point]
def integer : Pattern := .apply "dl-src:integer-decimal"
  [.apply "dl-src:digits-one" [ScalarCore.wordLeaf ⟨3,by decide +kernel⟩ 49]]
def constant : Pattern := .apply "dl-src:constant-integer" [integer]
def groundAtom : Pattern := GroundAtoms.source (name 112) trivia trivia (ConstantLists.one constant trivia)
def fact : Pattern := Facts.source groundAtom trivia

def items : List Pattern → Pattern
  | [] => ProgramItems.empty
  | first :: rest => ProgramItems.more first trivia (items rest)
def sourceProgram (statements : List Pattern) : Pattern := Program.source trivia (items statements)
def factItem : Pattern := .apply "dl-src:item-fact" [fact]
def ordinarySource : Pattern := sourceProgram [factItem]
def ordinaryCore : Pattern :=
  (SourceReader.readProgramCertificate? [112,40,49,41,46] SourceReader.Controls.programCertificate).get
    SourceReader.Controls.whole_program_syntax_round_trip.2.1 |>.core

def groundResult : Pattern := .apply "GroundFact" [Reference.relation (name 112),
  Reference.groundTuple [.apply "IntegerValue" [integer]]]
def variableSource : Pattern := Terms.variableSource (identifier 112)
def variableResult : Pattern := Terms.variableResult (identifier 112)
def sourceAtom (point : Fin (16 ^ 6)) : Pattern := Atoms.source (name point) trivia trivia (TermLists.one variableSource trivia)
def atomResult (point : Fin (16 ^ 6)) : Pattern := .apply "PositiveAtom"
  [Reference.relation (name point),Reference.tuple [variableResult]]
def comparison : Pattern := Comparisons.source variableSource trivia (ComparisonOperators.source 2) trivia
  (.apply "dl-src:term-constant" [constant])
def body : Pattern := Bodies.more (.apply "dl-src:positive-atom" [sourceAtom 112]) trivia trivia
  (Bodies.one (.apply "dl-src:positive-comparison" [comparison]) trivia)
def clause : Pattern := Clauses.source (sourceAtom 113) trivia trivia body

def space : Pattern := .apply "dl-src:directive-space" [ScalarCore.wordLeaf ⟨8,by decide +kernel⟩ 32,trivia]
def attributes : Pattern := AttributeLists.one
  (Attributes.source (identifier 112) trivia trivia (AttributeTypes.source 1)) trivia
def relations : Pattern := Relations.more (identifier 112) trivia trivia (Relations.one (identifier 113))
def declarationItem : Pattern := ItemDeclarations.source space relations trivia trivia attributes
def inputItem : Pattern := ItemDirectives.source 0 space (name 112)
def outputItem : Pattern := ItemDirectives.source 1 space (name 113)
def clauseItem : Pattern := .apply "dl-src:item-rule" [clause]
def fullSource : Pattern := sourceProgram [declarationItem,inputItem,factItem,clauseItem,outputItem]
def fields : List Pattern := [Attributes.result (identifier 112) (AttributeTypes.result 1)]
def clauseResult : Pattern := Clauses.result (Reference.relation (name 113)) (Reference.tuple [variableResult])
  [atomResult 112,.apply "Comparison" [.apply "Less" [variableResult,.apply "ValueArgument" [.apply "IntegerValue" [integer]]]]]
def fullResult : Pattern := Reference.program
  [Reference.declaration (identifier 112) fields,Reference.declaration (identifier 113) fields,
    ItemDirectives.statement 0 (name 112),groundResult,clauseResult,ItemDirectives.statement 1 (name 113)]

theorem empty_step (environment : Engine.RelationEnv) :
    ReferenceStep.Step environment NativeSlice.language (Program.call (sourceProgram [])) (Reference.program []) := by
  rw [Native.program_exact]
  rfl

theorem ordinary_step (environment : Engine.RelationEnv) :
    ReferenceStep.Step environment NativeSlice.language (Program.call ordinarySource)
      (Reference.program [groundResult]) := by
  rw [Native.program_exact]
  rfl

theorem duplicates_preserved (environment : Engine.RelationEnv) :
    ReferenceStep.Step environment NativeSlice.language (Program.call (sourceProgram [factItem,factItem]))
      (Reference.program [groundResult,groundResult]) := by
  rw [Native.program_exact]
  rfl

theorem complete_program_step (environment : Engine.RelationEnv) :
    ReferenceStep.Step environment NativeSlice.language (Program.call fullSource) fullResult := by
  rw [Native.program_exact]
  rfl

theorem malformed_refused (environment : Engine.RelationEnv) (target : Pattern) :
    ¬ReferenceStep.Step environment NativeSlice.language
      (Program.call (.apply "dl-src:program" [trivia])) target := by
  rw [Native.program_exact]
  change ¬(none = some target)
  intro impossible
  cases impossible

#guard ordinaryCore == ordinarySource

#print axioms ordinary_step
#print axioms complete_program_step
#print axioms malformed_refused

end Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalog.ProgramProjection.Native.ProgramControls
