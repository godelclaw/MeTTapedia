import Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalog
import Mettapedia.GSLT.Parsing.ClassAwareParserPackCorrespondence
import Mettapedia.GSLT.LanguageDef.CanonicalWire
import Lean

set_option autoImplicit false

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.ModuleFormat
open Mettapedia.GSLT.Parsing
open LanguageDefSyntaxCompiler ClassAwareParserPackCorrespondence ParserProfileSemantics
open CettaWire (Term)
open Lean (Json toJson)

namespace GoldPackedReaderExport

def literalScalars? (text : String) : Option (List Nat) :=
  some (text.toList.map Char.toNat)

def literalName (text : String) : String :=
  "literal:" ++ String.intercalate ":" (text.toList.map fun scalar => toString scalar.toNat)

def binding (profile : ParserProfileLayer) : Binding where
  literalRef := fun text => some (literalName text)
  lexicalSortRef := profile.lexicalRule?
  categoryRef := fun category => "category:" ++ category
  ruleRef := fun label => "rule:" ++ label

def state (sort : String) : Term := .application "pp-def" [.string sort]

def peano : Nat → Term
  | 0 => .symbol "q-zero"
  | n + 1 => .application "q-succ" [peano n]

def linked (cons nil : String) : List Term → Term
  | [] => .symbol nil
  | head :: tail => .application cons [head, linked cons nil tail]

def matcher : TerminalMatcher → Term
  | .any => .symbol "pp-terminal-any"
  | .eof => .symbol "pp-terminal-eof"
  | .char scalar => .application "pp-terminal-char" [.application "cp" [.natural scalar]]
  | .class className => .application "pp-terminal-class"
      [.application "pp-class" [.string className]]

def item : PackItem → Term
  | .terminal terminal => .application "pp-terminal" [matcher terminal]
  | .nonterminal sort => .application "pp-nonterminal" [state sort]

def production (label resultSort : String) (items : List PackItem)
    (slots : List Nat) : Term :=
  .application "pp-production"
    [.application "pp-label" [state resultSort, .string label], state resultSort,
     linked "pp-items-cons" "pp-items-nil" (items.map item),
     .application "pa-apply" [.symbol "CstRuleV1",
       linked "pa-cons" "pa-nil"
         (.application "pa-const" [.string label] ::
           slots.map fun slot => .application "pa-slot" [peano slot])]]

def lexicalProduction (row : CompiledLexicalProduction) : Term :=
  production row.label row.resultSort [.terminal row.matcher] row.childSlots

def structuralProduction (row : CompiledStructuralProduction) : Term :=
  production row.label row.resultSort row.items row.childSlots

def entryState (plan : CompiledParserPackPlan) : Term :=
  .application "pp-entry" [state plan.lexical.startSort]

def entryProduction (plan : CompiledParserPackPlan) : Term :=
  .application "pp-production"
    [.application "pp-label" [entryState plan, .string plan.entryProduction.label],
     entryState plan,
     linked "pp-items-cons" "pp-items-nil" (plan.entryProduction.items.map item),
     .application "pa-slot" [peano plan.entryProduction.resultSlot]]

def classClauses (row : LexicalClassDecl) : List Term :=
  let classTerm := Term.application "pp-class" [.string row.name]
  match row.kind with
  | .points points => points.map fun point =>
      .application "pp-class-point" [classTerm, .application "cp" [.natural point]]
  | .except excluded =>
      [.application "pp-class-except" [classTerm,
        linked "pp-points-cons" "pp-points-nil"
          (excluded.map fun point => .application "cp" [.natural point])]]

def classJson (row : LexicalClassDecl) : Json :=
  let (kind, points) := match row.kind with
    | .points points => ("points", points)
    | .except points => ("except", points)
  Json.mkObj [("name", toJson row.name), ("kind", toJson kind), ("points", toJson points)]

def profileRules (classes : List LexicalClassDecl) : List Term :=
  classes.zipIdx |>.flatMap fun (row, rowPosition) =>
    let member := fun scalar => Term.application "member" [.symbol row.name, scalar]
    let rule := fun (suffix : String) (point : Term) (premises : List Term) =>
      Term.application "rule"
        [.symbol s!"profile-member:{rowPosition}:{suffix}",
         .application "head" [member point], .application "body" premises]
    match row.kind with
    | .points points => points.zipIdx.map fun (point, position) =>
        rule (toString position) (.application "cp" [.natural point]) []
    | .except excluded =>
        [rule "complement" (.symbol "?codepoint") (excluded.map fun point =>
          .application "different" [.symbol "?codepoint", .application "cp" [.natural point]])]

def profilePresentation (profile : ParserProfileLayer) : Term :=
  .application "gslt-presentation-v1"
    [.symbol (profile.name ++ "Classes"), .application "signature" [],
     .application "equations" [], .application "rewrites" (profileRules profile.classes)]

def itemJson : PackItem → Json
  | .nonterminal sort => Json.mkObj [("nonterminal", toJson sort)]
  | .terminal .any => Json.mkObj [("terminal", toJson "any")]
  | .terminal .eof => Json.mkObj [("terminal", toJson "eof")]
  | .terminal (.char scalar) => Json.mkObj [("char", toJson scalar)]
  | .terminal (.class className) => Json.mkObj [("class", toJson className)]

def main (arguments : List String) : IO UInt32 := do
  let [outputPath] := arguments | throw (IO.userError "expected one output directory")
  let output := System.FilePath.mk outputPath
  IO.FS.createDirAll output
  let some description := SouffleDatalog.syntaxDescription?
    | throw (IO.userError "actual authored syntax or selected profile port was refused")
  let some rules := compileRules? (binding description.profile) description.grammar
    | throw (IO.userError "actual source rows are outside the shared structural compiler")
  let some plan := compileParserPackPlan? literalScalars? description.profile rules
    | throw (IO.userError "actual compiled rules are outside the shared ParserPack compiler")
  let some canonical := CanonicalWire.renderLanguage? description.grammar
    | throw (IO.userError "actual grammar is outside the existing canonical native wire")
  let some categories := compileCategoryDefinitions? (binding description.profile)
      description.grammar rules
    | throw (IO.userError "source category definitions were refused")
  let literals := (description.grammar.terms.flatMap fun row =>
    row.syntaxPattern.filterMap fun
      | .terminal text => some text
      | _ => none).eraseDups
  let literalDefinitions := literals.map fun text =>
    ({ name := literalName text, body := .literal (text.toList.map Char.toNat) } : Definition)
  let lexicalDefinitions := description.profile.states.map fun row =>
    ({ name := row.ruleLabel, body := .node row.ruleLabel (.class row.className) } : Definition)
  let entryName := "source:whole"
  let source : Presentation := {
    name := description.profile.name ++ "Structural"
    definitions := literalDefinitions ++ lexicalDefinitions ++
      rules.map (CompiledRule.definition (binding description.profile)) ++ categories ++
      [{ name := entryName,
         body := .left (.ref ((binding description.profile).categoryRef
           description.profile.startSort)) .eof }]
    members := [] }
  IO.FS.writeFile (output / "source-structural.metta") source.render
  IO.FS.writeFile (output / "source-classes.metta")
    ((profilePresentation description.profile).render ++ "\n")
  IO.FS.writeFile (output / "source-start.term")
    ((Term.application "pp-def" [.symbol entryName]).render ++ "\n")
  let productions := plan.lexical.productions.map lexicalProduction ++
    plan.structural.map structuralProduction ++ [entryProduction plan]
  let classes := plan.lexical.classes.flatMap classClauses
  IO.FS.writeFile (output / "productions.terms")
    (String.intercalate "\n" (productions.map Term.render) ++ "\n")
  IO.FS.writeFile (output / "classes.terms")
    (String.intercalate "\n" (classes.map Term.render) ++ "\n")
  IO.FS.writeFile (output / "start.term") ((entryState plan).render ++ "\n")
  IO.FS.writeFile (output / "syntax.canonical.metta") canonical
  IO.FS.writeFile (output / "profile.metta") (ParserProfileWire.render description.profile)
  let rows := plan.structural.zipIdx |>.map fun (row, position) =>
    Json.mkObj [("position", toJson position), ("label", toJson row.label),
      ("resultSort", toJson row.resultSort), ("items", toJson (row.items.map itemJson)),
      ("childSlots", toJson row.childSlots),
      ("source", toJson (reprStr row.source))]
  let metadata := Json.mkObj [
    ("grammarName", toJson description.grammar.name),
    ("profileName", toJson description.profile.name),
    ("startSort", toJson description.profile.startSort),
    ("authoredRuleCount", toJson description.grammar.terms.length),
    ("lexicalRuleCount", toJson plan.lexical.productions.length),
    ("entryCount", toJson (1 : Nat)),
    ("classes", toJson (plan.lexical.classes.map classJson)),
    ("structuralRows", toJson rows),
    ("rawSourcePreservedSeparately", toJson true),
    ("packedReaderExecutionCertified", toJson false)]
  IO.FS.writeFile (output / "plan.json") (metadata.pretty ++ "\n")
  IO.println s!"exported {description.grammar.terms.length} authored + {plan.lexical.productions.length} lexical + 1 administrative entry rows"
  pure 0

end GoldPackedReaderExport

def main := GoldPackedReaderExport.main
