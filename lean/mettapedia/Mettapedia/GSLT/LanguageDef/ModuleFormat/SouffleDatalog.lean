import Mettapedia.GSLT.LanguageDef.ModuleSource.Commands
import Mettapedia.GSLT.LanguageDef.ModuleFormat.Portable
import Mettapedia.GSLT.Parsing.LanguageDefSyntaxCorrespondence

/-!
# Compositional positive function-free Datalog source

The human-authored modules separate the ordinary source grammar, program data
and an explicit lexical-profile message. Structural compilation and portable
payloads are checked here. Range restriction, packed-forest coverage, source
selection and Datalog evaluation require their own correspondence proofs.
-/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 800000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalog

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.ModuleSource.Commands
open scoped Mettapedia.GSLT.LanguageDef.ModuleSource.Commands

#module_file "../../../../../../metta/gslt/module/gold/SouffleDatalog/Syntax.module"
#module_file "../../../../../../metta/gslt/module/gold/SouffleDatalog/GroundKernel.module"
#module_file "../../../../../../metta/gslt/module/gold/SouffleDatalog/Core.module"
#module_file "../../../../../../metta/gslt/module/gold/SouffleDatalog/Language.module"

#module_roundtrip GroundKernel
#module_roundtrip Core
#module_roundtrip Language

def grammar? : Option LanguageDef := Syntax.language.toOption

def programData? : Option LanguageDef := Core.language.toOption

def components? : Option LanguageDef := Language.language.toOption

def lexicalFragment : Except ModuleSource.Error (String × ModuleSource.Value) :=
  ModuleSource.applyTheory Syntax.library Syntax.module ["LexicalProfile"] []

def lexicalLanguage? : Option LanguageDef :=
  (lexicalFragment.map fun (theoryName, value) => ModuleSource.flatten theoryName value).toOption

/-- The explicit message interface selects a unique declaration and retains its
complete origin-bearing packet beside the typed reply. -/
def lexicalReplyAt? (portName : String) (request : Pattern) :
    Option (ModuleSource.Item × Parsing.ParserProfileSemantics.ParserProfileLayer) := do
  let (_, fragment) ← lexicalFragment.toOption
  match fragment.entries.filter (fun entry => entry.label == (.rewrite,portName)) with
  | [entry] =>
      match entry.body with
      | .rewrite rule =>
          if rule.left == request && rule.premises.isEmpty && rule.bindings.isNone then
            (Portable.readLexicalData? rule.right).map (entry, ·)
          else none
      | _ => none
  | _ => none

def profileRequest : Pattern := .apply "GetLexicalProfile" []

def lexicalReply? : Option (ModuleSource.Item × Parsing.ParserProfileSemantics.ParserProfileLayer) :=
  lexicalReplyAt? "ReturnLexicalProfile" profileRequest

def syntaxDescription? : Option Portable.SyntaxDescription := do
  let grammar ← grammar?
  let (_, profile) ← lexicalReply?
  pure ⟨grammar,profile⟩

def portableCore? : Option Export := do
  let programData ← programData?
  pure ⟨"core",Value.Wire.quoteTerm (Portable.coreCodec.encode programData)⟩

def portableModule? : Option («Module» upstreamLimits) := do
  let description ← syntaxDescription?
  let core ← portableCore?
  let raw : RawModule :=
    ⟨"SouffleDatalog",[],[Portable.syntaxExport "syntax" description,core]⟩
  decode? upstreamLimits (encodeRaw raw)

def portableText? : Option String := portableModule?.map (renderText upstreamLimits)

private theorem optionalModuleText_readback (value : Option («Module» upstreamLimits)) :
    (value.map (renderText upstreamLimits)).bind (readText? upstreamLimits) = value := by
  cases value with
  | none => rfl
  | some module => simpa only [Option.map_some, Option.bind_some] using
      readText_renderText upstreamLimits module

/-- Portable recovery applies to every successfully constructed module; source
elaboration remains a separate condition. -/
theorem portableText_readback :
    portableText?.bind (readText? upstreamLimits) = portableModule? :=
  optionalModuleText_readback portableModule?

#guard Syntax.language.isOk
#guard Core.language.isOk
#guard Language.language.isOk
#guard (programData?.map (fun language => language.rewrites.length)) == some 2
#guard (components?.map (fun language => language.rewrites.length)) == some 3
#guard lexicalFragment.isOk
#guard (grammar?.map (fun grammar => grammar.terms.length)) == some 101
#guard (lexicalLanguage?.map (fun language => language.rewrites.length)) == some 1
#guard lexicalReply?.isSome
#guard (lexicalReply?.map (fun reply => reply.2.classes.length)) == some 12
#guard (lexicalReply?.map (fun reply => reply.2.states.length)) == some 12
#guard portableModule?.isSome
#guard (lexicalReplyAt? "MissingProfile" profileRequest).isNone
#guard (lexicalReplyAt? "ReturnLexicalProfile"
  (.apply "GetLexicalProfile" [.apply "unexpected" []])).isNone

#print axioms portableText_readback

end Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalog
