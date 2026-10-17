import Mettapedia.GSLT.LanguageDef.ModuleFormat.RegexSelectionAuthoring
import Mettapedia.GSLT.LanguageDef.ModuleFormat.RegexSyntaxAuthoring
import Lean.Data.Json

/-!
# Export the authored compiler to complete modules and equation packets

The packet renderer admits only the first-order fragment used by this compiler.
It does not silently render binders, premises or annotations as plain equations.
Exported equation packets are inputs to the deterministic equation-plan profile;
the complete portable module remains the authoritative declaration carrier.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Tools.ExportRegexSelectionCompiler

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.ModuleFormat
open Mettapedia.GSLT.LanguageDef.ModuleFormat.RegexSelectionAuthoring
open Lean (toJson)

private def quote (text : String) : String := (Lean.Json.str text).compress

mutual
  private def packetPattern? : Pattern → Option String
    | .fvar parameterName => some ("?" ++ parameterName)
    | .apply head [] => some head
    | .apply head arguments => do
        pure ("(" ++ head ++ " " ++ String.intercalate " " (← packetPatterns? arguments) ++ ")")
    | _ => none

  private def packetPatterns? : List Pattern → Option (List String)
    | [] => some []
    | first :: rest => do pure ((← packetPattern? first) :: (← packetPatterns? rest))
end

private def packetEquation? (equation : Equation) : Option String := do
  if !equation.premises.isEmpty || equation.bindings.isSome then none else do
    pure ("    (rule " ++ equation.name ++ " (head (metta-equation " ++
      (← packetPattern? equation.left) ++ " " ++ (← packetPattern? equation.right) ++ ")) (body))")

def equationPacket? (language : LanguageDef) : Option String := do
  if !language.rewrites.isEmpty then none else do
    let equations ← language.equations.mapM packetEquation?
    let operators := language.terms.map fun rule =>
      "    (operator " ++ rule.label ++ " " ++ toString rule.params.length ++ ")"
    pure ("(gslt-presentation-v1 " ++ language.name ++ "\n  (signature\n" ++
      "    (operator metta-equation 2)\n" ++ String.intercalate "\n" operators ++
      ")\n  (equations)\n  (rewrites\n" ++ String.intercalate "\n" equations ++ "))\n")

private def readableType? : TypeExpr → Option String
  | .base sort => some sort
  | _ => none

private def readableParameter? : TermParam → Option String
  | .simple parameterName type => do pure (parameterName ++ ":" ++ (← readableType? type))
  | _ => none

private def readableSyntax? : SyntaxItem → Option String
  | .terminal text => some (quote text)
  | .nonTerminal parameterName => some parameterName
  | _ => none

private def readableTerm? (rule : GrammarRule) : Option String := do
  if rule.evalPolicy?.isSome || rule.algebra?.isSome then none else do
    pure ("      " ++ quote rule.label ++ ". " ++
      String.intercalate ", " (← rule.params.mapM readableParameter?) ++ " |- " ++
      String.intercalate " " (← rule.syntaxPattern.mapM readableSyntax?) ++ " : " ++ rule.category ++ ";")

mutual
  private def readablePattern? : Pattern → Option String
    | .fvar parameterName => some parameterName
    | .apply head arguments => do
        pure (quote head ++ "(" ++ String.intercalate ", " (← readablePatterns? arguments) ++ ")")
    | _ => none

  private def readablePatterns? : List Pattern → Option (List String)
    | [] => some []
    | first :: rest => do pure ((← readablePattern? first) :: (← readablePatterns? rest))
end

private def readableBinding? (binding : String × TypeExpr) : Option String := do
  pure (binding.1 ++ ":" ++ (← readableType? binding.2))

private def readableEquation? (equation : Equation) : Option String := do
  if !equation.premises.isEmpty || equation.bindings.isSome then none else do
    pure ("      " ++ quote equation.name ++ ". " ++
      String.intercalate ", " (← equation.typeContext.mapM readableBinding?) ++ " |- " ++
      (← readablePattern? equation.left) ++ " = " ++ (← readablePattern? equation.right) ++ ";")

def readableModule? (language : LanguageDef) : Option String := do
  if !language.rewrites.isEmpty || language.types != [⟨"ReValue", .builtinString⟩] then none else do
    let terms ← language.terms.mapM readableTerm?
    let equations ← language.equations.mapM readableEquation?
    pure ("Module RegexSelection {\n  Theory " ++ language.name ++ "() {\n    Empty\n" ++
      "    Types { ReValue = String; }\n    Terms {\n" ++ String.intercalate "\n" terms ++
      "\n    }\n    Equations {\n" ++ String.intercalate "\n" equations ++ "\n    }\n  }\n}\n")

def run (arguments : List String) : IO UInt32 := do
  let [destination] := arguments | do
    IO.eprintln "usage: ExportRegexSelectionCompiler OUTPUT_DIRECTORY"
    return 2
  let directory : System.FilePath := destination
  IO.FS.createDirAll directory
  let some packet := equationPacket? theory | do
    IO.eprintln "compiler exceeds the equation-packet rendering profile"
    return 1
  let some readable := readableModule? theory | do
    IO.eprintln "compiler exceeds the readable module rendering profile"
    return 1
  IO.FS.writeFile (directory / "RegexSelectionCompiler.portable.module") portableText
  IO.FS.writeFile (directory / "RegexSelectionCompiler.module") readable
  IO.FS.writeFile (directory / "selection_compiler_v1.metta") packet
  IO.FS.writeFile (directory / "RegexSyntax.portable.module") RegexSyntaxAuthoring.portableText
  IO.FS.writeFile (directory / "source_profile_v1.metta") RegexSyntaxAuthoring.profileText
  let metadata := Lean.Json.mkObj [
    ("name", .str theory.name),
    ("types", toJson theory.types.length),
    ("terms", toJson theory.terms.length),
    ("equations", toJson theory.equations.length),
    ("rewrites", toJson theory.rewrites.length),
    ("numericCodecLawsProved", .bool true),
    ("nativeNumericAdapterAdequacyProved", .bool false),
    ("nativeAdequacyProved", .bool false),
    ("syntaxTypes", toJson RegexSyntaxAuthoring.authored.types.length),
    ("syntaxTerms", toJson RegexSyntaxAuthoring.authored.terms.length)]
  IO.FS.writeFile (directory / "manifest.json") (metadata.pretty ++ "\n")
  IO.println "(RegexSelectionAuthoringExport 5 0)"
  return 0

end Mettapedia.GSLT.Tools.ExportRegexSelectionCompiler

def main := Mettapedia.GSLT.Tools.ExportRegexSelectionCompiler.run
