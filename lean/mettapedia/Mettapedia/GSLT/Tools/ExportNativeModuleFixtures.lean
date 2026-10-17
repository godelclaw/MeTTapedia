import Mettapedia.GSLT.LanguageDef.ModuleFormat.NativeFixtures
import Lean.Data.Json

/-!
# Export complete portable modules for independent native comparisons

Run with one output-directory argument. Exported `.module` files use the
verified inert text surface; `.sexpr` files expose the physical wire schema.
The JSON manifest states expected decoding outcomes and exact source counts.
Native agreement with these specimens is regression evidence, not adequacy.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Tools.ExportNativeModuleFixtures

open Lean (toJson)
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.ModuleFormat
open Mettapedia.GSLT.LanguageDef.ModuleFormat.NativeFixtures
open Mettapedia.GSLT.LanguageDef.ModuleAlgebra.NativeAuthoring

private def field (key value : String) : String × Lean.Json := (key, .str value)

private def coreMetadata (name : String) (language : LanguageDef) : Lean.Json :=
  .mkObj [field "name" name, field "kind" "core", field "expect" "data",
    field "portable" (name ++ ".module"), field "physical" (name ++ ".sexpr"),
    ("types", toJson language.types.length), ("terms", toJson language.terms.length),
    ("equations", toJson language.equations.length), ("rewrites", toJson language.rewrites.length)]

private def sameCore (expected : LanguageDef) (actual : Option LanguageDef) : Bool :=
  match actual with
  | none => false
  | some actual => coreText actual == coreText expected

private def quote (value : String) : String := (Lean.Json.str value).compress

private def readableType? : TypeExpr → Option String
  | .base name => some name
  | _ => none

private def readableTypeDecl? (declaration : TypeDecl) : Option String :=
  match declaration.carrier with
  | .ast => some (declaration.name ++ ";")
  | .builtinString => some (declaration.name ++ " = String;")
  | _ => none

private def readableParameter? : TermParam → Option String
  | .simple name type => do pure (name ++ ":" ++ (← readableType? type))
  | _ => none

private def readableSyntax? : SyntaxItem → Option String
  | .terminal text => some (quote text)
  | .nonTerminal name => some name
  | _ => none

private def readableTerm? (rule : GrammarRule) : Option String := do
  if rule.evalPolicy?.isSome || rule.algebra?.isSome then none else do
    let parameters ← rule.params.mapM readableParameter?
    let syntaxRows ← rule.syntaxPattern.mapM readableSyntax?
    pure (quote rule.label ++ ". " ++ String.intercalate ", " parameters ++
      " |- " ++ String.intercalate " " syntaxRows ++ " : " ++ rule.category ++ ";")

mutual
  private def readablePattern? : Pattern → Option String
    | .fvar name => some name
    | .apply head arguments => do
        pure (quote head ++ "(" ++ String.intercalate ", " (← readablePatterns? arguments) ++ ")")
    | _ => none

  private def readablePatterns? : List Pattern → Option (List String)
    | [] => some []
    | first :: rest => do pure ((← readablePattern? first) :: (← readablePatterns? rest))
end

private def readablePremise? : Premise → Option String
  | .congruence source target => do
      pure ((← readablePattern? source) ++ " ~> " ++ (← readablePattern? target))
  | .relationQuery relation arguments => do
      pure (quote relation ++ "(" ++ String.intercalate ", " (← readablePatterns? arguments) ++ ")")
  | _ => none

private def readableBinding? (binding : String × TypeExpr) : Option String := do
  pure (binding.1 ++ ":" ++ (← readableType? binding.2))

private def readableRule? (rule : RewriteRule) : Option String := do
  if rule.bindings.isSome then none else do
    let context ← rule.typeContext.mapM readableBinding?
    let premises ← rule.premises.mapM readablePremise?
    let conditions := if premises.isEmpty then "" else " | " ++ String.intercalate ", " premises
    pure (quote rule.name ++ ". " ++ String.intercalate ", " context ++ conditions ++
      " |- " ++ (← readablePattern? rule.left) ++ " ~> " ++ (← readablePattern? rule.right) ++ ";")

/-- A readable subset of the historical theory-builder surface. Unsupported
fields return `none`; no complete-core field is silently erased. The native
reader must independently demonstrate the source-to-core correspondence. -/
private def readableModule? (language : LanguageDef) : Option String := do
  if !language.equations.isEmpty then none else do
    let types ← language.types.mapM readableTypeDecl?
    let terms ← language.terms.mapM readableTerm?
    let rewrites ← language.rewrites.mapM readableRule?
    let rows := fun entries => String.intercalate "\n" (entries.map ("      " ++ ·))
    pure ("Module RegexCore {\n  Theory " ++ language.name ++ "() {\n    Empty\n    Types {\n" ++
      rows types ++ "\n    }\n    Terms {\n" ++ rows terms ++ "\n    }\n    Rewrites {\n" ++
      rows rewrites ++ "\n    }\n  }\n}\n")

def run (arguments : List String) : IO UInt32 := do
  let [output] := arguments | do
    IO.eprintln "usage: ExportNativeModuleFixtures OUTPUT_DIRECTORY"
    return 2
  let directory : System.FilePath := output
  IO.FS.createDirAll directory
  let mut records : List Lean.Json := []
  let mut checks : Nat := 0
  for (name, language) in cores do
    let source := coreText language
    unless sameCore language (readCore? source) do
      IO.eprintln s!"core recovery failed: {name}"
      return 1
    IO.FS.writeFile (directory / (name ++ ".module")) source
    IO.FS.writeFile (directory / (name ++ ".sexpr")) (Wire.language language).render
    records := records ++ [coreMetadata name language]
    checks := checks + 1
  for (name, term) in refusedCores do
    unless (Wire.language? term).isNone do
      IO.eprintln s!"malformed core accepted: {name}"
      return 1
    IO.FS.writeFile (directory / (name ++ ".module")) (Text.render term)
    IO.FS.writeFile (directory / (name ++ ".sexpr")) term.render
    records := records ++ [.mkObj [field "name" name, field "kind" "core",
      field "expect" "refused", field "portable" (name ++ ".module"),
      field "physical" (name ++ ".sexpr")]]
    checks := checks + 1
  for (name, source) in refusedTexts do
    unless (Text.read? source).isNone do
      IO.eprintln s!"malformed text accepted: {name}"
      return 1
    IO.FS.writeFile (directory / (name ++ ".module")) source
    records := records ++ [.mkObj [field "name" name, field "kind" "text",
      field "expect" "refused", field "portable" (name ++ ".module")]]
    checks := checks + 1
  IO.FS.writeFile (directory / "decorated.module") decoratedText
  IO.FS.writeFile (directory / "entries.module") entriesText
  IO.FS.writeFile (directory / "envelope.module") (renderText upstreamLimits envelope)
  let some readable := readableModule? Mettapedia.GSLT.LanguageDef.RegexTheory.theory | do
    IO.eprintln "regex theory lies outside the declared readable surface"
    return 1
  IO.FS.writeFile (directory / "regex.readable.module") readable
  unless (Portable.readTheory? "exports/1" Portable.exportsCodec decoratedText).isSome &&
      (Portable.readTheory? "exports/2" Portable.exportsCodec decoratedText).isNone &&
      (Portable.readEntries? "exports/1" Portable.exportsCodec entriesText).isSome &&
      (readText? upstreamLimits (renderText upstreamLimits envelope)).isSome do
    IO.eprintln "module/layer recovery failed"
    return 1
  checks := checks + 4
  records := records ++ [
    .mkObj [field "name" "decorated", field "kind" "extended-core",
      field "expect" "data", field "portable" "decorated.module", field "schema" "exports/1"],
    .mkObj [field "name" "entries", field "kind" "ordered-entry-list",
      field "expect" "data", field "portable" "entries.module", ("entries", toJson (2 : Nat))],
    .mkObj [field "name" "envelope", field "kind" "module-envelope",
      field "expect" "data", field "portable" "envelope.module", ("exports", toJson (3 : Nat))],
    .mkObj [field "name" "regex-readable", field "kind" "readable-source",
      field "expect" "independent-native-lowering-check",
      field "portable" "regex.readable.module", field "core-reference" "regex.module"]]
  let manifest := Lean.Json.mkObj [field "schema" "native-module-fixtures/1",
    field "scope" "complete finite data interchange; executable admission is separate",
    ("checks", toJson checks), ("fixtures", .arr records.toArray)]
  IO.FS.writeFile (directory / "manifest.json") (manifest.pretty ++ "\n")
  IO.println s!"(NativeModuleFixturesV1Summary {checks} 0)"
  return 0

end Mettapedia.GSLT.Tools.ExportNativeModuleFixtures

def main (arguments : List String) : IO UInt32 :=
  Mettapedia.GSLT.Tools.ExportNativeModuleFixtures.run arguments
