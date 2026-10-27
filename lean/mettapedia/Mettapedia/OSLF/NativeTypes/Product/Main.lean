import Lean

/-!
# `oslf`: the command-line front door

`lake exe oslf LANGUAGE.module FORMULA TERM [BUDGET ...] [SETTING ...]` reads a language from a `.module` file, with
the files it imports, and asks the front door whether the term has the native type, at each budget in turn, resuming
the question from one budget to the next. It prints the displayed status at each budget: established or refuted with
the evidence, or suspended. Settings are `fuel=N` (premise fuel, two by default) and `hints=N` (the finder looks for a
certificate over carriers of up to `N + 1` values, one by default; none at zero).

`lake exe oslf --matrix ROWS` checks a matrix file, each row `file | formula | term | budget | expected [| settings]`,
the expected answer a status or an answer in brief (`P certificate`, `R closed`, `open`, …).

The executable runs Lean's frontend on a short source that reads the module files with the format's reader and
evaluates the front door (`Mettapedia.OSLF.NativeTypes.Product.report`), so the language is elaborated exactly as the
library elaborates it.
-/

open Lean

namespace Mettapedia.OSLF.NativeTypes.Product.Main

def usage : String :=
  "usage: oslf LANGUAGE.module[#Theory] FORMULA TERM [BUDGET ...] [fuel=N] [hints=N]\n" ++
  "       oslf --matrix ROWS   (each row: file | formula | term | budget | expected [| settings])\n" ++
  "  FORMULA and TERM are S-expressions, for example\n" ++
  "    oslf Counters.module '(reach (Halted))' '(Counter (Succ Zero))' 2 4 8"

/-- The name a `.module` text declares after `Module`. -/
def moduleName (text : String) : Option String :=
  let words := text.splitOn "\n" |>.flatMap fun line =>
    (line.splitOn " ").filter (· ≠ "") |>.map (·.trimAscii.toString)
  match words.dropWhile (· ≠ "Module") with
  | _ :: name :: _ => some ((name.splitOn "{").head!)
  | _ => none

/-- The files a `.module` text imports. -/
def importedFiles (text : String) : List String :=
  (text.splitOn "\n").filterMap fun line =>
    let trimmed := line.trimAscii.toString
    if trimmed.startsWith "import \"" then
      match ((trimmed.drop 8).toString).splitOn "\"" with
      | file :: _ => some file
      | [] => none
    else none

/-- The module files in dependency order, imports first. -/
partial def loadOrder (directory : System.FilePath) (file : String) (seen : List String) : IO (List String) := do
  if seen.contains file then return seen
  let text ← IO.FS.readFile (directory / file)
  let mut order := seen
  for imported in importedFiles text do
    order ← loadOrder directory imported order
  return order ++ [file]

/-- A file argument `FILE.module` or `FILE.module#Theory`: the file, and the theory it names, if any. A module that
declares theories and no entry, as CeTTa's core modules do, is read through a named theory. -/
def splitTheory (argument : String) : String × Option String :=
  match argument.splitOn "#" with
  | [file, theory] => (file, some theory)
  | _ => (argument, none)

/-- The language a module denotes: its entry, or the named theory applied to no arguments. -/
def languageTerm (base : String) : Option String → String
  | none => s!"{base}.language"
  | some theory =>
    s!"(Mettapedia.GSLT.LanguageDef.ModuleSource.elaborateTheory {base}.library {base}.module " ++
      s!"{(theory.splitOn ".").map String.quote})"

/-- The source the frontend runs. -/
def source (files : List String) (language formula term : String) (budgets : List Nat) (settings : List String) :
    String :=
  "import Mettapedia.OSLF.NativeTypes.Product.Query\n" ++
  "open Mettapedia.GSLT.LanguageDef.ModuleSource.Commands\n" ++
  String.join (files.map fun file => s!"#module_file {file.quote}\n") ++
  s!"#eval Mettapedia.OSLF.NativeTypes.Product.report {language} {formula.quote} {term.quote} {budgets} " ++
    s!"{settings.map String.quote}\n"

/-- A row of a matrix file: `file | formula | term | budget | expected [| settings]`. -/
structure Row where
  file : String
  formula : String
  term : String
  budget : Nat
  expected : String
  settings : List String

/-- The rows of a matrix file; blank lines and lines starting with `#` are skipped. -/
def readRows (text : String) : Except String (List Row) :=
  (text.splitOn "\n").filterMap (fun line =>
      let trimmed := line.trimAscii.toString
      if trimmed.isEmpty || trimmed.startsWith "#" then none else some trimmed)
    |>.mapM fun line =>
      let fields := (line.splitOn "|").map (·.trimAscii.toString)
      match fields with
      | file :: formula :: term :: budget :: expected :: rest =>
        let settings := (rest.flatMap (·.splitOn " ")).filter (· ≠ "")
        if rest.length > 1 then .error s!"a row has at most six fields: {line}" else
        match budget.toNat? with
        | some number => .ok ⟨file, formula, term, number, expected, settings⟩
        | none => .error s!"not a budget: {budget}"
      | _ => .error s!"a row needs five fields: {line}"

/-- The source that checks a matrix. -/
def matrixSource (files : List String) (rows : List (Row × String)) : String :=
  "import Mettapedia.OSLF.NativeTypes.Product.Query\n" ++
  "open Mettapedia.GSLT.LanguageDef.ModuleSource.Commands\n" ++
  String.join (files.map fun file => s!"#module_file {file.quote}\n") ++
  "#eval Mettapedia.OSLF.NativeTypes.Product.checkRows [" ++
  ", ".intercalate (rows.map fun (row, base) =>
    s!"({row.file.quote}, {languageTerm base (splitTheory row.file).2}, {row.formula.quote}, {row.term.quote}, " ++
      s!"{row.budget}, " ++
      s!"{row.expected.quote}, {row.settings.map String.quote})") ++
  "]\n"

end Mettapedia.OSLF.NativeTypes.Product.Main

open Mettapedia.OSLF.NativeTypes.Product.Main in
def main (arguments : List String) : IO UInt32 := do
  match arguments with
  | ["--matrix", matrixFile] =>
    let path : System.FilePath := matrixFile
    let directory := path.parent.getD "."
    match readRows (← IO.FS.readFile path) with
    | .error problem =>
      IO.eprintln s!"oslf: {problem}"
      return 2
    | .ok rows =>
      let mut order : List String := []
      let mut named : List (Row × String) := []
      for row in rows do
        let file := (splitTheory row.file).1
        order ← loadOrder directory file order
        match moduleName (← IO.FS.readFile (directory / file)) with
        | some base => named := named ++ [(row, base)]
        | none =>
          IO.eprintln s!"oslf: {row.file} declares no Module"
          return 2
      initSearchPath (← findSysroot)
      unsafe Lean.enableInitializersExecution
      let result ← Lean.Elab.runFrontend (matrixSource order named) {}
        (directory / "OslfMatrix.lean").toString `OslfMatrix
      return if result.isSome then 0 else 1
  | argument :: formula :: term :: words =>
    let (file, theory) := splitTheory argument
    let budgets := words.filterMap String.toNat?
    let settings := words.filter (·.contains '=')
    let budgets := if budgets.isEmpty then [4] else budgets
    let path : System.FilePath := file
    let directory := path.parent.getD "."
    let name := path.fileName.getD file
    let order ← loadOrder directory name []
    let text ← IO.FS.readFile path
    match moduleName text with
    | none =>
      IO.eprintln s!"oslf: {file} declares no Module"
      return 2
    | some base =>
      initSearchPath (← findSysroot)
      unsafe Lean.enableInitializersExecution
      let result ← Lean.Elab.runFrontend (source order (languageTerm base theory) formula term budgets settings) {}
        (directory / "OslfQuery.lean").toString `OslfQuery
      return if result.isSome then 0 else 1
  | _ =>
    IO.eprintln usage
    return 2
