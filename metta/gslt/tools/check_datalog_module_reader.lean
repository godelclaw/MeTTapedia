import Mettapedia.GSLT.LanguageDef.ModuleSource.LbnfDecode
import Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalog
import Mettapedia.GSLT.LanguageDef.ModuleSource.CollectionLiteralControls

/-! Replay actual grammar-reader packets against the independently read source
modules. This finite control does not assert packed-parser completeness. -/

open Mettapedia.GSLT.LanguageDef ModuleSource ModuleFormat.SouffleDatalog
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)

def expected : List (String × ModuleData) :=
  [("kernel", GroundKernel.module), ("printed-kernel", GroundKernel.module),
   ("core", Core.module), ("printed-core", Core.module),
   ("language", Language.module), ("printed-language", Language.module),
   ("printed-collections", CollectionLiteralControls.CollectionLiterals.module),
   ("printed-options", CollectionLiteralControls.CollectionWrappers.module)]

def exportPrinted (directory : System.FilePath) : IO Unit := do
  IO.FS.createDirAll directory
  for (name, source) in expected do
    if name.startsWith "printed-" then
      IO.FS.writeFile (directory / (name ++ ".module")) (Printer.print source)

def check (input : System.FilePath) : IO Unit := do
  let .ok [.expression (.symbol "DatalogModuleReads" :: cases)] :=
      Mettapedia.Languages.MeTTa.PeTTa.SpaceSemantics.readSource (← IO.FS.readFile input)
    | throw (IO.userError "expected one DatalogModuleReads packet")
  unless cases.length == expected.length do throw (IO.userError "wrong case count")
  for (entry, (name, source)) in cases.zip expected do
    let .expression [.symbol "Case", .grounded (.string label), parsed] := entry
      | throw (IO.userError "malformed case")
    unless label == name do throw (IO.userError "changed case order or identity")
    let .ok trees := LbnfDecode.acceptedTrees parsed
      | throw (IO.userError s!"{name}: source refused")
    let [tree] := trees | throw (IO.userError s!"{name}: expected one selected syntax tree")
    let .ok decoded := LbnfDecode.decode tree
      | throw (IO.userError s!"{name}: source decode failed")
    unless reprStr decoded == reprStr source do
      let actual := (reprStr decoded).toList
      let wanted := (reprStr source).toList
      let offset := (actual.zip wanted).findIdx (fun pair => pair.1 != pair.2)
      throw (IO.userError (s!"{name}: the two readers disagree at {offset}: " ++
        String.ofList (actual.drop (offset - 60) |>.take 180) ++ " versus " ++
        String.ofList (wanted.drop (offset - 60) |>.take 180)))
    IO.println s!"(DatalogModuleReaderControl {name} true)"

def main (arguments : List String) : IO Unit := do
  match arguments with
  | ["print", directory] => exportPrinted directory
  | ["check", packet] => check packet
  | _ => throw (IO.userError "usage: check_datalog_module_reader.lean print DIRECTORY | check PACKET")
