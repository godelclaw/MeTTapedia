/-
Fixture agreement of the two `.module` readers: CeTTa's parse of each upstream example with the grammar
`module/module_v1.cf`, decoded by `ModuleSource.LbnfDecode`, is the data that `#module_file`
reads in Lean. Run by `check_module_reader.sh`, which writes CeTTa's parses first.
Every malformed packet or disagreement fails the process. This fixture check
does not certify completeness of a packed parse forest.
-/
import Mettapedia.GSLT.LanguageDef.ModuleSource.Commands
import Mettapedia.GSLT.LanguageDef.ModuleSource.LbnfDecode
open Mettapedia.GSLT.LanguageDef.ModuleSource.Commands
#module_file "../../../lean/mettapedia/artifacts/upstream-authoring-20261008/UnivAlg.module"
#module_file "../../../lean/mettapedia/artifacts/upstream-authoring-20261008/Rholang.module"
open Mettapedia.GSLT.LanguageDef.ModuleSource
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)

def check (input : System.FilePath) : IO Unit := do
  let source ← IO.FS.readFile input
  match Mettapedia.Languages.MeTTa.PeTTa.SpaceSemantics.readSource source with
  | .error e => throw (IO.userError s!"read error {e}")
  | .ok [.expression [.symbol "ModuleReads", univalg, rholang]] =>
      for (label, parsed, lean) in [("UnivAlg", univalg, UnivAlg.module), ("Rholang", rholang, Rholang.module)] do
        match LbnfDecode.acceptedTrees parsed >>= fun trees => match trees with
            | [tree] => LbnfDecode.decode tree
            | _ => .error "expected one tree" with
        | .error e => throw (IO.userError s!"(ModuleReaderControl {label} false) decode error {e}")
        | .ok decoded =>
            if reprStr decoded == reprStr lean then IO.println s!"(ModuleReaderControl {label} true)"
            else
              let a := (reprStr decoded).toList
              let b := (reprStr lean).toList
              let i := (List.zip a b).findIdx (fun p => p.1 != p.2)
              throw (IO.userError s!"(ModuleReaderControl {label} false) differ at {i}: {String.ofList (a.drop (i-80) |>.take 220)} ||| {String.ofList (b.drop (i-80) |>.take 220)}")
  | .ok other => throw (IO.userError s!"unexpected packet shape ({other.length} expressions)")

def main (args : List String) : IO Unit := do
  match args with
  | [] => check "../../metta/gslt/tools/out/module_reads.metta"
  | [input] => check input
  | _ => throw (IO.userError "usage: check_module_reader.lean [packet-file]")
