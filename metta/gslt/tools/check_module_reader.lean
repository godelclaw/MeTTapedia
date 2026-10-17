/-
The two `.module` readers agree: CeTTa's parse of each upstream example with the grammar
`module/module_v1.cf`, decoded by `ModuleSource.LbnfDecode`, is the data that `#module_file`
reads in Lean. Run by `check_module_reader.sh`, which writes CeTTa's parses first.
-/
import Mettapedia.GSLT.LanguageDef.ModuleSource.Commands
import Mettapedia.GSLT.LanguageDef.ModuleSource.LbnfDecode
open Mettapedia.GSLT.LanguageDef.ModuleSource.Commands
#module_file "../../../lean/mettapedia/artifacts/upstream-authoring-20261008/UnivAlg.module"
#module_file "../../../lean/mettapedia/artifacts/upstream-authoring-20261008/Rholang.module"
open Mettapedia.GSLT.LanguageDef.ModuleSource
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)

def check : IO Unit := do
  let source ← IO.FS.readFile "../../metta/gslt/tools/out/module_reads.metta"
  match Mettapedia.Languages.MeTTa.PeTTa.SpaceSemantics.readSource source with
  | .error e => IO.println s!"read error {e}"
  | .ok [.expression [_, univalg, rholang]] =>
      for (label, parsed, lean) in [("UnivAlg", univalg, UnivAlg.module), ("Rholang", rholang, Rholang.module)] do
        match LbnfDecode.acceptedTrees parsed >>= fun trees => match trees with
            | [tree] => LbnfDecode.decode tree
            | _ => .error "expected one tree" with
        | .error e => IO.println s!"(ModuleReaderControl {label} false) decode error {e}"
        | .ok decoded =>
            if reprStr decoded == reprStr lean then IO.println s!"(ModuleReaderControl {label} true)"
            else
              let a := (reprStr decoded).toList
              let b := (reprStr lean).toList
              let i := (List.zip a b).findIdx (fun p => p.1 != p.2)
              IO.println s!"(ModuleReaderControl {label} false) differ at {i}: {String.ofList (a.drop (i-80) |>.take 220)} ||| {String.ofList (b.drop (i-80) |>.take 220)}"
  | .ok other => IO.println s!"unexpected shape {other.length}"
#eval check
