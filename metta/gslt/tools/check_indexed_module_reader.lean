import Mettapedia.GSLT.LanguageDef.ModuleSource.LbnfDecode
import Mettapedia.GSLT.LanguageDef.ModuleSource.IndexedNatVecSourceControls

/-! The grammar-driven reader and Lean reader meet at the shared source data.
This gate qualifies the named Nat/Vec frontend; it is not a completeness proof
for packed parsing or a qualification of dependent program execution. -/

open Mettapedia.GSLT.LanguageDef.ModuleSource
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)

def expectations : List (String × Bool) := [
  ("valid", true), ("alpha", true), ("negative-field", false),
  ("payload-shadow", false), ("recursive-shadow", false), ("global-shadow", false),
  ("wrong-result", false), ("wrong-parameter", false), ("wrong-entry", false),
  ("extra-import", false), ("duplicate-constructor", false), ("unknown-field", false)]

def checkPacket (packet : Atom) : IO Unit := do
  let .expression (.symbol "IndexedModuleReads" :: cases) := packet
    | throw (IO.userError "unexpected indexed reader envelope")
  unless cases.length == expectations.length do
    throw (IO.userError "missing or extra indexed reader cases")
  for (item, (label, expected)) in cases.zip expectations do
    let .expression [.symbol "Case", .grounded (.string name), parsed] := item
      | throw (IO.userError "malformed indexed reader case")
    unless name == label do throw (IO.userError "reordered or duplicate indexed reader case")
    let decoded := LbnfDecode.acceptedTrees parsed >>= fun trees => match trees with
      | [tree] => LbnfDecode.decode tree
      | _ => .error "exactly one source parse required"
    let .ok source := decoded
      | throw (IO.userError s!"{label}: no unique decoded source: {repr decoded}")
    if label == "valid" then
      unless reprStr source == reprStr IndexedNatVecSourceControls.IndexedNatVec.module do
        throw (IO.userError "grammar-driven source differs from Lean source")
    unless IndexedNatVecSource.check IndexedNatVecSourceControls.names source == expected do
      throw (IO.userError s!"{label}: wrong frontend verdict")
    IO.println s!"(IndexedModuleReaderControl {label} true)"

def main (args : List String) : IO Unit := do
  let [input] := args | throw (IO.userError "usage: check_indexed_module_reader.lean PACKET")
  match Mettapedia.Languages.MeTTa.PeTTa.SpaceSemantics.readSource (← IO.FS.readFile input) with
  | .ok [packet] => checkPacket packet
  | .ok _ => throw (IO.userError "expected one indexed reader packet")
  | .error error => throw (IO.userError s!"malformed reader packet: {error}")
