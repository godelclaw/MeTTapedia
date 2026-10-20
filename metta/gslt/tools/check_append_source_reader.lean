import Mettapedia.GSLT.LanguageDef.ModuleSource.LbnfDecode
import Mettapedia.GSLT.LanguageDef.IndexedInductiveAppendChecking

/-!
The grammar-driven reader submits data to the same operation producer and
dependent replay as the Lean source fixture, under its actual generated
natural-only checking policy. Raw and explicitly name-resolved data are
compared for the selected positive input. Packed-parser completeness and
Prime execution remain separate obligations.
-/

open Mettapedia.GSLT.LanguageDef.ModuleSource
open Mettapedia.GSLT.LanguageDef.IndexedInductive
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)

def expectations : List (String × Bool) := [
  ("valid", true), ("alpha", true), ("wrong-child", false), ("omitted-recursion", false),
  ("wrong-index", false), ("unbound", false), ("missing-clause", false),
  ("extra-block", false), ("negative-field", false), ("wrong-entry", false)]

def normalizeSource (source : ModuleData) : Option ModuleData := do
  let selected ← OperationSource.selectModule source
  let rows := selected.rules.map
    (OperationSource.resolveRule AppendSource.constructorSymbols .declaredNullary)
  return { selected with rules := rows }.assemble

def checkPacket (packet : Atom) : IO Unit := do
  let .expression (.symbol "AppendSourceReads" :: cases) := packet
    | throw (IO.userError "unexpected append source envelope")
  unless cases.length == expectations.length do
    throw (IO.userError "missing or extra append reader cases")
  for (item, (label, expected)) in cases.zip expectations do
    let .expression [.symbol "Case", .grounded (.string name), parsed] := item
      | throw (IO.userError "malformed append reader case")
    unless name == label do throw (IO.userError "reordered or duplicate append reader case")
    let decoded := LbnfDecode.acceptedTrees parsed >>= fun trees => match trees with
      | [tree] => LbnfDecode.decode tree
      | _ => .error "exactly one source parse required"
    let .ok source := decoded
      | throw (IO.userError s!"{label}: no unique decoded source: {repr decoded}")
    if label == "valid" then
      let rawAgreement := reprStr source == reprStr AppendSource.IndexedNatVecAppend.module
      IO.println s!"(AppendSourceRawAgreement {rawAgreement})"
      unless rawAgreement do throw (IO.userError "raw grammar data differs from the Lean source")
      unless (normalizeSource source).isSome &&
          reprStr (normalizeSource source) == reprStr
            (normalizeSource AppendSource.IndexedNatVecAppend.module) do
        throw (IO.userError "name-resolved grammar data differs from the Lean source")
    unless AppendChecking.replaySource AppendChecking.naturalOnly source == expected do
      throw (IO.userError s!"{label}: wrong dependent replay verdict")
    IO.println s!"(AppendSourceReaderControl {label} true)"
  let permitted := (List.range
    Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeNaturalVectorFamilies.Checking.table.length).filter
      AppendChecking.naturalOnly
  IO.println s!"(AppendSourceCheckingPolicy {permitted})"

def main (args : List String) : IO Unit := do
  let [input] := args | throw (IO.userError "usage: check_append_source_reader.lean PACKET")
  match Mettapedia.Languages.MeTTa.PeTTa.SpaceSemantics.readSource (← IO.FS.readFile input) with
  | .ok [packet] => checkPacket packet
  | .ok _ => throw (IO.userError "expected one append reader packet")
  | .error error => throw (IO.userError s!"malformed reader packet: {error}")
