import Mettapedia.GSLT.LanguageDef.ModuleSource.LbnfDecode
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.IndexedInductiveAppendAnnotated

/-! Consume the live reader's decoded sources through the generated-policy
emitter. The selected emitted library is subsequently executed by the existing
append and observation gates. Parsing and typing reuse their existing owners. -/

open Mettapedia.GSLT.LanguageDef.ModuleSource
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.PeTTa
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeNaturalVectorFamilies

def permissionRows (selection : Programs.ComputationProfiles.Selection) : List Nat :=
  ((List.finRange Checking.table.length).filter fun index => selection index).map Fin.val

def computationRecord (selection : Programs.ComputationProfiles.Selection) : Lean.Json :=
  Lean.Json.mkObj [
    ("permissions", Lean.toJson (permissionRows selection)),
    ("nil_certificate_accepted", Lean.toJson
      (((Programs.ComputationProfiles.decoder selection).decode
        (Programs.Annotated.Append.nilCertificate selection)).isSome)),
    ("cons_certificate_accepted", Lean.toJson
      (((Programs.ComputationProfiles.decoder selection).decode
        (Programs.Annotated.Append.consCertificate selection)).isSome))]

/-- An exact checking subject and policy record. Native proof exports retain
their separate routes; these strings are qualification data, not a codec. -/
def annotationRecord (label : String)
    (result : Bridges.IndexedInductiveAppend.Annotated.Output) : Lean.Json :=
  Lean.Json.mkObj [
    ("case", .str label),
    ("judgment", .str "CumulativePiSigmaId.CTyped"),
    ("typing_permissions", Lean.toJson (permissionRows Programs.ComputationProfiles.naturalOnly)),
    ("source_function", .str (reprStr result.sourceFunction)),
    ("annotated_function", .str (reprStr result.annotation)),
    ("expected_type", .str (reprStr result.expectedType)),
    ("erasure_matches_source", Lean.toJson (decide (result.annotation.erase = result.sourceFunction))),
    ("annotation_matches_independent", Lean.toJson
      (decide (result.annotation = Programs.Annotated.Append.appendFunction))),
    ("type_matches_independent", Lean.toJson
      (decide (result.expectedType = Programs.Annotated.Append.appendFunctionType))),
    ("computation_policies", .arr #[computationRecord Programs.ComputationProfiles.naturalOnly,
      computationRecord Programs.Annotated.Append.naturalAndNil,
      computationRecord (fun _ => true)])]

def emitPacket (packet : Atom) (destination : System.FilePath)
    (annotationDestination : Option System.FilePath) : IO Unit := do
  let .expression (.symbol "AppendSourceReads" :: cases) := packet
    | throw (IO.userError "unexpected append source envelope")
  let mut seen : List String := []
  let mut selected : Option String := none
  let mut annotations : Array Lean.Json := #[]
  for item in cases do
    let .expression [.symbol "Case", .grounded (.string label), parsed] := item
      | throw (IO.userError "malformed source case")
    if seen.contains label then throw (IO.userError "duplicate source case")
    seen := label :: seen
    let .ok [tree] := LbnfDecode.acceptedTrees parsed
      | throw (IO.userError "exactly one accepted source tree required")
    let .ok source := LbnfDecode.decode tree
      | throw (IO.userError "source tree decoding failed")
    match Bridges.IndexedInductiveAppend.Annotated.emit? source with
    | some result =>
        if label == "valid" then selected := some result.text
        annotations := annotations.push (annotationRecord label result)
        IO.println s!"(AppendSourceEmission {reprStr label} NativeEmitted)"
    | none => IO.println s!"(AppendSourceEmission {reprStr label} NativeRefused)"
  let some text := selected
    | throw (IO.userError "selected source was absent or refused")
  IO.FS.writeFile destination text
  if let some path := annotationDestination then
    IO.FS.writeFile path ((Lean.Json.arr annotations).pretty ++ "\n")

def main (arguments : List String) : IO Unit := do
  let (input, output, annotations) ← match arguments with
    | [input, output] => pure (input, output, none)
    | [input, output, annotations] => pure (input, output, some annotations)
    | _ => throw (IO.userError "usage: emit_checked_append_source.lean PACKET LIBRARY [ANNOTATIONS]")
  let .ok [packet] := SpaceSemantics.readSource (← IO.FS.readFile input)
    | throw (IO.userError "expected one append reader packet")
  emitPacket packet output (annotations.map System.FilePath.mk)
