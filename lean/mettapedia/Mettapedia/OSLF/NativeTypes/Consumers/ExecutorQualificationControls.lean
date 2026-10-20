import Mettapedia.OSLF.NativeTypes.Consumers.ExecutorQualification
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.NativeTypes.RuntimeControls

/-! # Complete-packet contracts applied to actual native-query output. -/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Consumers.ExecutorQualification.Controls

open Mettapedia.Languages.MeTTa.PeTTa.Bridges.NativeTypes
open Mettapedia.OSLF.NativeTypes.Generation.IndexedModal
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.GSLT.LanguageDef

/-- This consumes output of the existing CeTTa/PeTTa gate. Its inputs must
still be qualified against the chosen backend; a wire packet is not a proof
that the backend actually implements Lean's operational semantics. -/
def checkOutput (text : String) : IO Unit := do
  let fixtures ← RuntimeControls.fixtures
  let output ← RuntimeControls.parseOutput text
  let paused := fixtures.filterMap fun fixture =>
    fixture.splitAt.map fun first => fixture.paused first
  let mut compared := 0
  let mut separated := false
  for fixture in fixtures ++ paused do
    let session := Discovery.begin fixture.question
    let positions := List.finRange (Discovery.sources fixture.question).length
    let mut atoms := []
    for position in positions do
      let some row := output.find? (fun row => row.1 == fixture.label && row.2.1 == position.val)
        | throw (IO.userError ("Missing actual native packet: " ++ fixture.label))
      atoms := atoms ++ [row.2.2]
    if size : atoms.length = (Discovery.sources fixture.question).length then
      let packets : QueryTransport.Packets fixture.question :=
        fun position => atoms[position.val]'(by omega)
      if !checkPackets session fixture.fuel packets then
        throw (IO.userError ("Complete-packet native contract failed: " ++ fixture.label))
      compared := compared + 1
      if fixture.label == "provider-duplicate-origins" then
        for position in positions do
          let some observation := SourceExecution.decodeAtom? (packets position)
            | throw (IO.userError "Actual packet did not decode")
          if observation.payloads.length > 1 then
            let trimmed := Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CettaWireAtom.encode
              {observation with payloads := observation.payloads.tail}.term
            let modified : QueryTransport.Packets fixture.question :=
              fun candidate => if candidate == position then trimmed else packets candidate
            if checkPackets session fixture.fuel modified then
              throw (IO.userError "Contract lost an equal-target origin")
            if QueryTransport.receive fixture.question packets == some .proved &&
                QueryTransport.receive fixture.question modified == some .proved then
              separated := true
    else throw (IO.userError "Packet arity mismatch")
  if !separated then
    throw (IO.userError "Expected verdict-equality/receipt-inequality separator did not run")
  IO.println s!"Complete-packet native contracts: {compared} passed"
  IO.println "Equal Proved verdicts do not imply complete receipt preservation: passed"

end Mettapedia.OSLF.NativeTypes.Consumers.ExecutorQualification.Controls
