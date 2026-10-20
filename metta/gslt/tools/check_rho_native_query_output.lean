import Mettapedia.Languages.MeTTa.PeTTa.Bridges.NativeTypes.RhoRuntimeMeaning

open Mettapedia.Languages.MeTTa.PeTTa.Bridges.NativeTypes.RhoRuntime
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)

private def dropLog : Atom → Atom
  | .expression [.symbol "LCons", _, tail] => tail
  | other => other

private def dropReceipt : Atom → Atom
  | .expression [.symbol "RhoNativeReadout", plan, policy, source, normal, target,
      .expression [.symbol "ClassState", round, reps, entries, log],
      .expression [.symbol "ClassReadout", members, readoutLog, complete], result] =>
    .expression [.symbol "RhoNativeReadout", plan, policy, source, normal, target,
      .expression [.symbol "ClassState", round, reps, entries, dropLog log],
      .expression [.symbol "ClassReadout", members, dropLog readoutLog, complete], result]
  | other => other

private def changeField (index : Nat) (value : Atom) : Atom → Atom
  | .expression fields => .expression (fields.set index value)
  | other => other

private def outputText (packets : List (String × Atom)) : IO String := do
  let mut lines := []
  for (label, packet) in packets do
    let some text := Mettapedia.Languages.MeTTa.PeTTa.ReadAfterRender.render? packet
      | throw (IO.userError "Altered packet has no exact rendering")
    lines := lines ++ ["(RhoNativePacket " ++ reprStr label ++ " " ++ text ++ ")",
      "(RhoNativeControl " ++ reprStr label ++ " True)"]
  pure (String.intercalate "\n" lines ++ "\n")

private def mutationRejected (packets : List (String × Atom)) (label : String)
    (modify : Atom → Atom) : IO Unit := do
  let altered := packets.map fun (key, packet) => (key, if key == label then modify packet else packet)
  if altered == packets then throw (IO.userError "Negative packet control did not alter its input")
  let text ← outputText altered
  let rejected ← try check text; pure false catch _ => pure true
  if !rejected then throw (IO.userError "Altered rho packet retained semantic authority")

private def qualify (text : String) : IO Unit := do
  check text
  let packets ← parseOutput text
  let paused := fixtures.filterMap fun fixture => fixture.splitAt.map (fixture.paused)
  for fixture in fixtures ++ paused do
    let original : PLift (Mettapedia.GSLT.LanguageDef.WellSorted.checkOpenPatternWellSorted
        spec.plan.snapshot.language spec.plan.snapshot.free spec.bound spec.expected fixture.source = true) ←
      if admitted : Mettapedia.GSLT.LanguageDef.WellSorted.checkOpenPatternWellSorted
          spec.plan.snapshot.language spec.plan.snapshot.free spec.bound spec.expected fixture.source = true then
        pure ⟨admitted⟩
      else throw (IO.userError "Rho runtime fixture was not admitted at its original source")
    let some (_, packet) := packets.find? (fun item => item.1 == fixture.label)
      | throw (IO.userError "Native proof readback lost its packet")
    if accepted : acceptsPacket fixture packet = true then
      match polarity : packetVerdict packet with
      | some .proved =>
        let _membership : NativeMeaning fixture.source fixture.target :=
          accepted_packet_proved fixture packet accepted polarity
        let _admittedMembership := accepted_admitted_proved fixture packet original.down accepted polarity
        pure ()
      | some .refuted =>
        let _nonmembership : ¬ NativeMeaning fixture.source fixture.target :=
          accepted_packet_refuted fixture packet accepted polarity
        pure ()
      | some .unknown => pure ()
      | none => throw (IO.userError "Native packet has no declared polarity")
    else throw (IO.userError "Native packet failed full proof readback")
    if fixture.label == "duplicate-matches" then
      match fixture.state.log with
      | [first, second] =>
        if Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution.classReceiptTerm first ==
            Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution.classReceiptTerm second then
          throw (IO.userError "Duplicate fixture repeated one packet instead of two physical matches")
        if first.target != second.target then
          throw (IO.userError "Duplicate fixture does not exercise equal-target receipt retention")
      | _ => throw (IO.userError "Duplicate fixture lost a physical matching occurrence")
  mutationRejected packets "quote-drop-positive" (changeField 1 (.symbol "WrongPlan"))
  mutationRejected packets "quote-drop-positive" (changeField 2 (.symbol "WrongPolicy"))
  mutationRejected packets "quote-drop-positive" (changeField 3 (.symbol "WrongSource"))
  mutationRejected packets "quote-drop-positive" (changeField 5 (.symbol "WrongTarget"))
  mutationRejected packets "duplicate-matches" dropReceipt
  mutationRejected packets "zero-work" (changeField 8 (.symbol "RhoRefuted"))
  IO.println "RhoNativeAuthority 10 admitted packets, 7 decided native judgments, 6 altered-packet controls"

def main (arguments : List String) : IO Unit := do
  let [output] := arguments
    | throw (IO.userError "usage: check_rho_native_query_output.lean ENGINE_OUTPUT")
  qualify (← IO.FS.readFile output)
