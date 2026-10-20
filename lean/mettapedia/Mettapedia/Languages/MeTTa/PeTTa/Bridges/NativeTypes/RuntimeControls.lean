import Mettapedia.Languages.MeTTa.PeTTa.Bridges.NativeTypes.SourceExecution
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.NativeTypes.QueryTransport
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.NativeTypes.QueryExecution
import Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.Discovery.ControlsProviders
import Mettapedia.Languages.MeTTa.PeTTa.ReadAfterRender

/-!
# Target-executed native receipt controls

Independent finite native questions generate actual descent programs. Their
returned packets are parsed with the existing PeTTa reader and rechecked by
the existing native response-family checker. The packet comparison includes
the environment, goal, retained scheduler state and every receipt field.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.NativeTypes.RuntimeControls

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.OSLF.MeTTaIL Syntax GeneralPremise StructuralDescent
open Mettapedia.OSLF.NativeTypes.Modal NativeReceiptRechecking
open Mettapedia.OSLF.NativeTypes.Generation
open IndexedModal FiniteFocusChecking FocusMeaning Discovery
open Discovery.ControlsParameters Discovery.ControlsPreparation
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open MeTTaIL CompleteExecution WireKit

structure Fixture where
  label : String
  installed : Joined.Installed
  ambient : List String
  question : FocusQuery.Question installed ambient
  fuel : Nat
  expected : Discovery.Verdict
  splitAt : Option Nat := none
  origins : Option (List Nat) := none
  scopedHistory : Bool := false
  providerRows : List Nat := []

def Fixture.session (fixture : Fixture) : Discovery.Session fixture.question :=
  Discovery.discover fixture.question fixture.fuel

abbrev Fixture.source (fixture : Fixture) (position : Fin (Discovery.sources fixture.question).length) :
    SourceExecution.Source :=
  QueryTransport.sourceAt fixture.question position

def Fixture.expectedPacket (fixture : Fixture)
    (position : Fin (Discovery.sources fixture.question).length) : Atom :=
  QueryTransport.observeSession fixture.session position

def Fixture.code (fixture : Fixture) (position : Fin (Discovery.sources fixture.question).length) : Atom :=
  SourceExecution.startCode fixture.installed.indexed.operational.Environment (fixture.source position)
    (fixture.splitAt.getD fixture.fuel)

def Fixture.paused (fixture : Fixture) (first : Nat) : Fixture :=
  {fixture with
    label := fixture.label ++ "-paused"
    fuel := first
    expected := .unknown
    splitAt := none
    origins := none
    scopedHistory := false
    providerRows := []}

def fixtures : IO (List Fixture) := do
  let lambda ← install BindingPipeline.Controls.originalLambda
  let question ← expect (lambdaQuestion lambda)
  let root ← expect (rootQuestion lambda)
  let binder ← expect (binderQuestion lambda)
  let letCase ← install BindingPipeline.Controls.originalLetCase
  let pair ← expect (caseQuestion letCase)
  let shared ← install indexedLanguage
  let first ← expect (sharedQuestion shared 0)
  let second ← expect (sharedQuestion shared 1)
  let changed ← expect (prepareAt shared [] 0 [0] [("x", .apply "F1" [])]
    [("x", [.apply "F1" []])] (fun _ _ _ target => target == Consumers.sharedTarget) (.apply "F0" []))
  let provider ← Discovery.ControlsProviders.install
    [⟨"permit", [.apply "F0" []]⟩, ⟨"permit", [.apply "F0" []]⟩]
  let permitted ← expect (sharedQuestion provider 0)
  let missing ← Discovery.ControlsProviders.install []
  let denied ← expect (sharedQuestion missing 0)
  let ambient ← expect (prepareAt lambda ["Term"] 0 [0] []
    [("A", [.bvar 0, identity])] (fun _ => lambdaTarget) identity)
  let outerTarget := Pattern.apply "Lam" [.lambda none (.bvar 1)]
  let ambientBinder ← expect (prepareAt lambda ["Term"] 1 [0, 0] [] []
    (fun _ _ _ target => target == outerTarget) (.apply "App" [identity, .bvar 1]))
  pure [
    ⟨"lambda-full", lambda, [], question, 2000, .proved, none, none, false, []⟩,
    ⟨"lambda-zero", lambda, [], question, 0, .unknown, none, none, false, []⟩,
    ⟨"lambda-short", lambda, [], question, 1, .unknown, none, none, false, []⟩,
    ⟨"lambda-split", lambda, [], question, 2000, .proved, some 7, none, false, []⟩,
    ⟨"lambda-dependent-false", lambda, [], constantIdentityTarget question, 2000, .refuted, none, none, false, []⟩,
    ⟨"root-zero-rely", lambda, [], root, 2000, .proved, none, none, false, []⟩,
    ⟨"root-false-target", lambda, [], falseTarget root, 2000, .refuted, none, none, false, []⟩,
    ⟨"binder-local", lambda, [], binder, 2000, .proved, none, none, true, []⟩,
    ⟨"binder-false-target", lambda, [], falseTarget binder, 2000, .refuted, none, none, true, []⟩,
    ⟨"paircase-four", letCase, [], pair, 2000, .proved, none, none, false, []⟩,
    ⟨"paircase-false-target", letCase, [], falseTarget pair, 2000, .refuted, none, none, false, []⟩,
    ⟨"shared-first", shared, [], first, 500, .proved, none, some [0, 1], false, []⟩,
    ⟨"shared-second", shared, [], second, 500, .proved, none, some [0, 1], false, []⟩,
    ⟨"shared-changed-index", shared, [], changed, 500, .refuted, none, some [], false, []⟩,
    ⟨"provider-duplicate-origins", provider, [], permitted, 500, .proved, none, some [0, 0], false, [0, 1]⟩,
    ⟨"provider-absent", missing, [], denied, 500, .refuted, none, some [], false, []⟩,
    ⟨"ambient-argument", lambda, ["Term"], ambient, 2000, .proved, none, none, false, []⟩,
    ⟨"ambient-under-binder", lambda, ["Term"], ambientBinder, 2000, .proved, none, none, true, []⟩,
    ⟨"ambient-false-target", lambda, ["Term"], falseTarget ambientBinder, 2000, .refuted, none, none, true, []⟩]

private def render (atom : Atom) : IO String :=
  match ReadAfterRender.render? atom with
  | some text => pure text
  | none => throw (IO.userError "Native fixture atom has no exact source rendering")

private def control (label : String) (position : Nat) (code expected : Atom) : IO String := do
  let source ← render code
  let wanted ← render expected
  let key := reprStr (label ++ ":" ++ toString position)
  pure ("!(let $packet " ++ source ++
    " (let $printed (println! (NativeSourcePacket " ++ reprStr label ++ " " ++ toString position ++ " $packet))" ++
    " (println! (NativeReceiptControl " ++ key ++ " (== $packet (quote " ++ wanted ++ "))))))")

def generate (fixtures : List Fixture) : IO String := do
  let mut lines := ["; Generated native source observations; run the native receipt output checker."]
  for fixture in fixtures do
    for position in List.finRange (Discovery.sources fixture.question).length do
      let initialLabel := if fixture.splitAt.isSome then fixture.label ++ "-paused" else fixture.label
      let initial := Discovery.discover fixture.question (fixture.splitAt.getD fixture.fuel)
      lines := lines ++ [← control initialLabel position.val (fixture.code position)
        (QueryTransport.observeSession initial position)]
  pure (String.intercalate "\n" lines ++ "\n")

def parseOutput (text : String) : IO (List (String × Nat × Atom)) := do
  let mut packets := []
  let mut controls : List String := []
  for line in text.splitOn "\n" do
    if line.startsWith "(NativeSourcePacket " || line.startsWith "(NativeReceiptControl " then
      let atoms ← expect (SpaceSemantics.readSource line)
      match atoms with
      | [.expression [.symbol "NativeSourcePacket", .grounded (.string label),
          .grounded (.int (.ofNat position)), packet]] =>
          if packets.any (fun entry => entry.1 == label && entry.2.1 == position) then
            throw (IO.userError "Duplicate native source packet")
          packets := packets ++ [(label, position, packet)]
      | [.expression [.symbol "NativeReceiptControl", .grounded (.string label), .grounded (.bool true)]] =>
          if controls.contains label then throw (IO.userError "Duplicate native receipt comparison")
          controls := controls ++ [label]
      | _ => throw (IO.userError "Malformed or failing native receipt output")
  if controls.length != packets.length then
    throw (IO.userError "Native packet/comparison counts disagree")
  for (label, position, _) in packets do
    if !controls.contains (label ++ ":" ++ toString position) then
      throw (IO.userError "Native packet lacks its complete payload comparison")
  pure packets

/-- Resume expressions are built from snapshots returned by the engine.
Constructing them never advances the Lean reference scheduler. -/
def generateResume (fixtures : List Fixture) (text : String) : IO String := do
  let output ← parseOutput text
  let mut lines := ["; Resume the actual returned target snapshots."]
  for fixture in fixtures do
    if let some first := fixture.splitAt then
      for position in List.finRange (Discovery.sources fixture.question).length do
        let some row := output.find? (fun row => row.1 == (fixture.paused first).label &&
            row.2.1 == position.val)
          | throw (IO.userError "Paused target packet missing before continuation")
        let some code := QueryExecution.continue? fixture.question position row.2.2 (fixture.fuel - first)
          | throw (IO.userError "Paused target snapshot failed exact context validation")
        lines := lines ++ [← control fixture.label position.val code (fixture.expectedPacket position)]
  pure (String.intercalate "\n" lines ++ "\n")

def checkFixture (fixture : Fixture) (output : List (String × Nat × Atom)) : IO Unit := do
  let mut atoms := []
  for position in List.finRange (Discovery.sources fixture.question).length do
    let some row := output.find? (fun row => row.1 == fixture.label && row.2.1 == position.val)
      | throw (IO.userError ("Missing native packet: " ++ fixture.label))
    if row.2.2 != fixture.expectedPacket position then
      throw (IO.userError ("Target packet differs from its complete Lean source observation: " ++ fixture.label))
    atoms := atoms ++ [row.2.2]
  if size : atoms.length = (Discovery.sources fixture.question).length then
    let packets : QueryTransport.Packets fixture.question :=
      fun position => atoms[position.val]'(by omega)
    let certified ←
      if agreed : (List.finRange (Discovery.sources fixture.question).length).all
          (fun position => decide (packets position = fixture.expectedPacket position)) = true then
        pure (⟨funext fun position => of_decide_eq_true
          (List.all_eq_true.mp agreed position (List.mem_finRange position))⟩ :
          PLift (packets = QueryTransport.observeSession fixture.session))
      else throw (IO.userError "Actual target packets lack full source-session correspondence")
    let replay := certified.down
    let some readout := QueryTransport.decodeBatch? fixture.question packets
      | throw (IO.userError "Actual target packets failed exact native transport")
    if readout.certificate != fixture.session.certificate || readout.settled != fixture.session.settled then
      throw (IO.userError "Received target evidence changed certificate, origin order or settlement")
    if QueryTransport.receive fixture.question packets != some fixture.expected then
      throw (IO.userError ("Wrong received native verdict: " ++ fixture.label))
    if fixture.expected == .proved then
      let some membership := QueryTransport.membership? fixture.question packets
        | throw (IO.userError "Received proof did not expose its executable response family")
      for values in (requests fixture.question.parameters).attach do
        let response := membership.family.respond values.val
          ((requests_exact fixture.question.parameters values.val).mp values.property)
        if !fixture.question.parameters.target values.val response.receipt.firing.answer.completed
            response.receipt.firing.answer.target then
          throw (IO.userError "Received family failed an independently declared target")
        if response.receipt.firing.answer.index != (fixture.installed.indexed.schema fixture.question.index).ordinal then
          throw (IO.userError "Received response selected another declaration's origin")
    if fixture.expected == .refuted then
      if !readout.settled || (QueryTransport.membership? fixture.question packets).isSome then
        throw (IO.userError "Received refutation lacks complete failed coverage")
      let some counterexample := QueryTransport.counterexample? fixture.session packets replay
        | throw (IO.userError "Received refutation lost its counterexample tuple")
      let _absent : ¬ fixture.question.Meaning := counterexample.not_member
      if readout.certificate.any
          (accepts fixture.question.parameters fixture.question.focus counterexample.values) then
        throw (IO.userError "Received counterexample has a response")
    if fixture.expected == .unknown && readout.settled then
      throw (IO.userError "Unfinished control unexpectedly drained")
    if fixture.expected == .unknown && (QueryTransport.counterexample? fixture.session packets replay).isSome then
      throw (IO.userError "Unfinished execution produced a semantic counterexample")
    if let some origins := fixture.origins then
      if readout.certificate.map (·.payload.index) != origins then
        throw (IO.userError "Declaration origins were invented, merged or reordered")
    if fixture.scopedHistory && !readout.certificate.any (fun witness => !witness.payload.history.isEmpty) then
      throw (IO.userError "Scoped premise history was dropped")
    if !fixture.providerRows.isEmpty then
      let rows := readout.certificate.flatMap fun witness => witness.payload.history.filterMap fun event =>
        match event with | .query _ _ row _ => some row | _ => none
      if rows != fixture.providerRows then throw (IO.userError "Distinct provider origins were merged")
    if !readout.certificate.isEmpty then
      if (QueryTransport.receive fixture.question (fun _ => .symbol "MalformedPacket")).isSome then
        throw (IO.userError "Malformed packets were accepted")
      for position in List.finRange (Discovery.sources fixture.question).length do
        let environment := fixture.installed.indexed.operational.Environment
        let source := fixture.source position
        let some observation := SourceExecution.decodeAtom? (packets position)
          | throw (IO.userError "Exact target observation failed physical decoding")
        let badEnvironment := {observation with environment := .symbol "WrongEnvironment"}
        if (QueryTransport.decodeSource? environment source (CettaWireAtom.encode badEnvironment.term)).isSome then
          throw (IO.userError "Wrong operational environment was accepted")
        if (QueryTransport.receive fixture.question (fun other =>
            if other == position then CettaWireAtom.encode badEnvironment.term else packets other)).isSome then
          throw (IO.userError "Wrong operational environment became a semantic verdict")
        let wrongGoal := {observation with goal := .symbol "WrongGoal"}
        if (QueryTransport.decodeSource? environment source (CettaWireAtom.encode wrongGoal.term)).isSome then
          throw (IO.userError "Wrong source or binder context was accepted")
        if (QueryTransport.receive fixture.question (fun other =>
            if other == position then CettaWireAtom.encode wrongGoal.term else packets other)).isSome then
          throw (IO.userError "Wrong source or binder context became a semantic verdict")
    IO.println ("NativeQueryCheck " ++ fixture.label ++ " " ++ reprStr fixture.expected ++
      " sources=" ++ toString atoms.length ++ " receipts=" ++ toString readout.certificate.length)
  else throw (IO.userError "Actual target packet count differs from its source family")

def check (fixtures : List Fixture) (text : String) : IO Unit := do
  let output ← parseOutput text
  let expected := (fixtures.map (fun fixture => (Discovery.sources fixture.question).length)).sum
  let paused := (fixtures.filterMap fun fixture =>
    fixture.splitAt.map fun first => fixture.paused first)
  let pausedCount := (paused.map (fun fixture => (Discovery.sources fixture.question).length)).sum
  if output.length != expected + pausedCount then throw (IO.userError "Unexpected native source packet count")
  for fixture in fixtures ++ paused do checkFixture fixture output
  IO.println ("NativeQueryGate " ++ toString (fixtures.length + paused.length) ++ " questions " ++
    toString output.length ++ " packets")

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.NativeTypes.RuntimeControls
