import Mettapedia.Languages.MeTTa.MeTTaAuthoredProgramExecution
import Mettapedia.Languages.GuardedAtomRule.Services
import Mettapedia.Languages.MeTTa.PeTTa.ProgramReplay

/-!
# Running pinned and live-store Atom profiles

`pettaRun MODE REQUESTS FUEL PROGRAM...` retains the original pinned `stream`
and `requests` modes. Stream runs program initializers with parsed input;
requests evaluates separate expressions with persistent private spaces/cells.

`live-requests` instead indexes the current stored equations and declarations
at each original transition. Its fuel may be one natural number or a schedule
such as `8+492`; chunks retain the same configuration without replaying effects.
This explicit live-store profile differs from PeTTa's translated code-entry
policy. It is not an unqualified whole-engine adapter.

`pettaRun atom-services REQUESTS` runs the source `fresh`, `match-value` and
`match-binding` operations through their source Pattern packets. The additive request
`(proof-root (ROWS...) ARTICLE SUBJECT TARGET)` checks a canonical explicit
article against the submitted original source rows and claimed endpoint. It
does not assert that the submitted rows are the current mutable world. Matching requests give
an explicit incoming substitution such as `(("x" a))`; an empty one is `()`.
Unknown forms retain their original Atom. This mode supplies primitive services,
not a replacement evaluation policy for any of the three execution modes.

`pettaRun authored-program POLICY PROGRAM BUDGET MODULE...` runs the explicit
conditional Atom profile, including finite provided module commands. POLICY is
`pinned` for immutable call-entry guard evidence or `current` for exact
current-world authorization. MODULE paths are provided quoted-string keys,
resolved only from the supplied module list. Source unknowns remain distinct
from faults and exhausted budgets; stale current-world receipts request
replanning. BUDGET can be a natural number or an exact chunk schedule.

Completed answers are printed; faults and exhaustion have distinct nonzero
statuses. Input reading remains the original reader boundary. The driver
performs native execution without receiving or replaying a submitted proof.
-/

set_option autoImplicit false

open Mettapedia.Languages.MeTTa.PeTTa
open Mettapedia.Languages.MeTTa.PeTTa.Eval
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)

private def readProgram (paths : List String) : IO SpaceSemantics.Program := do
  let mut loaded : SpaceSemantics.Program := { equations := [], declarations := [] }
  for path in paths do
    match SpaceSemantics.readProgram (← IO.FS.readFile path) with
    | .ok program => loaded := loaded.append program
    | .error reason => throw (IO.userError s!"{path}: {reason}")
  return loaded

private def readRequests (path : String) : IO (List Atom) := do
  let mut requests := []
  for line in (← IO.FS.readFile path).splitOn "\n" do
    if line.trimAscii.toString.isEmpty then continue
    match SpaceSemantics.readSource line with
    | .ok [expression] => requests := expression :: requests
    | .ok _ => throw (IO.userError "expected one request per line")
    | .error reason => throw (IO.userError s!"request: {reason}")
  return requests.reverse

private def printAnswer (answer : Atom) : IO Unit :=
  match answer with
  | .grounded (.bool true) => IO.println "true"
  | .grounded (.bool false) => IO.println "false"
  | _ => IO.println answer

private def runStream (program : SpaceSemantics.Program) (fuel : Nat)
    (requests : List Atom) : IO UInt32 := do
  let initial : Configuration := {
    state := Effects.loaded program
    control := .sequence (program.initializers.map (.evaluate [] ·)) []
    input := requests }
  match run program fuel initial with
  | .complete _ answers remaining printed =>
      if !remaining.isEmpty then throw (IO.userError "unconsumed input")
      for answer in printed ++ answers do printAnswer answer
      return 0
  | .fault fault configuration =>
      for line in configuration.output do printAnswer line
      IO.eprintln s!"fault: {repr fault}"
      return 1
  | .exhausted configuration =>
      IO.eprintln s!"exhausted: {repr configuration.control}"
      return 2

private def runRequests (program : SpaceSemantics.Program) (fuel : Nat)
    (requests : List Atom) : IO UInt32 := do
  let mut state := Effects.loaded program
  for request in requests do
    match evaluate program fuel state request with
    | .complete after answers _ printed =>
        for answer in printed ++ answers do printAnswer answer
        state := after
    | .fault fault configuration =>
        for line in configuration.output do printAnswer line
        IO.eprintln s!"fault: {repr fault}"
        return 1
    | .exhausted configuration =>
        IO.eprintln s!"exhausted: {repr configuration.control}"
        return 2
  return 0

private def runLiveRequests (program : SpaceSemantics.Program) (budgets : List Nat)
    (requests : List Atom) : IO UInt32 := do
  let mut retained := ProgramReplay.snapshot []
    { state := Effects.loaded program, control := .returned [] }
  for request in requests do
    let prepared := { retained with control := .evaluate [] request, frames := [], input := [], output := [] }
    let after := ProgramReplay.LiveRegistry.nativeChunks budgets prepared
    match ProgramReplay.LiveRegistry.readout after.decode with
    | .complete _ answers _ printed =>
        for answer in printed ++ answers do printAnswer answer
        retained := after
    | .fault reason configuration =>
        for line in configuration.output do printAnswer line
        IO.eprintln s!"fault: {repr reason}"
        return 1
    | .exhausted configuration =>
        IO.eprintln s!"exhausted: {repr configuration.control}"
        return 2
  return 0

private def runAtomServices (requests : List Atom) : IO UInt32 := do
  for request in requests do
    printAnswer (Mettapedia.Languages.GuardedAtomRule.Services.Article.onAtom request)
  return 0


private def readAuthored (path : String) : IO (Mettapedia.OSLF.MeTTaIL.MeTTaSyntaxQuotation.Program Atom) := do
  match Mettapedia.Languages.MeTTa.MeTTaAuthoredProgramExecution.Text.parse (← IO.FS.readFile path) with
  | .ok program => return program
  | .error reason => throw (IO.userError s!"{path}: {reason}")

private def readProvidedModules (paths : List String) :
    IO Mettapedia.Languages.MeTTa.MeTTaRevisionedQueryBindEval.AuthoredActivation.AtomCommands.ProvidedModules := do
  paths.mapM fun path => do
    return (.grounded (.string path), ← readAuthored path)

private def printAuthoredObservation
    (observation : Mettapedia.Languages.MeTTa.MeTTaAuthoredProgramExecution.ProgramExecution.Observation) : IO Unit := do
  match observation.answer with
  | .values answers => for answer in answers do printAnswer answer
  | .imported _ _ => pure ()
  | .retained command =>
      match command with
      | .directive name arguments => printAnswer (.expression (.symbol name :: arguments))
      | .eval term | .fact term => printAnswer term
      | _ => pure ()

/-- Drive the same retained source controller, printing new source I/O before
new command answers at each actual transition. Budget chunks retain all
cursors and state; they do not replay a completed command or output. -/
private def authoredTicks
    (settings : Mettapedia.Languages.MeTTa.MeTTaAuthoredProgramExecution.ProgramExecution.Settings) :
    Nat → Mettapedia.Languages.MeTTa.MeTTaAuthoredProgramExecution.ProgramExecution.Session → Nat → Nat →
      IO (Mettapedia.Languages.MeTTa.MeTTaAuthoredProgramExecution.ProgramExecution.Session × Nat × Nat)
  | 0, session, printed, observed => return (session, printed, observed)
  | fuel + 1, session, printed, observed => do
      match Mettapedia.Languages.MeTTa.MeTTaAuthoredProgramExecution.ProgramExecution.step settings session with
      | none => return (session, printed, observed)
      | some next =>
          let world := Mettapedia.Languages.MeTTa.MeTTaAuthoredProgramExecution.Text.observedWorld next
          for line in world.packet.output.drop printed do printAnswer line
          for answer in next.observations.drop observed do printAuthoredObservation answer
          authoredTicks settings fuel next world.packet.output.length next.observations.length

private def runAuthoredProgram (policy path : String) (budgets : List Nat)
    (modules : List String) : IO UInt32 := do
  let activation ← match policy with
    | "pinned" => pure Mettapedia.Languages.MeTTa.MeTTaAuthoredProgramExecution.Search.ActivationPolicy.pinnedEntry
    | "current" => pure Mettapedia.Languages.MeTTa.MeTTaAuthoredProgramExecution.Search.ActivationPolicy.currentWorld
    | _ => throw (IO.userError "authored guard policy must be pinned or current")
  let program ← readAuthored path
  let provided ← readProvidedModules modules
  let settings : Mettapedia.Languages.MeTTa.MeTTaAuthoredProgramExecution.ProgramExecution.Settings := {
    evaluator := {
      activation
      registration := Mettapedia.Languages.MeTTa.MeTTaFiniteRevisionedKernel.AuthoredActivation.AtomServices.registration
      dynamic := Mettapedia.Languages.MeTTa.MeTTaFiniteRevisionedKernel.AuthoredActivation.AtomServices.provider}
    modules := provided }
  let world : Mettapedia.Languages.MeTTa.MeTTaFiniteRevisionedKernel.AuthoredActivation.AtomCommands.StateCode := {
    packet := {core := [], spaces := [], cells := [], control := .returned [], frames := [], input := [], output := []}
    fuel := budgets.sum }
  let mut retained := Mettapedia.Languages.MeTTa.MeTTaAuthoredProgramExecution.ProgramExecution.initial world program
  let mut printed := 0
  let mut observed := 0
  for budget in budgets do
    let (next, nextPrinted, nextObserved) ← authoredTicks settings budget retained printed observed
    retained := next
    printed := nextPrinted
    observed := nextObserved
  match Mettapedia.Languages.MeTTa.MeTTaAuthoredProgramExecution.ProgramExecution.status retained with
  | .complete => return 0
  | .fault reason => IO.eprintln s!"fault: {repr reason}"; return 1
  | .exhausted => IO.eprintln "exhausted"; return 2
  | .stale => IO.eprintln "stale: current-world guard receipt requires replanning"; return 4
  | .unknown =>
      match retained.phase with
      | .moduleHeld _ _ module => IO.eprintln s!"unknown import: {module}"
      | .blocked active =>
          match active.command with
          | .eval term => IO.eprintln s!"unknown: {term}"
          | _ => IO.eprintln "unknown"
      | _ => IO.eprintln "unknown"
      return 3

def main (arguments : List String) : IO UInt32 := do
  if let "authored-program" :: policy :: path :: rawBudget :: modules := arguments then
    let some budgets := (rawBudget.splitOn "+").mapM String.toNat?
      | throw (IO.userError "expected natural-number budgets separated by +")
    return ← runAuthoredProgram policy path budgets modules
  if let ["atom-services", path] := arguments then
    return ← runAtomServices (← readRequests path)
  let mode :: requests :: rawFuel :: paths := arguments
    | throw (IO.userError "use MODE REQUESTS FUEL PROGRAM...")
  if paths.isEmpty then throw (IO.userError "no program files")
  if mode = "live-requests" then
    let some budgets := (rawFuel.splitOn "+").mapM String.toNat?
      | throw (IO.userError "expected natural-number budgets separated by +")
    let program ← readProgram paths
    let requests ← readRequests requests
    runLiveRequests program budgets requests
  else
    let some fuel := rawFuel.toNat?
      | throw (IO.userError "expected a natural-number fuel bound")
    let program ← readProgram paths
    let requests ← readRequests requests
    match mode with
    | "stream" => runStream program fuel requests
    | "requests" => runRequests program fuel requests
    | _ => throw (IO.userError "mode must be stream, requests or live-requests")
