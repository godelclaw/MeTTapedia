import Mettapedia.Logic.Prolog.ReaderSWIProfile
import Mettapedia.Logic.Prolog.ReaderModuleLink
import Mettapedia.Logic.Prolog.ReaderLoadRuntime
import Mettapedia.Logic.Prolog.ReaderUnitClosure
import Mettapedia.Logic.Prolog.SourceRuntime
import Mettapedia.Logic.Prolog.SourceRuntimeRegression
import Mettapedia.Logic.LP.RuntimeReadback

/-!
Execute real pinned `parser.pl` DCG clauses, the `parse/2` and `repr/2`
wrappers from pinned `metta.pl`, and `eval/2` through pinned `translator.pl`
and `specializer.pl` on the canonical shared runtime. The registration path
executes the real retained `maplist(register_fun, ...)` load goal through SWI's pinned
`library(apply)` clauses and carries its persistent database forward.  Other
retained loader obligations stay explicit; this canary claims only the named
paths.  Compound evaluation remains gated by the standard-term-ordering
operations and `library(pairs)` source used by pinned `lists:list_to_set/2`.
-/

open Mettapedia.Logic
open Mettapedia.Logic.Prolog

def resolver (dcgBasicsSource listsSource errorSource applySource
    pairsSource : String) :
    ReaderUnitClosure.Resolver String Unit := fun request =>
  match ReaderSWIProfile.sourceKey? request.source with
  | some "library(dcg/basics)" =>
      .ok [.source "library(dcg/basics)" dcgBasicsSource]
  | some "library(lists)" => .ok [.source "library(lists)" listsSource]
  | some "library(error)" => .ok [.source "library(error)" errorSource]
  | some "library(apply)" => .ok [.source "library(apply)" applySource]
  | some "library(pairs)" => .ok [.source "library(pairs)" pairsSource]
  | some key => .ok [.external key]
  | none => .error ()

def loadParserClosure
    (parserSource dcgBasicsSource listsSource errorSource pairsSource : String) :
    IO (ReaderUnitClosure.Closure String) := do
  let closure <- match ReaderUnitClosure.loadWith 32
      (ReaderDirective.effectWith ReaderSWIProfile.pinnedPeTTa)
      ReaderOperator.defaults
      (resolver dcgBasicsSource listsSource errorSource "" pairsSource)
      "parser" parserSource with
    | .ok closure => pure closure
    | .error _ => throw <| IO.userError "source-unit closure failed"
  let linked <- match ReaderUnitClosure.linkDisjoint closure with
    | .ok linked => pure linked
    | .error _ => throw <| IO.userError "source-unit predicates collided"
  if linked.program.length != 318 ||
      closure.external.map (·.key) != ["library(debug)"] ||
      linked.declarations.length != 5 || linked.pendingGoals.length != 3 then
    throw <| IO.userError s!"source-unit boundary changed: clauses={linked.program.length}, \
      external={repr (closure.external.map (·.key))}, \
      declarations={linked.declarations.length}, goals={linked.pendingGoals.length}"
  pure closure

private def appendNewUnits
    (left right : List (ReaderUnitClosure.NamedUnit String)) :
    List (ReaderUnitClosure.NamedUnit String) :=
  left ++ right.filter fun candidate =>
    left.all fun existing => existing.key != candidate.key

private def calledSymbols : SourceSignature.Goal →
    List SourceSignature.PredicateIndicator
  | .call atom => [atom.symbol]
  | .conj left right | .disj left right =>
      calledSymbols left ++ calledSymbols right
  | .ifThenElse condition thenBranch elseBranch
  | .softIfThenElse condition thenBranch elseBranch =>
      calledSymbols condition ++ calledSymbols thenBranch ++
        calledSymbols elseBranch
  | .once goal | .transaction goal | .neg goal => calledSymbols goal
  | .findall _ generator _ => calledSymbols generator
  | .catch guarded _ recovery =>
      calledSymbols guarded ++ calledSymbols recovery
  | _ => []

/-- Link the real pinned `metta.pl`, `parser.pl`, and `translator.pl` closures
without pretending that `metta.pl`'s conditional load-time goal has executed.
The closures are read independently, their already-loaded source units are
combined by key, and module qualification is applied to the same canonical
clauses consumed by the shared runtime. -/
def loadPeTTaSlice (parserClosure : ReaderUnitClosure.Closure String)
    (mettaSource translatorSource specializerSource dcgBasicsSource listsSource
      errorSource applySource pairsSource : String) :
    IO (ReaderUnitClosure.FlatLink String) := do
  let mettaClosure ← match ReaderUnitClosure.loadWith 32
      (ReaderDirective.effectWith ReaderSWIProfile.pinnedPeTTa)
      ReaderOperator.defaults
      (resolver dcgBasicsSource listsSource errorSource applySource pairsSource)
      "metta" mettaSource with
    | .ok closure => pure closure
    | .error _ => throw <| IO.userError "metta source-unit closure failed"
  let translatorClosure ← match ReaderUnitClosure.loadWith 4
      (ReaderDirective.effectWith ReaderSWIProfile.pinnedPeTTa)
      ReaderOperator.defaults
      (resolver dcgBasicsSource listsSource errorSource applySource pairsSource)
      "translator" translatorSource with
    | .ok closure => pure closure
    | .error _ => throw <| IO.userError "translator source-unit closure failed"
  let specializerClosure ← match ReaderUnitClosure.loadWith 2
      (ReaderDirective.effectWith ReaderSWIProfile.pinnedPeTTa)
      ReaderOperator.defaults
      (resolver dcgBasicsSource listsSource errorSource applySource pairsSource)
      "specializer" specializerSource with
    | .ok closure => pure closure
    | .error _ => throw <| IO.userError "specializer source-unit closure failed"
  let userUnits := appendNewUnits mettaClosure.units parserClosure.units
  let userUnits := appendNewUnits userUnits translatorClosure.units
  let combined : ReaderUnitClosure.Closure String := {
    units := appendNewUnits userUnits specializerClosure.units
    external := mettaClosure.external ++ parserClosure.external ++
      translatorClosure.external ++ specializerClosure.external
  }
  let linked ← match ReaderModuleLink.link ReaderSWIProfile.sourceKey? combined with
    | .ok linked => pure linked
    | .error _ => throw <| IO.userError "module-aware source link failed"
  let some mettaUnit := mettaClosure.units.find? fun named => named.key = "metta"
    | throw <| IO.userError "metta root unit missing"
  let some translatorUnit := translatorClosure.units.find? fun named =>
      named.key = "translator"
    | throw <| IO.userError "translator root unit missing"
  let some specializerUnit := specializerClosure.units.find? fun named =>
      named.key = "specializer"
    | throw <| IO.userError "specializer root unit missing"
  if mettaUnit.unit.program.length != 159 then
    throw <| IO.userError s!"metta source boundary changed: \
      clauses={mettaUnit.unit.program.length}"
  if translatorUnit.unit.program.length != 52 then
    throw <| IO.userError s!"translator source boundary changed: \
      clauses={translatorUnit.unit.program.length}"
  if specializerUnit.unit.program.length != 13 then
    throw <| IO.userError s!"specializer source boundary changed: \
      clauses={specializerUnit.unit.program.length}"
  let numberSymbol : SourceSignature.PredicateIndicator := {
    name := "dcg_basics:number"
    arity := 3
  }
  if !(linked.program.any fun clause => clause.head.symbol = numberSymbol) then
    throw <| IO.userError "qualified dcg_basics:number/3 definition missing"
  if !(linked.program.any fun clause =>
      clause.head.symbol = { name := "sexpr", arity := 5 } &&
        numberSymbol ∈ calledSymbols clause.body) then
    throw <| IO.userError "parser number//1 call was not module-qualified"
  if linked.program.length != 691 then
    throw <| IO.userError s!"module-aware source boundary changed: \
      clauses={linked.program.length}"
  pure linked

def codesIdentity : SourceSignature.Variable := {
  spelling := "Codes"
  occurrence := 0
}

def query : SourceSignature.Goal :=
  SourceSignature.call "phrase" [
    SourceSignature.compound "swrite_exp" [SourceSignature.nil],
    .var codesIdentity,
    SourceSignature.nil
  ]

def atomListQuery : SourceSignature.Goal :=
  SourceSignature.call "phrase" [
    SourceSignature.compound "swrite_exp" [
      SourceSignature.list [SourceSignature.atom "a"]
    ],
    .var codesIdentity,
    SourceSignature.nil
  ]

def integerQuery : SourceSignature.Goal :=
  SourceSignature.call "phrase" [
    SourceSignature.compound "swrite_exp" [SourceSignature.integer (-42)],
    .var codesIdentity,
    SourceSignature.nil
  ]

def termIdentity : SourceSignature.Variable := {
  spelling := "Term"
  occurrence := 0
}

def environmentIdentity : SourceSignature.Variable := {
  spelling := "Environment"
  occurrence := 0
}

def sreadQuery (input : SourceSignature.Term) : SourceSignature.Goal :=
  SourceSignature.call "sread" [input, .var termIdentity]

def swriteQuery (input : SourceSignature.Term) : SourceSignature.Goal :=
  SourceSignature.call "swrite" [input, .var termIdentity]

def parseQuery (input : SourceSignature.Term) : SourceSignature.Goal :=
  SourceSignature.call "parse" [input, .var termIdentity]

def reprQuery (input : SourceSignature.Term) : SourceSignature.Goal :=
  SourceSignature.call "repr" [input, .var termIdentity]

def evalQuery (input : SourceSignature.Term) : SourceSignature.Goal :=
  SourceSignature.call "eval" [input, .var termIdentity]

/-- Exercise the parser in its forward direction on the smallest nonempty
S-expression.  This reaches pinned `dcg/basics:string_without//2`, including
its finite-list `memberchk/2` test, rather than merely exercising PeTTa's
writer DCGs. -/
def readQuery (codes : List Int) : SourceSignature.Goal :=
  SourceSignature.call "phrase" [
    SourceSignature.compound "sexpr" [
      .var termIdentity,
      SourceSignature.nil,
      .var environmentIdentity
    ],
    SourceSignature.list (codes.map SourceSignature.integer),
    SourceSignature.nil
  ]

def readAtomQuery : SourceSignature.Goal :=
  readQuery [40, 97, 41]

def qualifiedNumberQuery : SourceSignature.Goal :=
  SourceSignature.call "phrase" [
    SourceSignature.compound "dcg_basics:number" [.var termIdentity],
    SourceSignature.list [SourceSignature.integer 49],
    SourceSignature.nil
  ]

def integerListAux : Nat -> LP.Term SourceRuntime.Sigma.scoped ->
    Option (List Int)
  | 0, _ => none
  | _ + 1, .const (.atom "[]") => some []
  | fuel + 1, .app indicator arguments => do
      if indicator.name != "[|]" || indicator.arity != 2 then none else
        let [head, tail] := List.ofFn arguments | none
        let value <- match head with
          | .const (.integer value) => some value
          | _ => none
        let rest <- integerListAux fuel tail
        pure (value :: rest)
  | _ + 1, _ => none

def integerList? (term : LP.Term SourceRuntime.Sigma.scoped) :
    Option (List Int) :=
  integerListAux (term.size + 1) term

def answerCodes? (answer : LP.RuntimeQuery.Answer SourceRuntime.Sigma) :
    Option (List Int) := do
  let (_, address) <- answer.queryVarMap.find? fun entry =>
    decide (entry.1 = LP.ScopedVar.at 0 codesIdentity)
  let term <- match LP.RuntimeReadback.Heap.readTerm answer.memory.heap address with
    | .ok term => some term
    | .error _ => none
  integerList? term

def answerTerm? (answer : LP.RuntimeQuery.Answer SourceRuntime.Sigma) :
    Option (LP.Term SourceRuntime.Sigma.scoped) := do
  let (_, address) <- answer.queryVarMap.find? fun entry =>
    decide (entry.1 = LP.ScopedVar.at 0 termIdentity)
  match LP.RuntimeReadback.Heap.readTerm answer.memory.heap address with
  | .ok term => some term
  | .error _ => none

def renderCodes (values : List Int) : String :=
  "[" ++ String.intercalate "," (values.map toString) ++ "]"

def renderTermAux : Nat -> LP.Term SourceRuntime.Sigma.scoped -> String
  | 0, _ => "..."
  | _ + 1, .var identity =>
      s!"_{identity.scope}_{identity.name.occurrence}"
  | _ + 1, .const (.atom name) => name
  | _ + 1, .const (.integer value) => toString value
  | _ + 1, .const (.floatBits bits) => s!"float({bits})"
  | _ + 1, .const (.string value) => s!"string({value})"
  | _ + 1, .const (.clauseReference reference) => s!"ref({reference})"
  | fuel + 1, .app indicator arguments =>
      let rendered := (List.ofFn arguments).map (renderTermAux fuel)
      indicator.name ++ "(" ++ String.intercalate "," rendered ++ ")"

def renderTerm (term : LP.Term SourceRuntime.Sigma.scoped) : String :=
  renderTermAux (term.size + 1) term

def execute (program : SourceSignature.Program)
    (goal : SourceSignature.Goal) : IO (List Int × Nat × Nat) := do
  let session <- match SourceRuntime.openEmpty program goal with
    | .ok session => pure session
    | .error _ => throw <| IO.userError "runtime failed to open"
  let (codes, resumed) <- match SourceRuntime.pullSession 8192 session with
    | .answer answer resumed =>
        match answerCodes? answer with
        | some codes => pure (codes, resumed)
        | none => throw <| IO.userError "answer readback failed"
    | .open _ => throw <| IO.userError "runtime remained open"
    | .terminal (.completed _) _ =>
        throw <| IO.userError "runtime completed without an answer"
    | .terminal (.runtimeError error _) _ =>
        throw <| IO.userError s!"runtime error: {repr error}"
    | .terminal (.raised packet _) _ =>
        throw <| IO.userError s!"runtime raised: {renderTerm packet.term}"
  match SourceRuntime.pullSession 8192 resumed with
  | .terminal (.completed memory) _ =>
      pure (codes, memory.heap.size, memory.trail.size)
  | .answer _ _ => throw <| IO.userError "runtime produced an extra answer"
  | .open _ => throw <| IO.userError "runtime remained open after answer"
  | .terminal _ _ => throw <| IO.userError "runtime did not complete"

def executeTermSession (session : SourceRuntime.Session) :
    IO (LP.Term SourceRuntime.Sigma.scoped × Nat × Nat) := do
  let (term, resumed) <- match SourceRuntime.pullSession 32768 session with
    | .answer answer resumed =>
        match answerTerm? answer with
        | some term => pure (term, resumed)
        | none => throw <| IO.userError "term answer readback failed"
    | .open _ => throw <| IO.userError "runtime remained open"
    | .terminal (.completed _) _ =>
        throw <| IO.userError "runtime completed without a term answer"
    | .terminal (.runtimeError error _) _ =>
        throw <| IO.userError s!"runtime error: {repr error}"
    | .terminal (.raised packet _) _ =>
        throw <| IO.userError s!"runtime raised: {renderTerm packet.term}"
  match SourceRuntime.pullSession 32768 resumed with
  | .terminal (.completed memory) _ =>
      pure (term, memory.heap.size, memory.trail.size)
  | .answer _ _ => throw <| IO.userError "runtime produced an extra term answer"
  | .open _ => throw <| IO.userError "runtime remained open after term answer"
  | .terminal _ _ => throw <| IO.userError "runtime term query did not complete"

def executeTerm (program : SourceSignature.Program)
    (goal : SourceSignature.Goal) :
    IO (LP.Term SourceRuntime.Sigma.scoped × Nat × Nat) := do
  let session <- match SourceRuntime.openEmpty program goal with
    | .ok session => pure session
    | .error _ => throw <| IO.userError "runtime failed to open"
  executeTermSession session

def executeTermDatabase (database : ReaderLoadRuntime.Database)
    (goal : SourceSignature.Goal) :
    IO (LP.Term SourceRuntime.Sigma.scoped × Nat × Nat) := do
  let session <- match SourceRuntime.openDatabase database goal with
    | .ok session => pure session
    | .error _ => throw <| IO.userError "runtime database query failed to open"
  executeTermSession session

def checkGoal (program : SourceSignature.Program) (label : String)
    (goal : SourceSignature.Goal) (expected : SourceSignature.Term) : IO Unit := do
  let (actual, heapSize, trailSize) ← executeTerm program goal
  let actualShape := SourceRuntimeRegression.runtimeTermShape actual
  let expectedShape :=
    SourceRuntimeRegression.runtimeTermShape (LP.Term.atScope 0 expected)
  if actualShape == expectedShape then
    pure ()
  else
    throw <| IO.userError s!"{label}: expected {repr expectedShape}, \
      got {repr actualShape}"
  if heapSize != 0 || trailSize != 0 then
    throw <| IO.userError s!"{label}: cleanup left {heapSize}/{trailSize}"
  IO.println s!"{label}=exact"

def checkDatabaseGoal (database : ReaderLoadRuntime.Database) (label : String)
    (goal : SourceSignature.Goal) (expected : SourceSignature.Term) : IO Unit := do
  let (actual, heapSize, trailSize) ← executeTermDatabase database goal
  let actualShape := SourceRuntimeRegression.runtimeTermShape actual
  let expectedShape :=
    SourceRuntimeRegression.runtimeTermShape (LP.Term.atScope 0 expected)
  if actualShape != expectedShape then
    throw <| IO.userError s!"{label}: expected {repr expectedShape}, \
      got {repr actualShape}"
  if heapSize != 0 || trailSize != 0 then
    throw <| IO.userError s!"{label}: cleanup left {heapSize}/{trailSize}"
  IO.println s!"{label}=exact"

private def collectTermAnswers : Nat → SourceRuntime.Session →
    List (LP.Term SourceRuntime.Sigma.scoped) →
    IO (List (LP.Term SourceRuntime.Sigma.scoped) × Nat × Nat)
  | 0, _, _ => throw <| IO.userError "answer collection exhausted pull budget"
  | pulls + 1, session, reversed =>
      match SourceRuntime.pullSession 262144 session with
      | .answer answer resumed =>
          match answerTerm? answer with
          | some term => collectTermAnswers pulls resumed (term :: reversed)
          | none => throw <| IO.userError "collected answer readback failed"
      | .open _ => throw <| IO.userError "answer collection remained open"
      | .terminal (.completed memory) _ =>
          pure (reversed.reverse, memory.heap.size, memory.trail.size)
      | .terminal (.runtimeError error _) _ =>
          throw <| IO.userError s!"answer collection runtime error: {repr error}"
      | .terminal (.raised packet _) _ =>
          throw <| IO.userError s!"answer collection raised: {renderTerm packet.term}"

/-- Compare the complete ordered answer stream, including zero answers and
multiplicity, then require canonical query cleanup. -/
def checkDatabaseAnswers (database : ReaderLoadRuntime.Database) (label : String)
    (goal : SourceSignature.Goal) (expected : List SourceSignature.Term) : IO Unit := do
  let session ← match SourceRuntime.openDatabase database goal with
    | .ok session => pure session
    | .error error =>
        throw <| IO.userError s!"{label}: failed to open: {repr error}"
  let (actual, heapSize, trailSize) ← collectTermAnswers 64 session []
  let actualShapes := actual.map SourceRuntimeRegression.runtimeTermShape
  let expectedShapes := expected.map fun term =>
    SourceRuntimeRegression.runtimeTermShape (LP.Term.atScope 0 term)
  if actualShapes != expectedShapes then
    throw <| IO.userError s!"{label}: expected {repr expectedShapes}, \
      got {repr actualShapes}"
  if heapSize != 0 || trailSize != 0 then
    throw <| IO.userError s!"{label}: cleanup left {heapSize}/{trailSize}"
  IO.println s!"{label}=exact"

def requireDatabaseGoal (database : ReaderLoadRuntime.Database) (label : String)
    (goal : SourceSignature.Goal) : IO Unit := do
  let session ← match SourceRuntime.openDatabase database goal with
    | .ok session => pure session
    | .error error =>
        throw <| IO.userError s!"{label}: failed to open: {repr error}"
  match SourceRuntime.pullSession 32768 session with
  | .answer _ _ => IO.println s!"{label}=exact"
  | .open _ => throw <| IO.userError s!"{label}: remained open"
  | .terminal (.completed _) _ =>
      throw <| IO.userError s!"{label}: completed without an answer"
  | .terminal (.runtimeError error _) _ =>
      throw <| IO.userError s!"{label}: runtime error: {repr error}"
  | .terminal (.raised packet _) _ =>
      throw <| IO.userError s!"{label}: raised: {renderTerm packet.term}"

/-- Require a source-order batch of distinct top-level goals to succeed while
threading the complete persistent world between them. -/
def requireWorldGoals (world : ReaderLoadRuntime.World) (label : String)
    (goals : List SourceSignature.Goal) : IO ReaderLoadRuntime.World := do
  match ReaderLoadRuntime.runGoalsWorld 32768 world goals with
  | .succeeded nextWorld =>
      IO.println s!"{label}=exact"
      pure nextWorld
  | .failed _ _ remaining =>
      throw <| IO.userError s!"{label}: goal failed; remaining={remaining.length}"
  | .open _ remaining =>
      throw <| IO.userError s!"{label}: remained open; remaining={remaining.length}"
  | .raised packet _ _ remaining =>
      throw <| IO.userError s!"{label}: raised {renderTerm packet.term}; \
        remaining={remaining.length}"
  | .runtimeError error _ _ remaining =>
      throw <| IO.userError s!"{label}: runtime error {repr error}; \
        remaining={remaining.length}"
  | .openingError error _ remaining =>
      throw <| IO.userError s!"{label}: opening error {repr error}; \
        remaining={remaining.length}"

def checkRead (program : SourceSignature.Program) (label : String)
    (codes : List Int) (expected : SourceSignature.Term) : IO Unit :=
  checkGoal program label (readQuery codes) expected

def checkVariableGoal (program : SourceSignature.Program) (label : String)
    (goal : SourceSignature.Goal) (relation :
      SourceRuntimeRegression.RuntimeTermShape → Bool) : IO Unit := do
  let (actual, heapSize, trailSize) ← executeTerm program goal
  if relation (SourceRuntimeRegression.runtimeTermShape actual) then
    pure ()
  else
    throw <| IO.userError s!"{label}: variable identity mismatch in {renderTerm actual}"
  if heapSize != 0 || trailSize != 0 then
    throw <| IO.userError s!"{label}: cleanup left {heapSize}/{trailSize}"
  IO.println s!"{label}=exact"

def checkVariableRead (program : SourceSignature.Program) (label : String)
    (codes : List Int) (relation :
      SourceRuntimeRegression.RuntimeTermShape → Bool) : IO Unit :=
  checkVariableGoal program label (readQuery codes) relation

def isSingleVariableList : SourceRuntimeRegression.RuntimeTermShape → Bool
  | .compound "[|]" [.variable _ _ _, .atom "[]"] => true
  | _ => false

def reusesVariableInTwoElementList :
    SourceRuntimeRegression.RuntimeTermShape → Bool
  | .compound "[|]" [.variable leftScope leftSpelling leftOccurrence,
      .compound "[|]" [.variable rightScope rightSpelling rightOccurrence,
        .atom "[]"]] =>
      leftScope == rightScope && leftSpelling == rightSpelling &&
        leftOccurrence == rightOccurrence
  | _ => false

def separatesVariablesInTwoElementList :
    SourceRuntimeRegression.RuntimeTermShape → Bool
  | .compound "[|]" [.variable leftScope leftSpelling leftOccurrence,
      .compound "[|]" [.variable rightScope rightSpelling rightOccurrence,
        .atom "[]"]] =>
      !(leftScope == rightScope && leftSpelling == rightSpelling &&
        leftOccurrence == rightOccurrence)
  | _ => false

private def registrationGoal? :
    String × SourceSignature.Goal → Option SourceSignature.Goal
  | ("metta", goal@(.call atom)) =>
      if atom.symbol.name != "apply:maplist" || atom.symbol.arity != 2 then
        none
      else
        match List.ofFn atom.args with
        | [.const (.atom "register_fun"), _] => some goal
        | _ => none
  | _ => none

/-- Execute exactly the pinned registration directive selected from the
retained source obligations.  All other load goals stay retained and outside
this narrow source-execution claim. -/
def executeRegistration (linked : ReaderUnitClosure.FlatLink String) :
    IO ReaderLoadRuntime.World := do
  let goals := linked.pendingGoals.filterMap registrationGoal?
  let [goal] := goals
    | throw <| IO.userError s!"registration source boundary changed: \
        matching_goals={goals.length}"
  let database := LP.RuntimeDatabase.Database.ofProgram linked.program
  match ReaderLoadRuntime.runFirst 262144 database goal with
  | .ok (.succeeded world) => pure world
  | .ok (.failed _ _) =>
      throw <| IO.userError "pinned registration goal failed"
  | .ok (.open _) =>
      throw <| IO.userError "pinned registration goal remained open"
  | .ok (.raised packet _ _) =>
      throw <| IO.userError s!"pinned registration raised: \
        {renderTerm packet.term}"
  | .ok (.runtimeError error _ _) =>
      throw <| IO.userError s!"pinned registration runtime error: {repr error}"
  | .error error =>
      throw <| IO.userError s!"pinned registration failed to open: {repr error}"

def main (arguments : List String) : IO Unit := do
  let [mettaPath, parserPath, translatorPath, specializerPath,
      dcgBasicsPath, listsPath,
      errorPath, applyPath, pairsPath] := arguments
    | throw <| IO.userError
        "usage: pinned_parser_source_runtime \
         <metta.pl> <parser.pl> <translator.pl> \
         <specializer.pl> \
         <dcg/basics.pl> <lists.pl> <error.pl> <apply.pl> <pairs.pl>"
  let parserClosure <- loadParserClosure
    (← IO.FS.readFile parserPath)
    (← IO.FS.readFile dcgBasicsPath)
    (← IO.FS.readFile listsPath)
    (← IO.FS.readFile errorPath)
    (← IO.FS.readFile pairsPath)
  let linked ← loadPeTTaSlice parserClosure (← IO.FS.readFile mettaPath)
    (← IO.FS.readFile translatorPath)
    (← IO.FS.readFile specializerPath)
    (← IO.FS.readFile dcgBasicsPath)
    (← IO.FS.readFile listsPath)
    (← IO.FS.readFile errorPath)
    (← IO.FS.readFile applyPath)
    (← IO.FS.readFile pairsPath)
  let program := linked.program
  let (emptyCodes, emptyHeap, emptyTrail) <- execute program query
  let (atomListCodes, atomListHeap, atomListTrail) <-
    execute program atomListQuery
  let (integerCodes, integerHeap, integerTrail) <-
    execute program integerQuery
  let (readAtom, readAtomHeap, readAtomTrail) <-
    executeTerm program readAtomQuery
  IO.println s!"empty_codes={renderCodes emptyCodes}"
  IO.println s!"empty_cleanup={emptyHeap}/{emptyTrail}"
  IO.println s!"atom_list_codes={renderCodes atomListCodes}"
  IO.println s!"atom_list_cleanup={atomListHeap}/{atomListTrail}"
  IO.println s!"integer_codes={renderCodes integerCodes}"
  IO.println s!"integer_cleanup={integerHeap}/{integerTrail}"
  IO.println s!"read_atom={renderTerm readAtom}"
  IO.println s!"read_cleanup={readAtomHeap}/{readAtomTrail}"
  checkGoal program "qualified_number" qualifiedNumberQuery
    (SourceSignature.integer 1)
  checkRead program "read_list" [40, 97, 32, 98, 41]
    (SourceSignature.list [SourceSignature.atom "a", SourceSignature.atom "b"])
  checkRead program "read_integer" [40, 49, 41]
    (SourceSignature.list [SourceSignature.integer 1])
  checkRead program "read_negative" [40, 45, 50, 41]
    (SourceSignature.list [SourceSignature.integer (-2)])
  checkRead program "read_float" [40, 49, 46, 53, 41]
    (SourceSignature.list [SourceSignature.floatBits
      (Float.ofScientific 15 true 1).toBits])
  checkRead program "read_exponent" [40, 49, 101, 50, 41]
    (SourceSignature.list [SourceSignature.floatBits
      (Float.ofScientific 1 false 2).toBits])
  checkRead program "read_string" [40, 34, 97, 34, 41]
    (SourceSignature.list [SourceSignature.string "a"])
  checkRead program "read_nested" [40, 40, 97, 41, 41]
    (SourceSignature.list [SourceSignature.list [SourceSignature.atom "a"]])
  checkRead program "read_hyphen_atom" [40, 97, 45, 98, 41]
    (SourceSignature.list [SourceSignature.atom "a-b"])
  checkRead program "read_numeric_looking_atom" [40, 49, 95, 50, 95, 51, 41]
    (SourceSignature.list [SourceSignature.atom "1_2_3"])
  checkRead program "read_hash_atom" [40, 35, 102, 111, 111, 41]
    (SourceSignature.list [SourceSignature.atom "#foo"])
  checkRead program "read_escaped_string" [40, 34, 97, 92, 110, 98, 34, 41]
    (SourceSignature.list [SourceSignature.string "a\nb"])
  checkVariableRead program "read_variable" [40, 36, 120, 41]
    isSingleVariableList
  checkVariableRead program "read_variable_reuse"
    [40, 36, 120, 32, 36, 120, 41]
    reusesVariableInTwoElementList
  checkVariableRead program "read_anonymous_separation"
    [40, 36, 95, 32, 36, 95, 41]
    separatesVariablesInTwoElementList
  checkGoal program "sread_string"
    (sreadQuery (SourceSignature.string "(a b)"))
    (SourceSignature.list [SourceSignature.atom "a", SourceSignature.atom "b"])
  checkGoal program "sread_atom"
    (sreadQuery (SourceSignature.atom "(1)"))
    (SourceSignature.list [SourceSignature.integer 1])
  checkVariableGoal program "sread_variable_reuse"
    (sreadQuery (SourceSignature.string "($x $x)"))
    reusesVariableInTwoElementList
  checkGoal program "swrite_list"
    (swriteQuery (SourceSignature.list
      [SourceSignature.atom "a", SourceSignature.atom "b"]))
    (SourceSignature.string "(a b)")
  checkGoal program "swrite_compound"
    (swriteQuery (SourceSignature.compound "pair"
      [SourceSignature.atom "a", SourceSignature.atom "b"]))
    (SourceSignature.string "(pair a b)")
  checkGoal program "metta_parse"
    (parseQuery (SourceSignature.string "(a b)"))
    (SourceSignature.list [SourceSignature.atom "a", SourceSignature.atom "b"])
  checkGoal program "metta_repr"
    (reprQuery (SourceSignature.compound "pair"
      [SourceSignature.atom "a", SourceSignature.atom "b"]))
    (SourceSignature.string "(pair a b)")
  checkGoal program "metta_eval_atomic"
    (evalQuery (SourceSignature.atom "a"))
    (SourceSignature.atom "a")
  let registeredWorld ← executeRegistration linked
  let registeredDatabase := registeredWorld.database
  requireDatabaseGoal registeredDatabase "metta_fun_id_registered"
    (SourceSignature.call "fun" [SourceSignature.atom "id"])
  checkDatabaseGoal registeredDatabase "metta_id_direct"
    (SourceSignature.call "id"
    [SourceSignature.atom "a", .var termIdentity])
    (SourceSignature.atom "a")
  checkDatabaseGoal registeredDatabase "metta_copy_term_direct"
    (SourceSignature.call "copy_term" [
      SourceSignature.list [SourceSignature.atom "a", SourceSignature.atom "b"],
      .var termIdentity
    ])
    (SourceSignature.list [SourceSignature.atom "a", SourceSignature.atom "b"])
  checkDatabaseGoal registeredDatabase "metta_term_variables_direct"
    (SourceSignature.call "term_variables" [
      SourceSignature.compound "pair" [
        SourceRuntimeRegression.x, SourceRuntimeRegression.y],
      .var termIdentity
    ])
    (SourceSignature.list [
      SourceRuntimeRegression.x, SourceRuntimeRegression.y])
  checkDatabaseGoal registeredDatabase "metta_functor_decompose_direct"
    (SourceSignature.call "functor" [
      SourceSignature.compound "pair" [
        SourceSignature.atom "a", SourceSignature.atom "b"],
      .var termIdentity,
      SourceSignature.integer 2
    ])
    (SourceSignature.atom "pair")
  checkDatabaseGoal registeredDatabase "metta_functor_construct_direct"
    (.conj
      (SourceSignature.call "functor" [
        .var termIdentity,
        SourceSignature.atom "pair",
        SourceSignature.integer 2
      ])
      (.unify (.var termIdentity)
        (SourceSignature.compound "pair" [
          SourceSignature.atom "a", SourceSignature.atom "b"])))
    (SourceSignature.compound "pair" [
      SourceSignature.atom "a", SourceSignature.atom "b"])
  let _ ← requireWorldGoals registeredWorld "metta_nb_global_direct" [
    .conj
      (SourceSignature.call "nb_setval" [
        SourceSignature.atom "metta_runtime_global",
        SourceSignature.compound "f" [SourceRuntimeRegression.x]
      ])
      (.unify SourceRuntimeRegression.x (SourceSignature.atom "source")),
    .conj
      (SourceSignature.call "nb_getval" [
        SourceSignature.atom "metta_runtime_global",
        .var termIdentity
      ])
      (.unify (.var termIdentity)
        (SourceSignature.compound "f" [SourceSignature.atom "stored"]))
  ]
  checkDatabaseGoal registeredDatabase "metta_eval_compound"
    (evalQuery (SourceSignature.list
      [SourceSignature.atom "id", SourceSignature.atom "a"]))
    (SourceSignature.atom "a")
  checkDatabaseGoal registeredDatabase "metta_eval_nested_arithmetic"
    (evalQuery (SourceSignature.list [
      SourceSignature.atom "id",
      SourceSignature.list [SourceSignature.atom "+",
        SourceSignature.integer 1, SourceSignature.integer 2]
    ]))
    (SourceSignature.integer 3)
  checkDatabaseGoal registeredDatabase "metta_eval_imported_reverse"
    (evalQuery (SourceSignature.list [
      SourceSignature.atom "reverse",
      SourceSignature.list [SourceSignature.atom "a", SourceSignature.atom "b"]
    ]))
    (SourceSignature.list [SourceSignature.atom "b", SourceSignature.atom "a"])
  checkDatabaseGoal registeredDatabase "metta_eval_if"
    (evalQuery (SourceSignature.list [
      SourceSignature.atom "if",
      SourceSignature.list [SourceSignature.atom ">",
        SourceSignature.integer 2, SourceSignature.integer 1],
      SourceSignature.atom "then", SourceSignature.atom "else"
    ]))
    (SourceSignature.atom "then")
  checkDatabaseGoal registeredDatabase "metta_eval_map_atom"
    (evalQuery (SourceSignature.list [
      SourceSignature.atom "map-atom",
      SourceSignature.list [SourceSignature.atom "a", SourceSignature.atom "b"],
      SourceSignature.atom "id"
    ]))
    (SourceSignature.list [SourceSignature.atom "a", SourceSignature.atom "b"])
  checkDatabaseGoal registeredDatabase "metta_eval_foldl_atom"
    (evalQuery (SourceSignature.list [
      SourceSignature.atom "foldl-atom",
      SourceSignature.list [SourceSignature.integer 1, SourceSignature.integer 2],
      SourceSignature.integer 0, SourceSignature.atom "+"
    ]))
    (SourceSignature.integer 3)
  checkDatabaseGoal registeredDatabase "metta_eval_first_pair"
    (evalQuery (SourceSignature.list [
      SourceSignature.atom "first-from-pair",
      SourceSignature.list [SourceSignature.atom "a", SourceSignature.atom "b"]
    ]))
    (SourceSignature.atom "a")
  checkDatabaseGoal registeredDatabase "metta_eval_size"
    (evalQuery (SourceSignature.list [
      SourceSignature.atom "size-atom",
      SourceSignature.list [SourceSignature.atom "a", SourceSignature.atom "b"]
    ]))
    (SourceSignature.integer 2)
  checkDatabaseGoal registeredDatabase "metta_eval_unique"
    (evalQuery (SourceSignature.list [
      SourceSignature.atom "unique-atom",
      SourceSignature.list [SourceSignature.atom "b", SourceSignature.atom "a",
        SourceSignature.atom "b"]
    ]))
    (SourceSignature.list [SourceSignature.atom "b", SourceSignature.atom "a"])
  checkDatabaseAnswers registeredDatabase "metta_eval_superpose_order"
    (evalQuery (SourceSignature.list [
      SourceSignature.atom "superpose",
      SourceSignature.list [SourceSignature.atom "a", SourceSignature.atom "b"]
    ]))
    [SourceSignature.atom "a", SourceSignature.atom "b"]
  checkDatabaseAnswers registeredDatabase "metta_eval_collapse"
    (evalQuery (SourceSignature.list [
      SourceSignature.atom "collapse",
      SourceSignature.list [SourceSignature.atom "superpose",
        SourceSignature.list [SourceSignature.atom "a", SourceSignature.atom "b"]]
    ]))
    [SourceSignature.list [SourceSignature.atom "a", SourceSignature.atom "b"]]
  checkDatabaseAnswers registeredDatabase "metta_eval_once"
    (evalQuery (SourceSignature.list [
      SourceSignature.atom "once",
      SourceSignature.list [SourceSignature.atom "superpose",
        SourceSignature.list [SourceSignature.atom "a", SourceSignature.atom "b"]]
    ]))
    [SourceSignature.atom "a"]
  checkDatabaseAnswers registeredDatabase "metta_eval_if_false"
    (evalQuery (SourceSignature.list [
      SourceSignature.atom "if",
      SourceSignature.list [SourceSignature.atom ">",
        SourceSignature.integer 1, SourceSignature.integer 2],
      SourceSignature.atom "then", SourceSignature.atom "else"
    ]))
    [SourceSignature.atom "else"]
  checkDatabaseAnswers registeredDatabase "metta_eval_empty"
    (evalQuery (SourceSignature.list [SourceSignature.atom "empty"])) []
  checkDatabaseAnswers registeredDatabase "metta_eval_transaction"
    (evalQuery (SourceSignature.list [
      SourceSignature.atom "transaction",
      SourceSignature.list [SourceSignature.atom "id", SourceSignature.atom "a"]
    ]))
    [SourceSignature.atom "a"]
  checkDatabaseAnswers registeredDatabase "metta_eval_copy_term"
    (evalQuery (SourceSignature.list [
      SourceSignature.atom "copy_term",
      SourceSignature.list [SourceSignature.atom "a", SourceSignature.atom "b"]
    ]))
    [SourceSignature.list [SourceSignature.atom "a", SourceSignature.atom "b"]]
