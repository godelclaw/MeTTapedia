import Mettapedia.Logic.Prolog.ReaderSWIProfile
import Mettapedia.Logic.Prolog.ReaderModuleLink
import Mettapedia.Logic.Prolog.ReaderUnitClosure
import Mettapedia.Logic.Prolog.SourceRuntime
import Mettapedia.Logic.Prolog.SourceRuntimeRegression
import Mettapedia.Logic.LP.RuntimeReadback

/-!
Execute real pinned `parser.pl` DCG clauses and the `parse/2` and `repr/2`
wrappers from pinned `metta.pl` through the canonical shared runtime.  The
loaded source slice retains unresolved loader obligations; this canary claims
only the explicitly exercised writer and reader paths.
-/

open Mettapedia.Logic
open Mettapedia.Logic.Prolog

def resolver (dcgBasicsSource listsSource errorSource : String) :
    ReaderUnitClosure.Resolver String Unit := fun request =>
  match ReaderSWIProfile.sourceKey? request.source with
  | some "library(dcg/basics)" =>
      .ok [.source "library(dcg/basics)" dcgBasicsSource]
  | some "library(lists)" => .ok [.source "library(lists)" listsSource]
  | some "library(error)" => .ok [.source "library(error)" errorSource]
  | some key => .ok [.external key]
  | none => .error ()

def loadParserClosure
    (parserSource dcgBasicsSource listsSource errorSource : String) :
    IO (ReaderUnitClosure.Closure String) := do
  let closure <- match ReaderUnitClosure.loadWith 32
      (ReaderDirective.effectWith ReaderSWIProfile.pinnedPeTTa)
      ReaderOperator.defaults
      (resolver dcgBasicsSource listsSource errorSource) "parser" parserSource with
    | .ok closure => pure closure
    | .error _ => throw <| IO.userError "source-unit closure failed"
  let linked <- match ReaderUnitClosure.linkDisjoint closure with
    | .ok linked => pure linked
    | .error _ => throw <| IO.userError "source-unit predicates collided"
  if linked.program.length != 297 ||
      closure.external.map (·.key) != ["library(pairs)", "library(debug)"] ||
      linked.declarations.length != 4 || linked.pendingGoals.length != 3 then
    throw <| IO.userError "source-unit boundary changed"
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
  | .once goal | .neg goal => calledSymbols goal
  | .findall _ generator _ => calledSymbols generator
  | .catch guarded _ recovery =>
      calledSymbols guarded ++ calledSymbols recovery
  | _ => []

/-- Link the real pinned `metta.pl` and `parser.pl` closures without pretending
that `metta.pl`'s conditional load-time goal has executed.  Both closures are
read independently, their already-loaded source units are combined by key,
and module qualification is applied to the same canonical clauses consumed by
the shared runtime. -/
def loadMettaSlice (parserClosure : ReaderUnitClosure.Closure String)
    (mettaSource dcgBasicsSource listsSource errorSource : String) :
    IO SourceSignature.Program := do
  let mettaClosure ← match ReaderUnitClosure.loadWith 32
      (ReaderDirective.effectWith ReaderSWIProfile.pinnedPeTTa)
      ReaderOperator.defaults
      (resolver dcgBasicsSource listsSource errorSource) "metta" mettaSource with
    | .ok closure => pure closure
    | .error _ => throw <| IO.userError "metta source-unit closure failed"
  let combined : ReaderUnitClosure.Closure String := {
    units := appendNewUnits mettaClosure.units parserClosure.units
    external := mettaClosure.external ++ parserClosure.external
  }
  let linked ← match ReaderModuleLink.link ReaderSWIProfile.sourceKey? combined with
    | .ok linked => pure linked
    | .error _ => throw <| IO.userError "module-aware source link failed"
  let some mettaUnit := mettaClosure.units.find? fun named => named.key = "metta"
    | throw <| IO.userError "metta root unit missing"
  if mettaUnit.unit.program.length != 159 then
    throw <| IO.userError s!"metta source boundary changed: \
      clauses={mettaUnit.unit.program.length}"
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
  if linked.program.length != 456 then
    throw <| IO.userError s!"module-aware source boundary changed: \
      clauses={linked.program.length}"
  pure linked.program

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

def executeTerm (program : SourceSignature.Program)
    (goal : SourceSignature.Goal) :
    IO (LP.Term SourceRuntime.Sigma.scoped × Nat × Nat) := do
  let session <- match SourceRuntime.openEmpty program goal with
    | .ok session => pure session
    | .error _ => throw <| IO.userError "runtime failed to open"
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

def main (arguments : List String) : IO Unit := do
  let [mettaPath, parserPath, dcgBasicsPath, listsPath, errorPath] := arguments
    | throw <| IO.userError
        "usage: pinned_parser_source_runtime \
         <metta.pl> <parser.pl> <dcg/basics.pl> <lists.pl> <error.pl>"
  let parserClosure <- loadParserClosure
    (← IO.FS.readFile parserPath)
    (← IO.FS.readFile dcgBasicsPath)
    (← IO.FS.readFile listsPath)
    (← IO.FS.readFile errorPath)
  let program ← loadMettaSlice parserClosure (← IO.FS.readFile mettaPath)
    (← IO.FS.readFile dcgBasicsPath)
    (← IO.FS.readFile listsPath)
    (← IO.FS.readFile errorPath)
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
