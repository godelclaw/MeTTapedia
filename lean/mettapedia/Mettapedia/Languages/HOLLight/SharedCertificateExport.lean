import Mettapedia.Languages.HOLLight.ProofExecution
import Lean.Data.Json

/-!
# Shared tables for native certificate export

This is an untrusted serialization boundary for already constructed receipts.
Names, simple types, canonical terms and named request terms have separate
structural tables. Entries refer only to earlier entries in their own table.
Bounded pointer caches accelerate traversal; clearing them preserves the
structural tables and their identifiers. The native receiver checks the
generated proof, its hypotheses and its dependency assertions independently.

Symbol provenance is supplied by the separately replayed declaration history,
as in the existing native format. This projection is not a source identity or
an independent declaration-admission procedure.
-/

set_option autoImplicit false
namespace Mettapedia.Languages.HOLLight.SharedCertificateExport
open Mettapedia.Languages.OpenTheory Lean

abbrev NameKey := List String × String

inductive TypeNode where
  | variable (name : Nat)
  | operator (name : Nat) (arguments : List Nat)
  deriving BEq, Hashable

inductive CanonicalNode where
  | constant (name type : Nat)
  | free (name type : Nat)
  | bound (index : Nat)
  | application (function argument : Nat)
  | abstraction (type body : Nat)
  deriving BEq, Hashable

inductive NamedNode where
  | variable (name type : Nat)
  | constant (name type : Nat)
  | application (function argument : Nat)
  | abstraction (name type body : Nat)
  deriving BEq, Hashable

private def nums (values : List Nat) : Json := toJson values

def TypeNode.json : TypeNode → Json
  | .variable name => .arr #[toJson 0, toJson name]
  | .operator name arguments => .arr #[toJson 1, toJson name, nums arguments]

def CanonicalNode.json : CanonicalNode → Json
  | .constant name type => nums [0, name, type]
  | .free name type => nums [1, name, type]
  | .bound index => nums [2, index]
  | .application function argument => nums [3, function, argument]
  | .abstraction type body => nums [4, type, body]

def NamedNode.json : NamedNode → Json
  | .variable name type => nums [0, name, type]
  | .constant name type => nums [1, name, type]
  | .application function argument => nums [2, function, argument]
  | .abstraction name type body => nums [3, name, type, body]

structure Tables where
  names : Std.HashMap NameKey Nat := {}
  types : Std.HashMap TypeNode Nat := {}
  canonical : Std.HashMap CanonicalNode Nat := {}
  named : Std.HashMap NamedNode Nat := {}
  pendingNames : Array Json := #[]
  pendingTypes : Array Json := #[]
  pendingCanonical : Array Json := #[]
  pendingNamed : Array Json := #[]
  canonicalPointers : Std.HashMap USize Nat := {}
  retainedCanonical : Array DBTerm := #[]
  namedPointers : Std.HashMap USize Nat := {}
  retainedNamed : Array SourceTerm := #[]
  axiomSources : Array (Nat × Sequent) := #[]
  canonicalPointerHits : Nat := 0
  namedPointerHits : Nat := 0
  canonicalStructuralHits : Nat := 0
  namedStructuralHits : Nat := 0

def internName (name : Mettapedia.Languages.OpenTheory.Name) : StateM Tables Nat := do
  let key := (name.namespaceComponents, name.component)
  if let some index := (← get).names[key]? then return index
  let index := (← get).names.size
  modify fun state => { state with
    names := state.names.insert key index
    pendingNames := state.pendingNames.push (.arr #[toJson key.1, toJson key.2]) }
  return index

partial def internType : Ty → StateM Tables Nat
  | .var name => do
      let node := TypeNode.variable (← internName name)
      if let some index := (← get).types[node]? then return index
      let index := (← get).types.size
      modify fun state => { state with
        types := state.types.insert node index
        pendingTypes := state.pendingTypes.push node.json }
      return index
  | .op (.mk name _) arguments => do
      let name ← internName name
      let arguments ← arguments.mapM internType
      let node := TypeNode.operator name arguments
      if let some index := (← get).types[node]? then return index
      let index := (← get).types.size
      modify fun state => { state with
        types := state.types.insert node index
        pendingTypes := state.pendingTypes.push node.json }
      return index

unsafe def internCanonical (term : DBTerm) : StateM Tables Nat := do
  let pointer := ptrAddrUnsafe term
  if let some index := (← get).canonicalPointers[pointer]? then
    modify fun state => { state with canonicalPointerHits := state.canonicalPointerHits + 1 }
    return index
  let node : CanonicalNode ← match term with
    | .const (.mk name _) type => pure (.constant (← internName name) (← internType type))
    | .free sourceVariable => pure (.free (← internName sourceVariable.name) (← internType sourceVariable.ty))
    | .bound index => pure (.bound index)
    | .app function argument => pure (.application (← internCanonical function) (← internCanonical argument))
    | .abs type body => pure (.abstraction (← internType type) (← internCanonical body))
  let index ← match (← get).canonical[node]? with
    | some index => do
        modify fun state => { state with canonicalStructuralHits := state.canonicalStructuralHits + 1 }
        pure index
    | none => do
        let index := (← get).canonical.size
        modify fun state => { state with
          canonical := state.canonical.insert node index
          pendingCanonical := state.pendingCanonical.push node.json }
        pure index
  modify fun state => { state with
    canonicalPointers := state.canonicalPointers.insert pointer index
    retainedCanonical := state.retainedCanonical.push term }
  return index

unsafe def internNamed (term : SourceTerm) : StateM Tables Nat := do
  let pointer := ptrAddrUnsafe term
  if let some index := (← get).namedPointers[pointer]? then
    modify fun state => { state with namedPointerHits := state.namedPointerHits + 1 }
    return index
  let node : NamedNode ← match term with
    | .var name type => pure (.variable (← internName name) (← internType type))
    | .const (.mk name _) type => pure (.constant (← internName name) (← internType type))
    | .app function argument => pure (.application (← internNamed function) (← internNamed argument))
    | .abs name type body => pure (.abstraction (← internName name) (← internType type) (← internNamed body))
  let index ← match (← get).named[node]? with
    | some index => do
        modify fun state => { state with namedStructuralHits := state.namedStructuralHits + 1 }
        pure index
    | none => do
        let index := (← get).named.size
        modify fun state => { state with
          named := state.named.insert node index
          pendingNamed := state.pendingNamed.push node.json }
        pure index
  modify fun state => { state with
    namedPointers := state.namedPointers.insert pointer index
    retainedNamed := state.retainedNamed.push term }
  return index

unsafe def inference : InferenceRequest → StateM Tables (Nat × Json)
  | .refl term => do return (0, nums [← internCanonical term.term])
  | .trans _ _ => pure (1, nums [])
  | .mkComb _ _ => pure (2, nums [])
  | .abs binder _ => do return (3, nums [← internNamed (.var binder.name binder.ty)])
  | .beta term => do return (4, nums [← internNamed term.source])
  | .assume term => do return (5, nums [← internCanonical term.term])
  | .eqMp _ _ => pure (6, nums [])
  | .deductAntisym _ _ => pure (7, nums [])
  | .instType entries _ => do
      let pairs ← entries.mapM fun entry => do
        pure (nums [← internType entry.1, ← internType entry.2])
      return (8, toJson pairs)
  | .inst entries _ => do
      let pairs ← entries.mapM fun entry => do
        pure (nums [← internNamed entry.1.source, ← internNamed entry.2])
      return (9, toJson pairs)

unsafe def receipt (value : ProofExecution.Receipt) : StateM Tables Json := do
  let (operation, arguments) ← match value.witness with
    | .inference request => inference request
    | .axiom sequent => do pure (10, nums [← internCanonical sequent.concl.term])
  let hypotheses ← value.conclusion.sequent.hyp.val.unquot.mapM fun term => internCanonical term.term
  let conclusion ← internCanonical value.conclusion.sequent.concl.term
  let mut dependencies : Array Nat := #[]
  for premise in value.conclusion.axioms.val.unquot do
    let some entry := (← get).axiomSources.find? (fun entry =>
        entry.2.hyp.card == 0 && premise.hyp.card == 0 && entry.2.concl.same premise.concl) |
      panic! "unregistered source axiom dependency"
    dependencies := dependencies.push entry.1
  let origin ← internName ⟨[], value.origin.1⟩
  return Json.mkObj [("r", .arr #[toJson operation, arguments, toJson value.parents,
    nums hypotheses, toJson conclusion, toJson dependencies, toJson origin, toJson value.origin.2])]

def Tables.pending (state : Tables) : Option Json :=
  if state.pendingNames.isEmpty && state.pendingTypes.isEmpty &&
      state.pendingCanonical.isEmpty && state.pendingNamed.isEmpty then none
  else some (Json.mkObj [("tables", .arr #[toJson state.pendingNames, toJson state.pendingTypes,
    toJson state.pendingCanonical, toJson state.pendingNamed])])

def Tables.clearPending (state : Tables) : Tables :=
  { state with pendingNames := #[], pendingTypes := #[], pendingCanonical := #[], pendingNamed := #[] }

def Tables.clearPointers (state : Tables) : Tables :=
  { state with canonicalPointers := {}, retainedCanonical := #[], namedPointers := {}, retainedNamed := #[] }

def Tables.statistics (state : Tables) : Json := Json.mkObj [
  ("names", toJson state.names.size), ("types", toJson state.types.size),
  ("canonical", toJson state.canonical.size), ("named", toJson state.named.size),
  ("canonicalPointerHits", toJson state.canonicalPointerHits),
  ("namedPointerHits", toJson state.namedPointerHits),
  ("canonicalStructuralHits", toJson state.canonicalStructuralHits),
  ("namedStructuralHits", toJson state.namedStructuralHits)]

end Mettapedia.Languages.HOLLight.SharedCertificateExport
