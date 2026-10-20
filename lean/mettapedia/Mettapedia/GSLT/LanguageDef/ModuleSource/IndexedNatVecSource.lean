import Mettapedia.GSLT.LanguageDef.ModuleSource.Syntax
import Mettapedia.GSLT.LanguageDef.ModuleSource.IndexedNatVecNames

/-!
# Named Nat/Vec declarations into indexed admission

The selected source profile uses the admitted natural interface and one explicit
payload parameter. Name resolution precedes the existing scoped-index lowering.
All constructor fields and result indices are retained. Reserved operation and
family names cannot be shadowed; ordinary field shadowing is handled by the
existing nearest-binding resolver. Unsupported fields are refused, not erased.

This is a concrete consumer of the general declaration syntax. Other indexed
and mutual signatures need their own interpretation into the generic polynomial
interface. The source profile does not grant guest iota or arithmetic conversion.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleSource.IndexedNatVecSource

open InductiveSyntax IndexedNatVecNames IndexedInductiveNatVec

/-- The source names selected by this interpretation. They are resolved before
lowering; the host's natural constructors are not consulted by the parser. -/
structure Names where
  natural : String := "Nat"
  zero : String := "Zero"
  successor : String := "Succ"
  vector : String := "Vec"
  payload : String := "A"
  deriving DecidableEq, Repr

def Names.reserved (names : Names) : List String :=
  ["Type", names.natural, names.zero, names.successor, names.vector, names.payload]

def Names.distinct (names : Names) : Bool := decide names.reserved.Nodup

/-- A natural index uses only the declared constructors and nearest field
names. Arithmetic definitions are a separate operation-admission package. -/
def index (names : Names) : Term → Option Index
  | .name name => if name = names.zero then some .zero else some (.name name)
  | .app (.name name) argument =>
      if name = names.successor then (index names argument).map .successor else none
  | _ => none

def resultIndex (names : Names) : Term → Option Index
  | .app (.app (.name family) (.name parameter)) indexTerm =>
      if family = names.vector ∧ parameter = names.payload then index names indexTerm else none
  | _ => none

def body (names : Names) (result : Term) : List Binder → Option ConstructorBody
  | [] => (resultIndex names result).map .result
  | field :: rest => do
      if names.reserved.contains field.name then none else do
        let tail ← body names result rest
        match field.type with
        | .name type =>
            if type = names.natural then pure (.data field.name .length tail)
            else if type = names.payload then pure (.data field.name .payload tail)
            else none
        | type =>
            let recursiveIndex ← resultIndex names type
            pure (.recursive field.name recursiveIndex tail)

def constructor (names : Names) (source : InductiveSyntax.Constructor) :
    Option IndexedNatVecNames.Constructor :=
  (body names source.result source.fields).map fun body => ⟨source.name, body⟩

/-- Recognize the source presentation of the natural algebra before using it
as the vector index. Names, result types and the successor domain are checked. -/
def naturalMatches (names : Names) (family : Family) : Bool :=
  family.name == names.natural && family.parameters.isEmpty && family.indices.isEmpty &&
    family.sort == .name "Type" &&
    match family.constructors with
    | [zero, successor] =>
        zero.name == names.zero && zero.fields.isEmpty && zero.result == .name names.natural &&
        successor.name == names.successor && successor.result == .name names.natural &&
        match successor.fields with
        | [field] => field.type == .name names.natural && !names.reserved.contains field.name
        | _ => false
    | _ => false

/-- Translate the natural constructor telescope itself, retaining every direct
recursive field, before invoking the same structural admission as for vectors. -/
def naturalBody (names : Names) (result : Term) : List Binder →
    Option (IndexedInductive.RawCode Natural.interface [])
  | [] => if result = .name names.natural then some (.result ()) else none
  | field :: rest =>
      if field.type = .name names.natural ∧ !names.reserved.contains field.name then
        (naturalBody names result rest).map (.recursive ())
      else none

def admitNatural (names : Names) (family : Family) :
    Option (IndexedInductive.Admitted Natural.interface []) := do
  if !(names.distinct && naturalMatches names family) then none else do
    let constructors ← family.constructors.mapM fun constructor =>
      (naturalBody names constructor.result constructor.fields).map fun body =>
        (⟨constructor.name, body⟩ : IndexedInductive.RawConstructor Natural.interface [])
    IndexedInductive.admitList? constructors

def vectorMatches (names : Names) (family : Family) : Bool :=
  family.name == names.vector && family.parameters == [⟨names.payload, .name "Type"⟩] &&
    family.sort == .name "Type" &&
    match family.indices with
    | [binder] => binder.type == .name names.natural && !names.reserved.contains binder.name
    | _ => false

def lower (names : Names) (natural vector : Family) : Option (List IndexedNatVecNames.Constructor) := do
  if !(names.distinct && naturalMatches names natural && vectorMatches names vector) then none
  else vector.constructors.mapM (constructor names)

noncomputable def admit (A : Type) (names : Names) (natural vector : Family) :
    Option (IndexedInductive.Admitted (Vectors.interface A) []) := do
  let constructors ← lower names natural vector
  IndexedNatVecNames.admit? A constructors

/-- This consumer selects one direct theory with one inductive block. Imports,
joins, other blocks and an entry selecting another theory are not ignored. -/
def select (source : Module) : Option (Family × Family) :=
  match source.imports, source.theories, source.entry with
  | [], [theory], some ([entry], []) =>
      if entry = theory.name ∧ theory.params = [] then
        match theory.body with
        | .extend none [.inductives [natural, vector]] => some (natural, vector)
        | _ => none
      else none
  | _, _, _ => none

noncomputable def admitModule (A : Type) (names : Names) (source : Module) :
    Option (IndexedInductive.Admitted (Vectors.interface A) []) := do
  let (natural, vector) ← select source
  admit A names natural vector

/-- The executable frontend stops at scope and constructor-name checks. Full
guest declaration replay remains the separate typed admission boundary. -/
def check (names : Names) (source : Module) : Bool :=
  match select source with
  | none => false
  | some (natural, vector) =>
      match lower names natural vector with
      | none => false
      | some constructors =>
          decide (constructors.map IndexedNatVecNames.Constructor.name).Nodup &&
            constructors.all (fun constructor => constructor.body.wellScoped .empty)

/-- Every accepted source occurrence has a complete scoped telescope under
the existing lowering. No unbound index can hide behind the executable check. -/
theorem check_scoped (A : Type) (names : Names) (source : Module)
    (accepted : check names source = true) :
    ∃ natural vector constructors,
      select source = some (natural, vector) ∧
      lower names natural vector = some constructors ∧
      (constructors.map IndexedNatVecNames.Constructor.name).Nodup ∧
      ∀ constructor ∈ constructors,
        ∃ raw, constructor.body.lower A .empty = some raw := by
  cases selected : select source with
  | none => simp [check, selected] at accepted
  | some pair =>
      rcases pair with ⟨natural, vector⟩
      cases lowered : lower names natural vector with
      | none => simp [check, selected, lowered] at accepted
      | some constructors =>
          have parts : (constructors.map IndexedNatVecNames.Constructor.name).Nodup ∧
              constructors.all (fun constructor => constructor.body.wellScoped .empty) = true := by
            simpa [check, selected, lowered] using accepted
          refine ⟨natural, vector, constructors, rfl, lowered, parts.1, ?_⟩
          intro constructor member
          have scopeChecked := List.all_eq_true.mp parts.2 constructor member
          rw [ConstructorBody.wellScoped_eq A] at scopeChecked
          exact Option.isSome_iff_exists.mp scopeChecked

/-- Source constructor identities and their order survive resolution. -/
theorem constructor_name (names : Names) (source : InductiveSyntax.Constructor)
    (target : IndexedNatVecNames.Constructor) (resolved : constructor names source = some target) :
    target.name = source.name := by
  cases found : body names source.result source.fields with
  | none => simp [constructor, found] at resolved
  | some body =>
      have same : (⟨source.name, body⟩ : IndexedNatVecNames.Constructor) = target := by
        simpa [constructor, found] using resolved
      cases same
      rfl

theorem constructors_names (names : Names) (source : List InductiveSyntax.Constructor)
    (target : List IndexedNatVecNames.Constructor)
    (resolved : source.mapM (constructor names) = some target) :
    target.map IndexedNatVecNames.Constructor.name = source.map InductiveSyntax.Constructor.name := by
  induction source generalizing target with
  | nil => simp at resolved; subst target; rfl
  | cons first rest ih =>
      cases firstFound : constructor names first with
      | none => simp [List.mapM_cons, firstFound] at resolved
      | some firstTarget =>
          cases restFound : rest.mapM (constructor names) with
          | none => simp [List.mapM_cons, firstFound, restFound] at resolved
          | some restTarget =>
              have same : firstTarget :: restTarget = target := by
                simpa [List.mapM_cons, firstFound, restFound] using resolved
              subst target
              simp only [List.map_cons, constructor_name names first firstTarget firstFound,
                ih restTarget restFound]

theorem lower_names (names : Names) (natural vector : Family)
    (target : List IndexedNatVecNames.Constructor) (resolved : lower names natural vector = some target) :
    target.map IndexedNatVecNames.Constructor.name = vector.constructors.map InductiveSyntax.Constructor.name := by
  by_cases valid : (names.distinct && naturalMatches names natural && vectorMatches names vector) = true
  · exact constructors_names names _ _ (by simpa [lower, valid] using resolved)
  · simp [lower, valid] at resolved

/-- The selected direct-field fragment refuses an arrow rather than admitting
a possibly negative recursive occurrence as an uninterpreted data field. -/
theorem arrow_refused (names : Names) (result domain codomain : Term)
    (field : String) (rest : List Binder) :
    body names result (⟨field, .arrow domain codomain⟩ :: rest) = none := by
  simp only [body]
  split
  · rfl
  · cases body names result rest <;> rfl

end Mettapedia.GSLT.LanguageDef.ModuleSource.IndexedNatVecSource
