import Mettapedia.GSLT.LanguageDef.IndexedPositiveContainerGuestPlans

/-!
# Result-argument adapters from registered constructor codes

Scanning the admitted code fixes the outer method-argument order. A direct
child contributes its motive witness unchanged; a nested field contributes
one complete bundle and the registered projection to its result view. The
number of outer arguments is distinct from the number of positions inside
a container. Ambient substitution retains the actual indices, output
expressions, fields and projection programmes.

The typing theorem derives the lambda adapter from primitive slot evidence
and the source function's result-view interface. Interpreting arbitrary open
container variables and proving each registered projection remain separate
source-specific obligations.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.IndexedPositiveContainerGuestResultArguments

open Mettapedia.TypeTheory.IndexedPolynomial.Description
open Mettapedia.TypeTheory.IndexedPositiveContainer
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation FormationSensitive FunctionArgumentAdapters
open IndexedInductive.Guest (TermEnv mapEnv)
open IndexedPositiveContainerGuestTypes
open IndexedPositiveContainerGuestPlans

universe u
variable {I : Interface.{u}} {registry : Registry I} {Head : Type}

/-- A registered result view retains the complete source indexing data.
Its projection is programme syntax, not an assumed equality of readouts. -/
structure ResultSyntax (I : Interface.{u}) (registry : Registry I) (Head : Type) where
  viewType : ∀ {context : List I.SortCode} {n : Nat}
    (name : String) (entry : Entry I), registry.lookup name = some entry →
      entry.OutputExpr context → TermEnv I Head n context →
      Tm Head n → Tm Head n → Tm Head n → Tm Head n
  projection : ∀ {context : List I.SortCode} {n : Nat}
    (name : String) (entry : Entry I), registry.lookup name = some entry →
      entry.OutputExpr context → TermEnv I Head n context →
      Tm Head n → Tm Head n → Tm Head n → Tm Head n
  viewType_substitute : ∀ {context n m} name entry registered
    (output : entry.OutputExpr context) (environment : TermEnv I Head n context)
    (element predicate field : Tm Head n) (sigma : Sub Head n m),
    subst sigma (viewType name entry registered output environment element predicate field) =
      viewType name entry registered output (mapEnv (subst sigma) environment)
        (subst sigma element) (subst sigma predicate) (subst sigma field)
  projection_substitute : ∀ {context n m} name entry registered
    (output : entry.OutputExpr context) (environment : TermEnv I Head n context)
    (element predicate field : Tm Head n) (sigma : Sub Head n m),
    subst sigma (projection name entry registered output environment element predicate field) =
      projection name entry registered output (mapEnv (subst sigma) environment)
        (subst sigma element) (subst sigma predicate) (subst sigma field)

def ResultSyntax.viewRegistry (results : ResultSyntax I registry Head)
    (containers : RegistrySyntax I registry Head) : RegistrySyntax I registry Head where
  fieldType := containers.fieldType
  bundleType := results.viewType
  fieldType_substitute := containers.fieldType_substitute
  bundleType_substitute := results.viewType_substitute

def directSlot {n : Nat} (type : Tm Head n) : Slot Head n :=
  ⟨type, type, .lam (.var 0)⟩

def nestedSlot (indexing : Indexing I Head) (containers : RegistrySyntax I registry Head)
    (results : ResultSyntax I registry Head) {context : List I.SortCode} {n : Nat}
    (name : String) (entry : Entry I) (registered : registry.lookup name = some entry)
    (output : entry.OutputExpr context) (index : I.IndexExpr context)
    (types : TypeSyntax I Head n) (environment : TermEnv I Head n context)
    (motive field : Tm Head n) : Slot Head n :=
  let element := indexing.familyAt types.family index environment
  let predicate := indexing.predicateAt motive index environment
  ⟨containers.bundleType name entry registered output environment element predicate field,
    results.viewType name entry registered output environment element predicate field,
    results.projection name entry registered output environment element predicate field⟩

def slots (indexing : Indexing I Head) (containers : RegistrySyntax I registry Head)
    (results : ResultSyntax I registry Head) {parameters : Nat} :
    {context : List I.SortCode} → (code : Code I registry parameters context) →
      {n : Nat} → TypeSyntax I Head n → TermEnv I Head n context → Tm Head n →
      (Fin (fieldCount code) → Tm Head n) → List (Slot Head n)
  | _, .result _, _, _, _, _, _ => []
  | _, .data _ rest, _, types, environment, motive, fields =>
      slots indexing containers results rest types
        (fields ⟨0, by simp [fieldCount]⟩, environment) motive (fun i => fields i.succ)
  | _, .recursive index rest, _, types, environment, motive, fields =>
      directSlot (.app (indexing.predicateAt motive index environment)
        (fields ⟨0, by simp [fieldCount]⟩)) ::
        slots indexing containers results rest types environment motive (fun i => fields i.succ)
  | _, .nested name entry registered output index rest, _, types, environment, motive, fields =>
      nestedSlot indexing containers results name entry registered output index types environment
        motive (fields ⟨0, by simp [fieldCount]⟩) ::
        slots indexing containers results rest types environment motive (fun i => fields i.succ)

theorem slots_length (indexing : Indexing I Head) (containers : RegistrySyntax I registry Head)
    (results : ResultSyntax I registry Head) {parameters : Nat} {context : List I.SortCode}
    (code : Code I registry parameters context) {n : Nat} (types : TypeSyntax I Head n)
    (environment : TermEnv I Head n context) (motive : Tm Head n)
    (fields : Fin (fieldCount code) → Tm Head n) :
    (slots indexing containers results code types environment motive fields).length = hypothesisCount code := by
  induction code with
  | result _ => rfl
  | data _ _ ih => exact ih _ _
  | recursive _ _ ih => simp only [slots, List.length_cons, ih, hypothesisCount]
  | nested _ _ _ _ _ _ ih => simp only [slots, List.length_cons, ih, hypothesisCount]

theorem slots_substitute (indexing : Indexing I Head) (containers : RegistrySyntax I registry Head)
    (results : ResultSyntax I registry Head) {parameters : Nat} {context : List I.SortCode}
    (code : Code I registry parameters context) {n m : Nat} (types : TypeSyntax I Head n)
    (environment : TermEnv I Head n context) (motive : Tm Head n)
    (fields : Fin (fieldCount code) → Tm Head n) (sigma : Sub Head n m) :
    (slots indexing containers results code types environment motive fields).map (Slot.map (subst sigma)) =
      slots indexing containers results code (types.map (subst sigma))
        (mapEnv (subst sigma) environment) (subst sigma motive) (fun i => subst sigma (fields i)) := by
  induction code with
  | result _ => rfl
  | data _ _ ih =>
      simpa only [slots, mapEnv] using
        ih (fields ⟨0, by simp [fieldCount]⟩, environment) (fun i => fields i.succ)
  | recursive _ _ ih =>
      simp only [slots, List.map_cons, ih, directSlot, Slot.map, subst,
        indexing.predicateAt_substitute, liftSub, Fin.cases_zero]
  | nested _ _ _ _ _ _ ih =>
      simp only [slots, List.map_cons, ih, nestedSlot, Slot.map, containers.bundleType_substitute,
        results.viewType_substitute, results.projection_substitute, TypeSyntax.map,
        indexing.familyAt_substitute, indexing.predicateAt_substitute]

def adapter (indexing : Indexing I Head) (containers : RegistrySyntax I registry Head)
    (results : ResultSyntax I registry Head) {parameters : Nat} {context : List I.SortCode}
    (code : Code I registry parameters context) {n : Nat} (types : TypeSyntax I Head n)
    (environment : TermEnv I Head n context) (motive : Tm Head n)
    (fields : Fin (fieldCount code) → Tm Head n) (function : Tm Head n) : Tm Head n :=
  adapt (slots indexing containers results code types environment motive fields) function

theorem adapter_substitute (indexing : Indexing I Head) (containers : RegistrySyntax I registry Head)
    (results : ResultSyntax I registry Head) {parameters : Nat} {context : List I.SortCode}
    (code : Code I registry parameters context) {n m : Nat} (types : TypeSyntax I Head n)
    (environment : TermEnv I Head n context) (motive : Tm Head n)
    (fields : Fin (fieldCount code) → Tm Head n) (function : Tm Head n) (sigma : Sub Head n m) :
    subst sigma (adapter indexing containers results code types environment motive fields function) =
      adapter indexing containers results code (types.map (subst sigma))
        (mapEnv (subst sigma) environment) (subst sigma motive)
        (fun i => subst sigma (fields i)) (subst sigma function) := by
  simp only [adapter, adapt_substitute, slots_substitute]

/-- Primitive input/output formation and projection typing suffice for every
admitted code. No typing premise for the generated adapter is supplied. -/
theorem adapter_typed (indexing : Indexing I Head) (containers : RegistrySyntax I registry Head)
    (results : ResultSyntax I registry Head) {parameters : Nat} {context : List I.SortCode}
    (code : Code I registry parameters context) {n : Nat} (types : TypeSyntax I Head n)
    (environment : TermEnv I Head n context) (motive : Tm Head n)
    (fields : Fin (fieldCount code) → Tm Head n) {R : Rules Head} {ambient : Ctx Head n}
    {level : Head} (isUniverse : R.isUniverse level)
    (closure : ∃ result, R.join level level result ∧ (result = level ∨ R.cumulative result level))
    (primitiveEvidence : SlotsTyped R ambient level
      (slots indexing containers results code types environment motive fields))
    {function result : Tm Head n} (resultFormed : Typing R ambient result (.head level))
    (source : Judgment R ambient function
      (hypotheses ((slots indexing containers results code types environment motive fields).map Slot.output) result)) :
    Judgment R ambient (adapter indexing containers results code types environment motive fields function)
      (hypotheses ((slots indexing containers results code types environment motive fields).map Slot.input) result) :=
  adapt_judgment isUniverse closure _ primitiveEvidence resultFormed source

theorem adapter_apply (indexing : Indexing I Head) (containers : RegistrySyntax I registry Head)
    (results : ResultSyntax I registry Head) {parameters : Nat} {context : List I.SortCode}
    (code : Code I registry parameters context) {n : Nat} (types : TypeSyntax I Head n)
    (environment : TermEnv I Head n context) (motive : Tm Head n)
    (fields : Fin (fieldCount code) → Tm Head n) (function : Tm Head n)
    (arguments : List (Tm Head n)) (arity : arguments.length = hypothesisCount code) :
    TelescopeAbstraction.BetaSteps
      (arguments.foldl Tm.app (adapter indexing containers results code types environment motive fields function))
      ((((slots indexing containers results code types environment motive fields).zip arguments).map
        (fun pair => Tm.app pair.1.projection pair.2)).foldl Tm.app function) :=
  adapt_apply _ arguments function (arity.trans (slots_length indexing containers results code types environment motive fields).symm)

structure ResultSyntax.HeadNatural (source target : ResultSyntax I registry Head)
    (map : Head → Head) : Prop where
  view : ∀ {context : List I.SortCode} {n : Nat} name entry registered
    (output : entry.OutputExpr context) (environment : TermEnv I Head n context)
    (element predicate field : Tm Head n),
    (source.viewType name entry registered output environment element predicate field).mapHead map =
      target.viewType name entry registered output (mapEnv (Tm.mapHead map) environment)
        (element.mapHead map) (predicate.mapHead map) (field.mapHead map)
  projection : ∀ {context : List I.SortCode} {n : Nat} name entry registered
    (output : entry.OutputExpr context) (environment : TermEnv I Head n context)
    (element predicate field : Tm Head n),
    (source.projection name entry registered output environment element predicate field).mapHead map =
      target.projection name entry registered output (mapEnv (Tm.mapHead map) environment)
        (element.mapHead map) (predicate.mapHead map) (field.mapHead map)

theorem slots_mapHead (indexing : Indexing I Head) (map : Head → Head)
    (indexNatural : indexing.HeadNatural map) {source target : RegistrySyntax I registry Head}
    (containerNatural : source.HeadNatural target map) {first second : ResultSyntax I registry Head}
    (resultNatural : first.HeadNatural second map) {parameters : Nat} {context : List I.SortCode}
    (code : Code I registry parameters context) {n : Nat} (types : TypeSyntax I Head n)
    (environment : TermEnv I Head n context) (motive : Tm Head n)
    (fields : Fin (fieldCount code) → Tm Head n) :
    (slots indexing source first code types environment motive fields).map (Slot.map (Tm.mapHead map)) =
      slots indexing target second code (types.map (Tm.mapHead map))
        (mapEnv (Tm.mapHead map) environment) (motive.mapHead map) (fun i => (fields i).mapHead map) := by
  induction code with
  | result _ => rfl
  | data _ _ ih =>
      simpa only [slots, mapEnv] using
        ih (fields ⟨0, by simp [fieldCount]⟩, environment) (fun i => fields i.succ)
  | recursive _ _ ih =>
      simp only [slots, List.map_cons, ih, directSlot, Slot.map, Tm.mapHead,
        indexing.predicateAt_mapHead map indexNatural]
  | nested _ _ _ _ _ _ ih =>
      simp only [slots, List.map_cons, ih, nestedSlot, Slot.map, containerNatural.bundle,
        resultNatural.view, resultNatural.projection, TypeSyntax.map,
        indexing.familyAt_mapHead map indexNatural, indexing.predicateAt_mapHead map indexNatural]

theorem adapter_mapHead (indexing : Indexing I Head) (map : Head → Head)
    (indexNatural : indexing.HeadNatural map) {source target : RegistrySyntax I registry Head}
    (containerNatural : source.HeadNatural target map) {first second : ResultSyntax I registry Head}
    (resultNatural : first.HeadNatural second map) {parameters : Nat} {context : List I.SortCode}
    (code : Code I registry parameters context) {n : Nat} (types : TypeSyntax I Head n)
    (environment : TermEnv I Head n context) (motive : Tm Head n)
    (fields : Fin (fieldCount code) → Tm Head n) (function : Tm Head n) :
    (adapter indexing source first code types environment motive fields function).mapHead map =
      adapter indexing target second code (types.map (Tm.mapHead map))
        (mapEnv (Tm.mapHead map) environment) (motive.mapHead map)
        (fun i => (fields i).mapHead map) (function.mapHead map) := by
  simp only [adapter, adapt_mapHead, slots_mapHead indexing map indexNatural containerNatural resultNatural]

#print axioms slots_substitute
#print axioms adapter_typed
#print axioms adapter_apply
#print axioms adapter_mapHead

end Mettapedia.GSLT.LanguageDef.IndexedPositiveContainerGuestResultArguments
