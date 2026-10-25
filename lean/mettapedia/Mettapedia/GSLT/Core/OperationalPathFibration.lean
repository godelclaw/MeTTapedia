import Mathlib.CategoryTheory.Grothendieck
import Mettapedia.GSLT.Core.IndexedOperational
import Mettapedia.GSLT.Core.InteractionComposition

/-!
# Operational transport of semantic and occurrence paths

This module extracts the category-valued structure already forced by forward
operational translations.  A GSLT contributes its free category of finite,
proof-relevant execution paths.  A forward translation acts functorially on
that category, and the resulting functor into `Cat` has a standard
Grothendieck total category.

Forward operational translations also push authenticated interaction
presentations forward. Their history maps preserve concatenation and retain
source occurrences. An injective state map earns constructive history
readback; without it, newly composable target histories need not lift.

This is a theorem-level account of the functional indexed structure of
GSLT-IL.  It does not assert that every authored route is functional, nor
that a Grothendieck category alone represents refinement cells or relational
routes.  Those are separate comparison obligations.
-/

namespace Mettapedia.GSLT.IndexedOperational

open CategoryTheory
open Mettapedia.GSLT
open Mettapedia.GSLT.Ultrainfinite

universe uTerm uSourceTerm uTargetTerm

/-! ## Free execution-path categories -/

/-- A distinct category carrier for the terms of one GSLT. -/
def ExecutionObject (system : GSLT.{uTerm}) := system.Term

/-- The original term represented by an execution-category object. -/
def ExecutionObject.term {system : GSLT.{uTerm}} :
    ExecutionObject system -> system.Term :=
  id

/-- Finite proof-relevant executions are the homs of the free path category. -/
abbrev ExecutionPath (system : GSLT.{uTerm})
    (source target : ExecutionObject system) :=
  Route (fun left right : system.Term => PLift (system.Step left right))
    source target

instance executionCategory (system : GSLT.{uTerm}) :
    CategoryTheory.Category (ExecutionObject system) where
  Hom := ExecutionPath system
  id object := .refl object
  comp first second := first.append second
  id_comp morphism := Route.refl_append morphism
  comp_id morphism := Route.append_refl morphism
  assoc first second third := Route.append_assoc first second third

/-! ## Functorial transport of complete executions -/

namespace OperationalTranslation

/-- A forward operational translation maps every retained step of a finite
execution path. -/
def mapRoute {source : GSLT.{uSourceTerm}} {target : GSLT.{uTargetTerm}}
    (translation : OperationalTranslation source target) :
    {first last : source.Term} ->
      Route (fun left right => PLift (source.Step left right)) first last ->
      Route (fun left right => PLift (target.Step left right))
        (translation.mapTerm first) (translation.mapTerm last)
  | _, _, .refl object => .refl (translation.mapTerm object)
  | _, _, .cons step rest =>
      .cons ⟨translation.mapStep step.down⟩ (translation.mapRoute rest)

@[simp] theorem mapRoute_refl
    {source : GSLT.{uSourceTerm}} {target : GSLT.{uTargetTerm}}
    (translation : OperationalTranslation source target)
    (object : source.Term) :
    translation.mapRoute (.refl object) =
      .refl (translation.mapTerm object) :=
  rfl

@[simp] theorem mapRoute_append
    {source : GSLT.{uSourceTerm}} {target : GSLT.{uTargetTerm}}
    (translation : OperationalTranslation source target)
    {first middle last : source.Term}
    (earlier : Route (fun left right => PLift (source.Step left right)) first middle)
    (later : Route (fun left right => PLift (source.Step left right)) middle last) :
    translation.mapRoute (earlier.append later) =
      (translation.mapRoute earlier).append (translation.mapRoute later) := by
  induction earlier with
  | refl => rfl
  | cons step rest inductionHypothesis =>
      simp [Route.append, mapRoute, inductionHypothesis]

@[simp] theorem mapRoute_length
    {source : GSLT.{uSourceTerm}} {target : GSLT.{uTargetTerm}}
    (translation : OperationalTranslation source target)
    {first last : source.Term}
    (route : Route (fun left right => PLift (source.Step left right)) first last) :
    (translation.mapRoute route).length = route.length := by
  induction route with
  | refl => rfl
  | cons step rest inductionHypothesis =>
      simp [mapRoute, Route.length, inductionHypothesis]

@[simp] theorem mapRoute_id
    {system : GSLT.{uTerm}} {first last : system.Term}
    (route : Route (fun left right => PLift (system.Step left right)) first last) :
    (OperationalTranslation.id system).mapRoute route = route := by
  induction route with
  | refl => rfl
  | cons step rest inductionHypothesis =>
      cases step
      simp only [mapRoute]
      congr

@[simp] theorem mapRoute_comp
    {first : GSLT.{uSourceTerm}} {middle : GSLT.{uTerm}}
    {last : GSLT.{uTargetTerm}}
    (earlier : OperationalTranslation first middle)
    (later : OperationalTranslation middle last)
    {source target : first.Term}
    (route : Route (fun left right => PLift (first.Step left right)) source target) :
    (earlier.comp later).mapRoute route =
      later.mapRoute (earlier.mapRoute route) := by
  induction route with
  | refl => rfl
  | cons step rest inductionHypothesis =>
      cases step
      simp only [mapRoute]
      congr

/-- Every forward operational translation induces a functor between free
execution-path categories. -/
def pathFunctor {source : GSLT.{uTerm}} {target : GSLT.{uTerm}}
    (translation : OperationalTranslation source target) :
    CategoryTheory.Functor (ExecutionObject source) (ExecutionObject target) where
  obj := translation.mapTerm
  map := translation.mapRoute
  map_id _ := rfl
  map_comp first second := translation.mapRoute_append first second

@[simp] theorem pathFunctor_obj
    {source target : GSLT.{uTerm}}
    (translation : OperationalTranslation source target)
    (term : ExecutionObject source) :
    (translation.pathFunctor).obj term = translation.mapTerm term :=
  rfl

@[simp] theorem pathFunctor_map
    {source target : GSLT.{uTerm}}
    (translation : OperationalTranslation source target)
    {first last : ExecutionObject source}
    (route : first ⟶ last) :
    (translation.pathFunctor).map route = translation.mapRoute route :=
  rfl

end OperationalTranslation

/-! ## The category-valued index and its total category -/

/-- Functional operational transport is a category-valued indexed system of
proof-relevant execution paths. -/
def executionIndex :
    CategoryTheory.Functor OperationalTheory.{uTerm}
      CategoryTheory.Cat.{uTerm, uTerm} where
  obj system := CategoryTheory.Cat.of (ExecutionObject system.theory)
  map translation := translation.pathFunctor.toCatHom
  map_id system := by
    apply CategoryTheory.Cat.ext
    refine CategoryTheory.Functor.hext (fun _ => rfl) ?_
    intro first last route
    exact heq_of_eq (OperationalTranslation.mapRoute_id route)
  map_comp earlier later := by
    apply CategoryTheory.Cat.ext
    refine CategoryTheory.Functor.hext (fun _ => rfl) ?_
    intro first last route
    exact heq_of_eq (OperationalTranslation.mapRoute_comp earlier later route)

/-- The standard Grothendieck total category of a GSLT together with one of
its states.  A total morphism retains both the selected language translation
and the target-fibre execution following transport. -/
abbrev OperationalExecutionTotal :=
  CategoryTheory.Grothendieck executionIndex

/-- Embed a language/state pair as an object of the operational total
category. -/
def totalObject (system : OperationalTheory.{uTerm})
    (state : ExecutionObject system.theory) :
    OperationalExecutionTotal :=
  ⟨system, state⟩

/-! ## Occurrence-preserving transport of interaction histories -/

namespace EventTransport

open Mettapedia.GSLT.Core.InteractionEvent
open Mettapedia.GSLT.Core.InteractionComposition

universe uSite uEvent

/-! ## Exact pushforward of an interaction presentation -/

/-- One transported event retains the complete source occurrence that
generated it.  Its target endpoints are fixed intrinsically by the constructor,
so an event with invented translated endpoints is unconstructible.  Equal
visible endpoints therefore do not identify distinct source sites or
derivations. -/
inductive TransportedEvent
    {source target : GSLT}
    (translation : OperationalTranslation source target)
    (presentation : InteractionPresentation.{uSite, uEvent} source) :
    presentation.Site → target.Term → target.Term → Type _ where
  | ofSource {site : presentation.Site} {first last : source.Term}
      (evidence : presentation.Event site first last) :
      TransportedEvent translation presentation site
        (translation.mapTerm first) (translation.mapTerm last)

/-- Push an interaction presentation through an operational translation while
retaining source occurrence identity in every target event. -/
def transportedPresentation
    {source target : GSLT}
    (translation : OperationalTranslation source target)
    (presentation : InteractionPresentation.{uSite, uEvent} source) :
    InteractionPresentation target where
  Site := presentation.Site
  Event := TransportedEvent translation presentation
  sound := by
    intro site translatedSource translatedTarget event
    cases event with
    | ofSource evidence =>
        exact translation.mapStep (presentation.sound evidence)

/-- The canonical transported occurrence. -/
def transportEvent
    {source target : GSLT}
    (translation : OperationalTranslation source target)
    {presentation : InteractionPresentation.{uSite, uEvent} source}
    {site : presentation.Site} {first last : source.Term}
    (event : presentation.Event site first last) :
    (transportedPresentation translation presentation).Event site
      (translation.mapTerm first) (translation.mapTerm last) :=
  .ofSource event

/-- Transport every authenticated occurrence in a finite interaction path. -/
def transportEventPath
    {source target : GSLT}
    (translation : OperationalTranslation source target)
    (presentation : InteractionPresentation.{uSite, uEvent} source) :
    {first last : source.Term} → EventPath presentation first last →
      EventPath (transportedPresentation translation presentation)
        (translation.mapTerm first) (translation.mapTerm last)
  := EventPath.map presentation (transportedPresentation translation presentation)
    translation.mapTerm id (transportEvent translation)

@[simp] theorem transportEventPath_length
    {source target : GSLT}
    (translation : OperationalTranslation source target)
    (presentation : InteractionPresentation.{uSite, uEvent} source)
    {first last : source.Term} (path : EventPath presentation first last) :
    EventPath.pathLength (transportedPresentation translation presentation)
        (transportEventPath translation presentation path) =
      EventPath.pathLength presentation path := by
  exact EventPath.map_length presentation _ _ _ _ path

@[simp] theorem transportEventPath_append
    {source target : GSLT}
    (translation : OperationalTranslation source target)
    (presentation : InteractionPresentation.{uSite, uEvent} source)
    {first middle last : source.Term}
    (earlier : EventPath presentation first middle)
    (later : EventPath presentation middle last) :
    transportEventPath translation presentation
        (EventPath.append presentation earlier later) =
      EventPath.append (transportedPresentation translation presentation)
        (transportEventPath translation presentation earlier)
        (transportEventPath translation presentation later) := by
  exact EventPath.map_append presentation _ _ _ _ earlier later

/-- Forward translation of the endpoint-only rewrite-path representation. -/
def mapRewritePath
    {source target : GSLT}
    (translation : OperationalTranslation source target) :
    {first last : source.Term} → source.RewritePath first last →
      target.RewritePath (translation.mapTerm first)
        (translation.mapTerm last)
  := Mettapedia.GSLT.RewritePath.map translation.mapTerm translation.mapStep

/-- Occurrence-preserving transport agrees exactly with ordinary GSLT path
transport after erasing occurrence identity. -/
@[simp] theorem transportEventPath_erase
    {source target : GSLT}
    (translation : OperationalTranslation source target)
    (presentation : InteractionPresentation.{uSite, uEvent} source)
    {first last : source.Term} (path : EventPath presentation first last) :
    EventPath.erase (transportedPresentation translation presentation)
        (transportEventPath translation presentation path) =
      mapRewritePath translation (EventPath.erase presentation path) := by
  exact EventPath.erase_map presentation _ _ _ _ translation.mapStep path

/-- Mapping an erased history commutes with the same chronological cut. -/
@[simp] theorem mapRewritePath_append
    {source target : GSLT}
    (translation : OperationalTranslation source target)
    {first cut last : source.Term}
    (earlier : source.RewritePath first cut) (later : source.RewritePath cut last) :
    mapRewritePath translation (Mettapedia.GSLT.RewritePath.append earlier later) =
      Mettapedia.GSLT.RewritePath.append (mapRewritePath translation earlier)
        (mapRewritePath translation later) :=
  Mettapedia.GSLT.RewritePath.map_append translation.mapTerm translation.mapStep earlier later

/-! ## Event-level identity and composition -/

/-- Reconstruct a source history from a pushed-forward history when the
state map is injective. The endpoint equations identify the requested source
states; every event supplies its original occurrence evidence. -/
def readbackEventPath
    {source target : GSLT}
    (translation : OperationalTranslation source target)
    (presentation : InteractionPresentation.{uSite, uEvent} source)
    (injective : Function.Injective translation.mapTerm) :
    {actualFirst actualLast : target.Term} →
      (path : EventPath (transportedPresentation translation presentation)
        actualFirst actualLast) →
      (first last : source.Term) →
      translation.mapTerm first = actualFirst →
      translation.mapTerm last = actualLast → EventPath presentation first last
  | _, _, .nil _, first, last, firstEq, lastEq => by
      have same := injective (firstEq.trans lastEq.symm)
      cases same
      exact .nil first
  | _, _, .cons (.ofSource event) rest, first, last, firstEq, lastEq => by
      have tail := readbackEventPath translation presentation injective rest _ last rfl lastEq
      exact (injective firstEq).symm ▸ EventPath.cons event tail

/-- Reading back a transported history recovers the complete original
history, including its event evidence. -/
@[simp] theorem readback_transportEventPath
    {source target : GSLT}
    (translation : OperationalTranslation source target)
    (presentation : InteractionPresentation.{uSite, uEvent} source)
    (injective : Function.Injective translation.mapTerm)
    {first last : source.Term} (path : EventPath presentation first last) :
    readbackEventPath translation presentation injective
        (transportEventPath translation presentation path) first last rfl rfl = path := by
  induction path with
  | nil => rfl
  | cons event rest ih => exact congrArg (EventPath.cons event) ih

private theorem transport_readbackEventPath_heq
    {source target : GSLT}
    (translation : OperationalTranslation source target)
    (presentation : InteractionPresentation.{uSite, uEvent} source)
    (injective : Function.Injective translation.mapTerm)
    {actualFirst actualLast : target.Term}
    (path : EventPath (transportedPresentation translation presentation)
      actualFirst actualLast) :
    ∀ (first last : source.Term) (firstEq : translation.mapTerm first = actualFirst)
      (lastEq : translation.mapTerm last = actualLast),
      HEq (transportEventPath translation presentation
        (readbackEventPath translation presentation injective path first last firstEq lastEq))
        path := by
  induction path with
  | nil actual =>
      intro first last firstEq lastEq
      have same := injective (firstEq.trans lastEq.symm)
      subst last
      cases firstEq
      rfl
  | cons event rest ih =>
      cases event with
      | ofSource evidence =>
          intro first last firstEq lastEq
          have same := injective firstEq
          subst first
          cases lastEq
          exact heq_of_eq (congrArg (EventPath.cons (transportEvent translation evidence))
            (eq_of_heq (ih _ _ rfl rfl)))

/-- Readback also recovers every target history between translated endpoints;
it is not merely a choice of some source path with the same endpoints. -/
@[simp] theorem transport_readbackEventPath
    {source target : GSLT}
    (translation : OperationalTranslation source target)
    (presentation : InteractionPresentation.{uSite, uEvent} source)
    (injective : Function.Injective translation.mapTerm)
    {first last : source.Term}
    (path : EventPath (transportedPresentation translation presentation)
      (translation.mapTerm first) (translation.mapTerm last)) :
    transportEventPath translation presentation
        (readbackEventPath translation presentation injective path first last rfl rfl) = path :=
  eq_of_heq (transport_readbackEventPath_heq translation presentation injective path
    first last rfl rfl)

/-- Injective state transport gives a constructive equivalence of complete
occurrence histories over the translated endpoints. -/
def transportedPathEquiv
    {source target : GSLT}
    (translation : OperationalTranslation source target)
    (presentation : InteractionPresentation.{uSite, uEvent} source)
    (injective : Function.Injective translation.mapTerm)
    (first last : source.Term) :
    EventPath presentation first last ≃
      EventPath (transportedPresentation translation presentation)
        (translation.mapTerm first) (translation.mapTerm last) where
  toFun := transportEventPath translation presentation
  invFun := fun path => readbackEventPath translation presentation injective path first last rfl rfl
  left_inv := readback_transportEventPath translation presentation injective
  right_inv := transport_readbackEventPath translation presentation injective

/-- Under an injective state map, existence of a source occurrence history
is equivalent to existence of a pushed-forward history between its images.
Forward simulation alone does not supply the reverse implication. -/
theorem nonempty_transportEventPath_iff
    {source target : GSLT}
    (translation : OperationalTranslation source target)
    (presentation : InteractionPresentation.{uSite, uEvent} source)
    (injective : Function.Injective translation.mapTerm)
    (first last : source.Term) :
    Nonempty (EventPath (transportedPresentation translation presentation)
      (translation.mapTerm first) (translation.mapTerm last)) ↔
      Nonempty (EventPath presentation first last) := by
  constructor
  · rintro ⟨path⟩
    exact ⟨readbackEventPath translation presentation injective path first last rfl rfl⟩
  · rintro ⟨path⟩
    exact ⟨transportEventPath translation presentation path⟩

/-- Transport does not merge source histories when its state map is
injective. This result retains event evidence rather than only theoremhood. -/
theorem transportEventPath_injective
    {source target : GSLT}
    (translation : OperationalTranslation source target)
    (presentation : InteractionPresentation.{uSite, uEvent} source)
    (injective : Function.Injective translation.mapTerm)
    (first last : source.Term) :
    Function.Injective (transportEventPath translation presentation
      (first := first) (last := last)) := by
  intro left right same
  have readback := congrArg
    (fun path => readbackEventPath translation presentation injective path first last rfl rfl)
    same
  simpa only [readback_transportEventPath] using readback

/-- Remove one identity-transport wrapper from an authenticated event. -/
def forgetIdentityEvent
    {theory : GSLT}
    (presentation : InteractionPresentation.{uSite, uEvent} theory)
    {site : presentation.Site} {source target : theory.Term} :
    (transportedPresentation (OperationalTranslation.id theory) presentation).Event
        site source target →
      presentation.Event site source target
  | .ofSource event => event

/-- Add the canonical identity-transport wrapper. -/
def wrapIdentityEvent
    {theory : GSLT}
    (presentation : InteractionPresentation.{uSite, uEvent} theory)
    {site : presentation.Site} {source target : theory.Term} :
    presentation.Event site source target →
      (transportedPresentation (OperationalTranslation.id theory) presentation).Event
        site source target :=
  .ofSource

/-- Identity transport is proof-relevantly equivalent to the original event
family. -/
def transportedEventIdentityEquiv
    {theory : GSLT}
    (presentation : InteractionPresentation.{uSite, uEvent} theory)
    {site : presentation.Site} {source target : theory.Term} :
    (transportedPresentation (OperationalTranslation.id theory) presentation).Event
        site source target ≃
      presentation.Event site source target where
  toFun := forgetIdentityEvent presentation
  invFun := wrapIdentityEvent presentation
  left_inv := by intro event; cases event; rfl
  right_inv := by intro event; rfl

/-- Flatten the two provenance wrappers supplied by successive transport into
the single wrapper supplied by the composite operational translation. -/
def flattenTransportedEvent
    {first middle last : GSLT}
    (earlier : OperationalTranslation first middle)
    (later : OperationalTranslation middle last)
    (presentation : InteractionPresentation.{uSite, uEvent} first)
    {site : presentation.Site} {source target : last.Term} :
    (transportedPresentation later
      (transportedPresentation earlier presentation)).Event
        site source target →
      (transportedPresentation (OperationalTranslation.comp earlier later)
        presentation).Event site source target
  | .ofSource (.ofSource event) => .ofSource event

/-- Expand one composite provenance wrapper into the two wrappers supplied by
successive transport. -/
def expandTransportedEvent
    {first middle last : GSLT}
    (earlier : OperationalTranslation first middle)
    (later : OperationalTranslation middle last)
    (presentation : InteractionPresentation.{uSite, uEvent} first)
    {site : presentation.Site} {source target : last.Term} :
    (transportedPresentation (OperationalTranslation.comp earlier later)
      presentation).Event site source target →
      (transportedPresentation later
        (transportedPresentation earlier presentation)).Event
          site source target
  | .ofSource event => .ofSource (.ofSource event)

/-- Successive and composite event transport retain exactly equivalent source
occurrence evidence. -/
def transportedEventCompEquiv
    {first middle last : GSLT}
    (earlier : OperationalTranslation first middle)
    (later : OperationalTranslation middle last)
    (presentation : InteractionPresentation.{uSite, uEvent} first)
    {site : presentation.Site} {source target : last.Term} :
    (transportedPresentation later
      (transportedPresentation earlier presentation)).Event
        site source target ≃
      (transportedPresentation (OperationalTranslation.comp earlier later)
        presentation).Event site source target where
  toFun := flattenTransportedEvent earlier later presentation
  invFun := expandTransportedEvent earlier later presentation
  left_inv := by
    intro event
    cases event with
    | ofSource inner => cases inner; rfl
  right_inv := by intro event; cases event; rfl

/-! ## Path-level identity and composition -/

/-- Remove identity wrappers from every event of a finite history. -/
def forgetIdentityPath
    {theory : GSLT}
    (presentation : InteractionPresentation.{uSite, uEvent} theory) :
    {source target : theory.Term} →
    EventPath
        (transportedPresentation (OperationalTranslation.id theory) presentation)
        source target →
      EventPath presentation source target
  := EventPath.map
    (transportedPresentation (OperationalTranslation.id theory) presentation)
    presentation id id (forgetIdentityEvent presentation)

/-- Add identity wrappers to every event of a finite history. -/
def wrapIdentityPath
    {theory : GSLT}
    (presentation : InteractionPresentation.{uSite, uEvent} theory) :
    {source target : theory.Term} → EventPath presentation source target →
      EventPath
        (transportedPresentation (OperationalTranslation.id theory) presentation)
        source target
  := EventPath.map presentation
    (transportedPresentation (OperationalTranslation.id theory) presentation)
    id id (wrapIdentityEvent presentation)

/-- Identity transport preserves the complete proof-relevant history. -/
def transportedPathIdentityEquiv
    {theory : GSLT}
    (presentation : InteractionPresentation.{uSite, uEvent} theory)
    {source target : theory.Term} :
    EventPath
        (transportedPresentation (OperationalTranslation.id theory) presentation)
        source target ≃
      EventPath presentation source target where
  toFun := forgetIdentityPath presentation
  invFun := wrapIdentityPath presentation
  left_inv := by
    intro path
    induction path with
    | nil => rfl
    | cons event rest ih =>
        cases event with
        | ofSource original =>
            exact congrArg
              (EventPath.cons (transportEvent (OperationalTranslation.id theory) original)) ih
  right_inv := by
    intro path
    induction path with
    | nil => rfl
    | cons event rest ih => exact congrArg (EventPath.cons event) ih

/-- Flatten successive provenance wrappers throughout a finite target
history. -/
def flattenTransportedPath
    {first middle last : GSLT}
    (earlier : OperationalTranslation first middle)
    (later : OperationalTranslation middle last)
    (presentation : InteractionPresentation.{uSite, uEvent} first) :
    {source target : last.Term} →
    EventPath
        (transportedPresentation later
          (transportedPresentation earlier presentation)) source target →
      EventPath
        (transportedPresentation (OperationalTranslation.comp earlier later)
          presentation) source target
  := EventPath.map
    (transportedPresentation later (transportedPresentation earlier presentation))
    (transportedPresentation (OperationalTranslation.comp earlier later) presentation)
    id id (flattenTransportedEvent earlier later presentation)

/-- Expand the composite provenance wrapper throughout a finite target
history. -/
def expandTransportedPath
    {first middle last : GSLT}
    (earlier : OperationalTranslation first middle)
    (later : OperationalTranslation middle last)
    (presentation : InteractionPresentation.{uSite, uEvent} first) :
    {source target : last.Term} →
    EventPath
        (transportedPresentation (OperationalTranslation.comp earlier later)
          presentation) source target →
      EventPath
        (transportedPresentation later
          (transportedPresentation earlier presentation)) source target
  := EventPath.map
    (transportedPresentation (OperationalTranslation.comp earlier later) presentation)
    (transportedPresentation later (transportedPresentation earlier presentation))
    id id (expandTransportedEvent earlier later presentation)

/-- Successive and composite transport are equivalent on all proof-relevant
target histories, including histories newly composable after a non-injective
translation. -/
def transportedPathCompEquiv
    {first middle last : GSLT}
    (earlier : OperationalTranslation first middle)
    (later : OperationalTranslation middle last)
    (presentation : InteractionPresentation.{uSite, uEvent} first)
    {source target : last.Term} :
    EventPath
        (transportedPresentation later
          (transportedPresentation earlier presentation)) source target ≃
      EventPath
        (transportedPresentation (OperationalTranslation.comp earlier later)
          presentation) source target where
  toFun := flattenTransportedPath earlier later presentation
  invFun := expandTransportedPath earlier later presentation
  left_inv := by
    intro path
    induction path with
    | nil => rfl
    | cons event rest ih =>
        cases event with
        | ofSource inner =>
            cases inner with
            | ofSource original =>
                exact congrArg
                  (EventPath.cons (transportEvent later (transportEvent earlier original))) ih
  right_inv := by
    intro path
    induction path with
    | nil => rfl
    | cons event rest ih =>
        cases event with
        | ofSource original =>
            exact congrArg
              (EventPath.cons (transportEvent (OperationalTranslation.comp earlier later) original)) ih

@[simp] theorem flatten_transport_twice
    {first middle last : GSLT}
    (earlier : OperationalTranslation first middle)
    (later : OperationalTranslation middle last)
    (presentation : InteractionPresentation.{uSite, uEvent} first)
    {source target : first.Term}
    (path : EventPath presentation source target) :
    flattenTransportedPath earlier later presentation
        (transportEventPath later (transportedPresentation earlier presentation)
          (transportEventPath earlier presentation path)) =
      transportEventPath (OperationalTranslation.comp earlier later)
        presentation path := by
  induction path with
  | nil => rfl
  | cons event rest ih =>
      exact congrArg (fun suffix =>
        EventPath.cons (transportEvent (OperationalTranslation.comp earlier later) event)
          suffix) ih

/-- Endpoint erasure sees the same compositional law: mapping a source rewrite
path through the composite is mapping it through the earlier and later routes
in succession. -/
@[simp] theorem mapRewritePath_comp
    {first middle last : GSLT}
    (earlier : OperationalTranslation first middle)
    (later : OperationalTranslation middle last)
    {source target : first.Term}
    (path : first.RewritePath source target) :
    mapRewritePath (OperationalTranslation.comp earlier later) path =
      mapRewritePath later (mapRewritePath earlier path) := by
  exact (Mettapedia.GSLT.RewritePath.map_comp earlier.mapTerm earlier.mapStep
    later.mapTerm later.mapStep path).symm

@[simp] theorem flattenTransportedPath_append
    {first middle last : GSLT}
    (earlier : OperationalTranslation first middle)
    (later : OperationalTranslation middle last)
    (presentation : InteractionPresentation.{uSite, uEvent} first)
    {source middleTerm target : last.Term}
    (firstPath : EventPath
      (transportedPresentation later
        (transportedPresentation earlier presentation)) source middleTerm)
    (suffix : EventPath
      (transportedPresentation later
        (transportedPresentation earlier presentation)) middleTerm target) :
    flattenTransportedPath earlier later presentation
        (EventPath.append _ firstPath suffix) =
      EventPath.append _
        (flattenTransportedPath earlier later presentation firstPath)
        (flattenTransportedPath earlier later presentation suffix) := by
  exact EventPath.map_append _ _ _ _ _ firstPath suffix

end EventTransport

end Mettapedia.GSLT.IndexedOperational
