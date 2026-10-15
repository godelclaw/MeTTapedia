import Mathlib.CategoryTheory.Iso
import Mathlib.Data.Nat.Init

/-!
# Reflexive valence as propagated separation and formation

This module gives a process-level formalization of a relational account of
pain and joy.  A separation or formation is initially only proto-valenced.
Pain or joy requires a nonempty propagation path into a reflexive
representation which itself separates or forms.  Suffering and happiness
instead require a self-sustaining propagation carrier, not merely several
consecutive observations.  The reflexive and self-sustaining conditions are
independent: neither is defined as an intensity or an amplification of the
other.

The cascade predicate here isolates the self-sustaining branch of the
account.  Finite cascades, environmental maintenance and actual temporal
activity require additional models.  The independence results concern this
carrier definition; they do not deny that familiar pain can be understood as
contained suffering in a broader account of finite propagation.

The definitions are deliberately structural.  They do not identify valence
with a scalar, model accuracy, duration, or any particular physical
substrate.  Morphisms preserve propagation, reflexive representation, and
both relational polarities; consequently they preserve pain, joy, suffering,
and happiness.  This makes the ontology transportable without making it
observer-independent or claiming that these necessary structural conditions
are a complete theory of experience.

The positive and negative examples distinguish:

* proto-pain from reflexively propagated pain;
* a finite run of separating events from an auto-propagating cascade;
* reflexive pain from a self-sustaining separation cascade, and their
  formation-polar counterparts;
* coexistence of the two polarities from a forced positive/negative choice.

Reference: "On the Ontology of Joy and Pain, Happiness and Suffering",
Garden of Minds.
-/

set_option autoImplicit false

namespace Mettapedia.Cybernetics.ReflexiveValence

open CategoryTheory

universe u

/-- A relational process substrate on which valence can be interpreted.
`propagates` records causal or representational transmission.  The two
polarities are not assumed to be exhaustive or disjoint. -/
structure System where
  Event : Type u
  propagates : Event -> Event -> Prop
  separates : Event -> Prop
  forms : Event -> Prop
  reflexiveRepresentation : Event -> Prop

/-- A nonempty, proof-relevant propagation path. -/
inductive PropagationPath (system : System.{u}) :
    system.Event -> system.Event -> Type u where
  | edge {source target : system.Event} :
      system.propagates source target -> PropagationPath system source target
  | trans {source middle target : system.Event} :
      PropagationPath system source middle ->
      PropagationPath system middle target ->
      PropagationPath system source target

namespace PropagationPath

variable {system : System.{u}} {source target : system.Event}

/-- Every nonempty path contains a genuine propagation edge. -/
theorem containsEdge (path : PropagationPath system source target) :
    exists first second, system.propagates first second := by
  induction path with
  | edge propagation => exact ⟨_, _, propagation⟩
  | trans _ _ firstPath _ => exact firstPath

end PropagationPath

/-- Proto-pain is the local polarity of a separation event. -/
def ProtoPain (system : System.{u}) (event : system.Event) : Prop :=
  system.separates event

/-- Proto-joy is the local polarity of a formation event. -/
def ProtoJoy (system : System.{u}) (event : system.Event) : Prop :=
  system.forms event

/-- Pain at `target` requires an originating separation, a nonempty
propagation path into a reflexive representation, and a new separation at
that representational level. -/
def PainAt (system : System.{u}) (target : system.Event) : Prop :=
  exists origin,
    ProtoPain system origin /\
    Nonempty (PropagationPath system origin target) /\
    system.reflexiveRepresentation target /\
    system.separates target

/-- Joy is the formation-polar dual of `PainAt`. -/
def JoyAt (system : System.{u}) (target : system.Event) : Prop :=
  exists origin,
    ProtoJoy system origin /\
    Nonempty (PropagationPath system origin target) /\
    system.reflexiveRepresentation target /\
    system.forms target

/-- A self-sustaining propagation carrier for a selected signal predicate.
Every event in the nonempty carrier bears the signal and has a successor in
the same carrier.  No arbitrary duration threshold is involved. -/
structure Cascade (system : System.{u})
    (signal : system.Event -> Prop) : Type u where
  carrier : Set system.Event
  inhabited : carrier.Nonempty
  advances : forall event, event ∈ carrier ->
    exists next, next ∈ carrier /\
      Nonempty (PropagationPath system event next)
  carries : forall event, event ∈ carrier -> signal event

/-- The self-sustaining structural suffering condition.  This names a
continuing separation carrier in the available propagation relation, rather
than classifying every finite episode or certifying its actual activity. -/
def Suffering (system : System.{u}) : Prop :=
  Nonempty (Cascade system system.separates)

/-- The corresponding self-sustaining structural happiness condition. -/
def Happiness (system : System.{u}) : Prop :=
  Nonempty (Cascade system system.forms)

/-! ## Independent structural conditions and interruption -/

/-- Reflexive pain entails a local separation at the representation. -/
theorem pain_requires_separation {system : System.{u}} {event : system.Event}
    (pain : PainAt system event) : system.separates event := by
  rcases pain with ⟨_, _, _, _, separation⟩
  exact separation

/-- Reflexive joy entails a local formation at the representation. -/
theorem joy_requires_formation {system : System.{u}} {event : system.Event}
    (joy : JoyAt system event) : system.forms event := by
  rcases joy with ⟨_, _, _, _, formation⟩
  exact formation

/-- A reflexive representation is necessary for pain, independently of
whether the propagation system supports a cascade. -/
theorem pain_requires_reflexivity {system : System.{u}} {event : system.Event}
    (pain : PainAt system event) : system.reflexiveRepresentation event := by
  rcases pain with ⟨_, _, _, reflexive, _⟩
  exact reflexive

/-- A reflexive representation is necessary for joy. -/
theorem joy_requires_reflexivity {system : System.{u}} {event : system.Event}
    (joy : JoyAt system event) : system.reflexiveRepresentation event := by
  rcases joy with ⟨_, _, _, reflexive, _⟩
  exact reflexive

/-- Local exclusivity follows only when the model supplies disjoint
separation and formation predicates. -/
theorem not_pain_and_joy_of_disjoint {system : System.{u}}
    (disjoint : forall event, system.separates event -> ¬ system.forms event)
    (event : system.Event) : ¬ (PainAt system event /\ JoyAt system event) := by
  rintro ⟨pain, joy⟩
  exact disjoint event (pain_requires_separation pain)
    (joy_requires_formation joy)

namespace PropagationPath

/-- An edgewise strictly decreasing natural rank decreases along every
nonempty propagation path, including paths with neutral intermediate events. -/
theorem rank_decreases {system : System.{u}} (rank : system.Event -> Nat)
    (decreases : forall {first second}, system.propagates first second ->
      rank second < rank first) {first second : system.Event}
    (path : PropagationPath system first second) : rank second < rank first := by
  induction path with
  | edge propagation => exact decreases propagation
  | trans _ _ firstDecrease secondDecrease =>
      exact Nat.lt_trans secondDecrease firstDecrease

end PropagationPath

namespace Cascade

/-- Every cascade has at least one event bearing its selected signal. -/
theorem exists_signal {system : System.{u}} {signal : system.Event -> Prop}
    (cascade : Cascade system signal) : exists event, signal event := by
  rcases cascade.inhabited with ⟨event, member⟩
  exact ⟨event, cascade.carries event member⟩

/-- Enlarging the signal predicate preserves the same propagation carrier.
This does not identify the old and new signals or equate their experiences. -/
def widenSignal {system : System.{u}} {first second : system.Event -> Prop}
    (cascade : Cascade system first)
    (includes : forall event, first event -> second event) :
    Cascade system second where
  carrier := cascade.carrier
  inhabited := cascade.inhabited
  advances := cascade.advances
  carries := fun event member => includes event (cascade.carries event member)

/-- A signal-bearing event with a nonempty returning path supports a
singleton cascade.  The path is retained rather than replaced by a duration. -/
def ofCycle {system : System.{u}} {signal : system.Event -> Prop}
    (event : system.Event) (bearsSignal : signal event)
    (cycle : PropagationPath system event event) : Cascade system signal where
  carrier := {event}
  inhabited := ⟨event, rfl⟩
  advances := by
    intro current member
    have equal : current = event := member
    subst current
    exact ⟨event, rfl, ⟨cycle⟩⟩
  carries := by
    intro current member
    have equal : current = event := member
    subst current
    exact bearsSignal

/-- A strictly decreasing natural rank rules out a self-sustaining carrier.
The interruption obligation is a law of the propagation relation, not an
arbitrary upper bound on how long a painful episode may last. -/
theorem impossible_of_decreasing_rank {system : System.{u}}
    {signal : system.Event -> Prop} (cascade : Cascade system signal)
    (rank : system.Event -> Nat)
    (decreases : forall {first second}, system.propagates first second ->
      rank second < rank first) : False := by
  have terminates : forall n event, rank event = n ->
      event ∈ cascade.carrier -> False := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n inductionHypothesis =>
        intro event rankEqual member
        rcases cascade.advances event member with ⟨next, nextMember, ⟨path⟩⟩
        have lower : rank next < n := by
          rw [← rankEqual]
          exact path.rank_decreases rank decreases
        exact inductionHypothesis (rank next) lower next rfl nextMember
  rcases cascade.inhabited with ⟨event, member⟩
  exact terminates (rank event) event rfl member

end Cascade

theorem suffering_has_separation {system : System.{u}}
    (suffering : Suffering system) : exists event, system.separates event := by
  rcases suffering with ⟨cascade⟩
  exact cascade.exists_signal

theorem happiness_has_formation {system : System.{u}}
    (happiness : Happiness system) : exists event, system.forms event := by
  rcases happiness with ⟨cascade⟩
  exact cascade.exists_signal

/-- A returning separation path suffices for the structural suffering
predicate without requiring a reflexive representation. -/
theorem suffering_of_cycle {system : System.{u}} {event : system.Event}
    (separates : system.separates event)
    (cycle : PropagationPath system event event) : Suffering system :=
  ⟨Cascade.ofCycle event separates cycle⟩

theorem happiness_of_cycle {system : System.{u}} {event : system.Event}
    (forms : system.forms event)
    (cycle : PropagationPath system event event) : Happiness system :=
  ⟨Cascade.ofCycle event forms cycle⟩

/-- Strict decrease interrupts both polarities' cascade conditions.  It
does not suppress finite reflexive pain or joy. -/
theorem no_cascades_of_decreasing_rank {system : System.{u}}
    (rank : system.Event -> Nat)
    (decreases : forall {first second}, system.propagates first second ->
      rank second < rank first) : ¬ Suffering system /\ ¬ Happiness system := by
  constructor
  · rintro ⟨cascade⟩
    exact cascade.impossible_of_decreasing_rank rank decreases
  · rintro ⟨cascade⟩
    exact cascade.impossible_of_decreasing_rank rank decreases

/-! ## Structure-preserving maps -/

/-- A map of valence systems preserves the process relation, both polarities,
and the reflexive-representation boundary. -/
structure Hom (source target : System.{u}) where
  toFun : source.Event -> target.Event
  map_propagates : forall {first second}, source.propagates first second ->
    target.propagates (toFun first) (toFun second)
  map_separates : forall {event}, source.separates event ->
    target.separates (toFun event)
  map_forms : forall {event}, source.forms event ->
    target.forms (toFun event)
  map_reflexiveRepresentation : forall {event},
    source.reflexiveRepresentation event ->
    target.reflexiveRepresentation (toFun event)

@[ext]
theorem Hom.ext {source target : System.{u}} {left right : Hom source target}
    (equal : left.toFun = right.toFun) : left = right := by
  cases left
  cases right
  cases equal
  rfl

/-- Valence systems and structure-preserving maps form a category. -/
instance : Category.{u} (System.{u}) where
  Hom := Hom
  id system := {
    toFun := id
    map_propagates := fun propagation => propagation
    map_separates := fun separation => separation
    map_forms := fun formation => formation
    map_reflexiveRepresentation := fun reflexive => reflexive }
  comp first second := {
    toFun := second.toFun ∘ first.toFun
    map_propagates := fun propagation =>
      second.map_propagates (first.map_propagates propagation)
    map_separates := fun separation =>
      second.map_separates (first.map_separates separation)
    map_forms := fun formation =>
      second.map_forms (first.map_forms formation)
    map_reflexiveRepresentation := fun reflexive =>
      second.map_reflexiveRepresentation
        (first.map_reflexiveRepresentation reflexive) }
  id_comp := by intros; ext; rfl
  comp_id := by intros; ext; rfl
  assoc := by intros; ext; rfl

namespace PropagationPath

variable {source target : System.{u}} {first second : source.Event}

/-- Structure-preserving maps transport complete propagation histories. -/
def map (morphism : source ⟶ target) :
    {first second : source.Event} -> PropagationPath source first second ->
      PropagationPath target (morphism.toFun first) (morphism.toFun second)
  | _, _, .edge propagation =>
      .edge (morphism.map_propagates propagation)
  | _, _, .trans firstPath secondPath =>
      .trans (map morphism firstPath) (map morphism secondPath)

end PropagationPath

/-- Structure-preserving interpretations preserve pain in the forward
direction.  Reflection requires additional structure. -/
theorem pain_map {source target : System.{u}} (morphism : source ⟶ target)
    {event : source.Event} (pain : PainAt source event) :
    PainAt target (morphism.toFun event) := by
  rcases pain with ⟨origin, originSeparates, ⟨path⟩,
    reflexive, targetSeparates⟩
  exact ⟨morphism.toFun origin,
    morphism.map_separates originSeparates,
    ⟨path.map morphism⟩,
    morphism.map_reflexiveRepresentation reflexive,
    morphism.map_separates targetSeparates⟩

/-- Structure-preserving interpretations preserve joy in the forward
direction. -/
theorem joy_map {source target : System.{u}} (morphism : source ⟶ target)
    {event : source.Event} (joy : JoyAt source event) :
    JoyAt target (morphism.toFun event) := by
  rcases joy with ⟨origin, originForms, ⟨path⟩,
    reflexive, targetForms⟩
  exact ⟨morphism.toFun origin,
    morphism.map_forms originForms,
    ⟨path.map morphism⟩,
    morphism.map_reflexiveRepresentation reflexive,
    morphism.map_forms targetForms⟩

namespace Cascade

variable {source target : System.{u}} {signal : source.Event -> Prop}
  {targetSignal : target.Event -> Prop}

/-- A signal-preserving map transports a self-sustaining cascade. -/
def map (morphism : source ⟶ target) (cascade : Cascade source signal)
    (mapsSignal : forall {event}, signal event ->
      targetSignal (morphism.toFun event)) : Cascade target targetSignal where
  carrier := Set.image morphism.toFun cascade.carrier
  inhabited := by
    rcases cascade.inhabited with ⟨event, member⟩
    exact ⟨morphism.toFun event, ⟨event, member, rfl⟩⟩
  advances := by
    rintro _ ⟨event, member, rfl⟩
    rcases cascade.advances event member with
      ⟨next, nextMember, ⟨path⟩⟩
    exact ⟨morphism.toFun next, ⟨next, nextMember, rfl⟩,
      ⟨path.map morphism⟩⟩
  carries := by
    rintro _ ⟨event, member, rfl⟩
    exact mapsSignal (cascade.carries event member)

end Cascade

/-- Suffering cascades survive structure-preserving interpretation. -/
theorem suffering_map {source target : System.{u}} (morphism : source ⟶ target)
    (suffering : Suffering source) : Suffering target := by
  rcases suffering with ⟨cascade⟩
  exact ⟨cascade.map morphism (fun separation =>
    morphism.map_separates separation)⟩

/-- Happiness cascades survive structure-preserving interpretation. -/
theorem happiness_map {source target : System.{u}} (morphism : source ⟶ target)
    (happiness : Happiness source) : Happiness target := by
  rcases happiness with ⟨cascade⟩
  exact ⟨cascade.map morphism (fun formation =>
    morphism.map_forms formation)⟩

/-- A map preserving every propagation and polarity cannot implement a
cascade-interrupting intervention.  Repair must state which structure it
changes, rather than require the full transport contract unchanged. -/
theorem no_map_to_decreasing_rank {source target : System.{u}}
    (cascade : Suffering source ∨ Happiness source)
    (rank : target.Event -> Nat)
    (decreases : forall {first second}, target.propagates first second ->
      rank second < rank first) : ¬ Nonempty (source ⟶ target) := by
  rintro ⟨morphism⟩
  have interrupted := no_cascades_of_decreasing_rank rank decreases
  cases cascade with
  | inl suffering => exact interrupted.1 (suffering_map morphism suffering)
  | inr happiness => exact interrupted.2 (happiness_map morphism happiness)

/-! ## Exact transport and four-coordinate logical observations -/

/-- An isomorphism in the existing category recovers event identity after
transport in both directions. -/
theorem event_roundTrip {source target : System.{u}} (isomorphism : source ≅ target)
    (event : source.Event) :
    isomorphism.inv.toFun (isomorphism.hom.toFun event) = event := by
  exact congrArg (fun morphism : source ⟶ source => morphism.toFun event)
    isomorphism.hom_inv_id

/-- Pain is reflected as well as preserved by invertible structural maps. -/
theorem pain_iso_iff {source target : System.{u}} (isomorphism : source ≅ target)
    (event : source.Event) :
    PainAt target (isomorphism.hom.toFun event) ↔ PainAt source event := by
  constructor
  · intro pain
    have returned := pain_map isomorphism.inv pain
    rw [event_roundTrip isomorphism event] at returned
    exact returned
  · exact pain_map isomorphism.hom

theorem joy_iso_iff {source target : System.{u}} (isomorphism : source ≅ target)
    (event : source.Event) :
    JoyAt target (isomorphism.hom.toFun event) ↔ JoyAt source event := by
  constructor
  · intro joy
    have returned := joy_map isomorphism.inv joy
    rw [event_roundTrip isomorphism event] at returned
    exact returned
  · exact joy_map isomorphism.hom

theorem suffering_iso_iff {source target : System.{u}}
    (isomorphism : source ≅ target) : Suffering target ↔ Suffering source :=
  ⟨suffering_map isomorphism.inv, suffering_map isomorphism.hom⟩

theorem happiness_iso_iff {source target : System.{u}}
    (isomorphism : source ≅ target) : Happiness target ↔ Happiness source :=
  ⟨happiness_map isomorphism.inv, happiness_map isomorphism.hom⟩

/-- Four independent logical observations of a whole process substrate.
The fields record existence of reflexive events or sustaining carriers;
they are neither numerical intensities nor a certificate of felt experience.
They do not identify pain with suffering, or joy with happiness. -/
structure Profile where
  pain : Prop
  suffering : Prop
  joy : Prop
  happiness : Prop

namespace Profile

@[ext]
theorem ext {source target : Profile}
    (pain : source.pain = target.pain)
    (suffering : source.suffering = target.suffering)
    (joy : source.joy = target.joy)
    (happiness : source.happiness = target.happiness) : source = target := by
  cases source
  cases target
  cases pain
  cases suffering
  cases joy
  cases happiness
  rfl

/-- The four structural predicates remain separately observable. -/
def ofSystem (system : System.{u}) : Profile where
  pain := exists event, PainAt system event
  suffering := Suffering system
  joy := exists event, JoyAt system event
  happiness := Happiness system

/-- An explicit projection retaining reflexive-event existence alone. -/
def reflexive (profile : Profile) : Prop × Prop := (profile.pain, profile.joy)

/-- An explicit projection retaining sustaining-carrier existence alone. -/
def sustained (profile : Profile) : Prop × Prop :=
  (profile.suffering, profile.happiness)

/-- Positive-query preservation retains all four implication obligations.
It need not reflect absence or forbid new target events and cycles. -/
def Preserves (source target : Profile) : Prop :=
  (source.pain -> target.pain) /\
  (source.suffering -> target.suffering) /\
  (source.joy -> target.joy) /\
  (source.happiness -> target.happiness)

theorem preserves_refl (profile : Profile) : Preserves profile profile :=
  ⟨id, id, id, id⟩

theorem preserves_trans {first second third : Profile}
    (left : Preserves first second) (right : Preserves second third) :
    Preserves first third :=
  ⟨fun pain => right.1 (left.1 pain),
   fun suffering => right.2.1 (left.2.1 suffering),
   fun joy => right.2.2.1 (left.2.2.1 joy),
   fun happiness => right.2.2.2 (left.2.2.2 happiness)⟩

/-- Every valence-system morphism preserves all four positive observations. -/
theorem ofSystem_map {source target : System.{u}} (morphism : source ⟶ target) :
    Preserves (ofSystem source) (ofSystem target) := by
  refine ⟨?_, suffering_map morphism, ?_, happiness_map morphism⟩
  · rintro ⟨event, pain⟩
    exact ⟨morphism.toFun event, pain_map morphism pain⟩
  · rintro ⟨event, joy⟩
    exact ⟨morphism.toFun event, joy_map morphism joy⟩

/-- Invertible structural transport gives exact agreement of every logical
coordinate, not a scalar agreement after cancellation. -/
theorem ofSystem_iso_eq {source target : System.{u}}
    (isomorphism : source ≅ target) : ofSystem source = ofSystem target := by
  have forward := ofSystem_map isomorphism.hom
  have backward := ofSystem_map isomorphism.inv
  have painEqual := propext ⟨forward.1, backward.1⟩
  have sufferingEqual := propext ⟨forward.2.1, backward.2.1⟩
  have joyEqual := propext ⟨forward.2.2.1, backward.2.2.1⟩
  have happinessEqual := propext ⟨forward.2.2.2, backward.2.2.2⟩
  exact ext painEqual sufferingEqual joyEqual happinessEqual

end Profile

/-! ## Discriminating examples -/

namespace Canary

inductive PainEvent where
  | origin
  | signal
  | representation
  deriving DecidableEq

inductive painPropagation : PainEvent -> PainEvent -> Prop where
  | origin_signal : painPropagation .origin .signal
  | signal_representation : painPropagation .signal .representation

/-- A separation propagates through a signal into a reflexive separation. -/
def painSystem : System where
  Event := PainEvent
  propagates := painPropagation
  separates
    | .origin => True
    | .signal => False
    | .representation => True
  forms := fun _ => False
  reflexiveRepresentation
    | .representation => True
    | _ => False

/-- The source-faithful positive witness: reflexive propagation creates pain. -/
theorem pain_at_representation :
    PainAt painSystem .representation := by
  refine ⟨.origin, trivial, ⟨?path⟩, trivial, trivial⟩
  exact PropagationPath.trans
    (.edge painPropagation.origin_signal)
    (.edge painPropagation.signal_representation)

/-- An isolated separation is proto-pain but cannot be pain because nothing
propagates into its reflexive model. -/
def isolatedSeparation : System where
  Event := Unit
  propagates := fun _ _ => False
  separates := fun _ => True
  forms := fun _ => False
  reflexiveRepresentation := fun _ => True

theorem isolated_protoPain_but_not_pain :
    ProtoPain isolatedSeparation () /\
      ¬ PainAt isolatedSeparation () := by
  refine ⟨trivial, ?_⟩
  rintro ⟨_, _, ⟨path⟩, _, _⟩
  rcases path.containsEdge with ⟨first, second, propagation⟩
  exact propagation

/-- A one-event separating loop is a genuine auto-propagating suffering
cascade. -/
def separatingLoop : System where
  Event := Unit
  propagates := fun _ _ => True
  separates := fun _ => True
  forms := fun _ => False
  reflexiveRepresentation := fun _ => True

theorem separatingLoop_suffers : Suffering separatingLoop := by
  refine ⟨{
    carrier := fun _ => True
    inhabited := ⟨(show separatingLoop.Event from ()), trivial⟩
    advances := ?_
    carries := ?_ }⟩
  · intro event _
    exact ⟨event, trivial, ⟨.edge trivial⟩⟩
  · intro _ _
    trivial

/-- The formation-polar loop is happy and is not a suffering cascade. -/
def formingLoop : System where
  Event := Unit
  propagates := fun _ _ => True
  separates := fun _ => False
  forms := fun _ => True
  reflexiveRepresentation := fun _ => True

theorem formingLoop_happy_not_suffering :
    Happiness formingLoop /\ ¬ Suffering formingLoop := by
  constructor
  · refine ⟨{
      carrier := fun _ => True
      inhabited := ⟨(show formingLoop.Event from ()), trivial⟩
      advances := ?_
      carries := ?_ }⟩
    · intro event _
      exact ⟨event, trivial, ⟨.edge trivial⟩⟩
    · intro _ _
      trivial
  · rintro ⟨cascade⟩
    rcases cascade.inhabited with ⟨event, member⟩
    exact cascade.carries event member

/-- A finite separating process with a terminal event.  It can look like a
sustained run under a bounded observer, but it is not auto-propagating. -/
def terminalSeparation : System where
  Event := Bool
  propagates := fun source target => source = false /\ target = true
  separates := fun _ => True
  forms := fun _ => False
  reflexiveRepresentation := fun _ => True

theorem terminalSeparation_all_events_separate :
    forall event, terminalSeparation.separates event := by
  intro _
  trivial

theorem terminalSeparation_path_endpoints :
    {source target : Bool} ->
      PropagationPath terminalSeparation source target ->
        source = false /\ target = true
  | _, _, .edge propagation => propagation
  | _, _, .trans firstPath secondPath => by
      have firstEndpoints :=
        terminalSeparation_path_endpoints firstPath
      have secondEndpoints :=
        terminalSeparation_path_endpoints secondPath
      have impossible : true = false :=
        firstEndpoints.2.symm.trans secondEndpoints.1
      exact Bool.noConfusion impossible

theorem terminalSeparation_no_path_from_true {target : Bool}
    (path : PropagationPath terminalSeparation true target) : False := by
  exact Bool.noConfusion (terminalSeparation_path_endpoints path).1

theorem terminalSeparation_path_from_false_ends_true {target : Bool}
    (path : PropagationPath terminalSeparation false target) :
    target = true := by
  exact (terminalSeparation_path_endpoints path).2

theorem terminalSeparation_not_suffering :
    ¬ Suffering terminalSeparation := by
  rintro ⟨cascade⟩
  rcases cascade.inhabited with ⟨start, startMember⟩
  cases start with
  | false =>
      rcases cascade.advances false startMember with
        ⟨next, nextMember, ⟨path⟩⟩
      have nextIsTrue : next = true :=
        terminalSeparation_path_from_false_ends_true path
      subst next
      rcases cascade.advances true nextMember with
        ⟨after, _, ⟨terminalPath⟩⟩
      exact terminalSeparation_no_path_from_true terminalPath
  | true =>
      rcases cascade.advances true startMember with
        ⟨after, _, ⟨terminalPath⟩⟩
      exact terminalSeparation_no_path_from_true terminalPath

/-- A terminal process can contain reflexive pain without suffering under
the self-sustaining carrier condition used in this module. -/
theorem terminalSeparation_pain_without_suffering :
    PainAt terminalSeparation true /\ ¬ Suffering terminalSeparation := by
  refine ⟨?_, terminalSeparation_not_suffering⟩
  exact ⟨false, trivial, ⟨.edge ⟨rfl, rfl⟩⟩, trivial, trivial⟩

theorem separatingLoop_has_pain :
    (Profile.ofSystem separatingLoop).pain :=
  ⟨(), (), trivial, ⟨.edge trivial⟩, trivial, trivial⟩

theorem separatingLoop_not_happy : ¬ Happiness separatingLoop := by
  intro happiness
  rcases happiness_has_formation happiness with ⟨_, formation⟩
  exact formation

theorem separatingLoop_has_no_joy : ¬ (Profile.ofSystem separatingLoop).joy := by
  rintro ⟨_, joy⟩
  exact joy_requires_formation joy

/-- Removing the reflexive boundary does not remove the separation cycle.
This finite structural example represents neither an AGI nor an assertion
that its events possess experience. -/
def nonreflexiveSeparatingLoop : System where
  Event := Unit
  propagates := fun _ _ => True
  separates := fun _ => True
  forms := fun _ => False
  reflexiveRepresentation := fun _ => False

theorem nonreflexiveSeparatingLoop_suffers_without_pain :
    Suffering nonreflexiveSeparatingLoop /\
      ¬ (Profile.ofSystem nonreflexiveSeparatingLoop).pain := by
  constructor
  · exact suffering_of_cycle (event := ()) trivial (.edge trivial)
  · rintro ⟨_, pain⟩
    exact pain_requires_reflexivity pain

theorem nonreflexiveSeparatingLoop_not_happy :
    ¬ Happiness nonreflexiveSeparatingLoop := by
  intro happiness
  rcases happiness_has_formation happiness with ⟨_, formation⟩
  exact formation

/-- The formative finite episode uses the same terminal relation, but a
different polarity. -/
def terminalFormation : System where
  Event := Bool
  propagates := fun source target => source = false /\ target = true
  separates := fun _ => False
  forms := fun _ => True
  reflexiveRepresentation := fun _ => True

/-- Joy need not be accompanied by a sustaining formative carrier. -/
theorem terminalFormation_joy_without_happiness :
    JoyAt terminalFormation true /\ ¬ Happiness terminalFormation := by
  constructor
  · exact ⟨false, trivial, ⟨.edge ⟨rfl, rfl⟩⟩, trivial, trivial⟩
  · apply (no_cascades_of_decreasing_rank
      (system := terminalFormation)
      (fun event => match event with | false => 1 | true => 0) ?_).2
    intro first second propagation
    rcases propagation with ⟨rfl, rfl⟩
    exact Nat.zero_lt_succ 0

def nonreflexiveFormingLoop : System where
  Event := Unit
  propagates := fun _ _ => True
  separates := fun _ => False
  forms := fun _ => True
  reflexiveRepresentation := fun _ => False

/-- Happiness need not be accompanied by reflexive joy. -/
theorem nonreflexiveFormingLoop_happy_without_joy :
    Happiness nonreflexiveFormingLoop /\
      ¬ (Profile.ofSystem nonreflexiveFormingLoop).joy := by
  constructor
  · exact happiness_of_cycle (event := ()) trivial (.edge trivial)
  · rintro ⟨_, joy⟩
    exact joy_requires_reflexivity joy

/-- Two disjoint sustaining components retain opposite polarities.  No
single event separates and forms, yet both global coordinates can hold. -/
def mixedLoops : System where
  Event := Bool
  propagates := fun first second => first = second
  separates := fun event => event = false
  forms := fun event => event = true
  reflexiveRepresentation := fun _ => True

theorem mixedLoops_all_four_coordinates :
    (Profile.ofSystem mixedLoops).pain /\
    (Profile.ofSystem mixedLoops).suffering /\
    (Profile.ofSystem mixedLoops).joy /\
    (Profile.ofSystem mixedLoops).happiness := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact ⟨false, false, rfl, ⟨.edge rfl⟩, trivial, rfl⟩
  · exact suffering_of_cycle (event := false) rfl (.edge rfl)
  · exact ⟨true, true, rfl, ⟨.edge rfl⟩, trivial, rfl⟩
  · exact happiness_of_cycle (event := true) rfl (.edge rfl)

theorem mixedLoops_no_event_has_both_reflexive_polarities (event : Bool) :
    ¬ (PainAt mixedLoops event /\ JoyAt mixedLoops event) := by
  apply not_pain_and_joy_of_disjoint
  intro current separation formation
  exact Bool.noConfusion (separation.symm.trans formation)

/-- A carrier may propagate through a neutral intermediary: the existing
`Cascade` requires signal-bearing carrier endpoints, not homogeneous polarity
at every event traversed by a path. -/
def neutralTransitCycle : System where
  Event := Bool
  propagates := fun first second => first ≠ second
  separates := fun event => event = false
  forms := fun _ => False
  reflexiveRepresentation := fun _ => False

theorem neutralTransitCycle_suffers : Suffering neutralTransitCycle := by
  apply suffering_of_cycle (event := false) rfl
  exact .trans (.edge Bool.false_ne_true)
    (.edge (fun equal => Bool.false_ne_true equal.symm))

/-- Its sustaining separation carrier has no direct separation-to-separation
edge.  This makes the path-based interpretation boundary explicit. -/
theorem neutralTransitCycle_no_direct_separation_edge :
    ¬ exists first second, neutralTransitCycle.separates first /\
      neutralTransitCycle.separates second /\
      neutralTransitCycle.propagates first second := by
  rintro ⟨first, second, firstSignal, secondSignal, propagation⟩
  exact propagation (firstSignal.trans secondSignal.symm)

/-- Ordinary maps can add pain and joy or collapse a terminal process into
a cycle.  Category membership alone is therefore not a reflection theorem. -/
def terminalToSeparatingLoop : terminalSeparation ⟶ separatingLoop where
  toFun := fun _ => ()
  map_propagates := fun _ => trivial
  map_separates := fun _ => trivial
  map_forms := fun formation => False.elim formation
  map_reflexiveRepresentation := fun _ => trivial

theorem ordinary_morphism_does_not_reflect_suffering :
    Nonempty (terminalSeparation ⟶ separatingLoop) /\
      Suffering separatingLoop /\ ¬ Suffering terminalSeparation :=
  ⟨⟨terminalToSeparatingLoop⟩, separatingLoop_suffers,
    terminalSeparation_not_suffering⟩

def nonreflexiveToSeparatingLoop : nonreflexiveSeparatingLoop ⟶ separatingLoop where
  toFun := id
  map_propagates := fun propagation => propagation
  map_separates := fun separation => separation
  map_forms := fun formation => formation
  map_reflexiveRepresentation := fun reflexive => False.elim reflexive

theorem ordinary_morphism_does_not_reflect_pain :
    Nonempty (nonreflexiveSeparatingLoop ⟶ separatingLoop) /\
      (Profile.ofSystem separatingLoop).pain /\
      ¬ (Profile.ofSystem nonreflexiveSeparatingLoop).pain :=
  ⟨⟨nonreflexiveToSeparatingLoop⟩, separatingLoop_has_pain,
    nonreflexiveSeparatingLoop_suffers_without_pain.2⟩

/-- The finite painful episode and sustaining painful loop have the same
reflexive observations, despite different suffering coordinates. -/
theorem terminal_and_loop_same_reflexive_projection :
    (Profile.ofSystem terminalSeparation).reflexive =
      (Profile.ofSystem separatingLoop).reflexive := by
  apply Prod.ext
  · exact propext ⟨fun _ => separatingLoop_has_pain,
      fun _ => ⟨true, terminalSeparation_pain_without_suffering.1⟩⟩
  · apply propext
    constructor
    · rintro ⟨_, joy⟩
      exact False.elim (joy_requires_formation joy)
    · intro joy
      exact False.elim (separatingLoop_has_no_joy joy)

/-- Reflexive-event existence cannot reconstruct the suffering coordinate
across these concrete systems. -/
theorem no_reflexive_projection_recovers_suffering :
    ¬ exists observer : (Prop × Prop) -> Prop,
      forall system : System.{0},
        observer (Profile.ofSystem system).reflexive ↔ Suffering system := by
  rintro ⟨observer, reconstructs⟩
  have predictsLoop := (reconstructs separatingLoop).2 separatingLoop_suffers
  rw [← terminal_and_loop_same_reflexive_projection] at predictsLoop
  exact terminalSeparation_not_suffering
    ((reconstructs terminalSeparation).1 predictsLoop)

/-- Two sustaining separation loops can have the same sustained observations
while differing in whether any separation reaches a reflexive representation. -/
theorem reflexive_and_nonreflexive_same_sustained_projection :
    (Profile.ofSystem separatingLoop).sustained =
      (Profile.ofSystem nonreflexiveSeparatingLoop).sustained := by
  apply Prod.ext
  · exact propext ⟨fun _ => nonreflexiveSeparatingLoop_suffers_without_pain.1,
      fun _ => separatingLoop_suffers⟩
  · apply propext
    exact ⟨fun happy => False.elim (separatingLoop_not_happy happy),
      fun happy => False.elim (nonreflexiveSeparatingLoop_not_happy happy)⟩

/-- Sustaining-carrier existence cannot reconstruct reflexive pain. -/
theorem no_sustained_projection_recovers_pain :
    ¬ exists observer : (Prop × Prop) -> Prop,
      forall system : System.{0},
        observer (Profile.ofSystem system).sustained ↔
          (Profile.ofSystem system).pain := by
  rintro ⟨observer, reconstructs⟩
  have predictsPain := (reconstructs separatingLoop).2 separatingLoop_has_pain
  rw [reflexive_and_nonreflexive_same_sustained_projection] at predictsPain
  exact nonreflexiveSeparatingLoop_suffers_without_pain.2
    ((reconstructs nonreflexiveSeparatingLoop).1 predictsPain)

end Canary

end Mettapedia.Cybernetics.ReflexiveValence

#print axioms Mettapedia.Cybernetics.ReflexiveValence.pain_map
#print axioms Mettapedia.Cybernetics.ReflexiveValence.suffering_map
#print axioms Mettapedia.Cybernetics.ReflexiveValence.Canary.pain_at_representation
#print axioms Mettapedia.Cybernetics.ReflexiveValence.Canary.isolated_protoPain_but_not_pain
#print axioms Mettapedia.Cybernetics.ReflexiveValence.Canary.terminalSeparation_not_suffering
#print axioms Mettapedia.Cybernetics.ReflexiveValence.no_cascades_of_decreasing_rank
#print axioms Mettapedia.Cybernetics.ReflexiveValence.no_map_to_decreasing_rank
#print axioms Mettapedia.Cybernetics.ReflexiveValence.Profile.ofSystem_iso_eq
#print axioms Mettapedia.Cybernetics.ReflexiveValence.Canary.terminalSeparation_pain_without_suffering
#print axioms Mettapedia.Cybernetics.ReflexiveValence.Canary.nonreflexiveSeparatingLoop_suffers_without_pain
#print axioms Mettapedia.Cybernetics.ReflexiveValence.Canary.terminalFormation_joy_without_happiness
#print axioms Mettapedia.Cybernetics.ReflexiveValence.Canary.nonreflexiveFormingLoop_happy_without_joy
#print axioms Mettapedia.Cybernetics.ReflexiveValence.Canary.mixedLoops_all_four_coordinates
#print axioms Mettapedia.Cybernetics.ReflexiveValence.Canary.neutralTransitCycle_no_direct_separation_edge
#print axioms Mettapedia.Cybernetics.ReflexiveValence.Canary.no_reflexive_projection_recovers_suffering
#print axioms Mettapedia.Cybernetics.ReflexiveValence.Canary.no_sustained_projection_recovers_pain
