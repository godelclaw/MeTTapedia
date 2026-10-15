import Mettapedia.Cybernetics.ReflexiveValence
import Mettapedia.CategoryTheory.PartialSections
import Mathlib.CategoryTheory.Yoneda

/-!
# Rooted content presentations and their partial descriptions

A content presentation consists of an existing relational valence system and
a selected event.  Its arrows retain the full event map and carry that event
to the selected target.  They form a genuinely non-thin category: different
root-preserving automorphisms can act differently on other events.

This is a candidate structural vocabulary for phenomenal interpretation, not
a theory assigning actual experience to its objects.  The local predicates
`PainAt` and `JoyAt` remain separate from the explicitly global sustaining
carrier predicates `Suffering` and `Happiness`.  None is a scalar, and the
four logical facets are not claimed to exhaust phenomenal content.

Exact profiles are partial sections with all four facets assigned.  General
structural maps preserve positive predicates but can create new predicates;
they therefore need not preserve those exact assignments.  Exact profile
transport is proved for isomorphisms.  A separate positive-description
functor records the supported facets, and deliberately forgets event maps.
Arbitrary additional features and structured values can be retained beside
the four facets without requiring a shared scalar scale.

Enriched presentations retain those additional values at every event, not
only in a selected report.  Their arrows preserve the values along the full
event map.  Feature restriction forgets a declared vocabulary, whereas a
full Yoneda interface reconstructs an enriched presentation up to isomorphism
within this specified category.  Neither construction establishes an actual
experience assignment or a correspondence with a physical implementation.

The construction is a mathematical extension of the relational account in
*On the Ontology of Joy and Pain, Happiness and Suffering*, Garden of Minds.
It takes seriously the distinction between proposed categories of content
and reports discussed by Tsuchiya and Saigo (2021), and by Tsuchiya, Saigo
and Phillips (2023): https://doi.org/10.1093/nc/niab034 and
https://doi.org/10.3389/fpsyg.2022.1053977.  The assignment adjunction in
`PartialSections` is not identified with their hypothesized qualia/report adjunction.
Experiential adequacy and a physical or experiential interpretation remain
additional hypotheses.
-/

set_option autoImplicit false

namespace Mettapedia.CogArch.Consciousness.PhenomenalContent

open _root_.CategoryTheory

open Mettapedia.Cybernetics Mettapedia.CategoryTheory

universe u v w

/-- A relational presentation with the event whose local content is selected. -/
structure Content where
  system : ReflexiveValence.System.{u}
  focus : system.Event

/-- An arrow retains its full event map and the selected-event equation. -/
structure Hom (source target : Content.{u}) where
  underlying : source.system ⟶ target.system
  map_focus : underlying.toFun source.focus = target.focus

@[ext]
theorem Hom.ext {source target : Content.{u}} {first second : Hom source target}
    (sameMap : first.underlying = second.underlying) : first = second := by
  cases first
  cases second
  cases sameMap
  rfl

instance : Category.{u} (Content.{u}) where
  Hom := Hom
  id content := ⟨𝟙 content.system, rfl⟩
  comp first second := {
    underlying := first.underlying ≫ second.underlying
    map_focus := (congrArg second.underlying.toFun first.map_focus).trans second.map_focus }
  id_comp := by intros; apply Hom.ext; exact Category.id_comp _
  comp_id := by intros; apply Hom.ext; exact Category.comp_id _
  assoc := by intros; apply Hom.ext; exact Category.assoc _ _ _

/-- Forgetting the selected event retains the actual relational-system map. -/
def forget : Content.{u} ⥤ ReflexiveValence.System.{u} where
  obj := Content.system
  map := Hom.underlying
  map_id _ := rfl
  map_comp _ _ := rfl

instance : forget.{u}.Faithful where
  map_injective sameMap := Hom.ext sameMap

/-- An isomorphism of the complete representable interfaces reconstructs
an isomorphism of these rooted presentations.  This uses Mathlib's Yoneda
construction and is relative to this choice of objects and arrows; it is
neither experiential equality nor an assertion of physical realization. -/
noncomputable def reconstruct (source target : Content.{u})
    (comparison : yoneda.obj source ≅ yoneda.obj target) : source ≅ target :=
  Yoneda.fullyFaithful.preimageIso comparison

theorem isomorphic_iff_full_interface (source target : Content.{u}) :
    Nonempty (source ≅ target) ↔ Nonempty (yoneda.obj source ≅ yoneda.obj target) := by
  constructor
  · rintro ⟨isomorphism⟩
    exact ⟨yoneda.mapIso isomorphism⟩
  · rintro ⟨comparison⟩
    exact ⟨reconstruct source target comparison⟩

namespace Hom

variable {source target : Content.{u}} (morphism : source ⟶ target)

include morphism

/-- Local separation polarity transports to the selected target event. -/
theorem protoPain_map (separation : ReflexiveValence.ProtoPain source.system source.focus) :
    ReflexiveValence.ProtoPain target.system target.focus := by
  have mapped := morphism.underlying.map_separates separation
  simpa only [ReflexiveValence.ProtoPain, morphism.map_focus] using mapped

theorem protoJoy_map (formation : ReflexiveValence.ProtoJoy source.system source.focus) :
    ReflexiveValence.ProtoJoy target.system target.focus := by
  have mapped := morphism.underlying.map_forms formation
  simpa only [ReflexiveValence.ProtoJoy, morphism.map_focus] using mapped

/-- The complete nonempty propagation history remains available at the
selected target, including the mapped originating event. -/
def pathToFocus {origin : source.system.Event}
    (path : ReflexiveValence.PropagationPath source.system origin source.focus) :
    ReflexiveValence.PropagationPath target.system (morphism.underlying.toFun origin) target.focus :=
  morphism.map_focus ▸ path.map morphism.underlying

theorem pain_map (pain : ReflexiveValence.PainAt source.system source.focus) :
    ReflexiveValence.PainAt target.system target.focus := by
  have mapped := ReflexiveValence.pain_map morphism.underlying pain
  simpa only [morphism.map_focus] using mapped

theorem joy_map (joy : ReflexiveValence.JoyAt source.system source.focus) :
    ReflexiveValence.JoyAt target.system target.focus := by
  have mapped := ReflexiveValence.joy_map morphism.underlying joy
  simpa only [morphism.map_focus] using mapped

theorem suffering_map (suffering : ReflexiveValence.Suffering source.system) :
    ReflexiveValence.Suffering target.system := ReflexiveValence.suffering_map morphism.underlying suffering

theorem happiness_map (happiness : ReflexiveValence.Happiness source.system) :
    ReflexiveValence.Happiness target.system := ReflexiveValence.happiness_map morphism.underlying happiness

end Hom

/-- The labels mark local versus global scope explicitly. -/
inductive Facet
  | pain
  | joy
  | globalSuffering
  | globalHappiness
  deriving DecidableEq, Repr

/-- Four separately named structural propositions; none entails an actual
experience assignment merely by being a predicate of this presentation. -/
def statement (content : Content.{u}) : Facet → Prop
  | .pain => ReflexiveValence.PainAt content.system content.focus
  | .joy => ReflexiveValence.JoyAt content.system content.focus
  | .globalSuffering => ReflexiveValence.Suffering content.system
  | .globalHappiness => ReflexiveValence.Happiness content.system

theorem statement_map {source target : Content.{u}} (morphism : source ⟶ target)
    (facet : Facet) : statement source facet → statement target facet := by
  cases facet
  · exact morphism.pain_map
  · exact morphism.joy_map
  · exact morphism.suffering_map
  · exact morphism.happiness_map

theorem statement_iso_iff {source target : Content.{u}}
    (isomorphism : source ≅ target) (facet : Facet) :
    statement target facet ↔ statement source facet :=
  ⟨statement_map isomorphism.inv facet, statement_map isomorphism.hom facet⟩

/-- An exact assignment of the chosen vocabulary; its total context is not a
claim that the vocabulary describes every aspect of experience or reality. -/
def description (content : Content.{u}) : PartialSections.View Facet Prop :=
  PartialSections.total (statement content)

/-- A declared report restricts the exact assignment to the named facets. -/
def report (observed : Set Facet) (content : Content.{u}) : PartialSections.View Facet Prop :=
  PartialSections.restrict observed (description content)

theorem description_iso_eq {source target : Content.{u}} (isomorphism : source ≅ target) :
    description source = description target := by
  apply PartialSections.View.ext
  · rfl
  · intro facet _ _
    exact propext (statement_iso_iff isomorphism facet).symm

theorem report_iso_eq {source target : Content.{u}} (isomorphism : source ≅ target)
    (observed : Set Facet) : report observed source = report observed target :=
  congrArg (PartialSections.restrict observed) (description_iso_eq isomorphism)

/-- Successive reporting obeys the existing context-intersection law. -/
theorem report_restrict (first second : Set Facet) (content : Content.{u}) :
    PartialSections.restrict first (report second content) = report (first ∩ second) content :=
  PartialSections.restrict_restrict first second (description content)

/-- A positive description exposes exactly the currently supported facets.
The true assertion value is deliberate; unsupported facets are outside its
context rather than silently identified with established falsehood. -/
def positiveDescription (content : Content.{u}) : PartialSections.View Facet Bool where
  context := {facet | statement content facet}
  values _ := true

theorem positiveDescription_le {source target : Content.{u}} (morphism : source ⟶ target) :
    positiveDescription source ≤ positiveDescription target :=
  ⟨fun facet supported => statement_map morphism facet supported, fun _ _ _ => rfl⟩

/-- This actual functor retains positive support and forgets event maps.
Exact four-coordinate profiles above do not define this functor. -/
def positiveDescriptionFunctor : Content.{u} ⥤ PartialSections.View Facet Bool where
  obj := positiveDescription
  map morphism := homOfLE (positiveDescription_le morphism)

/-- Reporting positive support is compositional through context restriction. -/
def positiveReportFunctor (observed : Set Facet) : Content.{u} ⥤ PartialSections.View Facet Bool :=
  positiveDescriptionFunctor ⋙ PartialSections.restrictionFunctor observed

/-- Additional features can have arbitrary structured values, independently
of the proposition-valued structural facets.  The sum tags retain which kind
of value is present. -/
def enrichedDescription {Feature : Type v} {Value : Type w}
    (content : Content.{u}) (extra : Feature → Value) :
    PartialSections.View (Facet ⊕ Feature) (Prop ⊕ Value) :=
  PartialSections.total fun
    | .inl facet => .inl (statement content facet)
    | .inr feature => .inr (extra feature)

/-- Changing an additional dimension remains visible in its exact enriched
description, even when the four structural propositions stay fixed. -/
theorem extra_difference_is_retained {Feature : Type v} {Value : Type w}
    (content : Content.{u}) (first second : Feature → Value) (feature : Feature)
    (different : first feature ≠ second feature) :
    enrichedDescription content first ≠ enrichedDescription content second := by
  intro same
  have assignments := PartialSections.total_injective same
  exact different (Sum.inr.inj (congrFun assignments (.inr feature)))

/-! ## Event-indexed additional qualities and their structural maps -/

/-- Additional qualities are part of the event presentation itself.  Their
value type can retain any product or structured family; no numerical order,
aggregation or common scalar is assumed. -/
structure EnrichedContent (Feature : Type v) (Value : Type w) where
  content : Content.{u}
  extra : Feature → content.system.Event → Value

namespace EnrichedContent

variable {Feature : Type v} {Value : Type w}

/-- An enriched arrow retains the rooted event map and each independently
named quality at every mapped event, including events outside the focus. -/
structure Hom (source target : EnrichedContent.{u} Feature Value) where
  underlying : source.content ⟶ target.content
  map_extra : ∀ feature event,
    target.extra feature (underlying.underlying.toFun event) = source.extra feature event

@[ext]
theorem Hom.ext {source target : EnrichedContent.{u} Feature Value}
    {first second : Hom source target} (sameMap : first.underlying = second.underlying) :
    first = second := by
  cases first
  cases second
  cases sameMap
  rfl

instance : Category.{u} (EnrichedContent.{u} Feature Value) where
  Hom := Hom
  id presentation := {
    underlying := 𝟙 presentation.content
    map_extra := fun _ _ => rfl }
  comp first second := {
    underlying := first.underlying ≫ second.underlying
    map_extra := fun feature event =>
      (second.map_extra feature (first.underlying.underlying.toFun event)).trans
        (first.map_extra feature event) }
  id_comp := by intros; apply Hom.ext; exact Category.id_comp _
  comp_id := by intros; apply Hom.ext; exact Category.comp_id _
  assoc := by intros; apply Hom.ext; exact Category.assoc _ _ _

/-- Forgetting the additional qualities retains the actual rooted event map;
it need not reflect the existence of an enriched arrow. -/
def forget : EnrichedContent.{u} Feature Value ⥤ Content.{u} where
  obj := EnrichedContent.content
  map := Hom.underlying
  map_id _ := rfl
  map_comp _ _ := rfl

instance : (forget (Feature := Feature) (Value := Value)).Faithful where
  map_injective sameMap := Hom.ext sameMap

/-- Read each additional quality at the explicitly selected event. -/
def atFocus (presentation : EnrichedContent.{u} Feature Value) : Feature → Value :=
  fun feature => presentation.extra feature presentation.content.focus

/-- Exact extra-coordinate transport holds along every enriched arrow,
independently of the one-sided transport of structural propositions. -/
theorem atFocus_map {source target : EnrichedContent.{u} Feature Value}
    (morphism : source ⟶ target) (feature : Feature) :
    atFocus target feature = atFocus source feature := by
  simpa only [atFocus, morphism.underlying.map_focus] using
    morphism.map_extra feature source.content.focus

/-- A mismatch at a retained root coordinate blocks any enriched arrow,
even if the bare rooted contents happen to agree. -/
theorem no_hom_of_focus_mismatch {source target : EnrichedContent.{u} Feature Value}
    (feature : Feature) (different : atFocus source feature ≠ atFocus target feature) :
    ¬ Nonempty (source ⟶ target) := by
  rintro ⟨morphism⟩
  exact different (atFocus_map morphism feature).symm

/-- The exact report reads the existing four structural facets and every
additional quality from the enriched object's selected event. -/
def description (presentation : EnrichedContent.{u} Feature Value) :
    PartialSections.View (Facet ⊕ Feature) (Prop ⊕ Value) :=
  enrichedDescription presentation.content (atFocus presentation)

def report (observed : Set (Facet ⊕ Feature))
    (presentation : EnrichedContent.{u} Feature Value) :
    PartialSections.View (Facet ⊕ Feature) (Prop ⊕ Value) :=
  PartialSections.restrict observed (description presentation)

/-- An enriched isomorphism preserves both structural truth assignments and
the independently named extra values.  This identifies descriptions rather
than subjects or physical occurrences. -/
theorem description_iso_eq {source target : EnrichedContent.{u} Feature Value}
    (isomorphism : source ≅ target) : description source = description target := by
  apply PartialSections.View.ext
  · rfl
  · intro feature _ _
    cases feature with
    | inl facet =>
        exact congrArg Sum.inl (propext (statement_iso_iff (forget.mapIso isomorphism) facet).symm)
    | inr feature => exact congrArg Sum.inr (atFocus_map isomorphism.hom feature).symm

theorem report_iso_eq {source target : EnrichedContent.{u} Feature Value}
    (isomorphism : source ≅ target) (observed : Set (Facet ⊕ Feature)) :
    report observed source = report observed target :=
  congrArg (PartialSections.restrict observed) (description_iso_eq isomorphism)

/-- Reconstruction includes every retained event-indexed quality because
those values constrain the arrows of this enriched category. -/
noncomputable def reconstruct (source target : EnrichedContent.{u} Feature Value)
    (comparison : yoneda.obj source ≅ yoneda.obj target) : source ≅ target :=
  Yoneda.fullyFaithful.preimageIso comparison

theorem isomorphic_iff_full_interface (source target : EnrichedContent.{u} Feature Value) :
    Nonempty (source ≅ target) ↔ Nonempty (yoneda.obj source ≅ yoneda.obj target) := by
  constructor
  · rintro ⟨isomorphism⟩
    exact ⟨yoneda.mapIso isomorphism⟩
  · rintro ⟨comparison⟩
    exact ⟨reconstruct source target comparison⟩

/-- Restrict qualities to the declared subtype vocabulary.  The rooted
events and propagation structure remain available without re-encoding. -/
def restrict (observed : Set Feature) (presentation : EnrichedContent.{u} Feature Value) :
    EnrichedContent.{u} observed Value where
  content := presentation.content
  extra feature event := presentation.extra feature.val event

/-- Feature restriction acts on the full event maps, and its preservation
proof specializes the original coordinate law to the retained features. -/
def restrictionFunctor (observed : Set Feature) :
    EnrichedContent.{u} Feature Value ⥤ EnrichedContent.{u} observed Value where
  obj := restrict observed
  map morphism := {
    underlying := morphism.underlying
    map_extra := fun feature event => morphism.map_extra feature.val event }
  map_id _ := by apply Hom.ext; rfl
  map_comp _ _ := by apply Hom.ext; rfl

instance (observed : Set Feature) :
    (restrictionFunctor (Value := Value) observed).Faithful where
  map_injective {source target} {first second} sameMap := by
    apply Hom.ext
    exact congrArg (fun morphism : restrict observed source ⟶ restrict observed target =>
      morphism.underlying) sameMap

/-- Restriction changes the quality vocabulary while preserving exactly the
underlying rooted-map functor. -/
theorem restriction_forget (observed : Set Feature) :
    restrictionFunctor (Value := Value) observed ⋙ forget =
      forget (Feature := Feature) (Value := Value) := rfl

theorem atFocus_restrict (observed : Set Feature)
    (presentation : EnrichedContent.{u} Feature Value) (feature : observed) :
    atFocus (restrict observed presentation) feature = atFocus presentation feature.val := rfl

/-- Re-index a restricted-quality description in the original combined
vocabulary. Structural facets are retained, and selected qualities name their
original coordinates rather than acquiring new values. -/
def includedFeatures (observed : Set Feature) : Facet ⊕ observed → Facet ⊕ Feature :=
  Sum.map id Subtype.val

/-- Feature restriction retains every structural facet and only the declared
additional-quality coordinates. It does not constrain what exists outside
the vocabulary. -/
def featureContext (observed : Set Feature) : Set (Facet ⊕ Feature) :=
  {coordinate | match coordinate with
    | .inl _ => True
    | .inr feature => feature ∈ observed}

theorem includedFeatures_context (observed : Set Feature) :
    includedFeatures observed ⁻¹' featureContext observed = Set.univ := by
  ext coordinate
  cases coordinate with
  | inl facet => simp [includedFeatures, featureContext]
  | inr feature => simp [includedFeatures, featureContext, feature.property]

/-- The generic feature-pullback law exactly describes reading the enriched
object with a smaller quality vocabulary. -/
theorem description_restrict (observed : Set Feature)
    (presentation : EnrichedContent.{u} Feature Value) :
    PartialSections.reindexFeatures (includedFeatures observed) (description presentation) =
      description (restrict observed presentation) := by
  apply PartialSections.View.ext
  · exact Set.preimage_univ
  · intro coordinate _ _
    cases coordinate <;> rfl

/-- Restricting the object and reporting the corresponding original
coordinates commute after their explicit subtype re-indexing. -/
theorem report_restrict (observed : Set Feature)
    (presentation : EnrichedContent.{u} Feature Value) :
    PartialSections.reindexFeatures (includedFeatures observed)
      (report (featureContext observed) presentation) =
        description (restrict observed presentation) := by
  rw [report, PartialSections.reindexFeatures_restrict, includedFeatures_context,
    PartialSections.restrict_univ, description_restrict]

end EnrichedContent

/-! ## Real maps and scope-sensitive controls -/

namespace Controls

def terminalPain : Content := ⟨ReflexiveValence.Canary.terminalSeparation, true⟩
def separatingPainLoop : Content := ⟨ReflexiveValence.Canary.separatingLoop, ()⟩
def nonreflexiveSeparation : Content := ⟨ReflexiveValence.Canary.nonreflexiveSeparatingLoop, ()⟩
def terminalJoy : Content := ⟨ReflexiveValence.Canary.terminalFormation, true⟩
def formingJoyLoop : Content := ⟨ReflexiveValence.Canary.formingLoop, ()⟩
def nonreflexiveFormation : Content := ⟨ReflexiveValence.Canary.nonreflexiveFormingLoop, ()⟩

theorem local_pain_without_global_suffering :
    statement terminalPain .pain ∧ ¬ statement terminalPain .globalSuffering :=
  ReflexiveValence.Canary.terminalSeparation_pain_without_suffering

theorem global_suffering_without_local_pain :
    statement nonreflexiveSeparation .globalSuffering ∧
      ¬ statement nonreflexiveSeparation .pain := by
  refine ⟨ReflexiveValence.Canary.nonreflexiveSeparatingLoop_suffers_without_pain.1, ?_⟩
  intro pain
  exact ReflexiveValence.Canary.nonreflexiveSeparatingLoop_suffers_without_pain.2 ⟨(), pain⟩

theorem local_joy_without_global_happiness :
    statement terminalJoy .joy ∧ ¬ statement terminalJoy .globalHappiness :=
  ReflexiveValence.Canary.terminalFormation_joy_without_happiness

theorem global_happiness_without_local_joy :
    statement nonreflexiveFormation .globalHappiness ∧
      ¬ statement nonreflexiveFormation .joy := by
  refine ⟨ReflexiveValence.Canary.nonreflexiveFormingLoop_happy_without_joy.1, ?_⟩
  intro joy
  exact ReflexiveValence.Canary.nonreflexiveFormingLoop_happy_without_joy.2 ⟨(), joy⟩

theorem separatingPainLoop_pain : statement separatingPainLoop .pain :=
  ⟨(), trivial, ⟨.edge trivial⟩, trivial, trivial⟩

theorem separatingPainLoop_suffering : statement separatingPainLoop .globalSuffering :=
  ReflexiveValence.Canary.separatingLoop_suffers

def painOnly : Set Facet := {.pain}

/-- A local pain-only report cannot distinguish a finite terminal episode
from a sustaining carrier.  The whole rooted objects remain different. -/
theorem pain_only_reports_agree :
    report painOnly terminalPain = report painOnly separatingPainLoop := by
  apply PartialSections.View.ext
  · rfl
  · intro facet inFirst _
    have same : facet = .pain := inFirst.2
    subst facet
    exact propext ⟨fun _ => separatingPainLoop_pain,
      fun _ => local_pain_without_global_suffering.1⟩

theorem exact_descriptions_distinguish_global_suffering :
    description terminalPain ≠ description separatingPainLoop := by
  intro same
  have assignments := PartialSections.total_injective same
  have sufferingEqual := congrFun assignments Facet.globalSuffering
  exact local_pain_without_global_suffering.2 (sufferingEqual.symm ▸ separatingPainLoop_suffering)

/-- Adding real returning edges changes the sustaining-carrier condition.
The event carrier itself still has two distinguishable events. -/
def loopCompletionSystem : ReflexiveValence.System where
  Event := Bool
  propagates first second :=
    ReflexiveValence.Canary.terminalSeparation.propagates first second ∨ first = second
  separates _ := True
  forms _ := False
  reflexiveRepresentation _ := True

def loopCompletion : Content := ⟨loopCompletionSystem, true⟩

/-- The nonconstant event map embeds the original terminal relation into
the enlarged relation; this is not an identity arrow of rooted contents. -/
def addReturningEdges : terminalPain ⟶ loopCompletion where
  underlying := {
    toFun := id
    map_propagates := fun propagation => .inl propagation
    map_separates := fun separation => separation
    map_forms := fun formation => formation
    map_reflexiveRepresentation := fun reflexive => reflexive }
  map_focus := rfl

theorem loopCompletion_suffers : statement loopCompletion .globalSuffering :=
  ReflexiveValence.suffering_of_cycle (event := true) trivial (.edge (.inr rfl))

/-- Positive support transports, although exact absence of the global
sustaining condition does not. -/
theorem positive_transport_need_not_preserve_exact_profile :
    positiveDescription terminalPain ≤ positiveDescription loopCompletion ∧
      ¬ (description terminalPain ≤ description loopCompletion) := by
  refine ⟨positiveDescription_le addReturningEdges, ?_⟩
  intro exactExtension
  have equal : statement terminalPain .globalSuffering =
      statement loopCompletion .globalSuffering :=
    exactExtension.2 .globalSuffering (by simp [description, PartialSections.total])
      (by simp [description, PartialSections.total])
  exact local_pain_without_global_suffering.2 (equal.symm ▸ loopCompletion_suffers)

theorem enlarged_relation_has_no_return_map : ¬ Nonempty (loopCompletion ⟶ terminalPain) := by
  rintro ⟨morphism⟩
  exact local_pain_without_global_suffering.2 (morphism.suffering_map loopCompletion_suffers)

/-- A presentation with genuinely independent event coordinates.  Both
polarities may occur in the same event, and events have real returning edges. -/
def pairSystem : ReflexiveValence.System where
  Event := Bool × Bool
  propagates := Eq
  separates event := event.1 = false ∨ event.2 = false
  forms event := event.1 = true ∨ event.2 = true
  reflexiveRepresentation _ := True

def paired : Content := ⟨pairSystem, (false, false)⟩

/-- Swapping event coordinates is a nonconstant rooted automorphism. -/
def swap : paired ⟶ paired where
  underlying := {
    toFun := Prod.swap
    map_propagates := fun equal => congrArg Prod.swap equal
    map_separates := fun separation => separation.elim Or.inr Or.inl
    map_forms := fun formation => formation.elim Or.inr Or.inl
    map_reflexiveRepresentation := fun reflexive => reflexive }
  map_focus := rfl

def swapIso : paired ≅ paired where
  hom := swap
  inv := swap
  hom_inv_id := by apply Hom.ext; apply ReflexiveValence.Hom.ext; funext event; cases event; rfl
  inv_hom_id := by apply Hom.ext; apply ReflexiveValence.Hom.ext; funext event; cases event; rfl

theorem swap_is_distinct_from_identity : swap ≠ 𝟙 paired := by
  intro same
  have eventEqual := congrArg
    (fun morphism : paired ⟶ paired => morphism.underlying.toFun (false, true)) same
  change (true, false) = (false, true) at eventEqual
  exact Bool.noConfusion (congrArg Prod.fst eventEqual)

/-- The rooted category is genuinely non-thin: two event maps can agree on
the selected root and still disagree on another event. -/
theorem rooted_category_has_distinct_parallel_arrows :
    ∃ first second : paired ⟶ paired, first ≠ second :=
  ⟨swap, 𝟙 paired, swap_is_distinct_from_identity⟩

/-- Positive descriptions intentionally forget those arrow distinctions. -/
theorem positive_description_functor_forgets_event_map :
    positiveDescriptionFunctor.map swap = positiveDescriptionFunctor.map (𝟙 paired) ∧
      swap ≠ 𝟙 paired :=
  ⟨Subsingleton.elim _ _, swap_is_distinct_from_identity⟩

theorem positiveDescriptionFunctor_not_faithful : ¬ positiveDescriptionFunctor.{0}.Faithful := by
  intro faithful
  exact swap_is_distinct_from_identity
    (faithful.map_injective positive_description_functor_forgets_event_map.1)

/-- The full representable interface retains the event-map distinction that
the positive-coordinate report functor erased. -/
theorem full_probes_distinguish_event_maps :
    yoneda.map swap ≠ yoneda.map (𝟙 paired) := by
  intro same
  exact swap_is_distinct_from_identity (yoneda.map_injective same)

/-- A real injective, nonconstant map from the existing mixed-polarity loop
system places each event on the diagonal of the pair system. -/
def mixedRoot : Content := ⟨ReflexiveValence.Canary.mixedLoops, false⟩

def mixedOtherRoot : Content := ⟨ReflexiveValence.Canary.mixedLoops, true⟩

theorem mixedRoot_has_local_pain : statement mixedRoot .pain :=
  ⟨false, rfl, ⟨.edge rfl⟩, trivial, rfl⟩

theorem mixedOtherRoot_has_local_joy : statement mixedOtherRoot .joy :=
  ⟨true, rfl, ⟨.edge rfl⟩, trivial, rfl⟩

theorem mixedOtherRoot_has_no_local_pain : ¬ statement mixedOtherRoot .pain := by
  intro pain
  have impossible : true = false := ReflexiveValence.pain_requires_separation pain
  exact Bool.noConfusion impossible

/-- Changing the selected event changes local content without changing the
whole presented substrate.  This is a concrete indexical distinction. -/
theorem same_substrate_different_local_content :
    mixedRoot.system = mixedOtherRoot.system ∧ statement mixedRoot .pain ∧
      ¬ statement mixedOtherRoot .pain :=
  ⟨rfl, mixedRoot_has_local_pain, mixedOtherRoot_has_no_local_pain⟩

theorem incompatible_focus_blocks_rooted_map : ¬ Nonempty (mixedRoot ⟶ mixedOtherRoot) := by
  rintro ⟨morphism⟩
  exact mixedOtherRoot_has_no_local_pain (morphism.pain_map mixedRoot_has_local_pain)

def diagonal : mixedRoot ⟶ paired where
  underlying := {
    toFun event := (event, event)
    map_propagates := fun equal => congrArg (fun event => (event, event)) equal
    map_separates := Or.inl
    map_forms := Or.inl
    map_reflexiveRepresentation := fun reflexive => reflexive }
  map_focus := rfl

theorem diagonal_is_injective : Function.Injective diagonal.underlying.toFun := by
  intro first second equal
  exact congrArg Prod.fst equal

end Controls

/-! ## Extra-coordinate recoding and deliberate information loss -/

namespace EnrichedControls

/-- The two feature names read independently variable event coordinates. -/
def coordinateSource : EnrichedContent Bool Bool where
  content := Controls.paired
  extra feature event := if feature then event.2 else event.1

/-- The target uses the opposite event-coordinate convention. -/
def coordinateTarget : EnrichedContent Bool Bool where
  content := Controls.paired
  extra feature event := if feature then event.1 else event.2

/-- A real event swap transports both labelled quality readings, including
events that are different from the selected root. -/
def coordinateSwap : coordinateSource ≅ coordinateTarget where
  hom := {
    underlying := Controls.swap
    map_extra := by intro feature event; cases feature <;> rfl }
  inv := {
    underlying := Controls.swap
    map_extra := by intro feature event; cases feature <;> rfl }
  hom_inv_id := by apply EnrichedContent.Hom.ext; exact Controls.swapIso.hom_inv_id
  inv_hom_id := by apply EnrichedContent.Hom.ext; exact Controls.swapIso.inv_hom_id

theorem coordinate_recoding_changes_event_map :
    coordinateSwap.hom.underlying ≠ 𝟙 Controls.paired :=
  Controls.swap_is_distinct_from_identity

theorem source_coordinates_remain_distinct :
    coordinateSource.extra false (false, true) = false ∧
      coordinateSource.extra true (false, true) = true := ⟨rfl, rfl⟩

theorem recoded_coordinates_remain_distinct :
    coordinateTarget.extra false (coordinateSwap.hom.underlying.underlying.toFun (false, true)) =
      false ∧
    coordinateTarget.extra true (coordinateSwap.hom.underlying.underlying.toFun (false, true)) =
      true := ⟨rfl, rfl⟩

theorem coordinate_recoding_preserves_enriched_description :
    EnrichedContent.description coordinateSource = EnrichedContent.description coordinateTarget :=
  EnrichedContent.description_iso_eq coordinateSwap

/-- Reversing one quality changes its value at the root without changing the
bare event carrier, propagation structure, structural facets or other quality. -/
def alteredRoot : EnrichedContent Bool Bool where
  content := Controls.paired
  extra feature event := if feature then event.2 else !event.1

theorem altered_coordinate_mismatches_at_root :
    EnrichedContent.atFocus coordinateSource false ≠ EnrichedContent.atFocus alteredRoot false := by
  intro same
  exact Bool.noConfusion same

theorem same_bare_content_does_not_license_enriched_map :
    coordinateSource.content = alteredRoot.content ∧
      ¬ Nonempty (coordinateSource ⟶ alteredRoot) :=
  ⟨rfl, EnrichedContent.no_hom_of_focus_mismatch false altered_coordinate_mismatches_at_root⟩

theorem mismatched_quality_blocks_enriched_isomorphism :
    ¬ Nonempty (coordinateSource ≅ alteredRoot) := by
  rintro ⟨isomorphism⟩
  exact same_bare_content_does_not_license_enriched_map.2 ⟨isomorphism.hom⟩

theorem enriched_description_retains_root_difference :
    EnrichedContent.description coordinateSource ≠ EnrichedContent.description alteredRoot :=
  extra_difference_is_retained Controls.paired _ _ false altered_coordinate_mismatches_at_root

theorem enriched_full_interfaces_retain_root_difference :
    ¬ Nonempty (yoneda.obj coordinateSource ≅ yoneda.obj alteredRoot) :=
  fun comparison => mismatched_quality_blocks_enriched_isomorphism
    ((EnrichedContent.isomorphic_iff_full_interface coordinateSource alteredRoot).2 comparison)

/-- Removing the disagreeing quality from the vocabulary makes the same
bare identity map admissible. This explicitly loses an object distinction;
it does not assert that the removed quality ceased to exist. -/
def restrictionHidesMismatch :
    EnrichedContent.restrict {true} coordinateSource ≅
      EnrichedContent.restrict {true} alteredRoot where
  hom := {
    underlying := 𝟙 Controls.paired
    map_extra := by
      rintro ⟨feature, member⟩ event
      have equal : feature = true := member
      subst feature
      rfl }
  inv := {
    underlying := 𝟙 Controls.paired
    map_extra := by
      rintro ⟨feature, member⟩ event
      have equal : feature = true := member
      subst feature
      rfl }
  hom_inv_id := by apply EnrichedContent.Hom.ext; exact Category.id_comp _
  inv_hom_id := by apply EnrichedContent.Hom.ext; exact Category.id_comp _

theorem retained_quality_reports_agree :
    EnrichedContent.description (EnrichedContent.restrict {true} coordinateSource) =
      EnrichedContent.description (EnrichedContent.restrict {true} alteredRoot) :=
  EnrichedContent.description_iso_eq restrictionHidesMismatch

/-- Nonconstant additional values can coexist with distinguishable parallel
event maps. These two names read disjunction and conjunction respectively. -/
def symmetricQualities : EnrichedContent Bool Bool where
  content := Controls.paired
  extra feature event := if feature then event.1 || event.2 else event.1 && event.2

def symmetricSwap : symmetricQualities ⟶ symmetricQualities where
  underlying := Controls.swap
  map_extra := by
    intro feature event
    rcases event with ⟨first, second⟩
    cases feature <;> cases first <;> cases second <;> rfl

theorem symmetric_swap_is_distinct_from_identity : symmetricSwap ≠ 𝟙 symmetricQualities := by
  intro same
  exact Controls.swap_is_distinct_from_identity
    (congrArg (fun morphism : symmetricQualities ⟶ symmetricQualities => morphism.underlying) same)

theorem enriched_category_has_distinct_parallel_arrows :
    ∃ first second : symmetricQualities ⟶ symmetricQualities, first ≠ second :=
  ⟨symmetricSwap, 𝟙 symmetricQualities, symmetric_swap_is_distinct_from_identity⟩

theorem enriched_full_probes_distinguish_event_maps :
    yoneda.map symmetricSwap ≠ yoneda.map (𝟙 symmetricQualities) := by
  intro same
  exact symmetric_swap_is_distinct_from_identity (yoneda.map_injective same)

end EnrichedControls
end Mettapedia.CogArch.Consciousness.PhenomenalContent
