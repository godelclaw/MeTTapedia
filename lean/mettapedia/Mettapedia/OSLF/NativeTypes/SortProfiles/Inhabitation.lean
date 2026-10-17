import Mettapedia.OSLF.NativeTypes.SortProfiles.SiteInterfaces
import Mettapedia.Logic.LP.HypotheticalPropositional

open Mettapedia.OSLF.Framework

/-!
# Which levels of a generated hypercube have classifiers

A level is a carrier together with a sort, `(X, ∗)` or `(X, □)`: the place
where a classifier of `X`-elements lives. The completion of a presentation
adds the sort constants `∗^X : □^X`, so every `(X, □)` has a classifier. A
type at `(X, ∗)` must be built by a generated former.

A site with interface (index carriers, rely carriers, hole carrier, target
carrier) generates, at a profile `(α⃗, β⃗; γ)`, the formation rule

  `A⃗ : α⃗,   x⃗ : A⃗ ⊢ B⃗ : β⃗,   x⃗ : A⃗, y⃗ : B⃗ ⊢ C : γ   ⟹   ⟨K⟩ A⃗ B⃗ C : γ`

at the hole carrier. A variable whose slot is `□` ranges over types, so under
it the level `(carrier, ∗)` has a classifier, the variable itself. Formation
is therefore a hypothetical Horn problem (`HypotheticalPropositional`); the
classifiers obtained this way may mention index parameters, which the former
keeps outside its modality.

Two general facts follow:

* `no_star_without_seed`: the paper's completion (sort constants and modal
  formers, no constructor types) has no type at any `(X, ∗)` at its origin
  vertex. Every former concluding a `∗` level needs a `∗` target first. Types
  appear only through `□`-sorted bound slots (polymorphism) or through a seed,
  such as the native type of a nullary constructor.
* `lambda_cube_closed_types`: for the beta site of the lambda calculus the
  closed types exist exactly at the four vertices with polymorphism, which is
  the classical fact about pure type systems without base types.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.SortProfiles.Inhabitation

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.Framework.ModalHypercube (HSort)
open Mettapedia.Logic.LP.HypotheticalPropositional

/-- The derived `BEq` of sorts is lawful, so list membership of profiles is
decidable through it. -/
instance : LawfulBEq HSort where
  eq_of_beq := by intro first second; cases first <;> cases second <;> decide
  rfl := by intro sort; cases sort <;> decide

/-- A carrier with a sort. -/
abbrev Level := TypeExpr × HSort

/-- Carriers of a generated former's slots. -/
structure Interface where
  index : List TypeExpr
  rely : List TypeExpr
  hole : TypeExpr
  target : TypeExpr
  deriving DecidableEq, Repr

/-- A sort for each index slot, each rely slot and the target slot. -/
structure Profile where
  index : List HSort
  rely : List HSort
  target : HSort
  deriving DecidableEq, Repr

/-- A `□`-sorted variable is a type: under it, its carrier has a type. -/
def boundTypes (carriers : List TypeExpr) (sorts : List HSort) : Finset Level :=
  ((carriers.zip sorts).filter fun slot => slot.2 == .box).map (fun slot => (slot.1, .star))
    |>.toFinset

/-- The formation rule of a site at a profile. -/
def modalClause (interface : Interface) (profile : Profile) : Clause Level :=
  let indexTypes := boundTypes interface.index profile.index
  let relyTypes := boundTypes interface.rely profile.rely
  { premises :=
      (interface.index.zip profile.index).map (fun slot => (∅, slot)) ++
      (interface.rely.zip profile.rely).map (fun slot => (indexTypes, slot)) ++
      [(indexTypes ∪ relyTypes, (interface.target, profile.target))]
    conclusion := (interface.hole, profile.target) }

/-- The sort constant `∗^X : □^X`. -/
def sortClause (carrier : TypeExpr) : Clause Level := ⟨[], (carrier, .box)⟩

/-- The origin profile of an interface. -/
def originProfile (interface : Interface) : Profile :=
  ⟨interface.index.map fun _ => .star, interface.rely.map fun _ => .star, .star⟩

theorem mem_boundTypes {carriers : List TypeExpr} {sorts : List HSort} {level : Level}
    (member : level ∈ boundTypes carriers sorts) :
    ∃ carrier, (carrier, HSort.box) ∈ carriers.zip sorts ∧ level = (carrier, .star) := by
  simp only [boundTypes, List.mem_toFinset, List.mem_map, List.mem_filter] at member
  obtain ⟨⟨carrier, sort⟩, ⟨zipped, isBox⟩, rfl⟩ := member
  cases sort with
  | star => cases isBox
  | box => exact ⟨carrier, zipped, rfl⟩

/-- At the origin profile no slot binds a type. -/
theorem not_mem_boundTypes_origin (carriers : List TypeExpr) (level : Level) :
    level ∉ boundTypes carriers (carriers.map fun _ => .star) := by
  intro member
  obtain ⟨carrier, zipped, _⟩ := mem_boundTypes member
  have := (List.of_mem_zip zipped).2
  simp at this

/-- The target premise of a modal clause. -/
theorem target_premise_mem (interface : Interface) (profile : Profile) :
    (boundTypes interface.index profile.index ∪ boundTypes interface.rely profile.rely,
        (interface.target, profile.target)) ∈ (modalClause interface profile).premises := by
  simp [modalClause]

/-- A site with no index and no rely variable asks only for its target: it
forms a type from a type, and is not a seed. -/
theorem rely_free_premises {interface : Interface} (noIndex : interface.index = [])
    (noRely : interface.rely = []) (profile : Profile) :
    (modalClause interface profile).premises = [(∅, (interface.target, profile.target))] := by
  simp [modalClause, noIndex, noRely, boundTypes]

/-! ## No types without a seed -/

/-- The levels at sort `□`. -/
def BoxLevel (level : Level) : Prop := level.2 = .box

/-- A clause list is seedless if every clause concluding at a `∗` level has a
premise asking for a `∗` level under `□`-only hypotheses. -/
def Seedless (clauses : List (Clause Level)) : Prop :=
  ∀ clause ∈ clauses, clause.conclusion.2 = .star →
    ∃ premise ∈ clause.premises, premise.2.2 = .star ∧ ∀ level ∈ premise.1, BoxLevel level

/-- From `□`-only hypotheses, a seedless clause list derives only `□` levels. -/
theorem no_star_without_seed {clauses : List (Clause Level)} (seedless : Seedless clauses)
    {hypotheses : Finset Level} (boxes : ∀ level ∈ hypotheses, BoxLevel level) {level : Level}
    (derivation : Derives clauses hypotheses level) : BoxLevel level := by
  have notStar : ∀ level : Level, ¬ level.2 = .star ↔ BoxLevel level := by
    rintro ⟨carrier, sort⟩
    cases sort <;> simp [BoxLevel]
  apply (notStar level).mp
  refine not_derives_of_blocking (fun level : Level => level.2 = .star) ?_ ?_ derivation
  · intro clause member isStar
    obtain ⟨premise, premiseMember, premiseStar, premiseBoxes⟩ := seedless clause member isStar
    exact ⟨premise, premiseMember, premiseStar, fun level member => (notStar level).mpr (premiseBoxes level member)⟩
  · exact fun level member => (notStar level).mpr (boxes level member)

/-- Origin clauses of a set of interfaces, with the sort constants. -/
def originClauses (interfaces : List Interface) (carriers : List TypeExpr) : List (Clause Level) :=
  carriers.map sortClause ++ interfaces.map fun interface => modalClause interface (originProfile interface)

/-- The paper's completion at its origin vertex: no type at any level. -/
theorem origin_has_no_types (interfaces : List Interface) (carriers : List TypeExpr)
    (carrier : TypeExpr) : ¬ Derives (originClauses interfaces carriers) ∅ (carrier, .star) := by
  intro derivation
  have seedless : Seedless (originClauses interfaces carriers) := by
    intro clause member isStar
    rcases List.mem_append.mp member with fromSorts | fromModal
    · obtain ⟨carrier, _, rfl⟩ := List.mem_map.mp fromSorts
      cases isStar
    · obtain ⟨interface, _, rfl⟩ := List.mem_map.mp fromModal
      refine ⟨_, target_premise_mem interface (originProfile interface), isStar, ?_⟩
      intro level member
      rcases Finset.mem_union.mp member with fromIndex | fromRely
      · exact absurd fromIndex (not_mem_boundTypes_origin _ _)
      · exact absurd fromRely (not_mem_boundTypes_origin _ _)
  have := no_star_without_seed seedless (by simp) derivation
  cases this

/-! ## Interfaces of generated sites -/

open Mettapedia.OSLF.NativeTypes.Generation.Occurrences (Site ruleFree generate)
open Mettapedia.OSLF.MeTTaIL.DerivedContexts (OneHoleContext)

/-- The carrier a constructor declares at an argument position. -/
def argumentCarrier? (language : LanguageDef) (label : String) (position : Nat) :
    Option TypeExpr :=
  (language.terms.find? fun constructor => constructor.label == label).bind fun constructor =>
    (constructor.params[position]?).map TermParam.typeExpr

/-- The carrier of a binder body, given the carrier of the binder. -/
def bodyCarrier? : Option TypeExpr → Option TypeExpr
  | some (.arrow _ codomain) => some codomain
  | _ => none

/-- Whether a constructor is a bare collection of a given kind. -/
def bareCollectionOf (kind : CollType) (constructor : GrammarRule) : Bool :=
  match constructor.params with
  | [.simple _ (.collection actual _)] => actual == kind
  | _ => false

/-- The carrier of a collection's elements, given the collection's carrier. -/
def elementCarrier? (language : LanguageDef) : Option TypeExpr → Option TypeExpr
  | some (.collection _ element) => some element
  | some (.base category) =>
      (language.terms.find? fun constructor =>
        constructor.category == category &&
          match constructor.params with
          | [.simple _ (.collection _ _)] => true
          | _ => false).bind fun constructor =>
        match constructor.params with
        | [.simple _ (.collection _ element)] => some element
        | _ => none
  | _ => none

mutual
  /-- The carrier expected at each metavariable occurrence of a pattern. A rest
  variable ranges over the remainder of its collection, with that collection's
  carrier. -/
  def expectedCarriers (language : LanguageDef) (expected : Option TypeExpr) :
      Pattern → List (String × TypeExpr)
    | .fvar name => expected.toList.map fun carrier => (name, carrier)
    | .apply label arguments => argumentCarriers language label 0 arguments
    | .lambda _ body => expectedCarriers language (bodyCarrier? expected) body
    | .multiLambda _ _ body => expectedCarriers language (bodyCarrier? expected) body
    | .subst body replacement =>
        expectedCarriers language expected body ++ expectedCarriers language none replacement
    | .collection _ elements rest =>
        elementCarriers language (elementCarrier? language expected) elements ++
          rest.toList.flatMap fun name => expected.toList.map fun carrier => (name, carrier)
    | .bvar _ => []

  def argumentCarriers (language : LanguageDef) (label : String) (position : Nat) :
      List Pattern → List (String × TypeExpr)
    | [] => []
    | argument :: arguments =>
        expectedCarriers language (argumentCarrier? language label position) argument ++
          argumentCarriers language label (position + 1) arguments

  def elementCarriers (language : LanguageDef) (element : Option TypeExpr) :
      List Pattern → List (String × TypeExpr)
    | [] => []
    | pattern :: patterns =>
        expectedCarriers language element pattern ++ elementCarriers language element patterns
end

/-- The carrier of a rewrite's source: its head constructor's category. -/
def sourceCarrier? (language : LanguageDef) : Pattern → Option TypeExpr
  | .apply label _ => (language.terms.find? fun constructor => constructor.label == label).map
      fun constructor => .base constructor.category
  | .collection kind _ _ => (language.terms.find? (bareCollectionOf kind)).map
      fun constructor => .base constructor.category
  | _ => none

/-- The carrier expected at the hole of a context. -/
def holeCarrier? (language : LanguageDef) (expected : Option TypeExpr) :
    OneHoleContext → Option TypeExpr
  | .hole => expected
  | .apply label before inner _ =>
      holeCarrier? language (argumentCarrier? language label before.length) inner
  | .lambda _ inner => holeCarrier? language (bodyCarrier? expected) inner
  | .multiLambda _ _ inner => holeCarrier? language (bodyCarrier? expected) inner
  | .substBody inner _ => holeCarrier? language expected inner
  | .substReplacement _ _ => none
  | .collection _ _ inner _ _ => holeCarrier? language (elementCarrier? language expected) inner

/-- The declared carrier of a rule variable, or else the carrier its first
occurrence position expects. -/
def variableCarrier? (language : LanguageDef) (rule : RewriteRule) (name : String) :
    Option TypeExpr :=
  match ruleFree rule name with
  | some carrier => some carrier
  | none =>
      let source := sourceCarrier? language rule.left
      ((expectedCarriers language source rule.left ++ expectedCarriers language source rule.right).find?
        fun entry => entry.1 == name).map Prod.snd

/-- The carrier interface of a generated site: the carriers of its index and
rely variables, of its hole and of its source. `none` when one is unknown. -/
def interfaceOf? (language : LanguageDef) (site : Site) : Option Interface := do
  let source ← sourceCarrier? language site.rule.left
  let index ← (SiteInterfaces.indexNames site).mapM (variableCarrier? language site.rule)
  let rely ← site.relyNames.mapM (variableCarrier? language site.rule)
  let hole ← holeCarrier? language (some source) site.context
  pure ⟨index, rely, hole, source⟩

/-- The distinct interfaces of all generated sites of a presentation. -/
def interfaces (language : LanguageDef) : List Interface :=
  ((generate language).filterMap (interfaceOf? language)).dedup

theorem mapM_some_length {α β : Type} {read : α → Option β} :
    ∀ {items : List α} {values : List β}, items.mapM read = some values → values.length = items.length
  | [], values, mapped => by simp at mapped; subst mapped; rfl
  | item :: items, values, mapped => by
      simp only [List.mapM_cons] at mapped
      cases first : read item with
      | none => simp [first] at mapped
      | some value =>
          cases rest : items.mapM read with
          | none => simp [first, rest] at mapped
          | some others =>
              simp [first, rest] at mapped
              subst mapped
              simp [mapM_some_length rest]

/-- An interface has one carrier per index variable and per rely variable. -/
theorem interfaceOf?_lengths {language : LanguageDef} {site : Site} {interface : Interface}
    (read : interfaceOf? language site = some interface) :
    interface.index.length = (SiteInterfaces.indexNames site).length ∧
      interface.rely.length = site.relyNames.length := by
  unfold interfaceOf? at read
  cases source : sourceCarrier? language site.rule.left with
  | none => simp [source] at read
  | some source' =>
      cases index : (SiteInterfaces.indexNames site).mapM (variableCarrier? language site.rule) with
      | none => simp [source, index] at read
      | some index' =>
          cases rely : site.relyNames.mapM (variableCarrier? language site.rule) with
          | none => simp [source, index, rely] at read
          | some rely' =>
              cases hole : holeCarrier? language (some source') site.context with
              | none => simp [source, index, rely, hole] at read
              | some hole' =>
                  simp [source, index, rely, hole] at read
                  subst read
                  exact ⟨mapM_some_length index, mapM_some_length rely⟩

/-- The interface fixes the site's slot count. -/
theorem interfaceOf?_slotCount {language : LanguageDef} {site : Site} {interface : Interface}
    (read : interfaceOf? language site = some interface) :
    SiteInterfaces.slotCount site = interface.index.length + interface.rely.length + 1 := by
  obtain ⟨index, rely⟩ := interfaceOf?_lengths read
  rw [SiteInterfaces.slotCount, index, rely]

/-- Every list of sorts of a given length. -/
def sortLists : Nat → List (List HSort)
  | 0 => [[]]
  | count + 1 => (sortLists count).flatMap fun rest => [.star :: rest, .box :: rest]

theorem sortLists_length (count : Nat) : (sortLists count).length = 2 ^ count := by
  induction count with
  | zero => rfl
  | succ count ih =>
      rw [sortLists, List.length_flatMap]
      simp [ih, pow_succ, mul_comm]

/-- Every list of sorts is listed at its length. -/
theorem mem_sortLists (sorts : List HSort) : sorts ∈ sortLists sorts.length := by
  induction sorts with
  | nil => simp [sortLists]
  | cons head tail ih =>
      simp only [List.length_cons, sortLists, List.mem_flatMap]
      exact ⟨tail, ih, by cases head <;> simp⟩

/-- Every profile of an interface. -/
def profiles (interface : Interface) : List Profile :=
  (sortLists interface.index.length).flatMap fun index =>
    (sortLists interface.rely.length).flatMap fun rely => [⟨index, rely, .star⟩, ⟨index, rely, .box⟩]

/-- The top vertex of the paper's completion: every profile of every site. -/
def fullClauses (interfaces : List Interface) (carriers : List TypeExpr) : List (Clause Level) :=
  carriers.map sortClause ++ interfaces.flatMap fun interface => (profiles interface).map (modalClause interface)

/-- The carrier a constructor parameter classifies, or `none` for a collection,
whose empty value needs no classifier. -/
def parameterCarrier : TermParam → Option TypeExpr
  | .simple _ (.collection _ _) => none
  | .simple _ type => some type
  | .abstractionNamed _ _ (.arrow _ codomain) => some codomain
  | .abstractionNamed _ _ type => some type
  | .multiAbstractionNamed _ _ (.arrow _ codomain) => some codomain
  | .multiAbstractionNamed _ _ type => some type

/-- The native constructor type at the origin: the type of `c`-terms whose
components have the given types. A nullary constructor is a seed. -/
def constructorClause (rule : GrammarRule) : Clause Level :=
  ⟨rule.params.filterMap fun param => (parameterCarrier param).map fun carrier => (∅, (carrier, .star)),
    (.base rule.category, .star)⟩

/-- The carriers declared by a presentation. -/
def carriers (language : LanguageDef) : List TypeExpr :=
  language.types.map fun type => .base type.name

/-- The carriers that have a closed type under a clause list. -/
def typedCarriers (clauses : List (Clause Level)) (carriers : List TypeExpr) : List TypeExpr :=
  carriers.filter fun carrier =>
    decide ((carrier, HSort.star) ∈ closure clauses (fuelFor clauses) ∅)

/-- The origin is contained in the top vertex. -/
theorem origin_subset_full (interfaces : List Interface) (carriers : List TypeExpr) :
    originClauses interfaces carriers ⊆ fullClauses interfaces carriers := by
  intro clause member
  rcases List.mem_append.mp member with fromSorts | fromModal
  · exact List.mem_append_left _ fromSorts
  · obtain ⟨interface, interfaceMember, rfl⟩ := List.mem_map.mp fromModal
    refine List.mem_append_right _ (List.mem_flatMap.mpr ⟨interface, interfaceMember, ?_⟩)
    refine List.mem_map.mpr ⟨originProfile interface, ?_, rfl⟩
    simp only [profiles, originProfile, List.mem_flatMap]
    refine ⟨interface.index.map fun _ => HSort.star, ?_,
      interface.rely.map fun _ => HSort.star, ?_, by simp⟩
    · simpa using mem_sortLists (interface.index.map fun _ => HSort.star)
    · simpa using mem_sortLists (interface.rely.map fun _ => HSort.star)

/-! ## The top vertex reduces to one clause per interface and target sort -/

/-- Every carrier of a slot, hole or target, beside the declared ones. Each has
its sort constants. -/
def relevantCarriers (interfaces : List Interface) (declared : List TypeExpr) : List TypeExpr :=
  (declared ++ interfaces.flatMap fun interface =>
    interface.index ++ interface.rely ++ [interface.hole, interface.target]).dedup

theorem slot_mem_relevant {interfaces : List Interface} {interface : Interface}
    (member : interface ∈ interfaces) (declared : List TypeExpr) {carrier : TypeExpr}
    (slot : carrier ∈ interface.index ∨ carrier ∈ interface.rely) :
    carrier ∈ relevantCarriers interfaces declared := by
  apply List.mem_dedup.mpr
  refine List.mem_append_right _ (List.mem_flatMap.mpr ⟨interface, member, ?_⟩)
  rcases slot with inIndex | inRely <;> simp [*]

/-- Every bound slot at `□`: the strongest profile for a target sort. -/
def topProfile (interface : Interface) (target : HSort) : Profile :=
  ⟨interface.index.map fun _ => .box, interface.rely.map fun _ => .box, target⟩

/-- The top vertex, by its strongest profiles. -/
def topClauses (interfaces : List Interface) (carriers : List TypeExpr) : List (Clause Level) :=
  carriers.map sortClause ++ interfaces.flatMap fun interface =>
    [modalClause interface (topProfile interface .star), modalClause interface (topProfile interface .box)]

theorem mem_profiles_iff {interface : Interface} {profile : Profile} :
    profile ∈ profiles interface ↔
      profile.index ∈ sortLists interface.index.length ∧
      profile.rely ∈ sortLists interface.rely.length := by
  rcases profile with ⟨index, rely, target⟩
  simp only [profiles, List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false]
  constructor
  · rintro ⟨index', member, rely', relyMember, equal⟩
    rcases equal with equal | equal <;> cases equal <;> exact ⟨member, relyMember⟩
  · rintro ⟨member, relyMember⟩
    exact ⟨index, member, rely, relyMember, by cases target <;> simp⟩

theorem length_of_mem_sortLists : ∀ {count : Nat} {sorts : List HSort},
    sorts ∈ sortLists count → sorts.length = count
  | 0, sorts, member => by simp [sortLists] at member; simp [member]
  | count + 1, sorts, member => by
      simp only [sortLists, List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false] at member
      obtain ⟨rest, restMember, equal | equal⟩ := member <;>
        (subst equal; simp [length_of_mem_sortLists restMember])

theorem topProfile_mem (interface : Interface) (target : HSort) :
    topProfile interface target ∈ profiles interface := by
  rw [mem_profiles_iff]
  have index := mem_sortLists (interface.index.map fun _ => HSort.box)
  have rely := mem_sortLists (interface.rely.map fun _ => HSort.box)
  rw [List.length_map] at index rely
  exact ⟨index, rely⟩

theorem mem_zip_map_box {carriers : List TypeExpr} {carrier : TypeExpr} (member : carrier ∈ carriers) :
    (carrier, HSort.box) ∈ carriers.zip (carriers.map fun _ => HSort.box) := by
  induction carriers with
  | nil => cases member
  | cons head tail ih =>
      rcases List.mem_cons.mp member with rfl | inTail
      · simp
      · exact List.mem_cons_of_mem _ (ih inTail)

/-- All-box slots bind every slot carrier as a type. -/
theorem boundTypes_subset_box (carriers : List TypeExpr) (sorts : List HSort) :
    boundTypes carriers sorts ⊆ boundTypes carriers (carriers.map fun _ => .box) := by
  intro level member
  obtain ⟨carrier, zipped, rfl⟩ := mem_boundTypes member
  simp only [boundTypes, List.mem_toFinset, List.mem_map, List.mem_filter]
  exact ⟨(carrier, .box), ⟨mem_zip_map_box (List.of_mem_zip zipped).1, rfl⟩, rfl⟩

/-- Sort constants of the listed carriers hold under any hypotheses. -/
theorem sort_axiom {clauses : List (Clause Level)} {carrier : TypeExpr}
    (member : sortClause carrier ∈ clauses) (hypotheses : Finset Level) :
    Derives clauses hypotheses (carrier, .box) :=
  .clause member (by simp [sortClause])

/-- **The top vertex is its strongest profiles.** When every slot carrier has
its sort constants, the clauses of all profiles derive exactly what the
all-`□` profiles derive. -/
theorem full_iff_top (interfaces : List Interface) (carriers : List TypeExpr)
    (covered : ∀ interface ∈ interfaces, ∀ carrier,
      carrier ∈ interface.index ∨ carrier ∈ interface.rely → carrier ∈ carriers)
    (extra : List (Clause Level)) (hypotheses : Finset Level) (level : Level) :
    Derives (fullClauses interfaces carriers ++ extra) hypotheses level ↔
      Derives (topClauses interfaces carriers ++ extra) hypotheses level := by
  have sortMember : ∀ carrier ∈ carriers,
      sortClause carrier ∈ topClauses interfaces carriers ++ extra := fun carrier member =>
    List.mem_append_left _ (List.mem_append_left _ (List.mem_map.mpr ⟨carrier, member, rfl⟩))
  constructor
  · apply Derives.of_dominates
    intro clause member
    have self : clause ∈ topClauses interfaces carriers ++ extra → ∃ witness ∈ topClauses interfaces carriers ++ extra,
        witness.conclusion = clause.conclusion ∧ ∀ premise ∈ witness.premises,
          (∀ hypotheses, Derives (topClauses interfaces carriers ++ extra) hypotheses premise.2) ∨
          ∃ original ∈ clause.premises, original.2 = premise.2 ∧ original.1 ⊆ premise.1 :=
      fun inTop => ⟨clause, inTop, rfl, fun premise premiseMember =>
        Or.inr ⟨premise, premiseMember, rfl, subset_refl _⟩⟩
    rcases List.mem_append.mp member with inFull | inExtra
    · rcases List.mem_append.mp inFull with fromSorts | fromModal
      · exact self (List.mem_append_left _ (List.mem_append_left _ fromSorts))
      · obtain ⟨interface, interfaceMember, profileMember⟩ := List.mem_flatMap.mp fromModal
        obtain ⟨profile, profileIn, rfl⟩ := List.mem_map.mp profileMember
        have witnessMember : modalClause interface (topProfile interface profile.target) ∈
            topClauses interfaces carriers ++ extra := by
          refine List.mem_append_left _ (List.mem_append_right _
            (List.mem_flatMap.mpr ⟨interface, interfaceMember, ?_⟩))
          cases profile.target <;> simp
        refine ⟨_, witnessMember, rfl, fun premise premiseMember => ?_⟩
        simp only [modalClause, topProfile, List.mem_append, List.mem_map, List.mem_cons,
          List.not_mem_nil, or_false] at premiseMember
        rcases premiseMember with (⟨slot, zipped, rfl⟩ | ⟨slot, zipped, rfl⟩) | rfl
        · left
          have := List.of_mem_zip zipped
          simp at this
          obtain ⟨inCarriers, isBox⟩ := this
          rw [show slot = (slot.1, HSort.box) from Prod.ext rfl isBox.2]
          exact fun hypotheses => sort_axiom
            (sortMember _ (covered interface interfaceMember _ (Or.inl inCarriers))) hypotheses
        · left
          have := List.of_mem_zip zipped
          simp at this
          obtain ⟨inCarriers, isBox⟩ := this
          rw [show slot = (slot.1, HSort.box) from Prod.ext rfl isBox.2]
          exact fun hypotheses => sort_axiom
            (sortMember _ (covered interface interfaceMember _ (Or.inr inCarriers))) hypotheses
        · right
          refine ⟨_, target_premise_mem interface profile, rfl, ?_⟩
          exact Finset.union_subset_union (boundTypes_subset_box _ _) (boundTypes_subset_box _ _)
    · exact self (List.mem_append_right _ inExtra)
  · apply Derives.mono_clauses
    intro clause member
    rcases List.mem_append.mp member with inTop | inExtra
    · rcases List.mem_append.mp inTop with fromSorts | fromModal
      · exact List.mem_append_left _ (List.mem_append_left _ fromSorts)
      · obtain ⟨interface, interfaceMember, topMember⟩ := List.mem_flatMap.mp fromModal
        refine List.mem_append_left _ (List.mem_append_right _
          (List.mem_flatMap.mpr ⟨interface, interfaceMember, ?_⟩))
        simp only [List.mem_cons, List.not_mem_nil, or_false] at topMember
        rcases topMember with rfl | rfl
        · exact List.mem_map.mpr ⟨_, topProfile_mem interface .star, rfl⟩
        · exact List.mem_map.mpr ⟨_, topProfile_mem interface .box, rfl⟩
    · exact List.mem_append_right _ inExtra

/-! ## Targets that no slot binds -/

/-- The target carriers of a set of interfaces. -/
def targets (interfaces : List Interface) : List TypeExpr := interfaces.map Interface.target

/-- No slot of any interface ranges over a target carrier. -/
def TargetsUnbound (interfaces : List Interface) : Prop :=
  ∀ interface ∈ interfaces, ∀ carrier ∈ interface.index ++ interface.rely,
    carrier ∉ targets interfaces

instance (interfaces : List Interface) : Decidable (TargetsUnbound interfaces) := by
  unfold TargetsUnbound; infer_instance

theorem mem_boundTypes_carrier {carriers : List TypeExpr} {sorts : List HSort} {level : Level}
    (member : level ∈ boundTypes carriers sorts) : level.1 ∈ carriers ∧ level.2 = .star := by
  obtain ⟨carrier, zipped, rfl⟩ := mem_boundTypes member
  exact ⟨(List.of_mem_zip zipped).1, rfl⟩

/-- **When no slot ranges over a target carrier, the top vertex types
nothing.** A `∗` level at a hole needs a `∗` target under hypotheses that are
types of slot carriers; no target type is derivable under those. -/
theorem top_untyped_of_unbound_targets (interfaces : List Interface) (carriers : List TypeExpr)
    (unbound : TargetsUnbound interfaces) (carrier : TypeExpr) :
    ¬ Derives (topClauses interfaces carriers) ∅ (carrier, .star) := by
  let blocked : Level → Prop := fun level => level.1 ∈ targets interfaces ∧ level.2 = .star
  have slotTypesUnblocked : ∀ interface ∈ interfaces, ∀ level ∈
      boundTypes interface.index (interface.index.map fun _ => .box) ∪
        boundTypes interface.rely (interface.rely.map fun _ => .box), ¬ blocked level := by
    intro interface member level levelMember isBlocked
    rcases Finset.mem_union.mp levelMember with fromIndex | fromRely
    · exact unbound interface member level.1
        (List.mem_append_left _ (mem_boundTypes_carrier fromIndex).1) isBlocked.1
    · exact unbound interface member level.1
        (List.mem_append_right _ (mem_boundTypes_carrier fromRely).1) isBlocked.1
  have targetPremise : ∀ interface ∈ interfaces,
      (boundTypes interface.index (interface.index.map fun _ => .box) ∪
          boundTypes interface.rely (interface.rely.map fun _ => .box),
        (interface.target, HSort.star)) ∈ (modalClause interface (topProfile interface .star)).premises :=
    fun interface _ => target_premise_mem interface (topProfile interface .star)
  have noTarget : ∀ hypotheses : Finset Level, (∀ level ∈ hypotheses, ¬ blocked level) →
      ∀ level, Derives (topClauses interfaces carriers) hypotheses level → ¬ blocked level := by
    intro hypotheses unblocked level derivation
    refine not_derives_of_blocking blocked ?_ unblocked derivation
    intro clause member isBlocked
    rcases List.mem_append.mp member with fromSorts | fromModal
    · obtain ⟨_, _, rfl⟩ := List.mem_map.mp fromSorts
      exact absurd isBlocked.2 (by simp [sortClause])
    · obtain ⟨interface, interfaceMember, topMember⟩ := List.mem_flatMap.mp fromModal
      simp only [List.mem_cons, List.not_mem_nil, or_false] at topMember
      rcases topMember with rfl | rfl
      · exact ⟨_, targetPremise interface interfaceMember,
          ⟨List.mem_map_of_mem interfaceMember, rfl⟩, slotTypesUnblocked interface interfaceMember⟩
      · exact absurd isBlocked.2 (by simp [modalClause, topProfile])
  have noStar : ∀ level, Derives (topClauses interfaces carriers) ∅ level → level.2 ≠ .star := by
    intro level derivation isStar
    cases derivation with
    | hyp member => simp at member
    | @clause _ clause member premises =>
        rcases List.mem_append.mp member with fromSorts | fromModal
        · obtain ⟨_, _, rfl⟩ := List.mem_map.mp fromSorts
          simp [sortClause] at isStar
        · obtain ⟨interface, interfaceMember, topMember⟩ := List.mem_flatMap.mp fromModal
          simp only [List.mem_cons, List.not_mem_nil, or_false] at topMember
          rcases topMember with rfl | rfl
          · have derived := premises _ (targetPremise interface interfaceMember)
            rw [Finset.union_empty] at derived
            exact noTarget _ (slotTypesUnblocked interface interfaceMember) _ derived
              ⟨List.mem_map_of_mem interfaceMember, rfl⟩
          · simp [modalClause, topProfile] at isStar
  exact fun derivation => noStar _ derivation rfl

/-- **A slot over the target carrier types the hole.** Bound at `□`, that slot
is a type of the target carrier, which can serve as the target. -/
theorem top_types_hole_of_bound_target {interfaces : List Interface} {carriers : List TypeExpr}
    {interface : Interface} (member : interface ∈ interfaces)
    (covered : ∀ carrier ∈ interface.index ++ interface.rely, carrier ∈ carriers)
    (bound : interface.target ∈ interface.index ++ interface.rely) :
    Derives (topClauses interfaces carriers) ∅ (interface.hole, .star) := by
  have clauseMember : modalClause interface (topProfile interface .star) ∈ topClauses interfaces carriers :=
    List.mem_append_right _ (List.mem_flatMap.mpr ⟨interface, member, by simp⟩)
  refine .clause clauseMember fun premise premiseMember => ?_
  simp only [modalClause, topProfile, List.mem_append, List.mem_map, List.mem_cons,
    List.not_mem_nil, or_false] at premiseMember
  rcases premiseMember with (⟨slot, zipped, rfl⟩ | ⟨slot, zipped, rfl⟩) | rfl
  · have := List.of_mem_zip zipped
    simp at this
    obtain ⟨inCarriers, isBox⟩ := this
    rw [show slot = (slot.1, HSort.box) from Prod.ext rfl isBox.2]
    exact sort_axiom (List.mem_append_left _ (List.mem_map.mpr
      ⟨slot.1, covered _ (List.mem_append_left _ inCarriers), rfl⟩)) _
  · have := List.of_mem_zip zipped
    simp at this
    obtain ⟨inCarriers, isBox⟩ := this
    rw [show slot = (slot.1, HSort.box) from Prod.ext rfl isBox.2]
    exact sort_axiom (List.mem_append_left _ (List.mem_map.mpr
      ⟨slot.1, covered _ (List.mem_append_right _ inCarriers), rfl⟩)) _
  · apply Derives.hyp
    apply Finset.mem_union_left
    rcases List.mem_append.mp bound with inIndex | inRely
    · exact Finset.mem_union_left _ (by
        simp only [boundTypes, List.mem_toFinset, List.mem_map, List.mem_filter]
        exact ⟨(interface.target, .box), ⟨mem_zip_map_box inIndex, rfl⟩, rfl⟩)
    · exact Finset.mem_union_right _ (by
        simp only [boundTypes, List.mem_toFinset, List.mem_map, List.mem_filter]
        exact ⟨(interface.target, .box), ⟨mem_zip_map_box inRely, rfl⟩, rfl⟩)

/-! ## Regimes for a presentation -/

/-- The paper's completion at its origin: sort constants and modal formers. -/
def paperOrigin (language : LanguageDef) : List (Clause Level) :=
  originClauses (interfaces language) (relevantCarriers (interfaces language) (carriers language))

/-- The paper's completion at its top vertex, by its strongest profiles. -/
def paperTop (language : LanguageDef) : List (Clause Level) :=
  topClauses (interfaces language) (relevantCarriers (interfaces language) (carriers language))

/-- Native constructor types beside a regime. -/
def seeded (language : LanguageDef) (regime : List (Clause Level)) : List (Clause Level) :=
  regime ++ language.terms.map constructorClause

/-- The paper's top vertex of a presentation whose targets no slot binds
types nothing. -/
theorem paperTop_untyped (language : LanguageDef)
    (unbound : TargetsUnbound (interfaces language)) (carrier : TypeExpr) :
    ¬ Derives (paperTop language) ∅ (carrier, .star) :=
  top_untyped_of_unbound_targets _ _ unbound carrier

/-- A hole whose interface has a slot over its target carrier is typed at the
paper's top vertex. -/
theorem paperTop_types_hole (language : LanguageDef) {interface : Interface}
    (member : interface ∈ interfaces language)
    (bound : interface.target ∈ interface.index ++ interface.rely) :
    Derives (paperTop language) ∅ (interface.hole, .star) :=
  top_types_hole_of_bound_target member
    (fun _ slot => slot_mem_relevant member _ (List.mem_append.mp slot)) bound

/-- The top vertex of a presentation is decided by its strongest profiles. -/
theorem paperTop_exact (language : LanguageDef) (extra : List (Clause Level))
    (hypotheses : Finset Level) (level : Level) :
    Derives (fullClauses (interfaces language)
        (relevantCarriers (interfaces language) (carriers language)) ++ extra) hypotheses level ↔
      Derives (paperTop language ++ extra) hypotheses level :=
  full_iff_top _ _ (fun _ member _ slot => slot_mem_relevant member _ slot) extra hypotheses level

/-- The seeded origin is contained in the seeded top. -/
theorem seededOrigin_le_seededTop (language : LanguageDef) {hypotheses : Finset Level} {level : Level}
    (derivation : Derives (seeded language (paperOrigin language)) hypotheses level) :
    Derives (seeded language (paperTop language)) hypotheses level := by
  apply (paperTop_exact language _ hypotheses level).mp
  apply Derives.mono_clauses _ derivation
  intro clause member
  rcases List.mem_append.mp member with fromOrigin | fromSeeds
  · exact List.mem_append_left _ (origin_subset_full _ _ fromOrigin)
  · exact List.mem_append_right _ fromSeeds

/-! ## Reading the regimes -/

/-- The carriers that have a closed type are those whose `∗` level is derivable. -/
theorem mem_typedCarriers {clauses : List (Clause Level)} {carriers : List TypeExpr}
    {carrier : TypeExpr} :
    carrier ∈ typedCarriers clauses carriers ↔
      carrier ∈ carriers ∧ Derives clauses ∅ (carrier, .star) := by
  simp [typedCarriers, derives_iff]

/-! ## The lambda cube -/

/-- The interface of a beta site over a carrier: no index, one argument as
rely, the abstraction in the hole, a term as target. -/
def betaInterface (carrier : TypeExpr) : Interface := ⟨[], [carrier], carrier, carrier⟩

/-- A product profile `(domain, codomain)` at a beta site. -/
def productProfile (domain codomain : HSort) : Profile := ⟨[], [domain], codomain⟩

/-- The completion of one beta site at a signature choice of product profiles. -/
def productClauses (carrier : TypeExpr) (choice : List (HSort × HSort)) : List (Clause Level) :=
  sortClause carrier ::
    choice.map fun profile => modalClause (betaInterface carrier) (productProfile profile.1 profile.2)

/-- The four product profiles. -/
def productProfiles : List (HSort × HSort) := [(.star, .star), (.star, .box), (.box, .star), (.box, .box)]

/-- **The lambda cube.** At the beta site of the lambda calculus closed types
exist exactly at the vertices with polymorphism `(□, ∗)`. All sixteen choices
of product profiles are checked, the eight based ones among them. -/
theorem lambda_cube_closed_types :
    ∀ choice ∈ productProfiles.sublists,
      (Derives (productClauses (.base "Term") choice) ∅ (.base "Term", .star) ↔
        (.box, .star) ∈ choice) := by
  decide +kernel

/-- Kinds exist at every vertex: the sort constant. -/
theorem beta_site_kinds (carrier : TypeExpr) (choice : List (HSort × HSort)) :
    Derives (productClauses carrier choice) ∅ (carrier, .box) :=
  .clause List.mem_cons_self (by simp [sortClause])

end Mettapedia.OSLF.NativeTypes.SortProfiles.Inhabitation
