import Mettapedia.GSLT.Contexts.ConstantMap
import Mettapedia.GSLT.Contexts.TransitionProfile
import Mettapedia.Logic.HostingStyles.ContextShape

/-!
# The readings of a theory: how often a context may use a hole

A theory presented through its contexts fixes how a context uses its holes.
The contexts of a presented language use each hole once; the contexts of a
typed λ-calculus use a hole any number of times.  This module builds, from one
theory and a class of its interfaces, the theory in which the holes of the
*declared* interfaces may be used any number of times and every other hole is
used once (`ContextTheory.regionReading`).  Its two ends are

* the **linear reading** (`linearReading`): no interface is declared;
* the **cartesian reading** (`cartesianReading`): every interface is declared.

A context of a reading is what a context of the theory does to the terms that
fill it, once its holes are placed at the holes of the reading
(`RegionContext`).  Several holes placed at one hole is copying; no hole
placed at a hole is discarding.  Two clauses say what a reading admits
(`Admits`):

* a hole whose interface is not declared receives exactly one hole
  (`Admits.once`);
* a context whose result is of a declared interface has holes of declared
  interfaces only (`Admits.promotes`).  Without this clause plugging would
  copy what has to be used once: a context plugged into a hole that is used
  twice is used twice, with all its holes.

Contexts are compared by what they do, which is how the laws of a theory and
the conditions on maps of theories read them; the laws of a `ContextTheory`
then hold for every class of declared interfaces, and the content of the
construction is that the contexts are closed under the hole, plugging,
renaming and the terms (`RegionContext.identity`, `plug`, `rename`,
`constant`).

## What is proved

* The linear reading is the theory: the identity on terms goes both ways and
  each way is hosting and exhausting (`toLinearReading_hosting`,
  `toLinearReading_exhausting`, `ofLinearReading_hosting`,
  `ofLinearReading_exhausting`).
* The identity on terms goes from the theory into its cartesian reading and
  from every reading into the cartesian one; both maps are hosting
  (`toCartesianReading_hosting`, `regionToCartesian_hosting`).  The first is
  exhausting exactly when the theory already has every context with its holes
  placed anew (`toCartesianReading_exhausting_iff`), and then the theory
  discards at every interface (`discards_of_toCartesianReading_exhausting`).
  It is exhausting for a syntax with named holes and for the framework with
  rules as constants (`holeSyntax_toCartesianReading_exhausting`,
  `frameworkTheory_toCartesianReading_exhausting`).
* The identity goes from the theory into a reading with regions exactly under
  promotion (`Promotes`): it is a map when the theory promotes the declared
  class (`toRegionReading`), and a map that is the identity on interfaces
  forces promotion (`promotes_of_identity`).  Every map into a reading carries
  promotion back: when it sends the result of a context to a declared
  interface, it sends the holes of that context there too
  (`declared_of_contextMap`).
* A reading discards at an interface exactly when the interface is declared or
  the theory discards there (`regionReading_discards_iff`), and the same for
  copying (`regionReading_copies_iff`).  At a declared interface every context
  of two holes has its diagonal (`regionReading_diagonal`).
* A context of a reading all of whose holes are of interfaces that are not
  declared is a context of the theory (`RegionContext.exists_context`).
* Contexts over holes of declared interfaces compose over shared holes
  (`RegionContext.substitute`) and have the projections
  (`RegionContext.project`).

* **Every theory maps into every reading that declares an interface with a
  term** (`intoRegionReading`), in particular into the cartesian reading of
  every theory with a term (`intoCartesianReading`): the constant map, every
  context sent to the context that discards all its holes
  (`discardingConstant`).  It is not hosting as soon as the source has two
  terms that are apart (`intoCartesianReading_not_hosting`).  So for such a
  reading the question is never whether a map exists.

`ContextTheory.Copies` follows from `ContextTheory.Discards`
(`copies_of_discards`): a context that returns its first hole is a context of
two holes that the hole itself copies.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT

universe u

namespace ContextTheory

variable (theory : ContextTheory.{u})

/-- **A theory that discards at an interface copies there**: the context that
returns its first hole, filled twice with one term, is that term. -/
theorem copies_of_discards {interface : theory.Interface} (discards : theory.Discards interface) :
    theory.Copies interface := by
  obtain ⟨first, returns⟩ := discards
  refine ⟨first, theory.identity interface, fun term => ?_⟩
  rw [theory.apply_identity]
  exact (theory.equations interface).iseqv.symm (returns fun _ => term)

variable (declared : theory.Interface → Prop)

/-- **What a reading admits**, of a placement of the holes of a context at
the holes of the reading.  A hole of an interface that is not declared
receives exactly one hole; and a context whose result is of a declared
interface has holes of declared interfaces only. -/
structure Admits {positions arity : Type} (holes : arity → theory.Interface)
    (result : theory.Interface) (place : positions → arity) : Prop where
  /-- What is not declared is used once. -/
  once : ∀ index, ¬ declared (holes index) → ∃! position, place position = index
  /-- What may be copied contains nothing that has to be used once. -/
  promotes : declared result → ∀ index, declared (holes index)

/-- **Positive**, for `Admits`: every hole placed at itself, when the result
is not of a declared interface. -/
theorem admits_id {arity : Type} (holes : arity → theory.Interface) (result : theory.Interface)
    (linear : ¬ declared result) : theory.Admits declared holes result id :=
  ⟨fun index _ => ⟨index, rfl, fun _ same => same⟩, fun free => (linear free).elim⟩

/-- **Negative**, for `Admits`: two holes placed at one hole of an interface
that is not declared. -/
theorem not_admits_twice (interface : theory.Interface) (linear : ¬ declared interface) :
    ¬ theory.Admits declared (fun _ : Unit => interface) interface (fun _ : Bool => ()) := by
  intro admits
  obtain ⟨position, -, only⟩ := admits.once () linear
  exact absurd ((only true rfl).trans (only false rfl).symm) (by decide)

/-- **A context of a reading**: what some context of the theory does to the
terms that fill it, its holes placed at the holes of the reading as the
reading admits. -/
structure RegionContext {arity : Type} (holes : arity → theory.Interface)
    (result : theory.Interface) : Type u where
  /-- What the context does to the terms that fill its holes. -/
  act : ((index : arity) → theory.Term (holes index)) → theory.Term result
  /-- A context of the theory does it. -/
  realized : ∃ (positions : Type) (place : positions → arity)
      (inner : theory.Context (fun position => holes (place position)) result),
      theory.Admits declared holes result place ∧
        ∀ filling, act filling = theory.fill inner fun position => filling (place position)

namespace RegionContext

variable {theory declared}

/-- A context of the theory, as a context of a reading: each hole at itself.
The context has to respect promotion. -/
def ofContext {arity : Type} {holes : arity → theory.Interface} {result : theory.Interface}
    (context : theory.Context holes result)
    (promotes : declared result → ∀ index, declared (holes index)) :
    theory.RegionContext declared holes result where
  act := theory.fill context
  realized := ⟨arity, id, context,
    ⟨fun index _ => ⟨index, rfl, fun _ same => same⟩, promotes⟩, fun _ => rfl⟩

/-- Filling respects the static equivalence. -/
theorem act_resp {arity : Type} {holes : arity → theory.Interface} {result : theory.Interface}
    (context : theory.RegionContext declared holes result)
    {first second : (index : arity) → theory.Term (holes index)}
    (equivalent : ∀ index, (theory.equations (holes index)).r (first index) (second index)) :
    (theory.equations result).r (context.act first) (context.act second) := by
  obtain ⟨positions, place, inner, -, acts⟩ := context.realized
  rw [acts first, acts second]
  exact theory.fill_resp inner fun position => equivalent (place position)

/-- The context that is a hole. -/
def identity (interface : theory.Interface) :
    theory.RegionContext declared (fun _ : Unit => interface) interface where
  act := fun filling => filling ()
  realized := ⟨Unit, id, theory.identity interface,
    ⟨fun index _ => ⟨index, rfl, fun _ same => same⟩, fun free _ => free⟩,
    fun filling => (theory.fill_identity interface filling).symm⟩

/-- A term, as a context with no hole. -/
def constant {holes : Empty → theory.Interface} {result : theory.Interface}
    (term : theory.Term result) : theory.RegionContext declared holes result where
  act := fun _ => term
  realized := ⟨Empty, id, theory.constant term,
    ⟨fun index => index.elim, fun _ index => index.elim⟩,
    fun _ => (theory.fill_constant term _).symm⟩

/-- **Plug a family of contexts into the holes of a context.**  A hole of the
outer context that is used several times uses the context plugged into it
several times; promotion is what keeps the holes of that context free to be
used so. -/
def plug {arity : Type} {holes : arity → theory.Interface} {result : theory.Interface}
    {innerArity : arity → Type} {innerHoles : (index : arity) → innerArity index → theory.Interface}
    (context : theory.RegionContext declared holes result)
    (inner : (index : arity) → theory.RegionContext declared (innerHoles index) (holes index)) :
    theory.RegionContext declared
      (fun position : Σ index, innerArity index => innerHoles position.1 position.2) result where
  act := fun filling => context.act fun index => (inner index).act fun leaf => filling ⟨index, leaf⟩
  realized := by
    obtain ⟨positions, place, outer, admits, acts⟩ := context.realized
    choose innerPositions innerPlace innerContext innerAdmits innerActs using
      fun index => (inner index).realized
    refine ⟨Σ position : positions, innerPositions (place position),
      fun leaf => ⟨place leaf.1, innerPlace (place leaf.1) leaf.2⟩,
      theory.plug (innerArity := fun position => innerPositions (place position))
        (innerHoles := fun position leaf =>
          innerHoles (place position) (innerPlace (place position) leaf))
        outer fun position => innerContext (place position), ⟨?_, ?_⟩, ?_⟩
    · rintro ⟨index, slot⟩ linear
      have outerLinear : ¬ declared (holes index) := fun free =>
        linear ((innerAdmits index).promotes free slot)
      obtain ⟨position, placed, onlyPosition⟩ := admits.once index outerLinear
      subst placed
      obtain ⟨inside, insidePlaced, onlyInside⟩ := (innerAdmits (place position)).once slot linear
      subst insidePlaced
      refine ⟨⟨position, inside⟩, rfl, ?_⟩
      rintro ⟨otherPosition, otherInside⟩ same
      obtain rfl := onlyPosition otherPosition (congrArg Sigma.fst same)
      obtain rfl := onlyInside otherInside (eq_of_heq (Sigma.mk.inj same).2)
      rfl
    · rintro free ⟨index, slot⟩
      exact (innerAdmits index).promotes (admits.promotes free index) slot
    · intro filling
      rw [theory.fill_plug, acts]
      congr 1
      funext position
      exact innerActs (place position) _

/-- **Move the holes of a context along a map that the reading admits**: a
hole of an interface that is not declared is the image of exactly one hole.
Two holes moved to one hole are copied; a hole that is no image is
discarded. -/
def rename {arity newArity : Type} {holes : newArity → theory.Interface}
    {result : theory.Interface} (move : arity → newArity)
    (admitted : ∀ target, ¬ declared (holes target) → ∃! index, move index = target)
    (context : theory.RegionContext declared (fun index => holes (move index)) result) :
    theory.RegionContext declared holes result where
  act := fun filling => context.act fun index => filling (move index)
  realized := by
    obtain ⟨positions, place, inner, admits, acts⟩ := context.realized
    refine ⟨positions, fun position => move (place position), inner, ⟨?_, ?_⟩,
      fun filling => acts _⟩
    · intro target linear
      obtain ⟨index, rfl, onlyIndex⟩ := admitted target linear
      obtain ⟨position, placed, onlyPosition⟩ := admits.once index linear
      exact ⟨position, congrArg move placed, fun other same =>
        onlyPosition other (onlyIndex (place other) same)⟩
    · intro free target
      by_contra linear
      obtain ⟨index, rfl, -⟩ := admitted target linear
      exact linear (admits.promotes free index)

/-- **The context that returns what fills one of its holes**, when every hole
is of a declared interface. -/
def project {arity : Type} (holes : arity → theory.Interface) (index : arity)
    (free : ∀ other, declared (holes other)) :
    theory.RegionContext declared holes (holes index) where
  act := fun filling => filling index
  realized := ⟨Unit, fun _ => index, theory.identity (holes index),
    ⟨fun other linear => (linear (free other)).elim, fun _ => free⟩,
    fun filling => (theory.fill_identity (holes index) fun _ => filling index).symm⟩

/-- **Contexts over holes of declared interfaces compose over shared holes**:
each context put into a hole reads the same fillings. -/
def substitute {arity shared : Type} {holes : arity → theory.Interface}
    {sharedHoles : shared → theory.Interface} {result : theory.Interface}
    (outer : theory.RegionContext declared holes result)
    (inner : (index : arity) → theory.RegionContext declared sharedHoles (holes index))
    (free : ∀ index, declared (sharedHoles index)) :
    theory.RegionContext declared sharedHoles result :=
  rename (holes := sharedHoles) (fun leaf : Σ _ : arity, shared => leaf.2)
    (fun target linear => (linear (free target)).elim) (plug outer inner)

@[simp] theorem act_substitute {arity shared : Type} {holes : arity → theory.Interface}
    {sharedHoles : shared → theory.Interface} {result : theory.Interface}
    (outer : theory.RegionContext declared holes result)
    (inner : (index : arity) → theory.RegionContext declared sharedHoles (holes index))
    (free : ∀ index, declared (sharedHoles index))
    (filling : (index : shared) → theory.Term (sharedHoles index)) :
    (substitute outer inner free).act filling = outer.act fun index => (inner index).act filling :=
  rfl

/-- **A context all of whose holes are of interfaces that are not declared is
a context of the theory**: its holes are placed one to one. -/
theorem exists_context {arity : Type} {holes : arity → theory.Interface}
    {result : theory.Interface} (context : theory.RegionContext declared holes result)
    (linear : ∀ index, ¬ declared (holes index)) :
    ∃ inner : theory.Context holes result, ∀ filling, context.act filling = theory.fill inner filling := by
  obtain ⟨positions, place, inner, admits, acts⟩ := context.realized
  have bijective : Function.Bijective place :=
    ⟨fun first second same => by
        obtain ⟨position, -, only⟩ := admits.once (place first) (linear _)
        exact (only first rfl).trans (only second same.symm).symm,
      fun index => (admits.once index (linear index)).exists⟩
  exact ⟨theory.relabel place bijective inner, fun filling =>
    (acts filling).trans (theory.fill_relabel place bijective inner filling).symm⟩

end RegionContext

/-- **The reading of a theory with a class of declared interfaces**: the
holes of declared interfaces may be used any number of times, every other
hole once.  The terms, the static equivalence and the reduction are those of
the theory. -/
def regionReading : ContextTheory.{u} where
  Interface := theory.Interface
  Term := theory.Term
  equations := theory.equations
  rewrites := theory.rewrites
  rewrites_resp_left := theory.rewrites_resp_left
  rewrites_resp_right := theory.rewrites_resp_right
  Context := theory.RegionContext declared
  fill := fun context filling => context.act filling
  fill_resp := fun context _ _ equivalent => context.act_resp equivalent
  identity := RegionContext.identity
  fill_identity := fun _ _ => rfl
  plug := RegionContext.plug
  fill_plug := fun _ _ _ => rfl
  relabel := fun move bijective context =>
    context.rename move fun target _ => bijective.existsUnique target
  fill_relabel := fun _ _ _ _ => rfl
  constant := RegionContext.constant
  fill_constant := fun _ _ => rfl

/-- **The cartesian reading**: every hole may be used any number of times. -/
abbrev cartesianReading : ContextTheory.{u} := theory.regionReading fun _ => True

/-- **The linear reading**: every hole is used once. -/
abbrev linearReading : ContextTheory.{u} := theory.regionReading fun _ => False

/-! ## The linear reading is the theory -/

/-- The identity on terms, from a theory into its linear reading. -/
def toLinearReading : ContextMap theory theory.linearReading where
  interface := fun interface => interface
  term := fun term => term
  context := fun context => RegionContext.ofContext context fun impossible => impossible.elim
  term_resp := fun related => related
  equivariant := fun _ _ => (theory.equations _).iseqv.refl _

/-- The linear reading loses nothing of the theory. -/
theorem toLinearReading_hosting : theory.toLinearReading.Hosting := by
  rw [ContextMap.hosting_iff, ContextMap.preservesTransitions_iff_rewrites,
    ContextMap.reflectsTransitions_iff_rewrites]
  exact ⟨fun related => related, fun step => step,
    fun step => ⟨_, step, (theory.equations _).iseqv.refl _⟩⟩

/-- The linear reading adds no context. -/
theorem toLinearReading_exhausting : theory.toLinearReading.Exhausting := by
  intro arity holes result observer
  obtain ⟨context, same⟩ := RegionContext.exists_context observer fun _ impossible => impossible
  exact ⟨context, fun filling => by
    show (theory.equations result).r (theory.fill context filling) (observer.act filling)
    rw [same filling]
    exact (theory.equations result).iseqv.refl _⟩

/-- The identity on terms, from the linear reading of a theory back to it: a
context goes to a context of the theory that does the same. -/
noncomputable def ofLinearReading : ContextMap theory.linearReading theory where
  interface := fun interface => interface
  term := fun term => term
  context := fun context =>
    Classical.choose (RegionContext.exists_context context fun _ impossible => impossible)
  term_resp := fun related => related
  equivariant := fun context filling =>
    ContextMap.equations_of_eq (Classical.choose_spec
      (RegionContext.exists_context context fun _ impossible => impossible) filling)

/-- The context of the theory chosen for a context of its linear reading does
what that context does. -/
theorem fill_ofLinearReading {arity : Type} {holes : arity → theory.Interface}
    {result : theory.Interface} (context : theory.RegionContext (fun _ => False) holes result)
    (filling : (index : arity) → theory.Term (holes index)) :
    theory.fill (theory.ofLinearReading.context context) filling = context.act filling :=
  (Classical.choose_spec
    (RegionContext.exists_context context fun _ impossible => impossible) filling).symm

/-- The way back loses nothing either. -/
theorem ofLinearReading_hosting : theory.ofLinearReading.Hosting := by
  rw [ContextMap.hosting_iff, ContextMap.preservesTransitions_iff_rewrites,
    ContextMap.reflectsTransitions_iff_rewrites]
  exact ⟨fun related => related, fun step => step,
    fun step => ⟨_, step, (theory.equations _).iseqv.refl _⟩⟩

/-- And it adds no context. -/
theorem ofLinearReading_exhausting : theory.ofLinearReading.Exhausting := by
  intro arity holes result observer
  refine ⟨RegionContext.ofContext observer fun impossible => impossible.elim, fun filling => ?_⟩
  exact ContextMap.equations_of_eq (theory.fill_ofLinearReading
    (RegionContext.ofContext (declared := fun _ => False) observer
      fun impossible => impossible.elim) filling)

/-! ## Into the cartesian reading -/

/-- The identity on terms, from a theory into its cartesian reading. -/
def toCartesianReading : ContextMap theory theory.cartesianReading where
  interface := fun interface => interface
  term := fun term => term
  context := fun context => RegionContext.ofContext context fun _ _ => trivial
  term_resp := fun related => related
  equivariant := fun _ _ => (theory.equations _).iseqv.refl _

/-- **The cartesian reading loses nothing of the theory.** -/
theorem toCartesianReading_hosting : theory.toCartesianReading.Hosting := by
  rw [ContextMap.hosting_iff, ContextMap.preservesTransitions_iff_rewrites,
    ContextMap.reflectsTransitions_iff_rewrites]
  exact ⟨fun related => related, fun step => step,
    fun step => ⟨_, step, (theory.equations _).iseqv.refl _⟩⟩

/-- **The cartesian reading adds nothing exactly when the theory already has
every context of the reading.** -/
theorem toCartesianReading_exhausting_iff :
    theory.toCartesianReading.Exhausting ↔
      ∀ {arity : Type} {holes : arity → theory.Interface} {result : theory.Interface}
        (observer : theory.RegionContext (fun _ => True) holes result),
        ∃ context : theory.Context holes result, ∀ filling,
          (theory.equations result).r (theory.fill context filling) (observer.act filling) :=
  Iff.rfl

/-- A theory whose cartesian reading adds nothing discards at every
interface. -/
theorem discards_of_toCartesianReading_exhausting
    (exhausting : theory.toCartesianReading.Exhausting) (interface : theory.Interface) :
    theory.Discards interface := by
  obtain ⟨context, agrees⟩ := (theory.toCartesianReading_exhausting_iff).mp exhausting
    (RegionContext.project (fun _ : Bool => interface) false fun _ => trivial)
  exact ⟨context, agrees⟩

/-- The identity on terms, from a reading into the cartesian reading. -/
def regionToCartesian : ContextMap (theory.regionReading declared) theory.cartesianReading where
  interface := fun interface => interface
  term := fun term => term
  context := fun context =>
    { act := context.act
      realized := by
        obtain ⟨positions, place, inner, -, acts⟩ := context.realized
        exact ⟨positions, place, inner,
          ⟨fun _ linear => (linear trivial).elim, fun _ _ => trivial⟩, acts⟩ }
  term_resp := fun related => related
  equivariant := fun _ _ => (theory.equations _).iseqv.refl _

/-- **Every reading is hosted by the cartesian one.** -/
theorem regionToCartesian_hosting : (theory.regionToCartesian declared).Hosting := by
  rw [ContextMap.hosting_iff, ContextMap.preservesTransitions_iff_rewrites,
    ContextMap.reflectsTransitions_iff_rewrites]
  exact ⟨fun related => related, fun step => step,
    fun step => ⟨_, step, (theory.equations _).iseqv.refl _⟩⟩

/-- A reading that the cartesian reading adds nothing to discards at every
interface. -/
theorem discards_of_regionToCartesian_exhausting
    (exhausting : (theory.regionToCartesian declared).Exhausting) (interface : theory.Interface) :
    (theory.regionReading declared).Discards interface := by
  obtain ⟨context, agrees⟩ := exhausting (holes := fun _ : Bool => interface) (result := interface)
    (RegionContext.project (theory := theory) (declared := fun _ => True)
      (fun _ : Bool => interface) false fun _ => trivial)
  exact ⟨context, agrees⟩

/-! ## Into a reading with regions -/

/-- **A theory promotes a class of interfaces**: a context whose result is of
an interface of the class has holes of interfaces of the class only.  The
terms of such interfaces have no part that has to be used once. -/
def Promotes : Prop :=
  ∀ {arity : Type} {holes : arity → theory.Interface} {result : theory.Interface},
    theory.Context holes result → declared result → ∀ index, declared (holes index)

/-- The identity on terms, from a theory into a reading with regions that it
promotes. -/
def toRegionReading (promotes : theory.Promotes declared) :
    ContextMap theory (theory.regionReading declared) where
  interface := fun interface => interface
  term := fun term => term
  context := fun context => RegionContext.ofContext context (promotes context)
  term_resp := fun related => related
  equivariant := fun _ _ => (theory.equations _).iseqv.refl _

/-- A theory is hosted by each reading with regions that it promotes. -/
theorem toRegionReading_hosting (promotes : theory.Promotes declared) :
    (theory.toRegionReading declared promotes).Hosting := by
  rw [ContextMap.hosting_iff, ContextMap.preservesTransitions_iff_rewrites,
    ContextMap.reflectsTransitions_iff_rewrites]
  exact ⟨fun related => related, fun step => step,
    fun step => ⟨_, step, (theory.equations _).iseqv.refl _⟩⟩

/-- **Positive**: every theory promotes the empty class. -/
theorem promotes_none : theory.Promotes fun _ => False :=
  fun _ impossible => impossible.elim

/-- Every theory promotes the class of all its interfaces. -/
theorem promotes_all : theory.Promotes fun _ => True :=
  fun _ _ _ => trivial

/-- **A context of the theory that is a context of a reading respects
promotion.**  So a context from an interface that is not declared to a
declared one is a context of the theory and of no reading that keeps that
declaration. -/
theorem RegionContext.promotes {arity : Type} {holes : arity → theory.Interface}
    {result : theory.Interface} (context : theory.RegionContext declared holes result)
    (free : declared result) (index : arity) : declared (holes index) := by
  obtain ⟨_, _, _, admits, -⟩ := context.realized
  exact admits.promotes free index

/-- **A map into a reading carries promotion back**: when it sends the result
of a context of its source to a declared interface, it sends every hole of
that context to a declared interface. -/
theorem declared_of_contextMap {source : ContextTheory.{u}}
    (map : ContextMap source (theory.regionReading declared)) {arity : Type}
    {holes : arity → source.Interface} {result : source.Interface}
    (context : source.Context holes result) (free : declared (map.interface result))
    (index : arity) : declared (map.interface (holes index)) :=
  RegionContext.promotes theory declared (map.context context) free index

/-- **Only under promotion**: a map from a theory into one of its readings
that is the identity on interfaces exists only when the theory promotes the
declared class. -/
theorem promotes_of_identity (map : ContextMap theory (theory.regionReading declared))
    (same : ∀ interface, map.interface interface = interface) : theory.Promotes declared :=
  fun context free index =>
    (congrArg declared (same _)).mp
      (theory.declared_of_contextMap declared map context
        ((congrArg declared (same _)).mpr free) index)

/-! ## Where a reading discards and copies -/

variable {theory declared}

/-- **A reading discards at an interface exactly when the interface is
declared or the theory discards there.** -/
theorem regionReading_discards_iff {interface : theory.Interface} :
    (theory.regionReading declared).Discards interface ↔
      declared interface ∨ theory.Discards interface := by
  constructor
  · rintro ⟨first, returns⟩
    by_cases free : declared interface
    · exact .inl free
    · obtain ⟨inner, same⟩ := RegionContext.exists_context first fun _ => free
      exact .inr ⟨inner, fun filling => by
        rw [← same filling]
        exact returns filling⟩
  · rintro (free | ⟨first, returns⟩)
    · exact ⟨RegionContext.project (fun _ : Bool => interface) false fun _ => free,
        fun _ => (theory.equations interface).iseqv.refl _⟩
    · exact ⟨RegionContext.ofContext first fun free _ => free, returns⟩

/-- **At a declared interface every context of two holes has its diagonal**:
the context of one hole that fills both with one term. -/
theorem regionReading_diagonal {interface : theory.Interface} (free : declared interface)
    (pair : (theory.regionReading declared).Context (fun _ : Bool => interface) interface) :
    ∃ twice : (theory.regionReading declared).Label interface interface,
      ∀ term, (theory.regionReading declared).apply twice term =
        (theory.regionReading declared).fill pair fun _ => term :=
  ⟨RegionContext.rename (holes := fun _ : Unit => interface) (fun _ : Bool => ())
    (fun _ linear => (linear free).elim) pair, fun _ => rfl⟩

/-- **A reading copies at an interface exactly when the interface is declared
or the theory copies there.** -/
theorem regionReading_copies_iff {interface : theory.Interface} :
    (theory.regionReading declared).Copies interface ↔
      declared interface ∨ theory.Copies interface := by
  constructor
  · rintro ⟨pair, twice, same⟩
    by_cases free : declared interface
    · exact .inl free
    · obtain ⟨innerPair, pairSame⟩ := RegionContext.exists_context pair fun _ => free
      obtain ⟨innerTwice, twiceSame⟩ := RegionContext.exists_context twice fun _ => free
      refine .inr ⟨innerPair, innerTwice, fun term => ?_⟩
      have related := same term
      have left : (theory.regionReading declared).apply twice term =
          theory.apply innerTwice term := twiceSame fun _ => term
      have right : (theory.regionReading declared).fill pair (fun _ => term) =
          theory.fill innerPair fun _ => term := pairSame fun _ => term
      rw [left, right] at related
      exact related
  · rintro (free | ⟨pair, twice, same⟩)
    · exact copies_of_discards _ (regionReading_discards_iff.mpr (.inl free))
    · exact ⟨RegionContext.ofContext pair fun free _ => free,
        RegionContext.ofContext twice fun free _ => free, same⟩

/-- The cartesian reading discards at every interface. -/
theorem cartesianReading_discards (theory : ContextTheory.{u}) (interface : theory.Interface) :
    theory.cartesianReading.Discards interface :=
  regionReading_discards_iff.mpr (.inl trivial)

/-- The cartesian reading copies at every interface. -/
theorem cartesianReading_copies (theory : ContextTheory.{u}) (interface : theory.Interface) :
    theory.cartesianReading.Copies interface :=
  regionReading_copies_iff.mpr (.inl trivial)

/-- **The linear reading discards exactly where the theory does.** -/
theorem linearReading_discards_iff (theory : ContextTheory.{u}) {interface : theory.Interface} :
    theory.linearReading.Discards interface ↔ theory.Discards interface := by
  rw [regionReading_discards_iff]
  exact ⟨fun either => either.elim (fun impossible => impossible.elim) id, .inr⟩

/-! ## The constant map into a reading -/

/-- **The context that discards all its holes and returns one term**, over
holes of declared interfaces. -/
def discardingConstant {arity : Type} (holes : arity → theory.Interface)
    (free : ∀ index, declared (holes index)) {result : theory.Interface}
    (value : theory.Term result) : (theory.regionReading declared).Context holes result :=
  RegionContext.substitute (RegionContext.constant (holes := fun impossible : Empty => impossible.elim)
    value) (fun impossible => impossible.elim) free

@[simp] theorem fill_discardingConstant {arity : Type} (holes : arity → theory.Interface)
    (free : ∀ index, declared (holes index)) {result : theory.Interface}
    (value : theory.Term result) (filling : (index : arity) → theory.Term (holes index)) :
    (theory.regionReading declared).fill (discardingConstant holes free value) filling = value :=
  rfl

/-- **Every theory maps into a reading that declares an interface with a
term**: every term goes to that term, every context to the context that
discards all its holes and returns it. -/
def intoRegionReading (source : ContextTheory.{u}) {point : theory.Interface}
    (free : declared point) (value : theory.Term point) :
    ContextMap source (theory.regionReading declared) :=
  ContextMap.constant (target := theory.regionReading declared) point value
    (fun {arity} _ _ _ => discardingConstant (fun _ : arity => point) (fun _ => free) value)
    (fun _ => (theory.equations point).iseqv.refl value)

/-- **Every theory maps into the cartesian reading of a theory with a term**:
the constant map at that term. -/
def intoCartesianReading (source : ContextTheory.{u}) (theory : ContextTheory.{u})
    {point : theory.Interface} (value : theory.Term point) :
    ContextMap source theory.cartesianReading :=
  intoRegionReading (theory := theory) (declared := fun _ => True) source trivial value

/-- **The constant map is not hosting**, as soon as the source has two terms
that are apart. -/
theorem intoCartesianReading_not_hosting (source : ContextTheory.{u}) (theory : ContextTheory.{u})
    {point : theory.Interface} (value : theory.Term point) {origin : source.Interface}
    {first second : source.Term origin} (apart : ¬ (source.equations origin).r first second) :
    ¬ (intoCartesianReading source theory value).Hosting :=
  ContextMap.not_hosting_of_identifies _ apart ((theory.equations point).iseqv.refl value)

/-! ## Examples -/

/-- **Positive**: the context that returns its first hole, in the cartesian
reading of any theory. -/
def cartesianFirst (theory : ContextTheory.{u}) (interface : theory.Interface) :
    theory.cartesianReading.Context (fun _ : Bool => interface) interface :=
  RegionContext.project (fun _ : Bool => interface) false fun _ => trivial

@[simp] theorem fill_cartesianFirst (theory : ContextTheory.{u}) (interface : theory.Interface)
    (filling : Bool → theory.Term interface) :
    theory.cartesianReading.fill (cartesianFirst theory interface) filling = filling false :=
  rfl

open Mettapedia.GSLT.Dedukti in
/-- **Positive**: the cartesian reading adds nothing to the theory of a syntax
with named holes, in which a hole may already occur any number of times: a
context with its holes placed anew is a context. -/
theorem holeSyntax_toCartesianReading_exhausting {Carrier : Type} (shape : HoleSyntax Carrier)
    (equations : Setoid Carrier) (rewrites : Carrier → Carrier → Prop)
    (fill_resp : ∀ {slots : Type} (context : shape.Hole slots) {first second : slots → Carrier},
      (∀ slot, equations.r (first slot) (second slot)) →
        equations.r (shape.fill first context) (shape.fill second context))
    (left : ∀ {term term' next : Carrier}, equations.r term term' → rewrites term next →
      ∃ next', rewrites term' next' ∧ equations.r next next')
    (right : ∀ {term next next' : Carrier}, rewrites term next → equations.r next next' →
      rewrites term next') :
    (shape.theory equations rewrites fill_resp left right).toCartesianReading.Exhausting := by
  intro arity holes result observer
  obtain ⟨positions, place, inner, -, acts⟩ := observer.realized
  refine ⟨shape.bind (fun position => shape.hole (place position)) inner, fun filling => ?_⟩
  have placed : shape.fill filling (shape.bind (fun position => shape.hole (place position)) inner) =
      shape.fill (fun position => filling (place position)) inner :=
    (shape.fill_bind filling (fun position => shape.hole (place position)) inner).trans
      (congrArg (fun values => shape.fill values inner)
        (funext fun position => shape.fill_hole filling (place position)))
  exact ContextMap.equations_of_eq
    (target := (shape.theory equations rewrites fill_resp left right).cartesianReading)
    (interface := ()) (placed.trans (acts filling).symm)

open Mettapedia.GSLT.Dedukti in
/-- The cartesian reading adds nothing to the λΠ-calculus as it runs. -/
theorem rewritingTheory_toCartesianReading_exhausting (theory : Theory) :
    (rewritingTheory theory).toCartesianReading.Exhausting :=
  @holeSyntax_toCartesianReading_exhausting _ termShape
    ⟨Eq, ⟨fun _ => rfl, fun same => same.symm, fun first second => first.trans second⟩⟩
    (Step theory)
    (fun context _ _ same =>
      congrArg (fun filling => TermContext.fill filling context) (funext same))
    (fun same step => ⟨_, same ▸ step, rfl⟩) (fun step same => same ▸ step)

open Mettapedia.GSLT.Dedukti in
/-- Nor to the rule-table evaluator. -/
theorem tableEvaluator_toCartesianReading_exhausting :
    tableEvaluator.toCartesianReading.Exhausting :=
  @holeSyntax_toCartesianReading_exhausting _ tabledShape
    ⟨Eq, ⟨fun _ => rfl, fun same => same.symm, fun first second => first.trans second⟩⟩
    TableStep
    (fun context _ _ same =>
      congrArg (fun filling => TabledContext.fill filling context) (funext same))
    (fun same step => ⟨_, same ▸ step, rfl⟩) (fun step same => same ▸ step)

open Mettapedia.Logic.HostingStyles.Framework in
/-- **Positive**: nor to the framework with rules as constants; a term with
holes may use a hole any number of times. -/
theorem frameworkTheory_toCartesianReading_exhausting {B : Type} (signature : Signature B) :
    (frameworkTheory signature).toCartesianReading.Exhausting := by
  intro arity holes result observer
  obtain ⟨positions, place, inner, -, acts⟩ := observer.realized
  refine ⟨Tm.fill (fun position => Tm.hole (signature := signature) (holes := holes)
    (context := []) (place position)) inner, fun filling => ?_⟩
  have placed : (Tm.fill (fun position => Tm.hole (signature := signature) (holes := holes)
      (context := []) (place position)) inner).fill filling =
      Tm.fill (fun position => filling (place position)) inner :=
    (Tm.fill_fill _ filling inner).trans
      (congrArg (fun values => Tm.fill values inner)
        (funext fun position => (filling (place position)).rename_closed _))
  exact ContextMap.equations_of_eq (target := (frameworkTheory signature).cartesianReading)
    (interface := result) (placed.trans (acts filling).symm)

/-- **Negative**: the linear reading of a theory given by its terms alone
discards nowhere. -/
theorem termsAlone_linearReading_not_discards (theory : GSLT.{u})
    (interface : theory.termsAlone.Interface) :
    ¬ theory.termsAlone.linearReading.Discards interface :=
  fun discards => termsAlone_not_discards theory interface
    ((linearReading_discards_iff theory.termsAlone).mp discards)

end ContextTheory

#print axioms ContextTheory.copies_of_discards
#print axioms ContextTheory.RegionContext.plug
#print axioms ContextTheory.RegionContext.rename
#print axioms ContextTheory.RegionContext.exists_context
#print axioms ContextTheory.regionReading
#print axioms ContextTheory.toLinearReading_hosting
#print axioms ContextTheory.toLinearReading_exhausting
#print axioms ContextTheory.ofLinearReading_hosting
#print axioms ContextTheory.ofLinearReading_exhausting
#print axioms ContextTheory.toCartesianReading_hosting
#print axioms ContextTheory.discards_of_toCartesianReading_exhausting
#print axioms ContextTheory.regionToCartesian_hosting
#print axioms ContextTheory.toRegionReading_hosting
#print axioms ContextTheory.regionReading_discards_iff
#print axioms ContextTheory.regionReading_diagonal
#print axioms ContextTheory.regionReading_copies_iff
#print axioms ContextTheory.declared_of_contextMap
#print axioms ContextTheory.promotes_of_identity
#print axioms ContextTheory.intoRegionReading
#print axioms ContextTheory.intoCartesianReading
#print axioms ContextTheory.intoCartesianReading_not_hosting
#print axioms ContextTheory.termsAlone_linearReading_not_discards
#print axioms ContextTheory.not_admits_twice
#print axioms ContextTheory.discards_of_regionToCartesian_exhausting
#print axioms ContextTheory.holeSyntax_toCartesianReading_exhausting
#print axioms ContextTheory.rewritingTheory_toCartesianReading_exhausting
#print axioms ContextTheory.tableEvaluator_toCartesianReading_exhausting
#print axioms ContextTheory.frameworkTheory_toCartesianReading_exhausting

end Mettapedia.GSLT
