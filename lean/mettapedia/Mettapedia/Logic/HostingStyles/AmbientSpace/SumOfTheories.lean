import Mettapedia.GSLT.Contexts.TransitionProfile
import Mettapedia.Logic.HostingStyles.PrimeCandidate.ContextShape

/-!
# The sum of a family of theories presented through their contexts

A family of theories indexed by a type has a sum: one theory whose
interfaces are the pairs of an index and an interface of that member
(`ContextTheory.sum`).  The terms, the static equivalence and the reduction
at such an interface are those of the member.

A context of the sum is what a context of one member does to the terms that
fill it (`SumContext`): its holes and its result all belong to that member.
There is no context between two members (`sum_isEmpty_context_of_ne`).
Contexts are compared by what they do, as the laws of a theory read them.

* Each member is hosted by the sum, and the sum adds no context between the
  interfaces of one member: the inclusion is hosting and exhausting
  (`inject_hosting`, `inject_exhausting`).
* If every member has a linear size, the sum has one (`LinearSize.sum`).

`GSLT.familyTermsAlone` is the sum of a family of theories given by their
terms alone; this module is the same construction for theories that have
contexts.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT

universe u

namespace ContextTheory

variable {Index : Type u} (family : Index → ContextTheory.{u})

/-- An interface of the sum: an index, and an interface of that member. -/
abbrev SumInterface : Type u := Σ index, (family index).Interface

/-- The terms of the sum at an interface are those of the member. -/
abbrev SumTerm (interface : SumInterface family) : Type u :=
  (family interface.1).Term interface.2

/-- Terms of one interface written in two ways are related when they are. -/
theorem sum_cast_related {first second : SumInterface family} (same : first = second)
    {left right : SumTerm family first}
    (related : ((family first.1).equations first.2).r left right) :
    ((family second.1).equations second.2).r (cast (congrArg (SumTerm family) same) left)
      (cast (congrArg (SumTerm family) same) right) := by
  subst same
  exact related

/-- **A context of the sum**: what a context of one member does to the terms
that fill it.  Every hole and the result belong to that member. -/
structure SumContext {arity : Type} (holes : arity → SumInterface family)
    (result : SumInterface family) : Type u where
  /-- What the context does to the terms that fill its holes. -/
  act : ((position : arity) → SumTerm family (holes position)) → SumTerm family result
  /-- A context of the member of the result does it. -/
  realized : ∃ (inner : arity → (family result.1).Interface)
      (same : ∀ position, holes position = ⟨result.1, inner position⟩)
      (context : (family result.1).Context inner result.2),
      ∀ filling, act filling = (family result.1).fill context fun position =>
        cast (congrArg (SumTerm family) (same position)) (filling position)

namespace SumContext

variable {family}

/-- Filling respects the static equivalence. -/
theorem act_resp {arity : Type} {holes : arity → SumInterface family}
    {result : SumInterface family} (context : SumContext family holes result)
    {first second : (position : arity) → SumTerm family (holes position)}
    (equivalent : ∀ position,
      ((family (holes position).1).equations (holes position).2).r (first position)
        (second position)) :
    ((family result.1).equations result.2).r (context.act first) (context.act second) := by
  obtain ⟨inner, same, member, acts⟩ := context.realized
  rw [acts first, acts second]
  exact (family result.1).fill_resp member fun position =>
    sum_cast_related family (same position) (equivalent position)

/-- The context that is a hole. -/
def identity (interface : SumInterface family) :
    SumContext family (fun _ : Unit => interface) interface where
  act := fun filling => filling ()
  realized := ⟨fun _ => interface.2, fun _ => rfl, (family interface.1).identity interface.2,
    fun _ => ((family interface.1).fill_identity interface.2 _).symm⟩

/-- A term, as a context with no hole. -/
def constant {holes : Empty → SumInterface family} {result : SumInterface family}
    (term : SumTerm family result) : SumContext family holes result where
  act := fun _ => term
  realized := ⟨fun impossible => impossible.elim, fun impossible => impossible.elim,
    (family result.1).constant term, fun _ => ((family result.1).fill_constant term _).symm⟩

/-- Plug a family of contexts into the holes of a context. -/
def plug {arity : Type} {holes : arity → SumInterface family} {result : SumInterface family}
    {innerArity : arity → Type}
    {innerHoles : (index : arity) → innerArity index → SumInterface family}
    (context : SumContext family holes result)
    (inner : (index : arity) → SumContext family (innerHoles index) (holes index)) :
    SumContext family
      (fun position : Σ index, innerArity index => innerHoles position.1 position.2) result where
  act := fun filling => context.act fun index => (inner index).act fun leaf => filling ⟨index, leaf⟩
  realized := by
    obtain ⟨outerHoles, outerSame, outer, outerActs⟩ := context.realized
    obtain rfl : holes = fun position => ⟨result.1, outerHoles position⟩ := funext outerSame
    choose leafHoles leafSame leaves leafActs using fun index => (inner index).realized
    refine ⟨fun position => leafHoles position.1 position.2,
      fun position => leafSame position.1 position.2, (family result.1).plug outer leaves, ?_⟩
    intro filling
    rw [(family result.1).fill_plug, outerActs]
    congr 1
    funext index
    rw [cast_eq]
    exact leafActs index _

/-- Rename the holes along a bijection. -/
def relabel {arity newArity : Type} {holes : newArity → SumInterface family}
    {result : SumInterface family} (rename : arity → newArity)
    (bijective : Function.Bijective rename)
    (context : SumContext family (fun index => holes (rename index)) result) :
    SumContext family holes result where
  act := fun filling => context.act fun index => filling (rename index)
  realized := by
    obtain ⟨inner, same, member, acts⟩ := context.realized
    have located : ∀ target : newArity, ∃ interface : (family result.1).Interface,
        holes target = ⟨result.1, interface⟩ := by
      intro target
      obtain ⟨origin, rfl⟩ := bijective.2 target
      exact ⟨inner origin, same origin⟩
    choose moved movedSame using located
    obtain rfl : holes = fun target => ⟨result.1, moved target⟩ := funext movedSame
    obtain rfl : inner = fun index => moved (rename index) :=
      funext fun index => (eq_of_heq (Sigma.mk.inj (same index)).2).symm
    refine ⟨moved, fun _ => rfl, (family result.1).relabel rename bijective member, ?_⟩
    intro filling
    rw [(family result.1).fill_relabel, acts]

end SumContext

/-- **The sum of a family of theories**: an interface is an index and an
interface of that member; the terms, the static equivalence and the
reduction there are those of the member; a context is a context of one
member. -/
def sum : ContextTheory.{u} where
  Interface := SumInterface family
  Term := SumTerm family
  equations := fun interface => (family interface.1).equations interface.2
  rewrites := fun {interface} => (family interface.1).rewrites
  rewrites_resp_left := fun {interface} => (family interface.1).rewrites_resp_left
  rewrites_resp_right := fun {interface} => (family interface.1).rewrites_resp_right
  Context := SumContext family
  fill := fun context filling => context.act filling
  fill_resp := fun context _ _ equivalent => context.act_resp equivalent
  identity := SumContext.identity
  fill_identity := fun _ _ => rfl
  plug := SumContext.plug
  fill_plug := fun _ _ _ => rfl
  relabel := SumContext.relabel
  fill_relabel := fun _ _ _ _ => rfl
  constant := SumContext.constant
  fill_constant := fun _ _ => rfl

/-! ## The members in the sum -/

/-- **The inclusion of a member**: a term is itself, at the interface that
carries the index of the member. -/
def inject (index : Index) : ContextMap (family index) (sum family) where
  interface := fun interface => ⟨index, interface⟩
  term := fun term => term
  context := fun context =>
    { act := fun filling => (family index).fill context filling
      realized := ⟨_, fun _ => rfl, context, fun _ => rfl⟩ }
  term_resp := fun related => related
  equivariant := fun _ _ => ((family index).equations _).iseqv.refl _

/-- **The sum loses nothing of a member.** -/
theorem inject_hosting (index : Index) : (inject family index).Hosting := by
  rw [ContextMap.hosting_iff, ContextMap.preservesTransitions_iff_rewrites,
    ContextMap.reflectsTransitions_iff_rewrites]
  exact ⟨fun related => related, fun step => step,
    fun step => ⟨_, step, ((family index).equations _).iseqv.refl _⟩⟩

/-- **The sum adds no context between the interfaces of one member.** -/
theorem inject_exhausting (index : Index) : (inject family index).Exhausting := by
  intro arity holes result observer
  obtain ⟨inner, same, member, acts⟩ := observer.realized
  obtain rfl : holes = inner :=
    funext fun position => eq_of_heq (Sigma.mk.inj (same position)).2
  refine ⟨member, fun filling => ?_⟩
  show ((family index).equations result).r ((family index).fill member filling)
    (observer.act filling)
  rw [acts filling]
  exact ContextMap.equations_of_eq (target := family index)
    (congrArg ((family index).fill member) (funext fun position => (cast_eq _ _).symm))

/-- **Positive**: a context of a member is a context of the sum, and does
there what it does. -/
theorem fill_inject_context (index : Index) {arity : Type}
    {holes : arity → (family index).Interface} {result : (family index).Interface}
    (context : (family index).Context holes result)
    (filling : (position : arity) → (family index).Term (holes position)) :
    (sum family).fill ((inject family index).context context) filling =
      (family index).fill context filling :=
  rfl

/-- **Negative**: the sum has no context from an interface of one member to
an interface of another. -/
theorem sum_isEmpty_context_of_ne {first second : Index} (apart : first ≠ second)
    (source : (family first).Interface) (target : (family second).Interface) :
    IsEmpty ((sum family).Context (fun _ : Unit => (⟨first, source⟩ : SumInterface family))
      ⟨second, target⟩) :=
  ⟨fun context => by
    obtain ⟨inner, same, -, -⟩ := context.realized
    exact apart (congrArg Sigma.fst (same ()))⟩

/-! ## A linear size -/

/-- **A sum of theories with a linear size has a linear size**: the size of a
term is its size in its member. -/
def LinearSize.sum (sized : (index : Index) → (family index).LinearSize) :
    (sum family).LinearSize where
  size := fun {interface} term => (sized interface.1).size term
  positive := fun {interface} term => (sized interface.1).positive term
  respects := fun {interface} _ _ related => (sized interface.1).respects related
  additive := fun {arity} _ holes result context => by
    obtain ⟨inner, same, member, acts⟩ := context.realized
    obtain rfl : holes = fun position => ⟨result.1, inner position⟩ := funext same
    obtain ⟨weight, adds⟩ := (sized result.1).additive member
    refine ⟨weight, fun filling => ?_⟩
    show (sized result.1).size (context.act filling) = _
    rw [acts filling, adds]
    rfl

end ContextTheory

#print axioms ContextTheory.sum
#print axioms ContextTheory.inject_hosting
#print axioms ContextTheory.inject_exhausting
#print axioms ContextTheory.sum_isEmpty_context_of_ne
#print axioms ContextTheory.LinearSize.sum

end Mettapedia.GSLT
