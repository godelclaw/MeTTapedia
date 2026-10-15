import Mettapedia.GSLT.Contexts.TermsAlone

/-!
# A family of theories given by their terms, as one theory with many interfaces

`GSLT.termsAlone` presents one theory given by its terms through its contexts,
with one interface.  Here each interface has a theory of its own
(`familyTermsAlone family`): the terms of an interface, their static
equivalence and their reduction are those of `family interface`.  The only
contexts are the hole, at the interface of its result, and the terms.

A map out of such a theory is given by a map on interfaces and a map on terms
that respects the static equivalences (`ContextMap.ofFamilyTerms`).  Between
two such theories, a map whose action on interfaces is injective is exhausting
exactly when every term of the target at the image of an interface is
equivalent to the image of a term (`exhausting_iff_of_injective`): the contexts
of the target are the hole and the terms, and the hole is the image of the
hole.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT

universe u

/-- The contexts of a family of theories given by their terms: the hole, when
there is exactly one hole, at the interface of the result; and the terms,
when there is no hole. -/
inductive FamilyContext {Interface : Type u} (Carrier : Interface → Type u) {arity : Type}
    (holes : arity → Interface) : Interface → Type u where
  | hole (position : arity) (only : ∀ other : arity, other = position) :
      FamilyContext Carrier holes (holes position)
  | constant {result : Interface} (term : Carrier result) (empty : IsEmpty arity) :
      FamilyContext Carrier holes result

namespace FamilyContext

variable {Interface : Type u} {Carrier : Interface → Type u} {arity newArity : Type}

/-- Fill the hole, if there is one. -/
def fill {holes : arity → Interface} {result : Interface}
    (context : FamilyContext Carrier holes result) (filling : (index : arity) → Carrier (holes index)) :
    Carrier result :=
  match context with
  | .hole position _ => filling position
  | .constant term _ => term

/-- Rename the holes along a surjection. -/
def relabel {holes : newArity → Interface} (rename : arity → newArity)
    (surjective : Function.Surjective rename) {result : Interface} :
    FamilyContext Carrier (fun index => holes (rename index)) result →
      FamilyContext Carrier holes result
  | .hole position only =>
      .hole (rename position) fun other => by
        obtain ⟨origin, rfl⟩ := surjective other
        rw [only origin]
  | .constant term empty =>
      .constant term ⟨fun other => by
        obtain ⟨origin, rfl⟩ := surjective other
        exact empty.false origin⟩

theorem fill_relabel {holes : newArity → Interface} (rename : arity → newArity)
    (surjective : Function.Surjective rename) {result : Interface}
    (context : FamilyContext Carrier (fun index => holes (rename index)) result)
    (filling : (index : newArity) → Carrier (holes index)) :
    (context.relabel rename surjective).fill filling =
      context.fill fun index => filling (rename index) := by
  cases context <;> rfl

/-- Plug a family of contexts into the holes of a context. -/
def plug {holes : arity → Interface} {innerArity : arity → Type}
    {innerHoles : (index : arity) → innerArity index → Interface} {result : Interface}
    (context : FamilyContext Carrier holes result)
    (inner : (index : arity) → FamilyContext Carrier (innerHoles index) (holes index)) :
    FamilyContext Carrier (fun position : Σ index, innerArity index =>
      innerHoles position.1 position.2) result :=
  match context with
  | .hole position only =>
      (inner position).relabel (holes := fun position : Σ index, innerArity index =>
          innerHoles position.1 position.2)
        (fun leaf => ⟨position, leaf⟩) (TermsContext.leaf_surjective only)
  | .constant term empty => .constant term ⟨fun leaf => empty.false leaf.1⟩

theorem fill_plug {holes : arity → Interface} {innerArity : arity → Type}
    {innerHoles : (index : arity) → innerArity index → Interface} {result : Interface}
    (context : FamilyContext Carrier holes result)
    (inner : (index : arity) → FamilyContext Carrier (innerHoles index) (holes index))
    (filling : (position : Σ index, innerArity index) → Carrier (innerHoles position.1 position.2)) :
    (context.plug inner).fill filling =
      context.fill fun index => (inner index).fill fun leaf => filling ⟨index, leaf⟩ := by
  cases context with
  | hole position only =>
      exact fill_relabel (holes := fun position : Σ index, innerArity index =>
          innerHoles position.1 position.2)
        (fun leaf => ⟨position, leaf⟩) (TermsContext.leaf_surjective only) (inner position) filling
  | constant term empty => rfl

/-- **Every context is a hole or a term**, seen through its action. -/
theorem view {holes : arity → Interface} {result : Interface}
    (context : FamilyContext Carrier holes result) :
    (∃ (position : arity) (_ : ∀ other : arity, other = position) (same : holes position = result),
      ∀ filling : (index : arity) → Carrier (holes index),
        context.fill filling = same ▸ filling position) ∨
    (∃ term : Carrier result, IsEmpty arity ∧
      ∀ filling : (index : arity) → Carrier (holes index), context.fill filling = term) := by
  cases context with
  | hole position only => exact Or.inl ⟨position, only, rfl, fun _ => rfl⟩
  | constant term empty => exact Or.inr ⟨term, empty, fun _ => rfl⟩

end FamilyContext

/-- **A family of theories given by their terms, presented through its
contexts**: one interface per member, whose terms, static equivalence and
reduction are those of the member; the contexts are the hole and the terms. -/
def familyTermsAlone {Interface : Type u} (family : Interface → GSLT.{u}) : ContextTheory.{u} where
  Interface := Interface
  Term := fun interface => (family interface).Term
  equations := fun interface => (family interface).equations
  rewrites := fun {interface} => (family interface).rewrites
  rewrites_resp_left := fun {interface} => (family interface).rewrites_resp_left
  rewrites_resp_right := fun {interface} => (family interface).rewrites_resp_right
  Context := fun holes result => FamilyContext (fun interface => (family interface).Term) holes result
  fill := fun context filling => context.fill filling
  fill_resp := fun context first second equivalent => by
    cases context with
    | hole position only => exact equivalent position
    | constant term empty => exact (family _).equations.iseqv.refl term
  identity := fun _ => .hole () fun _ => rfl
  fill_identity := fun _ _ => rfl
  plug := fun context inner => context.plug inner
  fill_plug := fun context inner filling => context.fill_plug inner filling
  relabel := fun rename bijective context => context.relabel rename bijective.2
  fill_relabel := fun rename bijective context filling =>
    context.fill_relabel rename bijective.2 filling
  constant := fun term => .constant term ⟨fun impossible => impossible.elim⟩
  fill_constant := fun _ _ => rfl

namespace ContextMap

variable {Index : Type u} {family : Index → GSLT.{u}} {target : ContextTheory.{u}}

/-- The image of a context of a family given by its terms: the hole goes to
the hole, a term to its image. -/
def familyImage (interface : Index → target.Interface)
    (term : {origin : Index} → (family origin).Term → target.Term (interface origin))
    {arity : Type} {holes : arity → Index} {result : Index}
    (context : FamilyContext (fun origin => (family origin).Term) holes result) :
    target.Context (fun index => interface (holes index)) (interface result) :=
  match context with
  | .hole position only =>
      target.relabel (fun _ : Unit => position)
        ⟨fun _ _ _ => rfl, fun other => ⟨(), (only other).symm⟩⟩
        (target.identity (interface (holes position)))
  | .constant value empty =>
      target.relabel (fun impossible : Empty => impossible.elim)
        ⟨fun impossible => impossible.elim, fun other => (empty.false other).elim⟩
        (target.constant (term value))

theorem fill_familyImage (interface : Index → target.Interface)
    (term : {origin : Index} → (family origin).Term → target.Term (interface origin))
    {arity : Type} {holes : arity → Index} {result : Index}
    (context : FamilyContext (fun origin => (family origin).Term) holes result)
    (filling : (index : arity) → (family (holes index)).Term) :
    target.fill (familyImage interface term context) (fun index => term (filling index)) =
      term (context.fill filling) := by
  cases context with
  | hole position only =>
      exact (target.fill_relabel (holes := fun index => interface (holes index))
        (fun _ : Unit => position) ⟨fun _ _ _ => rfl, fun other => ⟨(), (only other).symm⟩⟩
        (target.identity (interface (holes position))) fun index => term (filling index)).trans
        (target.fill_identity _ _)
  | constant value empty =>
      exact (target.fill_relabel (holes := fun index => interface (holes index))
        (fun impossible : Empty => impossible.elim)
        ⟨fun impossible => impossible.elim, fun other => (empty.false other).elim⟩
        (target.constant (term value)) fun index => term (filling index)).trans
        (target.fill_constant (term value) _)

/-- **A map on interfaces and a map on terms that respects the static
equivalences are a map of theories out of a family given by its terms.** -/
def ofFamilyTerms (interface : Index → target.Interface)
    (term : {origin : Index} → (family origin).Term → target.Term (interface origin))
    (term_resp : ∀ {origin : Index} {first second : (family origin).Term},
      (family origin).equations.r first second →
        (target.equations (interface origin)).r (term first) (term second)) :
    ContextMap (familyTermsAlone family) target where
  interface := interface
  term := term
  context := fun context => familyImage interface term context
  term_resp := term_resp
  equivariant := fun context filling =>
    equations_of_eq (fill_familyImage interface term context filling).symm

variable {Other : Type u}

/-- **Between two families given by their terms, a map that is injective on
interfaces is exhausting exactly when every term of the target at the image
of an interface is equivalent to the image of a term.** -/
theorem exhausting_iff_of_injective {family' : Other → GSLT.{u}}
    (map : ContextMap (familyTermsAlone family) (familyTermsAlone family'))
    (injective : Function.Injective map.interface) :
    map.Exhausting ↔ ∀ (origin : Index) (image : (family' (map.interface origin)).Term),
      ∃ preimage : (family origin).Term,
        (family' (map.interface origin)).equations.r (map.term preimage) image := by
  constructor
  · intro exhausting origin image
    obtain ⟨preimage, equivalent⟩ :=
      ContextMap.Exhausting.term_surjective map exhausting (origin := origin) image
    exact ⟨preimage, (family' _).equations.iseqv.symm equivalent⟩
  · intro surjective arity holes result observer
    rcases FamilyContext.view observer with
      ⟨position, only, same, acts⟩ | ⟨value, empty, acts⟩
    · obtain rfl : holes position = result := injective same
      refine ⟨.hole position only, fun filling => ?_⟩
      have equivariant := map.equivariant
        (FamilyContext.hole position only : (familyTermsAlone family).Context holes (holes position))
        filling
      have imageActs : (familyTermsAlone family').fill observer
          (fun index => map.term (filling index)) = map.term (filling position) := acts _
      rw [imageActs]
      exact (family' _).equations.iseqv.symm equivariant
    · obtain ⟨preimage, equivalent⟩ := surjective result value
      refine ⟨.constant preimage empty, fun filling => ?_⟩
      have equivariant := map.equivariant
        (FamilyContext.constant preimage empty : (familyTermsAlone family).Context holes result)
        filling
      have imageActs : (familyTermsAlone family').fill observer
          (fun index => map.term (filling index)) = value := acts _
      rw [imageActs]
      exact (family' _).equations.iseqv.trans ((family' _).equations.iseqv.symm equivariant)
        equivalent

end ContextMap

#print axioms familyTermsAlone
#print axioms ContextMap.ofFamilyTerms
#print axioms ContextMap.exhausting_iff_of_injective

end Mettapedia.GSLT
