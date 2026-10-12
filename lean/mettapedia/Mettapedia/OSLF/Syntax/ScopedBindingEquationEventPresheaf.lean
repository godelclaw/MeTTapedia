import Mettapedia.OSLF.Syntax.ScopedBindingEquationEvents
import Mettapedia.OSLF.Syntax.ContextualEquationClassEvents

/-!
# Coherent reindexing of complete permitted binding occurrences

The full root assignment and selected scoped path obey identity and
composition, not merely their endpoint readouts. These earned laws supply an
actual event presheaf and natural endpoint maps into the existing authored
equation-class presheaf. Only permission proofs are omitted by the injective
payload comparison used in the proof.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.ScopedEquationEvents

open _root_.CategoryTheory ScopedEncoding ScopedEquationContexts

universe r

variable {S : Signature} {M : List (MetaArity S)} {Index : Type r}
  {rules : Index → UnpositionedRewrite (withMetas S M)} {permission : PositionPermission S}

local instance : Quiver (Scope S) := bindingFrameQuiver S

namespace Event

abbrev Payload (rules : Index → UnpositionedRewrite (withMetas S M)) (scope : Scope S) :=
  (index : Index) × (holeContext : Ctx S) ×
    ContextualRootEvents.Instance (rules index) holeContext ×
      BindingContext S (holeContext, (rules index).sort) scope

def payload {scope : Scope S} (event : Event rules permission scope) : Payload rules scope :=
  ⟨event.index, event.holeContext, event.root, event.context⟩

theorem payload_injective {scope : Scope S} :
    Function.Injective (payload (rules := rules) (permission := permission) (scope := scope)) := by
  rintro ⟨index, holeContext, root, context, permitted⟩
    ⟨index', holeContext', root', context', permitted'⟩ same
  change (⟨index, holeContext, root, context⟩ : Payload rules scope) =
    ⟨index', holeContext', root', context'⟩ at same
  obtain ⟨rfl, rest⟩ := Sigma.mk.inj_iff.mp same
  obtain ⟨rfl, components⟩ := Sigma.mk.inj_iff.mp (eq_of_heq rest)
  have both := eq_of_heq components
  have roots := congrArg Prod.fst both
  have contexts := congrArg Prod.snd both
  cases roots
  cases contexts
  rfl

theorem map_id {scope : Scope S} (event : Event rules permission scope) :
    event.map scope.1 (fun _ position => .var position) = event := by
  apply payload_injective
  change (⟨event.index,
    (substituteContext event.context scope.1 (fun _ position => .var position)).holeContext,
    event.root.map (substituteContext event.context scope.1
      (fun _ position => .var position)).holeVariables,
    (substituteContext event.context scope.1 (fun _ position => .var position)).path⟩ :
    Payload rules scope) = event.payload
  rw [substituteContext_identity, ContextualRootEvents.Instance.map_id]
  rfl

theorem map_comp {scope : Scope S} (middle destination : Ctx S)
    (first : Sub S scope.1 middle) (second : Sub S middle destination)
    (event : Event rules permission scope) :
    (event.map middle first).map destination second =
      event.map destination (fun sort position => bind second (first sort position)) := by
  apply payload_injective
  let firstMove := substituteContext event.context middle first
  let secondMove := substituteContext firstMove.path destination second
  have packed := congrArg
    (fun moved : SubstitutedContext S (event.holeContext, (rules event.index).sort)
        scope.2 destination =>
      (⟨event.index, moved.holeContext, event.root.map moved.holeVariables, moved.path⟩ :
        Payload rules (destination, scope.2)))
    (substituteContext_composition event.context middle destination first second)
  change (⟨event.index, secondMove.holeContext,
      (event.root.map firstMove.holeVariables).map secondMove.holeVariables,
      secondMove.path⟩ : Payload rules (destination, scope.2)) = _
  rw [ContextualRootEvents.Instance.map_comp]
  exact packed.symm

end Event

variable (rules : Index → UnpositionedRewrite (withMetas S M)) (permission : PositionPermission S)

/-- Complete event occurrences, with the independently earned coherent action. -/
def eventPresheaf (sort : S.Srt) : (Syntactic.Ctxt S)ᵒᵖ ⥤ Type r where
  obj X := Event rules permission (X.unop.vars, sort)
  map f := TypeCat.ofHom (Event.map _ f.unop)
  map_id X := by
    apply ConcreteCategory.hom_ext
    intro event
    exact Event.map_id event
  map_comp f g := by
    apply ConcreteCategory.hom_ext
    intro event
    exact (Event.map_comp _ _ f.unop g.unop event).symm

def sourceNatural (E : List (EqAxiom S M)) (sort : S.Srt) :
    eventPresheaf rules permission sort ⟶
      ContextualEquationClassEvents.termQPresheaf E sort ⋙ uliftFunctor.{r,0} where
  app X := TypeCat.ofHom (fun event => ULift.up (event.sourceClass E))
  naturality X Y f := by
    apply ConcreteCategory.hom_ext
    intro event
    change ULift.up ((event.map Y.unop.vars f.unop).sourceClass E) =
      ULift.up (bindQ f.unop (event.sourceClass E))
    exact congrArg
      (fun value : TermQ E Y.unop.vars sort => (ULift.up value : ULift.{r} _))
      (Event.sourceClass_map E Y.unop.vars f.unop event)

def targetNatural (E : List (EqAxiom S M)) (sort : S.Srt) :
    eventPresheaf rules permission sort ⟶
      ContextualEquationClassEvents.termQPresheaf E sort ⋙ uliftFunctor.{r,0} where
  app X := TypeCat.ofHom (fun event => ULift.up (event.targetClass E))
  naturality X Y f := by
    apply ConcreteCategory.hom_ext
    intro event
    change ULift.up ((event.map Y.unop.vars f.unop).targetClass E) =
      ULift.up (bindQ f.unop (event.targetClass E))
    exact congrArg
      (fun value : TermQ E Y.unop.vars sort => (ULift.up value : ULift.{r} _))
      (Event.targetClass_map E Y.unop.vars f.unop event)

end Mettapedia.OSLF.Binding.ScopedEquationEvents
