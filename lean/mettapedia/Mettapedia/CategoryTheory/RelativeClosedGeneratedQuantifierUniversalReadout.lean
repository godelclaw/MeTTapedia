import Mettapedia.CategoryTheory.RelativeClosedGeneratedQuantifierUniversalClosure
import Mettapedia.CategoryTheory.RelativeClosedSyntaxFunctorExtension

/-!
# Coherent weak-map extension from initial declaration comparisons

The candidate is an actual finite-limit closed functor. Independently
supplied base and fresh-object isomorphisms select its primitive target
presentations, and only the original arrow declarations are admitted by
their complete normalized values. Constructor reconstruction earns local
closure realization. Its six-equation successor uniqueness then recovers
every later operator, giving the whole natural isomorphism to the target's
independently constructed closure interpretation. Raw contexts are retained.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.CategoryTheory.RelativeClosedGeneratedQuantifier.UniversalReadout

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open RelativeClosedSyntax GeneratedCategory FunctorNormalization Iteration Closure

universe k w
variable {C : Type k} [Category.{k} C] {stage : Stage C}
variable {D : Type w} [Category.{k} D]
variable [CartesianMonoidalCategory D] [MonoidalClosed D] [HasFiniteLimits D]
variable {quantifiers : InternalPredicateQuantifiedObject.Operations D}
variable (initial : Model quantifiers stage)
variable (mapping : Object (Closure.signature stage) ⥤ D)
variable [PreservesFiniteLimits mapping] [MonoidalClosedFunctor mapping]
variable (images : AtomicPresentation.PrimitiveImages mapping (modelAssignment initial))

abbrev selected := AtomicPresentation.functor mapping (modelAssignment initial) images

abbrev extracted := FunctorNormalization.assignment (selected initial mapping images) (Closure.headers stage)

/-- Admission compares only independently supplied original primitive arrows. -/
structure InitialArrowImages : Prop where
  arrow (origin : stage.symbols.ArrowName) :
    (extracted initial mapping images).arrow (.inl origin) = initial.meanings.arrow origin

variable (admitted : InitialArrowImages initial mapping images)

omit [CartesianMonoidalCategory D] [MonoidalClosed D] [HasFiniteLimits D] in
private theorem assignment_extensionality {symbols : Symbols.{k}}
    {first second : RelativeClosedSyntax.Interpretation.Assignment C symbols D}
    (bases : first.base = second.base)
    (objects : first.object = second.object)
    (arrows : first.arrow = second.arrow) : first = second := by
  cases first
  cases second
  cases bases
  cases objects
  cases arrows
  rfl

include admitted in
theorem initial_assignment_recovered :
    (stageMap stage 0).precompose (extracted initial mapping images) = initial.meanings := by
  apply assignment_extensionality
  · change 𝟭 C ⋙ (baseFunctor (Closure.signature stage) ⋙ selected initial mapping images) = initial.meanings.base
    rw [Functor.id_comp]
    exact AtomicPresentation.functor_base mapping (modelAssignment initial) images
  · funext origin
    exact AtomicPresentation.functor_named_object mapping (modelAssignment initial) images origin
  · exact funext admitted.arrow

def extractedModel : Model quantifiers (completedStage stage) where
  meanings := extracted initial mapping images
  admitted := reconstruction_realization (selected initial mapping images) (Closure.headers stage)
  proposition :=
    ((stageMap stage 0).evaluateObject_precompose (extracted initial mapping images)
      stage.language.proposition.code).trans
        ((congrArg (fun meanings => meanings.evaluateObject stage.language.proposition.code)
          (initial_assignment_recovered initial mapping images admitted)).trans initial.proposition)
  conjunction :=
    ((stageMap stage 0).evaluateArrow_precompose (extracted initial mapping images)
      stage.language.conjunction.code).trans
        ((congrArg (fun meanings => meanings.evaluateArrow stage.language.conjunction.code)
          (initial_assignment_recovered initial mapping images admitted)).trans initial.conjunction)
  truth :=
    ((stageMap stage 0).evaluateArrow_precompose (extracted initial mapping images)
      stage.truth.code).trans
        ((congrArg (fun meanings => meanings.evaluateArrow stage.truth.code)
          (initial_assignment_recovered initial mapping images admitted)).trans initial.truth)

include admitted

theorem all_primitive_meanings_recovered : extracted initial mapping images = modelAssignment initial :=
  congrArg Model.meanings
    (UniversalClosure.extension_unique initial (extractedModel initial mapping images admitted)
      (initial_assignment_recovered initial mapping images admitted))

theorem all_added_arrow_images : CoherentExtension.ArrowImages mapping (modelAssignment initial)
    images (Closure.headers stage) where
  arrow origin := congrArg (fun meanings => meanings.arrow origin)
    (all_primitive_meanings_recovered initial mapping images admitted)

def comparison : mapping ≅ Closure.modelDiagram initial :=
  CoherentExtension.comparison mapping (modelAssignment initial) images (Closure.headers stage)
    (all_added_arrow_images initial mapping images admitted) (modelRealization initial)

theorem base_component (object : C) :
    (comparison initial mapping images admitted).hom.app (baseObject (Closure.signature stage) object) =
      images.base.hom.app object ≫
        eqToHom (RelativeClosedSyntax.Interpretation.functor_base_object
          (modelAssignment initial) (modelRealization initial) object).symm :=
  CoherentExtension.comparison_hom_base mapping (modelAssignment initial) images (Closure.headers stage)
    (all_added_arrow_images initial mapping images admitted) (modelRealization initial) object

theorem object_component (origin : stage.symbols.ObjectName) :
    (comparison initial mapping images admitted).hom.app (namedObject origin) =
      (images.object origin).hom ≫
        eqToHom (CoherentExtension.target_named_object (modelAssignment initial)
          (modelRealization initial) origin).symm :=
  CoherentExtension.comparison_hom_name mapping (modelAssignment initial) images (Closure.headers stage)
    (all_added_arrow_images initial mapping images admitted) (modelRealization initial) origin

theorem complete_arrow_square {source target : Object (Closure.signature stage)} (arrow : source ⟶ target) :
    mapping.map arrow ≫ (comparison initial mapping images admitted).hom.app target =
      (comparison initial mapping images admitted).hom.app source ≫ (Closure.modelDiagram initial).map arrow :=
  (comparison initial mapping images admitted).hom.naturality arrow

theorem all_raw_object_readings (code : ObjectCode C (symbols stage)) :
    (extracted initial mapping images).evaluateObject code = (modelAssignment initial).evaluateObject code :=
  congrArg (fun meanings => meanings.evaluateObject code)
    (all_primitive_meanings_recovered initial mapping images admitted)

theorem all_raw_arrow_readings (code : ArrowCode C (symbols stage)) :
    (extracted initial mapping images).evaluateArrow code = (modelAssignment initial).evaluateArrow code :=
  congrArg (fun meanings => meanings.evaluateArrow code)
    (all_primitive_meanings_recovered initial mapping images admitted)

end Mettapedia.CategoryTheory.RelativeClosedGeneratedQuantifier.UniversalReadout
