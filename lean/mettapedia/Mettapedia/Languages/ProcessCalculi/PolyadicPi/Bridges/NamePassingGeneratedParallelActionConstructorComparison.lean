import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingGeneratedParallelActionCategoryComparison
import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingGeneratedConstructorCanonicalRemaining

/-!
# Complete constructor images in the parallel-action guest

The extended guest's binding algebra is recovered from the mapped all-arity
primitive declarations. Its continuation constructors are formed using its
own ordered products, function objects, evaluation and abstraction. Whole
arrow transport identifies these independently formed constructors with the
postcomposed compiler images, retaining all padded and function arguments.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingGeneratedParallelActionConstructorComparison

open _root_.CategoryTheory _root_.CategoryTheory.Limits MonoidalCategory
open CartesianMonoidalCategory MonoidalClosed
open Mettapedia.CategoryTheory RelativeClosedSyntax GeneratedCategory Interpretation
open Mettapedia.OSLF.Binding
open Mettapedia.Languages.LambdaCalculus

universe k

abbrev Target := BindingClosedGeneratedParallelAction.Guest.{k}
abbrev Original := BindingClosedGeneratedOperationalModel.Target.{k}
abbrev mapping := BindingClosedGeneratedParallelAction.inclusion.{k}
abbrev quotient := mapping.{k}.functor
abbrev oldBinding := BindingClosedGeneratedOperationalModel.binding.{k}
abbrev oldOrdinary := BindingClosedGeneratedOperationalModel.ordinary.{k}

def binding := ClosedPresentation.GeneratedFunctor.mapOperations mapping oldBinding.{k}
def ordinary := BindingClosedPrimitiveOperations.continuation binding.{k}

private theorem primitive_transport {result : AllArity.sig.Srt} (operator : AllArity.sig.Op result) :
    HEq (binding.{k}.operation operator) (quotient.map (oldBinding.operation operator)) :=
  ClosedPresentation.GeneratedFunctor.mapOperations_operation_heq mapping oldBinding operator

private theorem plain_transport (result : AllArity.sig.Srt) :
    BindingClosedPrimitiveOperations.plain binding.{k} result =
      quotient.map (BindingClosedPrimitiveOperations.plain oldBinding result) :=
  BindingClosedGeneratedOperationalClosure.plain_transport mapping oldBinding result

private theorem unary_transport : BindingClosedPrimitiveOperations.unaryBody binding.{k} =
    quotient.map (BindingClosedPrimitiveOperations.unaryBody oldBinding) :=
  BindingClosedGeneratedOperationalClosure.unaryBody_transport mapping oldBinding

private theorem binary_hom_transport : (BindingClosedPrimitiveOperations.binaryTuple binding.{k}).hom =
    quotient.map (BindingClosedPrimitiveOperations.binaryTuple oldBinding).hom := by
  change (α_ (quotient.obj oldOrdinary.names) (quotient.obj oldOrdinary.names) (𝟙_ Target)).inv ≫
      (ρ_ (quotient.obj oldOrdinary.names ⊗ quotient.obj oldOrdinary.names)).hom =
    quotient.map ((α_ oldOrdinary.names oldOrdinary.names (𝟙_ Original)).inv ≫
      (ρ_ (oldOrdinary.names ⊗ oldOrdinary.names)).hom)
  rw [quotient.map_comp, mapping.functor_rightUnitor_hom]
  rfl

private theorem binary_inv_transport : (BindingClosedPrimitiveOperations.binaryTuple binding.{k}).inv =
    quotient.map (BindingClosedPrimitiveOperations.binaryTuple oldBinding).inv := by
  apply (cancel_mono (BindingClosedPrimitiveOperations.binaryTuple binding).hom).mp
  rw [Iso.inv_hom_id, binary_hom_transport, ← quotient.map_comp, Iso.inv_hom_id, quotient.map_id]
  rfl

private theorem binary_transport : BindingClosedPrimitiveOperations.binaryBody binding.{k} =
    quotient.map (BindingClosedPrimitiveOperations.binaryBody oldBinding) := by
  unfold BindingClosedPrimitiveOperations.binaryBody
  rw [mapping.functor_pre, ← binary_hom_transport]
  rfl

private theorem input_one_transport : BindingClosedPrimitiveOperations.input binding.{k} 1 =
    quotient.map (BindingClosedPrimitiveOperations.input oldBinding 1) := by
  unfold BindingClosedPrimitiveOperations.input
  have primitive := eq_of_heq (primitive_transport (AllArity.Op.inp 1))
  rw [primitive, quotient.map_comp, mapping.functor_lift, mapping.functor_lift,
    quotient.map_comp, mapping.functor_toUnit, plain_transport]
  rfl

private theorem input_two_transport : BindingClosedPrimitiveOperations.input binding.{k} 2 =
    quotient.map (BindingClosedPrimitiveOperations.input oldBinding 2) := by
  unfold BindingClosedPrimitiveOperations.input
  have primitive := eq_of_heq (primitive_transport (AllArity.Op.inp 2))
  rw [primitive, quotient.map_comp, mapping.functor_lift, mapping.functor_lift,
    quotient.map_comp, mapping.functor_toUnit, plain_transport]
  rfl

private theorem output_one_transport : BindingClosedPrimitiveOperations.output binding.{k} 1 =
    quotient.map (BindingClosedPrimitiveOperations.output oldBinding 1) := by
  unfold BindingClosedPrimitiveOperations.output
  have primitive := eq_of_heq (primitive_transport (AllArity.Op.out 1))
  rw [primitive, quotient.map_comp, mapping.functor_lift, quotient.map_comp, plain_transport]
  simp only [BindingClosedPrimitiveOperations.vector, quotient.map_comp,
    mapping.functor_lift, plain_transport]
  rfl

private theorem output_two_transport : BindingClosedPrimitiveOperations.output binding.{k} 2 =
    quotient.map (BindingClosedPrimitiveOperations.output oldBinding 2) := by
  unfold BindingClosedPrimitiveOperations.output
  have primitive := eq_of_heq (primitive_transport (AllArity.Op.out 2))
  rw [primitive, quotient.map_comp, mapping.functor_lift, quotient.map_comp, plain_transport]
  simp only [BindingClosedPrimitiveOperations.vector, quotient.map_comp,
    mapping.functor_lift, plain_transport]
  rfl

theorem target_output : ordinary.{k}.output = quotient.map oldOrdinary.output := by
  change lift (fst _ _) (lift (snd _ _) (toUnit _)) ≫ BindingClosedPrimitiveOperations.output binding 1 =
    quotient.map (lift (fst _ _) (lift (snd _ _) (toUnit _)) ≫ BindingClosedPrimitiveOperations.output oldBinding 1)
  rw [output_one_transport, quotient.map_comp, mapping.functor_lift, mapping.functor_lift, mapping.functor_toUnit]
  rfl

theorem target_send : ordinary.{k}.send = quotient.map oldOrdinary.send := by
  change lift (fst _ _) (snd _ _ ≫ (BindingClosedPrimitiveOperations.binaryTuple binding).inv) ≫
      BindingClosedPrimitiveOperations.output binding 2 =
    quotient.map (lift (fst _ _) (snd _ _ ≫ (BindingClosedPrimitiveOperations.binaryTuple oldBinding).inv) ≫
      BindingClosedPrimitiveOperations.output oldBinding 2)
  rw [output_two_transport, binary_inv_transport, quotient.map_comp, mapping.functor_lift, quotient.map_comp]
  rfl

theorem target_input : ordinary.{k}.input = quotient.map oldOrdinary.input := by
  change lift (fst _ _) (snd _ _ ≫ BindingClosedPrimitiveOperations.unaryBody binding) ≫
      BindingClosedPrimitiveOperations.input binding 1 =
    quotient.map (lift (fst _ _) (snd _ _ ≫ BindingClosedPrimitiveOperations.unaryBody oldBinding) ≫
      BindingClosedPrimitiveOperations.input oldBinding 1)
  rw [input_one_transport, unary_transport, quotient.map_comp, mapping.functor_lift, quotient.map_comp]
  rfl

theorem target_receive : ordinary.{k}.receive = quotient.map oldOrdinary.receive := by
  change lift (fst _ _) (snd _ _ ≫ BindingClosedPrimitiveOperations.binaryBody binding) ≫
      BindingClosedPrimitiveOperations.input binding 2 =
    quotient.map (lift (fst _ _) (snd _ _ ≫ BindingClosedPrimitiveOperations.binaryBody oldBinding) ≫
      BindingClosedPrimitiveOperations.input oldBinding 2)
  rw [input_two_transport, binary_transport, quotient.map_comp, mapping.functor_lift, quotient.map_comp]
  rfl

theorem target_parallel : ordinary.{k}.parallel = quotient.map oldOrdinary.parallel :=
  BindingClosedGeneratedOperationalClosure.parallel_transport mapping oldBinding

theorem target_fresh : ordinary.{k}.fresh = quotient.map oldOrdinary.fresh :=
  BindingClosedGeneratedOperationalClosure.fresh_transport mapping oldBinding

theorem target_replication : ordinary.{k}.replication = quotient.map oldOrdinary.replication := by
  change lift (BindingClosedPrimitiveOperations.plain binding .pr) (toUnit _) ≫ binding.operation AllArity.Op.rep =
    quotient.map (lift (BindingClosedPrimitiveOperations.plain oldBinding .pr) (toUnit _) ≫ oldBinding.operation AllArity.Op.rep)
  have primitive := eq_of_heq (primitive_transport AllArity.Op.rep)
  rw [primitive, quotient.map_comp, mapping.functor_lift, mapping.functor_toUnit, plain_transport]
  rfl

private theorem map_abstraction {context argument result : Original.{k}}
    (body : context ⊗ argument ⟶ result) :
    quotient.map (Interpretation.abstraction body) =
      Interpretation.abstraction (context := quotient.obj context) (argument := quotient.obj argument)
        (result := quotient.obj result) (quotient.map body) := by
  unfold Interpretation.abstraction Interpretation.exchange
  rw [mapping.functor_curry, quotient.map_comp, mapping.functor_lift]
  rfl

private theorem map_lift {context first second : Original.{k}}
    (before : context ⟶ first) (after : context ⟶ second) :
    quotient.map (lift before after) = lift (quotient.map before) (quotient.map after) :=
  mapping.functor_lift before after

private theorem map_evaluation (argument result : Original.{k}) :
    quotient.map (Interpretation.evaluation argument result) =
      Interpretation.evaluation (quotient.obj argument) (quotient.obj result) := by
  unfold Interpretation.evaluation Interpretation.exchange
  rw [quotient.map_comp, mapping.functor_lift, mapping.functor_monoidal_evaluation]
  rfl

theorem whole_reference : ordinary.{k}.reference = quotient.map oldOrdinary.reference := by
  change Interpretation.abstraction ordinary.output = quotient.map (Interpretation.abstraction oldOrdinary.output)
  rw [map_abstraction, target_output]

theorem whole_abstraction : ordinary.{k}.abstraction = quotient.map oldOrdinary.abstraction := by
  simp only [NamePassingContinuationOperations.Operations.abstraction, NamePassingContinuationOperations.call,
    quotient.map_comp, map_abstraction, map_lift, map_evaluation]
  rw [target_receive]
  rfl

theorem whole_application : ordinary.{k}.application = quotient.map oldOrdinary.application := by
  simp only [NamePassingContinuationOperations.Operations.application, NamePassingContinuationOperations.call,
    NamePassingContinuationOperations.bindFresh, quotient.map_comp,
    map_abstraction, map_lift, map_evaluation]
  rw [target_send, target_fresh, target_parallel]
  rfl

theorem whole_definition : ordinary.{k}.definition = quotient.map oldOrdinary.definition := by
  simp only [NamePassingContinuationOperations.Operations.definition, NamePassingContinuationOperations.call,
    NamePassingContinuationOperations.bindFresh, quotient.map_comp,
    map_abstraction, map_lift, map_evaluation]
  rw [target_input, target_replication, target_fresh, target_parallel]
  rfl

theorem whole_carrier : ordinary.{k}.carrier = quotient.map oldOrdinary.carrier := by
  simp only [NamePassingContinuationOperations.Operations.carrier, NamePassingContinuationOperations.call,
    quotient.map_comp, map_abstraction, map_lift, map_evaluation]
  rw [target_input, target_parallel]
  rfl

abbrev ConstructorSource := NamePassingGeneratedConstructorComparison.Source.{k}
abbrev sourceOperations := NamePassingGeneratedConstructorComparison.sourceOperations.{k}
abbrev oldConstructorCompiler := NamePassingGeneratedConstructorComparison.compiler.{k}

def constructorCompiler : ConstructorSource.{k} ⥤ Target := oldConstructorCompiler ⋙ quotient

instance constructorCompiler_finite : PreservesFiniteLimits constructorCompiler.{k} := by
  let : PreservesFiniteLimits oldConstructorCompiler := NamePassingGeneratedConstructorCanonical.compiler_finite
  exact comp_preservesFiniteLimits _ _

instance constructorCompiler_closed : MonoidalClosedFunctor constructorCompiler.{k} := by
  let : MonoidalClosedFunctor oldConstructorCompiler := NamePassingGeneratedConstructorCanonical.compiler_closed
  exact CartesianClosedFunctorCoherence.closed_composition _ _

theorem complete_compiler_restriction :
    NamePassingGeneratedParallelActionComparison.originalInclusion.{k} ⋙
      NamePassingGeneratedParallelActionComparison.compiler.functor = constructorCompiler :=
  NamePassingGeneratedParallelActionComparison.complete_original_restriction

def nativeDomainComparison (operator : NamePassing.Presentation.Operator .tm) :=
  quotient.mapIso (NamePassingGeneratedConstructorNaturality.nativeDomainComparison.{k} operator)

def nativeProgramComparison (operator : NamePassing.Presentation.Operator .tm) :=
  quotient.mapIso (NamePassingGeneratedConstructorNaturality.nativeProgramComparison.{k} operator)

theorem whole_native_constructor (operator : NamePassing.Presentation.Operator .tm) :
    (nativeDomainComparison.{k} operator).inv ≫
      constructorCompiler.map (NamePassingBindingClosedConstructorReadout.arrow sourceOperations operator) ≫
        (nativeProgramComparison operator).hom =
      quotient.map (NamePassingGeneratedConstructorComparison.targetValue operator).arrow := by
  have actual := congrArg quotient.map
    (NamePassingGeneratedConstructorNaturality.complete_native_constructor operator)
  simp only [quotient.map_comp] at actual
  exact actual

def targetValue : NamePassing.Presentation.Operator .tm → ArrowValue Target.{k}
  | .reference => ⟨ordinary.names, ordinary.termObject, ordinary.reference⟩
  | .abstraction => ⟨ordinary.boundBodyObject, ordinary.termObject, ordinary.abstraction⟩
  | .application => ⟨ordinary.termObject ⊗ ordinary.names, ordinary.termObject, ordinary.application⟩
  | .definition => ⟨ordinary.termObject ⊗ ordinary.boundBodyObject, ordinary.termObject, ordinary.definition⟩
  | .carrier => ⟨ordinary.names ⊗ (ordinary.termObject ⊗ ordinary.termObject), ordinary.termObject, ordinary.carrier⟩

private def mapValue (value : ArrowValue Original.{k}) : ArrowValue Target :=
  ⟨quotient.obj value.source, quotient.obj value.target, quotient.map value.arrow⟩

theorem whole_target_constructor (operator : NamePassing.Presentation.Operator .tm) :
    mapValue (NamePassingGeneratedConstructorComparison.targetValue.{k} operator) = targetValue operator := by
  cases operator with
  | reference =>
      exact congrArg (fun arrow : ordinary.names ⟶ ordinary.termObject =>
        (⟨ordinary.names, ordinary.termObject, arrow⟩ : ArrowValue Target))
          ((congrArg quotient.map NamePassingGeneratedConstructorComparison.reference_readout).trans whole_reference.symm)
  | abstraction =>
      exact congrArg (fun arrow : ordinary.boundBodyObject ⟶ ordinary.termObject =>
        (⟨ordinary.boundBodyObject, ordinary.termObject, arrow⟩ : ArrowValue Target))
          ((congrArg quotient.map NamePassingGeneratedConstructorComparison.abstraction_readout).trans whole_abstraction.symm)
  | application =>
      exact congrArg (fun arrow : ordinary.termObject ⊗ ordinary.names ⟶ ordinary.termObject =>
        (⟨ordinary.termObject ⊗ ordinary.names, ordinary.termObject, arrow⟩ : ArrowValue Target))
          ((congrArg quotient.map NamePassingGeneratedConstructorComparison.application_readout).trans whole_application.symm)
  | definition =>
      exact congrArg (fun arrow : ordinary.termObject ⊗ ordinary.boundBodyObject ⟶ ordinary.termObject =>
        (⟨ordinary.termObject ⊗ ordinary.boundBodyObject, ordinary.termObject, arrow⟩ : ArrowValue Target))
          ((congrArg quotient.map NamePassingGeneratedConstructorComparison.definition_readout).trans whole_definition.symm)
  | carrier =>
      exact congrArg (fun arrow : ordinary.names ⊗ (ordinary.termObject ⊗ ordinary.termObject) ⟶ ordinary.termObject =>
        (⟨ordinary.names ⊗ (ordinary.termObject ⊗ ordinary.termObject), ordinary.termObject, arrow⟩ : ArrowValue Target))
          ((congrArg quotient.map NamePassingGeneratedConstructorComparison.carrier_readout).trans whole_carrier.symm)

theorem whole_constructor_certificate (operator : NamePassing.Presentation.Operator .tm) :
    (⟨quotient.obj (NamePassingGeneratedConstructorComparison.targetValue.{k} operator).source,
      quotient.obj (NamePassingGeneratedConstructorComparison.targetValue operator).target,
      (nativeDomainComparison operator).inv ≫
        constructorCompiler.map (NamePassingBindingClosedConstructorReadout.arrow sourceOperations operator) ≫
          (nativeProgramComparison operator).hom⟩ : ArrowValue Target) = targetValue operator := by
  rw [whole_native_constructor]
  exact whole_target_constructor operator

def nameComparison : constructorCompiler.obj (NamePassingBindingPrimitiveOperations.names sourceOperations.{k}) ≅
    ordinary.names := quotient.mapIso NamePassingGeneratedConstructorCanonical.nameComparison

def termComparison : constructorCompiler.obj (NamePassingBindingPrimitiveOperations.terms sourceOperations.{k}) ≅
    ordinary.termObject := quotient.mapIso NamePassingGeneratedConstructorCanonical.termComparison

def applicationComparison : constructorCompiler.obj
    (NamePassingBindingPrimitiveOperations.terms sourceOperations.{k} ⊗
      NamePassingBindingPrimitiveOperations.names sourceOperations) ≅ ordinary.termObject ⊗ ordinary.names :=
  quotient.mapIso NamePassingGeneratedConstructorCanonical.applicationComparison

def abstractionComparison : constructorCompiler.obj (NamePassingBindingPrimitiveOperations.bodies sourceOperations.{k}) ≅
    ordinary.boundBodyObject := quotient.mapIso NamePassingGeneratedConstructorCanonical.abstractionComparison

def definitionComparison : constructorCompiler.obj
    (NamePassingBindingPrimitiveOperations.terms sourceOperations.{k} ⊗
      NamePassingBindingPrimitiveOperations.bodies sourceOperations) ≅ ordinary.termObject ⊗ ordinary.boundBodyObject :=
  quotient.mapIso NamePassingGeneratedConstructorCanonicalDomains.definitionComparison

def pairComparison : constructorCompiler.obj
    (NamePassingBindingPrimitiveOperations.terms sourceOperations.{k} ⊗
      NamePassingBindingPrimitiveOperations.terms sourceOperations) ≅ ordinary.termObject ⊗ ordinary.termObject :=
  quotient.mapIso NamePassingGeneratedConstructorCanonicalRemaining.pairComparison

def carrierComparison : constructorCompiler.obj
    (NamePassingBindingPrimitiveOperations.names sourceOperations.{k} ⊗
      (NamePassingBindingPrimitiveOperations.terms sourceOperations ⊗
        NamePassingBindingPrimitiveOperations.terms sourceOperations)) ≅
      ordinary.names ⊗ (ordinary.termObject ⊗ ordinary.termObject) :=
  quotient.mapIso NamePassingGeneratedConstructorCanonicalRemaining.carrierComparison

theorem complete_reference : nameComparison.{k}.inv ≫
    constructorCompiler.map (NamePassingBindingPrimitiveOperations.reference sourceOperations) ≫ termComparison.hom =
      ordinary.reference := by
  have actual := congrArg quotient.map NamePassingGeneratedConstructorCanonicalRemaining.complete_reference
  simp only [quotient.map_comp] at actual
  exact actual.trans whole_reference.symm

theorem complete_abstraction : abstractionComparison.{k}.inv ≫
    constructorCompiler.map (NamePassingBindingPrimitiveOperations.abstraction sourceOperations) ≫ termComparison.hom =
      ordinary.abstraction := by
  have actual := congrArg quotient.map NamePassingGeneratedConstructorCanonical.complete_abstraction
  simp only [quotient.map_comp] at actual
  exact actual.trans whole_abstraction.symm

theorem complete_application : applicationComparison.{k}.inv ≫
    constructorCompiler.map (NamePassingBindingPrimitiveOperations.application sourceOperations) ≫ termComparison.hom =
      ordinary.application := by
  have actual := congrArg quotient.map NamePassingGeneratedConstructorCanonical.complete_application
  simp only [quotient.map_comp] at actual
  exact actual.trans whole_application.symm

theorem complete_definition : definitionComparison.{k}.inv ≫
    constructorCompiler.map (NamePassingBindingPrimitiveOperations.definition sourceOperations) ≫ termComparison.hom =
      ordinary.definition := by
  have actual := congrArg quotient.map NamePassingGeneratedConstructorCanonicalDomains.complete_definition
  simp only [quotient.map_comp] at actual
  exact actual.trans whole_definition.symm

theorem complete_carrier : carrierComparison.{k}.inv ≫
    constructorCompiler.map (NamePassingBindingPrimitiveOperations.carrier sourceOperations) ≫ termComparison.hom =
      ordinary.carrier := by
  have actual := congrArg quotient.map NamePassingGeneratedConstructorCanonicalRemaining.complete_carrier
  simp only [quotient.map_comp] at actual
  exact actual.trans whole_carrier.symm

private theorem mapped_product_comparison (first second : ConstructorSource.{k}) :
    CartesianMonoidalCategory.prodComparison constructorCompiler first second = quotient.map (CartesianMonoidalCategory.prodComparison oldConstructorCompiler first second) := by
  change CartesianMonoidalCategory.prodComparison (oldConstructorCompiler ⋙ quotient) first second = _
  rw [CartesianMonoidalCategory.prodComparison_comp, mapping.productComparison_identity]
  exact Category.comp_id _

private theorem mapped_exponential_comparison (argument result : ConstructorSource.{k}) :
    (expComparison constructorCompiler argument).natTrans.app result =
      quotient.map ((expComparison oldConstructorCompiler argument).natTrans.app result) := by
  change (expComparison (oldConstructorCompiler ⋙ quotient) argument).natTrans.app result = _
  rw [CartesianClosedFunctorCoherence.exponential_composition, mapping.expComparison_identity]
  exact Category.comp_id _

private theorem map_product_comparison_iso (first second : ConstructorSource.{k}) :
    quotient.mapIso (asIso (CartesianMonoidalCategory.prodComparison oldConstructorCompiler first second)) =
      asIso (CartesianMonoidalCategory.prodComparison constructorCompiler first second) := by
  apply Iso.ext
  exact (mapped_product_comparison first second).symm

private theorem map_exponential_comparison_iso (argument result : ConstructorSource.{k}) :
    quotient.mapIso (asIso ((expComparison oldConstructorCompiler argument).natTrans.app result)) =
      asIso ((expComparison constructorCompiler argument).natTrans.app result) := by
  apply Iso.ext
  exact (mapped_exponential_comparison argument result).symm

private theorem map_tensor_iso {first nextFirst second nextSecond : Original.{k}}
    (before : first ≅ nextFirst) (after : second ≅ nextSecond) :
    quotient.mapIso (tensorIso before after) = tensorIso (quotient.mapIso before) (quotient.mapIso after) := by
  apply Iso.ext
  exact mapping.functor_tensorHom before.hom after.hom

private theorem map_function_iso {first nextFirst second nextSecond : Original.{k}}
    (before : first ≅ nextFirst) (after : second ≅ nextSecond) :
    quotient.mapIso (FunctorNormalization.functionIso before after) =
      FunctorNormalization.functionIso (quotient.mapIso before) (quotient.mapIso after) := by
  apply Iso.ext
  change quotient.map ((MonoidalClosed.pre before.inv).app second ≫ (ihom nextFirst).map after.hom) =
    (MonoidalClosed.pre (quotient.map before.inv)).app (quotient.obj second) ≫
      (ihom (quotient.obj nextFirst)).map (quotient.map after.hom)
  rw [quotient.map_comp, mapping.functor_pre, mapping.functor_ihom]

theorem applicationComparison_canonical : applicationComparison.{k} =
    asIso (CartesianMonoidalCategory.prodComparison constructorCompiler
      (NamePassingBindingPrimitiveOperations.terms sourceOperations)
      (NamePassingBindingPrimitiveOperations.names sourceOperations)) ≪≫
        tensorIso termComparison nameComparison := by
  change quotient.mapIso (asIso (CartesianMonoidalCategory.prodComparison oldConstructorCompiler _ _) ≪≫
    tensorIso NamePassingGeneratedConstructorCanonical.termComparison
      NamePassingGeneratedConstructorCanonical.nameComparison) = _
  rw [Functor.mapIso_trans, map_product_comparison_iso, map_tensor_iso]
  rfl

theorem abstractionComparison_canonical : abstractionComparison.{k} =
    asIso ((expComparison constructorCompiler
      (NamePassingBindingPrimitiveOperations.names sourceOperations)).natTrans.app
        (NamePassingBindingPrimitiveOperations.terms sourceOperations)) ≪≫
          FunctorNormalization.functionIso nameComparison termComparison := by
  change quotient.mapIso (asIso ((expComparison oldConstructorCompiler _).natTrans.app _) ≪≫
    FunctorNormalization.functionIso NamePassingGeneratedConstructorCanonical.nameComparison
      NamePassingGeneratedConstructorCanonical.termComparison) = _
  rw [Functor.mapIso_trans, map_exponential_comparison_iso, map_function_iso]
  rfl

theorem definitionComparison_canonical : definitionComparison.{k} =
    asIso (CartesianMonoidalCategory.prodComparison constructorCompiler
      (NamePassingBindingPrimitiveOperations.terms sourceOperations)
      (NamePassingBindingPrimitiveOperations.bodies sourceOperations)) ≪≫
        tensorIso termComparison abstractionComparison := by
  change quotient.mapIso NamePassingGeneratedConstructorCanonicalDomains.definitionComparison = _
  rw [NamePassingGeneratedConstructorCanonicalDomains.definitionComparison_canonical,
    Functor.mapIso_trans, map_product_comparison_iso, map_tensor_iso]
  rfl

theorem pairComparison_canonical : pairComparison.{k} =
    asIso (CartesianMonoidalCategory.prodComparison constructorCompiler
      (NamePassingBindingPrimitiveOperations.terms sourceOperations)
      (NamePassingBindingPrimitiveOperations.terms sourceOperations)) ≪≫
        tensorIso termComparison termComparison := by
  change quotient.mapIso (asIso (CartesianMonoidalCategory.prodComparison oldConstructorCompiler _ _) ≪≫
    tensorIso NamePassingGeneratedConstructorCanonical.termComparison
      NamePassingGeneratedConstructorCanonical.termComparison) = _
  rw [Functor.mapIso_trans, map_product_comparison_iso, map_tensor_iso]
  rfl

theorem carrierComparison_canonical : carrierComparison.{k} =
    asIso (CartesianMonoidalCategory.prodComparison constructorCompiler
      (NamePassingBindingPrimitiveOperations.names sourceOperations)
      (NamePassingBindingPrimitiveOperations.terms sourceOperations ⊗
        NamePassingBindingPrimitiveOperations.terms sourceOperations)) ≪≫
          tensorIso nameComparison pairComparison := by
  change quotient.mapIso NamePassingGeneratedConstructorCanonicalRemaining.carrierComparison = _
  rw [NamePassingGeneratedConstructorCanonicalRemaining.carrierComparison_canonical,
    Functor.mapIso_trans, map_product_comparison_iso, map_tensor_iso]
  rfl

def fullDomainComparison (operator : NamePassing.Presentation.Operator .tm) :=
  eqToIso (Functor.congr_obj complete_compiler_restriction
    (NamePassingBindingClosedConstructorReadout.domain sourceOperations.{k} operator)) ≪≫
      nativeDomainComparison operator

def fullProgramComparison (operator : NamePassing.Presentation.Operator .tm) :=
  eqToIso (Functor.congr_obj complete_compiler_restriction
    (NamePassingBindingPrimitiveOperations.terms sourceOperations.{k})) ≪≫ nativeProgramComparison operator

private theorem equal_route_arrow {C D : Type k} [Category.{k} C] [Category.{k} D]
    (before after : C ⥤ D) (same : before = after) {input output : D}
    {source target : C} (arrow : source ⟶ target)
    (domain : after.obj source ≅ input) (codomain : after.obj target ≅ output)
    (reading : input ⟶ output)
    (whole : domain.inv ≫ after.map arrow ≫ codomain.hom = reading) :
    (eqToIso (Functor.congr_obj same source) ≪≫ domain).inv ≫ before.map arrow ≫
      (eqToIso (Functor.congr_obj same target) ≪≫ codomain).hom = reading := by
  cases same
  simpa only [eqToIso_refl, Iso.refl_trans] using whole

theorem full_compiler_constructor (operator : NamePassing.Presentation.Operator .tm) :
    (fullDomainComparison.{k} operator).inv ≫
      NamePassingGeneratedParallelActionComparison.compiler.functor.map
        (NamePassingGeneratedParallelActionComparison.originalInclusion.map
          (NamePassingBindingClosedConstructorReadout.arrow sourceOperations operator)) ≫
            (fullProgramComparison operator).hom =
              quotient.map (NamePassingGeneratedConstructorComparison.targetValue operator).arrow :=
  equal_route_arrow _ _ complete_compiler_restriction _ _ _ _ (whole_native_constructor operator)

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingGeneratedParallelActionConstructorComparison
