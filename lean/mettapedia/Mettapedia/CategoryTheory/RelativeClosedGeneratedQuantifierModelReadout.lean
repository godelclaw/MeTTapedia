import Mettapedia.CategoryTheory.RelativeClosedGeneratedQuantifierModelClosure
import Mettapedia.CategoryTheory.RelativeClosedGeneratedQuantifierClosureQuantifierReadout

/-!
# Complete quantifier preservation in independently realized targets

Finite origin recovery supplies an actual earlier typed route. Its added
operator has an independent successful reading, which complete operation
uniqueness identifies with the closure's quantifier. The full quotient
image therefore retains both endpoint objects and the whole mapped arrow.
This holds at every closure route, not just at initially supplied arrows.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.CategoryTheory.RelativeClosedGeneratedQuantifier.Closure

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open RelativeClosedSyntax GeneratedCategory Iteration

universe k w z
variable {C : Type k} [Category.{k} C] {stage : Stage C}
variable {D : Type w} [Category.{z} D]
variable [CartesianMonoidalCategory D] [MonoidalClosed D] [HasFiniteLimits D]
variable {quantifiers : InternalPredicateQuantifiedObject.Operations D}
variable (initial : Model quantifiers stage)

def modelOperatorValue (route : Route (signature stage))
    (operation : InternalPredicateFunctionObject.power (operations stage) route.source ⟶
      InternalPredicateFunctionObject.power (operations stage) route.target) :
    RelativeClosedSyntax.Interpretation.ArrowValue D :=
  ⟨(modelDiagram initial).obj (InternalPredicateFunctionObject.power (operations stage) route.source),
    (modelDiagram initial).obj (InternalPredicateFunctionObject.power (operations stage) route.target),
    (modelDiagram initial).map operation⟩

def modelRouteValue (route : Route (signature stage)) :
    RelativeClosedSyntax.Interpretation.ArrowValue D :=
  ⟨(modelDiagram initial).obj route.source, (modelDiagram initial).obj route.target,
    (modelDiagram initial).map (classOf route.arrow)⟩

theorem named_universal_model_read (depth : Nat) (route : Route (stages stage depth).presentation)
    {source target : D} (arrow : source ⟶ target)
    (reading : RawInterpretation.Reads (models initial depth).meanings route.arrow arrow) :
    (modelAssignment initial).evaluateArrow (namedUniversalDiagrams stage depth route).operation.code =
      some (quantifiedValue quantifiers .universal ⟨source, target, arrow⟩) :=
  (congrArg (modelAssignment initial).evaluateArrow (named_universal_code stage depth route)).trans
    ((model_arrow_readout initial (depth + 1)
      ((stages stage depth).quantifierRoute .universal route).arrow.code).trans
        ((models initial depth).new_operator_readout .universal route arrow reading))

theorem named_existential_model_read (depth : Nat) (route : Route (stages stage depth).presentation)
    {source target : D} (arrow : source ⟶ target)
    (reading : RawInterpretation.Reads (models initial depth).meanings route.arrow arrow) :
    (modelAssignment initial).evaluateArrow (namedExistentialDiagrams stage depth route).operation.code =
      some (quantifiedValue quantifiers .existential ⟨source, target, arrow⟩) :=
  (congrArg (modelAssignment initial).evaluateArrow (named_existential_code stage depth route)).trans
    ((model_arrow_readout initial (depth + 1)
      ((stages stage depth).quantifierRoute .existential route).arrow.code).trans
        ((models initial depth).new_operator_readout .existential route arrow reading))

theorem unique_universal_model_read (depth : Nat) (route : Route (stages stage depth).presentation)
    {source target : D} (arrow : source ⟶ target)
    (reading : RawInterpretation.Reads (models initial depth).meanings route.arrow arrow) :
    modelOperatorValue initial (route.translate (stageMap stage depth))
      (universal stage (classOf (route.translate (stageMap stage depth)).arrow)).operation =
        quantifiedValue quantifiers .universal ⟨source, target, arrow⟩ := by
  have unique := universal_operation_unique stage (classOf (route.translate (stageMap stage depth)).arrow)
    ((namedUniversalDiagrams stage depth route).qualification (truth stage))
  have supplied := Option.some.inj
    ((model_complete_readout initial (namedUniversalDiagrams stage depth route).operation).symm.trans
      (named_universal_model_read initial depth route arrow reading))
  exact (congrArg (modelOperatorValue initial (route.translate (stageMap stage depth))) unique.symm).trans supplied

theorem unique_existential_model_read (depth : Nat) (route : Route (stages stage depth).presentation)
    {source target : D} (arrow : source ⟶ target)
    (reading : RawInterpretation.Reads (models initial depth).meanings route.arrow arrow) :
    modelOperatorValue initial (route.translate (stageMap stage depth))
      (existential stage (classOf (route.translate (stageMap stage depth)).arrow)).operation =
        quantifiedValue quantifiers .existential ⟨source, target, arrow⟩ := by
  have unique := existential_operation_unique stage (classOf (route.translate (stageMap stage depth)).arrow)
    ((namedExistentialDiagrams stage depth route).qualification (truth stage))
  have supplied := Option.some.inj
    ((model_complete_readout initial (namedExistentialDiagrams stage depth route).operation).symm.trans
      (named_existential_model_read initial depth route arrow reading))
  exact (congrArg (modelOperatorValue initial (route.translate (stageMap stage depth))) unique.symm).trans supplied

theorem model_route_value_at_stage (depth : Nat) (route : Route (stages stage depth).presentation) :
    modelRouteValue initial (route.translate (stageMap stage depth)) =
      ⟨RelativeClosedSyntax.Interpretation.objectValue
          (models initial depth).meanings (models initial depth).admitted route.source,
        RelativeClosedSyntax.Interpretation.objectValue
          (models initial depth).meanings (models initial depth).admitted route.target,
        RelativeClosedSyntax.Interpretation.rawArrowValue
          (models initial depth).meanings (models initial depth).admitted route.arrow⟩ := by
  have complete := model_complete_readout initial (route.translate (stageMap stage depth)).arrow
  have earlier := (model_arrow_readout initial depth route.arrow.code).trans
    (RelativeClosedSyntax.Interpretation.rawArrowValue_readout
      (models initial depth).meanings (models initial depth).admitted route.arrow)
  exact Option.some.inj (complete.symm.trans earlier)

theorem universal_image (route : Route (signature stage)) :
    modelOperatorValue initial route (universal stage (classOf route.arrow)).operation =
      quantifiedValue quantifiers .universal (modelRouteValue initial route) := by
  obtain ⟨depth, previous, retained⟩ := route_finite stage route
  cases retained
  have complete := unique_universal_model_read initial depth previous
    (RelativeClosedSyntax.Interpretation.rawArrowValue
      (models initial depth).meanings (models initial depth).admitted previous.arrow)
    (RelativeClosedSyntax.Interpretation.rawArrowValue_readout
      (models initial depth).meanings (models initial depth).admitted previous.arrow)
  exact complete.trans (congrArg (quantifiedValue quantifiers .universal)
    (model_route_value_at_stage initial depth previous).symm)

theorem existential_image (route : Route (signature stage)) :
    modelOperatorValue initial route (existential stage (classOf route.arrow)).operation =
      quantifiedValue quantifiers .existential (modelRouteValue initial route) := by
  obtain ⟨depth, previous, retained⟩ := route_finite stage route
  cases retained
  have complete := unique_existential_model_read initial depth previous
    (RelativeClosedSyntax.Interpretation.rawArrowValue
      (models initial depth).meanings (models initial depth).admitted previous.arrow)
    (RelativeClosedSyntax.Interpretation.rawArrowValue_readout
      (models initial depth).meanings (models initial depth).admitted previous.arrow)
  exact complete.trans (congrArg (quantifiedValue quantifiers .existential)
    (model_route_value_at_stage initial depth previous).symm)

end Mettapedia.CategoryTheory.RelativeClosedGeneratedQuantifier.Closure
