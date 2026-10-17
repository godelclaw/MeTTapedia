import Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.Open.SingleRelyBeta
import Mettapedia.TypeTheory.PresheafNativeContextLifting

/-!
# Actual generated requests for a constant dependent continuation

The original generated request scope is connected to the independently
constructed value-and-evidence scope by its typed native substitution.
The generated target computes through the original native beta rules.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.Open.SingleRelyRequests

open _root_.CategoryTheory Opposite
open Mettapedia.TypeTheory
open Calculi.NativeDependent.Refinement
open NativeLocalTypeFormers ContextualLocalUniverses ContextualModelTelescopes
open DisplayedPresheafComprehension
open Mettapedia.OSLF.Framework.ModalHypercube (HSort)
open Mettapedia.OSLF.NativeTypes.Semantics
open Presheaf CubeEnrichment CubeNativeDeclarations
open Classifier Families Operations CertifiedProjection
open SingleRelyParameters

universe u
variable {D : CubeEnrichment.Signature} {W : Type u} [Category.{u} W]
variable (operational : D.Carrier → Wᵒᵖ ⥤ Type u)
    (algebra : StructuralImages.Algebra operational) (vertex : Vertex D)
variable (rely target focus : D.Carrier) (kind sort : HSort)

noncomputable section

attribute [local irreducible] Classifier.Model.model

abbrev iface := SingleRelyParameters.interface rely target focus kind sort
abbrev requests := ContinuationSemantics.requests operational algebra vertex (iface rely target focus kind sort)
abbrev sourceScope := evidenceScope operational algebra vertex rely target kind sort
abbrev targetScope := ContinuationSemantics.requestScope operational algebra vertex (iface rely target focus kind sort)
abbrev model := Classifier.Model.model operational algebra vertex

def requestMap : (sourceScope operational algebra vertex rely target kind sort).1 ⟶
    (targetScope operational algebra vertex rely target focus kind sort).1 :=
  Classical.choose
    (((SingleRelyBeta.requestTyped vertex rely target focus kind sort).native_sound
      (model operational algebra vertex) (Classifier.Realization.realization operational algebra vertex)).substitutionAt
      (sourceScope operational algebra vertex rely target kind sort)
      (targetScope operational algebra vertex rely target focus kind sort)
      (evidence_read operational algebra vertex rely target kind sort)
      (ContinuationSemantics.requests_read operational algebra vertex (iface rely target focus kind sort)))

theorem requestMap_read :
    (model operational algebra vertex).evaluateSubstitution
      (sourceScope operational algebra vertex rely target kind sort)
      (targetScope operational algebra vertex rely target focus kind sort)
      (SingleRelyBeta.requestMapping vertex rely target focus kind sort) =
        some (requestMap operational algebra vertex rely target focus kind sort) :=
  Classical.choose_spec
    (((SingleRelyBeta.requestTyped vertex rely target focus kind sort).native_sound
      (model operational algebra vertex) (Classifier.Realization.realization operational algebra vertex)).substitutionAt
      (sourceScope operational algebra vertex rely target kind sort)
      (targetScope operational algebra vertex rely target focus kind sort)
      (evidence_read operational algebra vertex rely target kind sort)
      (ContinuationSemantics.requests_read operational algebra vertex (iface rely target focus kind sort)))


private def originalMap : ModelSubstitution (model operational algebra vertex)
    (sourceScope operational algebra vertex rely target kind sort)
    (pairScope operational rely target kind sort) (fun position => .var position.succ.succ) where
  arrow := originalProjection operational algebra vertex rely target kind sort
  readout position := by
    change some (Value.substitute (K := (NativeModel W).toCwf)
      (Value.substitute (K := (NativeModel W).toCwf)
        ((pairScope operational rely target kind sort).2.lookup position)
        (valueProjection operational rely target kind sort))
      (evidenceProjection operational algebra vertex rely target kind sort)) = _
    exact congrArg some (Value.substitute_composition (K := (NativeModel W).toCwf)
      ((pairScope operational rely target kind sort).2.lookup position)
      (valueProjection operational rely target kind sort)
      (evidenceProjection operational algebra vertex rely target kind sort)).symm


private theorem projection_substitute :
    composeSubstitution (ContinuationSemantics.requestSyntax vertex (iface rely target focus kind sort)).projection
      (SingleRelyBeta.requestMapping vertex rely target focus kind sort) =
    composeSubstitution (parameterMapping rely target focus kind sort)
      (fun position => (.var position.succ.succ : TermExpr (symbols D) 4)) := by
  funext position
  unfold composeSubstitution
  change ((SingleRelyBeta.generatedSyntax vertex rely target focus kind sort).projection position).substitute
      (fun entry => (liftSubstitution (liftSubstitution (parameterMapping rely target focus kind sort)))
        (Fin.cast (SingleRelyBeta.requestSize vertex rely target focus kind sort) entry)) = _
  rw [← SingleRelyBeta.resizeTerm_substitute]
  change (SingleRelyBeta.normalizedProjection vertex rely target focus kind sort position).substitute
    (liftSubstitution (liftSubstitution (parameterMapping rely target focus kind sort))) = _
  rw [SingleRelyBeta.normalizedProjection_eq]
  simp only [TermExpr.substitute, liftSubstitution_succ, TermExpr.rename_comp,
    TermExpr.substitute_variables]
  rfl

/-- The actual request lies over the original encoded modal parameters. -/
theorem requestMap_project :
    requestMap operational algebra vertex rely target focus kind sort ≫
      (requests operational algebra vertex rely target focus kind sort).project =
    originalProjection operational algebra vertex rely target kind sort ≫
      parameterMap operational algebra vertex rely target focus kind sort := by
  let projected := (ModelSubstitution.ofEvaluated (model operational algebra vertex)
    (targetScope operational algebra vertex rely target focus kind sort)
    (ContinuationSemantics.parameterScope operational algebra vertex (iface rely target focus kind sort))
    (ContinuationSemantics.requestSyntax vertex (iface rely target focus kind sort)).projection
    (requests operational algebra vertex rely target focus kind sort).project
    (ContinuationSemantics.projection_read operational algebra vertex (iface rely target focus kind sort))).compose
      (NativeLocalTypeOperations.products_substitution W)
      (ModelSubstitution.ofEvaluated _ _ _ _ _ (requestMap_read operational algebra vertex rely target focus kind sort))
  let original := (ModelSubstitution.ofEvaluated (model operational algebra vertex)
    (pairScope operational rely target kind sort)
    (ContinuationSemantics.parameterScope operational algebra vertex (iface rely target focus kind sort))
    (parameterMapping rely target focus kind sort)
    (parameterMap operational algebra vertex rely target focus kind sort)
    (parameterMap_read operational algebra vertex rely target focus kind sort)).compose
      (NativeLocalTypeOperations.products_substitution W)
      (originalMap operational algebra vertex rely target kind sort)
  have mapped := projected.evaluate
  change (model operational algebra vertex).evaluateSubstitution
    (sourceScope operational algebra vertex rely target kind sort)
    (ContinuationSemantics.parameterScope operational algebra vertex (iface rely target focus kind sort))
    (composeSubstitution (ContinuationSemantics.requestSyntax vertex (iface rely target focus kind sort)).projection
      (SingleRelyBeta.requestMapping vertex rely target focus kind sort)) =
      some (requestMap operational algebra vertex rely target focus kind sort ≫
        (requests operational algebra vertex rely target focus kind sort).project) at mapped
  rw [projection_substitute] at mapped
  exact Option.some.inj (mapped.symm.trans original.evaluate)

theorem requestMap_rely :
    requestMap operational algebra vertex rely target focus kind sort ≫
      (requests operational algebra vertex rely target focus kind sort).relies 0 =
    evidenceProjection operational algebra vertex rely target kind sort ≫
      valueName operational rely target kind sort := by
  have original := (model operational algebra vertex).evaluateTerm_rename
    (NativeLocalTypeOperations.products_substitution W) (.var 0)
    (sourceScope operational algebra vertex rely target kind sort)
    (valueScope operational rely target kind sort) Fin.succ (ModelRenaming.weaken _ _)
    (Arguments.codeValue operational rely (valueName operational rely target kind sort))
    (valueName_read operational algebra vertex rely target kind sort)
  have read := (model operational algebra vertex).evaluateTerm_substitute
    (NativeLocalTypeOperations.products_substitution W)
    (ContinuationSemantics.relyValueTerm vertex (iface rely target focus kind sort) 0)
    (sourceScope operational algebra vertex rely target kind sort)
    (targetScope operational algebra vertex rely target focus kind sort)
    (SingleRelyBeta.requestMapping vertex rely target focus kind sort)
    (ModelSubstitution.ofEvaluated _ _ _ _ _ (requestMap_read operational algebra vertex rely target focus kind sort))
    (Arguments.codeValue operational rely ((requests operational algebra vertex rely target focus kind sort).relies 0))
    (ContinuationSemantics.relyValue_evaluates operational algebra vertex (iface rely target focus kind sort) 0)
  rw [SingleRelyBeta.rely_substitute, Vectors.codeValue_substitution] at read
  rw [Vectors.codeValue_substitution] at original
  exact Vectors.codeValue_injective operational rely
    (Option.some.inj (read.symm.trans original))

/-- The actual generated continuation, applied to the actual generated
request, returns the supplied target classifier. -/
theorem requestMap_target :
    requestMap operational algebra vertex rely target focus kind sort ≫
      (requests operational algebra vertex rely target focus kind sort).target =
        evidenceTarget operational algebra vertex rely target kind sort := by
  let original := ContinuationSemantics.targetSection operational algebra vertex (iface rely target focus kind sort)
  have read := (model operational algebra vertex).evaluateTerm_substitute
    (NativeLocalTypeOperations.products_substitution W)
    (ContinuationSemantics.requestSyntax vertex (iface rely target focus kind sort)).output
    (sourceScope operational algebra vertex rely target kind sort)
    (targetScope operational algebra vertex rely target focus kind sort)
    (SingleRelyBeta.requestMapping vertex rely target focus kind sort)
    (ModelSubstitution.ofEvaluated _ _ _ _ _ (requestMap_read operational algebra vertex rely target focus kind sort))
    ⟨certifiedAt operational target sort (targetScope operational algebra vertex rely target focus kind sort).1, original⟩
    (ContinuationSemantics.target_evaluates operational algebra vertex (iface rely target focus kind sort))
  obtain ⟨value, applied, returned⟩ :=
    (((SingleRelyBeta.generated_target_beta vertex rely target focus kind sort).native_sound
      (model operational algebra vertex) (Classifier.Realization.realization operational algebra vertex)).termEqAt
      (sourceScope operational algebra vertex rely target kind sort)
      (certifiedAt operational target sort (sourceScope operational algebra vertex rely target kind sort).1)
      (evidence_read operational algebra vertex rely target kind sort)
      (Classifier.Realization.certified_read operational algebra vertex _ target sort))
  have related := Option.some.inj (read.symm.trans
    (applied.trans (returned.symm.trans (evidenceTarget_read operational algebra vertex rely target kind sort))))
  exact certifiedRead_substitution operational target sort original
    (evidenceTargetSection operational algebra vertex rely target kind sort)
    (requestMap operational algebra vertex rely target focus kind sort) related

def canonicalRequest {P : Wᵒᵖ ⥤ Type u}
    (relyName : P ⟶ validPresheaf operational rely kind)
    (targetName : P ⟶ validPresheaf operational target sort)
    (world : Wᵒᵖ) (parameter : P.obj world) (value : (operational rely).obj world)
    (member : Code.Member (.operational value) (relyName.app world parameter).val) :
    (targetScope operational algebra vertex rely target focus kind sort).1.obj world :=
  (requestMap operational algebra vertex rely target focus kind sort).app world
    (inputPoint operational algebra vertex rely target kind sort relyName targetName world parameter value member)


theorem canonicalRequest_project {P : Wᵒᵖ ⥤ Type u}
    (relyName : P ⟶ validPresheaf operational rely kind)
    (targetName : P ⟶ validPresheaf operational target sort)
    (world : Wᵒᵖ) (parameter : P.obj world) (value : (operational rely).obj world)
    (member : Code.Member (.operational value) (relyName.app world parameter).val) :
    (requests operational algebra vertex rely target focus kind sort).project.app world
      (canonicalRequest operational algebra vertex rely target focus kind sort
        relyName targetName world parameter value member) =
      (encode operational algebra vertex rely target focus kind sort relyName targetName).app world parameter :=
  ConcreteCategory.congr_hom
    (NatTrans.congr_app (requestMap_project operational algebra vertex rely target focus kind sort) world)
    (inputPoint operational algebra vertex rely target kind sort relyName targetName world parameter value member)

theorem canonicalRequest_rely {P : Wᵒᵖ ⥤ Type u}
    (relyName : P ⟶ validPresheaf operational rely kind)
    (targetName : P ⟶ validPresheaf operational target sort)
    (world : Wᵒᵖ) (parameter : P.obj world) (value : (operational rely).obj world)
    (member : Code.Member (.operational value) (relyName.app world parameter).val) :
    ((requests operational algebra vertex rely target focus kind sort).relies 0).app world
      (canonicalRequest operational algebra vertex rely target focus kind sort
        relyName targetName world parameter value member) = .operational value :=
  ConcreteCategory.congr_hom
    (NatTrans.congr_app (requestMap_rely operational algebra vertex rely target focus kind sort) world)
    (inputPoint operational algebra vertex rely target kind sort relyName targetName world parameter value member)

theorem canonicalRequest_target {P : Wᵒᵖ ⥤ Type u}
    (relyName : P ⟶ validPresheaf operational rely kind)
    (targetName : P ⟶ validPresheaf operational target sort)
    (world : Wᵒᵖ) (parameter : P.obj world) (value : (operational rely).obj world)
    (member : Code.Member (.operational value) (relyName.app world parameter).val) :
    (requests operational algebra vertex rely target focus kind sort).target.app world
      (canonicalRequest operational algebra vertex rely target focus kind sort
        relyName targetName world parameter value member) = (targetName.app world parameter).val :=
  (ConcreteCategory.congr_hom
    (NatTrans.congr_app (requestMap_target operational algebra vertex rely target focus kind sort) world)
    (inputPoint operational algebra vertex rely target kind sort relyName targetName world parameter value member)).trans
      (inputPoint_target operational algebra vertex rely target kind sort relyName targetName world parameter value member)

end
end Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.Open.SingleRelyRequests
