import Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.Open.SingleRelyRequests
import Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.Open.SingleRelyRequestProjection
import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementScopeResize

/-! # Every generated request lies in the actual lifted continuation fibre -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.Open.SingleRelyCoverage

open _root_.CategoryTheory Opposite
open Mettapedia.TypeTheory Calculi.NativeDependent.Refinement
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
abbrev model := Classifier.Model.model operational algebra vertex
abbrev params : Scope W 2 := ContinuationSemantics.parameterScope operational algebra vertex
  (iface rely target focus kind sort)
abbrev values : Scope W 3 := (params operational algebra vertex rely target focus kind sort).snoc
  (codeAt operational rely (params operational algebra vertex rely target focus kind sort).1)

def valueName : (values operational algebra vertex rely target focus kind sort).1 ⟶ Carrier.presheaf operational rely where
  app _ := TypeCat.ofHom fun point => point.2
  naturality _ _ _ := rfl

abbrev valueProjection := totalProjection
  (codeAt operational rely (params operational algebra vertex rely target focus kind sort).1).decoded
abbrev classifier := SingleRelyEvidence.parameterClassifier vertex operational algebra
  (iface rely target focus kind sort) 0
abbrev memberType := typingAt operational rely (valueName operational algebra vertex rely target focus kind sort)
  (valueProjection operational algebra vertex rely target focus kind sort ≫ classifier operational algebra vertex rely target focus kind sort)
abbrev completeScope : Scope W 4 := (values operational algebra vertex rely target focus kind sort).snoc
  (memberType operational algebra vertex rely target focus kind sort)

abbrev baseMap := ModelSubstitution.ofEvaluated (model operational algebra vertex)
  (pairScope operational rely target kind sort) (params operational algebra vertex rely target focus kind sort)
  (parameterMapping rely target focus kind sort) (parameterMap operational algebra vertex rely target focus kind sort)
  (parameterMap_read operational algebra vertex rely target focus kind sort)

abbrev firstMap := (baseMap operational algebra vertex rely target focus kind sort).liftAlong
  (NativeLocalTypeOperations.products_substitution W)
  (codeAt operational rely (params operational algebra vertex rely target focus kind sort).1)
  (codeAt operational rely (pairScope operational rely target kind sort).1)
  (CubeNativeSemanticTelescopes.closed_weaken _ _)

theorem values_read : (model operational algebra vertex).evaluateContext
    (.snoc (parameters (D := D) (iface rely target focus kind sort)) (codeType rely 2)) =
      some (values operational algebra vertex rely target focus kind sort) :=
  (model operational algebra vertex).evaluateContext_snoc _ _ _ _
    (ContinuationSemantics.parameters_read operational algebra vertex _)
    (Classifier.Realization.code_read operational algebra vertex _ rely)

theorem member_read : (model operational algebra vertex).evaluateType
    (values operational algebra vertex rely target focus kind sort)
    (SingleRelyBeta.originalMembership rely kind) =
      some (memberType operational algebra vertex rely target focus kind sort) := by
  have valueRead : (model operational algebra vertex).evaluateTerm
      (values operational algebra vertex rely target focus kind sort) (.var 0) =
      some (Arguments.codeValue operational rely (valueName operational algebra vertex rely target focus kind sort)) := by
    apply congrArg some
    apply Sigma.ext
    · exact CubeNativeSemanticTelescopes.closed_weaken _ _
    · rfl
  have classifierRead := (model operational algebra vertex).evaluateTerm_rename
    (NativeLocalTypeOperations.products_substitution W)
    (SingleRelyEvidence.parameterClassifierTerm (D := D) (iface rely target focus kind sort) 0)
    (values operational algebra vertex rely target focus kind sort)
    (params operational algebra vertex rely target focus kind sort) Fin.succ
    (ModelRenaming.weaken _ _)
    (Arguments.codeValue operational rely (classifier operational algebra vertex rely target focus kind sort))
    (SingleRelyEvidence.parameterClassifier_read vertex operational algebra (iface rely target focus kind sort) 0)
  rw [Vectors.codeValue_substitution] at classifierRead
  rw [SingleRelyBeta.parameterClassifierTerm_single, classifierValue_rename] at classifierRead
  exact Classifier.Realization.typing_read operational algebra vertex _ rely _ _ _ _ valueRead classifierRead

theorem member_substitution :
    (memberType operational algebra vertex rely target focus kind sort).reindex
      (firstMap operational algebra vertex rely target focus kind sort).arrow =
      membershipMeaning operational algebra vertex rely target kind sort := by
  have read := (model operational algebra vertex).evaluateType_substitute
    (NativeLocalTypeOperations.products_substitution W) (SingleRelyBeta.originalMembership rely kind)
    (valueScope operational rely target kind sort) (values operational algebra vertex rely target focus kind sort)
    (liftSubstitution (parameterMapping rely target focus kind sort))
    (firstMap operational algebra vertex rely target focus kind sort)
    (memberType operational algebra vertex rely target focus kind sort)
    (member_read operational algebra vertex rely target focus kind sort)
  have raw : (SingleRelyBeta.originalMembership (D := D) rely kind).substitute
      (liftSubstitution (parameterMapping rely target focus kind sort)) = membershipType rely kind := by
    rw [SingleRelyBeta.parameterMapping_explicit]
    simp only [SingleRelyBeta.originalMembership, typingType_substitute,
      IndexSyntax.classifierValue_substitute, TermExpr.substitute, membershipType,
      relyTerm, classifierValue_rename]
    rfl
  rw [raw] at read
  exact Option.some.inj (read.symm.trans (membership_read operational algebra vertex rely target kind sort))

abbrev doubleMap := (firstMap operational algebra vertex rely target focus kind sort).liftAlong
  (NativeLocalTypeOperations.products_substitution W)
  (memberType operational algebra vertex rely target focus kind sort)
  (membershipMeaning operational algebra vertex rely target kind sort)
  (member_substitution operational algebra vertex rely target focus kind sort)

theorem complete_read : (model operational algebra vertex).evaluateContext
    (SingleRelyBeta.originalContext (D := D) rely target focus kind sort) =
      some (completeScope operational algebra vertex rely target focus kind sort) :=
  (model operational algebra vertex).evaluateContext_snoc _ _ _ _
    (values_read operational algebra vertex rely target focus kind sort)
    (member_read operational algebra vertex rely target focus kind sort)

theorem scope_resize : Scope.resize (SingleRelyBeta.requestSize vertex rely target focus kind sort)
    (SingleRelyRequests.targetScope operational algebra vertex rely target focus kind sort) =
      completeScope operational algebra vertex rely target focus kind sort := by
  have read := (model operational algebra vertex).evaluateContext_resize
    (SingleRelyBeta.requestSize vertex rely target focus kind sort)
    (ContinuationSemantics.requestSyntax vertex (iface rely target focus kind sort)).scope
  rw [ContinuationSemantics.requests_read] at read
  change (model operational algebra vertex).evaluateContext
    (SingleRelyBeta.normalizedContext vertex rely target focus kind sort) = _ at read
  rw [SingleRelyBeta.normalizedContext_eq] at read
  exact Option.some.inj (read.symm.trans (complete_read operational algebra vertex rely target focus kind sort))

def targetIso : (SingleRelyRequests.targetScope operational algebra vertex rely target focus kind sort).1 ≅
    (completeScope operational algebra vertex rely target focus kind sort).1 :=
  eqToIso (congrArg (fun scope : Scope W 4 => scope.1)
    (scope_resize operational algebra vertex rely target focus kind sort))

private theorem substitution_scope_eq {n m : Nat} (localModel : ModelData (symbols D) W)
    (source : Scope W m) (first second : Scope W n) (same : first = second)
    (mapping : Substitution (symbols D) n m) (f : source.1 ⟶ first.1) (g : source.1 ⟶ second.1)
    (firstRead : localModel.evaluateSubstitution source first mapping = some f)
    (secondRead : localModel.evaluateSubstitution source second mapping = some g) :
    f ≫ eqToHom (congrArg (fun scope : Scope W n => scope.1) same) = g := by
  cases same
  simpa only [eqToHom_refl, Category.comp_id] using Option.some.inj (firstRead.symm.trans secondRead)

/-- The actual generated request map is the canonical double native lift. -/
theorem requestMap_equal :
    SingleRelyRequests.requestMap operational algebra vertex rely target focus kind sort ≫
      (targetIso operational algebra vertex rely target focus kind sort).hom =
      (doubleMap operational algebra vertex rely target focus kind sort).arrow := by
  have read := (model operational algebra vertex).evaluateSubstitution_resize_target
    (SingleRelyBeta.requestSize vertex rely target focus kind sort)
    (evidenceScope operational algebra vertex rely target kind sort)
    (SingleRelyRequests.targetScope operational algebra vertex rely target focus kind sort)
    (SingleRelyBeta.requestMapping vertex rely target focus kind sort)
  rw [SingleRelyRequests.requestMap_read] at read
  have mapping : (fun position => SingleRelyBeta.requestMapping vertex rely target focus kind sort
      (Fin.cast (SingleRelyBeta.requestSize vertex rely target focus kind sort).symm position)) =
      liftSubstitution (liftSubstitution (parameterMapping (D := D) rely target focus kind sort)) := by
    funext position
    simp only [SingleRelyBeta.requestMapping]
    apply congrArg (liftSubstitution (liftSubstitution (parameterMapping (D := D) rely target focus kind sort)))
    apply Fin.ext
    rfl
  rw [mapping] at read
  exact substitution_scope_eq (model operational algebra vertex) _ _ _
    (scope_resize operational algebra vertex rely target focus kind sort) _ _ _ read
    (doubleMap operational algebra vertex rely target focus kind sort).evaluate

theorem firstMap_arrow : (firstMap operational algebra vertex rely target focus kind sort).arrow =
    PresheafNativeContextLifting.lift
      (parameterMap operational algebra vertex rely target focus kind sort)
      (codeAt operational rely (params operational algebra vertex rely target focus kind sort).1)
      (codeAt operational rely (pairScope operational rely target kind sort).1)
      (CubeNativeSemanticTelescopes.closed_weaken _ _) :=
  (baseMap operational algebra vertex rely target focus kind sort).liftAlong_arrow
    (NativeLocalTypeOperations.products_substitution W) _ _ _

theorem doubleMap_arrow : (doubleMap operational algebra vertex rely target focus kind sort).arrow =
    PresheafNativeContextLifting.lift
      (firstMap operational algebra vertex rely target focus kind sort).arrow
      (memberType operational algebra vertex rely target focus kind sort)
      (membershipMeaning operational algebra vertex rely target kind sort)
      (member_substitution operational algebra vertex rely target focus kind sort) :=
  (firstMap operational algebra vertex rely target focus kind sort).liftAlong_arrow
    (NativeLocalTypeOperations.products_substitution W) _ _ _

/-- Both original value and evidence binders preserve their entire fibres. -/
theorem doubleMap_fibre (world : Wᵒᵖ)
    (base : (pairScope operational rely target kind sort).1.obj world)
    (request : (completeScope operational algebra vertex rely target focus kind sort).1.obj world)
    (lyingOver : request.1.1 = (parameterMap operational algebra vertex rely target focus kind sort).app world base) :
    ∃ value : (evidenceScope operational algebra vertex rely target kind sort).1.obj world,
      value.1.1 = base ∧
      (doubleMap operational algebra vertex rely target focus kind sort).arrow.app world value = request := by
  obtain ⟨value, valueOver, valueMap⟩ := PresheafNativeContextLifting.lift_fibre
    (parameterMap operational algebra vertex rely target focus kind sort)
    (codeAt operational rely (params operational algebra vertex rely target focus kind sort).1)
    (codeAt operational rely (pairScope operational rely target kind sort).1)
    (CubeNativeSemanticTelescopes.closed_weaken _ _) world base request.1 lyingOver
  rw [← firstMap_arrow] at valueMap
  obtain ⟨evidence, evidenceOver, evidenceMap⟩ := PresheafNativeContextLifting.lift_fibre
    (firstMap operational algebra vertex rely target focus kind sort).arrow
    (memberType operational algebra vertex rely target focus kind sort)
    (membershipMeaning operational algebra vertex rely target kind sort)
    (member_substitution operational algebra vertex rely target focus kind sort)
    world value request valueMap.symm
  refine ⟨evidence, ?_, ?_⟩
  · exact (congrArg (fun point => point.1) evidenceOver).trans valueOver
  · rw [doubleMap_arrow]
    exact evidenceMap

/-- Coverage refers to the original generated request space, not a separate
list of successfully observed source events. -/
theorem actualMap_fibre (world : Wᵒᵖ)
    (base : (pairScope operational rely target kind sort).1.obj world)
    (request : (SingleRelyRequests.targetScope operational algebra vertex rely target focus kind sort).1.obj world)
    (lyingOver : ((targetIso operational algebra vertex rely target focus kind sort).hom.app world request).1.1 =
      (parameterMap operational algebra vertex rely target focus kind sort).app world base) :
    ∃ value : (evidenceScope operational algebra vertex rely target kind sort).1.obj world,
      value.1.1 = base ∧
      (SingleRelyRequests.requestMap operational algebra vertex rely target focus kind sort).app world value = request := by
  let iso := targetIso operational algebra vertex rely target focus kind sort
  obtain ⟨value, overBase, mapped⟩ := doubleMap_fibre operational algebra vertex rely target focus kind sort
    world base (iso.hom.app world request) lyingOver
  refine ⟨value, overBase, ?_⟩
  have same := (ConcreteCategory.congr_hom
    (NatTrans.congr_app (requestMap_equal operational algebra vertex rely target focus kind sort) world) value).trans mapped
  have cancel (point) : iso.inv.app world (iso.hom.app world point) = point :=
    ConcreteCategory.congr_hom (NatTrans.congr_app iso.hom_inv_id world) point
  exact (cancel _).symm.trans ((congrArg (iso.inv.app world) same).trans (cancel request))

/-- Every actual request above the independently encoded classifiers computes
the supplied target, not merely the canonical request chosen for a test. -/
theorem fibre_target {P : Wᵒᵖ ⥤ Type u}
    (relyName : P ⟶ validPresheaf operational rely kind)
    (targetName : P ⟶ validPresheaf operational target sort)
    (world : Wᵒᵖ) (parameter : P.obj world)
    (request : (SingleRelyRequests.requests operational algebra vertex rely target focus kind sort).values.obj world)
    (lyingOver : (SingleRelyRequests.requests operational algebra vertex rely target focus kind sort).project.app world request =
      (encode operational algebra vertex rely target focus kind sort relyName targetName).app world parameter) :
    (SingleRelyRequests.requests operational algebra vertex rely target focus kind sort).target.app world request =
      (targetName.app world parameter).val := by
  have projection := SingleRelyRequestProjection.project_point operational algebra vertex rely target focus kind sort
    (codeAt operational rely (params operational algebra vertex rely target focus kind sort).1)
    (memberType operational algebra vertex rely target focus kind sort)
    (scope_resize operational algebra vertex rely target focus kind sort) world request
  have overBase : ((targetIso operational algebra vertex rely target focus kind sort).hom.app world request).1.1 =
      (parameterMap operational algebra vertex rely target focus kind sort).app world
        ((pairMap operational rely target kind sort relyName targetName).app world parameter) :=
    projection.symm.trans lyingOver
  obtain ⟨value, baseEq, mapped⟩ := actualMap_fibre operational algebra vertex rely target focus kind sort world
    ((pairMap operational rely target kind sort relyName targetName).app world parameter) request overBase
  have targetRead := ConcreteCategory.congr_hom
    (NatTrans.congr_app (SingleRelyRequests.requestMap_target operational algebra vertex rely target focus kind sort) world) value
  have originalRead := ConcreteCategory.congr_hom
    (NatTrans.congr_app (evidenceTarget_restrict operational algebra vertex rely target kind sort) world) value
  have supplied := ConcreteCategory.congr_hom
    (NatTrans.congr_app (pairMap_target operational algebra vertex rely target kind sort relyName targetName) world) parameter
  change (SingleRelyRequests.requests operational algebra vertex rely target focus kind sort).target.app world
    ((SingleRelyRequests.requestMap operational algebra vertex rely target focus kind sort).app world value) = _ at targetRead
  rw [mapped] at targetRead
  exact targetRead.trans (originalRead.symm.trans
    ((congrArg ((targetClassifier operational algebra vertex rely target kind sort).app world) baseEq).trans supplied))

end
end Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.Open.SingleRelyCoverage
