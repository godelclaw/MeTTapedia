import Mettapedia.OSLF.NativeTypes.Semantics.Classifier.Model
import Mettapedia.OSLF.NativeTypes.Semantics.Presheaf.CubeNativeSemanticCasts

/-!
# Every generated classifier declaration has its independent native meaning

The common native interpreter reads the independently assembled parameter
contexts and returns the actual membership family or structural-image code.
Full dependent native expressions inherit the common substitution semantics.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.OSLF.NativeTypes.Semantics.Classifier.Realization

open _root_.CategoryTheory Opposite
open Presheaf CubeEnrichment CubeNativeDeclarations
open Mettapedia.OSLF.Framework.ModalHypercube (HSort)
open Mettapedia.TypeTheory
open ContextualLocalUniverses ContextualModelTelescopes NativeLocalTypeFormers
open Calculi.NativeDependent.Refinement
open Families Operations Arguments Model Vectors

universe u
variable {D : CubeEnrichment.Signature} {W : Type u} [Category.{u} W]
variable (operational : D.Carrier → Wᵒᵖ ⥤ Type u)
variable (algebra : StructuralImages.Algebra operational) (vertex : Vertex D)

noncomputable section

theorem code_read {n : Nat} (scope : Scope W n) (carrier : D.Carrier) :
    (model operational algebra vertex).evaluateType scope (codeType carrier n) =
      some (codeAt operational carrier scope.1) :=
  (model operational algebra vertex).evaluate_family scope (.code carrier) Fin.elim0
    ((NativeModel W).toEmpty scope.1) (fun position => Fin.elim0 position)

theorem code_empty_read (carrier : D.Carrier) :
    (model operational algebra vertex).evaluateType Families.emptyScope (codeType carrier 0) =
      some (codeMeaning operational carrier) := by
  have read := code_read operational algebra vertex Families.emptyScope carrier
  have identity : (NativeModel W).toEmpty (Families.emptyScope (W := W)).1 =
      (NativeModel W).toCwf.idS Families.emptyScope.1 :=
    ((NativeModel W).toEmpty_unique _ _).symm
  change (model operational algebra vertex).evaluateType _ (codeType carrier 0) =
    some ((codeMeaning operational carrier).reindex _) at read
  exact read.trans (congrArg some
    ((congrArg (fun map => (codeMeaning operational carrier).reindex map) identity).trans
      (LocalType.reindex_id (C := DisplayedPresheafCwf.presheafCwf W) (codeMeaning operational carrier))))

theorem code_context_read (carrier : D.Carrier) :
    (model operational algebra vertex).evaluateContext (.snoc .nil (codeType carrier 0)) =
      some (codeScope operational carrier) :=
  (model operational algebra vertex).evaluateContext_snoc .nil (codeType carrier 0)
    Families.emptyScope (codeMeaning operational carrier) rfl
    (code_empty_read operational algebra vertex carrier)

theorem typing_context_read (carrier : D.Carrier) :
    (model operational algebra vertex).evaluateContext (CubeNativeDeclarations.typingContext carrier) =
      some (typingScope operational carrier) :=
  (model operational algebra vertex).evaluateContext_snoc _ (codeType carrier 1) _ _
    (code_context_read operational algebra vertex carrier) (code_read operational algebra vertex _ carrier)

theorem sort_substitution {P : Wᵒᵖ ⥤ Type u} (carrier : D.Carrier) (kind : HSort) :
    Value.substitute (K := (NativeModel W).toCwf)
      (⟨codeAt operational carrier Families.emptyScope.1,
        sortValue operational carrier kind⟩ : NativeValue Families.emptyScope.1)
      ((NativeModel W).toEmpty P) = codeValue operational carrier (sortName operational carrier kind) := by
  apply Sigma.ext
  · exact CubeNativeSemanticTelescopes.closed_weaken _ _
  · rfl

theorem sort_read {n : Nat} (scope : Scope W n) (carrier : D.Carrier) (kind : HSort) :
    (model operational algebra vertex).evaluateTerm scope (sortCode carrier kind n) =
      some (codeValue operational carrier (sortName operational carrier kind)) := by
  have read := (model operational algebra vertex).evaluate_primitive scope (.sort carrier kind) Fin.elim0
    ((NativeModel W).toEmpty scope.1) (fun position => Fin.elim0 position)
  exact read.trans (congrArg some (sort_substitution operational carrier kind))

theorem typing_read {n : Nat} (scope : Scope W n) (carrier : D.Carrier)
    (first second : TermExpr (symbols D) n)
    (code type : scope.1 ⟶ Carrier.presheaf operational carrier)
    (firstRead : (model operational algebra vertex).evaluateTerm scope first = some (codeValue operational carrier code))
    (secondRead : (model operational algebra vertex).evaluateTerm scope second = some (codeValue operational carrier type)) :
    (model operational algebra vertex).evaluateType scope (typingType carrier first second) =
      some (typingAt operational carrier code type) := by
  apply (model operational algebra vertex).evaluate_family scope (.typing carrier)
    (Fin.cases first (fun _ => second)) (pairArguments operational carrier code type)
  intro position
  cases position using Fin.cases with
  | zero => exact firstRead.trans (congrArg some (pair_component_zero operational carrier code type).symm)
  | succ position =>
      have last : position = 0 := Fin.eq_zero position
      cases last
      exact secondRead.trans (congrArg some (pair_component_one operational carrier code type).symm)

theorem code_variable_read (carrier : D.Carrier) :
    (model operational algebra vertex).evaluateTerm (codeScope operational carrier) (.var 0) =
      some (codeValue operational carrier (codeVariableName operational carrier)) := by
  apply congrArg some
  apply Sigma.ext
  · rfl
  · rfl

theorem certified_body_read (carrier : D.Carrier) (kind : HSort) :
    (model operational algebra vertex).evaluateType (codeScope operational carrier)
      (typingType carrier (.var 0) (sortCode carrier kind 1)) =
        some (certifiedBody operational carrier kind) :=
  typing_read operational algebra vertex _ carrier _ _ _ _ (code_variable_read operational algebra vertex carrier)
    (sort_read operational algebra vertex _ carrier kind)

theorem certified_empty_read (carrier : D.Carrier) (kind : HSort) :
    (model operational algebra vertex).evaluateType Families.emptyScope
      (certifiedCode carrier kind 0) = some (certifiedMeaning operational carrier kind) :=
  (model operational algebra vertex).evaluate_sigma Families.emptyScope _ _ _ _
    (code_empty_read operational algebra vertex carrier) (certified_body_read operational algebra vertex carrier kind)

theorem certified_read {n : Nat} (scope : Scope W n) (carrier : D.Carrier) (kind : HSort) :
    (model operational algebra vertex).evaluateType scope (certifiedCode carrier kind n) =
      some (CertifiedProjection.certifiedAt operational carrier kind scope.1) := by
  have read := (model operational algebra vertex).evaluateType_rename
    (NativeLocalTypeOperations.products_substitution W) (certifiedCode carrier kind 0)
    scope Families.emptyScope Fin.elim0 (CubeNativeSemanticTelescopes.emptyRenaming scope)
    (certifiedMeaning operational carrier kind) (certified_empty_read operational algebra vertex carrier kind)
  rw [certifiedCode_rename] at read
  exact read

theorem parameter_context_read (declaration : D.Former) :
    (model operational algebra vertex).evaluateContext (CubeNativeDeclarations.parameterContext declaration) =
      some (parameterScope operational declaration) :=
  CubeNativeSemanticTelescopes.vector_read (model operational algebra vertex) _ _
    (fun position => code_empty_read operational algebra vertex (D.input declaration position))

theorem formation_context_read (declaration : D.Former) :
    (model operational algebra vertex).evaluateContext (CubeNativeDeclarations.formationContext vertex declaration) =
      some (formationScope operational vertex declaration) :=
  CubeNativeSemanticTelescopes.vector_read (model operational algebra vertex) _ _
    (fun position => certified_empty_read operational algebra vertex (D.input declaration position)
      (inputSort D vertex declaration position))

def bodySyntax (carrier : D.Carrier) (kind : HSort) (n : Nat) : TypeExpr (symbols D) (n+1) :=
  typingType carrier (.var 0) (sortCode carrier kind (n+1))

theorem bodySyntax_rename (carrier : D.Carrier) (kind : HSort) (n : Nat) :
    (bodySyntax carrier kind 0).rename (liftRenaming (Fin.elim0 : Renaming 0 n)) =
      bodySyntax carrier kind n := by
  unfold bodySyntax typingType
  change TypeExpr.family (S := symbols D) (.typing carrier) _ = TypeExpr.family (S := symbols D) (.typing carrier) _
  apply congrArg (TypeExpr.family (S := symbols D) (.typing carrier))
  funext position
  cases position using Fin.cases with
  | zero => rfl
  | succ => exact sortCode_rename carrier kind _

abbrev bodyAt {n : Nat} (context : Scope W n) (carrier : D.Carrier) (kind : HSort) :
    NativeType (context.snoc (codeAt operational carrier context.1)).1 :=
  (certifiedBody operational carrier kind).reindex
    ((CubeNativeSemanticTelescopes.emptyRenaming context).lift (codeMeaning operational carrier)).arrow

theorem body_read {n : Nat} (context : Scope W n) (carrier : D.Carrier) (kind : HSort) :
    (model operational algebra vertex).evaluateType (context.snoc (codeAt operational carrier context.1))
      (bodySyntax carrier kind n) = some (bodyAt operational context carrier kind) := by
  have read := (model operational algebra vertex).evaluateType_rename
    (NativeLocalTypeOperations.products_substitution W) (bodySyntax carrier kind 0)
    (context.snoc (codeAt operational carrier context.1)) (codeScope operational carrier)
    (liftRenaming (Fin.elim0 : Renaming 0 n))
    ((CubeNativeSemanticTelescopes.emptyRenaming context).lift (codeMeaning operational carrier))
    (certifiedBody operational carrier kind) (certified_body_read operational algebra vertex carrier kind)
  rw [bodySyntax_rename] at read
  exact read

theorem sigma_at {n : Nat} (context : Scope W n) (carrier : D.Carrier) (kind : HSort) :
    (certifiedMeaning operational carrier kind).reindex ((NativeModel W).toEmpty context.1) =
      NativeLocalTypeFormers.sigma (codeAt operational carrier context.1)
        (bodyAt operational context carrier kind) :=
  NativeLocalTypeFormers.sigma_reindex ((NativeModel W).toEmpty context.1)
    (codeMeaning operational carrier) (certifiedBody operational carrier kind)

def sectionAt {n : Nat} (context : Scope W n) (carrier : D.Carrier) (kind : HSort)
    (value : ((certifiedMeaning operational carrier kind).reindex
      ((NativeModel W).toEmpty context.1)).decoded.sections) :
    (NativeLocalTypeFormers.sigma (codeAt operational carrier context.1)
      (bodyAt operational context carrier kind)).decoded.sections :=
  cast (congrArg ((NativeModel W).toCwf.Tm context.1) (sigma_at operational context carrier kind)) value

/-- The independent selected-kind readout and native Sigma first projection
read the same original first component. -/
theorem first_exact {n : Nat} (context : Scope W n) (carrier : D.Carrier) (kind : HSort)
    (value : ((certifiedMeaning operational carrier kind).reindex
      ((NativeModel W).toEmpty context.1)).decoded.sections) :
    NativeLocalTypeOperations.fst (sectionAt operational context carrier kind value) =
      codeSection operational carrier
        (closedReadSection (certifiedMeaning operational carrier kind)
          (certifiedRead operational carrier kind) value ≫ validInclusion operational carrier kind) := by
  apply Functor.sections_ext_iff.mpr
  intro point
  have decoded := NativeLocalTypeOperations.sumTermEquiv_heq
    (codeAt operational carrier context.1) (bodyAt operational context carrier kind)
    (sectionAt operational context carrier kind value)
  have castValue := cast_heq
    (congrArg ((NativeModel W).toCwf.Tm context.1) (sigma_at operational context carrier kind)) value
  have sections := decoded.trans castValue
  have families : DisplayedPresheafSigma.sigmaDisplayed (codeAt operational carrier context.1).decoded
      (bodyAt operational context carrier kind).decoded =
      ((certifiedMeaning operational carrier kind).reindex
        ((NativeModel W).toEmpty context.1)).decoded :=
    (sigmaDecode (codeAt operational carrier context.1) (bodyAt operational context carrier kind)).symm.trans
      (congrArg LocalType.decoded (sigma_at operational context carrier kind)).symm
  have points : HEq
      ((NativeLocalTypeOperations.sumTermEquiv _ _ (sectionAt operational context carrier kind value)).val point)
      (value.val point) := CubeNativeSemanticCasts.sectionValue_heq families sections point
  change _ = ((certifiedDecodeIso operational carrier kind).hom.app ⟨point.1, PUnit.unit⟩
    (value.val point)).1
  have oldDecoded : HEq
      ((certifiedDecodeIso operational carrier kind).hom.app ⟨point.1, PUnit.unit⟩ (value.val point))
      (value.val point) := by
    exact CubeNativeSemanticCasts.castIsoValue_heq
      (sigmaDecode (codeMeaning operational carrier) (certifiedBody operational carrier kind)) _ _
  exact congrArg Sigma.fst (eq_of_heq (points.trans oldDecoded.symm))

/-- Every generated input code projection executes the native first-projection
rule and recovers the corresponding independent certified code argument. -/
theorem codeArgument_read (declaration : D.Former) (position : Fin (D.arity declaration)) :
    (model operational algebra vertex).evaluateTerm (formationScope operational vertex declaration)
      (CubeNativeDeclarations.codeArguments vertex declaration position) =
      some (codeValue operational (D.input declaration position)
        (formationCodeNames operational vertex declaration position)) := by
  let context := formationScope operational vertex declaration
  let carrier := D.input declaration position
  let kind := inputSort D vertex declaration position
  let value := CubeNativeSemanticTelescopes.lookupSection (formationTypes operational vertex declaration) position
  have variableRead : (model operational algebra vertex).evaluateTerm context (.var position) =
      some ⟨(NativeLocalTypeFormers.sigma (codeAt operational carrier context.1)
        (bodyAt operational context carrier kind)), sectionAt operational context carrier kind value⟩ := by
    exact CubeNativeSemanticCasts.variable_cast (model operational algebra vertex) context position _ _ value
      (CubeNativeSemanticTelescopes.lookup_exact (formationTypes operational vertex declaration) position)
      (sigma_at operational context carrier kind)
  have projected := (model operational algebra vertex).evaluate_first context (codeType carrier _)
    (bodySyntax carrier kind _) (codeAt operational carrier context.1)
    (bodyAt operational context carrier kind) (code_read operational algebra vertex context carrier)
    (body_read operational algebra vertex context carrier kind) (.var position)
    (sectionAt operational context carrier kind value) variableRead
  exact projected.trans (congrArg some (congrArg
    (fun first => (⟨codeAt operational carrier context.1, first⟩ : NativeValue context.1))
    (first_exact operational context carrier kind value)))

theorem formerValue_vectorMap {P : Wᵒᵖ ⥤ Type u} (declaration : D.Former)
    (arguments : ∀ position, P ⟶ Carrier.presheaf operational (D.input declaration position)) :
    Value.substitute (K := (NativeModel W).toCwf)
      (⟨formerType operational declaration, formerValue operational algebra vertex declaration⟩ :
        NativeValue (parameterScope operational declaration).1)
      (vectorMap operational (D.input declaration) arguments) =
      codeValue operational (D.output declaration)
        (StructuralImages.formerName operational algebra vertex declaration arguments) := by
  change Value.substitute (K := (NativeModel W).toCwf)
    (codeValue operational (D.output declaration)
      (StructuralImages.formerName operational algebra vertex declaration
        (parameterName operational declaration))) _ = _
  rw [codeValue_substitution, StructuralImages.formerName_substitution]
  have maps : (fun position => vectorMap operational (D.input declaration) arguments ≫
      parameterName operational declaration position) = arguments := by
    funext position
    exact vectorName_map operational (D.input declaration) arguments position
  rw [maps]

theorem former_read {n : Nat} (context : Scope W n) (declaration : D.Former)
    (arguments : Fin (D.arity declaration) → TermExpr (symbols D) n)
    (names : ∀ position, context.1 ⟶ Carrier.presheaf operational (D.input declaration position))
    (reads : ∀ position, (model operational algebra vertex).evaluateTerm context (arguments position) =
      some (codeValue operational (D.input declaration position) (names position))) :
    (model operational algebra vertex).evaluateTerm context (.primitive (.former declaration) arguments) =
      some (codeValue operational (D.output declaration) (StructuralImages.formerName operational algebra vertex declaration names)) := by
  have read := (model operational algebra vertex).evaluate_primitive context (.former declaration) arguments
    (vectorMap operational (D.input declaration) names)
    (fun position => (reads position).trans (congrArg some
      (vectorMap_components operational (D.input declaration) names position).symm))
  exact read.trans (congrArg some (formerValue_vectorMap operational algebra vertex declaration names))

theorem formedCode_read (declaration : D.Former) :
    (model operational algebra vertex).evaluateTerm (formationScope operational vertex declaration)
      (CubeNativeDeclarations.formedCode vertex declaration) =
      some (codeValue operational (D.output declaration) (formationOutputName operational algebra vertex declaration)) :=
  former_read operational algebra vertex _ declaration _ _
    (fun position => codeArgument_read operational algebra vertex declaration position)

theorem formationResult_read (declaration : D.Former) :
    (model operational algebra vertex).evaluateType (formationScope operational vertex declaration)
      (CubeNativeDeclarations.formationResult vertex declaration) =
      some (formationType operational algebra vertex declaration) :=
  typing_read operational algebra vertex _ _ _ _ _ _
    (formedCode_read operational algebra vertex declaration)
    (sort_read operational algebra vertex _ _ _)

theorem starBoxResult_read (carrier : D.Carrier) :
    (model operational algebra vertex).evaluateType Families.emptyScope
      (typingType carrier (sortCode carrier .star 0) (sortCode carrier .box 0)) =
      some (starBoxType operational carrier) :=
  typing_read operational algebra vertex _ _ _ _ _ _
    (sort_read operational algebra vertex _ _ _) (sort_read operational algebra vertex _ _ _)

/-- The actual native declaration model obeys every computed raw header and
result. Its classification fibre is the independently defined operational membership relation. -/
theorem realization : SignatureRealization (model operational algebra vertex) (signature vertex) where
  typeHeader symbol := by
    cases symbol with
    | code => rfl
    | typing carrier => exact typing_context_read operational algebra vertex carrier
  termHeader symbol := by
    cases symbol with
    | sort => rfl
    | starBox => rfl
    | former declaration => exact parameter_context_read operational algebra vertex declaration
    | formation declaration => exact formation_context_read operational algebra vertex declaration
  predicateHeader symbol := nomatch symbol
  termResult symbol := by
    cases symbol with
    | sort carrier _ => exact code_read operational algebra vertex _ carrier
    | former declaration => exact code_read operational algebra vertex _ (D.output declaration)
    | starBox carrier => exact starBoxResult_read operational algebra vertex carrier
    | formation declaration => exact formationResult_read operational algebra vertex declaration

end
end Mettapedia.OSLF.NativeTypes.Semantics.Classifier.Realization
