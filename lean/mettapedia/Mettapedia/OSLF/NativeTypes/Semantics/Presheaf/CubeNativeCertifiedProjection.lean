import Mettapedia.OSLF.NativeTypes.Semantics.Presheaf.CubeNativeSemanticCasts

/-!
# Certified native Sigma projection retains the independent code value

The generated formation premises use actual native dependent pairs. The full
native first-projection evaluator is compared to the independently built
selected-kind readout, including its weakening into arbitrary contexts.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.OSLF.NativeTypes.Semantics.Presheaf.CubeNativeCertifiedProjection

open _root_.CategoryTheory Opposite
open CubeEnrichment
open Mettapedia.OSLF.Framework.ModalHypercube (HSort)
open Mettapedia.TypeTheory
open ContextualLocalUniverses ContextualModelTelescopes NativeLocalTypeFormers
open Calculi.NativeDependent.Refinement
open CubeNativeDeclarations CubeNativeSemanticFamilies CubeNativeSemanticOperations
open CubeNativeSemanticArguments CubeNativePresheafModel CubeNativePresheafReadout

universe u
variable {D : CubeEnrichment.Signature} {W : Type u} [Category.{u} W]
variable (operational : D.Carrier → Wᵒᵖ ⥤ Type u) (vertex : Vertex D)

noncomputable section

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
  (certifiedBody operational vertex carrier kind).reindex
    ((CubeNativeSemanticTelescopes.emptyRenaming context).lift (codeMeaning operational carrier)).arrow

theorem body_read {n : Nat} (context : Scope W n) (carrier : D.Carrier) (kind : HSort) :
    (model operational vertex).evaluateType (context.snoc (codeAt operational carrier context.1))
      (bodySyntax carrier kind n) = some (bodyAt operational vertex context carrier kind) := by
  have read := (model operational vertex).evaluateType_rename
    (NativeLocalTypeOperations.products_substitution W) (bodySyntax carrier kind 0)
    (context.snoc (codeAt operational carrier context.1)) (codeScope operational carrier)
    (liftRenaming (Fin.elim0 : Renaming 0 n))
    ((CubeNativeSemanticTelescopes.emptyRenaming context).lift (codeMeaning operational carrier))
    (certifiedBody operational vertex carrier kind) (certified_body_read operational vertex carrier kind)
  rw [bodySyntax_rename] at read
  exact read

theorem sigma_at {n : Nat} (context : Scope W n) (carrier : D.Carrier) (kind : HSort) :
    (certifiedMeaning operational vertex carrier kind).reindex ((NativeModel W).toEmpty context.1) =
      NativeLocalTypeFormers.sigma (codeAt operational carrier context.1)
        (bodyAt operational vertex context carrier kind) :=
  NativeLocalTypeFormers.sigma_reindex ((NativeModel W).toEmpty context.1)
    (codeMeaning operational carrier) (certifiedBody operational vertex carrier kind)

def sectionAt {n : Nat} (context : Scope W n) (carrier : D.Carrier) (kind : HSort)
    (value : ((certifiedMeaning operational vertex carrier kind).reindex
      ((NativeModel W).toEmpty context.1)).decoded.sections) :
    (NativeLocalTypeFormers.sigma (codeAt operational carrier context.1)
      (bodyAt operational vertex context carrier kind)).decoded.sections :=
  cast (congrArg ((NativeModel W).toCwf.Tm context.1) (sigma_at operational vertex context carrier kind)) value

/-- The independent selected-kind readout and native Sigma first projection
read the same original first component. -/
theorem first_exact {n : Nat} (context : Scope W n) (carrier : D.Carrier) (kind : HSort)
    (value : ((certifiedMeaning operational vertex carrier kind).reindex
      ((NativeModel W).toEmpty context.1)).decoded.sections) :
    NativeLocalTypeOperations.fst (sectionAt operational vertex context carrier kind value) =
      codeSection operational carrier
        (closedReadSection (certifiedMeaning operational vertex carrier kind)
          (certifiedRead operational vertex carrier kind) value ≫ validInclusion operational vertex carrier kind) := by
  apply Functor.sections_ext_iff.mpr
  intro point
  have decoded := NativeLocalTypeOperations.sumTermEquiv_heq
    (codeAt operational carrier context.1) (bodyAt operational vertex context carrier kind)
    (sectionAt operational vertex context carrier kind value)
  have castValue := cast_heq
    (congrArg ((NativeModel W).toCwf.Tm context.1) (sigma_at operational vertex context carrier kind)) value
  have sections := decoded.trans castValue
  have families : DisplayedPresheafSigma.sigmaDisplayed (codeAt operational carrier context.1).decoded
      (bodyAt operational vertex context carrier kind).decoded =
      ((certifiedMeaning operational vertex carrier kind).reindex
        ((NativeModel W).toEmpty context.1)).decoded :=
    (sigmaDecode (codeAt operational carrier context.1) (bodyAt operational vertex context carrier kind)).symm.trans
      (congrArg LocalType.decoded (sigma_at operational vertex context carrier kind)).symm
  have points : HEq
      ((NativeLocalTypeOperations.sumTermEquiv _ _ (sectionAt operational vertex context carrier kind value)).val point)
      (value.val point) := CubeNativeSemanticCasts.sectionValue_heq families sections point
  change _ = ((certifiedDecodeIso operational vertex carrier kind).hom.app ⟨point.1, PUnit.unit⟩
    (value.val point)).1
  have oldDecoded : HEq
      ((certifiedDecodeIso operational vertex carrier kind).hom.app ⟨point.1, PUnit.unit⟩ (value.val point))
      (value.val point) := by
    exact CubeNativeSemanticCasts.castIsoValue_heq
      (sigmaDecode (codeMeaning operational carrier) (certifiedBody operational vertex carrier kind)) _ _
  exact congrArg Sigma.fst (eq_of_heq (points.trans oldDecoded.symm))

/-- Every generated input code projection executes the native first-projection
rule and recovers the corresponding independent certified code argument. -/
theorem codeArgument_read (declaration : D.Former) (position : Fin (D.arity declaration)) :
    (model operational vertex).evaluateTerm (formationScope operational vertex declaration)
      (CubeNativeDeclarations.codeArguments vertex declaration position) =
      some (codeValue operational (D.input declaration position)
        (formationCodeNames operational vertex declaration position)) := by
  let context := formationScope operational vertex declaration
  let carrier := D.input declaration position
  let kind := inputSort D vertex declaration position
  let value := CubeNativeSemanticTelescopes.lookupSection (formationTypes operational vertex declaration) position
  have variableRead : (model operational vertex).evaluateTerm context (.var position) =
      some ⟨(NativeLocalTypeFormers.sigma (codeAt operational carrier context.1)
        (bodyAt operational vertex context carrier kind)), sectionAt operational vertex context carrier kind value⟩ := by
    exact CubeNativeSemanticCasts.variable_cast (model operational vertex) context position _ _ value
      (CubeNativeSemanticTelescopes.lookup_exact (formationTypes operational vertex declaration) position)
      (sigma_at operational vertex context carrier kind)
  have projected := (model operational vertex).evaluate_first context (codeType carrier _)
    (bodySyntax carrier kind _) (codeAt operational carrier context.1)
    (bodyAt operational vertex context carrier kind) (code_read operational vertex context carrier)
    (body_read operational vertex context carrier kind) (.var position)
    (sectionAt operational vertex context carrier kind value) variableRead
  exact projected.trans (congrArg some (congrArg
    (fun first => (⟨codeAt operational carrier context.1, first⟩ : NativeValue context.1))
    (first_exact operational vertex context carrier kind value)))

end

end Mettapedia.OSLF.NativeTypes.Semantics.Presheaf.CubeNativeCertifiedProjection
