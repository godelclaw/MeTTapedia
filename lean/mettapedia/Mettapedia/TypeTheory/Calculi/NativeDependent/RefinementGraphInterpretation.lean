import Mettapedia.OSLF.NativeTypes.Semantics.Presheaf.NativeEqualityComparison
import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementRenamingEvaluation

/-!
# Exact graph comprehension in the native dependent evaluator

The generated logical graph uses Leibniz equality. Actual native evaluation
computes the independent diagonal between the generic candidate and the
weakened supplied operation section. Its comprehension therefore retains
exactly the original carrier inhabitants satisfying that graph.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement

open _root_.CategoryTheory
open Mettapedia.TypeTheory NativeLocalTypeFormers ContextualLocalUniverses
open DisplayedPresheafTransport DisplayedPresheafComprehension ContextualModelTelescopes
open Mettapedia.OSLF.NativeTypes.Generation
open Mettapedia.OSLF.NativeTypes.Semantics.Presheaf.NativeEqualityComparison

universe u v
variable {C : Type u} [Category.{u} C] {S : Symbols.{v}} {P : Cᵒᵖ ⥤ Type u}

def graphComprehension {n : Nat} (carrier : TypeExpr S n) (operation : TermExpr S n) : TypeExpr S n :=
  .comprehension carrier
    (NativeEquality.equal (carrier.rename Fin.succ) (.var 0) (operation.rename Fin.succ))

noncomputable def graphPredicate (A : NativeType P) (operation : A.decoded.sections) :
    Subfunctor (totalSpace A.decoded) :=
  diagonal (A.reindex (totalProjection A.decoded))
    ((NativeModel C).toCwf.vz A)
    (ContextualLocalUniverses.substituteTerm (type := A) operation (totalProjection A.decoded))

noncomputable def graphNative (A : NativeType P) (operation : A.decoded.sections) : NativeType P :=
  PresheafNativeStableRefinement.chosen A (graphPredicate A operation)

set_option backward.isDefEq.respectTransparency false in
theorem ModelData.evaluate_graphComprehension (model : ModelData S C) {n : Nat} (scope : Scope C n)
    (carrier : TypeExpr S n) (operation : TermExpr S n) (A : NativeType scope.1)
    (value : A.decoded.sections)
    (carrierRead : model.evaluateType scope carrier = some A)
    (operationRead : model.evaluateTerm scope operation = some ⟨A, value⟩) :
    model.evaluateType scope (graphComprehension carrier operation) = some (graphNative A value) := by
  have carrierWeak := model.evaluateType_rename
    (NativeLocalTypeOperations.products_substitution C) carrier (scope.snoc A) scope Fin.succ
    (ModelRenaming.weaken scope A) A carrierRead
  have operationWeak := model.evaluateTerm_rename
    (NativeLocalTypeOperations.products_substitution C) operation (scope.snoc A) scope Fin.succ
    (ModelRenaming.weaken scope A) ⟨A, value⟩ operationRead
  have genericRead : model.evaluateTerm (scope.snoc A) (.var 0) =
      some ⟨A.reindex (totalProjection A.decoded), (NativeModel C).toCwf.vz A⟩ := rfl
  have predicateRead := evaluate_equal model (scope.snoc A) (carrier.rename Fin.succ)
    (.var 0) (operation.rename Fin.succ) (A.reindex (totalProjection A.decoded))
    ((NativeModel C).toCwf.vz A)
    (ContextualLocalUniverses.substituteTerm (type := A) value (totalProjection A.decoded))
    carrierWeak genericRead operationWeak
  exact model.evaluate_comprehension scope carrier _ A (graphPredicate A value) carrierRead predicateRead

noncomputable def graphDecodeIso (A : NativeType P) (operation : A.decoded.sections) :
    (show DisplayedFamily P from (graphNative A operation).decoded) ≅
      PresheafNativePredicateRefinement.displayed A.decoded (graphPredicate A operation) :=
  PresheafNativeStableRefinement.decodeIso A (graphPredicate A operation)

set_option backward.isDefEq.respectTransparency false in
theorem graphPredicate_member (A : NativeType P) (operation : A.decoded.sections)
    (X : Cᵒᵖ) (parameter : P.obj X) (candidate : A.decoded.obj ⟨X, parameter⟩) :
    (⟨parameter, candidate⟩ : (totalSpace A.decoded).obj X) ∈ (graphPredicate A operation).obj X ↔
      candidate = operation.val ⟨X, parameter⟩ := by
  let point : (totalSpace A.decoded).Elements := ⟨X, ⟨parameter, candidate⟩⟩
  have generic : HEq (((NativeModel C).toCwf.vz A).val point) candidate := by
    change HEq ((ContextualLocalUniverses.genericVariable A).val point) candidate
    exact DisplayedPresheafCwf.sectionCast_value_heq
      (A.decoded_reindex (totalProjection A.decoded)).symm
      (DisplayedPresheafCwf.presheafVariable A.decoded) point
  have weakened := NativeLocalTypeOperations.substituteTerm_value A operation
    (totalProjection A.decoded) point
  constructor
  · intro member
    exact eq_of_heq (generic.symm.trans ((heq_of_eq member).trans weakened))
  · intro same
    exact eq_of_heq (generic.trans ((heq_of_eq same).trans weakened.symm))

/-- Every generated graph inhabitant is exactly the original carrier value
equal to the operation's result at that complete parameter point. -/
noncomputable def graphFibreEquiv (A : NativeType P) (operation : A.decoded.sections)
    (point : P.Elements) :
    (graphNative A operation).decoded.obj point ≃
      {candidate : A.decoded.obj point | candidate = operation.val point} :=
  ((graphDecodeIso A operation).app point).toEquiv.trans
    (Equiv.subtypeEquivRight (fun candidate =>
      graphPredicate_member A operation point.1 point.2 candidate))

end Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement
