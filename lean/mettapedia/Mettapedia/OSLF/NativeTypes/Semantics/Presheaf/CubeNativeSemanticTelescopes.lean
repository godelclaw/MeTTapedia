import Mettapedia.OSLF.NativeTypes.Semantics.Presheaf.CubeNativeSemanticFamilies
import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementRenamingEvaluation

/-!
# Independent finite semantic parameter telescopes

Closed semantic parameter types are weakened along the actual terminal maps.
Every variable has its original closed family, and the raw telescope parser
is compared to this construction by the full native renaming theorem.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.OSLF.NativeTypes.Semantics.Presheaf.CubeNativeSemanticTelescopes

open _root_.CategoryTheory
open Mettapedia.TypeTheory
open NativeLocalTypeFormers ContextualLocalUniverses ContextualModelTelescopes
open Calculi.NativeDependent.Refinement

universe u v
variable {W : Type u} [Category.{u} W]

abbrev emptyScope : Scope W 0 := Scope.nil W

def vectorScope : {n : Nat} → (Fin n → NativeType (emptyScope (W := W)).1) → Scope W n
  | 0, _ => emptyScope
  | n + 1, types =>
      let previous := vectorScope (fun position : Fin n => types position.succ)
      previous.snoc ((types 0).reindex ((NativeModel W).toEmpty previous.1))

/-- The terminal map is the actual interpretation of the unique empty
renaming; no interpretation of a type is supplied by this map. -/
def emptyRenaming {n : Nat} (scope : Scope W n) :
    ModelRenaming scope (emptyScope (W := W)) (Fin.elim0 : Renaming 0 n) where
  arrow := (NativeModel W).toEmpty scope.1
  readout position := Fin.elim0 position

theorem closed_weaken {P Q : Wᵒᵖ ⥤ Type u}
    (type : NativeType (emptyScope (W := W)).1) (arrow : Q ⟶ P) :
    (type.reindex ((NativeModel W).toEmpty P)).reindex arrow =
      type.reindex ((NativeModel W).toEmpty Q) := by
  rw [← LocalType.reindex_comp]
  exact congrArg (fun map => type.reindex map)
    ((NativeModel W).toEmpty_unique _ _)

/-- Ordered lookup retains the original type of each authored parameter. -/
theorem lookup_type {n : Nat} (types : Fin n → NativeType (emptyScope (W := W)).1)
    (position : Fin n) :
    ((vectorScope types).2.lookup position).1 =
      (types position).reindex ((NativeModel W).toEmpty (vectorScope types).1) := by
  induction n with
  | zero => exact Fin.elim0 position
  | succ n hypotheses =>
      cases position using Fin.cases with
      | zero => exact closed_weaken (types 0) _
      | succ position =>
          change (((vectorScope (fun position : Fin n => types position.succ)).2.lookup position).1.reindex _)=_
          rw [hypotheses (fun position : Fin n => types position.succ) position]
          exact closed_weaken (types position.succ) _

def lookupSection {n : Nat} (types : Fin n → NativeType (emptyScope (W := W)).1)
    (position : Fin n) :
    ((types position).reindex ((NativeModel W).toEmpty (vectorScope types).1)).decoded.sections :=
  cast (congrArg ((NativeModel W).toCwf.Tm (vectorScope types).1)
    (lookup_type types position)) ((vectorScope types).2.lookup position).2

theorem lookup_exact {n : Nat} (types : Fin n → NativeType (emptyScope (W := W)).1)
    (position : Fin n) :
    (vectorScope types).2.lookup position =
      ⟨(types position).reindex ((NativeModel W).toEmpty (vectorScope types).1),
        lookupSection types position⟩ := by
  apply Sigma.ext
  · exact lookup_type types position
  · unfold lookupSection
    exact (cast_heq _ _).symm

variable {D : CubeEnrichment.Signature}

/-- Raw declaration parsing agrees with the independently assembled finite
scope for every vector, rather than only individual authored examples. -/
theorem vector_read (model : ModelData (CubeNativeDeclarations.symbols D) W)
    {n : Nat} (expressions : Fin n → TypeExpr (CubeNativeDeclarations.symbols D) 0)
    (types : Fin n → NativeType (emptyScope (W := W)).1)
    (closed : ∀ position, model.evaluateType emptyScope (expressions position) = some (types position)) :
    model.evaluateContext (CubeNativeDeclarations.vectorTelescope expressions) = some (vectorScope types) := by
  induction n with
  | zero => rfl
  | succ n hypotheses =>
      have previous := hypotheses (fun position : Fin n => expressions position.succ)
        (fun position : Fin n => types position.succ) (fun position => closed position.succ)
      have weakened := model.evaluateType_rename (NativeLocalTypeOperations.products_substitution W)
        (expressions 0) (vectorScope (fun position : Fin n => types position.succ)) emptyScope
        Fin.elim0 (emptyRenaming _) (types 0) (closed 0)
      exact model.evaluateContext_snoc _ _ _ _ previous weakened

end Mettapedia.OSLF.NativeTypes.Semantics.Presheaf.CubeNativeSemanticTelescopes
