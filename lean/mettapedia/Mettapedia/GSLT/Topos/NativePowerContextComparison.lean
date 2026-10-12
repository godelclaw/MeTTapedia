import Mettapedia.GSLT.Topos.NativePowerPiComparison
import Mettapedia.GSLT.Topos.NativePowerQuantifiers
import Mettapedia.TypeTheory.DisplayedPresheafSlice

/-!
# The actual context of native predicate variables

The full native function family, rather than its global sections, supplies
the predicate binder. Its comprehension context is compared with the product
by the local power presheaf, preserving the original parameter projection.
Thus native quantifiers retain all locally generalized predicates.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.GSLT.Topos.NativePowerContextComparison

open _root_.CategoryTheory Mettapedia.TypeTheory
open DisplayedPresheafTransport DisplayedPresheafComprehension
open DisplayedPresheafParameterFamilies DisplayedPresheafSlice
open NativeLocalTypeFormers PresheafNativePropositionReadout

universe u
variable {C : Type u} [Category.{u} C]

def projection (P A : Cᵒᵖ ⥤ Type u) : FunctorToTypes.prod P A ⟶ P where
  app _ := TypeCat.ofHom Prod.fst
  naturality := by intros; rfl

/-- Sigma evidence coordinates and product coordinates retain the same
complete generalized values; neither coordinate is forgotten. -/
def parameterContext (P A : Cᵒᵖ ⥤ Type u) :
    totalSpace (parameterFamily P A) ≅ FunctorToTypes.prod P A where
  hom := {
    app _ := TypeCat.ofHom fun value => (value.1, value.2)
    naturality := by intros; rfl }
  inv := {
    app _ := TypeCat.ofHom fun value => ⟨value.1, value.2⟩
    naturality := by intros; rfl }
  hom_inv_id := by apply NatTrans.ext; funext world; apply ConcreteCategory.hom_ext; intro value; rfl
  inv_hom_id := by apply NatTrans.ext; funext world; apply ConcreteCategory.hom_ext; intro value; rfl

theorem parameterContext_projection (P A : Cᵒᵖ ⥤ Type u) :
    (parameterContext P A).hom ≫ projection P A =
      totalProjection (parameterFamily P A) := by
  ext world value
  rfl

/-- Native predicate-variable comprehension is the complete local power
context. The function comparison is the earned native Π comparison. -/
noncomputable def nativeContext (P A : Cᵒᵖ ⥤ Type u) (native : NativeType P)
    (constant : native.decoded = parameterFamily P A) :
    totalSpace (NativeLocalTypeFormers.pi native
      (nativeOmega (totalSpace native.decoded))).decoded ≅
        FunctorToTypes.prod P (NativePowerPredicates.power A) :=
  ((totalFunctor P ⋙ Over.forget P).mapIso
    (NativePowerPiComparison.nativeComparison P A native constant).symm) ≪≫
      parameterContext P (NativePowerPredicates.power A)

theorem nativeContext_projection (P A : Cᵒᵖ ⥤ Type u) (native : NativeType P)
    (constant : native.decoded = parameterFamily P A) :
    (nativeContext P A native constant).hom ≫
      projection P (NativePowerPredicates.power A) =
        totalProjection (NativeLocalTypeFormers.pi native
          (nativeOmega (totalSpace native.decoded))).decoded := by
  apply NatTrans.ext
  funext world
  apply ConcreteCategory.hom_ext
  intro value
  rfl

theorem native_forall (P A : Cᵒᵖ ⥤ Type u) (native : NativeType P)
    (constant : native.decoded = parameterFamily P A)
    (predicate : Subfunctor (FunctorToTypes.prod P (NativePowerPredicates.power A))) :
    forallAlong (totalProjection (NativeLocalTypeFormers.pi native
      (nativeOmega (totalSpace native.decoded))).decoded)
      (predicate.preimage (nativeContext P A native constant).hom) =
        forallAlong (projection P (NativePowerPredicates.power A)) predicate :=
  NativePowerQuantifiers.forall_comparison (nativeContext P A native constant) _ _
    (nativeContext_projection P A native constant) predicate

theorem native_exists (P A : Cᵒᵖ ⥤ Type u) (native : NativeType P)
    (constant : native.decoded = parameterFamily P A)
    (predicate : Subfunctor (FunctorToTypes.prod P (NativePowerPredicates.power A))) :
    (predicate.preimage (nativeContext P A native constant).hom).image
      (totalProjection (NativeLocalTypeFormers.pi native
        (nativeOmega (totalSpace native.decoded))).decoded) =
        predicate.image (projection P (NativePowerPredicates.power A)) :=
  NativePowerQuantifiers.exists_comparison (nativeContext P A native constant) _ _
    (nativeContext_projection P A native constant) predicate

end Mettapedia.GSLT.Topos.NativePowerContextComparison
