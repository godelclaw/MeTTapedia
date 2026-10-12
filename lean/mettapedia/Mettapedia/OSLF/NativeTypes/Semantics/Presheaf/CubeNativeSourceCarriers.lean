import Mettapedia.OSLF.NativeTypes.Semantics.Presheaf.NativeModelSum
import Mettapedia.OSLF.NativeTypes.Semantics.Presheaf.CubeNativeExtension
import Mettapedia.OSLF.NativeTypes.Semantics.Presheaf.CubeNativePresheafRealization

/-!
# Operational source carriers come from actual closed native interpretations

Each carrier is interpreted from its authored native formation tree in the
original model. The old decoded fibre itself becomes the operational generator
presheaf; no separate semantic carrier or agreement oracle is supplied.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.OSLF.NativeTypes.Semantics.Presheaf.CubeNativeSourceCarriers

open _root_.CategoryTheory Opposite
open Mettapedia.TypeTheory
open ContextualLocalUniverses ContextualModelTelescopes NativeLocalTypeFormers
open Calculi.NativeDependent.Refinement
open CubeNativeSemanticFamilies CubeNativeSemanticOperations

universe u
variable {S : Symbols} {D : CubeEnrichment.Signature} {W : Type u} [Category.{u} W]
variable {bound : Nat} (source : Signature S)
    (carriers : CubeNativeExtension.SourceCarriers source D bound)
    (sourceModel : ModelData S W) (realized : SignatureRealization sourceModel source)

include realized

theorem carrierType_exists (carrier : D.Carrier) :
    ∃ A : NativeType (CubeNativeSemanticFamilies.emptyScope (W := W)).1,
      sourceModel.evaluateType CubeNativeSemanticFamilies.emptyScope (carriers.type carrier) = some A := by
  have meaning := (carriers.formed carrier).native_sound sourceModel realized
  rcases meaning with ⟨context, A, contextRead, typeRead⟩
  have empty : context = CubeNativeSemanticFamilies.emptyScope := (Option.some.inj contextRead).symm
  subst context
  exact ⟨A,typeRead⟩

noncomputable def carrierType (carrier : D.Carrier) :
    NativeType (CubeNativeSemanticFamilies.emptyScope (W := W)).1 :=
  Classical.choose (carrierType_exists source carriers sourceModel realized carrier)

theorem carrierType_read (carrier : D.Carrier) :
    sourceModel.evaluateType CubeNativeSemanticFamilies.emptyScope (carriers.type carrier) =
      some (carrierType source carriers sourceModel realized carrier) :=
  Classical.choose_spec (carrierType_exists source carriers sourceModel realized carrier)

/-- The original empty native scope has one component at each base object. -/
def emptyElements : Wᵒᵖ ⥤ (CubeNativeSemanticFamilies.emptyScope (W := W)).1.Elements where
  obj world := ⟨world,PUnit.unit⟩
  map arrow := ⟨arrow,rfl⟩
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The operational generator object is the actual old native fibre. -/
noncomputable def operational (carrier : D.Carrier) : Wᵒᵖ ⥤ Type u :=
  emptyElements ⋙ (carrierType source carriers sourceModel realized carrier).decoded

noncomputable abbrev injectionScope (carrier : D.Carrier) : Scope W 1 :=
  CubeNativeSemanticFamilies.emptyScope.snoc (carrierType source carriers sourceModel realized carrier)

/-- The newest actual source-carrier component is read without replacing the
old family with another presented native type. -/
noncomputable def sourceName (carrier : D.Carrier) :
    (injectionScope source carriers sourceModel realized carrier).1 ⟶
      operational source carriers sourceModel realized carrier where
  app world := TypeCat.ofHom fun value => by
    rcases value with ⟨base,value⟩
    cases base
    exact value
  naturality first second arrow := by
    apply ConcreteCategory.hom_ext
    intro value
    rcases value with ⟨base,value⟩
    cases base
    rfl

/-- Actual source values inject into the freely adjoined code presheaf. -/
noncomputable def injectionName (carrier : D.Carrier) :
    (injectionScope source carriers sourceModel realized carrier).1 ⟶
      CubePresheafCode.presheaf (operational source carriers sourceModel realized) carrier :=
  sourceName source carriers sourceModel realized carrier ≫
    CubePresheafCode.injection (operational source carriers sourceModel realized) carrier

theorem injectionName_exact (carrier : D.Carrier) (world : Wᵒᵖ)
    (value : (operational source carriers sourceModel realized carrier).obj world) :
    (injectionName source carriers sourceModel realized carrier).app world ⟨PUnit.unit,value⟩ =
      .operational value := rfl

theorem injectionName_injective (carrier : D.Carrier) (world : Wᵒᵖ) :
    Function.Injective ((injectionName source carriers sourceModel realized carrier).app world) := by
  rintro ⟨base,first⟩ ⟨other,second⟩ equal
  cases base
  cases other
  have values := CubeEnrichment.Code.operational_injective equal
  cases values
  rfl

end Mettapedia.OSLF.NativeTypes.Semantics.Presheaf.CubeNativeSourceCarriers
