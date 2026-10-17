import Mettapedia.OSLF.NativeTypes.Semantics.Classifier.CertifiedProjection
import Mettapedia.OSLF.NativeTypes.Semantics.Classifier.FamilyNaming

/-!
# Natural certified sections for open operational classifiers

Parameterized predicates produce actual values of the generated dependent
classifier type. Decoding those values recovers the predicate's membership,
and changing parameters commutes with decoding.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.OSLF.NativeTypes.Semantics.Classifier.CertifiedSections

open _root_.CategoryTheory Opposite
open Mettapedia.TypeTheory ContextualLocalUniverses
open Mettapedia.OSLF.Framework.ModalHypercube (HSort)
open Calculi.NativeDependent.Refinement
open Families Operations CertifiedProjection

universe u
variable {D : Presheaf.CubeEnrichment.Signature} {W : Type u} [Category.{u} W]
variable (operational : D.Carrier → Wᵒᵖ ⥤ Type u)

noncomputable section

/-- A complete natural code with its kind evidence determines a native
certified section, using the actual Sigma decoder in both directions. -/
def ofName {P : Wᵒᵖ ⥤ Type u} (carrier : D.Carrier) (kind : HSort)
    (name : P ⟶ validPresheaf operational carrier kind) :
    (certifiedAt operational carrier kind P).decoded.sections where
  val point := certifiedEncode operational carrier kind ⟨point.1, PUnit.unit⟩
    (name.app point.1 point.2)
  property := by
    intro first second arrow
    apply (certifiedEquiv operational carrier kind ⟨second.1, PUnit.unit⟩).injective
    let lifted := CategoryOfElements.homMk (F := (Families.emptyScope (W := W)).1)
      ⟨first.1, PUnit.unit⟩ ⟨second.1, PUnit.unit⟩ arrow.val rfl
    have natural := (certifiedRead operational carrier kind).naturality_apply lifted
      (certifiedEncode operational carrier kind ⟨first.1, PUnit.unit⟩ (name.app first.1 first.2))
    refine natural.trans ?_
    rw [certifiedRead_encode]
    change (validPresheaf operational carrier kind).map arrow.val (name.app first.1 first.2) =
      (certifiedRead operational carrier kind).app ⟨second.1, PUnit.unit⟩
        (certifiedEncode operational carrier kind ⟨second.1, PUnit.unit⟩ (name.app second.1 second.2))
    rw [certifiedRead_encode]
    exact ((name.naturality_apply arrow.val first.2).symm).trans
      (congrArg (name.app second.1) arrow.property)

@[simp] theorem read_ofName {P : Wᵒᵖ ⥤ Type u} (carrier : D.Carrier) (kind : HSort)
    (name : P ⟶ validPresheaf operational carrier kind) (point : P.Elements) :
    certifiedAtEquiv operational carrier kind P point ((ofName operational carrier kind name).val point) =
      name.app point.1 point.2 :=
  certifiedRead_encode operational carrier kind ⟨point.1, PUnit.unit⟩ (name.app point.1 point.2)

/-- The classifier is formed by its selected sort, independently of whether
any program has the specified property. -/
def predicateName {P : Wᵒᵖ ⥤ Type u} (carrier : D.Carrier) (kind : HSort)
    (predicate : Subfunctor (FunctorToTypes.prod (operational carrier) P)) :
    P ⟶ validPresheaf operational carrier kind where
  app world := TypeCat.ofHom fun parameter =>
    ⟨.classifier kind ((FamilyNaming.name predicate).app world parameter), rfl⟩
  naturality world future arrow := by
    apply ConcreteCategory.hom_ext
    intro parameter
    apply Subtype.ext
    exact congrArg (Code.classifier kind) ((FamilyNaming.name predicate).naturality_apply arrow parameter)

def classifier {P : Wᵒᵖ ⥤ Type u} (carrier : D.Carrier) (kind : HSort)
    (predicate : Subfunctor (FunctorToTypes.prod (operational carrier) P)) :
    (certifiedAt operational carrier kind P).decoded.sections :=
  ofName operational carrier kind (predicateName operational carrier kind predicate)

/-- Membership of a decoded generated classifier is its independently
defined operational predicate at the same open parameter environment. -/
theorem classifier_exact {P : Wᵒᵖ ⥤ Type u} (carrier : D.Carrier) (kind : HSort)
    (predicate : Subfunctor (FunctorToTypes.prod (operational carrier) P))
    (world : Wᵒᵖ) (parameter : P.obj world) (value : (operational carrier).obj world) :
    Code.Member (.operational value)
      (certifiedAtEquiv operational carrier kind P ⟨world, parameter⟩
        ((classifier operational carrier kind predicate).val ⟨world, parameter⟩)).val ↔
      (value, parameter) ∈ predicate.obj world := by
  rw [classifier, read_ofName]
  exact FamilyNaming.member_name predicate world value parameter

end
end Mettapedia.OSLF.NativeTypes.Semantics.Classifier.CertifiedSections
