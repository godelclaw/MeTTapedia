import Mettapedia.OSLF.NativeTypes.Semantics.Classifier.DecodedCode
import Mettapedia.OSLF.NativeTypes.Semantics.Presheaf.CubeNativeSemanticTelescopes

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.OSLF.NativeTypes.Semantics.Classifier.Families

open Presheaf

open _root_.CategoryTheory Opposite
open CubeEnrichment
open Mettapedia.OSLF.Framework.ModalHypercube (HSort)
open Mettapedia.TypeTheory
open ContextualLocalUniverses NativeLocalTypeFormers
open Calculi.NativeDependent.Refinement
open DisplayedPresheafTransport DisplayedPresheafComprehension

universe u
variable {D : CubeEnrichment.Signature} {W : Type u} [Category.{u} W]
variable (operational : D.Carrier → Wᵒᵖ ⥤ Type u)

abbrev emptyScope : Scope W 0 := Scope.nil W

/-- Only the actual code presheaf is used to interpret the new carrier. -/
def codeMeaning (carrier : D.Carrier) : NativeType (emptyScope (W := W)).1 :=
  LocalType.present (CategoryOfElements.π emptyScope.1 ⋙ Carrier.presheaf operational carrier)

abbrev codeAt (carrier : D.Carrier) (P : Wᵒᵖ ⥤ Type u) : NativeType P :=
  (codeMeaning operational carrier).reindex ((NativeModel W).toEmpty P)

abbrev codeScope (carrier : D.Carrier) : Scope W 1 :=
  emptyScope.snoc (codeMeaning operational carrier)

abbrev typingScope (carrier : D.Carrier) : Scope W 2 :=
  (codeScope operational carrier).snoc (codeAt operational carrier (codeScope operational carrier).1)

/-- The ordered declaration variables are (code, claimed type code). -/
def pairName (carrier : D.Carrier) :
    (typingScope operational carrier).1 ⟶ Carrier.pairPresheaf operational carrier where
  app _ := TypeCat.ofHom fun value => (value.2, value.1.2)
  naturality _ _ _ := rfl

def pairNameInverse (carrier : D.Carrier) :
    Carrier.pairPresheaf operational carrier ⟶ (typingScope operational carrier).1 where
  app _ := TypeCat.ofHom fun value => ⟨⟨PUnit.unit, value.2⟩, value.1⟩
  naturality _ _ _ := rfl

theorem pairName_inverse (carrier : D.Carrier) :
    pairName operational carrier ≫ pairNameInverse operational carrier = 𝟙 _ := by
  apply NatTrans.ext
  funext world
  apply ConcreteCategory.hom_ext
  rintro ⟨⟨empty, type⟩, code⟩
  cases empty
  rfl

theorem pairNameInverse_name (carrier : D.Carrier) :
    pairNameInverse operational carrier ≫ pairName operational carrier = 𝟙 _ := by
  ext world value
  rfl

/-- Actual classification evidence is a fibre of an independently built projection. -/
noncomputable def typingMeaning  (carrier : D.Carrier) :
    NativeType (typingScope operational carrier).1 :=
  LocalType.present (reindexDisplayed (pairName operational carrier)
    (Carrier.typingFamily operational carrier))

theorem typing_inhabited_iff (carrier : D.Carrier) (world : Wᵒᵖ)
    (code type : Code operational carrier world) :
    Nonempty ((typingMeaning operational carrier).decoded.obj
      ⟨world, (pairNameInverse operational carrier).app world (code, type)⟩) ↔
      Code.Member code type :=
  Carrier.fibre_inhabited_iff operational carrier world code type

/-- Generic sections are actual natural maps into the classifier carrier. -/
def codeSection {P : Wᵒᵖ ⥤ Type u} (carrier : D.Carrier)
    (name : P ⟶ Carrier.presheaf operational carrier) :
    (codeAt operational carrier P).decoded.sections where
  val point := name.app point.1 point.2
  property := by
    intro first second arrow
    change (Carrier.presheaf operational carrier).map arrow.val
      (name.app first.1 first.2) = name.app second.1 second.2
    rw [← name.naturality_apply arrow.val first.2]
    exact congrArg (name.app second.1) arrow.property

def sortName (carrier : D.Carrier) (kind : HSort) {P : Wᵒᵖ ⥤ Type u} :
    P ⟶ Carrier.presheaf operational carrier where
  app _ := TypeCat.ofHom fun _ => .sort kind
  naturality _ _ _ := rfl

abbrev sortValue (carrier : D.Carrier) (kind : HSort) {P : Wᵒᵖ ⥤ Type u} :=
  codeSection operational carrier (sortName operational carrier kind (P := P))

theorem sortValue_exact (carrier : D.Carrier) (kind : HSort) {P : Wᵒᵖ ⥤ Type u}
    (point : P.Elements) :
    (sortValue operational carrier kind (P := P)).val point = .sort kind := rfl

end Mettapedia.OSLF.NativeTypes.Semantics.Classifier.Families
