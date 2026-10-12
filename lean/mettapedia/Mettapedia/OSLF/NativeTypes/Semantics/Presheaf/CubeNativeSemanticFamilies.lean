import Mettapedia.OSLF.NativeTypes.Semantics.Presheaf.CubePresheafCode
import Mettapedia.OSLF.NativeTypes.Semantics.Presheaf.CubeNativeHeaderRanks
import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementEvidenceExtraction

/-!
# Actual native code carriers and typing fibres

Code carriers are the free presheaves over the prior operational carriers.
The binary native family is the independent kinding projection's actual
fibre, pulled back along the two ordered variables of its declaration.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.OSLF.NativeTypes.Semantics.Presheaf.CubeNativeSemanticFamilies

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
  LocalType.present (CategoryOfElements.π emptyScope.1 ⋙ CubePresheafCode.presheaf operational carrier)

abbrev codeAt (carrier : D.Carrier) (P : Wᵒᵖ ⥤ Type u) : NativeType P :=
  (codeMeaning operational carrier).reindex ((NativeModel W).toEmpty P)

abbrev codeScope (carrier : D.Carrier) : Scope W 1 :=
  emptyScope.snoc (codeMeaning operational carrier)

abbrev typingScope (carrier : D.Carrier) : Scope W 2 :=
  (codeScope operational carrier).snoc (codeAt operational carrier (codeScope operational carrier).1)

/-- The ordered declaration variables are (code, claimed type code). -/
def pairName (carrier : D.Carrier) :
    (typingScope operational carrier).1 ⟶ CubePresheafCode.pairPresheaf operational carrier where
  app _ := TypeCat.ofHom fun value => (value.2, value.1.2)
  naturality _ _ _ := rfl

def pairNameInverse (carrier : D.Carrier) :
    CubePresheafCode.pairPresheaf operational carrier ⟶ (typingScope operational carrier).1 where
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

/-- Actual kinding evidence is a fibre of an independently built projection. -/
def typingMeaning (vertex : Vertex D) (carrier : D.Carrier) :
    NativeType (typingScope operational carrier).1 :=
  LocalType.present (reindexDisplayed (pairName operational carrier)
    (CubePresheafCode.typingFamily operational vertex carrier))

/-- Pulling the meaning to any context gives exactly the independent fibre at
its actual ordered arguments, with no proposition-symbol interpretation. -/
theorem typing_inhabited_iff (vertex : Vertex D) (carrier : D.Carrier) (world : Wᵒᵖ)
    (code : (CubePresheafCode.presheaf operational carrier).obj world) (kind : HSort) :
    Nonempty ((typingMeaning operational vertex carrier).decoded.obj
      ⟨world, (pairNameInverse operational carrier).app world (code, .sort kind)⟩) ↔
    Nonempty (CubeEnrichment.Kinded vertex code kind) :=
  CubePresheafCode.fibre_inhabited_iff operational vertex carrier world code kind

/-- Generic sections are actual natural maps into the free code object. -/
def codeSection {P : Wᵒᵖ ⥤ Type u} (carrier : D.Carrier)
    (name : P ⟶ CubePresheafCode.presheaf operational carrier) :
    (codeAt operational carrier P).decoded.sections where
  val point := name.app point.1 point.2
  property := by
    intro first second arrow
    change (CubePresheafCode.presheaf operational carrier).map arrow.val
      (name.app first.1 first.2) = name.app second.1 second.2
    rw [← name.naturality_apply arrow.val first.2]
    exact congrArg (name.app second.1) arrow.property

def sortName (carrier : D.Carrier) (kind : HSort) {P : Wᵒᵖ ⥤ Type u} :
    P ⟶ CubePresheafCode.presheaf operational carrier where
  app _ := TypeCat.ofHom fun _ => .sort kind
  naturality _ _ _ := rfl

abbrev sortValue (carrier : D.Carrier) (kind : HSort) {P : Wᵒᵖ ⥤ Type u} :=
  codeSection operational carrier (sortName operational carrier kind (P := P))

theorem sortValue_exact (carrier : D.Carrier) (kind : HSort) {P : Wᵒᵖ ⥤ Type u}
    (point : P.Elements) :
    (sortValue operational carrier kind (P := P)).val point = .sort kind := rfl

/-- Formation evidence cannot turn an operational value into a generated
code kind merely because both occur in the same enriched carrier. -/
theorem injected_untyped (vertex : Vertex D) (carrier : D.Carrier) (world : Wᵒᵖ)
    (value : (operational carrier).obj world) (kind : HSort) :
    ¬ Nonempty ((typingMeaning operational vertex carrier).decoded.obj
      ⟨world, (pairNameInverse operational carrier).app world (.operational value, .sort kind)⟩) := by
  rw [typing_inhabited_iff]
  exact CubeEnrichment.no_operational_kind (operational := fun carrier => (operational carrier).obj world) vertex value kind

end Mettapedia.OSLF.NativeTypes.Semantics.Presheaf.CubeNativeSemanticFamilies
