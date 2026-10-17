import Mettapedia.OSLF.NativeTypes.Semantics.Classifier.FamilyNaming
import Mettapedia.OSLF.NativeTypes.Semantics.Classifier.Vectors
import Mettapedia.OSLF.NativeTypes.Semantics.Classifier.Readout

/-!
# Constructor classifiers are images of the authored operations

The argument predicate reads all ordered classifier arguments. Its image
under the original constructor gives exactly the output's inhabitants.
The carrier action retains future contexts and constructor naturality.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.OSLF.NativeTypes.Semantics.Classifier.StructuralImages

open _root_.CategoryTheory Opposite
open Presheaf CubeEnrichment
open Mettapedia.TypeTheory Calculi.NativeDependent.Refinement
open Mettapedia.GSLT.Topos
open Families Operations Arguments Vectors

universe u
variable {D : CubeEnrichment.Signature} {W : Type u} [Category.{u} W]
variable (operational : D.Carrier → Wᵒᵖ ⥤ Type u)

def operands (declaration : D.Former) : Wᵒᵖ ⥤ Type u where
  obj world := ∀ position, (operational (D.input declaration position)).obj world
  map arrow := TypeCat.ofHom fun values position => (operational (D.input declaration position)).map arrow (values position)
  map_id world := by
    apply ConcreteCategory.hom_ext
    intro values
    funext position
    exact ConcreteCategory.congr_hom ((operational (D.input declaration position)).map_id world) (values position)
  map_comp first second := by
    apply ConcreteCategory.hom_ext
    intro values
    funext position
    exact ConcreteCategory.congr_hom ((operational (D.input declaration position)).map_comp first second) (values position)

/-- Each operation is a natural map of the original ordered arguments. -/
structure Algebra where
  operation : ∀ declaration, operands operational declaration ⟶ operational (D.output declaration)

variable (algebra : Algebra operational)

noncomputable def image {P : Wᵒᵖ ⥤ Type u} (declaration : D.Former)
    (arguments : ∀ position, P ⟶ Carrier.presheaf operational (D.input declaration position)) :
    Subfunctor (FunctorToTypes.prod (operational (D.output declaration)) P) where
  obj world := fun pair => ∃ values : (operands operational declaration).obj world,
    (∀ position, Code.Member (.operational (values position)) ((arguments position).app world pair.2)) ∧
      (algebra.operation declaration).app world values = pair.1
  map arrow pair := by
    rintro ⟨values, members, result⟩
    refine ⟨(operands operational declaration).map arrow values, ?_, ?_⟩
    · intro position
      have member := Code.member_map arrow (members position)
      have natural := (arguments position).naturality_apply arrow pair.2
      change (arguments position).app _ (P.map arrow pair.2) =
        Code.map arrow ((arguments position).app _ pair.2) at natural
      rw [← natural] at member
      exact member
    · exact ((algebra.operation declaration).naturality_apply arrow values).trans
        (congrArg ((operational (D.output declaration)).map arrow) result)

noncomputable def formerName {P : Wᵒᵖ ⥤ Type u} (vertex : Vertex D) (declaration : D.Former)
    (arguments : ∀ position, P ⟶ Carrier.presheaf operational (D.input declaration position)) :
    P ⟶ Carrier.presheaf operational (D.output declaration) :=
  Carrier.classifierName operational (D.output declaration) (outputSort D vertex declaration)
    (FamilyNaming.name (image operational algebra declaration arguments))

theorem former_member {P : Wᵒᵖ ⥤ Type u} (vertex : Vertex D) (declaration : D.Former)
    (arguments : ∀ position, P ⟶ Carrier.presheaf operational (D.input declaration position))
    (world : Wᵒᵖ) (parameter : P.obj world) (result : (operational (D.output declaration)).obj world) :
    Code.Member (.operational result) ((formerName operational algebra vertex declaration arguments).app world parameter) ↔
      ∃ values : (operands operational declaration).obj world,
        (∀ position, Code.Member (.operational (values position)) ((arguments position).app world parameter)) ∧
          (algebra.operation declaration).app world values = result :=
  FamilyNaming.member_name _ world result parameter

/-- Substitution acts on every ordered argument, then on the constructor image. -/
theorem image_substitution {P Q : Wᵒᵖ ⥤ Type u} (declaration : D.Former)
    (arguments : ∀ position, P ⟶ Carrier.presheaf operational (D.input declaration position))
    (mapping : Q ⟶ P) :
    (image operational algebra declaration arguments).preimage (FamilyNaming.parameters mapping) =
      image operational algebra declaration (fun position => mapping ≫ arguments position) := by
  ext world pair
  rfl

theorem formerName_substitution {P Q : Wᵒᵖ ⥤ Type u} (vertex : Vertex D) (declaration : D.Former)
    (arguments : ∀ position, P ⟶ Carrier.presheaf operational (D.input declaration position))
    (mapping : Q ⟶ P) :
    mapping ≫ formerName operational algebra vertex declaration arguments =
      formerName operational algebra vertex declaration (fun position => mapping ≫ arguments position) := by
  unfold formerName
  rw [Readout.classifierName_substitution, FamilyNaming.substitution, image_substitution]

end Mettapedia.OSLF.NativeTypes.Semantics.Classifier.StructuralImages
