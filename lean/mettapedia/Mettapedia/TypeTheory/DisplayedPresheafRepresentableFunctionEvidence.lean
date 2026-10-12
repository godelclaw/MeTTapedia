import Mettapedia.TypeTheory.DisplayedPresheafRepresentableEvidence
import Mettapedia.TypeTheory.DisplayedPresheafEvidenceApplication

/-!
# Origin-retaining dependent function specifications

For an actual program map, a supplied source origin determines a coherent
function specification. Every argument returns the translated origin and
its independently supplied dependent answer. The complete function is built
by the native product adjunction; universal sum elimination extends it to
the compiler receipt. Naturality preserves both components.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.TypeTheory.DisplayedPresheafRepresentableFunctionEvidence

open _root_.CategoryTheory
open DisplayedPresheafTransport DisplayedPresheafComprehension
open DisplayedPresheafSliceSubstitution DisplayedPresheafSlicePi DisplayedPresheafPi
open DisplayedPresheafEvidenceTransport DisplayedPresheafEvidenceUniversal
open DisplayedPresheafEvidenceApplication DisplayedPresheafRepresentableEvidence

universe u

variable {C : Type u} [Category.{u} C] {P Q : Cᵒᵖ ⥤ Type u}
variable (f : P ⟶ Q) (root : P.Elements) (Input : Type u)
variable (Output : Input → Type u) (result : (argument : Input) → Output argument)

abbrev arguments : DisplayedFamily Q := (Functor.const Q.Elements).obj Input

def argumentSection (argument : Input) : (arguments (Q := Q) Input).sections where
  val _ := argument
  property _ := rfl

def argumentValue (point : (totalSpace (arguments (Q := Q) Input)).Elements) : Input := point.2.2

theorem argument_preserved {before after : (totalSpace (arguments (Q := Q) Input)).Elements}
    (change : before ⟶ after) : argumentValue Input before = argumentValue Input after :=
  congrArg (fun value : (totalSpace (arguments (Q := Q) Input)).obj after.1 => value.2) change.property

def answers : DisplayedFamily (totalSpace (arguments (Q := Q) Input)) where
  obj point := (origins (f.mapElements.obj root)).obj
      ((totalProjection (arguments Input)).mapElements.obj point) × Output (argumentValue Input point)
  map change := TypeCat.ofHom (fun answer =>
    ⟨(origins (f.mapElements.obj root)).map
      ((totalProjection (arguments Input)).mapElements.map change) answer.1,
      cast (congrArg Output (argument_preserved Input change)) answer.2⟩)
  map_id point := by
    apply ConcreteCategory.hom_ext
    intro answer
    apply Prod.ext
    · exact (origins (f.mapElements.obj root)).map_id_apply _ answer.1
    · change cast (congrArg Output (argument_preserved Input (𝟙 point))) answer.2 = answer.2
      exact eq_of_heq (cast_heq _ _)
  map_comp first second := by
    apply ConcreteCategory.hom_ext
    intro answer
    apply Prod.ext
    · exact (origins (f.mapElements.obj root)).map_comp_apply
        ((totalProjection (arguments Input)).mapElements.map first)
        ((totalProjection (arguments Input)).mapElements.map second) answer.1
    · exact eq_of_heq ((cast_heq _ _).trans ((cast_heq _ _).trans (cast_heq _ _)).symm)

private theorem dependent_result_cast {first second : Input} (same : first = second) :
    cast (congrArg Output same) (result first) = result second := by
  cases same
  rfl

def answerBody : reindexDisplayed (totalProjection (arguments Input))
      (origins (f.mapElements.obj root)) ⟶ answers f root Input Output where
  app point := TypeCat.ofHom (fun origin => ⟨origin, result (argumentValue Input point)⟩)
  naturality before after change := by
    apply ConcreteCategory.hom_ext
    intro origin
    apply Prod.ext
    · rfl
    · exact (dependent_result_cast Input Output result (argument_preserved Input change)).symm

noncomputable def functionConstructor : origins (f.mapElements.obj root) ⟶
    piDisplayed (arguments Input) (answers f root Input Output) :=
  abstractFamily (arguments Input) (answers f root Input Output) (answerBody f root Input Output result)

theorem functionConstructor_evaluation :
    (reindexFunctor (totalProjection (arguments Input))).map
        (functionConstructor f root Input Output result) ≫
      (displayedProductAdjunction (arguments Input)).counit.app (answers f root Input Output) =
        answerBody f root Input Output result :=
  abstractFamily_evaluation (arguments Input) (answers f root Input Output)
    (answerBody f root Input Output result)

theorem functionConstructor_application (point : Q.Elements)
    (origin : (origins (f.mapElements.obj root)).obj point) (argument : Input) :
    (applyAt (arguments Input) (answers f root Input Output) (argumentSection Input argument)).app point
        ((functionConstructor f root Input Output result).app point origin) =
      (⟨origin, result argument⟩ : (answers f root Input Output).obj
        ((sectionLift (arguments Input) (argumentSection Input argument)).mapElements.obj point)) :=
  abstractFamily_value (arguments Input) (answers f root Input Output)
    (answerBody f root Input Output result)
    ((sectionLift (arguments Input) (argumentSection Input argument)).mapElements.obj point) origin

noncomputable def functionBody : origins root ⟶ reindexDisplayed f
    (piDisplayed (arguments Input) (answers f root Input Output)) :=
  originMap f root ≫ (reindexFunctor f).map (functionConstructor f root Input Output result)

noncomputable def functionReadout : transport f (origins root) ⟶
    piDisplayed (arguments Input) (answers f root Input Output) :=
  descend f (functionBody f root Input Output result)

theorem receipt_application (point : P.Elements) (origin : (origins root).obj point) (argument : Input) :
    (applyAt (arguments Input) (answers f root Input Output) (argumentSection Input argument)).app
        (f.mapElements.obj point)
        ((functionReadout f root Input Output result).app (f.mapElements.obj point)
          ((unit f (origins root)).app point origin)) =
      (⟨f.mapElements.map origin, result argument⟩ : (answers f root Input Output).obj
        ((sectionLift (arguments Input) (argumentSection Input argument)).mapElements.obj
          (f.mapElements.obj point))) := by
  have computes := descend_unit f (functionBody f root Input Output result) point origin
  change (functionReadout f root Input Output result).app (f.mapElements.obj point)
      ((unit f (origins root)).app point origin) =
    (functionConstructor f root Input Output result).app (f.mapElements.obj point)
      (f.mapElements.map origin) at computes
  exact (congrArg ((applyAt (arguments Input) (answers f root Input Output)
      (argumentSection Input argument)).app (f.mapElements.obj point)) computes).trans
    (functionConstructor_application f root Input Output result (f.mapElements.obj point)
      (f.mapElements.map origin) argument)

theorem receipt_application_distinguishes_origins (point : P.Elements)
    {first second : (origins root).obj point} (different : first ≠ second) (argument : Input) :
    (applyAt (arguments Input) (answers f root Input Output) (argumentSection Input argument)).app
        (f.mapElements.obj point)
        ((functionReadout f root Input Output result).app (f.mapElements.obj point)
          ((unit f (origins root)).app point first)) ≠
      (applyAt (arguments Input) (answers f root Input Output) (argumentSection Input argument)).app
        (f.mapElements.obj point)
        ((functionReadout f root Input Output result).app (f.mapElements.obj point)
          ((unit f (origins root)).app point second)) := by
  rw [receipt_application, receipt_application]
  intro same
  exact different (originMap_injective f root point (congrArg Prod.fst same))

end Mettapedia.TypeTheory.DisplayedPresheafRepresentableFunctionEvidence
