import Mettapedia.TypeTheory.CwfYonedaProductFibre
import Mettapedia.TypeTheory.ContextualProductCellUniqueness

/-!
# The original generic evaluator as a native dependent function map

The source evaluator acts on the complete cartesian pairing of an original
function display witness with an original argument display witness. Its
natural transpose uses the chosen right-Kan product. Evaluation preserves
both witnesses and every subsequent source substitution.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.TypeTheory.CwfYoneda

open CategoryTheory Opposite
open Mettapedia.GSLT.Core.ContextualLadder
open DisplayedPresheafIndexedCwfBridge CategoryIndexedFamilyGeneralPi
open ContextualProductSections ContextualProductCellUniqueness

universe u w w'
variable (C : Cwf.{u, u, w, w'})

def indexedBodyFamily {Γ : C.Ctx} (A : C.Ty Γ) (B : C.Ty (C.ext Γ A)) :
    (family C A).Elements ⥤ Type u :=
  displayedToTotalElements (family C A) ⋙ dependentBodyFamily C A B

theorem indexedBodyFamily_restriction {Γ : C.Ctx}
    (A : C.Ty Γ) (B : C.Ty (C.ext Γ A))
    {first second : (family C A).Elements} (before : first ⟶ second)
    (receipt : (indexedBodyFamily C A B).obj first) :
    ((indexedBodyFamily C A B).map before receipt).val =
      C.compS receipt.val before.val.val.unop := by
  change C.compS receipt.val
    (((displayedToTotalElements (family C A)).map before).val.unop) = _
  rw [displayedToTotalElements_underlying]

def evaluatorArgumentLift (products : StableProducts C) {Γ : C.Ctx}
    (A : C.Ty Γ) (B : C.Ty (C.ext Γ A)) (point : (family C A).Elements)
    (function : (family C (products.operations.pi A B)).obj point.1) :
    C.Sub point.1.1.unop.val
      (C.ext (C.ext Γ (products.operations.pi A B))
        (C.tySub A (C.wk (products.operations.pi A B)))) :=
  (liftArgument C A (C.wk (products.operations.pi A B)) function.val
    ⟨point.2.val, point.2.property.trans function.property.symm⟩).val

theorem evaluatorArgumentLift_original (products : StableProducts C) {Γ : C.Ctx}
    (A : C.Ty Γ) (B : C.Ty (C.ext Γ A)) (point : (family C A).Elements)
    (function : (family C (products.operations.pi A B)).obj point.1) :
    C.compS (TypeOver.extensionSubstitution (C.wk (products.operations.pi A B)) A)
        (evaluatorArgumentLift C products A B point function) = point.2.val :=
  liftArgument_original C A _ _ _

theorem evaluatorArgumentLift_substitution (products : StableProducts C) {Γ : C.Ctx}
    (A : C.Ty Γ) (B : C.Ty (C.ext Γ A))
    {first second : (family C A).Elements} (before : first ⟶ second)
    (function : (family C (products.operations.pi A B)).obj first.1) :
    evaluatorArgumentLift C products A B second
        ((family C (products.operations.pi A B)).map before.val function) =
      C.compS (evaluatorArgumentLift C products A B first function) before.val.val.unop := by
  have arguments := congrArg Subtype.val before.property
  change C.compS first.2.val before.val.val.unop = second.2.val at arguments
  apply (liftArgument_unique C A (C.wk (products.operations.pi A B))
    (C.compS function.val before.val.val.unop) _ _ ?_ ?_).symm
  · rw [← C.comp_assoc]
    exact congrArg (fun arrow => C.compS arrow before.val.val.unop)
      (liftArgument_projection C A _ _ _)
  · rw [← C.comp_assoc, evaluatorArgumentLift_original, arguments]

/-- Independent whole source evaluation, naturally on every future
argument and every supplied function display map. -/
def sourceEvaluationBody (products : StableProducts C) {Γ : C.Ctx}
    (A : C.Ty Γ) (B : C.Ty (C.ext Γ A)) :
    CategoryOfElements.π (family C A) ⋙ family C (products.operations.pi A B) ⟶
      indexedBodyFamily C A B where
  app point := TypeCat.ofHom fun function =>
    ⟨C.compS (evaluation products.operations products.substitution.1 A B)
        (evaluatorArgumentLift C products A B point function), by
      change C.compS (C.wk B) (C.compS
        (evaluation products.operations products.substitution.1 A B)
        (evaluatorArgumentLift C products A B point function)) = point.2.val
      rw [← C.comp_assoc, evaluation_projection, evaluatorArgumentLift_original]⟩
  naturality first second before := by
    ext function
    let sourceReceipt : (indexedBodyFamily C A B).obj first :=
      ⟨C.compS (evaluation products.operations products.substitution.1 A B)
        (evaluatorArgumentLift C products A B first function), by
        change C.compS (C.wk B) (C.compS
          (evaluation products.operations products.substitution.1 A B)
          (evaluatorArgumentLift C products A B first function)) = first.2.val
        rw [← C.comp_assoc, evaluation_projection, evaluatorArgumentLift_original]⟩
    apply Subtype.ext
    change C.compS (evaluation products.operations products.substitution.1 A B)
      (evaluatorArgumentLift C products A B second
        ((family C (products.operations.pi A B)).map before.val function)) =
      ((indexedBodyFamily C A B).map before sourceReceipt).val
    rw [indexedBodyFamily_restriction, evaluatorArgumentLift_substitution]
    exact (C.comp_assoc _ _ _).symm

noncomputable section

def productFamilyForward (products : StableProducts C) {Γ : C.Ctx}
    (A : C.Ty Γ) (B : C.Ty (C.ext Γ A)) :
    family C (products.operations.pi A B) ⟶ representedProductFamily C A B :=
  generalPiTranspose (context := Cat.of (contextFace C Γ).Elements)
    (family C A) (sourceEvaluationBody C products A B)

/-- Transposing the original evaluator and evaluating at every argument
recovers the actual original evaluation body. -/
theorem productFamilyForward_evaluation (products : StableProducts C) {Γ : C.Ctx}
    (A : C.Ty Γ) (B : C.Ty (C.ext Γ A)) :
    Functor.whiskerLeft (CategoryOfElements.π (family C A))
        (productFamilyForward C products A B) ≫
      generalPiEvaluation (context := Cat.of (contextFace C Γ).Elements)
        (family C A) (indexedBodyFamily C A B) =
      sourceEvaluationBody C products A B :=
  generalPi_beta (context := Cat.of (contextFace C Γ).Elements) _ _

end

end Mettapedia.TypeTheory.CwfYoneda
