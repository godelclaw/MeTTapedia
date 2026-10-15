import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingGeneratedOperationalCategoryComparison
import Mettapedia.CategoryTheory.IndexedArrowReceiptPresheaf
import Mettapedia.TypeTheory.PresheafNativeManufacture

/-!
# Native receipts for the complete generated operational compiler

Each authored rule keeps its own complete premise object and origin. The
actual presheaf action restricts the resulting receipt family along the
finite-limit and closed compiler. Its native edge and dependent display
readouts recover the independently constructed communication and active
firings, including their authored source and target arrows.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingGeneratedNativeLanguage

open _root_.CategoryTheory Opposite
open Mettapedia.CategoryTheory RelativeClosedSyntax GeneratedCategory Interpretation
open Mettapedia.GSLT.Topos.PresheafTheoryAction
open Mettapedia.GSLT.Topos.PresheafTheoryPseudofunctor
open Mettapedia.TypeTheory

universe k

abbrev Source := NamePassingGeneratedOperationalCategoryComparison.Source.{k}
abbrev Target := NamePassingGeneratedOperationalCategoryComparison.Target.{k}
abbrev compiler := NamePassingGeneratedOperationalInterpretation.interpretation.{k}
abbrev compilerFunctor := NamePassingGeneratedOperationalCategoryComparison.compilerFunctor.{k}
abbrev Origin := ULift.{k} NamePassingGeneratedOperationalPresentation.Origin

def domain (origin : Origin.{k}) : Source := RelativeClosedInternalCategory.RulePresentation.ruleDomain
  NamePassingGeneratedOperationalPresentation.vertex
  NamePassingGeneratedOperationalPresentation.categoryMap NamePassingGeneratedOperationalPresentation.declaration origin

def ruleArrow (origin : Origin.{k}) : domain origin ⟶ NamePassingGeneratedOperationalPresentation.category.edge :=
  classOf (NamePassingGeneratedOperationalPresentation.fire origin)

def targetDomain (origin : Origin.{k}) : Target := compilerFunctor.obj (domain origin)
def targetEdge : Target.{k} := compilerFunctor.obj NamePassingGeneratedOperationalPresentation.category.edge
def targetProgram : Target.{k} := compilerFunctor.obj NamePassingGeneratedOperationalPresentation.category.vertex

def targetReceipts : Target.{k}ᵒᵖ ⥤ Type k :=
  IndexedArrowReceiptPresheaf.receipts.{k,k,k,k} targetDomain

def edgeReadout : targetReceipts.{k} ⟶ uliftYoneda.{k}.obj targetEdge :=
  IndexedArrowReceiptPresheaf.evaluate targetDomain (fun origin => compilerFunctor.map (ruleArrow origin))

def sourcePort (side : Bool) : NamePassingGeneratedOperationalPresentation.category.edge ⟶
    NamePassingGeneratedOperationalPresentation.category.vertex :=
  if side then NamePassingGeneratedOperationalPresentation.category.target
  else NamePassingGeneratedOperationalPresentation.category.source

def declaredEndpoint (origin : Origin.{k}) (side : Bool) : domain origin ⟶
    NamePassingGeneratedOperationalPresentation.category.vertex :=
  if side then classOf (RelativeClosedInternalCategory.RulePresentation.after
    NamePassingGeneratedOperationalPresentation.vertex NamePassingGeneratedOperationalPresentation.categoryMap
      NamePassingGeneratedOperationalPresentation.declaration origin)
  else classOf (RelativeClosedInternalCategory.RulePresentation.before
    NamePassingGeneratedOperationalPresentation.vertex NamePassingGeneratedOperationalPresentation.categoryMap
      NamePassingGeneratedOperationalPresentation.declaration origin)

theorem declared_endpoint (origin : Origin.{k}) (side : Bool) :
    ruleArrow origin ≫ sourcePort side = declaredEndpoint origin side := by
  cases side with
  | false => exact NamePassingGeneratedOperationalPresentation.authored_source origin
  | true => exact NamePassingGeneratedOperationalPresentation.authored_target origin

def endpointReadout (side : Bool) : targetReceipts.{k} ⟶ uliftYoneda.{k}.obj targetProgram :=
  edgeReadout ≫ uliftYoneda.map (compilerFunctor.map (sourcePort side))

def nativeRead {P Q : Target.{k}ᵒᵖ ⥤ Type k} (map : P ⟶ Q) :
    (inverseImage compilerFunctor).obj P ⟶ (inverseImage compilerFunctor).obj Q :=
  (ElementaryToposObjectUniverseLift.down
    (Mettapedia.GSLT.Topos.PresheafElementaryTopos.topos
      (theory NamePassingGeneratedOperationalPresentation.theory))).map
    ((PresheafNativeManufacture.action.map (route compiler)).hom.hom.right.square.right.toFunctor.map
      ((ElementaryToposObjectUniverseLift.up
        (Mettapedia.GSLT.Topos.PresheafElementaryTopos.topos
          (theory BindingClosedGeneratedOperational.theory))).map map))

theorem native_read_complete {P Q : Target.{k}ᵒᵖ ⥤ Type k} (map : P ⟶ Q) :
    nativeRead map = (inverseImage compilerFunctor).map map :=
  PresheafNativeManufacture.original_program_arrow compiler map

def nativeFiring := nativeRead edgeReadout.{k}
def nativeEndpoint (side : Bool) := nativeRead (endpointReadout.{k} side)

theorem whole_firing {stage : Source.{k}}
    (receipt : ((inverseImage compilerFunctor).obj targetReceipts).obj (op stage)) :
    (nativeFiring.app (op stage) receipt).down = receipt.2.down ≫ compilerFunctor.map (ruleArrow receipt.1) := by
  rw [nativeFiring, native_read_complete]
  rfl

theorem whole_endpoint {stage : Source.{k}}
    (receipt : ((inverseImage compilerFunctor).obj targetReceipts).obj (op stage)) (side : Bool) :
    ((nativeEndpoint side).app (op stage) receipt).down =
      receipt.2.down ≫ compilerFunctor.map (declaredEndpoint receipt.1 side) := by
  rw [nativeEndpoint, native_read_complete]
  change (receipt.2.down ≫ compilerFunctor.map (ruleArrow receipt.1)) ≫
    compilerFunctor.map (sourcePort side) = _
  rw [Category.assoc, ← compilerFunctor.map_comp, declared_endpoint]

def premiseComparison (origin : Origin.{k}) : targetDomain origin ≅
    RelativeClosedInternalCategory.RuleInterpretation.premise
      NamePassingGeneratedOperationalPresentation.vertex NamePassingGeneratedOperationalPresentation.categoryMap
      NamePassingGeneratedOperationalPresentation.declaration
      NamePassingGeneratedOperationalInterpretation.meanings NamePassingGeneratedOperationalInterpretation.realized origin :=
  eqToIso (congrArg ArrowValue.source (NamePassingGeneratedOperationalInterpretation.whole_firing_readout origin))

def resultComparison (origin : Origin.{k}) : targetEdge ≅
    RelativeClosedInternalCategory.RuleInterpretation.edges
      NamePassingGeneratedOperationalPresentation.vertex NamePassingGeneratedOperationalPresentation.categoryMap
      NamePassingGeneratedOperationalInterpretation.meanings NamePassingGeneratedOperationalInterpretation.realized :=
  eqToIso (congrArg ArrowValue.target (NamePassingGeneratedOperationalInterpretation.whole_firing_readout origin))

theorem independent_firing_square (origin : Origin.{k}) :
    compilerFunctor.map (ruleArrow origin) ≫ (resultComparison origin).hom =
      (premiseComparison origin).hom ≫ NamePassingGeneratedOperationalInterpretation.firing origin := by
  have actual := (conj_eqToHom_iff_heq _ _
    (congrArg ArrowValue.source (NamePassingGeneratedOperationalInterpretation.whole_firing_readout origin))
    (congrArg ArrowValue.target (NamePassingGeneratedOperationalInterpretation.whole_firing_readout origin))).mpr
      (ArrowValue.arrows_heq (NamePassingGeneratedOperationalInterpretation.whole_firing_readout origin))
  change compilerFunctor.map (ruleArrow origin) = (premiseComparison origin).hom ≫
    NamePassingGeneratedOperationalInterpretation.firing origin ≫ (resultComparison origin).inv at actual
  rw [actual]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

theorem complete_independent_firing {stage : Source.{k}}
    (receipt : ((inverseImage compilerFunctor).obj targetReceipts).obj (op stage)) :
    (nativeFiring.app (op stage) receipt).down ≫ (resultComparison receipt.1).hom =
      receipt.2.down ≫ (premiseComparison receipt.1).hom ≫
        NamePassingGeneratedOperationalInterpretation.firing receipt.1 := by
  rw [whole_firing, Category.assoc, independent_firing_square]

theorem future_origin {first second : Source.{k}} (change : first ⟶ second)
    (receipt : ((inverseImage compilerFunctor).obj targetReceipts).obj (op second)) :
    (((inverseImage compilerFunctor).obj targetReceipts).map change.op receipt).1 = receipt.1 := rfl

theorem whole_future_firing {first second : Source.{k}} (change : first ⟶ second)
    (receipt : ((inverseImage compilerFunctor).obj targetReceipts).obj (op second)) :
    (nativeFiring.app (op first)
      (((inverseImage compilerFunctor).obj targetReceipts).map change.op receipt)).down =
        compilerFunctor.map change ≫ (nativeFiring.app (op second) receipt).down := by
  rw [nativeFiring, native_read_complete]
  exact IndexedArrowReceiptPresheaf.complete_restriction targetDomain
    (fun origin => compilerFunctor.map (ruleArrow origin)) (compilerFunctor.map change) receipt

def receiptDisplay (side : Bool) : Arrow (Target.{k}ᵒᵖ ⥤ Type k) := Arrow.mk (endpointReadout side)
def edgeDisplay (side : Bool) : Arrow (Target.{k}ᵒᵖ ⥤ Type k) :=
  Arrow.mk (uliftYoneda.{k}.map (compilerFunctor.map (sourcePort side)))

def firingDisplay (side : Bool) : receiptDisplay.{k} side ⟶ edgeDisplay side :=
  Arrow.homMk edgeReadout (𝟙 _) (by simp [receiptDisplay, edgeDisplay, endpointReadout])

theorem full_native_display (side : Bool) :
    (ElementaryToposObjectUniverseLift.down
      (Mettapedia.GSLT.Topos.PresheafElementaryTopos.topos
        (theory NamePassingGeneratedOperationalPresentation.theory))).mapArrow.map
      ((PresheafNativeManufacture.action.map (route compiler)).hom.hom.right.square.left.toFunctor.map
        ((ElementaryToposObjectUniverseLift.up
          (Mettapedia.GSLT.Topos.PresheafElementaryTopos.topos
            (theory BindingClosedGeneratedOperational.theory))).mapArrow.map (firingDisplay side))) =
      (inverseImage compilerFunctor).mapArrow.map (firingDisplay side) :=
  PresheafNativeManufacture.full_display_square (route compiler) (firingDisplay side)

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingGeneratedNativeLanguage
