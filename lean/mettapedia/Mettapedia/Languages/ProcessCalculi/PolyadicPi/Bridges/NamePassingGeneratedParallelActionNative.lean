import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingGeneratedParallelActionComparison

/-!+# Native rule receipts after the complete parallel-action equations

The actual native manufacture acts on the postcomposed closed theory map.
Its full dependent squares recover the independently constructed firing
arrows and both endpoint declarations at every stage. Restriction retains
the supplied origin and the entire generalized premise argument.

The edge-action equations identify generated edge classes. They do not
identify the authored origins stored by the receipt family.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingGeneratedParallelActionNative

open _root_.CategoryTheory Opposite
open Mettapedia.CategoryTheory
open Mettapedia.GSLT.Topos.PresheafTheoryAction
open Mettapedia.GSLT.Topos.PresheafTheoryPseudofunctor
open Mettapedia.TypeTheory

universe k

abbrev Source := NamePassingGeneratedParallelActionComparison.Source.{k}
abbrev Target := NamePassingGeneratedParallelActionComparison.Target.{k}
abbrev compiler := NamePassingGeneratedParallelActionComparison.compiler.{k}
abbrev compilerFunctor := compiler.{k}.functor
abbrev Origin := NamePassingGeneratedParallelActionComparison.Origin.{k}
abbrev domain := NamePassingGeneratedParallelActionComparison.sourceDomain.{k}
abbrev ruleArrow := NamePassingGeneratedParallelActionComparison.sourceFiring.{k}

def targetDomain (origin : Origin.{k}) : Target := compilerFunctor.obj (domain origin)
def targetEdge : Target.{k} := compilerFunctor.obj NamePassingGeneratedOperationalPresentation.category.edge
def targetProgram : Target.{k} := compilerFunctor.obj NamePassingGeneratedOperationalPresentation.category.vertex

def targetReceipts : Target.{k}ᵒᵖ ⥤ Type k :=
  IndexedArrowReceiptPresheaf.receipts.{k,k,k,k} targetDomain

def edgeReadout : targetReceipts.{k} ⟶ uliftYoneda.{k}.obj targetEdge :=
  IndexedArrowReceiptPresheaf.evaluate targetDomain (fun origin => compilerFunctor.map (ruleArrow origin))

def endpointReadout (side : Bool) : targetReceipts.{k} ⟶ uliftYoneda.{k}.obj targetProgram :=
  edgeReadout ≫ uliftYoneda.map (compilerFunctor.map (NamePassingGeneratedNativeLanguage.sourcePort side))

def nativeRead {P Q : Target.{k}ᵒᵖ ⥤ Type k} (map : P ⟶ Q) :
    (inverseImage compilerFunctor).obj P ⟶ (inverseImage compilerFunctor).obj Q :=
  (ElementaryToposObjectUniverseLift.down
    (Mettapedia.GSLT.Topos.PresheafElementaryTopos.topos
      (theory NamePassingGeneratedOperationalPresentation.theory))).map
    ((PresheafNativeManufacture.action.map (route compiler)).hom.hom.right.square.right.toFunctor.map
      ((ElementaryToposObjectUniverseLift.up
        (Mettapedia.GSLT.Topos.PresheafElementaryTopos.topos
          (theory BindingClosedGeneratedParallelAction.theory))).map map))

theorem native_read_complete {P Q : Target.{k}ᵒᵖ ⥤ Type k} (map : P ⟶ Q) :
    nativeRead map = (inverseImage compilerFunctor).map map :=
  PresheafNativeManufacture.original_program_arrow compiler map

theorem native_action_strong : HigherOrderDependentSigma.Strong
    (PresheafNativeManufacture.action.map (route compiler.{k})) :=
  PresheafNativeManufacture.map_strong (route compiler)

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
      receipt.2.down ≫ compilerFunctor.map (NamePassingGeneratedNativeLanguage.declaredEndpoint receipt.1 side) := by
  rw [nativeEndpoint, native_read_complete]
  change (receipt.2.down ≫ compilerFunctor.map (ruleArrow receipt.1)) ≫
    compilerFunctor.map (NamePassingGeneratedNativeLanguage.sourcePort side) = _
  rw [Category.assoc, ← compilerFunctor.map_comp, NamePassingGeneratedNativeLanguage.declared_endpoint]

theorem whole_independent_firing {stage : Source.{k}}
    (receipt : ((inverseImage compilerFunctor).obj targetReceipts).obj (op stage)) :
    (nativeFiring.app (op stage) receipt).down ≫
      (NamePassingGeneratedParallelActionComparison.resultComparison receipt.1).hom =
        receipt.2.down ≫ (NamePassingGeneratedParallelActionComparison.premiseComparison receipt.1).hom ≫
          NamePassingGeneratedParallelActionComparison.firing receipt.1 := by
  rw [whole_firing, Category.assoc, NamePassingGeneratedParallelActionComparison.complete_firing_square]

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

theorem whole_future_endpoint {first second : Source.{k}} (change : first ⟶ second)
    (receipt : ((inverseImage compilerFunctor).obj targetReceipts).obj (op second)) (side : Bool) :
    ((nativeEndpoint side).app (op first)
      (((inverseImage compilerFunctor).obj targetReceipts).map change.op receipt)).down =
        compilerFunctor.map change ≫ ((nativeEndpoint side).app (op second) receipt).down := by
  rw [whole_endpoint, whole_endpoint]
  exact Category.assoc _ _ _

def receiptDisplay (side : Bool) : Arrow (Target.{k}ᵒᵖ ⥤ Type k) := Arrow.mk (endpointReadout side)
def edgeDisplay (side : Bool) : Arrow (Target.{k}ᵒᵖ ⥤ Type k) :=
  Arrow.mk (uliftYoneda.{k}.map (compilerFunctor.map (NamePassingGeneratedNativeLanguage.sourcePort side)))

def firingDisplay (side : Bool) : receiptDisplay.{k} side ⟶ edgeDisplay side :=
  Arrow.homMk edgeReadout (𝟙 _) (by simp [receiptDisplay, edgeDisplay, endpointReadout])

theorem full_native_display (side : Bool) :
    (ElementaryToposObjectUniverseLift.down
      (Mettapedia.GSLT.Topos.PresheafElementaryTopos.topos
        (theory NamePassingGeneratedOperationalPresentation.theory))).mapArrow.map
      ((PresheafNativeManufacture.action.map (route compiler)).hom.hom.right.square.left.toFunctor.map
        ((ElementaryToposObjectUniverseLift.up
          (Mettapedia.GSLT.Topos.PresheafElementaryTopos.topos
            (theory BindingClosedGeneratedParallelAction.theory))).mapArrow.map (firingDisplay side))) =
      (inverseImage compilerFunctor).mapArrow.map (firingDisplay side) :=
  PresheafNativeManufacture.full_display_square (route compiler) (firingDisplay side)

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingGeneratedParallelActionNative
