import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingGeneratedParallelActionNative
import Mettapedia.CategoryTheory.CartesianMonoidActionControls

/-!
# Whole action classes and separately retained firing origins

The complete generated edge action is tested on arbitrary stage arguments.
Plain and zero-framed edge presentations have the same whole readout while
their independently supplied receipt origins remain distinct, including
after the actual native compiler action. All five authored source rule
domains are exercised through the new postcomposed compiler.

The independent weighted models distinguish endpoint-preserving operations
from actual actions and independently test generated model admission.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingGeneratedParallelActionControls

open _root_.CategoryTheory Opposite MonoidalCategory CartesianMonoidalCategory
open Mettapedia.CategoryTheory
open Mettapedia.GSLT.Topos.PresheafTheoryAction
open NamePassingGeneratedParallelActionNative

universe k

namespace ActualCompiler

def supplied (origin : Origin.{k}) :
    ((inverseImage compilerFunctor).obj targetReceipts).obj (op (domain origin)) :=
  ⟨origin, ULift.up (𝟙 (targetDomain origin))⟩

theorem all_five_native_firings (origin : Origin.{k}) :
    (nativeFiring.app (op (domain origin)) (supplied origin)).down ≫
      (NamePassingGeneratedParallelActionComparison.resultComparison origin).hom =
        (NamePassingGeneratedParallelActionComparison.premiseComparison origin).hom ≫
          NamePassingGeneratedParallelActionComparison.firing origin := by
  have actual := whole_independent_firing (supplied origin)
  erw [Category.id_comp] at actual
  exact actual

theorem all_five_authored_endpoints (origin : Origin.{k}) (side : Bool) :
    ((nativeEndpoint side).app (op (domain origin)) (supplied origin)).down =
      compilerFunctor.map (NamePassingGeneratedNativeLanguage.declaredEndpoint origin side) := by
  have actual := whole_endpoint (supplied origin) side
  erw [Category.id_comp] at actual
  exact actual

def simultaneousDomain : Source.{k} := domain ⟨.beta⟩ ⊗ domain ⟨.fetch⟩

def betaReceipt : ((inverseImage compilerFunctor).obj targetReceipts.{k}).obj (op simultaneousDomain) :=
  ⟨⟨.beta⟩, ULift.up (compilerFunctor.map (fst (domain ⟨.beta⟩) (domain ⟨.fetch⟩)))⟩

def fetchReceipt : ((inverseImage compilerFunctor).obj targetReceipts.{k}).obj (op simultaneousDomain) :=
  ⟨⟨.fetch⟩, ULift.up (compilerFunctor.map (snd (domain ⟨.beta⟩) (domain ⟨.fetch⟩)))⟩

theorem beta_fetch_origins_remain_distinct : betaReceipt.{k} ≠ fetchReceipt := by
  intro same
  have origins := congrArg Sigma.fst same
  have impossible := congrArg ULift.down origins
  cases impossible

theorem future_whole_argument {first second : Source.{k}} (change : first ⟶ second)
    (receipt : ((inverseImage compilerFunctor).obj targetReceipts).obj (op second)) :
    (((inverseImage compilerFunctor).obj targetReceipts).map change.op receipt).2.down =
      compilerFunctor.map change ≫ receipt.2.down := rfl

end ActualCompiler

namespace EdgeClasses

abbrev operations := BindingClosedGeneratedParallelAction.operations.{k}

inductive ClosureOrigin where
  | plain
  | emptyFrame
  deriving DecidableEq

abbrev Index := ULift.{k} ClosureOrigin

def domains (_ : Index.{k}) : Target.{k} := operations.edge

def arrows : ∀ origin : Index.{k}, domains origin ⟶ operations.edge
  | ⟨.plain⟩ => 𝟙 operations.edge
  | ⟨.emptyFrame⟩ => CartesianMonoidAction.unitDiagram operations

def receipts : Target.{k}ᵒᵖ ⥤ Type k :=
  IndexedArrowReceiptPresheaf.receipts.{k,k,k,k} domains

def evaluate : receipts.{k} ⟶ uliftYoneda.{k}.obj operations.edge :=
  IndexedArrowReceiptPresheaf.evaluate domains arrows

def supplied {stage : Target.{k}} (origin : Index) (argument : stage ⟶ operations.edge) :
    receipts.obj (op stage) := ⟨origin, ULift.up argument⟩

theorem zero_frame_whole_readout {stage : Target.{k}} (argument : stage ⟶ operations.edge) :
    evaluate.app (op stage) (supplied ⟨.emptyFrame⟩ argument) =
      evaluate.app (op stage) (supplied ⟨.plain⟩ argument) := by
  change ULift.up (argument ≫ CartesianMonoidAction.unitDiagram operations) = ULift.up (argument ≫ 𝟙 _)
  rw [BindingClosedGeneratedParallelAction.action_laws.unit]

theorem different_receipt_origins {stage : Target.{k}} (argument : stage ⟶ operations.edge) :
    supplied ⟨.plain⟩ argument ≠ supplied ⟨.emptyFrame⟩ argument := by
  apply IndexedArrowReceiptPresheaf.different_origins domains ⟨.plain⟩ ⟨.emptyFrame⟩ _ argument argument
  intro same
  have impossible := congrArg ULift.down same
  cases impossible

theorem no_edge_origin_decoder :
    ¬ ∃ decoder : (uliftYoneda.{k}.obj operations.edge).obj (op operations.edge) → Index.{k},
      ∀ origin, decoder (evaluate.app (op operations.edge) (supplied origin (𝟙 operations.edge))) = origin := by
  rintro ⟨decoder, reads⟩
  have actual := zero_frame_whole_readout (𝟙 operations.edge)
  have same := (reads ⟨.emptyFrame⟩).symm.trans ((congrArg decoder actual).trans (reads ⟨.plain⟩))
  have impossible := congrArg ULift.down same
  cases impossible

theorem complete_associativity {stage : Target.{k}} (edge : stage ⟶ operations.edge)
    (first second : stage ⟶ operations.scalar) :
    CartesianMonoidAction.apply operations (CartesianMonoidAction.apply operations edge first) second =
      CartesianMonoidAction.apply operations edge (CartesianMonoidAction.product operations first second) :=
  BindingClosedGeneratedParallelAction.parallel_associativity edge first second

theorem complete_frame_exchange {stage : Target.{k}} (edge : stage ⟶ operations.edge)
    (first second : stage ⟶ operations.scalar) :
    CartesianMonoidAction.apply operations (CartesianMonoidAction.apply operations edge first) second =
      CartesianMonoidAction.apply operations (CartesianMonoidAction.apply operations edge second) first :=
  BindingClosedGeneratedParallelAction.parallel_frame_exchange edge first second

def nativeEvaluate := nativeRead evaluate.{k}

theorem actual_native_zero_frame {stage : Source.{k}}
    (argument : compilerFunctor.obj stage ⟶ operations.edge) :
    nativeEvaluate.app (op stage) (supplied ⟨.emptyFrame⟩ argument) =
      nativeEvaluate.app (op stage) (supplied ⟨.plain⟩ argument) := by
  rw [nativeEvaluate, native_read_complete]
  exact zero_frame_whole_readout argument

theorem actual_native_origin_preservation {first second : Source.{k}} (change : first ⟶ second)
    (origin : Index) (argument : compilerFunctor.obj second ⟶ operations.edge) :
    (((inverseImage compilerFunctor).obj receipts).map change.op (supplied origin argument)).1 = origin := rfl

theorem future_zero_frame_whole_readout {first second : Target.{k}} (change : first ⟶ second)
    (argument : second ⟶ operations.edge) :
    evaluate.app (op first) (receipts.map change.op (supplied ⟨.emptyFrame⟩ argument)) =
      ULift.up (change ≫ argument) := by
  change ULift.up ((change ≫ argument) ≫ CartesianMonoidAction.unitDiagram operations) = _
  rw [BindingClosedGeneratedParallelAction.action_laws.unit, Category.comp_id]

end EdgeClasses

namespace IndependentModel

open CartesianMonoidAction.Controls

def varyingEdge : Nat ⟶ Evidence := TypeCat.ofHom (fun stage => (stage, stage + 3, 2 * stage + 7))
def varyingFrame : Nat ⟶ Nat := TypeCat.ofHom (fun stage => stage + 1)

def acted : Nat ⟶ Evidence := CartesianMonoidAction.apply (arithmetic false) varyingEdge varyingFrame

theorem complete_nonconstant_readout (stage : Nat) :
    acted stage = (stage + (stage + 1), stage + 3 + (stage + 1), 2 * stage + 7) :=
  complete_retained_readout _ _ _ _

theorem complete_future_readout (stage : Nat) :
    (TypeCat.ofHom Nat.succ ≫ acted) stage =
      ((stage + 1) + ((stage + 1) + 1), (stage + 1) + 3 + ((stage + 1) + 1), 2 * (stage + 1) + 7) :=
  complete_nonconstant_readout (stage + 1)

theorem omitting_future_change_loses_evidence :
    (TypeCat.ofHom Nat.succ ≫ acted) 1 ≠ acted 1 := by
  intro same
  have impossible := congrArg (fun edge : Evidence => edge.2.2) same
  exact (by decide : (11 : Nat) ≠ 9) impossible

end IndependentModel

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingGeneratedParallelActionControls
