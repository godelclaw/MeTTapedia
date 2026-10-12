import Mettapedia.GSLT.Core.RelativeClosedQuantifiedRuleFrames
import Mettapedia.GSLT.Core.PositionedRewriteFiringReceipt
import Mettapedia.GSLT.Core.RelativeClosedPositionedModalControlData
import Mettapedia.GSLT.Core.RelativeClosedQuantifiedAdjunctionControls
import Mettapedia.CategoryTheory.HigherOrderInternalPredicateImplication

/-!
# Numeric firing receipts through the actual quantified completion

The existing independently authored rule adds its two parameters and takes
a successor. The actual completion unit transports the complete match and
event. Its earned weak-map extension to the native model recovers every
source and target reading. Distinct authored origins give distinct receipts
despite equal events. A future parameter changes the readout, so a constant
or dropped-input interpretation cannot satisfy the complete comparison.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.GSLT.Core.RelativeClosedQuantifiedRuleFrameControls

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open Mettapedia.CategoryTheory ProgramReductionTheory AuthoredClosedTheory
open RelativeClosedQuantified
open PositionedRewriteFiringReceipt

open RelativeClosedPositionedModalControlData
open RelativeClosedQuantifiedRuleFrames

abbrev predicates := RelativeClosedQuantifiedAdjunctionControls.nativeOperations.predicates
abbrev laws := RelativeClosedQuantifiedAdjunctionControls.nativeOperations.laws
abbrev source := conjunctive theory predicates laws
abbrev included := generatedInclusion theory predicates laws
abbrev generated := generatedTheory theory predicates laws

abbrev target : QuantifiedClosedTheory.{1} where
  closed := theory.closed
  operations := RelativeClosedQuantifiedAdjunctionControls.nativeOperations

def supplied : ConjunctiveClosedTheory.Map source target.conjunctive where
  declarations := InternalConjunctiveObject.Map.identity predicates
  finite := by change PreservesFiniteLimits (𝟭 Base); infer_instance
  closed := by
    change MonoidalClosedFunctor (𝟭 Base)
    exact cartesianClosedFunctorOfLeftAdjointPreservesBinaryProducts _ Adjunction.id

abbrev folded := Extension.extendMap supplied
abbrev completeDiagram := included.closed.functor ⋙ folded.functor

def recovery : completeDiagram ≅ 𝟭 Base :=
  eqToIso (Extension.complete_base_recovered supplied)

def decode {before after : Base} (reading : included.closed.functor.obj before ⟶
    included.closed.functor.obj after) : before ⟶ after :=
  recovery.inv.app before ≫ folded.functor.map reading ≫ recovery.hom.app after

theorem complete_arrow_recovered {before after : Base} (reading : before ⟶ after) :
    decode (included.closed.functor.map reading) = reading := by
  change recovery.inv.app before ≫ completeDiagram.map reading ≫ recovery.hom.app after = reading
  rw [recovery.hom.naturality, ← Category.assoc, recovery.inv_hom_id_app, Category.id_comp]
  rfl

abbrev rules (_ : Bool) := rule
abbrev frames (origin : Bool) : PositionedRewriteModal.Frame (rules origin) := frame

def receipt (origin : Bool) : Receipt rules frames rule.parameters where
  origin := origin
  assignment := frame.forget
  assay := frame.instantiate
  compatible := frame.square.w

theorem complete_parameter_instance (origin : Bool) :
    (receipt origin).parameterInstance = 𝟙 rule.parameters := by
  change frame.suppliedInstance frame.forget frame.instantiate frame.square.w = _
  apply frame.square.hom_ext
  · exact (frame.suppliedInstance_assignment _ _ _).trans (Category.id_comp _).symm
  · exact (frame.suppliedInstance_assay _ _ _).trans (Category.id_comp _).symm

theorem complete_event (origin : Bool) : (receipt origin).event = rule.action := by
  change (receipt origin).parameterInstance ≫ rule.action = _
  rw [complete_parameter_instance, Category.id_comp]

abbrev translated (origin : Bool) := (receipt origin).transport included

theorem complete_translated_event (origin : Bool) :
    (translated origin).event = included.closed.functor.map rule.action ≫ included.reduction := by
  exact ((receipt origin).event_transport included).trans
    (congrArg (fun arrow => included.closed.functor.map arrow ≫ included.reduction) (complete_event origin))

theorem translated_source (origin : Bool) :
    (translated origin).event ≫ generated.source = included.closed.functor.map rule.left := by
  rw [complete_translated_event, Category.assoc, included.source]
  change included.closed.functor.map rule.action ≫
    (included.closed.functor.map theory.source ≫ 𝟙 _) = _
  rw [Category.comp_id, ← included.closed.functor.map_comp, rule.source]

theorem translated_target (origin : Bool) :
    (translated origin).event ≫ generated.target = included.closed.functor.map rule.right := by
  rw [complete_translated_event, Category.assoc, included.target]
  change included.closed.functor.map rule.action ≫
    (included.closed.functor.map theory.target ≫ 𝟙 _) = _
  rw [Category.comp_id, ← included.closed.functor.map_comp, rule.target]

def recoveredSource (origin : Bool) : rule.parameters ⟶ program :=
  decode ((translated origin).event ≫ generated.source)

def recoveredTarget (origin : Bool) : rule.parameters ⟶ program :=
  decode ((translated origin).event ≫ generated.target)

theorem complete_source_reading (origin : Bool) : recoveredSource origin = rule.left := by
  exact (congrArg decode (translated_source origin)).trans (complete_arrow_recovered rule.left)

theorem complete_target_reading (origin : Bool) : recoveredTarget origin = rule.right := by
  exact (congrArg decode (translated_target origin)).trans (complete_arrow_recovered rule.right)

theorem source_numbers (origin : Bool) (pair : Nat × Nat) :
    base.map (recoveredSource origin) ((Types.binaryProductIso Nat Nat).inv pair) =
      pair.1 + pair.2 := by
  rw [complete_source_reading]
  exact the_actual_rule_retains_both_numbers pair

theorem target_numbers (origin : Bool) (pair : Nat × Nat) :
    base.map (recoveredTarget origin) ((Types.binaryProductIso Nat Nat).inv pair) =
      pair.1 + pair.2 + 1 := by
  rw [complete_target_reading]
  exact the_actual_reduct_retains_both_numbers pair

theorem two_receipts_one_actual_event :
    translated false ≠ translated true ∧
      (translated false).event = (translated true).event := by
  refine ⟨Receipt.transported_origins_separate (receipt false) included Bool.false_ne_true, ?_⟩
  rw [complete_translated_event, complete_translated_event]

def future : rule.parameters ⟶ rule.parameters := upward.map
  ((Types.binaryProductIso Nat Nat).hom ≫ TypeCat.ofHom (fun pair : Nat × Nat => (pair.1, pair.2 + 1)) ≫
    (Types.binaryProductIso Nat Nat).inv)

theorem supplied_future_event (origin : Bool) :
    (((receipt origin).precompose future).transport included).event =
      included.closed.functor.map future ≫
        (included.closed.functor.map rule.action ≫ included.reduction) := by
  exact ((receipt origin).event_transport_future included future).trans
    (congrArg (fun arrow => included.closed.functor.map future ≫
      (included.closed.functor.map arrow ≫ included.reduction)) (complete_event origin))

theorem translated_future_target (origin : Bool) :
    (((receipt origin).precompose future).transport included).event ≫ generated.target =
      included.closed.functor.map (future ≫ rule.right) := by
  rw [Receipt.event_transport_target]
  change included.closed.functor.map
    (((receipt origin).precompose future).event ≫ theory.target) ≫ 𝟙 _ = _
  rw [Category.comp_id, Receipt.event_precompose, complete_event, Category.assoc, rule.target]

theorem recovered_future_target (origin : Bool) :
    decode ((((receipt origin).precompose future).transport included).event ≫ generated.target) =
      future ≫ rule.right :=
  (congrArg decode (translated_future_target origin)).trans (complete_arrow_recovered _)

theorem neither_input_can_be_dropped :
    base.map (recoveredTarget false) ((Types.binaryProductIso Nat Nat).inv (2, 3)) = (6 : Nat) ∧
    base.map (recoveredTarget false) ((Types.binaryProductIso Nat Nat).inv (2, 4)) = (7 : Nat) ∧
    base.map (recoveredTarget false) ((Types.binaryProductIso Nat Nat).inv (3, 3)) = (7 : Nat) :=
  ⟨target_numbers false (2, 3), target_numbers false (2, 4), target_numbers false (3, 3)⟩

theorem future_changes_target :
    future ≫ recoveredTarget false ≠ recoveredTarget false := by
  intro same
  have point := congrArg
    (fun arrow : rule.parameters ⟶ program => base.map arrow ((Types.binaryProductIso Nat Nat).inv (2, 3))) same
  have before := target_numbers false (2, 3)
  have after := target_numbers false (2, 4)
  have futurePoint : base.map future ((Types.binaryProductIso Nat Nat).inv (2, 3)) =
      (Types.binaryProductIso Nat Nat).inv (2, 4) := by
    change (Types.binaryProductIso Nat Nat).inv
      ((fun pair : Nat × Nat => (pair.1, pair.2 + 1))
        ((Types.binaryProductIso Nat Nat).hom ((Types.binaryProductIso Nat Nat).inv (2, 3)))) = _
    have retained : (Types.binaryProductIso Nat Nat).hom
        ((Types.binaryProductIso Nat Nat).inv (2, 3)) = (2, 3) :=
      congrArg (fun arrow : Nat × Nat ⟶ Nat × Nat => arrow (2, 3))
        (Types.binaryProductIso Nat Nat).inv_hom_id
    rw [retained]
  have changed : base.map (future ≫ recoveredTarget false)
      ((Types.binaryProductIso Nat Nat).inv (2, 3)) = (7 : Nat) := by
    change base.map (recoveredTarget false)
      (base.map future ((Types.binaryProductIso Nat Nat).inv (2, 3))) = _
    rw [futurePoint]
    exact after
  exact (by decide : (7 : Nat) ≠ 6) (changed.symm.trans (point.trans before))

end Mettapedia.GSLT.Core.RelativeClosedQuantifiedRuleFrameControls
