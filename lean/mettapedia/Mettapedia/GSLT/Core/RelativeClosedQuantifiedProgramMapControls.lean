import Mettapedia.GSLT.Core.RelativeClosedQuantifiedProgramMaps
import Mettapedia.GSLT.Core.PositionedRewriteProgramComparisonControls

/-!
# An independently renamed native target for the program-map extension

The target relation and nonidentity program comparison precede the
extension. The supplied native predicate declarations earn the weak map
out of the actual quantified completion. Both complete endpoint arrows
and the actual supplied firing agree with the independent renamed rule.
The zero/zero firing therefore reads one-to-zero; interpreting it as the
original zero-to-one firing violates the complete target comparison.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.GSLT.Core.RelativeClosedQuantifiedProgramMapControls

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open Mettapedia.CategoryTheory ProgramReductionTheory
open RelativeClosedPositionedModalControlData
open RelativeClosedQuantifiedProgramMaps

abbrev nativeOperations := RelativeClosedQuantifiedAdjunctionControls.nativeOperations
abbrev nativeSource := RelativeClosedQuantifiedRuleFrames.conjunctive theory
  nativeOperations.predicates nativeOperations.laws

def supplied : Supplied theory PositionedRewriteProgramComparisonControls.renamedTheory
    nativeOperations.predicates nativeOperations.laws nativeOperations where
  declarations := ConjunctiveClosedTheory.Map.identity nativeSource
  program := PositionedRewriteProgramComparisonControls.programComparison
  event := PositionedRewriteProgramComparisonControls.eventComparison.hom
  sourceEquation := PositionedRewriteProgramComparisonControls.source_reading
  targetEquation := PositionedRewriteProgramComparisonControls.target_reading

abbrev included := RelativeClosedQuantifiedRuleFrames.generatedInclusion theory
  nativeOperations.predicates nativeOperations.laws
abbrev generated := RelativeClosedQuantifiedRuleFrames.generatedTheory theory
  nativeOperations.predicates nativeOperations.laws

def sourceReadout : rule.parameters ⟶ program :=
  supplied.baseComparison.comparison.inv.app rule.parameters ≫
    supplied.extension.functor.map (included.closed.functor.map rule.left) ≫ supplied.extendedProgram.hom

def targetReadout : rule.parameters ⟶ program :=
  supplied.baseComparison.comparison.inv.app rule.parameters ≫
    supplied.extension.functor.map (included.closed.functor.map rule.right) ≫ supplied.extendedProgram.hom

theorem complete_source_readout : sourceReadout = PositionedRewriteProgramComparisonControls.sourceReading :=
  (supplied.complete_program_readout rule.left).trans PositionedRewriteProgramComparisonControls.entire_source_reading.symm

theorem complete_target_readout : targetReadout = PositionedRewriteProgramComparisonControls.reductReading :=
  (supplied.complete_program_readout rule.right).trans PositionedRewriteProgramComparisonControls.entire_reduct_reading.symm

def actualFiring : rule.parameters ⟶ PositionedRewriteProgramComparisonControls.renamedTheory.Event :=
  supplied.baseComparison.comparison.inv.app rule.parameters ≫
    supplied.extension.functor.map
      (RelativeClosedQuantifiedRuleFrameControls.translated false).event ≫ supplied.extendedEvent

theorem complete_actual_firing :
    actualFiring = rule.action ≫ PositionedRewriteProgramComparisonControls.eventComparison.hom :=
  (congrArg (fun arrow : included.closed.functor.obj rule.parameters ⟶ generated.Event =>
    supplied.baseComparison.comparison.inv.app rule.parameters ≫ supplied.extension.functor.map arrow ≫
      supplied.extendedEvent) (RelativeClosedQuantifiedRuleFrameControls.complete_translated_event false)).trans
        (supplied.complete_event_readout rule.action)

theorem actual_firing_source :
    actualFiring ≫ PositionedRewriteProgramComparisonControls.renamedTheory.source = sourceReadout :=
  (congrArg (fun event => event ≫ PositionedRewriteProgramComparisonControls.renamedTheory.source)
    complete_actual_firing).trans
      ((Category.assoc _ _ _).trans
        ((congrArg (fun endpoint => rule.action ≫ endpoint)
          PositionedRewriteProgramComparisonControls.source_reading).trans
            ((Category.assoc _ _ _).symm.trans
              ((congrArg (fun endpoint => endpoint ≫ PositionedRewriteProgramComparisonControls.programComparison.hom)
                rule.source).trans
                  (PositionedRewriteProgramComparisonControls.entire_source_reading.symm.trans
                    complete_source_readout.symm)))))

theorem actual_firing_target :
    actualFiring ≫ PositionedRewriteProgramComparisonControls.renamedTheory.target = targetReadout :=
  (congrArg (fun event => event ≫ PositionedRewriteProgramComparisonControls.renamedTheory.target)
    complete_actual_firing).trans
      ((Category.assoc _ _ _).trans
        ((congrArg (fun endpoint => rule.action ≫ endpoint)
          PositionedRewriteProgramComparisonControls.target_reading).trans
            ((Category.assoc _ _ _).symm.trans
              ((congrArg (fun endpoint => endpoint ≫ PositionedRewriteProgramComparisonControls.programComparison.hom)
                rule.target).trans
                  (PositionedRewriteProgramComparisonControls.entire_reduct_reading.symm.trans
                    complete_target_readout.symm)))))

theorem independent_native_source :
    base.map sourceReadout ((Types.binaryProductIso Nat Nat).inv (0, 0)) = (1 : Nat) :=
  (congrArg (fun arrow : rule.parameters ⟶ program =>
    base.map arrow ((Types.binaryProductIso Nat Nat).inv (0, 0))) complete_source_readout).trans
      PositionedRewriteProgramComparisonControls.actual_zero_pair_source

theorem independent_native_target :
    base.map targetReadout ((Types.binaryProductIso Nat Nat).inv (0, 0)) = (0 : Nat) :=
  (congrArg (fun arrow : rule.parameters ⟶ program =>
    base.map arrow ((Types.binaryProductIso Nat Nat).inv (0, 0))) complete_target_readout).trans
      PositionedRewriteProgramComparisonControls.actual_zero_pair_reduct

theorem original_reduct_is_rejected : targetReadout ≠ rule.right := by
  intro same
  exact PositionedRewriteProgramComparisonControls.outgoing_comparison_cannot_be_omitted
    (complete_target_readout.symm.trans same)

end Mettapedia.GSLT.Core.RelativeClosedQuantifiedProgramMapControls
