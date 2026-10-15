import Mettapedia.CategoryTheory.RelativeClosedQuantifiedProgramMonad
import Mettapedia.GSLT.Core.RelativeClosedQuantifiedProgramMapControls
import Mettapedia.GSLT.Core.RelativeClosedQuantifiedProgramFrameAction

/-!
# Independent operational controls for the program adjunction

A native numeric successor theory is interpreted in the independently
renamed successor relation. The categorical extension recovers its full
endpoint arrows and actual firing. The identity interpretation of the
generated theory is independently supplied; its universal comparison
recovers the whole event map. Iterated completion then folds an actual
authored firing through the earned monad multiplication.

The unchanged local predicate declarations do not permit dropping the
nonidentity program comparison: the resulting event source square fails.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.GSLT.Core.RelativeClosedQuantifiedProgramTheoryControls

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open Mettapedia.CategoryTheory
open RelativeClosedPositionedModalControlData
open RelativeClosedQuantifiedProgram

abbrev nativeOperations := RelativeClosedQuantifiedAdjunctionControls.nativeOperations

def source : ConjunctiveProgramTheory.{1} where
  programTheory := theory
  operations := nativeOperations.predicates
  laws := nativeOperations.laws

def target : QuantifiedProgramTheory.{1} where
  programTheory := PositionedRewriteProgramComparisonControls.renamedTheory
  operations := nativeOperations

def supplied : ConjunctiveProgramTheory.Map source target.conjunctive :=
  HomEquivalence.categoryMap source target RelativeClosedQuantifiedProgramMapControls.supplied

abbrev extended := HomEquivalence.extension source target supplied
abbrev recovered := HomEquivalence.extension_restriction source target supplied

theorem complete_native_source_reading :
    recovered.comparison.inv.app rule.parameters ≫
        extended.functor.map ((unitMap source).functor.map rule.left) ≫ extended.program.hom =
      PositionedRewriteProgramComparisonControls.sourceReading :=
  RelativeClosedQuantifiedProgramMapControls.complete_source_readout

theorem complete_native_target_reading :
    recovered.comparison.inv.app rule.parameters ≫
        extended.functor.map ((unitMap source).functor.map rule.right) ≫ extended.program.hom =
      PositionedRewriteProgramComparisonControls.reductReading :=
  RelativeClosedQuantifiedProgramMapControls.complete_target_readout

theorem complete_native_actual_firing :
    recovered.comparison.inv.app rule.parameters ≫ extended.functor.map
        (RelativeClosedQuantifiedRuleFrameControls.translated false).event ≫ extended.reduction =
      rule.action ≫ PositionedRewriteProgramComparisonControls.eventComparison.hom :=
  RelativeClosedQuantifiedProgramMapControls.complete_actual_firing

abbrev actualGeneratedFrame := RelativeClosedQuantifiedRuleFrames.generatedFrame
  theory nativeOperations.predicates nativeOperations.laws frame
abbrev actualComparison := RelativeClosedQuantifiedProgramMapControls.supplied.predicateComparison
abbrev nativeImplication := HigherOrderInternalPredicateImplication.qualification
  RelativeClosedQuantifiedAdjunctionControls.nativeLogic

theorem complete_independent_target_frame_operator :
    extended.functor.map (RelativeClosedQuantifiedRuleFrames.actualOperator nativeImplication frame) ≫
        (InternalPredicateFunctionObjectMaps.powerComparison actualComparison.predicates
          actualGeneratedFrame.carrier).hom =
      (PositionedRewritePredicateTransport.inputsComparison actualComparison actualGeneratedFrame).hom ≫
        InternalPredicatePositionedModalMaps.modalityOperator nativeOperations nativeImplication
          (actualGeneratedFrame.transport extended.underlying).forget
          (actualGeneratedFrame.transport extended.underlying).focus
          (actualGeneratedFrame.transport extended.underlying).instantiate
          (actualGeneratedFrame.transport extended.underlying).outgoing :=
  RelativeClosedQuantifiedProgramMapControls.supplied.complete_frame_operator_square
    nativeImplication nativeImplication frame

def identityCandidate : QuantifiedProgramTheory.Map (freeObject source) (freeObject source) :=
  ConjunctiveProgramTheory.Map.identity (freeObject source).conjunctive

def identityComparison : QuantifiedProgramTheory.MapIso identityCandidate
    (HomEquivalence.extension source (freeObject source)
      (HomEquivalence.restriction source (freeObject source) identityCandidate)) :=
  HomEquivalence.completeComparison source (freeObject source)
    (HomEquivalence.restriction source (freeObject source) identityCandidate) identityCandidate
      (ConjunctiveProgramTheory.MapIso.refl _)

theorem entire_independent_identity_event_reading :
    identityComparison.comparison.hom.app (freeObject source).programTheory.Event ≫
        (HomEquivalence.extension source (freeObject source)
          (HomEquivalence.restriction source (freeObject source) identityCandidate)).reduction =
      𝟙 (freeObject source).programTheory.Event :=
  identityComparison.reduction_square

theorem independent_identity_hom_roundtrip :
    (HomEquivalence.homEquiv source (freeObject source)).symm
        ((HomEquivalence.homEquiv source (freeObject source))
          (QuantifiedProgramTheory.classOf identityCandidate)) =
      QuantifiedProgramTheory.classOf identityCandidate :=
  (HomEquivalence.homEquiv source (freeObject source)).symm_apply_apply _

theorem multiplication_recovers_actual_authored_firing :
    (Construction.baseComparison source).comparison.inv.app
        ((unitMap source).functor.obj rule.parameters) ≫
      (Construction.multiplicationMap source).functor.map
        ((unitMap (freeObject source).conjunctive).functor.map
            (RelativeClosedQuantifiedRuleFrameControls.translated false).event ≫
          (unitMap (freeObject source).conjunctive).reduction) ≫
        (Construction.multiplicationMap source).reduction =
      (RelativeClosedQuantifiedRuleFrameControls.translated false).event :=
  Construction.complete_event_readout source _

theorem identity_program_endpoint_rejected :
    PositionedRewriteProgramComparisonControls.eventComparison.hom ≫
        PositionedRewriteProgramComparisonControls.renamedTheory.source ≠ theory.source := by
  intro same
  have sourceEqual : PositionedRewriteProgramComparisonControls.sourceReading = rule.left := by
    calc
      _ = rule.left ≫ PositionedRewriteProgramComparisonControls.programComparison.hom :=
        PositionedRewriteProgramComparisonControls.entire_source_reading
      _ = (rule.action ≫ theory.source) ≫
          PositionedRewriteProgramComparisonControls.programComparison.hom :=
        congrArg (fun arrow => arrow ≫ PositionedRewriteProgramComparisonControls.programComparison.hom)
          rule.source.symm
      _ = rule.action ≫ (PositionedRewriteProgramComparisonControls.eventComparison.hom ≫
          PositionedRewriteProgramComparisonControls.renamedTheory.source) :=
        (Category.assoc _ _ _).trans (congrArg (fun arrow => rule.action ≫ arrow)
          PositionedRewriteProgramComparisonControls.source_reading.symm)
      _ = rule.left := (congrArg (fun arrow => rule.action ≫ arrow) same).trans rule.source
  have point := congrArg (fun arrow : rule.parameters ⟶ program =>
    base.map arrow ((Types.binaryProductIso Nat Nat).inv (0, 0))) sourceEqual
  exact (by decide : (1 : Nat) ≠ 0)
    (PositionedRewriteProgramComparisonControls.actual_zero_pair_source.symm.trans
      (point.trans (the_actual_rule_retains_both_numbers (0, 0))))

end Mettapedia.GSLT.Core.RelativeClosedQuantifiedProgramTheoryControls
