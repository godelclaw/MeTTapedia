import Mettapedia.GSLT.Core.RelativeClosedQuantifiedRuleFrameControls

/-!
# A nonidentity program comparison changes the actual reduct

An independently renamed successor relation exchanges program values zero
and one. The genuine program theory map carries this nonidentity comparison
in both event endpoints. Its transported frame therefore reads one-to-zero
at the zero/zero input, whereas omitting the outgoing program comparison
reads zero-to-one. The whole quantified operator square applies to the same
map with the unchanged native predicate presentation.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.GSLT.Core.PositionedRewriteProgramComparisonControls

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open Mettapedia.CategoryTheory ProgramReductionTheory AuthoredClosedTheory
open RelativeClosedPositionedModalControlData
open InternalPredicateFunctionObject InternalPredicateFunctionObjectMaps
open InternalPredicatePositionedModalMaps

def programComparison : program ≅ program :=
  upward.mapIso (Equiv.swap (0 : Nat) 1).toIso

def endpoints : theory.Event ⟶ program ⨯ program :=
  theory.reduction.arrow ≫ (prod.mapIso programComparison programComparison).hom

instance endpoints_mono : Mono endpoints := by unfold endpoints; infer_instance

def renamedTheory : Theory.{1,1} where
  closed := theory.closed
  program := program
  reduction := Subobject.mk endpoints

def eventComparison : theory.Event ≅ renamedTheory.Event :=
  (Subobject.underlyingIso endpoints).symm

theorem source_reading : eventComparison.hom ≫ renamedTheory.source = theory.source ≫ programComparison.hom := by
  change (Subobject.underlyingIso endpoints).inv ≫ ((Subobject.mk endpoints).arrow ≫ prod.fst) = _
  rw [← Category.assoc, Subobject.underlyingIso_arrow]
  change (theory.reduction.arrow ≫ prod.map programComparison.hom programComparison.hom) ≫ prod.fst = _
  rw [Category.assoc, prod.map_fst, ← Category.assoc]
  rfl

theorem target_reading : eventComparison.hom ≫ renamedTheory.target = theory.target ≫ programComparison.hom := by
  change (Subobject.underlyingIso endpoints).inv ≫ ((Subobject.mk endpoints).arrow ≫ prod.snd) = _
  rw [← Category.assoc, Subobject.underlyingIso_arrow]
  change (theory.reduction.arrow ≫ prod.map programComparison.hom programComparison.hom) ≫ prod.snd = _
  rw [Category.assoc, prod.map_snd, ← Category.assoc]
  rfl

def programMap : Map theory renamedTheory where
  closed := LambdaTheoryMap.id theory.closed
  program := programComparison
  reduction := eventComparison.hom
  source := source_reading
  target := target_reading

abbrev actualFrame := frame.transport programMap

def sourceReading : rule.parameters ⟶ program := actualFrame.instantiate ≫ actualFrame.plug

theorem entire_source_reading : sourceReading = rule.left ≫ programComparison.hom :=
  actualFrame.source

def reductReading : rule.parameters ⟶ program :=
  (actualFrame.outgoing : rule.parameters ⟶ frame.assay ⨯ program) ≫
    (prod.snd : frame.assay ⨯ program ⟶ program)

theorem entire_reduct_reading : reductReading = rule.right ≫ programComparison.hom := by
  change prod.lift frame.instantiate (rule.right ≫ programComparison.hom) ≫ prod.snd = _
  exact prod.lift_snd _ _

theorem program_comparison_is_nonidentity : programComparison.hom ≠ 𝟙 program := by
  intro same
  have point := congrArg (fun arrow : program ⟶ program => base.map arrow (0 : Nat)) same
  change Equiv.swap (0 : Nat) 1 0 = (0 : Nat) at point
  exact (by decide : (1 : Nat) ≠ 0)
    ((Equiv.swap_apply_left (0 : Nat) 1).symm.trans point)

theorem actual_zero_pair_source :
    base.map sourceReading ((Types.binaryProductIso Nat Nat).inv (0, 0)) = (1 : Nat) := by
  rw [entire_source_reading]
  change Equiv.swap (0 : Nat) 1 (base.map rule.left ((Types.binaryProductIso Nat Nat).inv (0, 0))) = 1
  rw [the_actual_rule_retains_both_numbers]
  exact Equiv.swap_apply_left 0 1

theorem actual_zero_pair_reduct :
    base.map reductReading ((Types.binaryProductIso Nat Nat).inv (0, 0)) = (0 : Nat) := by
  rw [entire_reduct_reading]
  change Equiv.swap (0 : Nat) 1 (base.map rule.right ((Types.binaryProductIso Nat Nat).inv (0, 0))) = 0
  rw [the_actual_reduct_retains_both_numbers]
  exact Equiv.swap_apply_right 0 1

theorem omitted_comparison_reduct :
    base.map rule.right ((Types.binaryProductIso Nat Nat).inv (0, 0)) = (1 : Nat) :=
  the_actual_reduct_retains_both_numbers (0, 0)

theorem outgoing_comparison_cannot_be_omitted : reductReading ≠ rule.right := by
  intro same
  have point := congrArg
    (fun arrow : rule.parameters ⟶ program => base.map arrow ((Types.binaryProductIso Nat Nat).inv (0, 0))) same
  exact (by decide : (0 : Nat) ≠ 1)
    (actual_zero_pair_reduct.symm.trans (point.trans omitted_comparison_reduct))

abbrev nativeOperations := RelativeClosedQuantifiedAdjunctionControls.nativeOperations
abbrev nativeLogic := RelativeClosedQuantifiedAdjunctionControls.nativeLogic

def nativeComparison : PositionedRewritePredicateTransport.PredicateComparison programMap nativeOperations nativeOperations where
  proposition := Iso.refl _
  truth := (InternalConjunctiveObject.Map.identity nativeOperations.predicates).truth
  conjunction := (InternalConjunctiveObject.Map.identity nativeOperations.predicates).conjunction

local instance native_finite : PreservesFiniteLimits nativeComparison.predicates.functor :=
  programMap.closed.preservesFiniteLimits
local instance native_closed : MonoidalClosedFunctor nativeComparison.predicates.functor :=
  programMap.closed.preservesExponentials

theorem complete_nonidentity_operator_square :
    programMap.closed.functor.map (modalityOperator nativeOperations
        (HigherOrderInternalPredicateImplication.qualification nativeLogic)
        frame.forget frame.focus frame.instantiate frame.outgoing) ≫
        (powerComparison nativeComparison.predicates frame.carrier).hom =
      (PositionedRewritePredicateTransport.inputsComparison nativeComparison frame).hom ≫
        modalityOperator nativeOperations (HigherOrderInternalPredicateImplication.qualification nativeLogic)
          actualFrame.forget actualFrame.focus actualFrame.instantiate actualFrame.outgoing :=
  PositionedRewritePredicateTransport.complete_operator_square nativeComparison
    (HigherOrderInternalPredicateImplication.qualification nativeLogic)
    (HigherOrderInternalPredicateImplication.qualification nativeLogic) frame

end Mettapedia.GSLT.Core.PositionedRewriteProgramComparisonControls
