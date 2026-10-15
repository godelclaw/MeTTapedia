import Mettapedia.OSLF.Syntax.RhoScopedParallelSourceAdequacy
import Mettapedia.OSLF.Syntax.RhoScopedEquationBindingControls

/-!
# Controls for actual scoped rho least-context transitions

COMM, an open continuation and the separately admitted Drop rule use the
original source schemas. Origins remain distinct at equal endpoints. A
padding control rejects a nonleast bound. A separate original process-class
bound is least before variable identification and nonleast afterwards;
recomputing labels is therefore necessary under general substitution.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.OSLF.Binding.RhoScopedParallelReactiveControls

open _root_.CategoryTheory RhoSchema RhoQuotationClassFibres RhoEquationConstructorControls
open RhoIntrinsicCanonicalBag RhoScopedParallelInventory RhoScopedParallelContexts
open RhoScopedParallelEvents RhoScopedParallelReactiveSystem RhoScopedEquationEventControls
open Mettapedia.GSLT.RelativePushout Mettapedia.GSLT.RedexRelativeCongruence
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.Canonical

local instance (context : Ctx sig) : DecidableEq (Prime context) := Classical.decEq _

def commRoot : Root sourceRules core [] :=
  ⟨⟨.communication, trivial⟩, discardRoot⟩

def suppliedComm : Firing (rules := sourceRules) (admitted := core)
    (project waitingInput) (project RhoSourceOutputPredicate.output) (zero []) where
  root := commRoot
  surrounding := zero []
  square := (join_commutes _ _).trans (join_zero_right commRoot.source).symm
  least := by rw [read_zero, Multiset.inter_zero]
  target := (join_zero_right commRoot.target).symm

theorem actual_comm_label :
    leastLabel (project waitingInput) commRoot = project RhoSourceOutputPredicate.output :=
  (firing_normal_form suppliedComm).1.symm

theorem actual_comm_transition :
    ActIPO (reactionRules sourceRules core) (arrow (project RhoSourceOutputPredicate.output))
      (arrow (project waitingInput)) (arrow (zero [])) :=
  (firing_iff_actIPO _ _ _).mp ⟨suppliedComm⟩

def dropRoot : Root sourceRules withReflection [] :=
  ⟨⟨.reflection, trivial⟩,
    ⟨ContextualAssignment.ofClosed contDiscard [], closeDrop nilP⟩⟩

theorem actual_drop_step :
    RhoScopedParallelEvents.Step (rules := sourceRules) (admitted := withReflection)
      (project dropChan) (zero []) := by
  apply (step_iff_root_surrounding _ _).mpr
  exact ⟨dropRoot, zero [], (join_zero_right dropRoot.source).symm,
    (join_zero_right dropRoot.target).symm⟩

theorem core_excludes_drop_origin {context : Ctx sig} :
    ¬ ∃ root : Root sourceRules core context, root.1.val = .reflection := by
  rintro ⟨root, same⟩
  have allowed := root.1.property
  rw [same] at allowed
  exact allowed

def openRoot : Root sourceRules core [Srt.pr] :=
  ⟨⟨.communication, trivial⟩, ContextualRootEvents.RhoExample.openCommunication⟩

theorem open_comm_retains_caller : openRoot.target = project (.var .zero) :=
  congrArg (fun term : Term sig [Srt.pr] Srt.pr => (project term : Process [Srt.pr]))
    ContextualRootEvents.RhoExample.open_target

theorem open_comm_identity_transition :
    ActIPO (reactionRules sourceRules core) (𝟙 (interface [Srt.pr]))
      (arrow openRoot.source) (arrow (project (.var .zero))) := by
  apply (step_iff_actIPO_identity _ _).mp
  apply (step_iff_root_surrounding _ _).mpr
  exact ⟨openRoot, zero [Srt.pr], (join_zero_right _).symm,
    open_comm_retains_caller.symm.trans (join_zero_right _).symm⟩

theorem substituted_open_comm_target (process : Term sig [] Srt.pr) :
    (openRoot.map (extend process)).target = project process :=
  congrArg (fun term : Term sig [] Srt.pr => (project term : Process []))
    (ContextualRootEvents.RhoExample.supplied_process_survives process)

def duplicateRules : Fin 2 → ProcessRule := fun _ => communication

def duplicateRoot (index : Fin 2) : Root duplicateRules (fun _ => True) [] :=
  ⟨⟨index, trivial⟩, discardRoot⟩

def duplicateFiring (index : Fin 2) :
    Firing (rules := duplicateRules) (admitted := fun _ => True)
      (duplicateRoot 0).source (zero []) (zero []) where
  root := duplicateRoot index
  surrounding := zero []
  square := rfl
  least := by rw [read_zero, Multiset.zero_inter]
  target := (join_zero_right _).symm

theorem duplicate_receipts_distinct : duplicateFiring 0 ≠ duplicateFiring 1 := by
  intro same
  have origins := congrArg (fun receipt => receipt.root.1.val) same
  exact (by decide : (0 : Fin 2) ≠ 1) origins

def idle : Process [] := drop (quote (zero []))

theorem idle_nonzero : idle ≠ zero [] := drop_not_zero (quote (zero []))

theorem padded_same_root_rejected (target : Process []) :
    ¬ ∃ receipt : Firing (rules := sourceRules) (admitted := core)
        (project waitingInput) (join (project RhoSourceOutputPredicate.output) idle) target,
      receipt.root = commRoot := by
  rintro ⟨receipt, sameRoot⟩
  have labelRead := (firing_normal_form receipt).1
  rw [sameRoot, actual_comm_label] at labelRead
  have inventories := congrArg read labelRead
  rw [read_join] at inventories
  have zeroRead : read idle = 0 := add_left_cancel (inventories.trans (add_zero _).symm)
  exact idle_nonzero (read_injective [] (zeroRead.trans (read_zero []).symm))

theorem read_inter_zero_of_components_disjoint {context : Ctx sig}
    (first second : Process context) (separated : Disjoint (components first) (components second)) :
    read first ∩ read second = 0 := by
  apply Multiset.inter_eq_zero_iff_disjoint.mpr
  apply Multiset.disjoint_left.mpr
  intro prime firstMember secondMember
  have firstRead : prime.val ∈ components first := by
    rw [← values_read]
    exact Multiset.mem_map.mpr ⟨prime, firstMember, rfl⟩
  have secondRead : prime.val ∈ components second := by
    rw [← values_read]
    exact Multiset.mem_map.mpr ⟨prime, secondMember, rfl⟩
  exact (Multiset.disjoint_left.mp separated) firstRead secondRead

def firstVariable : Process [Srt.pr, Srt.pr] := project (.var .zero)

def secondVariable : Process [Srt.pr, Srt.pr] := project (.var (.succ .zero))

theorem variable_inventories_separate : read firstVariable ∩ read secondVariable = 0 := by
  apply read_inter_zero_of_components_disjoint
  rw [components_bagContents, components_bagContents]
  change Disjoint ((bagContents [canonicalize (.bvar 0)] : List Pattern) : Multiset Pattern)
    ((bagContents [canonicalize (.bvar 1)] : List Pattern) : Multiset Pattern)
  simp [canonicalize, bagContents, bagSplice]

theorem original_variable_bound_minimal
    (square : arrow secondVariable ≫ arrow firstVariable = arrow firstVariable ≫ arrow secondVariable) :
    IsIdemPushout (arrow secondVariable) (arrow firstVariable)
      (arrow firstVariable) (arrow secondVariable) square :=
  (idemPushout_iff _ _ _ _ square).mpr variable_inventories_separate

def collapseVariables : Sub sig [Srt.pr, Srt.pr] []
  | _, .zero => RhoSourceOutputPredicate.output
  | _, .succ .zero => RhoSourceOutputPredicate.output

theorem both_variables_collapse :
    bindQ collapseVariables firstVariable = project RhoSourceOutputPredicate.output ∧
      bindQ collapseVariables secondVariable = project RhoSourceOutputPredicate.output := ⟨rfl, rfl⟩

theorem output_nonzero : (project RhoSourceOutputPredicate.output : Process []) ≠ zero [] := by
  intro same
  have counts := congrArg RhoSourceOutputPredicate.count same
  change (1 : Nat) = 0 at counts
  omega

/-- This is an original class-bound counterexample, not a claim about an authored COMM firing. -/
theorem substituted_variable_bound_not_minimal
    (square : arrow (project RhoSourceOutputPredicate.output) ≫
        arrow (project RhoSourceOutputPredicate.output) =
      arrow (project RhoSourceOutputPredicate.output) ≫ arrow (project RhoSourceOutputPredicate.output)) :
    ¬ IsIdemPushout (arrow (project RhoSourceOutputPredicate.output))
      (arrow (project RhoSourceOutputPredicate.output))
      (arrow (project RhoSourceOutputPredicate.output))
      (arrow (project RhoSourceOutputPredicate.output)) square := by
  intro minimal
  have emptyRead := (idemPushout_iff _ _ _ _ square).mp minimal
  change read (project RhoSourceOutputPredicate.output) ∩
    read (project RhoSourceOutputPredicate.output) = 0 at emptyRead
  rw [← Multiset.inf_eq_inter, inf_idem] at emptyRead
  exact output_nonzero (read_injective [] (emptyRead.trans (read_zero []).symm))

theorem identification_changes_minimality :
    (∃ square : arrow secondVariable ≫ arrow firstVariable =
        arrow firstVariable ≫ arrow secondVariable,
      IsIdemPushout (arrow secondVariable) (arrow firstVariable)
        (arrow firstVariable) (arrow secondVariable) square) ∧
    ¬ IsIdemPushout (arrow (project RhoSourceOutputPredicate.output))
      (arrow (project RhoSourceOutputPredicate.output))
      (arrow (project RhoSourceOutputPredicate.output))
      (arrow (project RhoSourceOutputPredicate.output)) rfl := by
  constructor
  · have square : arrow secondVariable ≫ arrow firstVariable =
        arrow firstVariable ≫ arrow secondVariable := by
      rw [arrow_comp, arrow_comp]
      exact congrArg arrow (join_commutes secondVariable firstVariable)
    exact ⟨square, original_variable_bound_minimal square⟩
  · exact substituted_variable_bound_not_minimal rfl

end Mettapedia.OSLF.Binding.RhoScopedParallelReactiveControls
