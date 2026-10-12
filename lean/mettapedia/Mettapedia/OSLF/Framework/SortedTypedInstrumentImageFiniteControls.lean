import Mettapedia.OSLF.Framework.SortedTypedInstrumentKitImageFinite
import Mettapedia.OSLF.Framework.SortedTypedInstrumentProbeControls

/-!
# Complete finite branching, ordered Cut alternatives and infinite originals

A nontrivial original unit reaction and the complete administrative family
earn all-interface modal completeness at arbitrary supported native states.
Proper-Cut ask retains two different ordered outputs, and infinitely many
supplied origins retain distinct receipts despite finite extensional fibres.
The independently authored infinite unit-reaction family has infinitely
many actual IPO successors even when no administrative head is opened.
Finite instrument permissions therefore do not supply primitive branching.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.OSLF.Framework.SortedTypedInstrumentImageFiniteControls

open _root_.CategoryTheory
open Mettapedia.OSLF.SortedCommutative
open Mettapedia.OSLF.SortedCommutative.ReactiveFiniteness
open Mettapedia.GSLT.RedexRelativeCongruence
open Mettapedia.GSLT.InterfaceModalLogic
open SortedTypedInstruments SortedTypedInstrumentControls SortedTypedInstrumentProbeControls

def singleRule (_origin : Unit) : ReactionRule (.origin : SourceCategory sourceSignature sourceParallel) where
  codomain := .interface .process
  redex := .value (classOf (.zero rfl : SourceValue .process))
  reactum := .value (classOf (sourcePayload 17))

theorem singleRule_fibres : FiniteReactumFibres (Kit.originalRulePredicate singleRule) :=
  Kit.original_fibres_of_finite_rule_image singleRule (Set.finite_range singleRule)

def sendOnly : Kit.Policy sourceSignature sourceParallel := fun head => head = sendHead

theorem sendOnly_finite : Set.Finite {head | sendOnly head} := Set.finite_singleton sendHead

theorem actual_auxiliary_bundle_modal_iff (firstIndex secondIndex : Nat)
    (firstPayload secondPayload : SourceValue .process) :
    IPOBisimilar (Kit.ambientRules (NativeOrigins := Nat) singleRule sendOnly)
        (RawArrow.value (classOf (bundle sendHead (sendArguments firstIndex firstPayload))))
        (RawArrow.value (classOf (bundle sendHead (sendArguments secondIndex secondPayload)))) ↔
      LogicallyEquivalent (Kit.ambientRules (NativeOrigins := Nat) singleRule sendOnly)
        (RawArrow.value (classOf (bundle sendHead (sendArguments firstIndex firstPayload))))
        (RawArrow.value (classOf (bundle sendHead (sendArguments secondIndex secondPayload)))) :=
  Kit.arbitrary_native_ipo_iff_all_interface_modal sendOnly singleRule singleRule_fibres _ _

theorem complete_supported_native_modal_iff {interface : Kit.Object sendOnly}
    (first second : Kit.origin sendOnly ⟶ interface) :
    IPOBisimilar (Kit.categoryRules (NativeOrigins := Nat) singleRule sendOnly) first second ↔
      LogicallyEquivalent (Kit.categoryRules (NativeOrigins := Nat) singleRule sendOnly) first second :=
  Kit.arbitrary_supported_ipo_iff_all_interface_modal sendOnly singleRule singleRule_fibres first second

theorem finite_cut_ask_has_distinct_complete_outputs :
    Set.Finite {target | ActIPO (rules sourceSignature sourceParallel Nat) (probeLabel (.ask cutHead))
      (RawArrow.value (classOf (sourceNode cutHead orderedCutArguments))) target} ∧
      ActIPO (rules sourceSignature sourceParallel Nat) (probeLabel (.ask cutHead))
        (RawArrow.value (classOf (sourceNode cutHead orderedCutArguments)))
        (RawArrow.value (classOf (bundle cutHead orderedCutArguments))) ∧
      ActIPO (rules sourceSignature sourceParallel Nat) (probeLabel (.ask cutHead))
        (RawArrow.value (classOf (sourceNode cutHead orderedCutArguments)))
        (RawArrow.value (classOf (bundle cutHead exchangedCutArguments))) ∧
      classOf (bundle cutHead orderedCutArguments) ≠ classOf (bundle cutHead exchangedCutArguments) := by
  exact ⟨ReactiveFibres.administrative_imageFinite _ _, actual_cut_ask_keeps_both_ordered_alternatives⟩

theorem finite_extensional_fibre_preserves_duplicate_origin_receipts :
    Set.Finite {target | ActIPO (rules sourceSignature sourceParallel Nat)
      (processGet 24 7 (sourcePayload 9)).label (processGet 24 7 (sourcePayload 9)).agent target} ∧
      directReceipt (processGet 24 7 (sourcePayload 9)) ≠
        directReceipt (processGet 25 7 (sourcePayload 9)) :=
  ⟨ReactiveFibres.administrative_imageFinite _ _, complete_receipts_do_not_merge_duplicate_origins.2⟩

def infiniteRules (origin : Nat) : ReactionRule (.origin : SourceCategory sourceSignature sourceParallel) where
  codomain := .interface .process
  redex := .value (classOf (.zero rfl : SourceValue .process))
  reactum := .value (classOf (sourcePayload origin))

def noHeads : Kit.Policy sourceSignature sourceParallel := fun _ => False

theorem noHeads_finite : Set.Finite {head | noHeads head} := Set.finite_empty

def nativeUnit : (.origin : ContextCategory sourceSignature sourceParallel) ⟶ .interface (.original .process) :=
  .value (classEmbedding (classOf (.zero rfl : SourceValue .process)))

def nativePayload (index : Nat) :
    (.origin : ContextCategory sourceSignature sourceParallel) ⟶ .interface (.original .process) :=
  .value (classEmbedding (classOf (sourcePayload index)))

theorem the_finite_original_reaction_is_a_real_step :
    ActIPO (Kit.ambientRules (NativeOrigins := Nat) singleRule sendOnly)
      (𝟙 (.interface (.original .process) : ContextCategory sourceSignature sourceParallel))
      nativeUnit (nativePayload 17) := by
  let supplied := Source.mapReactionRule (singleRule ())
  have square : nativeUnit ≫ (𝟙 (.interface (.original .process) :
      ContextCategory sourceSignature sourceParallel)) = supplied.redex := Category.comp_id nativeUnit
  exact ⟨supplied, ⟨Kit.Declaration.original (), rfl⟩, 𝟙 _,
    square.trans (Category.comp_id supplied.redex).symm,
    raw_right_identity_isIPO _ square, (Category.comp_id supplied.reactum).symm⟩

theorem nativePayload_injective : Function.Injective nativePayload := by
  intro first second same
  have values := RawArrow.value.inj same
  change classOf (embed (sourcePayload first)) = classOf (embed (sourcePayload second)) at values
  have coordinates := (node_class_eq_iff (signature := signature sourceSignature sourceParallel)
    (Parallel := NativeParallel) (Constructor.original Symbol.send) _ _).mp values
  by_contra different
  exact different_channel_indices_remain_distinct first second different (coordinates 0)

theorem every_original_unit_target_fires (index : Nat) :
    ActIPO (Kit.ambientRules (NativeOrigins := Nat) infiniteRules noHeads)
      (𝟙 (.interface (.original .process) : ContextCategory sourceSignature sourceParallel))
      nativeUnit (nativePayload index) := by
  let supplied := Source.mapReactionRule (infiniteRules index)
  have square : nativeUnit ≫ (𝟙 (.interface (.original .process) :
      ContextCategory sourceSignature sourceParallel)) = supplied.redex := Category.comp_id nativeUnit
  refine ⟨supplied, ⟨Kit.Declaration.original index, rfl⟩, 𝟙 _,
    square.trans (Category.comp_id supplied.redex).symm,
    raw_right_identity_isIPO _ square, (Category.comp_id supplied.reactum).symm⟩

theorem a_finite_instrument_kit_can_have_infinite_actual_branching :
    Set.Finite {head | noHeads head} ∧
      ¬ImageFinite (Kit.ambientRules (NativeOrigins := Nat) infiniteRules noHeads) := by
  refine ⟨noHeads_finite, ?_⟩
  intro finite
  have infinite : Set.Infinite (Set.range nativePayload) := Set.infinite_range_of_injective nativePayload_injective
  apply infinite
  apply (finite (𝟙 (.interface (.original .process) : ContextCategory sourceSignature sourceParallel)) nativeUnit).subset
  rintro target ⟨index, rfl⟩
  exact every_original_unit_target_fires index

theorem original_reactum_finiteness_is_not_automatic :
    ¬FiniteReactumFibres (Kit.originalRulePredicate infiniteRules) := by
  intro finite
  exact a_finite_instrument_kit_can_have_infinite_actual_branching.2
    (Kit.ambient_imageFinite noHeads infiniteRules finite)

theorem the_actual_supported_category_has_the_same_infinite_branching :
    ¬ImageFinite (Kit.categoryRules (NativeOrigins := Nat) infiniteRules noHeads) := by
  intro finite
  exact original_reactum_finiteness_is_not_automatic
    ((Kit.category_imageFinite_iff_original_fibres noHeads infiniteRules).mp finite)

end Mettapedia.OSLF.Framework.SortedTypedInstrumentImageFiniteControls
