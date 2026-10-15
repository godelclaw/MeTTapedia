import Mettapedia.OSLF.Syntax.SortedCommutativeGroundFactorAllSorts
import Mettapedia.OSLF.Framework.SortedCommutativeInstrumentControls
import Mettapedia.OSLF.Framework.SortedTypedInstrumentControls

/-!
# Complete finite factors retain ground collisions and actual units

Two genuine selected free-constructor positions read the same whole ground
value but remain different complete factors. Both are retained in the finite
fibre. Unit-valued factors instead have an earned identity context; no frame
can disappear through AC1. The heterogeneous example retains the unbounded
authored Nat channel family, while its fixed-value all-sort fibre is finite.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.OSLF.Framework.SortedCommutativeGroundFactorControls

open Mettapedia.OSLF.SortedCommutative
open SortedCommutativeInstruments SortedCommutativeInstrumentControls
open GroundFactors

def whole := classOf (firstHole.fill low)

def firstFactor : Factor (.base : Srt arity) whole :=
  ⟨(firstHole.normalize, classOf low), RawContext.normalize_filling firstHole low⟩

def secondFactor : Factor (.base : Srt arity) whole :=
  ⟨(secondHole.normalize, classOf low),
    (RawContext.normalize_filling secondHole low).trans (congrArg classOf position_collision.symm)⟩

theorem both_complete_selected_positions_are_retained : firstFactor ≠ secondFactor := by
  intro same
  have contexts := congrArg (fun supplied : Factor (.base : Srt arity) whole => supplied.val.1) same
  change normalizeContext (contextClassOf firstHole) = normalizeContext (contextClassOf secondHole) at contexts
  exact actual_context_classes_differ ((contextEquiv _ _).injective contexts)

theorem the_actual_ground_action_collision_is_retained :
    evaluate firstFactor.val = evaluate secondFactor.val := firstFactor.property.trans secondFactor.property.symm

theorem the_whole_ground_fibre_is_genuinely_finite : Finite (TotalFactor whole) := totalFactor_finite whole

theorem ground_readout_does_not_determine_the_complete_factor :
    ¬Function.Injective (evaluate (signature := signature arity) (Parallel := Parallel arity)
      (source := .base) (target := .base)) := by
  intro injective
  exact both_complete_selected_positions_are_retained
    (Subtype.ext (injective the_actual_ground_action_collision_is_retained))

def unitValue : ValueClass arity .base := classOf (.zero rfl)

theorem every_actual_unit_factor_has_the_full_identity_reading (supplied : Factor (.base : Srt arity) unitValue) :
    supplied.val = (.parallel 0, unitValue) := by
  obtain ⟨⟨context, input⟩, read⟩ := supplied
  have inventoryRead := congrArg inventoryQ read
  cases context with
  | parallel bag =>
    change inventoryQ (residue bag input) = 0 at inventoryRead
    rw [residue_inventory] at inventoryRead
    obtain ⟨bagRead, inputRead⟩ := add_eq_zero.mp inventoryRead
    have empty : bag = 0 := Multiset.map_injective Subtype.val_injective
      (bagRead.trans (Multiset.map_zero _).symm)
    have value : input = unitValue := inventoryQ_injective inputRead
    subst bag
    subst input
    rfl
  | frame bag edge inner =>
    let actualContext : MixedContext (signature arity) (Parallel arity) .base .base := .frame bag edge inner
    have framed : 0 < actualContext.frameCount := by
      simp only [actualContext, Mettapedia.CategoryTheory.MixedResidue.Context.frameCount]
      omega
    let code := framedCode (⟨⟨(actualContext, input), read⟩, framed⟩ :
      FramedFactor (.base : Srt arity) unitValue)
    have member := code.2.1.property
    change code.2.1.val ∈ (0 : Multiset (Head (signature := signature arity)
      (Parallel := Parallel arity) .base)) at member
    exact (Multiset.notMem_zero _ member).elim

theorem unit_factors_have_no_hidden_frame_or_input : Subsingleton (Factor (.base : Srt arity) unitValue) := by
  refine ⟨fun first second => Subtype.ext ?_⟩
  exact (every_actual_unit_factor_has_the_full_identity_reading first).trans
    (every_actual_unit_factor_has_the_full_identity_reading second).symm

theorem a_fixed_typed_value_has_finitely_many_complete_factors_across_every_hole_sort (channel : Nat) :
    Finite (TotalFactor (classOf (SortedTypedInstruments.embed
      (SortedTypedInstrumentControls.sourcePayload channel)))) :=
  totalFactor_finite _

theorem unbounded_authored_channels_are_not_identified (first second : Nat)
    (same : classOf (SortedTypedInstrumentControls.sourceName first) =
      classOf (SortedTypedInstrumentControls.sourceName second)) : first = second := by
  have inventories := congrArg inventoryQ same
  change inventory (SortedTypedInstrumentControls.sourceName first) =
    inventory (SortedTypedInstrumentControls.sourceName second) at inventories
  have heads := Multiset.singleton_inj.mp inventories
  cases heads
  rfl

end Mettapedia.OSLF.Framework.SortedCommutativeGroundFactorControls
