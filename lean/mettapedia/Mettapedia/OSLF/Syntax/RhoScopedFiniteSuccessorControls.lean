import Mettapedia.OSLF.Syntax.RhoScopedDropSuccessors
import Mettapedia.OSLF.Syntax.RhoScopedReactionReceiptControls

/-!
# Original scoped finite-outcome and future-context controls

Reflection has two distinct outcomes at an exposed closed quotation and one
at a bound open name. Null has no identity-labelled outcome in either rule
profile, although a permitted parallel context can enable an actual firing.
Current absence consequently does not imply absence in every future context.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.OSLF.Binding.RhoScopedFiniteSuccessorControls

open RhoSchema RhoQuotationClassFibres RhoEquationConstructorControls RhoIntrinsicReadback
open RhoIntrinsicCanonicalBag RhoScopedParallelInventory RhoScopedConstructorInventory
open RhoScopedReactionReadout RhoScopedFiniteReactions RhoScopedFiniteSuccessors
open RhoScopedDropSuccessors RhoScopedParallelEvents RhoScopedParallelReactiveSystem

theorem no_reading_fits_zero {context : Ctx sig} (reading : Reading context) :
    ¬ fits (zero context) reading := by
  intro included
  have patterns := components_le included
  rw [zero_components] at patterns
  cases reading with
  | communication channel payload continuation =>
      change components (join (outputClass channel payload) (inputClass channel continuation)) ≤ _
        at patterns
      rw [join_components, output_components, input_components] at patterns
      have count := Multiset.card_le_card patterns
      simp only [Multiset.card_add, Multiset.card_singleton, Multiset.card_zero] at count
      omega
  | reflection payload =>
      change components (drop (quote payload)) ≤ _ at patterns
      rw [drop_components] at patterns
      have count := Multiset.card_le_card patterns
      simp only [Multiset.card_singleton, Multiset.card_zero] at count
      omega

theorem zero_identity_successors_empty (admitted : SourceRule → Prop) (context : Ctx sig) :
    successors admitted (zero context) (zero context) = ∅ := by
  classical
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro second member
  obtain ⟨root, least, _target⟩ := (actIPO_iff_computed _ _ _).mp
    ((mem_successors_iff admitted _ _ _).mp member)
  have included := root_included (zero context) (zero context) root least
  rw [join_zero_right] at included
  exact no_reading_fits_zero (rootReading root) (by simpa only [fits, rootReading_source] using included)

theorem every_authored_root_has_identity_outcome {context : Ctx sig} {admitted : SourceRule → Prop}
    (root : Root sourceRules admitted context) :
    root.target ∈ successors admitted root.source (zero context) := by
  have target := supplied_root_target_listed root.source (zero context) root
    (by simp only [leastLabel, tsub_self, write_zero])
  simpa only [reactionRemainder, tsub_self, write_zero, join_zero_right] using target

/-- The permitted parallel context is an actual process class. -/
theorem quiet_now_can_fire_after_parallel_context :
    successors core (zero []) (zero []) = ∅ ∧
      RhoScopedReactionReceiptControls.quotedBoundRoot.target ∈
        successors core (join (zero []) RhoScopedReactionReceiptControls.quotedBoundRoot.source) (zero []) := by
  refine ⟨zero_identity_successors_empty core [], ?_⟩
  rw [join_zero_left]
  exact every_authored_root_has_identity_outcome _

theorem visible_two_reflection_outcomes :
    (successors withReflection suspended (zero [])).card = 2 := by
  change (successors withReflection (drop (quote visible)) (zero [])).card = 2
  rw [reflection_successors]
  exact RhoFiniteQuotationOrigins.visible_two_origins

theorem visible_and_suspended_both_listed :
    visible ∈ successors withReflection suspended (zero []) ∧
      suspended ∈ successors withReflection suspended (zero []) ∧ suspended ≠ visible := by
  unfold suspended
  rw [reflection_successors]
  exact ⟨(RhoFiniteQuotationOrigins.quotation_fibre_iff _ _).mp rfl,
    (RhoFiniteQuotationOrigins.quotation_fibre_iff _ _).mp same_actual_name, suspended_not_visible⟩

theorem open_bound_name_one_outcome :
    (successors withReflection (drop RhoFiniteQuotationOrigins.openName) (zero [Srt.nm])).card = 1 := by
  rw [reflection_successors]
  exact RhoFiniteQuotationOrigins.bound_name_one_origin

theorem open_bound_name_has_self_outcome :
    drop RhoFiniteQuotationOrigins.openName ∈
      successors withReflection (drop RhoFiniteQuotationOrigins.openName) (zero [Srt.nm]) :=
  original_eta_self_outcome _

end Mettapedia.OSLF.Binding.RhoScopedFiniteSuccessorControls
