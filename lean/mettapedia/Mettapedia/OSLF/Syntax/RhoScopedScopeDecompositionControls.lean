import Mettapedia.OSLF.Syntax.RhoScopedScopeDecision
import Mettapedia.OSLF.Syntax.RhoScopeQuotientControls

/-!
# Concrete scoped decomposition controls at the original rho quotient

Two outputs use different actual quoted channels. The left scope retains
two equal output occurrences and the right scope retains a third output.
The checked colour admission earns the exact readback and unique receipt.

The suspended-output control has a complete admitted interpretation but
fails the fast procedure's exposure condition. The unrestricted finite
search retains both process origins when both are admitted.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.RhoScopedScopeDecompositionControls

open RhoSchema RhoQuotationClassFibres RhoEquationConstructorControls
open RhoScopedParallelInventory RhoScopedScopeDecomposition RhoScopedScopeDecision
open RhoSchema.IntrinsicEncoding RhoIntrinsicCanonicalBag RhoIntrinsicReadback
open Mettapedia.OSLF.MeTTaIL.Syntax

local instance (context : Ctx sig) : DecidableEq (Process context) :=
  equationClassDecision context Srt.pr

def firstOutput : Process [] := visible

def secondOutput : Process [] :=
  project (outputRaw (quoteRaw RhoSourceOutputPredicate.output) null)

def firstPrime : Prime [] :=
  ⟨encodeEquationClass firstOutput, contents_prime firstOutput (by decide +kernel)⟩

def secondPrime : Prime [] :=
  ⟨encodeEquationClass secondOutput, contents_prime secondOutput (by decide +kernel)⟩

theorem read_first : read firstOutput = {firstPrime} := by
  apply values_injective []
  rw [values_read, components_bagContents]
  decide +kernel

theorem read_second : read secondOutput = {secondPrime} := by
  apply values_injective []
  rw [values_read, components_bagContents]
  decide +kernel

def classify (prime : Prime []) : Bool := decide (prime.val = firstPrime.val)

theorem first_colour : classify firstPrime = true := by simp [classify]

theorem second_colour : classify secondPrime = false := by decide +kernel

def repeatedLeft : Process [] := join firstOutput firstOutput

def leftScope (process : Process []) : Prop := process = repeatedLeft

def rightScope (process : Process []) : Prop := process = secondOutput

instance : DecidablePred leftScope := fun _ => inferInstanceAs (Decidable (_ = _))
instance : DecidablePred rightScope := fun _ => inferInstanceAs (Decidable (_ = _))

theorem left_support : LeftSupported classify leftScope := by
  intro inventory admitted prime member
  have same : inventory = read repeatedLeft := by
    simpa only [read_write] using congrArg read admitted
  rw [same, repeatedLeft, read_join, read_first] at member
  simp only [Multiset.mem_add, Multiset.mem_singleton, or_self] at member
  subst prime
  exact first_colour

theorem right_support : RightSupported classify rightScope := by
  intro inventory admitted prime member
  have same : inventory = read secondOutput := by
    simpa only [read_write] using congrArg read admitted
  rw [same, read_second, Multiset.mem_singleton] at member
  subst prime
  rw [second_colour]
  decide

theorem left_occurrences : (read repeatedLeft).card = 2 := by
  rw [repeatedLeft, read_join, read_first, Multiset.card_add, Multiset.card_singleton]

theorem right_occurrences : (read secondOutput).card = 1 := by
  rw [read_second, Multiset.card_singleton]

theorem composite_exposed : ExposedComposites leftScope rightScope := by
  apply exposedComposites_of_nonempty
  · intro process admitted
    change process = repeatedLeft at admitted
    rw [admitted, left_occurrences]
    decide
  · intro process admitted
    change process = secondOutput at admitted
    rw [admitted, right_occurrences]
    decide

def compositeName : Name [] := quote (join repeatedLeft secondOutput)

theorem fast_readback_preserves_duplicate_occurrences :
    validated classify leftScope rightScope compositeName = some (repeatedLeft, secondOutput) :=
  validated_recovers left_support right_support composite_exposed rfl rfl rfl

theorem independent_search_is_exactly_the_recovered_pair :
    admittedCatalogue leftScope rightScope compositeName = {(repeatedLeft, secondOutput)} :=
  admittedCatalogue_singleton left_support right_support composite_exposed
    fast_readback_preserves_duplicate_occurrences

theorem composite_has_three_actual_occurrences :
    (read (join repeatedLeft secondOutput)).card = 3 := by
  rw [read_join, Multiset.card_add, left_occurrences, right_occurrences]

theorem actual_quoted_scope_has_unique_components :
    ∃! pair : Process [] × Process [], leftScope pair.1 ∧ rightScope pair.2 ∧
      quote (join pair.1 pair.2) = compositeName :=
  composite_unique (classified_component_separation left_support right_support)
    composite_exposed ⟨repeatedLeft, secondOutput, rfl, rfl, rfl⟩

theorem different_channel_rejected :
    verdict classify leftScope rightScope (quote repeatedLeft) = false := by
  apply Bool.eq_false_iff.mpr
  intro accepted
  obtain ⟨first, second, firstAdmitted, secondAdmitted, readout⟩ := verdict_sound accepted
  change first = repeatedLeft at firstAdmitted
  change second = secondOutput at secondAdmitted
  subst first
  subst second
  have sameBodies := quote_injective_on_exposed
    (composite_exposed _ _ rfl rfl)
    (exposed_join_of_nonempty (by rw [read_first, Multiset.card_singleton]; decide)
      (by rw [read_first, Multiset.card_singleton]; decide)) readout
  have sameCounts := congrArg (fun process => (read process).card) sameBodies
  rw [composite_has_three_actual_occurrences] at sameCounts
  change 3 = (read repeatedLeft).card at sameCounts
  rw [left_occurrences] at sameCounts
  cases sameCounts

def suspendedOnly (process : Process []) : Prop := process = suspended

instance : DecidablePred suspendedOnly := fun _ => inferInstanceAs (Decidable (_ = _))

instance : DecidablePred RhoScopeQuotientControls.leftScope := fun _ =>
  inferInstanceAs (Decidable (_ = _))

instance : DecidablePred RhoScopeQuotientControls.rightScope := fun _ =>
  inferInstanceAs (Decidable (_ = _ ∨ _ = _))

theorem suspended_is_not_exposed : ¬ Exposed suspended := by
  intro exposed
  exact (exposed_iff_not_drop suspended).mp exposed ⟨quote visible, rfl⟩

theorem fast_search_can_miss_an_admitted_origin :
    Composite RhoScopeQuotientControls.leftScope suspendedOnly (quote visible) ∧
      validated (fun _ => false) RhoScopeQuotientControls.leftScope suspendedOnly
        (quote visible) = none := by
  refine ⟨⟨zero [], suspended, rfl, rfl,
    (congrArg quote (join_zero_left suspended)).trans same_actual_name⟩, ?_⟩
  unfold validated readPair
  rw [RhoFiniteQuotationOrigins.visible_body_origin]
  have leftRead : leftPart (fun _ => false) visible = zero [] := by
    simp only [leftPart, Mettapedia.Algebra.SupportSeparatedDecomposition.leftPart,
      Bool.false_eq_true, Multiset.filter_false, write_zero]
  have rightRead : rightPart (fun _ => false) visible = visible := by
    simp [rightPart, Mettapedia.Algebra.SupportSeparatedDecomposition.rightPart, write_read]
  simp only [Option.map_some, leftRead, rightRead, Option.filter_some,
    RhoScopeQuotientControls.leftScope, suspendedOnly]
  have different : visible ≠ suspended := suspended_not_visible.symm
  simp [different]

theorem complete_search_retains_distinct_origins :
    (zero [], visible) ∈ admittedCatalogue RhoScopeQuotientControls.leftScope
      RhoScopeQuotientControls.rightScope (quote visible) ∧
    (zero [], suspended) ∈ admittedCatalogue RhoScopeQuotientControls.leftScope
      RhoScopeQuotientControls.rightScope (quote visible) ∧
    (zero [], visible) ≠ (zero [], suspended) := by
  refine ⟨(mem_admittedCatalogue _ _).mpr ?_, (mem_admittedCatalogue _ _).mpr ?_, ?_⟩
  · exact ⟨rfl, Or.inl rfl, congrArg quote (join_zero_left visible)⟩
  · exact ⟨rfl, Or.inr rfl,
      (congrArg quote (join_zero_left suspended)).trans same_actual_name⟩
  · intro same
    exact suspended_not_visible (congrArg Prod.snd same).symm

end Mettapedia.OSLF.Binding.RhoScopedScopeDecompositionControls
