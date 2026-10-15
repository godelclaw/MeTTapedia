import Mettapedia.OSLF.Framework.RhoGeneratedScopeSubstitution

/-!
# A nonconstant inventory invariant for generated rho scopes

The equation-compatible output-occurrence inventory commutes with quotation,
drop and parallel sum. When the left atomic predicate requires an output,
every finitely generated name retains one. This gives an actual exclusion
control for the generated native family at every open context.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.OSLF.Framework.RhoGeneratedScopeInventory

open Mettapedia.OSLF.Binding
open RhoSchema RhoQuotationClassFibres RhoEquationConstructorControls
open RhoEquationGeneratedScope RhoGeneratedScopeSubstitution BindingConstructorPredicates

theorem count_quote {context : Ctx sig} (process : Process context) :
    RhoSourceOutputPredicate.count (quote process) = RhoSourceOutputPredicate.count process := by
  rw [quote_operation, RhoSourceOutputPredicate.count_operation]
  simp only [outputHeadCount, RhoSourceOutputPredicate.countArguments, Nat.zero_add, Nat.add_zero]

theorem count_drop {context : Ctx sig} (name : Name context) :
    RhoSourceOutputPredicate.count (drop name) = RhoSourceOutputPredicate.count name := by
  rw [drop_operation, RhoSourceOutputPredicate.count_operation]
  simp only [outputHeadCount, RhoSourceOutputPredicate.countArguments, Nat.zero_add, Nat.add_zero]

theorem count_join {context : Ctx sig} (first second : Process context) :
    RhoSourceOutputPredicate.count (join first second) =
      RhoSourceOutputPredicate.count first + RhoSourceOutputPredicate.count second := by
  rw [join_operation, RhoSourceOutputPredicate.count_operation]
  simp only [outputHeadCount, RhoSourceOutputPredicate.countArguments, Nat.zero_add, Nat.add_zero]

theorem generated_retains_output {context : Ctx sig} (right : Process context → Prop) :
    generated (RhoSourceOutputPredicate.positive Srt.pr).holds right ≤
      fun name => 0 < RhoSourceOutputPredicate.count name := by
  apply generated_induction
  intro name
  rintro ⟨first, second, rfl, admitted, _⟩
  rw [count_quote, count_join]
  have positive : 0 < RhoSourceOutputPredicate.count first := by
    rcases admitted with atomic | ⟨inner, member, rfl⟩
    · exact atomic
    · simpa only [count_drop] using member
  exact positive.trans_le (Nat.le_add_right _ _)

def outputScope : Predicate model Srt.nm :=
  native (RhoSourceOutputPredicate.positive Srt.pr) (RhoSourceOutputPredicate.positive Srt.pr)

theorem output_scope_excludes_null {context : Ctx sig} :
    ¬ outputScope.holds (quote (zero context)) := by
  intro member
  have positive := generated_retains_output _ _ member
  change 0 < RhoSourceOutputPredicate.count (quote (zero context)) at positive
  rw [count_quote] at positive
  change (0 : Nat) < 0 at positive
  exact Nat.lt_irrefl 0 positive

end Mettapedia.OSLF.Framework.RhoGeneratedScopeInventory
