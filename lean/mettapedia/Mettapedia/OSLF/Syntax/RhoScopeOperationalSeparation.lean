import Mettapedia.OSLF.Syntax.RhoScopeQuotientControls
import Mettapedia.OSLF.Syntax.RhoSourceInputInventory

/-!
# The scope decomposition separator has no communication occurrences

The disjoint scopes used in the quotient control have no inputs, even beneath
their quoted code. The existing source-equation input inventory excludes
every admitted communication occurrence at their joined equation class.
Thus the two different decompositions are not explained by an interaction
spanning their parts. This statement uses the actual communication-only
profile and its declared position permission; operational Drop is a separate
profile.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.RhoScopeOperationalSeparation

open RhoSchema RhoQuotationClassFibres RhoScopeQuotientControls
open ScopedEquationEvents RhoScopedEquationEventControls

theorem joined_scope_has_no_input (first second : Process [])
    (firstAdmitted : leftScope first) (secondAdmitted : rightScope second) :
    RhoSourceInputInventory.count (join first second) = 0 := by
  cases firstAdmitted
  rw [join_zero_left]
  rcases secondAdmitted with rfl | rfl <;> rfl

theorem joined_scope_has_no_communication (first second : Process [])
    (firstAdmitted : leftScope first) (secondAdmitted : rightScope second) :
    ¬ ∃ occurrence : Event rules parallelPermission ([], Srt.pr),
      occurrence.sourceClass rhoSourceE = join first second := by
  rintro ⟨occurrence, readout⟩
  have positive := RhoSourceInputInventory.event_source_has_input occurrence
  rw [readout, joined_scope_has_no_input first second firstAdmitted secondAdmitted] at positive
  exact Nat.lt_irrefl 0 positive

theorem separated_without_unique_process_origins :
    (∀ name, ¬ (nameImage leftScope name ∧ nameImage rightScope name)) ∧
    (∀ first second, leftScope first → rightScope second →
      ¬ ∃ occurrence : Event rules parallelPermission ([], Srt.pr),
        occurrence.sourceClass rhoSourceE = join first second) ∧
    outputDecomposition ≠ suspendedDecomposition :=
  ⟨disjoint_name_extensions, joined_scope_has_no_communication, same_name_distinct_decompositions⟩

end Mettapedia.OSLF.Binding.RhoScopeOperationalSeparation
