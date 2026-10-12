import Mettapedia.OSLF.MeTTaIL.GeneralScopedMatchMachine

/-!
# Independent matching and traced origin comparison

Every ordinary scoped derivation retains an actual bag-choice trace. Erasing
that trace recovers the existing matching judgment and executable interface.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.GeneralScopedMatchMachine

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.RuleBinding
open Mettapedia.OSLF.MeTTaIL.ScopedRuleMatching

mutual
theorem matches_trace {rule : RewriteRule} {spec : RuleBindingSpec} {ambient : Nat}
    {site : RulePatternSite} {path : List Nat} {depth : Nat} {initial final : Assignment}
    {schema target : Pattern}
    (matched : GeneralScopedMatch.Matches rule spec ambient site path depth initial schema target final) :
    ∃ trace, TracedMatches rule spec ambient site path depth initial schema target trace final := by
  cases matched with
  | capture captured => exact ⟨[], .capture captured⟩
  | bound => exact ⟨[], .bound⟩
  | constructor arguments =>
    obtain ⟨trace, traced⟩ := arguments_trace arguments
    exact ⟨trace, .constructor traced⟩
  | binder body =>
    obtain ⟨trace, traced⟩ := matches_trace body
    exact ⟨trace, .binder traced⟩
  | binders body =>
    obtain ⟨trace, traced⟩ := matches_trace body
    exact ⟨trace, .binders traced⟩
  | substitution body replacement =>
    obtain ⟨first, bodyTraced⟩ := matches_trace body
    obtain ⟨second, replacementTraced⟩ := matches_trace replacement
    exact ⟨first ++ second, .substitution bodyTraced replacementTraced⟩
  | bag notVector bag =>
    obtain ⟨trace, traced⟩ := bag_trace bag
    exact ⟨trace, .bag notVector traced⟩
  | vector arguments =>
    obtain ⟨trace, traced⟩ := arguments_trace arguments
    exact ⟨trace, .vector traced⟩
  | vectorRest arguments captured =>
    obtain ⟨trace, traced⟩ := arguments_trace arguments
    exact ⟨trace, .vectorRest traced captured⟩
termination_by sizeOf schema

theorem arguments_trace {rule : RewriteRule} {spec : RuleBindingSpec} {ambient : Nat}
    {site : RulePatternSite} {path : List Nat} {depth index : Nat} {initial final : Assignment}
    {schemas targets : List Pattern}
    (matched : GeneralScopedMatch.Arguments rule spec ambient site path depth initial index schemas targets final) :
    ∃ trace, TracedArguments rule spec ambient site path depth initial index schemas targets trace final := by
  cases matched with
  | nil => exact ⟨[], .nil⟩
  | cons head tail =>
    obtain ⟨first, headTraced⟩ := matches_trace head
    obtain ⟨second, tailTraced⟩ := arguments_trace tail
    exact ⟨first ++ second, .cons headTraced tailTraced⟩
termination_by sizeOf schemas

theorem bag_trace {rule : RewriteRule} {spec : RuleBindingSpec} {ambient : Nat}
    {site : RulePatternSite} {path : List Nat} {depth index : Nat} {initial final : Assignment}
    {schemas targets : List Pattern} {rest : Option String} {kind : CollType}
    (matched : GeneralScopedMatch.Bag rule spec ambient site path depth initial index schemas rest kind targets final) :
    ∃ trace, TracedBag rule spec ambient site path depth initial index schemas rest kind targets trace final := by
  cases matched with
  | nil => exact ⟨[], .nil⟩
  | rest captured => exact ⟨[], .rest captured⟩
  | cons selected within head tail =>
    obtain ⟨first, headTraced⟩ := matches_trace head
    obtain ⟨second, tailTraced⟩ := bag_trace tail
    exact ⟨_, .cons selected within headTraced tailTraced⟩
termination_by sizeOf schemas
end

theorem traced_iff_matches {rule : RewriteRule} {spec : RuleBindingSpec} {ambient : Nat}
    {site : RulePatternSite} {path : List Nat} {depth : Nat} {initial final : Assignment}
    {schema target : Pattern} :
    (∃ trace, TracedMatches rule spec ambient site path depth initial schema target trace final) ↔
      GeneralScopedMatch.Matches rule spec ambient site path depth initial schema target final :=
  ⟨fun ⟨_, traced⟩ => traced.matching, matches_trace⟩

theorem traced_iff_matchAt {rule : RewriteRule} {spec : RuleBindingSpec} {ambient : Nat}
    {site : RulePatternSite} {path : List Nat} {depth : Nat} {initial final : Assignment}
    {schema target : Pattern} :
    (∃ trace, TracedMatches rule spec ambient site path depth initial schema target trace final) ↔
      final ∈ matchAt rule spec ambient site path depth initial schema target :=
  traced_iff_matches.trans GeneralScopedMatch.matchAt_iff.symm

end Mettapedia.OSLF.MeTTaIL.GeneralScopedMatchMachine
