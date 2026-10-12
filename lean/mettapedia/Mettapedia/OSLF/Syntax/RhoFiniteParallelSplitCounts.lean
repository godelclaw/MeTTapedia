import Mettapedia.OSLF.Syntax.RhoFiniteParallelSplits

/-!
# Sizes of complete parallel-split value catalogues

Reconstruction preserves the selected submultiset, so distinct cuts give
distinct ordered value pairs. There are at most two to the number of prime
component occurrences such pairs. Repeated components are retained in the
inventory, while selecting equal occurrences can give the same value cut.
This counts candidate values rather than runtime firings or parser work.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.RhoFiniteParallelSplitCounts

open RhoSchema RhoQuotationClassFibres RhoIntrinsicCanonicalBag RhoFiniteParallelSplits
open RhoIntrinsicReadback MeTTaIL.Syntax

local instance processClassDecision (context : Ctx sig) : DecidableEq (Process context) :=
  equationClassDecision context Srt.pr

theorem reconstruction_injective {context : Ctx sig} (process : Process context) :
    Function.Injective (fun cut : {parts : Multiset Pattern // parts ∈ cuts process} =>
      makeSplit process cut.val ((mem_cuts _ _).mp cut.property)) := by
  intro first second same
  apply Subtype.ext
  have inventory := congrArg (fun pair : Process context × Process context => components pair.1) same
  change components (factor process first.val _) = components (factor process second.val _) at inventory
  simpa only [factor_components] using inventory

theorem candidates_card_eq_cuts {context : Ctx sig} (process : Process context) :
    (candidates process).card = (cuts process).card := by
  rw [candidates, Finset.card_image_of_injective _ (reconstruction_injective process), Finset.card_attach]

theorem candidates_card_le_power {context : Ctx sig} (process : Process context) :
    (candidates process).card ≤ 2 ^ (components process).card := by
  rw [candidates_card_eq_cuts, cuts]
  simpa only [Multiset.card_powerset] using (components process).powerset.toFinset_card_le

theorem zero_has_one_value_split (context : Ctx sig) : (candidates (zero context)).card = 1 := by
  rw [candidates_card_eq_cuts, cuts, zero_components]
  simp

theorem singleton_powerset (component : Pattern) :
    ({component} : Multiset Pattern).powerset = {0, {component}} := by
  change (component ::ₘ (0 : Multiset Pattern)).powerset = _
  rw [Multiset.powerset_cons, Multiset.powerset_zero, Multiset.map_singleton]
  rfl

theorem single_component_has_two_value_splits {context : Ctx sig} (process : Process context)
    (component : Pattern) (inventory : components process = {component}) :
    (candidates process).card = 2 := by
  rw [candidates_card_eq_cuts, cuts, inventory]
  rw [singleton_powerset]
  simp

theorem two_equal_components_have_three_value_splits {context : Ctx sig} (process : Process context)
    (component : Pattern) (inventory : components process = {component, component}) :
    (candidates process).card = 3 := by
  rw [candidates_card_eq_cuts, cuts, inventory]
  change ((component ::ₘ ({component} : Multiset Pattern)).powerset.toFinset).card = 3
  rw [Multiset.powerset_cons, singleton_powerset]
  simp

end Mettapedia.OSLF.Binding.RhoFiniteParallelSplitCounts
