import Mettapedia.OSLF.Syntax.RhoScopedScopeDecomposition
import Mettapedia.Algebra.NameSupportedDecomposition
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Context

/-!
# Actual channel supports and the detection condition for scoped decomposition

The canonical channel support equals the union of supports of the complete
typed parallel inventory. Whole-extension name separation therefore earns
component separation when the left scope detects every admitted component
by a channel. Faithful quotation readback then earns unique quoted halves.
All statements use the original equation quotient in arbitrary source contexts.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.RhoScopedNameSeparatedDecomposition

open RhoSchema RhoQuotationClassFibres RhoScopedParallelInventory RhoScopedScopeDecomposition
open RhoIntrinsicCanonicalBag RhoSchema.IntrinsicEncoding
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.Context
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.Canonical
open Mettapedia.Algebra

variable {context : Ctx sig}

theorem freeNames_collapseBag (patterns : List Pattern) (name : Pattern) :
    name ∈ freeNames (collapseBag patterns) ↔
      ∃ pattern ∈ patterns, name ∈ freeNames pattern := by
  cases patterns with
  | nil => simp [collapseBag, freeNames]
  | cons first rest =>
    cases rest with
    | nil => simp [collapseBag]
    | cons second rest =>
      rw [collapseBag, freeNames, Mettapedia.Lists.SetFold.Set.mem_foldl_union] <;> simp

def componentSupport (prime : Prime context) : Set Pattern := freeNames prime.val

def channelSupport (process : Process context) : Set Pattern :=
  freeNames (encodeEquationClass process)

/-- Actual canonical channel support is recovered from the complete occurrence inventory. -/
theorem channelSupport_eq_inventory (process : Process context) :
    channelSupport process = NameSupportedDecomposition.names componentSupport (read process) := by
  apply Set.ext
  intro name
  have represented := encode_realize (decompose process)
  rw [realize_decompose] at represented
  change name ∈ freeNames (encodeEquationClass process) ↔ _
  rw [represented, freeNames_collapseBag, ordered_decompose]
  constructor
  · rintro ⟨pattern, member, carried⟩
    have listed : pattern ∈ values (read process) := by
      rw [values_read]
      exact member
    obtain ⟨prime, listedPrime, same⟩ := Multiset.mem_map.mp listed
    refine ⟨prime, listedPrime, ?_⟩
    change name ∈ freeNames prime.val
    rw [same]
    exact carried
  · rintro ⟨prime, member, carried⟩
    refine ⟨prime.val, ?_, carried⟩
    have listed : prime.val ∈ values (read process) :=
      Multiset.mem_map.mpr ⟨prime, member, rfl⟩
    rw [values_read] at listed
    exact listed

theorem channelSupport_join (first second : Process context) :
    channelSupport (join first second) = channelSupport first ∪ channelSupport second := by
  rw [channelSupport_eq_inventory, read_join,
    channelSupport_eq_inventory, channelSupport_eq_inventory]
  ext name
  simp [NameSupportedDecomposition.names, Multiset.mem_add, or_and_right, exists_or]

def NameSeparated (left right : Process context → Prop) : Prop :=
  ∀ first second, left first → right second → Disjoint (channelSupport first) (channelSupport second)

def NamesDetect (scope : Process context → Prop) : Prop :=
  ∀ process, scope process → ∀ prime ∈ read process, ∃ name, name ∈ componentSupport prime

theorem component_separation_of_name_separation {left right : Process context → Prop}
    (separated : NameSeparated left right) (detected : NamesDetect left) :
    ComponentSeparated left right := by
  have inventorySeparated : NameSupportedDecomposition.NameSeparated componentSupport
      (inventoryScope left) (inventoryScope right) := by
    intro first second firstAdmitted secondAdmitted
    have actual := separated (write first) (write second) firstAdmitted secondAdmitted
    rwa [channelSupport_eq_inventory, channelSupport_eq_inventory, read_write, read_write] at actual
  have inventoryDetected : NameSupportedDecomposition.NamesDetect componentSupport
      (inventoryScope left) := by
    intro inventory admitted prime member
    have actual := detected (write inventory) admitted prime
    rw [read_write] at actual
    exact actual member
  exact NameSupportedDecomposition.particle_separation_of_name_separation
    inventorySeparated inventoryDetected

/-- Complete channel separation and detection suffice after quotation exposure is earned. -/
theorem named_quoted_decomposition_unique {left right : Process context → Prop}
    (separated : NameSeparated left right) (detected : NamesDetect left)
    (exposed : ExposedComposites left right) {name : Name context}
    (member : Composite left right name) :
    ∃! pair : Process context × Process context,
      left pair.1 ∧ right pair.2 ∧ quote (join pair.1 pair.2) = name :=
  composite_unique (component_separation_of_name_separation separated detected) exposed member

end Mettapedia.OSLF.Binding.RhoScopedNameSeparatedDecomposition
