import Mettapedia.OSLF.Syntax.RhoIntrinsicCanonicalBag
import Mathlib.Data.Multiset.Powerset

/-!
# Complete finite parallel-split catalogues in every intrinsic rho context

All submultisets of the actual prime inventory are enumerated. Reconstructing
a selected inventory and its complement gives a genuine source parallel
split. The inverse process/inventory comparison proves that every source split
occurs in this catalogue, including units and repeated equal components.
The catalogue lists value pairs; it does not reconstruct runtime occurrences
or an omitted execution provenance ledger.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.RhoFiniteParallelSplits

open RhoSchema RhoQuotationClassFibres RhoIntrinsicReadback RhoIntrinsicCanonicalBag
open MeTTaIL.Syntax

local instance processClassDecision (context : Ctx sig) : DecidableEq (Process context) :=
  equationClassDecision context Srt.pr

def subInventory {context : Ctx sig} (process : Process context) (parts : Multiset Pattern)
    (included : parts ≤ components process) : Inventory context :=
  ⟨parts, fun pattern member => (decompose process).property pattern
    (Multiset.mem_of_le included member)⟩

def factor {context : Ctx sig} (process : Process context) (parts : Multiset Pattern)
    (included : parts ≤ components process) : Process context := realize (subInventory process parts included)

theorem factor_components {context : Ctx sig} (process : Process context) (parts : Multiset Pattern)
    (included : parts ≤ components process) : components (factor process parts included) = parts := by
  change (decompose (realize (subInventory process parts included))).val = parts
  rw [decompose_realize]
  rfl

def makeSplit {context : Ctx sig} (process : Process context) (parts : Multiset Pattern)
    (included : parts ≤ components process) : Process context × Process context :=
  (factor process parts included,
    factor process (components process - parts) (Multiset.sub_le_self _ _))

theorem makeSplit_sound {context : Ctx sig} (process : Process context) (parts : Multiset Pattern)
    (included : parts ≤ components process) :
    join (makeSplit process parts included).1 (makeSplit process parts included).2 = process := by
  apply components_injective context
  rw [join_components]
  change components (factor process parts included) +
    components (factor process (components process - parts) _) = components process
  rw [factor_components, factor_components, add_comm]
  exact Multiset.sub_add_cancel included

def cuts {context : Ctx sig} (process : Process context) : Finset (Multiset Pattern) :=
  (components process).powerset.toFinset

theorem mem_cuts {context : Ctx sig} (process : Process context) (parts : Multiset Pattern) :
    parts ∈ cuts process ↔ parts ≤ components process := by
  rw [cuts, Multiset.mem_toFinset, Multiset.mem_powerset]

def candidates {context : Ctx sig} (process : Process context) :
    Finset (Process context × Process context) :=
  (cuts process).attach.image fun cut => makeSplit process cut.val ((mem_cuts _ _).mp cut.property)

theorem candidates_sound {context : Ctx sig} (process first second : Process context)
    (member : (first, second) ∈ candidates process) : join first second = process := by
  obtain ⟨cut, _, readout⟩ := Finset.mem_image.mp member
  have actual := makeSplit_sound process cut.val ((mem_cuts _ _).mp cut.property)
  rw [readout] at actual
  exact actual

theorem candidates_complete {context : Ctx sig} (process first second : Process context)
    (readout : join first second = process) : (first, second) ∈ candidates process := by
  have inventory : components first + components second = components process := by
    rw [← readout, join_components]
  have included : components first ≤ components process := by
    rw [← inventory]
    exact Multiset.le_add_right _ _
  let cut : {parts : Multiset Pattern // parts ∈ cuts process} :=
    ⟨components first, (mem_cuts _ _).mpr included⟩
  apply Finset.mem_image.mpr
  refine ⟨cut, Finset.mem_attach _ cut, ?_⟩
  apply Prod.ext
  · apply components_injective context
    exact factor_components process (components first) ((mem_cuts _ _).mp cut.property)
  · apply components_injective context
    change components (factor process (components process - components first) _) = components second
    rw [factor_components, ← inventory, add_comm]
    exact Multiset.add_sub_cancel_right

theorem parallel_split_iff {context : Ctx sig} (process first second : Process context) :
    join first second = process ↔ (first, second) ∈ candidates process :=
  ⟨candidates_complete process first second, candidates_sound process first second⟩

end Mettapedia.OSLF.Binding.RhoFiniteParallelSplits
