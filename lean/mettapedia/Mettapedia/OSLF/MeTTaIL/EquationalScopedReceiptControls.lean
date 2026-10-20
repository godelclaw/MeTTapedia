import Mettapedia.OSLF.MeTTaIL.EquationalScopedReceipts
import Mettapedia.OSLF.MeTTaIL.EquationalScopedMatchingControls

/-! Positive and corrupt-history controls for recursive collection receipts. -/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.EquationalScopedReceipts.Controls

open Syntax RuleBinding ScopedRuleMatching CollectionSelection
open EquationalScopedMatching
open EquationalScopedMatching.Controls
open ScopedCollectionMatching.Controls (a spec)

def schema : Pattern := set [x, y]
def target : Pattern := set [a]
def selected : Allocation Pattern :=
  ⟨[a, a], [], [⟨0, true⟩, ⟨0, false⟩]⟩

def xAssignment : Assignment := [("X", ⟨[], 0, a⟩)]
def xyAssignment : Assignment := [("Y", ⟨[], 0, a⟩), ("X", ⟨[], 0, a⟩)]

theorem selected_present : selected ∈ tracedAllocations true 2 [a] := by decide

theorem capture_x :
    captureWith? literalBodyComparison (authored schema) spec 0 0 .left [0]
      [] "X" a = some xAssignment := by decide

theorem capture_y :
    captureWith? literalBodyComparison (authored schema) spec 0 0 .left [1]
      xAssignment "Y" a = some xyAssignment := by decide

theorem singleton_reuse_receipt :
    Matches literalBodyComparison (authored schema) spec 0 .left [] 0 [] schema target
      [⟨[], .hashSet, selected.decisions⟩] xyAssignment := by
  apply Matches.unordered (by decide) selected_present
  · exact .cons (.capture capture_x) (.cons (.capture capture_y) .nil)
  · change (PatternLexOrder.sortLex ([] : List Pattern)).dedup = [] ∧
        xyAssignment = xyAssignment
    constructor
    · have empty : PatternLexOrder.sortLex ([] : List Pattern) = [] :=
        (PatternLexOrder.sortLex_perm []).symm.eq_nil
      rw [empty]
      rfl
    · rfl

theorem singleton_reuse_meaning :
    Meaning literalBodyComparison (authored schema) spec 0 .left [] 0 []
      schema target xyAssignment := singleton_reuse_receipt.meaning

example : replay false [a] selected.decisions = none := by decide
example : selected ∉ tracedAllocations false 2 [a] := by decide

end Mettapedia.OSLF.MeTTaIL.EquationalScopedReceipts.Controls
