import Mettapedia.OSLF.Framework.RhoScopePairReceipts
import Mettapedia.OSLF.Framework.RhoScopeBoundedDecision
import Mettapedia.OSLF.Syntax.RhoQuotedParallelLists

/-!
# Complete constructed scope receipts at a supplied finite depth

The search traverses the constructed decomposition list and retains the first
successful derivation. Recursive calls decrease the supplied depth. Returned
data contain the actual source process premises and child certificates; a
separate induction proves presence exactly at semantic bounded membership.
The selection is a declared search order, not uniqueness of scope evidence.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Framework.RhoScopeBoundedReceipts

open Mettapedia.OSLF.Binding
open RhoSchema RhoQuotationClassFibres RhoQuotedParallelLists
open RhoEquationGeneratedScope RhoGeneratedScopeStrata RhoScopeFiniteStep
open RhoScopePartReceipts RhoScopePairReceipts RhoScopeBoundedDecision

def select? {context : Ctx sig} {left right : Process context → Prop} (limit : Nat)
    (pairs : (first second : Process context) →
      Option (BoundedReceipt left right limit (quote (join first second))))
    (name : Name context) : Option (BoundedReceipt left right limit name) :=
  (decompositionList name).findSome? fun (entry : Decomposition name) =>
    (pairs entry.val.1 entry.val.2).map fun receipt => entry.property ▸ receipt

theorem select?_presence {context : Ctx sig} {left right : Process context → Prop} (limit : Nat)
    (pairs : (first second : Process context) →
      Option (BoundedReceipt left right limit (quote (join first second))))
    (name : Name context) :
    (select? limit pairs name).isSome = true ↔
      ∃ first second, quote (join first second) = name ∧ (pairs first second).isSome = true := by
  unfold select?
  rw [List.findSome?_isSome_iff]
  simp only [Option.isSome_map]
  constructor
  · rintro ⟨entry, _, accepted⟩
    exact ⟨entry.val.1, entry.val.2, entry.property, accepted⟩
  · rintro ⟨first, second, readout, accepted⟩
    obtain ⟨entry, listed, pairReadout⟩ := decompositionList_complete name first second readout
    refine ⟨entry, listed, ?_⟩
    rw [pairReadout]
    exact accepted

def boundedReceipt? {context : Ctx sig} (left right : Process context → Prop)
    [DecidablePred left] [DecidablePred right] :
    (limit : Nat) → (name : Name context) → Option (BoundedReceipt left right limit name)
  | 0, name => select? 0 (basePair? left right) name
  | limit + 1, name => select? (limit + 1)
      (successorPair? left right limit (boundedReceipt? left right limit)) name

theorem boundedReceipt?_presence {context : Ctx sig} (left right : Process context → Prop)
    [DecidablePred left] [DecidablePred right] (limit : Nat) (name : Name context) :
    (boundedReceipt? left right limit name).isSome = true ↔ Bounded left right limit name := by
  induction limit generalizing name with
  | zero =>
    rw [boundedReceipt?, select?_presence, bounded_zero_iff_atoms]
    simp only [basePair?_presence]
    constructor
    · rintro ⟨first, second, readout, firstAtom, secondAtom⟩
      exact ⟨first, second, firstAtom, secondAtom, readout⟩
    · rintro ⟨first, second, firstAtom, secondAtom, readout⟩
      exact ⟨first, second, readout, firstAtom, secondAtom⟩
  | succ limit ih =>
    rw [boundedReceipt?, select?_presence, bounded_succ_iff]
    have namesAgree : (fun child => (boundedReceipt? left right limit child).isSome = true) =
        Bounded left right limit := funext fun child => propext (ih child)
    simp only [successorPair?_presence, namesAgree, ← part_readout_iff]
    rfl

theorem boundedReceipt?_none_iff {context : Ctx sig} (left right : Process context → Prop)
    [DecidablePred left] [DecidablePred right] (limit : Nat) (name : Name context) :
    boundedReceipt? left right limit name = none ↔ ¬ Bounded left right limit name := by
  rw [← boundedReceipt?_presence]
  cases boundedReceipt? left right limit name <;> simp

end Mettapedia.OSLF.Framework.RhoScopeBoundedReceipts
