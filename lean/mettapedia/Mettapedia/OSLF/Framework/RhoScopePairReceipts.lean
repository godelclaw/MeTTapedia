import Mettapedia.OSLF.Framework.RhoScopePartReceipts

/-!
# Constructed bounded certificates at one actual parallel pair

The depth-zero calculation tests both atomic premises. The successor
calculation retains each selected atomic or recursive part and assembles an
existing scope certificate. Presence is compared with independently read
part predicates, rather than defining those predicates by search success.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Framework.RhoScopePairReceipts

open Mettapedia.OSLF.Binding
open RhoSchema RhoQuotationClassFibres
open RhoEquationGeneratedScope RhoScopeFiniteStep RhoScopePartReceipts

def basePair? {context : Ctx sig} (left right : Process context → Prop)
    [DecidablePred left] [DecidablePred right] (first second : Process context) :
    Option (BoundedReceipt left right 0 (quote (join first second))) :=
  if firstAtom : left first then
    if secondAtom : right second then some ⟨.atoms first second firstAtom secondAtom, Nat.le_refl 0⟩
    else none
  else none

theorem basePair?_presence {context : Ctx sig} (left right : Process context → Prop)
    [DecidablePred left] [DecidablePred right] (first second : Process context) :
    (basePair? left right first second).isSome = true ↔ left first ∧ right second := by
  unfold basePair?
  split
  · split <;> simp_all
  · simp_all

def successorPair? {context : Ctx sig} (left right : Process context → Prop)
    [DecidablePred left] [DecidablePred right] (limit : Nat)
    (children : (name : Name context) → Option (BoundedReceipt left right limit name))
    (first second : Process context) :
    Option (BoundedReceipt left right (limit + 1) (quote (join first second))) :=
  (part? left right left limit children first).bind fun firstReceipt =>
    (part? left right right limit children second).map fun secondReceipt => assemble firstReceipt secondReceipt

theorem successorPair?_presence {context : Ctx sig} (left right : Process context → Prop)
    [DecidablePred left] [DecidablePred right] (limit : Nat)
    (children : (name : Name context) → Option (BoundedReceipt left right limit name))
    (first second : Process context) :
    (successorPair? left right limit children first second).isSome = true ↔
      (left first ∨ recursivePart (fun child => (children child).isSome = true) first) ∧
      (right second ∨ recursivePart (fun child => (children child).isSome = true) second) := by
  have firstSpec := part?_presence left right left limit children first
  have secondSpec := part?_presence left right right limit children second
  unfold successorPair?
  cases firstReadout : part? left right left limit children first with
  | none => simp_all
  | some firstReceipt =>
    cases secondReadout : part? left right right limit children second <;> simp_all

end Mettapedia.OSLF.Framework.RhoScopePairReceipts
