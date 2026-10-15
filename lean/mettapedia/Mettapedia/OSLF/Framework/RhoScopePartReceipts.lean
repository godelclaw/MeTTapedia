import Mettapedia.OSLF.Framework.RhoScopeFiniteStep
import Mettapedia.OSLF.Framework.RhoGeneratedScopeStrata
import Mettapedia.OSLF.Framework.RhoGeneratedScopeSubstitution

/-!
# Constructed certificates for atomic and recursive scope parts

An atomic part retains its actual process premise. A recursive part retains
the parsed child name, its complete bounded certificate and the actual drop
readout. These data are assembled into the existing scope derivation, rather
than extracted from erased propositional existence.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Framework.RhoScopePartReceipts

open Mettapedia.OSLF.Binding
open RhoSchema RhoQuotationClassFibres RhoDroppedNameReadout
open RhoEquationGeneratedScope RhoGeneratedScopeStrata RhoScopeFiniteStep

abbrev BoundedReceipt {context : Ctx sig} (left right : Process context → Prop)
    (limit : Nat) (name : Name context) :=
  {certificate : Certificate left right name // certificate.depth ≤ limit}

inductive PartReceipt {context : Ctx sig} (left right : Process context → Prop)
    (limit : Nat) (atom : Process context → Prop) (process : Process context) where
  | atomic (admitted : atom process)
  | recursive (child : Name context) (receipt : BoundedReceipt left right limit child)
      (readout : drop child = process)

def part? {context : Ctx sig} (left right atom : Process context → Prop)
    [DecidablePred atom] (limit : Nat)
    (children : (name : Name context) → Option (BoundedReceipt left right limit name))
    (process : Process context) : Option (PartReceipt left right limit atom process) :=
  if atomic : atom process then some (.atomic atomic)
  else match readout : child? process with
    | none => none
    | some child => (children child).map fun receipt => .recursive child receipt (child_sound readout)

theorem part?_presence {context : Ctx sig} (left right atom : Process context → Prop)
    [DecidablePred atom] (limit : Nat)
    (children : (name : Name context) → Option (BoundedReceipt left right limit name))
    (process : Process context) :
    (part? left right atom limit children process).isSome = true ↔
      atom process ∨ recursivePart (fun child => (children child).isSome = true) process := by
  unfold part?
  split
  · next atomic => simp [atomic]
  · next notAtomic =>
    split
    · next absent =>
      simp only [Option.isSome_none, Bool.false_eq_true, false_iff, notAtomic, false_or]
      rintro ⟨child, impossible, _⟩
      rw [absent] at impossible
      cases impossible
    · next child readout =>
      simp only [Option.isSome_map, notAtomic, false_or]
      constructor
      · intro present
        exact ⟨child, readout, present⟩
      · rintro ⟨other, otherReadout, present⟩
        have same : child = other := Option.some.inj (readout.symm.trans otherReadout)
        exact same.symm ▸ present

theorem partReceipt_sound {context : Ctx sig} {left right atom : Process context → Prop}
    {limit : Nat} {process : Process context} (receipt : PartReceipt left right limit atom process) :
    Part atom (Bounded left right limit) process := by
  cases receipt with
  | atomic admitted => exact Or.inl admitted
  | recursive child certificate readout =>
    exact Or.inr ⟨child, ⟨certificate.val, certificate.property⟩, readout.symm⟩

def assemble {context : Ctx sig} {left right : Process context → Prop} {limit : Nat}
    {first second : Process context}
    (firstReceipt : PartReceipt left right limit left first)
    (secondReceipt : PartReceipt left right limit right second) :
    BoundedReceipt left right (limit + 1) (quote (join first second)) := by
  cases firstReceipt with
  | atomic firstAtom =>
    cases secondReceipt with
    | atomic secondAtom => exact ⟨.atoms first second firstAtom secondAtom, Nat.zero_le _⟩
    | recursive child certificate readout =>
      subst second
      exact ⟨.right first firstAtom child certificate.val, Nat.add_le_add_right certificate.property 1⟩
  | recursive firstChild firstCertificate firstReadout =>
    subst first
    cases secondReceipt with
    | atomic secondAtom =>
      exact ⟨.left firstChild firstCertificate.val second secondAtom,
        Nat.add_le_add_right firstCertificate.property 1⟩
    | recursive secondChild secondCertificate secondReadout =>
      subst second
      exact ⟨.both firstChild secondChild firstCertificate.val secondCertificate.val,
        Nat.add_le_add_right (max_le firstCertificate.property secondCertificate.property) 1⟩

end Mettapedia.OSLF.Framework.RhoScopePartReceipts
