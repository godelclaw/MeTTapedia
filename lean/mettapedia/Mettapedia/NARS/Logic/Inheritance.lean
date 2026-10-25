import Mathlib.Tactic
import Mathlib.Data.Finset.Basic
import Mettapedia.KR.ConceptGeometry.AbstractInheritance

/-!
# NARS-Style Dual Inheritance

This module formalizes a small semantic core for NARS-style inheritance:

- terms carry both extensional and intensional meaning
- inheritance is simultaneously extent inclusion and reversed intent inclusion
- positive and negative extensional/intensional witness sets remain separate

The PLN `BinaryEvidence` and truth-value readouts are deliberately separated
into `Mettapedia.NARS.Bridges.PLN.InheritanceEvidence`.
-/

namespace Mettapedia.NARS.Logic.Inheritance

open Mettapedia.KR.ConceptGeometry
open Mettapedia.KR.ConceptGeometry.AbstractInheritance

universe u v w

/-- A minimal NARS term language for dual inheritance. -/
inductive Term (Atom : Type u) where
  | atom : Atom → Term Atom
  | inter : Term Atom → Term Atom → Term Atom
  | iinter : Term Atom → Term Atom → Term Atom
  | diff : Term Atom → Term Atom → Term Atom
  | idiff : Term Atom → Term Atom → Term Atom
  deriving DecidableEq, Repr

/-- Set-valued interpretation of every term, independent of the finite frame
implementation. The two difference operations retain their distinct channels. -/
def Term.denote {Obj : Type v} {Attr : Type w} (meaning : Atom → DualConcept Obj Attr) :
    Term Atom → DualConcept Obj Attr
  | .atom a => meaning a
  | .inter s t => DualConcept.inter (s.denote meaning) (t.denote meaning)
  | .iinter s t => DualConcept.union (s.denote meaning) (t.denote meaning)
  | .diff s t => DualConcept.diff (s.denote meaning) (t.denote meaning)
  | .idiff s t => DualConcept.idiff (s.denote meaning) (t.denote meaning)

/-- A semantic frame gives each atomic term both an extension and an intension. -/
structure Frame (Atom : Type u) (Obj : Type v) (Attr : Type w) where
  atomExtension : Atom → Finset Obj
  atomIntension : Atom → Finset Attr

namespace Frame

variable {Atom : Type u} {Obj : Type v} {Attr : Type w}
variable [DecidableEq Obj] [DecidableEq Attr]

/-- Recursive extensional meaning of a term. -/
def extension (F : Frame Atom Obj Attr) : Term Atom → Finset Obj
  | .atom a => F.atomExtension a
  | .inter s t => F.extension s ∩ F.extension t
  | .iinter s t => F.extension s ∪ F.extension t
  | .diff s t => F.extension s \ F.extension t
  | .idiff s _t => F.extension s

/-- Recursive intensional meaning of a term. -/
def intension (F : Frame Atom Obj Attr) : Term Atom → Finset Attr
  | .atom a => F.atomIntension a
  | .inter s t => F.intension s ∪ F.intension t
  | .iinter s t => F.intension s ∩ F.intension t
  | .diff s _t => F.intension s
  | .idiff s t => F.intension s \ F.intension t

omit [DecidableEq Attr] in
@[simp] theorem extension_atom (F : Frame Atom Obj Attr) (a : Atom) :
    F.extension (.atom a) = F.atomExtension a := rfl

omit [DecidableEq Obj] in
@[simp] theorem intension_atom (F : Frame Atom Obj Attr) (a : Atom) :
    F.intension (.atom a) = F.atomIntension a := rfl

/-- Extensional inheritance is subset between extensions. -/
def ExtensionalInherits (F : Frame Atom Obj Attr) (s p : Term Atom) : Prop :=
  F.extension s ⊆ F.extension p

/-- Intensional inheritance is reversed subset between intensions. -/
def IntensionalInherits (F : Frame Atom Obj Attr) (s p : Term Atom) : Prop :=
  F.intension p ⊆ F.intension s

/-- Full NARS inheritance requires both channels. -/
def Inherits (F : Frame Atom Obj Attr) (s p : Term Atom) : Prop :=
  F.ExtensionalInherits s p ∧ F.IntensionalInherits s p

instance instDecidableExtensionalInherits
    (F : Frame Atom Obj Attr) (s p : Term Atom) :
    Decidable (F.ExtensionalInherits s p) := by
  unfold ExtensionalInherits
  infer_instance

instance instDecidableIntensionalInherits
    (F : Frame Atom Obj Attr) (s p : Term Atom) :
    Decidable (F.IntensionalInherits s p) := by
  unfold IntensionalInherits
  infer_instance

instance instDecidableInherits
    (F : Frame Atom Obj Attr) (s p : Term Atom) :
    Decidable (F.Inherits s p) := by
  unfold Inherits
  infer_instance

@[simp] theorem inherits_iff (F : Frame Atom Obj Attr) (s p : Term Atom) :
    F.Inherits s p ↔
      F.extension s ⊆ F.extension p ∧ F.intension p ⊆ F.intension s := Iff.rfl

/-- Positive extensional witnesses for `S -> P`: members shared by both
extensions. -/
def positiveExtensionalWitnesses
    (F : Frame Atom Obj Attr) (s p : Term Atom) : Finset Obj :=
  F.extension s ∩ F.extension p

/-- Negative extensional witnesses for `S -> P`: members of `S` outside `P`. -/
def negativeExtensionalWitnesses
    (F : Frame Atom Obj Attr) (s p : Term Atom) : Finset Obj :=
  F.extension s \ F.extension p

/-- Positive intensional witnesses for `S -> P`: properties of `P` already
present in `S`. -/
def positiveIntensionalWitnesses
    (F : Frame Atom Obj Attr) (s p : Term Atom) : Finset Attr :=
  F.intension p ∩ F.intension s

/-- Negative intensional witnesses for `S -> P`: properties of `P` missing
from `S`. -/
def negativeIntensionalWitnesses
    (F : Frame Atom Obj Attr) (s p : Term Atom) : Finset Attr :=
  F.intension p \ F.intension s

omit [DecidableEq Attr] in
theorem negativeExtensionalWitnesses_eq_empty_of_extensionalInherits
    (F : Frame Atom Obj Attr) {s p : Term Atom}
    (hsp : F.ExtensionalInherits s p) :
    F.negativeExtensionalWitnesses s p = ∅ := by
  unfold negativeExtensionalWitnesses
  exact Finset.sdiff_eq_empty_iff_subset.mpr hsp

omit [DecidableEq Obj] in
theorem negativeIntensionalWitnesses_eq_empty_of_intensionalInherits
    (F : Frame Atom Obj Attr) {s p : Term Atom}
    (hsp : F.IntensionalInherits s p) :
    F.negativeIntensionalWitnesses s p = ∅ := by
  unfold negativeIntensionalWitnesses
  exact Finset.sdiff_eq_empty_iff_subset.mpr hsp

/-- The finite NARS semantics factors through the abstract dual-inheritance
core by coercing finite extents/intents to sets. -/
def interpretation (F : Frame Atom Obj Attr) :
    AbstractInheritance.Interpretation (Term Atom) Obj Attr where
  meaning t :=
    { extent := F.extension t
      intent := F.intension t }

@[simp] theorem interpretation_inter (F : Frame Atom Obj Attr) (s t : Term Atom) :
    F.interpretation.meaning (.inter s t) =
      DualConcept.inter (F.interpretation.meaning s) (F.interpretation.meaning t) := by
  apply DualConcept.ext <;> simp [interpretation, extension, intension, DualConcept.inter]

@[simp] theorem interpretation_iinter (F : Frame Atom Obj Attr) (s t : Term Atom) :
    F.interpretation.meaning (.iinter s t) =
      DualConcept.union (F.interpretation.meaning s) (F.interpretation.meaning t) := by
  apply DualConcept.ext <;> simp [interpretation, extension, intension, DualConcept.union]

@[simp] theorem interpretation_diff (F : Frame Atom Obj Attr) (s t : Term Atom) :
    F.interpretation.meaning (.diff s t) =
      DualConcept.diff (F.interpretation.meaning s) (F.interpretation.meaning t) := by
  apply DualConcept.ext <;> simp [interpretation, extension, intension, DualConcept.diff]

@[simp] theorem interpretation_idiff (F : Frame Atom Obj Attr) (s t : Term Atom) :
    F.interpretation.meaning (.idiff s t) =
      DualConcept.idiff (F.interpretation.meaning s) (F.interpretation.meaning t) := by
  apply DualConcept.ext <;> simp [interpretation, extension, intension, DualConcept.idiff]

/-- Every compound term agrees across the independent finite and set evaluators. -/
theorem interpretation_meaning_eq_denote (F : Frame Atom Obj Attr) (t : Term Atom) :
    F.interpretation.meaning t =
      t.denote (fun a => ⟨F.atomExtension a, F.atomIntension a⟩) := by
  induction t <;> simp_all only [Term.denote, interpretation_inter,
    interpretation_iinter, interpretation_diff, interpretation_idiff]
  rfl

theorem abstract_extensionalInherits_iff
    (F : Frame Atom Obj Attr) (s p : Term Atom) :
    (F.interpretation).ExtensionalInherits s p ↔ F.ExtensionalInherits s p := Iff.rfl

theorem abstract_intensionalInherits_iff
    (F : Frame Atom Obj Attr) (s p : Term Atom) :
    (F.interpretation).IntensionalInherits s p ↔ F.IntensionalInherits s p := Iff.rfl

theorem abstract_inherits_iff
    (F : Frame Atom Obj Attr) (s p : Term Atom) :
    (F.interpretation).Inherits s p ↔ F.Inherits s p := Iff.rfl

end Frame

namespace Examples

inductive ConceptAtom where
  | bird
  | penguin
  | flyer
  deriving DecidableEq, Repr

inductive Creature where
  | tweety
  | pingu
  deriving DecidableEq, Repr

inductive Feature where
  | winged
  | aquatic
  | flies
  deriving DecidableEq, Repr

def ontologyFrame : Frame ConceptAtom Creature Feature where
  atomExtension
    | .bird => {Creature.tweety, Creature.pingu}
    | .penguin => {Creature.pingu}
    | .flyer => {Creature.tweety}
  atomIntension
    | .bird => {Feature.winged}
    | .penguin => {Feature.winged, Feature.aquatic}
    | .flyer => {Feature.flies}

def bird : Term ConceptAtom := .atom .bird
def penguin : Term ConceptAtom := .atom .penguin
def flyer : Term ConceptAtom := .atom .flyer

theorem penguin_inherits_bird :
    ontologyFrame.Inherits penguin bird := by
  decide

theorem bird_does_not_inherit_flyer :
    ¬ ontologyFrame.Inherits bird flyer := by
  decide

theorem bird_inherits_iinter_bird_flyer :
    ontologyFrame.Inherits bird (.iinter bird flyer) := by
  decide

theorem not_iinter_bird_flyer_inherits_bird :
    ¬ ontologyFrame.Inherits (.iinter bird flyer) bird := by
  decide

theorem bird_minus_penguin_inherits_bird :
    ontologyFrame.Inherits (.diff bird penguin) bird := by
  decide

theorem bird_inherits_bird_idiff_penguin :
    ontologyFrame.Inherits bird (.idiff bird penguin) := by
  decide

theorem bird_does_not_inherit_bird_minus_penguin :
    ¬ ontologyFrame.Inherits bird (.diff bird penguin) := by
  decide

end Examples

end Mettapedia.NARS.Logic.Inheritance
