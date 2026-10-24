import Mathlib.Order.Concept
import Mettapedia.KR.ConceptOntology.FCA

/-!
# Abstract Dual Inheritance

This module isolates a small set-theoretic core that matches the usual
extension/intension duality:

- extensional inheritance is extent inclusion
- intensional inheritance is reversed intent inclusion
- full inheritance requires both

`DualConcept` is intentionally the pre-closure notion: just an extent/intent
pair. Mathlib's `_root_.Concept` is the closed special case, and we connect to
it explicitly below rather than redefining FCA structure in parallel.

This module is the foundational dual inheritance layer for NARS-style dual
inheritance and the extensional slices derived from WM-PLN concept ontology.
-/

namespace Mettapedia.KR.ConceptGeometry.AbstractInheritance

open Mettapedia.KR.ConceptOntology

universe u v w

/-- A semantic concept with both an extent and an intent. -/
structure DualConcept (Obj : Type u) (Attr : Type v) where
  extent : Set Obj
  intent : Set Attr

namespace DualConcept

variable {Obj : Type u} {Attr : Type v}

@[ext] theorem ext {A B : DualConcept Obj Attr}
    (hExtent : A.extent = B.extent) (hIntent : A.intent = B.intent) : A = B := by
  cases A
  cases B
  simp_all

/-- A `DualConcept` is closed exactly when it is a mathlib formal concept for
the given relation. -/
def IsClosed (r : Obj → Attr → Prop) (A : DualConcept Obj Attr) : Prop :=
  _root_.upperPolar r A.extent = A.intent ∧
    _root_.lowerPolar r A.intent = A.extent

/-- Forget the closure proof on a mathlib formal concept. -/
def ofConcept {r : Obj → Attr → Prop}
    (c : _root_.Concept Obj Attr r) : DualConcept Obj Attr where
  extent := c.extent
  intent := c.intent

/-- Promote a closed dual concept to a mathlib formal concept. -/
def toConcept {r : Obj → Attr → Prop}
    (A : DualConcept Obj Attr) (hA : IsClosed r A) :
    _root_.Concept Obj Attr r where
  extent := A.extent
  intent := A.intent
  upperPolar_extent := hA.1
  lowerPolar_intent := hA.2

@[simp] theorem ofConcept_extent {r : Obj → Attr → Prop}
    (c : _root_.Concept Obj Attr r) :
    (ofConcept c).extent = c.extent := rfl

@[simp] theorem ofConcept_intent {r : Obj → Attr → Prop}
    (c : _root_.Concept Obj Attr r) :
    (ofConcept c).intent = c.intent := rfl

theorem isClosed_ofConcept {r : Obj → Attr → Prop}
    (c : _root_.Concept Obj Attr r) :
    IsClosed r (ofConcept c) := ⟨c.upperPolar_extent, c.lowerPolar_intent⟩

@[simp] theorem toConcept_ofConcept {r : Obj → Attr → Prop}
    (c : _root_.Concept Obj Attr r) :
    toConcept (ofConcept c) (isClosed_ofConcept c) = c := rfl

@[simp] theorem ofConcept_toConcept {r : Obj → Attr → Prop}
    (A : DualConcept Obj Attr) (hA : IsClosed r A) :
    ofConcept (toConcept A hA) = A := rfl

/-- Order-theoretic view of a dual concept: direct order on extents and dual
order on intents. This lets us reuse mathlib's product-order machinery. -/
def toOrderPair (A : DualConcept Obj Attr) : Set Obj × OrderDual (Set Attr) :=
  (A.extent, A.intent)

theorem toOrderPair_injective : Function.Injective (@toOrderPair Obj Attr) :=
  fun _ _ h => ext (congrArg Prod.fst h) (congrArg Prod.snd h)

/-- Extensional inheritance is ordinary extent inclusion. -/
def ExtensionalInherits (A B : DualConcept Obj Attr) : Prop :=
  A.extent ⊆ B.extent

/-- Intensional inheritance is reversed intent inclusion. -/
def IntensionalInherits (A B : DualConcept Obj Attr) : Prop :=
  B.intent ⊆ A.intent

/-- Full inheritance requires both extensional and intensional coherence. -/
def Inherits (A B : DualConcept Obj Attr) : Prop :=
  ExtensionalInherits A B ∧ IntensionalInherits A B

@[simp] theorem inherits_iff (A B : DualConcept Obj Attr) :
    Inherits A B ↔ A.extent ⊆ B.extent ∧ B.intent ⊆ A.intent := Iff.rfl

instance : LE (DualConcept Obj Attr) where
  le A B := toOrderPair A ≤ toOrderPair B

@[simp] theorem le_iff (A B : DualConcept Obj Attr) :
    A ≤ B ↔ Inherits A B := Iff.rfl

/-- Meet of raw meanings: smaller extent and richer intent. This need not
be FCA-closed even when both inputs are closed. -/
def inter (A B : DualConcept Obj Attr) : DualConcept Obj Attr where
  extent := A.extent ∩ B.extent
  intent := A.intent ∪ B.intent

/-- Join of raw meanings: larger extent and poorer intent. -/
def union (A B : DualConcept Obj Attr) : DualConcept Obj Attr where
  extent := A.extent ∪ B.extent
  intent := A.intent ∩ B.intent

instance : Min (DualConcept Obj Attr) := ⟨inter⟩
instance : Max (DualConcept Obj Attr) := ⟨union⟩
instance : PartialOrder (DualConcept Obj Attr) :=
  PartialOrder.lift toOrderPair toOrderPair_injective
instance : DistribLattice (DualConcept Obj Attr) :=
  toOrderPair_injective.distribLattice toOrderPair
    (by intro x y; rfl) (by intro x y; rfl)
    (by intro x y; rfl) (by intro x y; rfl)

/-- Exact product-order representation; no closure or finiteness premise. -/
def orderIso : DualConcept Obj Attr ≃o Set Obj × OrderDual (Set Attr) where
  toFun := toOrderPair
  invFun p := ⟨p.1, p.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := Iff.rfl

theorem inter_inherits_left (A B : DualConcept Obj Attr) :
    Inherits (inter A B) A := (inf_le_left : A ⊓ B ≤ A)

theorem inter_inherits_right (A B : DualConcept Obj Attr) :
    Inherits (inter A B) B := (inf_le_right : A ⊓ B ≤ B)

theorem inherits_inter_of_inherits {A B C : DualConcept Obj Attr}
    (hAB : Inherits A B) (hAC : Inherits A C) :
    Inherits A (inter B C) := (le_inf hAB hAC : A ≤ B ⊓ C)

/-- Remove objects while retaining the subject's attributes. -/
def diff (A B : DualConcept Obj Attr) : DualConcept Obj Attr :=
  ⟨A.extent \ B.extent, A.intent⟩

/-- Remove attributes while retaining the subject's objects. -/
def idiff (A B : DualConcept Obj Attr) : DualConcept Obj Attr :=
  ⟨A.extent, A.intent \ B.intent⟩

theorem diff_le_left (A B : DualConcept Obj Attr) : diff A B ≤ A :=
  ⟨Set.sdiff_subset, Set.Subset.rfl⟩

theorem le_idiff_left (A B : DualConcept Obj Attr) : A ≤ idiff A B :=
  ⟨Set.Subset.rfl, Set.sdiff_subset⟩

theorem monotone_diff_left (B : DualConcept Obj Attr) : Monotone (diff · B) :=
  fun _ _ h => ⟨Set.sdiff_subset_sdiff_left h.1, h.2⟩

theorem antitone_diff_right (A : DualConcept Obj Attr) : Antitone (diff A) :=
  fun _ _ h => ⟨Set.sdiff_subset_sdiff_right h.1, Set.Subset.rfl⟩

theorem monotone_idiff_left (B : DualConcept Obj Attr) : Monotone (idiff · B) :=
  fun _ _ h => ⟨h.1, Set.sdiff_subset_sdiff_left h.2⟩

theorem antitone_idiff_right (A : DualConcept Obj Attr) : Antitone (idiff A) :=
  fun _ _ h => ⟨Set.Subset.rfl, Set.sdiff_subset_sdiff_right h.2⟩

theorem ofConcept_le_iff {r : Obj → Attr → Prop}
    (c d : _root_.Concept Obj Attr r) :
    ofConcept c ≤ ofConcept d ↔ c ≤ d := by
  constructor
  · intro h
    exact _root_.Concept.extent_subset_extent_iff.mp h.1
  · intro h
    exact ⟨_root_.Concept.extent_subset_extent_iff.mpr h,
      (_root_.Concept.intent_subset_intent_iff (c := d) (d := c)).mpr h⟩

theorem ofConcept_inherits_iff {r : Obj → Attr → Prop}
    (c d : _root_.Concept Obj Attr r) :
    Inherits (ofConcept c) (ofConcept d) ↔ c ≤ d := by
  exact ofConcept_le_iff c d

theorem toConcept_le_iff {r : Obj → Attr → Prop}
    (A B : DualConcept Obj Attr) (hA : IsClosed r A) (hB : IsClosed r B) :
    toConcept A hA ≤ toConcept B hB ↔ A ≤ B := by
  simpa using (ofConcept_le_iff (toConcept A hA) (toConcept B hB)).symm

theorem toConcept_inherits_iff {r : Obj → Attr → Prop}
    (A B : DualConcept Obj Attr) (hA : IsClosed r A) (hB : IsClosed r B) :
    toConcept A hA ≤ toConcept B hB ↔ Inherits A B := by
  simpa [le_iff] using toConcept_le_iff A B hA hB

end DualConcept

/-- An abstract carrier interpreted as dual concepts. -/
structure Interpretation (Carrier : Type u) (Obj : Type v) (Attr : Type w) where
  meaning : Carrier → DualConcept Obj Attr

namespace Interpretation

variable {Carrier : Type u} {Obj : Type v} {Attr : Type w}

/-- Extensional inheritance transported through an interpretation. -/
def ExtensionalInherits (I : Interpretation Carrier Obj Attr) (a b : Carrier) : Prop :=
  DualConcept.ExtensionalInherits (I.meaning a) (I.meaning b)

/-- Intensional inheritance transported through an interpretation. -/
def IntensionalInherits (I : Interpretation Carrier Obj Attr) (a b : Carrier) : Prop :=
  DualConcept.IntensionalInherits (I.meaning a) (I.meaning b)

/-- Full dual inheritance transported through an interpretation. -/
def Inherits (I : Interpretation Carrier Obj Attr) (a b : Carrier) : Prop :=
  DualConcept.Inherits (I.meaning a) (I.meaning b)

/-- Crisp similarity/equivalence at the abstract inheritance layer: inheritance
in both directions. Numeric PLN similarity rules can consume this as the
collapsed 0/1 case without inventing a second semantic relation. -/
def MutualInherits (I : Interpretation Carrier Obj Attr) (a b : Carrier) : Prop :=
  I.Inherits a b ∧ I.Inherits b a

@[simp] theorem inherits_iff (I : Interpretation Carrier Obj Attr) (a b : Carrier) :
    I.Inherits a b ↔
      I.ExtensionalInherits a b ∧ I.IntensionalInherits a b := Iff.rfl

@[simp] theorem mutualInherits_iff (I : Interpretation Carrier Obj Attr) (a b : Carrier) :
    I.MutualInherits a b ↔ I.Inherits a b ∧ I.Inherits b a := Iff.rfl

theorem inherits_refl (I : Interpretation Carrier Obj Attr) (a : Carrier) :
    I.Inherits a a :=
  (le_rfl : I.meaning a ≤ I.meaning a)

theorem mutualInherits_symm (I : Interpretation Carrier Obj Attr) {a b : Carrier}
    (h : I.MutualInherits a b) :
    I.MutualInherits b a :=
  ⟨h.2, h.1⟩

theorem inherits_trans (I : Interpretation Carrier Obj Attr) {a b c : Carrier}
    (hab : I.Inherits a b) (hbc : I.Inherits b c) :
    I.Inherits a c :=
  (le_trans hab hbc : I.meaning a ≤ I.meaning c)

/-- Mutual inheritance identifies meanings, not necessarily carrier identities. -/
theorem mutualInherits_iff_meaning_eq (I : Interpretation Carrier Obj Attr) (a b : Carrier) :
    I.MutualInherits a b ↔ I.meaning a = I.meaning b :=
  ⟨fun h => le_antisymm h.1 h.2, fun h => ⟨le_of_eq h, le_of_eq h.symm⟩⟩

/-- Pairwise subset semantics induced directly from the abstract inheritance
foundation. This is the generic relation used by downstream ASSOC/PAT
monotonicity theorem sets. -/
def PairSubsetRel (I : Interpretation Carrier Obj Attr)
    (a b c d : Carrier) : Prop :=
  I.Inherits c a ∧ I.Inherits b d

@[simp] theorem pairSubsetRel_iff
    (I : Interpretation Carrier Obj Attr) (a b c d : Carrier) :
    I.PairSubsetRel a b c d ↔ I.Inherits c a ∧ I.Inherits b d := Iff.rfl

end Interpretation

section FCA

variable {Obj : Type u} {Con : Type v} {Q : Type w} [Preorder Q]

/-- The closed crisp concept associated to a base concept under a gate. This is
the mathlib `Concept` underlying the later abstract view. -/
def crispBaseConcept
    (G : EvidenceGate Q) (M : Obj → Con → Q) (c : Con) :
    CrispConcept G M where
  extent := crispExtent G M c
  intent := _root_.upperPolar (crispRelation G M) (crispExtent G M c)
  upperPolar_extent := rfl
  lowerPolar_intent := by
    change
      _root_.lowerPolar (crispRelation G M)
          (_root_.upperPolar (crispRelation G M)
            (_root_.lowerPolar (crispRelation G M) ({c} : Set Con))) =
        _root_.lowerPolar (crispRelation G M) ({c} : Set Con)
    simp

@[simp] theorem crispBaseConcept_extent
    (G : EvidenceGate Q) (M : Obj → Con → Q) (c : Con) :
    (crispBaseConcept G M c).extent = crispExtent G M c := rfl

@[simp] theorem crispBaseConcept_intent
    (G : EvidenceGate Q) (M : Obj → Con → Q) (c : Con) :
    (crispBaseConcept G M c).intent =
      _root_.upperPolar (crispRelation G M) (crispExtent G M c) := rfl

/-- The extensional WM-PLN view of a base concept as a dual concept. The intent
component is the ordinary FCA upper polar of its gated extent. -/
def ofCrispBaseConcept
    (G : EvidenceGate Q) (M : Obj → Con → Q) (c : Con) :
    DualConcept Obj Con :=
  DualConcept.ofConcept (crispBaseConcept G M c)

theorem self_mem_intent_ofCrispBaseConcept
    (G : EvidenceGate Q) (M : Obj → Con → Q) (c : Con) :
    c ∈ (ofCrispBaseConcept G M c).intent := by
  change c ∈ _root_.upperPolar (crispRelation G M)
    (_root_.lowerPolar (crispRelation G M) ({c} : Set Con))
  exact (_root_.subset_upperPolar_lowerPolar (crispRelation G M) ({c} : Set Con))
    (by simp)

/-- Interpreting each base concept by its gated extent gives exactly the current
crisp extensional inheritance relation on the extent side. -/
theorem extensionalInherits_ofCrispBaseConcept_iff
    (G : EvidenceGate Q) (M : Obj → Con → Q) (c d : Con) :
    DualConcept.ExtensionalInherits
        (ofCrispBaseConcept G M c)
        (ofCrispBaseConcept G M d)
      ↔
    crispExtensionalInherits G M c d := Iff.rfl

theorem crispBaseConcept_le_iff
    (G : EvidenceGate Q) (M : Obj → Con → Q) (c d : Con) :
    crispBaseConcept G M c ≤ crispBaseConcept G M d ↔
      crispExtensionalInherits G M c d := by
  simpa [crispExtensionalInherits] using
    (_root_.Concept.extent_subset_extent_iff
      (c := crispBaseConcept G M c) (d := crispBaseConcept G M d)).symm

theorem inherits_ofCrispBaseConcept_iff
    (G : EvidenceGate Q) (M : Obj → Con → Q) (c d : Con) :
    DualConcept.Inherits
        (ofCrispBaseConcept G M c)
        (ofCrispBaseConcept G M d)
      ↔
    crispExtensionalInherits G M c d := by
  exact (DualConcept.ofConcept_inherits_iff
    (crispBaseConcept G M c) (crispBaseConcept G M d)).trans
      (crispBaseConcept_le_iff G M c d)

/-- The induced abstract interpretation of WM-PLN base concepts. -/
def crispInterpretation
    (G : EvidenceGate Q) (M : Obj → Con → Q) :
    Interpretation Con Obj Con where
  meaning := ofCrispBaseConcept G M

/-- The abstract interpretation recovers the existing crisp extensional
inheritance notion on its extensional projection. -/
theorem crispInterpretation_extensionalInherits_iff
    (G : EvidenceGate Q) (M : Obj → Con → Q) (c d : Con) :
    (crispInterpretation G M).ExtensionalInherits c d ↔
      crispExtensionalInherits G M c d := Iff.rfl

theorem crispInterpretation_inherits_iff
    (G : EvidenceGate Q) (M : Obj → Con → Q) (c d : Con) :
    (crispInterpretation G M).Inherits c d ↔
      crispExtensionalInherits G M c d := by
  exact inherits_ofCrispBaseConcept_iff G M c d

end FCA

end Mettapedia.KR.ConceptGeometry.AbstractInheritance
