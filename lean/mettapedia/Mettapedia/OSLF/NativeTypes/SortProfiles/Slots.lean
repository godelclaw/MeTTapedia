import Mettapedia.OSLF.NativeTypes.Generation.Occurrences.Typing
import Mettapedia.OSLF.NativeTypes.Structural.Formers
import Mettapedia.OSLF.Framework.ModalHypercube

open Mettapedia.OSLF.Framework

/-!
# Source-derived local sort profiles

The local cube classifies input and output sorts of a generated former. It
does not encode an operation truth table. All modal families are generated
from actual one-hole occurrences; all structural families are generated from
actual constructor declarations. The global profile is their disjoint union.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.SortProfiles.Slots

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.Framework.ModalHypercube (HSort)
open Mettapedia.OSLF.NativeTypes.Generation.Occurrences

inductive Origin where
  | modal (declaration : Nat) (position : List Nat)
  | structural (declaration : Nat)
  deriving DecidableEq, Repr

structure Family where
  origin : Origin
  inputs : List (String × Option TypeExpr)
  outputs : List TypeExpr
  deriving DecidableEq, Repr

def modalFamily (language : LanguageDef) (site : Site) : Family :=
  ⟨.modal site.declaration site.position,
    site.relyNames.map (fun name => (name, ruleFree site.rule name)),
    sourceCandidates language site.rule⟩

def structuralFamily (entry : GrammarRule × Nat) : Family :=
  ⟨.structural entry.2,
    entry.1.params.map (fun parameter =>
      (parameter.bodyName, some parameter.typeExpr)), [.base entry.1.category]⟩

def families (language : LanguageDef) : List Family :=
  (Mettapedia.OSLF.NativeTypes.Generation.Occurrences.generate language).map (modalFamily language) ++
    language.terms.zipIdx.map structuralFamily

/-- One slot for each input and one output, computed from the declaration. -/
def Family.slotCount (family : Family) : Nat := family.inputs.length + 1

def globalCount (language : LanguageDef) : Nat :=
  ((families language).map Family.slotCount).sum

abbrev GlobalVertex (language : LanguageDef) := Fin (globalCount language) → HSort

def rawCube (family : Family) : Finset (Fin family.slotCount → HSort) := Finset.univ

theorem modal_slot_count (language : LanguageDef) (site : Site) :
    (modalFamily language site).slotCount = site.relyNames.length + 1 := by
  simp [modalFamily, Family.slotCount]

theorem structural_slot_count (entry : GrammarRule × Nat) :
    (structuralFamily entry).slotCount = entry.1.params.length + 1 := by
  simp [structuralFamily, Family.slotCount]

theorem family_origin_iff (language : LanguageDef) (family : Family) :
    family ∈ families language ↔
      (∃ site ∈ Mettapedia.OSLF.NativeTypes.Generation.Occurrences.generate language, family = modalFamily language site) ∨
      ∃ entry ∈ language.terms.zipIdx, family = structuralFamily entry := by
  simp only [families, List.mem_append, List.mem_map]
  constructor
  · rintro (⟨site, member, equal⟩ | ⟨entry, member, equal⟩)
    · exact Or.inl ⟨site, member, equal.symm⟩
    · exact Or.inr ⟨entry, member, equal.symm⟩
  · rintro (⟨site, member, equal⟩ | ⟨entry, member, equal⟩)
    · exact Or.inl ⟨site, member, equal.symm⟩
    · exact Or.inr ⟨entry, member, equal.symm⟩

theorem modal_family_generated {language : LanguageDef} {site : Site}
    (member : site ∈ Mettapedia.OSLF.NativeTypes.Generation.Occurrences.generate language) :
    modalFamily language site ∈ families language :=
  (family_origin_iff _ _).mpr (Or.inl ⟨site, member, rfl⟩)

theorem structural_family_generated (language : LanguageDef) (entry : GrammarRule × Nat)
    (member : entry ∈ language.terms.zipIdx) :
    structuralFamily entry ∈ families language :=
  (family_origin_iff _ _).mpr (Or.inr ⟨entry, member, rfl⟩)

/-- The geometry itself is unaffected by equation choices; admission to it
is separately checked by the equational-center algorithm. -/
theorem equation_independent_slots (language : LanguageDef) (equations : List Equation) :
    families {language with equations := equations} = families language := rfl

theorem rawCube_card (family : Family) : (rawCube family).card = 2 ^ family.slotCount := by
  simp only [rawCube, Finset.card_univ, Fintype.card_fun, HSort.card, Fintype.card_fin]

/-- Each non-origin vertex is the direction obtained by boxing a nonempty
subset of the actual local slot list. -/
def axes (family : Family) : Finset (Fin family.slotCount → HSort) :=
  (rawCube family).erase (fun _ => .star)

theorem axes_card (family : Family) : (axes family).card = 2 ^ family.slotCount - 1 := by
  rw [axes, Finset.card_erase_of_mem (show (fun _ => HSort.star) ∈ rawCube family from
    Finset.mem_univ _), rawCube_card]

/-- The first slot is fixed, while every other input/output slot remains free.
The equivalence identifies the actual corners, rather than just their count. -/
def fixedFirstEquiv (remaining : Nat) :
    {vertex : Fin (remaining + 1) → HSort // vertex 0 = .star} ≃
      (Fin remaining → HSort) where
  toFun vertex := fun position => vertex.val position.succ
  invFun rest := ⟨Fin.cases .star rest, rfl⟩
  left_inv vertex := by
    apply Subtype.ext
    funext position
    refine Fin.cases ?_ (fun index => ?_) position
    · exact vertex.property.symm
    · rfl
  right_inv _ := rfl

def fixedFirstFace (remaining : Nat) : Finset (Fin (remaining + 1) → HSort) :=
  Finset.univ.filter fun vertex => vertex 0 = .star

theorem fixedFirstFace_card (remaining : Nat) :
    (fixedFirstFace remaining).card = 2 ^ remaining := by
  have equivalent := Fintype.card_congr (fixedFirstEquiv remaining)
  rw [Fintype.card_fun, HSort.card, Fintype.card_fin] at equivalent
  simpa only [fixedFirstFace, Fintype.card_subtype, Finset.card_univ,
    Finset.filter_mem_eq_inter, Finset.inter_self] using equivalent

end Mettapedia.OSLF.NativeTypes.SortProfiles.Slots
