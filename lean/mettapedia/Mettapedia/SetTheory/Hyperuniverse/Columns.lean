import Mettapedia.SetTheory.Hyperuniverse.Finite
import Mettapedia.TypeTheory.MaterialSets.Hypersets.AntiFoundation
import Mathlib.SetTheory.ZFC.Basic

/-!
# The other two columns

The carrier of this space has a universal set and a finite Quine atom. A
membership with separation has no set of its whole carrier, and neither does
`HSet`. The Russell class, the class of sets that are not members of
themselves, is not a set of hypersets and is not a member of any `ZFSet`.
A finite presentation of the Quine atom is a self-member, so finite
presentations have no membership-preserving map into an irreflexive
membership, including the members of a `ZFSet`.
-/

set_option autoImplicit false

namespace Mettapedia.SetTheory.Hyperuniverse

open Set Topology TopologicalSpace
open Mettapedia.TypeTheory.MaterialSets.Hypersets

universe u

/-- No hyperset collects exactly the hypersets that are not members of themselves. -/
theorem hset_not_russell_set :
    ¬ ∃ s : HSet.{u}, ∀ x : HSet.{u}, x ∈ s ↔ x ∉ x := by
  rintro ⟨s, hs⟩
  have absent : s ∉ s := fun present => (hs s).mp present present
  exact absent ((hs s).mpr absent)

/-- No member of a `ZFSet` collects exactly the members that are not members of themselves. -/
theorem elements_not_russell_set {U : ZFSet.{u}} :
    ¬ ∃ s : {x : ZFSet.{u} // x ∈ U},
      ∀ x : {x : ZFSet.{u} // x ∈ U}, x.1 ∈ s.1 ↔ x.1 ∉ x.1 := by
  rintro ⟨s, hs⟩
  have absent : s.1 ∉ s.1 := fun present => (hs s).mp present present
  exact absent ((hs s).mpr absent)

/-- The Quine atom has a one-node presentation, and it is a member of itself. -/
theorem finitePresented_quineAtom :
    ∃ x : FinitePresented, x.1 = HSet.quineAtom.{0} ∧ x.1 ∈ x.1 := by
  have hfin : Finite HSet.loop.{0}.Node := by
    change Finite PUnit.{1}
    infer_instance
  exact ⟨⟨HSet.quineAtom, ⟨HSet.loop, HSet.mk_loop, hfin⟩⟩, rfl, HSet.quineAtom_mem_self⟩

/-- A self-member blocks a membership-preserving map into an irreflexive membership. -/
theorem not_finitePresented_memHom_irreflexive {B : Type} {memB : B → B → Prop}
    (irreflexive : ∀ b, ¬ memB b b) :
    ¬ ∃ f : FinitePresented → B, ∀ x y, x.1 ∈ y.1 → memB (f x) (f y) := by
  rintro ⟨f, preserves⟩
  obtain ⟨x, hx⟩ := finitePresented_quineAtom
  exact irreflexive (f x) (preserves x x hx.2)

/-- Finite presentations do not keep membership into the members of a `ZFSet`. -/
theorem not_finitePresented_embed_elements {U : ZFSet.{0}} :
    ¬ ∃ f : FinitePresented → {x : ZFSet.{0} // x ∈ U},
      ∀ a b, a.1 ∈ b.1 ↔ (f a).1 ∈ (f b).1 := by
  rintro ⟨f, preserves⟩
  obtain ⟨x, hx⟩ := finitePresented_quineAtom
  exact ZFSet.mem_irrefl (f x).1 ((preserves x x).mp hx.2)

/-- Finite presentations do not keep membership into `ZFSet`. -/
theorem not_finitePresented_embed_zfset :
    ¬ ∃ f : FinitePresented → ZFSet.{0}, ∀ a b, a.1 ∈ b.1 ↔ f a ∈ f b := by
  rintro ⟨f, preserves⟩
  obtain ⟨x, hx⟩ := finitePresented_quineAtom
  exact ZFSet.mem_irrefl (f x) ((preserves x x).mp hx.2)

/-- No topology on `ZFSet` makes a membership-preserving finite-presentation image dense. -/
theorem not_finitePresented_dense_zfset :
    ¬ ∃ (t : TopologicalSpace ZFSet.{0}) (f : FinitePresented → ZFSet.{0}),
      (∀ a b, a.1 ∈ b.1 ↔ f a ∈ f b) ∧ @Dense ZFSet.{0} t (Set.range f) := by
  rintro ⟨_, f, preserves, _⟩
  exact not_finitePresented_embed_zfset ⟨f, preserves⟩

end Mettapedia.SetTheory.Hyperuniverse
