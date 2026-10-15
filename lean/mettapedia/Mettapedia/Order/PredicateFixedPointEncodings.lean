import Mathlib.Order.FixedPoints
import Mathlib.Data.Set.Lattice

/-!
# Quantified predicate encodings of least and greatest fixed points

The least predicate belongs to every pre-fixed predicate. The greatest
predicate belongs to some post-fixed predicate. These formulas are formed
independently of the lattice fixed-point construction and compared with
it by their induction and coinduction properties.
-/

set_option autoImplicit false

namespace Mettapedia.Order.PredicateFixedPointEncodings

universe u v

variable {State : Type u}

def least (transformer : Set State → Set State) : Set State :=
  {state | ∀ predicate, transformer predicate ⊆ predicate → state ∈ predicate}

def greatest (transformer : Set State → Set State) : Set State :=
  {state | ∃ predicate, predicate ⊆ transformer predicate ∧ state ∈ predicate}

theorem least_induction (transformer : Set State → Set State) (predicate : Set State)
    (closed : transformer predicate ⊆ predicate) : least transformer ⊆ predicate :=
  fun _ member => member predicate closed

theorem greatest_coinduction (transformer : Set State → Set State) (predicate : Set State)
    (invariant : predicate ⊆ transformer predicate) : predicate ⊆ greatest transformer :=
  fun _ member => ⟨predicate, invariant, member⟩

theorem least_eq_lfp (transformer : Set State →o Set State) :
    least transformer = transformer.lfp := by
  apply Set.Subset.antisymm
  · exact least_induction transformer transformer.lfp transformer.map_lfp.le
  · intro state member predicate closed
    exact transformer.lfp_le closed member

theorem greatest_eq_gfp (transformer : Set State →o Set State) :
    greatest transformer = transformer.gfp := by
  apply Set.Subset.antisymm
  · rintro state ⟨predicate, invariant, member⟩
    exact transformer.le_gfp invariant member
  · exact greatest_coinduction transformer transformer.gfp transformer.map_gfp.symm.le

theorem least_unfold (transformer : Set State →o Set State) :
    transformer (least transformer) = least transformer := by
  rw [least_eq_lfp]
  exact transformer.map_lfp

theorem greatest_unfold (transformer : Set State →o Set State) :
    transformer (greatest transformer) = greatest transformer := by
  rw [greatest_eq_gfp]
  exact transformer.map_gfp

theorem least_is_least_fixed (transformer : Set State →o Set State)
    (predicate : Set State) (fixed : transformer predicate = predicate) :
    least transformer ⊆ predicate := least_induction transformer predicate fixed.le

theorem greatest_is_greatest_fixed (transformer : Set State →o Set State)
    (predicate : Set State) (fixed : transformer predicate = predicate) :
    predicate ⊆ greatest transformer := greatest_coinduction transformer predicate fixed.symm.le

theorem least_mono {first second : Set State →o Set State} (compared : first ≤ second) :
    least first ⊆ least second := by
  rw [least_eq_lfp, least_eq_lfp]
  exact OrderHom.lfp.monotone compared

theorem greatest_mono {first second : Set State →o Set State} (compared : first ≤ second) :
    greatest first ⊆ greatest second := by
  rw [greatest_eq_gfp, greatest_eq_gfp]
  exact OrderHom.gfp.monotone compared

section Comparison

variable {Other : Type v} (comparison : Set State ≃o Set Other)
  (source : Set State →o Set State) (target : Set Other →o Set Other)
  (intertwines : ∀ predicate, comparison (source predicate) = target (comparison predicate))

include intertwines

theorem least_comparison : comparison (least source) = least target := by
  have sourceFixed := least_unfold source
  have targetFixed := least_unfold target
  apply le_antisymm
  · have pulled : source (comparison.symm (least target)) ⊆
        comparison.symm (least target) := by
      apply comparison.le_iff_le.mp
      simpa only [intertwines, comparison.apply_symm_apply] using targetFixed.le
    exact (comparison.monotone
      (least_induction source (comparison.symm (least target)) pulled)).trans_eq
        (comparison.apply_symm_apply (least target))
  · have pushed : target (comparison (least source)) ⊆ comparison (least source) := by
      rw [← intertwines, sourceFixed]
    exact least_induction target (comparison (least source)) pushed

theorem greatest_comparison : comparison (greatest source) = greatest target := by
  have sourceFixed := greatest_unfold source
  have targetFixed := greatest_unfold target
  apply le_antisymm
  · have pushed : comparison (greatest source) ⊆ target (comparison (greatest source)) := by
      rw [← intertwines, sourceFixed]
    exact greatest_coinduction target (comparison (greatest source)) pushed
  · have pulled : comparison.symm (greatest target) ⊆
        source (comparison.symm (greatest target)) := by
      apply comparison.le_iff_le.mp
      simpa only [intertwines, comparison.apply_symm_apply] using targetFixed.symm.le
    exact (comparison.apply_symm_apply (greatest target)).symm.le.trans
      (comparison.monotone
        (greatest_coinduction source (comparison.symm (greatest target)) pulled))

end Comparison

end Mettapedia.Order.PredicateFixedPointEncodings
