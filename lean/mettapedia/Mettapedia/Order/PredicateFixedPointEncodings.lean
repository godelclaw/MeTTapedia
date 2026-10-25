import Mathlib.Order.FixedPoints
import Mathlib.Data.Set.Lattice

/-!
# Quantified predicate encodings of least and greatest fixed points

The least predicate belongs to every pre-fixed predicate. The greatest
predicate belongs to some post-fixed predicate. These formulas are formed
independently of the lattice fixed-point construction and compared with
it by their induction and coinduction properties.

An order isomorphism that intertwines the operators transports their fixed
points. The transport law below works on arbitrary complete lattices; the
quantified predicate encodings are its powerset instance.
-/

set_option autoImplicit false

namespace Mettapedia.Order.FixedPointTransport

variable {α β : Type*} [CompleteLattice α] [CompleteLattice β]
  (comparison : α ≃o β) (source : α →o α) (target : β →o β)
  (intertwines : ∀ x, comparison (source x) = target (comparison x))

include intertwines

/-- Conjugate monotone operators have corresponding least fixed points. -/
theorem lfp_comparison : comparison source.lfp = target.lfp := by
  let forward := comparison.toOrderEmbedding.toOrderHom
  let pulled := source.comp comparison.symm.toOrderEmbedding.toOrderHom
  have left : pulled.comp forward = source := by ext x; simp [pulled, forward]
  have right : forward.comp pulled = target := by
    ext x
    simpa [pulled, forward] using intertwines (comparison.symm x)
  simpa [left, right, forward] using forward.map_lfp_comp pulled

/-- Greatest-point transport is least-point transport in the order dual. -/
theorem gfp_comparison : comparison source.gfp = target.gfp :=
  lfp_comparison comparison.dual source.dual target.dual intertwines

end Mettapedia.Order.FixedPointTransport

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
  simp only [least_eq_lfp, OrderHom.map_lfp]

theorem greatest_unfold (transformer : Set State →o Set State) :
    transformer (greatest transformer) = greatest transformer := by
  simp only [greatest_eq_gfp, OrderHom.map_gfp]

theorem least_is_least_fixed (transformer : Set State →o Set State)
    (predicate : Set State) (fixed : transformer predicate = predicate) :
    least transformer ⊆ predicate := least_induction transformer predicate fixed.le

theorem greatest_is_greatest_fixed (transformer : Set State →o Set State)
    (predicate : Set State) (fixed : transformer predicate = predicate) :
    predicate ⊆ greatest transformer := greatest_coinduction transformer predicate fixed.symm.le

theorem least_mono {first second : Set State →o Set State} (compared : first ≤ second) :
    least first ⊆ least second := by
  simpa only [least_eq_lfp] using OrderHom.lfp.monotone compared

theorem greatest_mono {first second : Set State →o Set State} (compared : first ≤ second) :
    greatest first ⊆ greatest second := by
  simpa only [greatest_eq_gfp] using OrderHom.gfp.monotone compared

section Comparison

variable {Other : Type v} (comparison : Set State ≃o Set Other)
  (source : Set State →o Set State) (target : Set Other →o Set Other)
  (intertwines : ∀ predicate, comparison (source predicate) = target (comparison predicate))

include intertwines

theorem least_comparison : comparison (least source) = least target := by
  simpa only [least_eq_lfp] using
    FixedPointTransport.lfp_comparison comparison source target intertwines

theorem greatest_comparison : comparison (greatest source) = greatest target := by
  simpa only [greatest_eq_gfp] using
    FixedPointTransport.gfp_comparison comparison source target intertwines

end Comparison

end Mettapedia.Order.PredicateFixedPointEncodings
