import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Card

/-!
# Honest intersections of finite quorums

For a fixed validator set of size `n ≥ 3f + 1`, use `n - f` distinct
signers. This threshold works also when `n` is larger than `3f + 1`.
Intersection is a safety fact; availability of enough honest validators
does not imply agreement on a proposal or delivery of their messages.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Contracts.Quorums

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem honest_intersection (faulty first second : Finset V) (f : Nat)
    (resilience : 3 * f + 1 ≤ Fintype.card V) (faultBound : faulty.card ≤ f)
    (firstSize : Fintype.card V - f ≤ first.card)
    (secondSize : Fintype.card V - f ≤ second.card) :
    ∃ v ∈ first, v ∈ second ∧ v ∉ faulty := by
  have unionBound := Finset.card_le_univ (first ∪ second)
  have count := Finset.card_union_add_card_inter first second
  have overlap : f < (first ∩ second).card := by omega
  by_contra missing
  have contained : first ∩ second ⊆ faulty := by
    intro v hv
    by_contra honest
    exact missing ⟨v, (Finset.mem_inter.mp hv).1, (Finset.mem_inter.mp hv).2, honest⟩
  have := Finset.card_le_card contained
  omega

theorem honest_available (faulty : Finset V) (f : Nat) (faultBound : faulty.card ≤ f) :
    Fintype.card V - f ≤ (Finset.univ \ faulty).card ∧
      Disjoint (Finset.univ \ faulty) faulty := by
  constructor
  · rw [Finset.card_sdiff_of_subset (Finset.subset_univ faulty), Finset.card_univ]
    omega
  · exact Finset.sdiff_disjoint

theorem four_one (faulty first second : Finset (Fin 4))
    (bad : faulty.card ≤ 1) (a : 3 ≤ first.card) (b : 3 ≤ second.card) :
    ∃ v ∈ first, v ∈ second ∧ v ∉ faulty :=
  honest_intersection faulty first second 1 (by decide) bad a b

/-- Two-of-four certificates may intersect only at the equivocating signer. -/
theorem insufficient_threshold :
    let faulty : Finset (Fin 4) := {0}
    let first : Finset (Fin 4) := {0, 1}
    let second : Finset (Fin 4) := {0, 2}
    faulty.card = 1 ∧ first.card = 2 ∧ second.card = 2 ∧ first ∩ second ⊆ faulty := by
  decide

end Mettapedia.GSLT.Contracts.Quorums
