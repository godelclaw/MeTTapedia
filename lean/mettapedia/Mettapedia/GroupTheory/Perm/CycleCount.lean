import Mathlib.Data.List.Iterate
import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.SetTheory.Cardinal.Finite

/-!
# Counting the cycles of a permutation by their least points

The cycles of a permutation `σ` of a finite type are the classes of `σ.SameCycle`, fixed
points included.  Mathlib counts them as the parts of the cycle partition `σ.partition`
(nontrivial cycles plus fixed points); `card_quotient_sameCycle` identifies the two counts.

The cycle of `x` is listed by its first `Fintype.card α` iterates
(`mem_iterate_card_iff_sameCycle`).  Given an injective index `idx : α → ℕ`, every cycle
has exactly one point of least index, so testing each point against its own iterates
counts the cycles: `cycleCount idx σ` is that count, and `cycleCount_eq_card_parts`
identifies it with Mathlib's.  It is a plain list-and-finset computation that the kernel
evaluates on a concrete permutation much faster than Mathlib's cycle factorization, so
statements about the cycles of concrete permutations (face counts of maps, for instance)
can be decided by `decide +kernel` through it.

## Main results

* `mem_iterate_card_iff_sameCycle`: the iterates up to the carrier size form the cycle.
* `card_quotient_sameCycle`: `Nat.card (Quotient (SameCycle.setoid σ)) = σ.partition.parts.card`.
* `cycleCount_eq_card_parts`, `cycleCount_eq_card_cycleType_add`.
-/

namespace Equiv.Perm

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- **The first `card α` iterates of `x` are exactly its cycle.** -/
theorem mem_iterate_card_iff_sameCycle (σ : Perm α) (x y : α) :
    y ∈ List.iterate σ x (Fintype.card α) ↔ σ.SameCycle x y := by
  rw [List.mem_iterate]
  constructor
  · rintro ⟨m, -, rfl⟩
    rw [iterate_eq_pow]
    exact (SameCycle.refl σ x).pow_right
  · intro h
    by_cases hx : x ∈ σ.support
    · obtain ⟨i, hi, rfl⟩ := h.exists_pow_eq_of_mem_support hx
      exact ⟨i, lt_of_lt_of_le hi (Finset.card_le_univ _), by rw [iterate_eq_pow]⟩
    · have hfix : σ x = x := notMem_support.mp hx
      obtain rfl := h.eq_of_left hfix
      exact ⟨0, Fintype.card_pos_iff.mpr ⟨x⟩, rfl⟩

section Partition

omit [DecidableEq α] in
/-- A cycle class of `σ` is either a nontrivial cycle factor or a fixed point. -/
private noncomputable def cycleClassify (σ : Perm α) (x : α) :
    σ.cycleFactorsFinset ⊕ Function.fixedPoints σ := by
  classical
  exact if hx : σ x = x then Sum.inr ⟨x, hx⟩
    else Sum.inl ⟨σ.cycleOf x, cycleOf_mem_cycleFactorsFinset_iff.mpr (mem_support.mpr hx)⟩

private theorem cycleClassify_eq_of_sameCycle (σ : Perm α) {x y : α} (h : σ.SameCycle x y) :
    cycleClassify σ x = cycleClassify σ y := by
  unfold cycleClassify
  by_cases hx : σ x = x
  · have hy : σ y = y := h.apply_eq_self_iff.mp hx
    simp only [dif_pos hx, dif_pos hy]
    congr 2
    exact h.eq_of_left hx
  · have hy : σ y ≠ y := fun hy => hx (h.apply_eq_self_iff.mpr hy)
    simp only [dif_neg hx, dif_neg hy]
    congr 2
    exact h.cycleOf_eq

/-- The cycle classes of `σ` correspond to its nontrivial cycle factors and its fixed
points. -/
noncomputable def quotientSameCycleEquiv (σ : Perm α) :
    Quotient (SameCycle.setoid σ) ≃ σ.cycleFactorsFinset ⊕ Function.fixedPoints σ :=
  Equiv.ofBijective
    (Quotient.lift (cycleClassify σ) fun _ _ => cycleClassify_eq_of_sameCycle σ)
    ⟨by
      intro p q hpq
      induction p, q using Quotient.inductionOn₂ with
      | _ x y =>
        apply Quotient.sound
        change cycleClassify σ x = cycleClassify σ y at hpq
        unfold cycleClassify at hpq
        by_cases hx : σ x = x
        · by_cases hy : σ y = y
          · simp only [dif_pos hx, dif_pos hy, Sum.inr.injEq] at hpq
            have hxy : x = y := congrArg Subtype.val hpq
            subst hxy
            exact SameCycle.refl σ x
          · simp [hx, hy] at hpq
        · by_cases hy : σ y = y
          · simp [hx, hy] at hpq
          · simp only [dif_neg hx, dif_neg hy, Sum.inl.injEq, Subtype.mk.injEq] at hpq
            exact (sameCycle_iff_cycleOf_eq_of_mem_support (mem_support.mpr hx)
              (mem_support.mpr hy)).mpr hpq,
     by
      rintro (c | ⟨x, hx⟩)
      · obtain ⟨x, hxc⟩ := (mem_cycleFactorsFinset_iff.mp c.2).1.nonempty_support
        have hxσ : x ∈ σ.support := mem_cycleFactorsFinset_support_le c.2 hxc
        refine ⟨Quotient.mk _ x, ?_⟩
        change cycleClassify σ x = _
        unfold cycleClassify
        rw [dif_neg (mem_support.mp hxσ)]
        congr 2
        exact ((eq_cycleOf_of_mem_cycleFactorsFinset_iff σ c c.2 x).mpr hxc).symm
      · refine ⟨Quotient.mk _ x, ?_⟩
        change cycleClassify σ x = _
        unfold cycleClassify
        rw [dif_pos (Function.mem_fixedPoints_iff.mp hx)]⟩

/-- **The cycle classes of a permutation, fixed points included, are counted by the parts
of its cycle partition.** -/
theorem card_quotient_sameCycle (σ : Perm α) :
    Nat.card (Quotient (SameCycle.setoid σ)) = σ.partition.parts.card := by
  rw [Nat.card_congr (quotientSameCycleEquiv σ), Nat.card_sum, Nat.card_eq_fintype_card,
    Nat.card_eq_fintype_card, Fintype.card_coe, σ.card_fixedPoints, σ.sum_cycleType,
    parts_partition, Multiset.card_add, Multiset.card_replicate, cycleType_def,
    Multiset.card_map]
  rfl

end Partition

section Count

variable (idx : α → ℕ) (σ : Perm α)

/-- `x` has the least index among its first `card α` iterates, that is, on its cycle. -/
def isCycleMin (x : α) : Bool :=
  (List.iterate σ x (Fintype.card α)).all fun y => decide (idx x ≤ idx y)

/-- The number of points of least index on their cycle. -/
def cycleCount : ℕ :=
  (Finset.univ.filter fun x => isCycleMin idx σ x = true).card

variable {idx σ}

theorem isCycleMin_iff {x : α} :
    isCycleMin idx σ x = true ↔ ∀ y, σ.SameCycle x y → idx x ≤ idx y := by
  rw [isCycleMin, List.all_eq_true]
  simp only [decide_eq_true_eq, mem_iterate_card_iff_sameCycle]

/-- With an injective index, the cycle minima represent the cycle classes bijectively. -/
theorem cycleCount_eq_card_quotient (hidx : Function.Injective idx) :
    cycleCount idx σ = Nat.card (Quotient (SameCycle.setoid σ)) := by
  rw [cycleCount, ← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
  refine Nat.card_congr (Equiv.ofBijective (fun x => Quotient.mk (SameCycle.setoid σ) x.1)
    ⟨?_, ?_⟩)
  · rintro ⟨x, hx⟩ ⟨y, hy⟩ h
    have hxy : σ.SameCycle x y := Quotient.exact h
    exact Subtype.ext (hidx (le_antisymm (isCycleMin_iff.mp hx y hxy)
      (isCycleMin_iff.mp hy x hxy.symm)))
  · intro q
    induction q using Quotient.inductionOn with
    | h z =>
      classical
      obtain ⟨x, hxz, hxmin⟩ := (Finset.univ.filter fun w => σ.SameCycle z w).exists_min_image
        idx ⟨z, Finset.mem_filter.mpr ⟨Finset.mem_univ z, SameCycle.refl σ z⟩⟩
      have hzx : σ.SameCycle z x := (Finset.mem_filter.mp hxz).2
      refine ⟨⟨x, isCycleMin_iff.mpr fun y hxy => hxmin y ?_⟩, Quotient.sound hzx.symm⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ y, hzx.trans hxy⟩

/-- **The computed count is Mathlib's number of cycles**, fixed points included. -/
theorem cycleCount_eq_card_parts (hidx : Function.Injective idx) :
    cycleCount idx σ = σ.partition.parts.card := by
  rw [cycleCount_eq_card_quotient hidx, card_quotient_sameCycle]

/-- The computed count is the number of nontrivial cycles plus the number of fixed
points. -/
theorem cycleCount_eq_card_cycleType_add (hidx : Function.Injective idx) :
    cycleCount idx σ = σ.cycleType.card + (Fintype.card α - σ.support.card) := by
  rw [cycleCount_eq_card_parts hidx, parts_partition, Multiset.card_add,
    Multiset.card_replicate]

end Count

end Equiv.Perm
