import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Finset.Lattice.Lemmas
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Mettapedia.ProbabilityTheory.Structures.Valuation.Basic
import Mettapedia.ProbabilityTheory.Common.Lattice
import Mettapedia.ProbabilityTheory.Common.LatticeValuation
import Mettapedia.ProbabilityTheory.Hypercube.NovelTheories

/-!
# Dempster–Shafer masses and their lattice interpretation

A mass assigns weight to exact focal sets; belief accumulates all masses below
an event and plausibility accumulates those meeting it. The common incidence
transform supplies unique reconstruction. Positivity is the additional semantic
condition: normalized monotone capacities alone need not have nonnegative mass.

The Boolean-lattice realization preserves these queries. General belief is
superadditive on disjoint events, and need not be additive.
-/

namespace Mettapedia.ProbabilityTheory.BeliefFunctions

open Finset BigOperators

variable {Ω : Type*} [DecidableEq Ω] [Fintype Ω]

structure MassFunction (Ω : Type*) [DecidableEq Ω] [Fintype Ω] where

  m : Finset Ω → ℝ

  m_empty : m ∅ = 0

  m_nonneg : ∀ A, 0 ≤ m A

  m_sum_one : ∑ A ∈ Finset.univ.powerset, m A = 1

namespace MassFunction

variable (m : MassFunction Ω)

def isFocal (A : Finset Ω) : Prop := m.m A > 0

def focalElements : Set (Finset Ω) := { A | m.isFocal A }

theorem m_le_one (A : Finset Ω) : m.m A ≤ 1 := by
  have hA : A ∈ Finset.univ.powerset := Finset.mem_powerset.mpr (Finset.subset_univ A)
  have h := m.m_sum_one
  calc m.m A ≤ ∑ B ∈ Finset.univ.powerset, m.m B := by
        apply Finset.single_le_sum (fun B _ => m.m_nonneg B) hA
    _ = 1 := h

/-- Unit mass on one nonempty focal set. -/
noncomputable def singleFocal (A : Finset Ω) (nonempty : A.Nonempty) : MassFunction Ω where
  m B := if B = A then 1 else 0
  m_empty := by simp [nonempty.ne_empty.symm]
  m_nonneg B := by split_ifs <;> norm_num
  m_sum_one := by simp

end MassFunction

def belief (m : MassFunction Ω) (A : Finset Ω) : ℝ :=
  ∑ B ∈ A.powerset, m.m B

def plausibility (m : MassFunction Ω) (A : Finset Ω) : ℝ :=
  ∑ B ∈ Finset.univ.powerset.filter (fun B => (B ∩ A).Nonempty), m.m B

namespace Belief

variable (m : MassFunction Ω)

theorem empty : belief m ∅ = 0 := by
  simp only [belief, Finset.powerset_empty, Finset.sum_singleton, m.m_empty]

theorem univ : belief m Finset.univ = 1 := by

  unfold belief
  rw [Finset.powerset_univ]
  exact m.m_sum_one

theorem nonneg (A : Finset Ω) : 0 ≤ belief m A := by
  apply Finset.sum_nonneg
  intro B _
  exact m.m_nonneg B

theorem le_one (A : Finset Ω) : belief m A ≤ 1 := by

  unfold belief
  calc ∑ B ∈ A.powerset, m.m B
      ≤ ∑ B ∈ Finset.univ.powerset, m.m B := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro B hB
            exact Finset.mem_powerset.mpr (Finset.subset_univ B)
          · intro B _ _
            exact m.m_nonneg B
    _ = 1 := m.m_sum_one

theorem mono {A B : Finset Ω} (h : A ⊆ B) : belief m A ≤ belief m B := by

  unfold belief
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro C hC
    exact Finset.mem_powerset.mpr (Finset.Subset.trans (Finset.mem_powerset.mp hC) h)
  · intro C _ _
    exact m.m_nonneg C

end Belief

/-- A single focal set contributes exactly when it lies below the queried event. -/
theorem belief_singleFocal (A : Finset Ω) (nonempty : A.Nonempty) (B : Finset Ω) :
    belief (MassFunction.singleFocal A nonempty) B = if A ⊆ B then 1 else 0 := by
  simp [belief, MassFunction.singleFocal]

namespace Plausibility

variable (m : MassFunction Ω)

theorem empty : plausibility m ∅ = 0 := by
  simp only [plausibility, Finset.inter_empty, Finset.not_nonempty_empty,
             Finset.filter_false, Finset.sum_empty]

theorem nonneg (A : Finset Ω) : 0 ≤ plausibility m A := by
  apply Finset.sum_nonneg
  intro B _
  exact m.m_nonneg B

theorem le_one (A : Finset Ω) : plausibility m A ≤ 1 := by

  unfold plausibility
  calc ∑ B ∈ Finset.univ.powerset.filter (fun B => (B ∩ A).Nonempty), m.m B
      ≤ ∑ B ∈ Finset.univ.powerset, m.m B := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · exact Finset.filter_subset _ _
          · intro B _ _
            exact m.m_nonneg B
    _ = 1 := m.m_sum_one

end Plausibility

theorem belief_le_plausibility (m : MassFunction Ω) (A : Finset Ω) :
    belief m A ≤ plausibility m A := by

  unfold belief plausibility

  have h_split : A.powerset = {∅} ∪ A.powerset.filter (fun B => B.Nonempty) := by
    ext B
    simp only [Finset.mem_union, Finset.mem_singleton, Finset.mem_filter]
    constructor
    · intro hB
      by_cases hBe : B = ∅
      · left; exact hBe
      · right; exact ⟨hB, Finset.nonempty_iff_ne_empty.mpr hBe⟩
    · intro h
      cases h with
      | inl h => simp [h]
      | inr h => exact h.1
  rw [h_split, Finset.sum_union]
  · simp only [Finset.sum_singleton, m.m_empty, zero_add]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro B hB
      rw [Finset.mem_filter] at hB ⊢
      constructor
      · exact Finset.mem_powerset.mpr (Finset.subset_univ B)
      · have hBA : B ⊆ A := Finset.mem_powerset.mp hB.1
        rw [Finset.inter_eq_left.mpr hBA]
        exact hB.2
    · intro B _ _
      exact m.m_nonneg B
  · rw [Finset.disjoint_singleton_left]
    simp only [Finset.mem_filter, Finset.not_nonempty_empty, and_false, not_false_eq_true]

def complement (A : Finset Ω) : Finset Ω := Finset.univ \ A

theorem plausibility_eq_one_sub_belief_compl (m : MassFunction Ω) (A : Finset Ω) :
    plausibility m A = 1 - belief m (complement A) := by
  have subsets : (complement A).powerset =
      Finset.univ.powerset.filter (fun B => ¬(B ∩ A).Nonempty) := by
    ext B
    simp [complement, Finset.subset_sdiff, Finset.not_nonempty_iff_eq_empty,
      Finset.disjoint_iff_inter_eq_empty]
  have total : plausibility m A + belief m (complement A) = 1 := by
    unfold plausibility belief
    rw [subsets, Finset.sum_filter_add_sum_filter_not]
    exact m.m_sum_one
  linarith

def toLowerProbability (m : MassFunction Ω) : Finset Ω → ℝ := belief m

def toUpperProbability (m : MassFunction Ω) : Finset Ω → ℝ := plausibility m

def imprecisionGap (m : MassFunction Ω) (A : Finset Ω) : ℝ :=
  plausibility m A - belief m A

theorem imprecisionGap_nonneg (m : MassFunction Ω) (A : Finset Ω) :
    0 ≤ imprecisionGap m A := by
  simp only [imprecisionGap]
  exact sub_nonneg.mpr (belief_le_plausibility m A)

def MassFunction.isBayesian (m : MassFunction Ω) : Prop :=
  ∀ A : Finset Ω, m.m A ≠ 0 → A.card = 1

def MassFunction.isVacuous (m : MassFunction Ω) : Prop :=
  m.m Finset.univ = 1 ∧ ∀ A : Finset Ω, A ≠ Finset.univ → m.m A = 0

omit [Fintype Ω] in
private lemma singleton_subset_iff_inter_nonempty {A : Finset Ω} {x : Ω} :
    {x} ⊆ A ↔ ({x} ∩ A).Nonempty := by
  rw [Finset.singleton_subset_iff]
  constructor
  · intro hxA
    rw [Finset.singleton_inter_of_mem hxA]
    exact Finset.singleton_nonempty x
  · intro h
    by_contra hxnA
    rw [Finset.singleton_inter_of_notMem hxnA] at h
    exact Finset.not_nonempty_empty h

theorem bayesian_precise (m : MassFunction Ω) (hb : m.isBayesian) (A : Finset Ω) :
    belief m A = plausibility m A := by

  apply le_antisymm
  · exact belief_le_plausibility m A
  ·

    unfold belief plausibility

    have h_bel : ∑ B ∈ A.powerset, m.m B =
        ∑ B ∈ A.powerset.filter (fun B => m.m B ≠ 0), m.m B := by
      symm
      apply Finset.sum_filter_ne_zero
    have h_pl : ∑ B ∈ Finset.univ.powerset.filter (fun B => (B ∩ A).Nonempty), m.m B =
        ∑ B ∈ (Finset.univ.powerset.filter (fun B => (B ∩ A).Nonempty)).filter
            (fun B => m.m B ≠ 0), m.m B := by
      symm
      apply Finset.sum_filter_ne_zero
    rw [h_bel, h_pl]

    have h_eq : (Finset.univ.powerset.filter (fun B => (B ∩ A).Nonempty)).filter
        (fun B => m.m B ≠ 0) = A.powerset.filter (fun B => m.m B ≠ 0) := by
      ext B
      simp only [Finset.mem_filter, Finset.mem_powerset, Finset.subset_univ, true_and]
      constructor
      · intro ⟨hinter, hne⟩
        constructor
        ·
          have hcard := hb B hne
          rw [Finset.card_eq_one] at hcard
          obtain ⟨x, hBx⟩ := hcard
          rw [hBx]
          rw [hBx] at hinter
          exact singleton_subset_iff_inter_nonempty.mpr hinter
        · exact hne
      · intro ⟨hBA, hne⟩
        constructor
        ·
          have hcard := hb B hne
          rw [Finset.card_eq_one] at hcard
          obtain ⟨x, hBx⟩ := hcard
          rw [hBx] at hBA ⊢
          exact singleton_subset_iff_inter_nonempty.mp hBA
        · exact hne
    rw [h_eq]

noncomputable def conflict (m₁ m₂ : MassFunction Ω) : ℝ :=
  ∑ p ∈ (Finset.univ.powerset ×ˢ Finset.univ.powerset).filter
        (fun p => (p.1 ∩ p.2) = ∅),
    m₁.m p.1 * m₂.m p.2

def areCombinableDS (m₁ m₂ : MassFunction Ω) : Prop := conflict m₁ m₂ < 1

noncomputable def unnormalizedCombine (m₁ m₂ : MassFunction Ω) (C : Finset Ω) : ℝ :=
  ∑ p ∈ (Finset.univ.powerset ×ˢ Finset.univ.powerset).filter
        (fun p => p.1 ∩ p.2 = C),
    m₁.m p.1 * m₂.m p.2

noncomputable def dempsterCombineValue (m₁ m₂ : MassFunction Ω)
    (_hcomb : areCombinableDS m₁ m₂) (C : Finset Ω) : ℝ :=
  if C = ∅ then 0
  else (1 - conflict m₁ m₂)⁻¹ * unnormalizedCombine m₁ m₂ C

section CommonFramework

open Mettapedia.ProbabilityTheory.Common

variable (m : MassFunction Ω)

def beliefAsMonotone : MonotoneValuation (Finset Ω) where
  val := belief m
  mono := fun _ _ h => Belief.mono m h

def beliefAsNormalized : NormalizedValuation (Finset Ω) where
  val := belief m
  mono := fun _ _ h => Belief.mono m h
  val_bot := Belief.empty m
  val_top := Belief.univ m

def toImpreciseValuation : ImpreciseValuation (Finset Ω) where
  lower := beliefAsNormalized m
  upper := plausibility m
  lower_le_upper := belief_le_plausibility m
  upper_top := by

    rw [plausibility_eq_one_sub_belief_compl]
    simp [complement, Belief.empty]

theorem imprecisionGap_eq_common_gap (A : Finset Ω) :
    imprecisionGap m A = (toImpreciseValuation m).gap A := rfl

theorem bayesian_isPrecise (hb : m.isBayesian) :
    (toImpreciseValuation m).IsPrecise := by
  intro A
  exact bayesian_precise m hb A

end CommonFramework

section LatticeUnification

open Mettapedia.ProbabilityTheory.Common

variable (m : MassFunction Ω)

def toLatticeSum (m : MassFunction Ω) (A : Finset Ω) : ℝ :=
  Finset.sum (Finset.filter (· ⊆ A) Finset.univ.powerset) m.m

theorem latticeSum_eq_belief (A : Finset Ω) : toLatticeSum m A = belief m A := by
  unfold toLatticeSum belief
  congr 1
  ext B
  simp only [Finset.mem_filter, Finset.mem_powerset]
  constructor
  · intro ⟨_, hBA⟩
    exact hBA
  · intro hBA
    exact ⟨Finset.subset_univ B, hBA⟩

theorem powerset_bounded :
    (⊥ : Finset Ω) = ∅ ∧ (⊤ : Finset Ω) = Finset.univ := by
  constructor <;> rfl

theorem ds_eq_lattice_belief (A : Finset Ω) :
    belief m A = Finset.sum (Finset.filter (fun B => B ≤ A) Finset.univ) m.m := by
  unfold belief
  congr 1
  ext B

  simp only [Finset.mem_powerset, Finset.mem_filter, Finset.mem_univ, true_and]

theorem ds_is_monotone_on_lattice : ∀ A B : Finset Ω, A ⊆ B → belief m A ≤ belief m B :=
  fun _ _ h => Belief.mono m h

end LatticeUnification

section QuantumBridge

open Mettapedia.ProbabilityTheory.Common
open Mettapedia.ProbabilityTheory.Hypercube.NovelTheories

theorem finset_compl_eq_sdiff (A : Finset Ω) : Aᶜ = Finset.univ \ A := rfl

def MassFunction.toQuantumMass (m : MassFunction Ω) : QuantumMassFunction (Finset Ω) where
  m := m.m
  m_bot := m.m_empty
  m_nonneg := m.m_nonneg

theorem belief_eq_quantum_belief (m : MassFunction Ω) (A : Finset Ω) :
    belief m A = (m.toQuantumMass).belief A := by

  unfold belief QuantumMassFunction.belief MassFunction.toQuantumMass sumBelow finsetBelow
  congr 1
  ext B
  simp only [Finset.mem_powerset, Finset.mem_filter, Finset.mem_univ, true_and]

theorem plausibility_eq_quantum_plausibility (m : MassFunction Ω) (A : Finset Ω) :
    plausibility m A = (m.toQuantumMass).plausibility A := by

  unfold QuantumMassFunction.plausibility
  rw [← belief_eq_quantum_belief m Aᶜ]
  rw [plausibility_eq_one_sub_belief_compl]
  simp only [complement, finset_compl_eq_sdiff]

theorem finset_all_commute (A B : Finset Ω) : commutes A B := by

  simp only [commutes, inf_eq_inter, sup_eq_union]
  ext x
  simp only [Finset.mem_union, Finset.mem_inter, finset_compl_eq_sdiff,
             Finset.mem_sdiff, Finset.mem_univ, true_and]
  constructor
  · intro hA
    by_cases hB : x ∈ B
    · left; exact ⟨hA, hB⟩
    · right; exact ⟨hA, hB⟩
  · intro h
    cases h with
    | inl h => exact h.1
    | inr h => exact h.1

theorem finset_sasaki_eq_inf (A B : Finset Ω) : sasakiProj A B = A ⊓ B := by

  simp only [sasakiProj, inf_eq_inter, sup_eq_union, finset_compl_eq_sdiff]
  ext x
  simp only [Finset.mem_inter, Finset.mem_union, Finset.mem_sdiff,
             Finset.mem_univ, true_and]
  constructor
  · intro ⟨hBorNotA, hA⟩
    constructor
    · exact hA
    · cases hBorNotA with
      | inl hB => exact hB
      | inr hNotA => exact absurd hA hNotA
  · intro ⟨hA, hB⟩
    exact ⟨Or.inl hB, hA⟩

theorem classical_ds_is_boolean_quantum_ds :
    ∀ m : MassFunction Ω, ∀ A : Finset Ω,
      belief m A = (m.toQuantumMass).belief A ∧
      plausibility m A = (m.toQuantumMass).plausibility A :=
  fun m A => ⟨belief_eq_quantum_belief m A, plausibility_eq_quantum_plausibility m A⟩

end QuantumBridge

section Reconstruction
open Mettapedia.ProbabilityTheory.Common

/-- Classical focal-set masses specialize the common lattice mass without changing entries. -/
def MassFunction.toLatticeMass (m : MassFunction Ω) : Common.MassFunction (Finset Ω) where
  m := m.m
  m_bot := m.m_empty
  m_nonneg := m.m_nonneg

@[simp] theorem MassFunction.toLatticeMass_belief (m : MassFunction Ω) :
    m.toLatticeMass.belief = belief m := by
  funext A
  exact (ds_eq_lattice_belief m A).symm

theorem MassFunction.toLatticeMass_normalized (m : MassFunction Ω) :
    m.toLatticeMass.IsNormalized := by
  change m.toLatticeMass.belief ⊤ = 1
  rw [m.toLatticeMass_belief]
  exact Belief.univ m

/-- Every classical belief satisfies the full finite-family inequalities. -/
theorem belief_completelyMonotone (m : MassFunction Ω) : Common.CompletelyMonotone (belief m) := by
  rw [← m.toLatticeMass_belief]
  exact Common.mass_belief_completelyMonotone m.toLatticeMass

/-- The inverse is signed in general; for a belief it recovers the original focal masses. -/
theorem inverse_belief (m : MassFunction Ω) :
    Mettapedia.Order.FiniteIncidence.inverse (belief m) = m.m := by
  rw [← m.toLatticeMass_belief]
  exact Mettapedia.Order.FiniteIncidence.inverse_lowerSum m.m

theorem MassFunction.belief_injective : Function.Injective (belief (Ω := Ω)) := by
  intro a b equal
  have data : a.m = b.m := by rw [← inverse_belief a, ← inverse_belief b, equal]
  cases a; cases b; cases data; rfl

noncomputable def massOfCapacity (v : Common.NormalizedValuation (Finset Ω))
    (complete : Common.CompletelyMonotone v.val) : MassFunction Ω where
  m := (Common.recoverMass v complete).m
  m_empty := (Common.recoverMass v complete).m_bot
  m_nonneg := (Common.recoverMass v complete).m_nonneg
  m_sum_one := by
    rw [Finset.powerset_univ]
    have normalized := Common.recoverMass_normalized v complete
    change Common.sumBelow (Common.recoverMass v complete).m ⊤ = 1 at normalized
    simpa only [Common.sumBelow.top] using normalized

@[simp] theorem belief_massOfCapacity (v : Common.NormalizedValuation (Finset Ω))
    (complete : Common.CompletelyMonotone v.val) : belief (massOfCapacity v complete) = v.val := by
  funext A
  rw [ds_eq_lattice_belief]
  exact congrFun (Common.recoverMass_belief v complete) A

/-- A normalized monotone capacity is a belief exactly when it has nonnegative inverse masses. -/
theorem capacity_is_belief_iff (v : Common.NormalizedValuation (Finset Ω)) :
    (∃ m : MassFunction Ω, belief m = v.val) ↔ Common.CompletelyMonotone v.val := by
  refine ⟨?_, fun complete => ⟨massOfCapacity v complete, belief_massOfCapacity v complete⟩⟩
  rintro ⟨m, equal⟩
  rw [← equal]
  exact belief_completelyMonotone m
/-- Classical focal-set data and completely monotone capacities are equivalent representations. -/
noncomputable def capacityEquiv : MassFunction Ω ≃
    {v : Common.NormalizedValuation (Finset Ω) // Common.CompletelyMonotone v.val} where
  toFun m := ⟨beliefAsNormalized m, belief_completelyMonotone m⟩
  invFun v := massOfCapacity v.1 v.2
  left_inv m := by
    apply MassFunction.belief_injective
    change belief (massOfCapacity (beliefAsNormalized m) (belief_completelyMonotone m)) = belief m
    exact belief_massOfCapacity (beliefAsNormalized m) (belief_completelyMonotone m)
  right_inv v := by
    apply Subtype.ext
    apply Common.NormalizedValuation.ext
    change belief (massOfCapacity v.1 v.2) = v.1.val
    exact belief_massOfCapacity v.1 v.2

end Reconstruction

end Mettapedia.ProbabilityTheory.BeliefFunctions
