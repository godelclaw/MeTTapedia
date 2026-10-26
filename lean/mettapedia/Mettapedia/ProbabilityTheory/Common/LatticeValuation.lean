import Mathlib.Order.Lattice
import Mathlib.Order.BooleanAlgebra.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic
import Mettapedia.ProbabilityTheory.Structures.Valuation.Basic
import Mettapedia.ProbabilityTheory.Common.LatticeSummation
import Mathlib.Combinatorics.Enumerative.InclusionExclusion

/-!
# Finite mass, belief and additive valuation profiles

Belief is the lower-set transform of a nonnegative mass. Normalization does not
make it additive: additive valuations are a stronger, separate profile. The
existing `AdditiveValuation` owns the common disjoint-additivity law.

The complement-preserving additive profile below does not itself supply an
orthomodular law for the underlying lattice; that is an ambient assumption.
-/

namespace Mettapedia.ProbabilityTheory.Common

section BeliefFromMass

variable {L : Type*} [Lattice L] [BoundedOrder L] [Fintype L]
variable [DecidableRel (α := L) (· ≤ ·)]

structure MassFunction (L : Type*) [Lattice L] [BoundedOrder L] where

  m : L → ℝ

  m_bot : m ⊥ = 0

  m_nonneg : ∀ a, 0 ≤ m a

namespace MassFunction

noncomputable def belief
    (mf : MassFunction L) (a : L) : ℝ :=
  sumBelow mf.m a

noncomputable def totalMass
    (mf : MassFunction L) : ℝ :=
  mf.belief ⊤

@[simp]
theorem belief_bot (mf : MassFunction L) : mf.belief ⊥ = 0 := by
  simp [belief, mf.m_bot]

theorem belief_mono (mf : MassFunction L) {a b : L} (h : a ≤ b) :
    mf.belief a ≤ mf.belief b :=
  sumBelow.mono_of_nonneg mf.m mf.m_nonneg h

theorem belief_nonneg (mf : MassFunction L) (a : L) : 0 ≤ mf.belief a :=
  sumBelow.nonneg_of_nonneg mf.m mf.m_nonneg a

theorem m_le_belief (mf : MassFunction L) (a : L) : mf.m a ≤ mf.belief a :=
  sumBelow.self_le_of_nonneg mf.m mf.m_nonneg a

theorem belief_le_totalMass (mf : MassFunction L) (a : L) :
    mf.belief a ≤ mf.totalMass :=
  mf.belief_mono le_top

def IsNormalized (mf : MassFunction L) : Prop := mf.totalMass = 1

noncomputable def toMonotoneValuation (mf : MassFunction L) : MonotoneValuation L where
  val := mf.belief
  mono := fun _ _ h => mf.belief_mono h

noncomputable def toNormalizedValuation (mf : MassFunction L) (hn : mf.IsNormalized) :
    NormalizedValuation L where
  val := mf.belief
  mono := fun _ _ h => mf.belief_mono h
  val_bot := mf.belief_bot
  val_top := hn

end MassFunction

end BeliefFromMass

section BooleanBridge

theorem additive_sum_rule_on_boolean {L : Type*} [BooleanAlgebra L]
    (v : AdditiveValuation L) (a b : L) :
    v.val (a ⊔ b) = v.val a + v.val b - v.val (a ⊓ b) := by

  have hdisj : a ⊓ (b ⊓ aᶜ) = ⊥ := by
    calc a ⊓ (b ⊓ aᶜ) = (a ⊓ aᶜ) ⊓ b := by ac_rfl
         _ = ⊥ ⊓ b := by rw [inf_compl_eq_bot]
         _ = ⊥ := by simp
  have hsup : a ⊔ b = a ⊔ (b ⊓ aᶜ) := by

    have h2 : b ⊓ (a ⊔ aᶜ) = (b ⊓ a) ⊔ (b ⊓ aᶜ) := inf_sup_left b a aᶜ
    have h3 : a ⊔ (a ⊓ b) = a := sup_inf_self
    calc a ⊔ b = a ⊔ (b ⊓ (a ⊔ aᶜ)) := by rw [sup_compl_eq_top, inf_top_eq]
         _ = a ⊔ ((b ⊓ a) ⊔ (b ⊓ aᶜ)) := by rw [h2]
         _ = a ⊔ ((a ⊓ b) ⊔ (b ⊓ aᶜ)) := by rw [inf_comm b a]
         _ = (a ⊔ (a ⊓ b)) ⊔ (b ⊓ aᶜ) := by rw [sup_assoc]
         _ = a ⊔ (b ⊓ aᶜ) := by rw [h3]
  rw [hsup, v.additive a (b ⊓ aᶜ) hdisj]

  have hb_disj : (a ⊓ b) ⊓ (b ⊓ aᶜ) = ⊥ := by
    calc (a ⊓ b) ⊓ (b ⊓ aᶜ) = (a ⊓ aᶜ) ⊓ (b ⊓ b) := by ac_rfl
         _ = ⊥ ⊓ b := by rw [inf_compl_eq_bot, inf_idem]
         _ = ⊥ := by simp
  have hb_eq : b = (a ⊓ b) ⊔ (b ⊓ aᶜ) := by
    calc b = b ⊓ ⊤ := by rw [inf_top_eq]
         _ = b ⊓ (a ⊔ aᶜ) := by rw [sup_compl_eq_top]
         _ = (b ⊓ a) ⊔ (b ⊓ aᶜ) := by rw [inf_sup_left]
         _ = (a ⊓ b) ⊔ (b ⊓ aᶜ) := by rw [inf_comm]
  have hval_b : v.val b = v.val (a ⊓ b) + v.val (b ⊓ aᶜ) := by
    conv_lhs => rw [hb_eq]
    exact v.additive (a ⊓ b) (b ⊓ aᶜ) hb_disj
  linarith

noncomputable def additiveToSumRule {L : Type*} [BooleanAlgebra L]
    (v : AdditiveValuation L) : SumRuleValuation L where
  toNormalizedValuation := v.toNormalizedValuation
  sum_rule := additive_sum_rule_on_boolean v

end BooleanBridge

class HasOrthocomplement (L : Type*) extends Compl L where
  compl_compl : ∀ a : L, aᶜᶜ = a

structure OrthomodularValuation (L : Type*) [Lattice L] [BoundedOrder L] [Compl L]
    extends AdditiveValuation L where

  val_compl : ∀ a, val aᶜ = 1 - val a

namespace OrthomodularValuation

variable {L : Type*} [Lattice L] [BoundedOrder L] [Compl L]

theorem add_compl (v : OrthomodularValuation L) (a : L) :
    v.val a + v.val aᶜ = 1 := by
  rw [v.val_compl]
  ring

theorem val_compl_bot (v : OrthomodularValuation L)
    (h : (⊥ : L)ᶜ = ⊤) : v.val (⊥ : L)ᶜ = 1 := by
  rw [h, v.val_top]

theorem val_compl_top (v : OrthomodularValuation L)
    (h : (⊤ : L)ᶜ = ⊥) : v.val (⊤ : L)ᶜ = 0 := by
  rw [h, v.val_bot]

end OrthomodularValuation

structure ImpreciseLatticeValuation (L : Type*) [Lattice L] [BoundedOrder L] where

  lower : MonotoneValuation L

  upper : L → ℝ

  lower_le_upper : ∀ a, lower.val a ≤ upper a

  lower_bot : lower.val ⊥ = 0

  upper_top : upper ⊤ = 1

namespace ImpreciseLatticeValuation

variable {L : Type*} [Lattice L] [BoundedOrder L]

def gap (v : ImpreciseLatticeValuation L) (a : L) : ℝ :=
  v.upper a - v.lower.val a

theorem gap_nonneg (v : ImpreciseLatticeValuation L) (a : L) : 0 ≤ v.gap a := by
  simp only [gap]
  linarith [v.lower_le_upper a]

def IsPrecise (v : ImpreciseLatticeValuation L) : Prop :=
  ∀ a, v.lower.val a = v.upper a

end ImpreciseLatticeValuation

section Reconstruction
open Finset
open Mettapedia.Order
open scoped BigOperators
variable {L : Type*} [Lattice L] [BoundedOrder L]

/-- Inclusion-exclusion on a finite indexed family, retaining repeated values. -/
noncomputable def alternating {ι : Type*} (v : L → ℝ) (s : Finset ι) (family : ι → L) : ℝ :=
  ∑ t : s.powerset.filter (·.Nonempty), (-1 : ℤ) ^ (t.1.card + 1) •
    v (t.1.inf' (mem_filter.mp t.2).2 family)

/-- The finite-subfamily presentation; `completelyMonotone_family` gives the
usual law for arbitrary indexed families, including duplicate values. -/
def CompletelyMonotone (v : L → ℝ) : Prop :=
  ∀ s : Finset L, alternating v s id ≤ v (s.sup id)

variable [Fintype L] [DecidableEq L] [DecidableLE L]

omit [BoundedOrder L] in
/-- Inclusion-exclusion for principal ideals works even with signed masses. -/
theorem alternating_lowerSum {ι : Type*} (m : L → ℝ) (s : Finset ι) (family : ι → L) :
    alternating (sumBelow m) s family =
      ∑ x ∈ s.biUnion (fun i => finsetBelow (family i)), m x := by
  classical
  rw [Finset.inclusion_exclusion_sum_biUnion]
  unfold alternating
  apply sum_congr rfl
  intro t _
  congr 1
  change (∑ x ∈ finsetBelow (t.1.inf' (mem_filter.mp t.2).2 family), m x) = _
  congr 1
  ext x
  simp only [finsetBelow.mem_iff, Finset.le_inf'_iff, Finset.mem_inf']

theorem alternating_mass_le {ι : Type*} (m : L → ℝ) (positive : ∀ x, 0 ≤ m x)
    (s : Finset ι) (family : ι → L) :
    alternating (sumBelow m) s family ≤ sumBelow m (s.sup family) := by
  classical
  rw [alternating_lowerSum]
  apply sum_le_sum_of_subset_of_nonneg
  · intro x member
    obtain ⟨i, hi, hx⟩ := mem_biUnion.mp member
    exact (finsetBelow.mem_iff _ _).mpr
      (le_trans ((finsetBelow.mem_iff _ _).mp hx) (Finset.le_sup hi))
  · intro x _ _; exact positive x

theorem mass_belief_completelyMonotone (m : MassFunction L) : CompletelyMonotone m.belief :=
  fun s => alternating_mass_le m.m m.m_nonneg s id

omit [BoundedOrder L] in
/-- Isolating the last coefficient of the independent inverse transform. -/
theorem inverse_recurrence (v : L → ℝ) (x : L) :
    FiniteIncidence.inverse v x = v x -
      ∑ y ∈ (finsetBelow x).erase x, FiniteIncidence.inverse v y := by
  have reconstruct := congrFun (FiniteIncidence.lowerSum_inverse v) x
  change ∑ y ∈ finsetBelow x, FiniteIncidence.inverse v y = v x at reconstruct
  rw [← Finset.add_sum_erase _ _ (finsetBelow.self_mem x)] at reconstruct
  linarith

/-- A capacity's independent inclusion-exclusion laws force every signed inverse
coefficient to be nonnegative. No positivity hypothesis is put on that inverse. -/
theorem inverse_nonneg_of_completelyMonotone (v : NormalizedValuation L)
    (complete : CompletelyMonotone v.val) (x : L) : 0 ≤ FiniteIncidence.inverse v.val x := by
  classical
  let s := (finsetBelow x).erase x
  have union : s.biUnion finsetBelow = s := by
    ext z
    simp only [mem_biUnion]
    constructor
    · rintro ⟨a, ha, hz⟩
      obtain ⟨different, below⟩ := mem_erase.mp ha
      have z_below := (finsetBelow.mem_iff _ _).mp hz
      apply mem_erase.mpr
      refine ⟨?_, (finsetBelow.mem_iff _ _).mpr (le_trans z_below ((finsetBelow.mem_iff _ _).mp below))⟩
      intro equal
      exact different (le_antisymm ((finsetBelow.mem_iff _ _).mp below) (equal ▸ z_below))
    · intro hz; exact ⟨z,hz,finsetBelow.self_mem z⟩
  have observations : sumBelow (FiniteIncidence.inverse v.val) = v.val :=
    FiniteIncidence.lowerSum_inverse v.val
  have identity : alternating v.val s id = ∑ y ∈ s, FiniteIncidence.inverse v.val y := by
    conv_lhs => rw [← observations]
    rw [alternating_lowerSum]
    simp only [id_eq, union]
  have bound := complete s
  rw [identity] at bound
  have smaller : s.sup id ≤ x := Finset.sup_le fun y hy =>
    (finsetBelow.mem_iff _ _).mp (mem_of_mem_erase hy)
  have cap_bound := v.mono _ _ smaller
  rw [inverse_recurrence]
  linarith

/-- Exact boundary between arbitrary capacities and nonnegative mass semantics. -/
theorem completelyMonotone_iff_inverse_nonneg (v : NormalizedValuation L) :
    CompletelyMonotone v.val ↔ ∀ x, 0 ≤ FiniteIncidence.inverse v.val x := by
  refine ⟨inverse_nonneg_of_completelyMonotone v, ?_⟩
  intro nonnegative s
  have observations : sumBelow (FiniteIncidence.inverse v.val) = v.val :=
    FiniteIncidence.lowerSum_inverse v.val
  rw [← observations]
  exact alternating_mass_le _ nonnegative s id

/-- Complete monotonicity covers arbitrary finite indexing and repeated events. -/
theorem completelyMonotone_family {ι : Type*} (v : NormalizedValuation L)
    (complete : CompletelyMonotone v.val) (s : Finset ι) (family : ι → L) :
    alternating v.val s family ≤ v.val (s.sup family) := by
  have observations : sumBelow (FiniteIncidence.inverse v.val) = v.val :=
    FiniteIncidence.lowerSum_inverse v.val
  rw [← observations]
  exact alternating_mass_le _ ((completelyMonotone_iff_inverse_nonneg v).mp complete) s family

noncomputable def recoverMass (v : NormalizedValuation L) (complete : CompletelyMonotone v.val) :
    MassFunction L where
  m := FiniteIncidence.inverse v.val
  m_bot := by
    have h := congrFun (FiniteIncidence.lowerSum_inverse v.val) ⊥
    change sumBelow (FiniteIncidence.inverse v.val) ⊥ = _ at h
    simpa using h.trans v.val_bot
  m_nonneg := inverse_nonneg_of_completelyMonotone v complete

@[simp] theorem recoverMass_belief (v : NormalizedValuation L) (complete : CompletelyMonotone v.val) :
    (recoverMass v complete).belief = v.val := FiniteIncidence.lowerSum_inverse v.val

theorem recoverMass_normalized (v : NormalizedValuation L) (complete : CompletelyMonotone v.val) :
    (recoverMass v complete).IsNormalized := by
  change (recoverMass v complete).belief ⊤ = 1
  rw [recoverMass_belief, v.val_top]

/-- All belief queries determine the mass uniquely. -/
theorem MassFunction.belief_injective : Function.Injective (MassFunction.belief (L := L)) := by
  intro a b equal
  have data : a.m = b.m := FiniteIncidence.lowerSum_injective equal
  cases a; cases b; cases data; rfl

omit [Fintype L] [DecidableEq L] [DecidableLE L] in
@[ext] theorem NormalizedValuation.ext {a b : NormalizedValuation L} (same : a.val = b.val) : a = b := by
  cases a with
  | mk a a0 a1 =>
    cases b with
    | mk b b0 b1 =>
      cases a; cases b
      cases same
      rfl

/-- Normalized positive mass and completely monotone capacity retain exactly the same data. -/
noncomputable def normalizedMassEquiv :
    {m : MassFunction L // m.IsNormalized} ≃
      {v : NormalizedValuation L // CompletelyMonotone v.val} where
  toFun m := ⟨m.1.toNormalizedValuation m.2, mass_belief_completelyMonotone m.1⟩
  invFun v := ⟨recoverMass v.1 v.2, recoverMass_normalized v.1 v.2⟩
  left_inv m := by
    apply Subtype.ext
    apply MassFunction.belief_injective
    change (recoverMass (m.1.toNormalizedValuation m.2)
      (mass_belief_completelyMonotone m.1)).belief = m.1.belief
    exact recoverMass_belief (m.1.toNormalizedValuation m.2) (mass_belief_completelyMonotone m.1)
  right_inv v := by
    apply Subtype.ext
    apply NormalizedValuation.ext
    change (recoverMass v.1 v.2).belief = v.1.val
    exact recoverMass_belief v.1 v.2

end Reconstruction

end Mettapedia.ProbabilityTheory.Common
