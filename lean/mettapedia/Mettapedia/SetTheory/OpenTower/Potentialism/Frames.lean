import Mettapedia.SetTheory.OpenTower.Strength.AdmittedTheories
import Mettapedia.SetTheory.OpenTower.Strength.ClosedLevels
import Mettapedia.SetTheory.OpenTower.Strength.Shapes

/-!
# Four frames under extension

Extension of stages, and extension of theories, as Kripke frames.

* The closed sets of one level, ordered by inclusion, are reflexive, transitive,
  directed and linear.
* The stages of a tower of stages, ordered by inclusion of the stages, are the
  same shape, and the order of the stages is the order of their indices.
* The admitted theories, ordered by inclusion, are reflexive and transitive, and
  neither directed nor linear: the well-founded theory and the anti-founded theory
  are admitted and have no common admitted extension.
* The plural family is that one frame. Its worlds are the admitted theories:
  any part of either maximal theory. The singleton of membership induction is
  a world.
-/

set_option autoImplicit false

namespace Mettapedia.SetTheory.OpenTower.Potentialism

open Mettapedia.Logic.HOL.Embedding.ZFSetUniverseClosure
open Mettapedia.SetTheory.CarveOuts
open Mettapedia.SetTheory.OpenTower.InternalTower
open Mettapedia.SetTheory.OpenTower.Strength.AdmittedTheories
open Mettapedia.SetTheory.OpenTower.Strength.ClosedLevels
open Mettapedia.SetTheory.OpenTower.Strength.Shapes
open Mettapedia.SetTheory.OpenTower.Strength.StageFamilies
open scoped ZFSet

universe u

/-! ## Closed sets of one level -/

/-- The closed sets of one level are reflexive under inclusion. -/
theorem closedFrame_refl (A : {U : ZFSet.{u} // Closed U}) : A.1 ⊆ A.1 :=
  fun _ hz => hz

/-- The closed sets of one level are transitive under inclusion. -/
theorem closedFrame_trans {A B C : {U : ZFSet.{u} // Closed U}}
    (hAB : A.1 ⊆ B.1) (hBC : B.1 ⊆ C.1) : A.1 ⊆ C.1 :=
  fun _ hz => hBC (hAB hz)

/-- **The closed sets of one level are linear under inclusion.** -/
theorem closedFrame_linear (A B : {U : ZFSet.{u} // Closed U}) :
    A.1 ⊆ B.1 ∨ B.1 ⊆ A.1 :=
  closed_subset_total A.2 B.2

/-- The closed sets of one level are directed under inclusion. -/
theorem closedFrame_directed (A B : {U : ZFSet.{u} // Closed U}) :
    ∃ C : {U : ZFSet.{u} // Closed U}, A.1 ⊆ C.1 ∧ B.1 ⊆ C.1 := by
  rcases closedFrame_linear A B with h | h
  · exact ⟨B, h, fun _ hz => hz⟩
  · exact ⟨A, fun _ hz => hz, h⟩

/-- The empty set is included in the hereditarily finite sets, and not conversely. -/
example :
    ((∅ : ZFSet.{u}) ⊆ V_ Ordinal.omega0) ∧ ¬ V_ Ordinal.omega0 ⊆ (∅ : ZFSet.{u}) := by
  refine ⟨ZFSet.empty_subset _, ?_⟩
  intro h
  exact ZFSet.notMem_empty _ (h empty_mem_vonNeumann_omega)

/-! ## A tower of stages -/

/-- An earlier index of a tower of stages is included in a later one. -/
theorem stageChain_subset_of_le {s : ℕ → ZFSet.{u}} (chain : StageChain s)
    {m n : ℕ} (hmn : m ≤ n) : s m ⊆ s n := by
  rcases Nat.lt_or_eq_of_le hmn with hlt | rfl
  · exact closed_subset_of_mem (chain.closed n) (chain.mem_of_lt hlt)
  · exact fun _ hz => hz

/-- **Inclusion of stages is the order of the indices.** -/
theorem stageChain_subset_iff_le {s : ℕ → ZFSet.{u}} (chain : StageChain s)
    {m n : ℕ} : s m ⊆ s n ↔ m ≤ n := by
  constructor
  · intro h
    rcases lt_trichotomy m n with hlt | rfl | hgt
    · exact le_of_lt hlt
    · exact le_rfl
    · exact absurd (h (chain.mem_of_lt hgt)) (ZFSet.mem_irrefl (s n))
  · exact stageChain_subset_of_le chain

/-- The stages of a tower are reflexive under inclusion. -/
theorem stageChain_frame_refl {s : ℕ → ZFSet.{u}} (chain : StageChain s) (n : ℕ) :
    s n ⊆ s n :=
  stageChain_subset_of_le chain le_rfl

/-- The stages of a tower are transitive under inclusion. -/
theorem stageChain_frame_trans {s : ℕ → ZFSet.{u}} (chain : StageChain s)
    {m n k : ℕ} (hmn : s m ⊆ s n) (hnk : s n ⊆ s k) : s m ⊆ s k := by
  have hmn' : m ≤ n := (stageChain_subset_iff_le chain).mp hmn
  have hnk' : n ≤ k := (stageChain_subset_iff_le chain).mp hnk
  exact stageChain_subset_of_le chain (hmn'.trans hnk')

/-- **The stages of a tower are linear under inclusion.** -/
theorem stageChain_frame_linear {s : ℕ → ZFSet.{u}} (chain : StageChain s) (m n : ℕ) :
    s m ⊆ s n ∨ s n ⊆ s m := by
  rcases le_total m n with h | h
  · exact Or.inl (stageChain_subset_of_le chain h)
  · exact Or.inr (stageChain_subset_of_le chain h)

/-- The stages of a tower are directed under inclusion. -/
theorem stageChain_frame_directed {s : ℕ → ZFSet.{u}} (chain : StageChain s) (m n : ℕ) :
    ∃ k, s m ⊆ s k ∧ s n ⊆ s k := by
  rcases le_total m n with h | h
  · exact ⟨n, stageChain_subset_of_le chain h, stageChain_frame_refl chain n⟩
  · exact ⟨m, stageChain_frame_refl chain m, stageChain_subset_of_le chain h⟩

/-- **A linear open tower is linear under inclusion.** Any two of its stages are
comparable, because they are stages of one tower. -/
theorem linearTower_frame {𝔖 : Set ZFSet.{u}} (tower : IsLinearTower 𝔖)
    {U V : ZFSet.{u}} (hU : U ∈ 𝔖) (hV : V ∈ 𝔖) : U ⊆ V ∨ V ⊆ U := by
  obtain ⟨s, chain, rfl⟩ := tower
  obtain ⟨m, rfl⟩ := hU
  obtain ⟨n, rfl⟩ := hV
  exact stageChain_frame_linear chain m n

/-- Each stage of a tower is included in the next, and the next is not included
in the previous. -/
example {s : ℕ → ZFSet.{u}} (chain : StageChain s) :
    s 0 ⊆ s 1 ∧ ¬ s 1 ⊆ s 0 := by
  refine ⟨stageChain_subset_of_le chain (Nat.le_succ 0), ?_⟩
  intro h
  exact ZFSet.mem_irrefl _ (h (chain.mem_succ 0))

/-! ## Admitted theories -/

theorem not_wellFounded_subset_antiFounded : ¬ wellFounded ⊆ antiFounded := by
  intro h
  have mem : Principle.induction ∈ antiFounded := h (by simp [wellFounded])
  simp [antiFounded, setForming] at mem

theorem not_antiFounded_subset_wellFounded : ¬ antiFounded ⊆ wellFounded := by
  intro h
  have mem : Principle.quineAtom ∈ wellFounded := h (by simp [antiFounded])
  simp [wellFounded, setForming] at mem

/-- The admitted theories are reflexive under inclusion. -/
theorem admitted_refl (A : {T : Set Principle // Admitted.{u + 1} T}) : A.1 ⊆ A.1 :=
  Set.Subset.refl _

/-- The admitted theories are transitive under inclusion. -/
theorem admitted_trans {A B C : {T : Set Principle // Admitted.{u + 1} T}}
    (hAB : A.1 ⊆ B.1) (hBC : B.1 ⊆ C.1) : A.1 ⊆ C.1 :=
  hAB.trans hBC

/-- **The admitted theories are not directed under inclusion.** The well-founded
theory and the anti-founded theory have no common admitted extension. -/
theorem admitted_not_directed :
    ¬ ∀ A B : {T : Set Principle // Admitted.{u + 1} T},
        ∃ C : {T : Set Principle // Admitted.{u + 1} T}, A.1 ⊆ C.1 ∧ B.1 ⊆ C.1 := by
  intro h
  obtain ⟨C, hA, hB⟩ :=
    h ⟨wellFounded, admitted_wellFounded⟩ ⟨antiFounded, admitted_antiFounded⟩
  exact no_common_admitted_extension hA hB C.2

/-- **The admitted theories are not linear under inclusion.** -/
theorem admitted_not_linear :
    ¬ ∀ A B : {T : Set Principle // Admitted.{u + 1} T}, A.1 ⊆ B.1 ∨ B.1 ⊆ A.1 := by
  intro h
  rcases h ⟨wellFounded, admitted_wellFounded⟩ ⟨antiFounded, admitted_antiFounded⟩ with
    h | h
  · exact not_wellFounded_subset_antiFounded h
  · exact not_antiFounded_subset_wellFounded h

/-- The singleton of membership induction is a world of this frame. Membership
induction together with a Quine atom is not admitted. -/
example :
    Admitted.{u + 1} {Principle.induction} ∧
      ¬ Admitted.{u + 1} ({Principle.induction, Principle.quineAtom} : Set Principle) := by
  refine ⟨admitted_wellFounded.mono (Set.singleton_subset_iff.mpr (by simp [wellFounded])),
    not_admitted_induction_quineAtom⟩

end Mettapedia.SetTheory.OpenTower.Potentialism
