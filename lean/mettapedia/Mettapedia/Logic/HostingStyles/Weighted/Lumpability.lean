import Mettapedia.Logic.HostingStyles.Weighted.KernelPreservation
import Mettapedia.ProbabilityTheory.FiniteLumpability

/-!
# Closed sums and strong lumpability

`lumpedKernel` at a class is the coarsening of the kernel at the chosen
representative. Along that section, closed-sum preservation is the definition
of the quotient row: it holds for every kernel. `StrongLumpability` is the
further claim that the same closed sum is the row of every state in the
fibre. `lumpedKernel_correct` is that claim. A two-point observation of three
states preserves closed sums at the section and fails off it.
-/

set_option autoImplicit false

universe u v

namespace Mettapedia.Logic.HostingStyles.Weighted

open Classical
open Finset
open Mettapedia.GSLT
open Mettapedia.GSLT.Distinction.Probabilistic
open Mettapedia.InformationTheory
open Mettapedia.InformationTheory.Prob
open Mettapedia.ProbabilityTheory.FiniteLumpability

/-! ## Probability rows as finitely supported weights -/

/-- The mass function of a finite distribution, as a finitely supported family. -/
noncomputable def probRow {α : Type*} [Fintype α] (prior : Prob α) : α →₀ ℝ :=
  Finsupp.ofSupportFinite prior.1 (Set.toFinite (Function.support prior.1))

theorem probRow_apply {α : Type*} [Fintype α] (prior : Prob α) (state : α) :
    probRow prior state = prior.1 state := by
  simp [probRow, Finsupp.ofSupportFinite_coe]

/-- **Positive.** A point mass is weight one at its state. -/
theorem probRow_dirac_self {α : Type*} [Fintype α] [DecidableEq α] (state : α) :
    probRow (dirac state) state = 1 := by
  rw [probRow_apply, dirac_apply]
  simp

/-- **Negative.** A point mass is weight zero at every other state. -/
theorem probRow_dirac_other {α : Type*} [Fintype α] [DecidableEq α] {state other : α}
    (different : other ≠ state) : probRow (dirac state) other = 0 := by
  rw [probRow_apply, dirac_apply, if_neg different]

theorem closedSum_probRow {α : Type*} [Fintype α] (prior : Prob α) (held : α → Prop) :
    closedSum (probRow prior) held =
      ∑ state : α, if held state then prior.1 state else 0 := by
  unfold closedSum
  rw [Finset.sum_subset (Finset.subset_univ (probRow prior).support)]
  · refine Finset.sum_congr rfl fun state _ => ?_
    rw [probRow_apply]
  · intro state _ outside
    have zero : probRow prior state = 0 := (Finsupp.notMem_support_iff).mp outside
    rw [zero]
    split_ifs <;> rfl

theorem indicator_expectation {α : Type*} [Fintype α] (mass : α → ℝ) (held : α → Prop) :
    (∑ state : α, (if held state then mass state else 0 : ℝ)) =
      ∑ state : α, mass state * (if held state then (1 : ℝ) else 0) := by
  refine Finset.sum_congr rfl fun state _ => ?_
  by_cases holds : held state
  · simp [holds]
  · simp [holds]

/-- Coarsening preserves the closed sum of every set of observations. -/
theorem closedSum_coarsen {S C : Type*} [Fintype S] [Fintype C] [DecidableEq C]
    (prior : Prob S) (view : S → C) (held : C → Prop) :
    closedSum (probRow (coarsen prior view)) held =
      closedSum (probRow prior) (fun state => held (view state)) := by
  rw [closedSum_probRow, closedSum_probRow, indicator_expectation, indicator_expectation,
    coarsen_expectation]

/-! ## The quotient map along a section -/

noncomputable def lumpMap {S C : Type u} {A : Type v} [Fintype S] [Fintype C] [DecidableEq S]
    [DecidableEq C] (view : S → C) (kernel : A → S → Prob S) (representative : C → S) :
    KernelMap ℝ (GSLT.stepFree C) (GSLT.stepFree S) where
  source := {
    Atom := Unit
    observes := fun _ _ => True
    observes_resp := fun _ {_ _} _ => Iff.rfl
    Label := A
    kernel := fun (action : A) (class_ : (GSLT.stepFree C).Term) =>
      (probRow (lumpedKernel view kernel representative action (show C from class_)) : C →₀ ℝ)
    kernel_resp := fun _ {_ _} equivalent _ _ => by
      cases equivalent
      rfl
  }
  target := {
    Atom := Unit
    observes := fun _ _ => True
    observes_resp := fun _ {_ _} _ => Iff.rfl
    Label := A
    kernel := fun (action : A) (state : (GSLT.stepFree S).Term) =>
      (probRow (kernel action (show S from state)) : S →₀ ℝ)
    kernel_resp := fun _ {_ _} equivalent _ _ => by
      cases equivalent
      rfl
  }
  term := representative
  labelMap := id
  readBack := view
  readBack_resp := fun equivalent => congrArg view equivalent

/-- **Positive.** The quotient row is the coarsening of its representative, so the
section map preserves every closed sum. Lumpability is not required. -/
theorem section_kernelPreserving {S C : Type u} {A : Type v} [Fintype S] [Fintype C] [DecidableEq S]
    [DecidableEq C] (view : S → C) (kernel : A → S → Prob S) (representative : C → S) :
    KernelPreserving (lumpMap view kernel representative) := by
  intro action class_ held _closed
  dsimp [lumpMap]
  unfold lumpedKernel
  exact closedSum_coarsen (kernel action (representative (show C from class_))) view held

/-- **Strong lumpability, as closed sums at every state.** With a section,
`lumpedKernel_correct` says the quotient row of a class equals the coarsening
of every state in that class, not only the representative. -/
theorem lumpable_state_closedSum {S C : Type u} {A : Type v} [Fintype S] [Fintype C] [DecidableEq S]
    [DecidableEq C] (view : S → C) (kernel : A → S → Prob S) (representative : C → S)
    (sectionLaw : Function.RightInverse representative view)
    (lumpable : StrongLumpability view kernel) (action : A) (state : S) (held : C → Prop) :
    closedSum (probRow (lumpedKernel view kernel representative action (view state))) held =
      closedSum (probRow (kernel action state)) (fun source => held (view source)) := by
  have agreed :=
    lumpedKernel_correct view kernel representative sectionLaw lumpable action state
  rw [show probRow (lumpedKernel view kernel representative action (view state)) =
      probRow (coarsen (kernel action state) view) from congrArg probRow agreed]
  exact closedSum_coarsen (kernel action state) view held

/-- **Positive.** A separating observation is strongly lumpable: each fibre is one state. -/
theorem id_strongLumpability {S : Type u} {A : Type v} [Fintype S] [DecidableEq S]
    (kernel : A → S → Prob S) : StrongLumpability (id : S → S) kernel := by
  intro _ _ _ same
  cases same
  rfl

/-! ## A section that preserves weights and is not lumpable -/

inductive LumpState where
  | l1
  | l2
  | r
  deriving DecidableEq

instance : Fintype LumpState where
  elems := {LumpState.l1, LumpState.l2, LumpState.r}
  complete := by
    intro state
    cases state
    · exact Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
    · exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))

inductive LumpClass where
  | left
  | right
  deriving DecidableEq

instance : Fintype LumpClass where
  elems := {LumpClass.left, LumpClass.right}
  complete := by
    intro class_
    cases class_
    · exact Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)

def lumpView : LumpState → LumpClass
  | .l1 => .left
  | .l2 => .left
  | .r => .right

def lumpRep : LumpClass → LumpState
  | .left => .l1
  | .right => .r

def separatingKernel : Unit → LumpState → Prob LumpState
  | _, LumpState.l1 => dirac LumpState.r
  | _, LumpState.l2 => dirac LumpState.l1
  | _, LumpState.r => dirac LumpState.r

theorem lumpRep_section : Function.RightInverse lumpRep lumpView := by
  intro class_
  cases class_ <;> rfl

theorem closedSum_dirac_right_class :
    closedSum (probRow (dirac LumpClass.right)) (fun class_ : LumpClass => class_ = .right) = 1 := by
  rw [closedSum_probRow, Finset.sum_eq_single (a := LumpClass.right)]
  · simp [dirac_apply]
  · intro class_ _ different
    cases class_ with
    | right => exact absurd rfl different
    | left => simp
  · intro absent
    exact (absent (Finset.mem_univ _)).elim

theorem closedSum_dirac_r_preimage :
    closedSum (probRow (dirac LumpState.r)) (fun state => lumpView state = .right) = 1 := by
  rw [closedSum_probRow, Finset.sum_eq_single (a := LumpState.r)]
  · simp [dirac_apply, lumpView]
  · intro state _ different
    cases state with
    | r => exact absurd rfl different
    | l1 => simp [lumpView]
    | l2 => simp [lumpView]
  · intro absent
    exact (absent (Finset.mem_univ _)).elim

theorem closedSum_dirac_l1_preimage :
    closedSum (probRow (dirac LumpState.l1)) (fun state => lumpView state = .right) = 0 := by
  rw [closedSum_probRow, Finset.sum_eq_single (a := LumpState.r)]
  · simp [dirac_apply, lumpView]
  · intro state _ different
    cases state with
    | r => exact absurd rfl different
    | l1 => simp [lumpView]
    | l2 => simp [lumpView]
  · intro absent
    exact (absent (Finset.mem_univ _)).elim

/-- **Negative.** The section map preserves closed sums, and the kernel is not
strongly lumpable: `l2` steps to `l1`, while the representative `l1` steps to
`r`. The closed sum of `{right}` is `1` on the quotient row and `0` at `l2`. -/
theorem separating_preserves_not_lumpable :
    KernelPreserving (lumpMap lumpView separatingKernel lumpRep) ∧
      ¬ StrongLumpability lumpView separatingKernel ∧
      closedSum (probRow (lumpedKernel lumpView separatingKernel lumpRep () .left))
          (fun class_ => class_ = .right) ≠
        closedSum (probRow (separatingKernel () .l2)) (fun state => lumpView state = .right) := by
  refine ⟨section_kernelPreserving lumpView separatingKernel lumpRep, ?_, ?_⟩
  · intro lumpable
    have same := lumpable () .l1 .l2 rfl
    simp only [separatingKernel, coarsen_dirac, lumpView] at same
    have atRight := congrArg (fun distribution : Prob LumpClass => distribution.1 .right) same
    simp [dirac_apply] at atRight
  · have lumpedOne :
        closedSum (probRow (lumpedKernel lumpView separatingKernel lumpRep () .left))
          (fun class_ => class_ = .right) = 1 := by
      have row :
          lumpedKernel lumpView separatingKernel lumpRep () .left =
            dirac LumpClass.right := by
        simp [lumpedKernel, lumpRep, separatingKernel, coarsen_dirac, lumpView]
      rw [row]
      exact closedSum_dirac_right_class
    have sourceZero :
        closedSum (probRow (separatingKernel () .l2)) (fun state => lumpView state = .right) =
          0 := by
      have row : separatingKernel () .l2 = dirac LumpState.l1 := by
        simp [separatingKernel]
      rw [row]
      exact closedSum_dirac_l1_preimage
    rw [lumpedOne, sourceZero]
    exact one_ne_zero

end Mettapedia.Logic.HostingStyles.Weighted
