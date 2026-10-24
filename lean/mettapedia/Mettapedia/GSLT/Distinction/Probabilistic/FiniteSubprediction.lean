import Mettapedia.GSLT.Distinction.Probabilistic.FinitePrediction
import Mettapedia.GSLT.Distinction.Probabilistic.Completion

/-!
# Finite subdistribution prediction through weighted traversal

A normalized prior may select a kernel row that refuses with positive
probability. Mixing such rows gives a subdistribution: successor weights are
mixed pointwise and their missing mass remains refusal. The existing weighted
traversal computes every successor coordinate and, independently, the total
enabled mass. Completing with a stopped state then agrees with first completing
every row and applying ordinary probability bind.

Support alone cannot recover refusal. Concrete controls keep that information
loss visible.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Distinction.Probabilistic.FiniteSubprediction

open Mettapedia.InformationTheory
open Mettapedia.InformationTheory.Prob
open Mettapedia.GSLT.Distinction.Probabilistic
open Mettapedia.GSLT.Distinction.Probabilistic.FinitePrediction
open scoped BigOperators

variable {n : Nat} {S T : Type*} [Fintype S] [Fintype T]

/-- Mix finite subdistribution rows under a normalized prior. -/
noncomputable def subBind (prior : Prob S) (kernel : S → SubDistribution T) :
    SubDistribution T :=
  SubDistribution.ofFunction
    (fun target => ∑ source, prior.1 source * (kernel source).weight target)
    (fun target => Finset.sum_nonneg fun source _ =>
      mul_nonneg (prior.2.1 source) ((kernel source).nonneg target))
    (by
      calc
        (∑ target, ∑ source, prior.1 source * (kernel source).weight target) =
            ∑ source, prior.1 source * ∑ target, (kernel source).weight target := by
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro source _
          rw [Finset.mul_sum]
        _ ≤ ∑ source, prior.1 source * 1 :=
          Finset.sum_le_sum fun source _ => mul_le_mul_of_nonneg_left
            ((kernel source).total_eq_sum.symm ▸ (kernel source).total_le_one')
            (prior.2.1 source)
        _ = 1 := by simpa using prior.2.2)

@[simp] theorem subBind_weight (prior : Prob S) (kernel : S → SubDistribution T)
    (target : T) :
    (subBind prior kernel).weight target =
      ∑ source, prior.1 source * (kernel source).weight target := by
  simp [subBind]

theorem subBind_total (prior : Prob S) (kernel : S → SubDistribution T) :
    (subBind prior kernel).total =
      ∑ source, prior.1 source * (kernel source).total := by
  rw [(subBind prior kernel).total_eq_sum]
  simp only [subBind_weight]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro source _
  rw [← Finset.mul_sum, ← (kernel source).total_eq_sum]

/-- Missing mass is the probability of refusing the step. -/
noncomputable def refusal (law : SubDistribution T) : ℝ := 1 - law.total

omit [Fintype T] in
theorem refusal_nonneg (law : SubDistribution T) : 0 ≤ refusal law := by
  unfold refusal
  linarith [law.total_le_one']

/-- Complete a subdistribution by sending all refusal mass to `none`. -/
noncomputable def complete (law : SubDistribution T) : Prob (Option T) :=
  ⟨fun
    | none => refusal law
    | some target => law.weight target,
    (fun target => by
      cases target with
      | none => exact refusal_nonneg law
      | some target => exact law.nonneg target),
    by
      rw [Fintype.sum_option]
      change refusal law + ∑ target, law.weight target = 1
      rw [← law.total_eq_sum]
      unfold refusal
      ring⟩

@[simp] theorem complete_none (law : SubDistribution T) :
    (complete law).1 none = refusal law := rfl

@[simp] theorem complete_some (law : SubDistribution T) (target : T) :
    (complete law).1 (some target) = law.weight target := rfl

/-- Standalone completion is the same stopped row used by a probabilistic
GSLT's canonical completion. -/
theorem complete_eq_completionTrans [DecidableEq S]
    (system : ProbabilisticSystem (stateGSLT S))
    (label : system.Label) (source : S) :
    (complete (system.kernel label source)).1 =
      completionTrans system label (some source) := by
  funext target
  cases target <;> rfl

/-- Completing after mixing preserves both successful mass and refusal. -/
theorem complete_subBind (prior : Prob S) (kernel : S → SubDistribution T) :
    complete (subBind prior kernel) = bind prior (fun source => complete (kernel source)) := by
  apply Subtype.ext
  funext target
  cases target with
  | some target =>
      simp only [complete_some, subBind_weight, bind_apply]
  | none =>
      simp only [complete_none, bind_apply]
      unfold refusal
      rw [subBind_total]
      calc
        1 - ∑ source, prior.1 source * (kernel source).total =
            ∑ source, prior.1 source -
              ∑ source, prior.1 source * (kernel source).total := by rw [prior.2.2]
        _ = ∑ source, (prior.1 source -
              prior.1 source * (kernel source).total) := by rw [Finset.sum_sub_distrib]
        _ = ∑ source, prior.1 source * (1 - (kernel source).total) := by
          apply Finset.sum_congr rfl
          intro source _
          ring

/-- The traversal's selected successor coordinate. -/
noncomputable def subpredictionRow (enumeration : Fin n ≃ S) (prior : Prob S)
    (kernel : S → SubDistribution T) (target : T) : ℝ :=
  rowValue (fun index => (kernel (enumeration index)).weight target)
    (fun index => prior.1 (enumeration index)) (List.finRange n)

theorem subpredictionRow_eq (enumeration : Fin n ≃ S) (prior : Prob S)
    (kernel : S → SubDistribution T) (target : T) :
    subpredictionRow enumeration prior kernel target = (subBind prior kernel).weight target := by
  rw [subpredictionRow, rowValue_eq_sum, ← Fin.sum_univ_def, subBind_weight]
  rw [enumeration.sum_comp
    (fun source => (kernel source).weight target * prior.1 source)]
  exact Finset.sum_congr rfl fun source _ => mul_comm _ _

/-- A second traversal computes enabled mass; refusal remains its complement. -/
noncomputable def subpredictionTotal (enumeration : Fin n ≃ S) (prior : Prob S)
    (kernel : S → SubDistribution T) : ℝ :=
  rowValue (fun index => (kernel (enumeration index)).total)
    (fun index => prior.1 (enumeration index)) (List.finRange n)

theorem subpredictionTotal_eq (enumeration : Fin n ≃ S) (prior : Prob S)
    (kernel : S → SubDistribution T) :
    subpredictionTotal enumeration prior kernel = (subBind prior kernel).total := by
  rw [subpredictionTotal, rowValue_eq_sum, ← Fin.sum_univ_def, subBind_total]
  rw [enumeration.sum_comp (fun source => (kernel source).total * prior.1 source)]
  exact Finset.sum_congr rfl fun source _ => mul_comm _ _

noncomputable def subpredictionRefusal (enumeration : Fin n ≃ S) (prior : Prob S)
    (kernel : S → SubDistribution T) : ℝ :=
  1 - subpredictionTotal enumeration prior kernel

theorem subpredictionRefusal_eq (enumeration : Fin n ≃ S) (prior : Prob S)
    (kernel : S → SubDistribution T) :
    subpredictionRefusal enumeration prior kernel = refusal (subBind prior kernel) := by
  rw [subpredictionRefusal, refusal, subpredictionTotal_eq]

/-- Bundle the independently traversed coordinates as a subdistribution. -/
noncomputable def interpretedSubprediction (enumeration : Fin n ≃ S) (prior : Prob S)
    (kernel : S → SubDistribution T) : SubDistribution T :=
  SubDistribution.ofFunction (subpredictionRow enumeration prior kernel)
    (fun target => by rw [subpredictionRow_eq]; exact (subBind prior kernel).nonneg target)
    (by
      simp_rw [subpredictionRow_eq]
      rw [← (subBind prior kernel).total_eq_sum]
      exact (subBind prior kernel).total_le_one')

theorem interpretedSubprediction_eq_subBind (enumeration : Fin n ≃ S) (prior : Prob S)
    (kernel : S → SubDistribution T) :
    interpretedSubprediction enumeration prior kernel = subBind prior kernel := by
  unfold interpretedSubprediction subBind
  congr 1
  funext target
  exact subpredictionRow_eq enumeration prior kernel target

/-- Completion of the traversal result agrees with normalized prediction over
the rowwise stopped completions. -/
theorem complete_interpretedSubprediction (enumeration : Fin n ≃ S) (prior : Prob S)
    (kernel : S → SubDistribution T) :
    complete (interpretedSubprediction enumeration prior kernel) =
      bind prior (fun source => complete (kernel source)) := by
  rw [interpretedSubprediction_eq_subBind, complete_subBind]

/-- Both the selected-coordinate traversal and enabled-mass traversal perform
one transition per input occurrence plus finalization. -/
theorem execution_lengths (enumeration : Fin n ≃ S) (prior : Prob S)
    (kernel : S → SubDistribution T) (target : T) :
    (rowPath (List.finRange n)).length = n + 1 ∧
    subpredictionRow enumeration prior kernel target = (subBind prior kernel).weight target ∧
    subpredictionTotal enumeration prior kernel = (subBind prior kernel).total := by
  exact ⟨by simp [rowPath_length], subpredictionRow_eq enumeration prior kernel target,
    subpredictionTotal_eq enumeration prior kernel⟩

namespace Controls

noncomputable def certain : SubDistribution Unit :=
  SubDistribution.ofFunction (fun _ => 1) (by simp) (by simp)

noncomputable def hesitant : SubDistribution Unit :=
  SubDistribution.ofFunction (fun _ => (1 / 2 : ℝ)) (by norm_num) (by norm_num)

/-- Equal successor support can conceal different refusal probabilities. -/
theorem support_forgets_refusal :
    certain.weight.support = hesitant.weight.support ∧
      refusal certain = 0 ∧ refusal hesitant = 1 / 2 := by
  constructor
  · ext target
    simp [certain, hesitant, Finsupp.mem_support_iff]
  · constructor
    · norm_num [refusal, certain, SubDistribution.total_eq_sum]
    · norm_num [refusal, hesitant, SubDistribution.total_eq_sum]

/-- Stopped completion exposes the distinction erased by successor support. -/
theorem completion_retains_refusal :
    (complete certain).1 none = 0 ∧ (complete hesitant).1 none = 1 / 2 ∧
      complete certain ≠ complete hesitant := by
  refine ⟨by norm_num [complete, refusal, certain, SubDistribution.total_eq_sum],
    by norm_num [complete, refusal, hesitant, SubDistribution.total_eq_sum], ?_⟩
  intro same
  have atStopped := congrArg (fun law : Prob (Option Unit) => law.1 none) same
  norm_num [complete, refusal, certain, hesitant, SubDistribution.total_eq_sum] at atStopped

end Controls

end Mettapedia.GSLT.Distinction.Probabilistic.FiniteSubprediction
