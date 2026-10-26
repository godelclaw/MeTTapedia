import Mettapedia.Cybernetics.ApproximateAdequacy.AdaptiveSemantics
import Mettapedia.ProbabilityTheory.FiniteLumpability
import Mathlib.Data.Fin.Tuple.Basic

/-!
# Trace semantics of finite adaptive policies

Each trace retains every next state and observation. Its probability law is
constructed from successive conditional kernel draws and tuple-prefix pushforward.
Projecting this independently defined law recovers the terminal law. Compatible
joint steps preserve the full trace law, hence every coarse-trace observation;
terminal reward is one such observation.
-/

namespace Mettapedia.Cybernetics.ApproximateAdequacy

open Mettapedia.InformationTheory
open Mettapedia.InformationTheory.Prob

variable {S O A : Type*} [Fintype S] [Fintype O] [DecidableEq S] [DecidableEq O]

def traceTerminal (initial : S) : {n : ℕ} → (Fin n → S × O) → S
  | 0, _ => initial
  | n + 1, trace => traceTerminal (trace 0).1 (n := n) (Fin.tail trace)

noncomputable def traceLaw (kernel : A → S → Prob (S × O)) :
    {n : ℕ} → ObservationPolicy O A n → S → Prob (Fin n → S × O)
  | 0, _, _ => Prob.dirac (fun i => Fin.elim0 i)
  | n + 1, policy, s =>
      Prob.bind (kernel policy.1 s) (fun next =>
        coarsen (traceLaw kernel (n := n) (policy.2 next.2) next.1)
          (fun trace : Fin n → S × O => Fin.cons next trace))

/-- The terminal distribution is the pushforward of the full execution law. -/
theorem terminalLaw_eq_coarsen_traceLaw (kernel : A → S → Prob (S × O))
    {n : ℕ} (policy : ObservationPolicy O A n) (s : S) :
    terminalLaw kernel policy s = coarsen (traceLaw kernel policy s) (traceTerminal s) := by
  symm
  induction n generalizing s with
  | zero => exact coarsen_dirac _ _
  | succ n ih =>
      rw [traceLaw, coarsen_bind]
      change Prob.bind (kernel policy.1 s) _ = Prob.bind (kernel policy.1 s) _
      congr 1
      funext next
      rw [coarsen_comp]
      simpa only [Function.comp_def, traceTerminal, Fin.cons_zero, Fin.tail_cons] using
        ih (policy.2 next.2) next.1

/-- The recurrence is derived from the entire finite execution law. -/
theorem traceLaw_value (kernel : A → S → Prob (S × O)) (reward : S → ℝ)
    {n : ℕ} (policy : ObservationPolicy O A n) (s : S) :
    (∑ trace, (traceLaw kernel policy s).1 trace * reward (traceTerminal s trace)) =
      adaptiveValue kernel reward policy s := by
  rw [← terminalLaw_value kernel reward, terminalLaw_eq_coarsen_traceLaw, coarsen_expectation]

variable {C : Type*} [Fintype C] [DecidableEq C]
variable (view : S → C) (source : A → S → Prob (S × O)) (target : A → C → Prob (C × O))
variable (compatible : ∀ a s,
  coarsen (source a s) (fun next => (view next.1, next.2)) = target a (view s))
include compatible

/-- Joint-step compatibility preserves complete ordered state/observation histories.
Only the state component is coarsened; observations continue to select the same policy branches. -/
theorem traceLaw_coarsen {n : ℕ} (policy : ObservationPolicy O A n) (s : S) :
    coarsen (traceLaw source policy s) (fun trace i => (view (trace i).1, (trace i).2)) =
      traceLaw target policy (view s) := by
  induction n generalizing s with
  | zero =>
      rw [traceLaw, traceLaw, coarsen_dirac]
      congr 1
      exact funext fun i => i.elim0
  | succ n ih =>
      change coarsen (Prob.bind (source policy.1 s) _)
        (fun trace : Fin (n + 1) → S × O => fun i => (view (trace i).1, (trace i).2)) =
          Prob.bind (target policy.1 (view s)) _
      refine (Mettapedia.ProbabilityTheory.FiniteLumpability.coarsen_bind_of_rows
        (fun next => (view next.1, next.2)) _ _
        (fun next : C × O => coarsen (traceLaw target (policy.2 next.2) next.1)
          (fun trace : Fin n → C × O => Fin.cons next trace))
        ?_ (source policy.1 s)).trans ?_
      · intro next
        rw [coarsen_comp]
        have mapCons : (fun trace : Fin (n + 1) → S × O =>
            fun i => (view (trace i).1, (trace i).2)) ∘
              (fun trace : Fin n → S × O => Fin.cons next trace) =
            (fun trace : Fin n → C × O => Fin.cons (view next.1, next.2) trace) ∘
              (fun trace : Fin n → S × O => fun i => (view (trace i).1, (trace i).2)) :=
          funext fun trace => Fin.comp_cons (fun z : S × O => (view z.1, z.2)) next trace
        rw [mapCons, ← coarsen_comp, ih]
      · rw [compatible]

/-- Every real-valued readout of the coarsened trace has the same expectation. -/
theorem traceLaw_expectation_coarsen {n : ℕ} (policy : ObservationPolicy O A n) (s : S)
    (observer : (Fin n → C × O) → ℝ) :
    expect (traceLaw source policy s).1
        (fun trace => observer (fun i => (view (trace i).1, (trace i).2))) =
      expect (traceLaw target policy (view s)).1 observer := by
  simpa only [expect, coarsen_expectation] using
    congrArg (fun law : Prob (Fin n → C × O) => expect law.1 observer)
      (traceLaw_coarsen view source target compatible policy s)

end Mettapedia.Cybernetics.ApproximateAdequacy
