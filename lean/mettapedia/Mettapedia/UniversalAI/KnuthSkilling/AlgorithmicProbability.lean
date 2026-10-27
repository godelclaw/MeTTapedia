import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic

import KnuthSkilling.Information.InformationEntropy
import Mettapedia.UniversalAI.GrainOfTruth.MeasureTheory.KLDivergenceBridge
import Mettapedia.UniversalAI.SolomonoffPrior

/-!
# Algorithmic weights and probability observations

A Solomonoff semimeasure need not have total mass one. Finite restriction and
normalization supply a probability distribution at positive total weight, with
an exact event-query law. Cylinder prediction has two distinct observations:
condition on continuation, or retain the missing mass as a stopped outcome.
KL against another predictor requires compatible supports for the real formula;
extended KL retains support violations as infinity in the information layer.
-/

namespace Mettapedia.UniversalAI.KnuthSkilling

open Classical
open Finset
open scoped BigOperators

open _root_.KnuthSkilling.Information.InformationEntropy

noncomputable def normalizeWeights {n : ℕ}
    (w : Fin n → ℝ) (hw : ∀ i, 0 ≤ w i) (hsum_pos : 0 < ∑ i, w i) : ProbDist n :=
  let Z : ℝ := ∑ i, w i
  { p := fun i => w i / Z
    nonneg := fun i => div_nonneg (hw i) (le_of_lt hsum_pos)
    sum_one := by
      rw [← Finset.sum_div]
      exact div_self (ne_of_gt hsum_pos) }

/-- Normalization preserves every finite weighted-event query. -/
theorem normalizeWeights_event {n : ℕ} (w : Fin n → ℝ) (hw : ∀ i, 0 ≤ w i)
    (h : 0 < ∑ i, w i) (E : Finset (Fin n)) :
    (∑ i ∈ E, (normalizeWeights w hw h).p i) = (∑ i ∈ E, w i) / ∑ i, w i := by
  simp only [normalizeWeights, Finset.sum_div]

namespace Solomonoff

open _root_.Mettapedia.UniversalAI.SolomonoffPrior

noncomputable def normalizeSemimeasureOnFinset
    (sm : Semimeasure) (s : Finset BinString)
    (hsum_pos : 0 < Finset.sum s (fun x => sm.μ x)) : ProbDist (#s) := by
  classical
  let e := s.equivFin
  let w : Fin #s → ℝ := fun i => sm.μ (e.symm i).1
  have hw : ∀ i, 0 ≤ w i := fun i => sm.nonneg (e.symm i).1

  have hsum_eq : (∑ i : Fin #s, w i) = ∑ x ∈ s, sm.μ x := by
    calc
      _ = ∑ x : s, sm.μ x.val := by simpa [w] using Equiv.sum_comp e.symm (fun x : s => sm.μ x.val)
      _ = _ := by simpa using Finset.sum_attach s sm.μ
  have hsum_pos' : 0 < ∑ i : Fin #s, w i := by rw [hsum_eq]; exact hsum_pos
  exact normalizeWeights w hw hsum_pos'

end Solomonoff

namespace Solomonoff

open _root_.Mettapedia.UniversalAI.SolomonoffPrior

namespace Prediction

noncomputable def cylinderConditional (U : MonotoneMachine) (programs : Finset BinString)
    (x : BinString) (b : Bool) (_hx : 0 < U.cylinderMeasure programs x) : ℝ :=
  U.cylinderMeasure programs (x ++ [b]) / U.cylinderMeasure programs x

theorem cylinderConditional_nonneg (U : MonotoneMachine) (programs : Finset BinString)
    (x : BinString) (b : Bool) (hx : 0 < U.cylinderMeasure programs x) :
    0 ≤ cylinderConditional U programs x b hx := by
  unfold cylinderConditional
  exact div_nonneg (U.cylinderMeasure_nonneg programs (x ++ [b])) (le_of_lt hx)

theorem cylinderConditional_sum_le_one (U : MonotoneMachine) (programs : Finset BinString)
    (x : BinString) (hx : 0 < U.cylinderMeasure programs x) :
    cylinderConditional U programs x false hx +
        cylinderConditional U programs x true hx ≤ 1 := by
  have hsub :
      U.cylinderMeasure programs (x ++ [false]) + U.cylinderMeasure programs (x ++ [true])
        ≤ U.cylinderMeasure programs x := by
    simpa using (cylinderMeasure_subadditive (U := U) programs x)
  have hdiv :
      (U.cylinderMeasure programs (x ++ [false]) + U.cylinderMeasure programs (x ++ [true])) /
          U.cylinderMeasure programs x ≤ 1 :=
    (div_le_one hx).2 hsub
  simpa [cylinderConditional, add_div] using hdiv

noncomputable def nextBitWeights (U : MonotoneMachine) (programs : Finset BinString) (x : BinString) :
    Fin 2 → ℝ :=
  fun i =>
    Fin.cases (U.cylinderMeasure programs (x ++ [false]))
      (fun _ => U.cylinderMeasure programs (x ++ [true])) i

theorem nextBitWeights_nonneg (U : MonotoneMachine) (programs : Finset BinString) (x : BinString) :
    ∀ i, 0 ≤ nextBitWeights U programs x i := by
  intro i
  refine Fin.cases ?_ (fun _ => ?_) i
  · exact U.cylinderMeasure_nonneg programs (x ++ [false])
  · exact U.cylinderMeasure_nonneg programs (x ++ [true])

/-- Condition on continuation; the enabled successor mass must be positive. -/
noncomputable def normalizedNextBitDist (U : MonotoneMachine) (programs : Finset BinString) (x : BinString)
    (hsum_pos : 0 < ∑ i : Fin 2, nextBitWeights U programs x i) : ProbDist 2 :=
  normalizeWeights (nextBitWeights U programs x) (nextBitWeights_nonneg U programs x) hsum_pos

theorem normalizedNextBitDist_kl_self_nonneg
    (U : MonotoneMachine) (programs : Finset BinString) (x : BinString)
    (hsum_pos : 0 < ∑ i : Fin 2, nextBitWeights U programs x i) :
    let P := normalizedNextBitDist U programs x hsum_pos
    0 ≤
      klDivergence P P (fun i hi =>
        lt_of_le_of_ne (P.nonneg i) (by
          intro h0
          exact hi (by simpa [eq_comm] using h0))) := by
  intro P
  exact klDivergence_nonneg' P P (fun i hi =>
    lt_of_le_of_ne (P.nonneg i) (by
      intro h0
      exact hi (by simpa [eq_comm] using h0)))

/-- Retain the missing successor mass as the third, stopped outcome. -/
noncomputable def nextBitHaltDist (U : MonotoneMachine) (programs : Finset BinString) (x : BinString)
    (hx : 0 < U.cylinderMeasure programs x) : ProbDist 3 :=
  let p0 := cylinderConditional U programs x false hx
  let p1 := cylinderConditional U programs x true hx
  { p := fun i =>
      match (i : ℕ) with
      | 0 => p0
      | 1 => p1
      | _ => 1 - p0 - p1
    nonneg := by
      intro i
      have hp0 : 0 ≤ p0 := cylinderConditional_nonneg U programs x false hx
      have hp1 : 0 ≤ p1 := cylinderConditional_nonneg U programs x true hx
      have hp2 : 0 ≤ 1 - p0 - p1 := by
        have hsum : p0 + p1 ≤ 1 := cylinderConditional_sum_le_one U programs x hx
        linarith
      fin_cases i
      · simpa [p0, p1] using hp0
      · simpa [p0, p1] using hp1
      · simpa [p0, p1] using hp2
    sum_one := by
      have h : p0 + p1 + (1 - p0 - p1) = (1 : ℝ) := by
        ring_nf
      simp [Fin.sum_univ_three, p0, p1, h] }

end Prediction
end Solomonoff

open Mettapedia.UniversalAI.GrainOfTruth.MeasureTheory.KLDivergenceBridge

theorem gibbs_inequality_shared_gate :
    (∀ {n : ℕ} (P Q : ProbDist n) (hQ_pos : ∀ i, P.p i ≠ 0 → 0 < Q.p i),
        0 ≤ klDivergence P Q hQ_pos) ∧
    (∀ {n : ℕ} (_hn : 0 < n) (P Q : Fin n → ℝ)
        (_hP_nonneg : ∀ i, 0 ≤ P i) (_hQ_nonneg : ∀ i, 0 ≤ Q i)
        (_hP_sum : ∑ i, P i = 1) (_hQ_sum : ∑ i, Q i = 1)
        (_hQ_pos : ∀ i, P i ≠ 0 → 0 < Q i),
        ∑ i, P i * Real.log (Q i / P i) ≤ 0) := by
  refine ⟨?_, ?_⟩
  · intro n P Q hQ_pos
    exact klDivergence_nonneg' P Q hQ_pos
  · intro n hn P Q hP_nonneg hQ_nonneg hP_sum hQ_sum hQ_pos
    exact stepLogLikelihood_sum_nonpos_via_gibbs (n := n) hn P Q hP_nonneg hQ_nonneg hP_sum hQ_sum hQ_pos

namespace Solomonoff

open _root_.Mettapedia.UniversalAI.SolomonoffPrior

namespace Prediction

theorem klDivergence_normalizedNextBitDist_nonneg
    (U V : MonotoneMachine) (programs : Finset BinString) (x : BinString)
    (hU : 0 < ∑ i : Fin 2, nextBitWeights U programs x i)
    (hV : 0 < ∑ i : Fin 2, nextBitWeights V programs x i)
    (hQ_pos :
      ∀ i,
        (normalizedNextBitDist U programs x hU).p i ≠ 0 → 0 < (normalizedNextBitDist V programs x hV).p i) :
    0 ≤
      klDivergence (normalizedNextBitDist U programs x hU) (normalizedNextBitDist V programs x hV) hQ_pos := by
  exact (gibbs_inequality_shared_gate).1 _ _ hQ_pos

end Prediction
end Solomonoff

theorem solomonoff_normalize_kl_self_nonneg
    (sm : _root_.Mettapedia.UniversalAI.SolomonoffPrior.Semimeasure)
    (s : Finset _root_.Mettapedia.UniversalAI.SolomonoffPrior.BinString)
    (hsum_pos : 0 < Finset.sum s (fun x => sm.μ x)) :
    let P := Solomonoff.normalizeSemimeasureOnFinset sm s hsum_pos
    0 ≤
      klDivergence P P (fun i hi =>
        lt_of_le_of_ne (P.nonneg i) (by
          intro h0
          exact hi (by simpa [eq_comm] using h0))) := by
  intro P
  exact (gibbs_inequality_shared_gate).1 P P (fun i hi =>
    lt_of_le_of_ne (P.nonneg i) (by
      intro h0
      exact hi (by simpa [eq_comm] using h0)))

end Mettapedia.UniversalAI.KnuthSkilling
