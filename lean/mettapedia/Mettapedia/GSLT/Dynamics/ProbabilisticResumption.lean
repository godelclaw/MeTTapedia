import Mettapedia.GSLT.Dynamics.WeightedBranchingResumption
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Algebra.BigOperators.Ring.List

/-!
# Probability readout of retained weighted execution

A normalized nonnegative response catalogue induces a Mathlib probability
mass function. Its sample space first consists of physical list positions;
only the answer readout combines equal values. The operational catalogue
itself retains duplicate and zero-weight occurrences.

The probability execution below uses `PMF.bind` independently of the weighted
frontier recursion. Their correspondence includes both returned answers and
pending states. In particular, a finite cut is not conditioning on the answers
that have already returned, and resuming retains all incoming probability.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Dynamics.ProbabilisticResumption

open WeightedResumption WeightedBranchingResumption
open scoped BigOperators ENNReal NNReal Classical

universe u v w

variable {A : Type u} {B : Type v} {State : Type w}

private theorem sum_positions (rows : Contributions A ℝ≥0) :
    (∑ index : Fin rows.length, rows[index].2) = total rows := by
  simpa only [List.sum_ofFn, Fin.getElem_fin, total, SemiringTraversal.weightSum] using
    congrArg List.sum (List.ofFn_getElem_eq_map rows Prod.snd)

/-- A probability on physical occurrences, with no quotient of equal answers. -/
noncomputable def occurrenceLaw (rows : Contributions A ℝ≥0) (normalized : total rows = 1) :
    PMF (Fin rows.length) :=
  PMF.ofFintype (fun index => (rows[index].2 : ℝ≥0∞)) (by
    rw [← ENNReal.ofNNReal_finsetSum, sum_positions, normalized]
    rfl)

/-- Combine equal answers only at this declared probability observation. -/
noncomputable def ofContributions (rows : Contributions A ℝ≥0) (normalized : total rows = 1) :
    PMF A := (occurrenceLaw rows normalized).map (fun index => rows[index].1)

@[simp] theorem occurrenceLaw_apply (rows : Contributions A ℝ≥0)
    (normalized : total rows = 1) (index : Fin rows.length) :
    occurrenceLaw rows normalized index = (rows[index].2 : ℝ≥0∞) := rfl

theorem ofContributions_apply (rows : Contributions A ℝ≥0)
    (normalized : total rows = 1) (answer : A) :
    ofContributions rows normalized answer =
      (rows.map fun row => if answer = row.1 then (row.2 : ℝ≥0∞) else 0).sum := by
  classical
  rw [ofContributions, PMF.map_apply, tsum_fintype]
  simp only [occurrenceLaw_apply]
  simpa only [List.sum_ofFn, Fin.getElem_fin] using congrArg List.sum
    (List.ofFn_getElem_eq_map rows
      (fun row => if answer = row.1 then (row.2 : ℝ≥0∞) else 0))

@[simp] theorem ofContributions_singleton (answer : A) :
    ofContributions [(answer, 1)] (by simp [total, SemiringTraversal.weightSum]) =
      PMF.pure answer := by
  classical
  ext other
  simp [ofContributions_apply, PMF.pure_apply, eq_comm]

/-- The continuation sum is over occurrences, including repeated answers. -/
theorem bind_ofContributions_apply (rows : Contributions A ℝ≥0)
    (normalized : total rows = 1) (next : A → PMF B) (answer : B) :
    (ofContributions rows normalized |>.bind next) answer =
      (rows.map fun row => (row.2 : ℝ≥0∞) * next row.1 answer).sum := by
  rw [ofContributions, PMF.bind_map, PMF.bind_apply, tsum_fintype]
  simp only [occurrenceLaw_apply, Function.comp_apply]
  simpa only [List.sum_ofFn, Fin.getElem_fin] using congrArg List.sum
    (List.ofFn_getElem_eq_map rows (fun row => (row.2 : ℝ≥0∞) * next row.1 answer))

theorem total_sequence_one (rows : Contributions A ℝ≥0)
    (normalized : total rows = 1) (next : A → Contributions B ℝ≥0)
    (nextNormalized : ∀ answer, total (next answer) = 1) :
    total (sequence rows next) = 1 := by
  rw [total_sequence]
  simp only [nextNormalized, mul_one]
  exact normalized

/-- The probability observation is a monad morphism on normalized catalogues. -/
theorem ofContributions_sequence (rows : Contributions A ℝ≥0)
    (normalized : total rows = 1) (next : A → Contributions B ℝ≥0)
    (nextNormalized : ∀ answer, total (next answer) = 1) :
    ofContributions (sequence rows next)
        (total_sequence_one rows normalized next nextNormalized) =
      (ofContributions rows normalized).bind
        (fun answer => ofContributions (next answer) (nextNormalized answer)) := by
  classical
  ext answer
  rw [ofContributions_apply, bind_ofContributions_apply]
  simp only [ofContributions_apply, WeightedResumption.sequence, List.flatMap, List.map_flatten,
    List.map_map, List.sum_flatten, Function.comp_def]
  apply congrArg List.sum
  apply List.map_congr_left
  intro row _
  rw [← List.sum_map_mul_left]
  congr 1
  apply List.map_congr_left
  intro other _
  simp only [ENNReal.coe_mul]
  split_ifs <;> simp

theorem total_map_answers (rows : Contributions A ℝ≥0) (readout : A → B) :
    total (rows.map fun row => (readout row.1, row.2)) = total rows := by
  simp [total, SemiringTraversal.weightSum, List.map_map, Function.comp_def]

theorem ofContributions_map (rows : Contributions A ℝ≥0)
    (normalized : total rows = 1) (readout : A → B) :
    ofContributions (rows.map fun row => (readout row.1, row.2))
        ((total_map_answers rows readout).trans normalized) =
      (ofContributions rows normalized).map readout := by
  have sequenced := ofContributions_sequence rows normalized
    (fun answer => [(readout answer, 1)])
    (fun _ => by simp [total, SemiringTraversal.weightSum])
  simpa only [sequence_map, ofContributions_singleton, PMF.map, Function.comp_def] using sequenced

/-- Each branching step is a normalized stochastic choice. Returning imposes
no choice, and an empty branching catalogue does not satisfy this condition. -/
abbrev Normalized (source : Coalgebra State A ℝ≥0) : Prop :=
  ∀ state rows, source state = .inr rows → total rows = 1

/-- Independently execute a finite stochastic cut. Open states remain outcomes. -/
noncomputable def law (source : Coalgebra State A ℝ≥0) (normalized : Normalized source) :
    Nat → State → PMF (A ⊕ State)
  | 0, state => PMF.pure (.inr state)
  | fuel + 1, state =>
      match inspected : source state with
      | .inl answer => PMF.pure (.inl answer)
      | .inr rows =>
          (ofContributions rows (normalized state rows inspected)).bind (law source normalized fuel)

@[simp] theorem law_zero (source : Coalgebra State A ℝ≥0) (normalized : Normalized source)
    (state : State) : law source normalized 0 state = PMF.pure (.inr state) := rfl

theorem law_return (source : Coalgebra State A ℝ≥0) (normalized : Normalized source)
    (fuel : Nat) {state : State} {answer : A} (returned : source state = .inl answer) :
    law source normalized (fuel + 1) state = PMF.pure (.inl answer) := by
  unfold law
  split <;> simp_all

theorem law_branch (source : Coalgebra State A ℝ≥0) (normalized : Normalized source)
    (fuel : Nat) {state : State} {rows : Contributions State ℝ≥0}
    (branches : source state = .inr rows) :
    law source normalized (fuel + 1) state =
      (ofContributions rows (normalized state rows branches)).bind (law source normalized fuel) := by
  unfold law
  split
  next answer inspected => cases inspected.symm.trans branches
  next alternatives inspected =>
    have same : alternatives = rows := Sum.inr.inj (inspected.symm.trans branches)
    subst alternatives
    rfl

theorem contributions_normalized (source : Coalgebra State A ℝ≥0)
    (normalized : Normalized source) (fuel : Nat) (state : State) :
    total (contributions source fuel state) = 1 := by
  induction fuel generalizing state with
  | zero => simp [contributions, total, SemiringTraversal.weightSum]
  | succ fuel ih =>
      cases inspected : source state with
      | inl answer => simp [contributions, inspected, total, SemiringTraversal.weightSum]
      | inr rows =>
          simpa only [contributions, inspected] using
            total_sequence_one rows (normalized state rows inspected)
              (contributions source fuel) ih

/-- The stochastic recursion agrees with the independently implemented
weighted frontier, including the complete residual state at a cut. -/
theorem law_eq_readout (source : Coalgebra State A ℝ≥0) (normalized : Normalized source)
    (fuel : Nat) (state : State) :
    law source normalized fuel state =
      ofContributions (contributions source fuel state)
        (contributions_normalized source normalized fuel state) := by
  induction fuel generalizing state with
  | zero => exact (ofContributions_singleton (Sum.inr state : A ⊕ State)).symm
  | succ fuel ih =>
      cases inspected : source state with
      | inl answer =>
          rw [law_return source normalized fuel inspected]
          simpa only [contributions, inspected] using
            (ofContributions_singleton (Sum.inl answer : A ⊕ State)).symm
      | inr rows =>
          rw [law_branch source normalized fuel inspected]
          rw [funext ih]
          simpa only [contributions, inspected] using
            (ofContributions_sequence rows (normalized state rows inspected)
              (contributions source fuel) (contributions_normalized source normalized fuel)).symm

noncomputable def resumeLaw (source : Coalgebra State A ℝ≥0) (normalized : Normalized source)
    (fuel : Nat) : A ⊕ State → PMF (A ⊕ State)
  | .inl answer => PMF.pure (.inl answer)
  | .inr state => law source normalized fuel state

/-- A cut preserves incoming mass: completed answers stay completed and each
pending world continues with its conditional law, without resampling its past. -/
theorem law_add (source : Coalgebra State A ℝ≥0) (normalized : Normalized source)
    (first second : Nat) (state : State) :
    law source normalized (first + second) state =
      (law source normalized first state).bind (resumeLaw source normalized second) := by
  induction first generalizing state with
  | zero => simp [law, resumeLaw]
  | succ first ih =>
      rw [Nat.succ_add]
      cases inspected : source state with
      | inl answer => simp only [law_return source normalized _ inspected, PMF.pure_bind, resumeLaw]
      | inr rows =>
          simp only [law_branch source normalized _ inspected, PMF.bind_bind]
          rw [funext ih]

/-- A certified completed frontier retains its full probability law at every
larger budget. The certificate is about returned tags, not exhausted fuel. -/
theorem law_stable_of_completed (source : Coalgebra State A ℝ≥0)
    (normalized : Normalized source) (fuel extra : Nat) (state : State)
    (completed : (contributions source fuel state).all (fun row => row.1.isLeft) = true) :
    law source normalized (fuel + extra) state = law source normalized fuel state := by
  have same : contributions source (fuel + extra) state = contributions source fuel state := by
    rw [contributions_add, continue_without_pending source extra _ completed]
  simp only [law_eq_readout, same]

/-- Read a finite cut without requiring decidable equality of retained worlds. -/
theorem law_map_apply (source : Coalgebra State A ℝ≥0) (normalized : Normalized source)
    (fuel : Nat) (state : State) (readout : A ⊕ State → B) (answer : B) :
    ((law source normalized fuel state).map readout) answer =
      ((contributions source fuel state).map fun row =>
        if answer = readout row.1 then (row.2 : ℝ≥0∞) else 0).sum := by
  rw [law_eq_readout, ← ofContributions_map, ofContributions_apply]
  simp only [List.map_map, Function.comp_def]

namespace Controls

/-- One choice terminates sooner than the other. The latter then branches again. -/
noncomputable def unequalDepth : Coalgebra Nat Bool ℝ≥0
  | 0 => .inr [(1, 1 / 2), (2, 1 / 2)]
  | 1 => .inl false
  | 2 => .inr [(3, 1 / 2), (4, 1 / 2)]
  | _ => .inl true

theorem unequalDepth_normalized : Normalized unequalDepth := by
  intro state rows inspected
  rcases state with _ | _ | _ | state <;>
    simp only [unequalDepth] at inspected
  all_goals cases inspected
  all_goals norm_num [total, SemiringTraversal.weightSum]

/-- Erase pending identities for this observation only; pending remains explicit. -/
def completed : Bool ⊕ Nat → Option Bool
  | .inl answer => some answer
  | .inr _ => none

theorem unequalDepth_frontier :
    contributions unequalDepth 3 0 =
      [(.inl false, 1 / 2), (.inl true, 1 / 4), (.inl true, 1 / 4)] := by
  norm_num [contributions, unequalDepth, WeightedResumption.sequence]

/-- Three physical leaves do not represent three equiprobable outcomes. -/
theorem counting_leaves_changes_probability :
    ((law unequalDepth unequalDepth_normalized 3 0).map completed) (some false) = 1 / 2 ∧
      ((law unequalDepth unequalDepth_normalized 3 0).map completed) (some false) ≠ 1 / 3 := by
  rw [law_map_apply, unequalDepth_frontier]
  norm_num [completed]

/-- A cut carries half its mass in completed answers and half in pending states. -/
theorem pending_mass_is_retained :
    ((law unequalDepth unequalDepth_normalized 2 0).map completed) (some false) = 1 / 2 ∧
      ((law unequalDepth unequalDepth_normalized 2 0).map completed) none = 1 / 2 := by
  simp only [law_map_apply]
  norm_num [contributions, unequalDepth, WeightedResumption.sequence, completed,
    Option.some_ne_none]
  simp only [reduceCtorEq, if_false, zero_add]
  have arithmetic : (4 : ℝ≥0)⁻¹ + 4⁻¹ = 2⁻¹ := by norm_num
  have lifted := congrArg (fun value : ℝ≥0 => (value : ℝ≥0∞)) arithmetic
  simpa only [ENNReal.coe_add, ENNReal.coe_inv (by norm_num : (4 : ℝ≥0) ≠ 0),
    ENNReal.coe_inv (by norm_num : (2 : ℝ≥0) ≠ 0), ENNReal.coe_ofNat] using lifted

/-- Conditioning on the only completed answer would give it mass one, which
is not the law of this cut or of the completed computation. -/
theorem completed_only_is_not_the_cut :
    PMF.pure (some false) ≠ (law unequalDepth unequalDepth_normalized 2 0).map completed := by
  intro same
  have atFalse := congrArg (fun probability => probability (some false)) same
  rw [PMF.pure_apply_self, pending_mass_is_retained.1] at atFalse
  have realEquality := congrArg ENNReal.toReal atFalse
  norm_num at realEquality

noncomputable def repeated : Contributions Nat ℝ≥0 := [(7, 1 / 2), (7, 1 / 2), (8, 0)]

theorem repeated_normalized : total repeated = 1 := by
  norm_num [repeated, total, SemiringTraversal.weightSum]

/-- Probability forgets the third, zero-mass occurrence and combines the first
two. The operational list still contains all three physical occurrences. -/
theorem repeated_probability :
    ofContributions repeated repeated_normalized = PMF.pure 7 ∧
      eraseCoefficients repeated = [7, 7, 8] := by
  constructor
  · ext answer
    by_cases same : answer = 7 <;>
      simp [ofContributions_apply, repeated, PMF.pure_apply, same, eq_comm,
        ENNReal.inv_two_add_inv_two]
  · rfl

theorem empty_branch_not_normalized :
    ¬ Normalized (fun _ : Unit => Sum.inr ([] : Contributions Unit ℝ≥0) :
      Coalgebra Unit Nat ℝ≥0) := by
  intro normalized
  have impossible := normalized () [] rfl
  norm_num [total, SemiringTraversal.weightSum] at impossible

end Controls

end Mettapedia.GSLT.Dynamics.ProbabilisticResumption
