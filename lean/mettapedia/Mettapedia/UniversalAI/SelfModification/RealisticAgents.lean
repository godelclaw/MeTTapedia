import Mettapedia.UniversalAI.SelfModification.ValueFunctions
import Mettapedia.GSLT.Core.GSLT
import Mathlib.Data.Nat.Pairing

/-!
# Supported continuation optimality for finite named-policy execution

An optimal action maximizes weighted continuation value among available names.
Positive discount, positive branch weight, and the ability to patch that branch
then imply optimality of the next action for the remaining horizon. The invariant
propagates along actual supported execution paths, not arbitrary histories.

This is a finite analogue of Everitt et al. (2016), Theorem 16. It asserts neither
infinite-horizon optimality nor literal identity of policies under tied values.
-/

namespace Mettapedia.UniversalAI.SelfModification

open BayesianAgents
open scoped BigOperators

/-- Pointwise optimality compares all available extended actions. -/
def ActionOptimalAt (data : RealisticValueData) (h : History)
    (a : PolicyModAction) (n : ℕ) : Prop :=
  ∀ b, qValueRealistic data h b n ≤ qValueRealistic data h a n

def isRealisticOptimal (data : RealisticValueData) (π : SelfModPolicy) (horizon : ℕ) : Prop :=
  ∀ h : History, h.wellFormed →
    ∀ a : PolicyModAction, qValueRealistic data h a horizon ≤ qValueRealistic data h (π h) horizon

def isOptimalPolicyName (data : RealisticValueData) (p : PolicyName) (horizon : ℕ) : Prop :=
  isRealisticOptimal data (data.policyInterp p) horizon

def nextPolicyName (π : SelfModPolicy) (h : History) : PolicyName := (π h).nextPolicyName

/-- Expressivity at a single decision point, not naming of every infinite policy. -/
def BranchComplete (ι : PolicyInterpreter) : Prop :=
  ∀ (h : History) (a : Action) (table : Percept → PolicyModAction),
    ∃ p, ∀ e, ι p (nextHistory h a e) = table e

noncomputable def continuationValue (data : RealisticValueData) (h : History)
    (a : Action) (p : PolicyName) (n : ℕ) : ℝ :=
  ∑ e : Percept, branchWeight data.envProb h a e *
    qValueRealistic data (nextHistory h a e) (data.policyInterp p (nextHistory h a e)) n

theorem realistic_bellman_split (data : RealisticValueData) (h : History)
    (a : PolicyModAction) (n : ℕ) (valid : h.wellFormed) :
    qValueRealistic data h a (n+1) =
      (∑ e : Percept, branchWeight data.envProb h a.worldAction e *
        data.currentUtility (nextHistory h a.worldAction e)) +
      data.γ.val * continuationValue data h a.worldAction a.nextPolicyName n := by
  rw [qValueRealistic_succ data h a n valid]
  simp only [continuationValue, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro e _
  ring

/-- Name replacement preserves immediate reward, so parent optimality compares continuations. -/
theorem realistic_weighted_continuation (data : RealisticValueData) (h : History)
    (a : PolicyModAction) (n : ℕ) (valid : h.wellFormed) (discount : 0 < data.γ.val)
    (optimal : ActionOptimalAt data h a (n+1)) (p : PolicyName) :
    continuationValue data h a.worldAction p n ≤
      continuationValue data h a.worldAction a.nextPolicyName n := by
  have bound := optimal {a with nextPolicyName := p}
  rw [realistic_bellman_split data h _ n valid,
    realistic_bellman_split data h _ n valid] at bound
  exact le_of_mul_le_mul_left ((add_le_add_iff_left _).mp bound) discount

/-- A supported branch can be improved independently when the interpreter is branch-complete. -/
theorem realistic_continuation_optimal (data : RealisticValueData)
    (complete : BranchComplete data.policyInterp) (h : History) (a : PolicyModAction)
    (n : ℕ) (valid : h.wellFormed) (discount : 0 < data.γ.val)
    (optimal : ActionOptimalAt data h a (n+1)) (e : Percept)
    (supported : 0 < branchWeight data.envProb h a.worldAction e) :
    ActionOptimalAt data (nextHistory h a.worldAction e)
      (data.policyInterp a.nextPolicyName (nextHistory h a.worldAction e)) n := by
  intro b
  by_contra not_le
  have better := lt_of_not_ge not_le
  obtain ⟨p, patch⟩ := complete h a.worldAction (fun x =>
    if x = e then b else data.policyInterp a.nextPolicyName (nextHistory h a.worldAction x))
  have strict : continuationValue data h a.worldAction a.nextPolicyName n <
      continuationValue data h a.worldAction p n := by
    apply Finset.sum_lt_sum
    · intro x _
      rw [patch x]
      by_cases equal : x = e
      · subst x
        simp only [↓reduceIte]
        exact mul_le_mul_of_nonneg_left better.le supported.le
      · simp [equal]
    · refine ⟨e, Finset.mem_univ e, ?_⟩
      rw [patch e]
      simpa using mul_lt_mul_of_pos_left better supported
  exact (not_lt_of_ge (realistic_weighted_continuation data h a n valid discount optimal p)) strict

/-! ## A concrete branch-complete interpreter -/

private def actionCode : Action → ℕ | .left => 0 | .right => 1 | .stay => 2
private def codeAction (n : ℕ) : Action :=
  match n % 3 with | 0 => .left | 1 => .right | _ => .stay
private def packAction (a : PolicyModAction) : ℕ := Nat.pair (actionCode a.worldAction) a.nextPolicyName
private def unpackAction (n : ℕ) : PolicyModAction := ⟨codeAction (Nat.unpair n).1, (Nat.unpair n).2⟩

private theorem unpack_pack (a : PolicyModAction) : unpackAction (packAction a) = a := by
  rcases a with ⟨w,p⟩
  cases w <;> simp [unpackAction, packAction, actionCode, codeAction]

/-- Four finite action entries, including their arbitrary next-policy names. -/
def packTable (table : Percept → PolicyModAction) : PolicyName :=
  Nat.pair (packAction (table ⟨false,false⟩)) (Nat.pair (packAction (table ⟨false,true⟩))
    (Nat.pair (packAction (table ⟨true,false⟩)) (packAction (table ⟨true,true⟩))))

/-- Names encode a table indexed by the last percept, not all functions on histories. -/
def tableInterpreter (p : PolicyName) (h : History) : PolicyModAction :=
  let first := Nat.unpair p
  let second := Nat.unpair first.2
  let third := Nat.unpair second.2
  unpackAction (match h.percepts.getLast? with
    | some (.mk false false) => first.1
    | some (.mk false true) => second.1
    | some (.mk true false) => third.1
    | _ => third.2)

theorem tableInterpreter_branch (table : Percept → PolicyModAction)
    (h : History) (a : Action) (e : Percept) :
    tableInterpreter (packTable table) (nextHistory h a e) = table e := by
  rcases e with ⟨x,y⟩
  cases x <;> cases y <;>
    simp [tableInterpreter, packTable, nextHistory, History.percepts_append,
      History.percepts, unpack_pack]

theorem tableInterpreter_complete : BranchComplete tableInterpreter :=
  fun h a table => ⟨packTable table, tableInterpreter_branch table h a⟩

theorem tableInterpreter_constant (a : PolicyModAction) (h : History) :
    tableInterpreter (packTable (fun _ => a)) h = a := by
  simp only [tableInterpreter, packTable, Nat.unpair_pair]
  split <;> exact unpack_pack a

/-! ## Retained named-policy execution -/

structure ExecutionState where
  history : History
  policyName : PolicyName
  remaining : ℕ

/-- Functional interaction, retaining the installed name; support is checked separately. -/
def nextState (data : RealisticValueData) (state : ExecutionState) (e : Percept) : ExecutionState :=
  { history := nextHistory state.history (data.policyInterp state.policyName state.history).worldAction e
    policyName := (data.policyInterp state.policyName state.history).nextPolicyName
    remaining := state.remaining - 1 }

noncomputable def executionValue (data : RealisticValueData) (state : ExecutionState) : ℝ :=
  vValueRealistic data (data.policyInterp state.policyName) state.history state.remaining

/-- Evaluating the actual successor states gives precisely the Bellman observation. -/
theorem execution_bellman (data : RealisticValueData) (h : History) (p n : ℕ)
    (valid : h.wellFormed) :
    executionValue data ⟨h,p,n+1⟩ =
      ∑ e : Percept, branchWeight data.envProb h (data.policyInterp p h).worldAction e *
        (data.currentUtility (nextState data ⟨h,p,n+1⟩ e).history +
          data.γ.val * executionValue data (nextState data ⟨h,p,n+1⟩ e)) := by
  simpa only [executionValue, vValueRealistic, nextState, Nat.add_sub_cancel] using
    qValueRealistic_succ data h (data.policyInterp p h) n valid

/-- One actual interaction; zero remaining horizon has no transition. -/
inductive SupportedStep (data : RealisticValueData) : ExecutionState → ExecutionState → Prop where
  | interaction (h : History) (p n : ℕ) (e : Percept) (valid : DecisionHistory h)
      (supported : 0 < branchWeight data.envProb h (data.policyInterp p h).worldAction e) :
      SupportedStep data ⟨h,p,n+1⟩
        ⟨nextHistory h (data.policyInterp p h).worldAction e, (data.policyInterp p h).nextPolicyName, n⟩

theorem SupportedStep.successor {data : RealisticValueData} {source target : ExecutionState}
    (step : SupportedStep data source target) : ∃ e, target = nextState data source e := by
  cases step with
  | interaction h p n e _ _ => exact ⟨e,rfl⟩

def executionTheory (data : RealisticValueData) : Mettapedia.GSLT.GSLT where
  Term := ExecutionState
  equations := ⟨Eq, ⟨Eq.refl, Eq.symm, Eq.trans⟩⟩
  rewrites := SupportedStep data
  rewrites_resp_left := fun equal transition => by subst_vars; exact ⟨_, transition, rfl⟩
  rewrites_resp_right := fun transition equal => by subst_vars; exact transition

def ExecutionOptimal (data : RealisticValueData) (state : ExecutionState) : Prop :=
  ActionOptimalAt data state.history (data.policyInterp state.policyName state.history) state.remaining

theorem supported_step_optimal (data : RealisticValueData)
    (complete : BranchComplete data.policyInterp) (discount : 0 < data.γ.val)
    {source target : ExecutionState} (step : SupportedStep data source target)
    (optimal : ExecutionOptimal data source) : ExecutionOptimal data target := by
  cases step with
  | interaction h p n e valid supported =>
      exact realistic_continuation_optimal data complete h _ n valid.1 discount optimal e supported

/-- Every supported path preserves optimality, interpreted at its own remaining horizon. -/
theorem supported_path_optimal (data : RealisticValueData)
    (complete : BranchComplete data.policyInterp) (discount : 0 < data.γ.val)
    {source target : ExecutionState} (path : (executionTheory data).RewritePath source target) :
    ExecutionOptimal data source → ExecutionOptimal data target := by
  exact Mettapedia.GSLT.GSLT.RewritePath.rec (S := executionTheory data)
    (motive := fun source target _ => ExecutionOptimal data source → ExecutionOptimal data target)
    (fun _ => id)
    (fun step _ ih optimal => ih (supported_step_optimal data complete discount step optimal)) path

theorem supported_path_horizon (data : RealisticValueData)
    {source target : ExecutionState} (path : (executionTheory data).RewritePath source target) :
    source.remaining = target.remaining + path.length := by
  exact Mettapedia.GSLT.GSLT.RewritePath.rec (S := executionTheory data)
    (motive := fun source target path => source.remaining = target.remaining + path.length)
    (fun _ => by simp [Mettapedia.GSLT.GSLT.RewritePath.length])
    (fun step _ ih => by cases step; simp_all [Mettapedia.GSLT.GSLT.RewritePath.length]; omega) path

theorem supported_path_decision (data : RealisticValueData)
    {source target : ExecutionState} (path : (executionTheory data).RewritePath source target) :
    DecisionHistory source.history → DecisionHistory target.history := by
  exact Mettapedia.GSLT.GSLT.RewritePath.rec (S := executionTheory data)
    (motive := fun source target _ => DecisionHistory source.history → DecisionHistory target.history)
    (fun _ => id)
    (fun step _ ih => by cases step with
      | interaction h p n e valid _ => exact fun _ => ih (valid.next _ _)) path

/-! ## Separating controls -/

namespace Controls

noncomputable section

private theorem percept_card : Fintype.card Percept = 4 := by decide

def half : DiscountFactor := ⟨1/2, by norm_num, by norm_num⟩
def uniform : History → Percept → ENNReal := fun _ _ => 1/4

def rightUtility : Utility := fun h => match h.reverse with
  | HistElem.per _ :: HistElem.act .right :: _ => 1
  | _ => 0

theorem rightUtility_next (h : History) (a : Action) (e : Percept) :
    rightUtility (nextHistory h a e) = if a = .right then 1 else 0 := by
  cases a <;> simp [rightUtility, nextHistory, List.reverse_append]

theorem rightUtility_upper (h : History) : rightUtility h ≤ 1 := by
  unfold rightUtility
  split <;> norm_num

def exampleData (ι : PolicyInterpreter) (γ : DiscountFactor := half) : RealisticValueData :=
  ⟨uniform, ι, rightUtility, γ⟩

theorem uniform_rows : ProbabilityRows uniform := by
  intro h a _
  constructor
  · intro e; norm_num [uniform]
  · have card : Fintype.card Percept = 4 := by decide
    norm_num [uniform, card]
    exact ENNReal.mul_inv_cancel (by norm_num) (by norm_num)

/-- Horizon one observes the world action, independent of the continuation name. -/
theorem one_step (ι : PolicyInterpreter) (γ : DiscountFactor) (h : History)
    (valid : h.wellFormed) (a : PolicyModAction) :
    qValueRealistic (exampleData ι γ) h a 1 = if a.worldAction = .right then 1 else 0 := by
  rw [qValueRealistic_succ _ _ _ 0 valid, sum_percepts]
  simp only [qValueRealistic, finiteQ_zero, exampleData, branchWeight, uniform, rightUtility_next]
  split_ifs <;> norm_num

/-- Different codes can prescribe equal-value actions; changing a name need not reduce value. -/
theorem one_step_tie (ι : PolicyInterpreter) (p q : ℕ) :
    qValueRealistic (exampleData ι) [] ⟨.right,p⟩ 1 =
      qValueRealistic (exampleData ι) [] ⟨.right,q⟩ 1 := by
  rw [one_step ι half [] rfl, one_step ι half [] rfl]

def leftName : PolicyName := packTable (fun _ => ⟨.left,0⟩)
def rightName : PolicyName := packTable (fun _ => ⟨.right,0⟩)
def startName : PolicyName := packTable (fun _ => ⟨.right,rightName⟩)

/-- Full branch expressivity does not extend a one-step plan to a two-step guarantee. -/
theorem remaining_horizon_matters :
    ActionOptimalAt (exampleData tableInterpreter) [] ⟨.right,leftName⟩ 1 ∧
    ¬ ActionOptimalAt (exampleData tableInterpreter) (nextHistory [] .right ⟨false,false⟩)
      (tableInterpreter leftName (nextHistory [] .right ⟨false,false⟩)) 1 := by
  constructor
  · intro a
    rw [one_step tableInterpreter half [] rfl, one_step tableInterpreter half [] rfl]
    norm_num only [PolicyModAction.worldAction, ↓reduceIte]
    split_ifs <;> norm_num
  · intro optimal
    have bad := optimal ⟨.right,0⟩
    rw [show tableInterpreter leftName (nextHistory [] .right ⟨false,false⟩) =
      ⟨.left,0⟩ by exact tableInterpreter_branch _ _ _ _] at bad
    rw [one_step tableInterpreter half _ rfl, one_step tableInterpreter half _ rfl] at bad
    simp at bad
    linarith


def restricted : PolicyInterpreter := fun _ _ => ⟨.left,0⟩

theorem restricted_two_step (h : History) (valid : DecisionHistory h) (a : PolicyModAction) :
    qValueRealistic (exampleData restricted) h a 2 = if a.worldAction = .right then 1 else 0 := by
  have future (e : Percept) : qValueRealistic (exampleData restricted)
      (nextHistory h a.worldAction e) (restricted a.nextPolicyName (nextHistory h a.worldAction e)) 1 = 0 := by
    rw [one_step restricted half _ (valid.next _ _).1]
    simp [restricted]
  rw [qValueRealistic_succ _ _ _ 1 valid.1]
  have reduced : ∀ e, qValueRealistic (exampleData restricted) (nextHistory h a.worldAction e)
      ((exampleData restricted).policyInterp a.nextPolicyName (nextHistory h a.worldAction e)) 1 = 0 := future
  simp_rw [reduced]
  rw [sum_percepts]
  simp only [exampleData, branchWeight, uniform, rightUtility_next, mul_zero, add_zero]
  split_ifs <;> norm_num

/-- Optimality among available names need not yield an optimal successor action. -/
theorem restricted_names_fail :
    ActionOptimalAt (exampleData restricted) [] ⟨.right,0⟩ 2 ∧
    ¬ ActionOptimalAt (exampleData restricted) (nextHistory [] .right ⟨false,false⟩) ⟨.left,0⟩ 1 ∧
    ¬ BranchComplete restricted := by
  refine ⟨?_, ?_, ?_⟩
  · intro a
    rw [restricted_two_step [] ⟨rfl,rfl⟩, restricted_two_step [] ⟨rfl,rfl⟩]
    simp only [↓reduceIte]
    split_ifs <;> norm_num
  · intro optimal
    have bad := optimal ⟨.right,0⟩
    rw [one_step restricted half _ rfl, one_step restricted half _ rfl] at bad
    simp at bad
    linarith
  · intro complete
    obtain ⟨p, eq⟩ := complete [] .right (fun _ => ⟨.right,0⟩)
    have bad := congrArg PolicyModAction.worldAction (eq ⟨false,false⟩)
    cases bad

/-- A positive-weight successor can be bad when future reward is discounted by zero. -/
theorem zero_discount_fail :
    let data := exampleData tableInterpreter ⟨0,by norm_num,by norm_num⟩
    ActionOptimalAt data [] ⟨.right,leftName⟩ 2 ∧
    ¬ ActionOptimalAt data (nextHistory [] .right ⟨false,false⟩) ⟨.left,0⟩ 1 := by
  dsimp only
  constructor
  · intro a
    change finiteQ _ _ _ _ 2 ≤ finiteQ _ _ _ _ 2
    rw [finiteQ_zero_discount _ _ _ _ 1 rfl, finiteQ_zero_discount _ _ _ _ 1 rfl]
    change qValueRealistic _ _ _ 1 ≤ qValueRealistic _ _ _ 1
    rw [one_step _ _ [] rfl, one_step _ _ [] rfl]
    simp only [↓reduceIte]
    split_ifs <;> norm_num
  · intro optimal
    have bad := optimal ⟨.right,0⟩
    rw [one_step _ _ _ rfl, one_step _ _ _ rfl] at bad
    simp at bad
    linarith

/-- Finite return can be nonzero, and depends on the installed continuation name. -/
theorem table_two_step (h : History) (valid : DecisionHistory h) (a : Action)
    (table : Percept → PolicyModAction) :
    qValueRealistic (exampleData tableInterpreter) h ⟨a,packTable table⟩ 2 =
      (if a = .right then 1 else 0) +
        (1/2 : ℝ) * ∑ e : Percept, (1/4 : ℝ) * (if (table e).worldAction = .right then 1 else 0) := by
  rw [realistic_bellman_split _ _ _ 1 valid.1]
  congr 1
  · rw [sum_percepts]
    simp only [exampleData, branchWeight, uniform, rightUtility_next]
    split_ifs <;> norm_num
  · unfold continuationValue
    change half.val * (∑ e : Percept, branchWeight uniform h a e *
      qValueRealistic (exampleData tableInterpreter) (nextHistory h a e)
        (tableInterpreter (packTable table) (nextHistory h a e)) 1) = _
    change (1/2 : ℝ) * _ = _
    congr 1
    apply Finset.sum_congr rfl
    intro e _
    rw [tableInterpreter_branch, one_step tableInterpreter half _ (valid.next _ _).1]
    norm_num [branchWeight, uniform]

/-- The world-history observer loses policy information relevant to the next return. -/
theorem world_history_loses_value :
    let h := nextHistory [] .right ⟨false,false⟩
    qValueRealistic (exampleData tableInterpreter) h (tableInterpreter leftName h) 1 = 0 ∧
    qValueRealistic (exampleData tableInterpreter) h (tableInterpreter rightName h) 1 = 1 := by
  dsimp only
  rw [show tableInterpreter leftName _ = ⟨.left,0⟩ by exact tableInterpreter_branch _ _ _ _,
    show tableInterpreter rightName _ = ⟨.right,0⟩ by exact tableInterpreter_branch _ _ _ _]
  rw [one_step tableInterpreter half _ rfl, one_step tableInterpreter half _ rfl]
  simp

/-- Two actual rewards are collected under two successive installed policy names. -/
theorem nonzero_performance :
    agentPerformance ⟨startName,tableInterpreter,uniform⟩ rightUtility half 2 = 3/2 := by
  change qValueRealistic (exampleData tableInterpreter) [] (tableInterpreter startName []) 2 = _
  rw [startName, tableInterpreter_constant ⟨.right,rightName⟩ [], rightName,
    table_two_step [] ⟨rfl,rfl⟩]
  rw [sum_percepts]
  norm_num


def pointMass : History → Percept → ENNReal := fun _ e => if e = ⟨false,false⟩ then 1 else 0
def pointData : RealisticValueData := {exampleData tableInterpreter with envProb := pointMass}

theorem point_rows : ProbabilityRows pointMass := by
  intro h a _
  constructor
  · intro e; simp only [pointMass]; split_ifs <;> norm_num
  · rw [sum_percepts]; norm_num [pointMass]

theorem point_bellman (h : History) (valid : h.wellFormed) (a : PolicyModAction) (n : ℕ) :
    qValueRealistic pointData h a (n+1) =
      rightUtility (nextHistory h a.worldAction ⟨false,false⟩) + half.val *
        qValueRealistic pointData (nextHistory h a.worldAction ⟨false,false⟩)
          (tableInterpreter a.nextPolicyName (nextHistory h a.worldAction ⟨false,false⟩)) n := by
  rw [qValueRealistic_succ _ _ _ n valid, sum_percepts]
  simp [List.foldl, pointData, exampleData, branchWeight, pointMass]

theorem point_one_step (h : History) (valid : h.wellFormed) (a : PolicyModAction) :
    qValueRealistic pointData h a 1 = if a.worldAction = .right then 1 else 0 := by
  rw [qValueRealistic_succ _ _ _ 0 valid, sum_percepts]
  simp [pointData, exampleData, branchWeight, pointMass, qValueRealistic, finiteQ_zero,
    rightUtility_next]

/-- The zero-probability percept can select a bad continuation in an optimal parent. -/
theorem unsupported_branch_fail :
    let table : Percept → PolicyModAction := fun e =>
      if e = ⟨false,false⟩ then ⟨.right,0⟩ else ⟨.left,0⟩
    ActionOptimalAt pointData [] ⟨.right,packTable table⟩ 2 ∧
    branchWeight pointMass [] .right ⟨false,true⟩ = 0 ∧
    ¬ ActionOptimalAt pointData (nextHistory [] .right ⟨false,true⟩)
      (tableInterpreter (packTable table) (nextHistory [] .right ⟨false,true⟩)) 1 := by
  dsimp only
  have value : qValueRealistic pointData [] ⟨.right,packTable (fun e =>
      if e = ⟨false,false⟩ then ⟨.right,0⟩ else ⟨.left,0⟩)⟩ 2 = 3/2 := by
    rw [point_bellman [] rfl _ 1, tableInterpreter_branch]
    simp only [↓reduceIte]
    rw [point_one_step (nextHistory [] .right ⟨false,false⟩) rfl]
    norm_num [half, rightUtility_next]

  refine ⟨?_, by simp [branchWeight, pointMass], ?_⟩
  · intro a
    rw [value]
    have bound := finiteQ_le_returnBound pointData.toFinite rightUtility rightUtility_upper
      point_rows [] ⟨rfl,rfl⟩ a 2
    convert bound using 1 <;>
      norm_num [qValueRealistic, returnBound, pointData, exampleData, RealisticValueData.toFinite, half]
  · intro optimal
    have bad := optimal ⟨.right,0⟩
    rw [tableInterpreter_branch] at bad
    norm_num only [Percept.mk.injEq, Bool.false_eq_true, and_false, ↓reduceIte] at bad
    rw [point_one_step _ rfl, point_one_step _ rfl] at bad
    simp at bad
    linarith

/-- A concrete two-step path changes the active name and exhausts exactly two cycles. -/
def twoStepPath : (executionTheory (exampleData tableInterpreter)).RewritePath
    ⟨[],startName,2⟩ ⟨nextHistory (nextHistory [] .right ⟨false,false⟩) .right ⟨false,false⟩,0,0⟩ := by
  have first : (exampleData tableInterpreter).policyInterp startName [] = ⟨.right,rightName⟩ := by
    simpa only [exampleData, startName] using tableInterpreter_constant ⟨.right,rightName⟩ []
  have second : (exampleData tableInterpreter).policyInterp rightName (nextHistory [] .right ⟨false,false⟩) =
      ⟨.right,0⟩ := by
        simpa only [exampleData, rightName] using
          tableInterpreter_branch (fun _ => ⟨.right,0⟩) [] .right ⟨false,false⟩
  refine .cons (SupportedStep.interaction [] startName 1 ⟨false,false⟩ ⟨rfl,rfl⟩ ?_) ?_
  · norm_num [exampleData, branchWeight, uniform]
  · rw [first]
    refine .cons (SupportedStep.interaction _ rightName 0 ⟨false,false⟩ ⟨rfl,rfl⟩ ?_) ?_
    · norm_num [exampleData, branchWeight, uniform]
    · rw [second]
      exact .nil _

theorem two_step_optimal :
    ExecutionOptimal (exampleData tableInterpreter) ⟨[],startName,2⟩ ∧
    ExecutionOptimal (exampleData tableInterpreter)
      ⟨nextHistory (nextHistory [] .right ⟨false,false⟩) .right ⟨false,false⟩,0,0⟩ ∧
    twoStepPath.length = 2 := by
  have optimal : ExecutionOptimal (exampleData tableInterpreter) ⟨[],startName,2⟩ := by
    intro a
    change qValueRealistic (exampleData tableInterpreter) [] a 2 ≤
      agentPerformance ⟨startName,tableInterpreter,uniform⟩ rightUtility half 2
    rw [nonzero_performance]
    have bound := finiteQ_le_returnBound (exampleData tableInterpreter).toFinite rightUtility
      rightUtility_upper uniform_rows [] ⟨rfl,rfl⟩ a 2
    convert bound using 1 <;>
      norm_num [qValueRealistic, returnBound, exampleData, RealisticValueData.toFinite, half]
  exact ⟨optimal, supported_path_optimal _ tableInterpreter_complete (by norm_num [exampleData,half])
    twoStepPath optimal, by have := supported_path_horizon _ twoStepPath; simpa using this.symm⟩


/-- This utility changes which action is desirable after the unchosen first action. -/
def offUtility : Utility := fun h => match h with
  | [HistElem.act .left, HistElem.per _, HistElem.act .left, HistElem.per _] => 1
  | [HistElem.act .left, HistElem.per _, HistElem.act .right, HistElem.per _] => 0
  | _ => rightUtility h

def offData : RealisticValueData := {exampleData tableInterpreter with currentUtility := offUtility}

theorem offUtility_upper (h : History) : offUtility h ≤ 1 := by
  unfold offUtility
  split <;> try norm_num
  exact rightUtility_upper h

/-- A reached-optimal named policy can still be bad after an unchosen world action. -/
theorem off_policy_fail :
    ActionOptimalAt offData [] ⟨.right,rightName⟩ 2 ∧
    ¬ ActionOptimalAt offData (nextHistory [] .left ⟨false,false⟩)
      (tableInterpreter rightName (nextHistory [] .left ⟨false,false⟩)) 1 := by
  have value : qValueRealistic offData [] ⟨.right,rightName⟩ 2 = 3/2 := by
    norm_num [qValueRealistic, finiteQ, RealisticValueData.toFinite, offData, exampleData,
      sum_percepts, rightName, tableInterpreter_constant, branchWeight, uniform,
      nextHistory, offUtility, rightUtility, half, History.wellFormed, percept_card]
  constructor
  · intro a
    rw [value]
    have bound := finiteQ_le_returnBound offData.toFinite offUtility offUtility_upper
      uniform_rows [] ⟨rfl,rfl⟩ a 2
    convert bound using 1 <;>
      norm_num [qValueRealistic, returnBound, offData, exampleData, RealisticValueData.toFinite, half]
  · intro optimal
    have bad := optimal ⟨.left,0⟩
    rw [show tableInterpreter rightName (nextHistory [] .left ⟨false,false⟩) =
      ⟨.right,0⟩ by exact tableInterpreter_branch _ _ _ _] at bad
    norm_num [qValueRealistic, finiteQ, RealisticValueData.toFinite, offData, exampleData,
      sum_percepts, branchWeight, uniform, nextHistory, offUtility, rightUtility,
      History.wellFormed, percept_card] at bad

/-- Tied continuations can disagree on a later policy name at a nonzero horizon. -/
theorem nonzero_continuation_tie :
    qValueRealistic (exampleData tableInterpreter) [] ⟨.right,rightName⟩ 2 =
      qValueRealistic (exampleData tableInterpreter) []
        ⟨.right,packTable (fun _ => ⟨.right,1⟩)⟩ 2 := by
  rw [rightName, table_two_step [] ⟨rfl,rfl⟩, table_two_step [] ⟨rfl,rfl⟩]

/-- A zero coefficient at infinity is not a nonzero probability branch. -/
theorem infinite_coefficient_erased :
    branchWeight (fun _ _ => ⊤) [] .right ⟨false,false⟩ = 0 := by
  simp [branchWeight]

end

end Controls

end Mettapedia.UniversalAI.SelfModification
