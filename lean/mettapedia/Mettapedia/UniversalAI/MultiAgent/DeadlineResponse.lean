import Mettapedia.UniversalAI.MultiAgent.BestResponse

/-!
# Best response to a fixed terminal cycle

The existing response replans with the same lookahead at every decision. Here the
terminal cycle is fixed and the remaining horizon decreases. Full-history Q-values
must still factor through the player's view; a clock cannot recover hidden information.
The finite evaluation ends at the deadline; the total policy then uses a zero-horizon choice.
The selector is mathematical and real-valued, without an effectiveness claim.
-/

set_option autoImplicit false

namespace Mettapedia.UniversalAI.MultiAgent

variable {n : ℕ}

open BayesianAgents

namespace MultiAgentHistory

/-- A player's view retains the interaction clock, even when it forgets other players. -/
theorem cycles_playerView {n : ℕ} (i : Fin n) (h : MultiAgentHistory n)
    (hw : h.wellFormed = true) : (h.playerView i).cycles = h.cycles := by
  match h with
  | [] => simp [playerView, History.cycles, History.percepts, cycles]
  | [.act _] => simp [playerView, JointHistElem.playerView, History.cycles, History.percepts, cycles]
  | .act _ :: .per _ :: rest =>
      have ih := cycles_playerView i rest hw
      simp only [playerView, List.map_cons, JointHistElem.playerView, History.cycles,
        History.percepts, List.length_cons, cycles] at ih ⊢
      omega
  | .per _ :: _ => simp only [wellFormed] at hw; cases hw
  | .act _ :: .act _ :: _ => simp only [wellFormed] at hw; cases hw
termination_by h.length

/-- Every complete interaction advances elapsed time by one. -/
theorem cycles_append_interaction {n : ℕ} (h : MultiAgentHistory n)
    (ja : JointAction n) (jp : JointPercept n) :
    (h ++ [JointHistElem.act ja, JointHistElem.per jp]).cycles = h.cycles + 1 := by
  simp only [cycles, List.length_append, List.length_cons, List.length_nil]
  omega

end MultiAgentHistory

/-- A response with terminal cycle `deadline`, measured in the player's own history. -/
noncomputable def deadlineResponseAgent (μ : MultiAgentEnvironment n) (i : Fin n)
    (others : (j : Fin n) → j ≠ i → Agent) (γ : DiscountFactor) (deadline : ℕ) : Agent where
  policy := fun h => (bestResponseAgent μ i others γ (deadline - h.cycles)).policy h
  policy_sum_one := fun h hw =>
    (bestResponseAgent μ i others γ (deadline - h.cycles)).policy_sum_one h hw

theorem deadlineResponseAgent_policy_toReal (μ : MultiAgentEnvironment n) (i : Fin n)
    (others : (j : Fin n) → j ≠ i → Agent) (γ : DiscountFactor) (D : ℕ)
    (h : History) (a : Action) :
    ((deadlineResponseAgent μ i others γ D).policy h a).toReal =
      if a = bestResponsePolicy μ (multiAgentPolicyFromOthers i others) γ i
        (D - h.cycles) h then 1 else 0 :=
  bestResponseAgent_policy_toReal μ i others γ (D - h.cycles) h a

/-- Backward induction with the invariant `elapsed + remaining = deadline`.
No relation between maximizers at different horizons is assumed. -/
theorem deadlineResponseAgent_optimal (μ : MultiAgentEnvironment n) (π : MultiAgentPolicy n)
    (γ : DiscountFactor) (i : Fin n) (D : ℕ)
    (full : playerIQValueDependsOnlyOnOwnView μ π γ i)
    (k : ℕ) (h : MultiAgentHistory n) (hw : h.wellFormed = true)
    (hep : h.endsWithPercept = true) (clock : h.cycles + k = D) :
    playerValue μ (π.updateAgent i (deadlineResponseAgent μ i (fun j _ => π.agents j) γ D))
      γ i h k = bestResponseValue μ π γ i h k := by
  let canon := multiAgentPolicyFromOthers i (fun j _ => π.agents j)
  have canon_eq : canon = π.updateAgent i uniformAgent := multiAgentPolicyFromOthers_eq_update π i
  apply playerValue_eq_bestResponseValue_on μ π _ γ i
    (fun j different => by simp [MultiAgentPolicy.updateAgent, different])
    (fun h k => h.cycles + k = D) ?_ ?_ k h hw hep clock
  · intro h k ja jp state
    rw [MultiAgentHistory.cycles_append_interaction]
    omega
  · intro h k hw hep state
    have remaining : D - (h.playerView i).cycles = k+1 := by
      rw [MultiAgentHistory.cycles_playerView i h hw]
      omega
    refine ⟨bestResponsePolicy μ canon γ i (k+1) (h.playerView i), ?_, ?_⟩
    · intro a
      simp only [MultiAgentPolicy.updateAgent, ↓reduceIte,
        deadlineResponseAgent_policy_toReal, remaining, canon]
    · apply isSupAchievingAt_of_playerView μ π γ i h hw hep full
      have optimal := bestResponsePolicy_isSupAchieving μ canon γ i (h.playerView i) (k+1)
      simpa only [isSupAchievingAt, canon_eq, bestResponseQValue_updateAgent_eq] using optimal

/-- The deadline policy realizes the optimum throughout the remaining interval,
including the zero interval at or after its deadline. -/
theorem deadlineResponseAgent_maximizes_value (μ : MultiAgentEnvironment n)
    (π : MultiAgentPolicy n) (γ : DiscountFactor) (i : Fin n) (D : ℕ)
    (full : playerIQValueDependsOnlyOnOwnView μ π γ i) (h : MultiAgentHistory n)
    (hw : h.wellFormed = true) (hep : h.endsWithPercept = true) :
    playerValue μ (π.updateAgent i (deadlineResponseAgent μ i (fun j _ => π.agents j) γ D))
      γ i h (D - h.cycles) = bestResponseValue μ π γ i h (D - h.cycles) := by
  by_cases past : D ≤ h.cycles
  · simp only [Nat.sub_eq_zero_of_le past, playerValue, bestResponseValue_zero]
  · exact deadlineResponseAgent_optimal μ π γ i D full _ h hw hep (by omega)

theorem deadlineResponseAgent_improves_value (μ : MultiAgentEnvironment n)
    (π : MultiAgentPolicy n) (γ : DiscountFactor) (i : Fin n) (D : ℕ)
    (full : playerIQValueDependsOnlyOnOwnView μ π γ i) (h : MultiAgentHistory n)
    (hw : h.wellFormed = true) (hep : h.endsWithPercept = true) :
    playerValue μ π γ i h (D - h.cycles) ≤
      playerValue μ (π.updateAgent i (deadlineResponseAgent μ i (fun j _ => π.agents j) γ D))
        γ i h (D - h.cycles) := by
  rw [deadlineResponseAgent_maximizes_value μ π γ i D full h hw hep]
  exact playerValue_le_bestResponseValue μ π γ i h hw hep _

namespace DeadlineControls

open Classical in
/-- A binary sample is pushed forward with occurrences retained, including collisions. -/
noncomputable def binaryEnvironment (outcome : MultiAgentHistory n → Bool → JointPercept n) :
    MultiAgentEnvironment n where
  prob := fun h jp => ∑ b : Bool, if jp = outcome h b then (1 / 2 : ENNReal) else 0
  prob_le_one := by
    classical
    intro h _
    simp only [tsum_fintype]
    rw [Finset.sum_comm]
    norm_num

theorem binary_expectation (outcome : MultiAgentHistory n → Bool → JointPercept n)
    (h : MultiAgentHistory n) (f : JointPercept n → ℝ) :
    (∑ jp, ((binaryEnvironment outcome).prob h jp).toReal * f jp) =
      (f (outcome h false) + f (outcome h true)) / 2 := by
  classical
  have finite (jp : JointPercept n) (b : Bool) :
      (if jp = outcome h b then (1 / 2 : ENNReal) else 0) ≠ ⊤ := by split_ifs <;> norm_num
  simp only [binaryEnvironment, ENNReal.toReal_sum (fun b _ => finite _ b), Finset.sum_mul]
  rw [Finset.sum_comm]
  simp only [apply_ite ENNReal.toReal, ENNReal.toReal_zero, ite_mul, zero_mul]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  norm_num [Fintype.sum_bool]
  ring

noncomputable def fixedProfile (n : ℕ) : MultiAgentPolicy n := ⟨fun _ => constantAgent .left⟩

/-- For constant opponents, the action guard leaves exactly one joint action. -/
theorem fixed_step (μ : MultiAgentEnvironment n) (γ : DiscountFactor) (i : Fin n)
    (h : MultiAgentHistory n) (a : Action) (v : MultiAgentHistory n → ℝ) :
    actionValueStep μ (fixedProfile n) γ i h a v =
      ∑ jp, (μ.prob (h ++ [.act (Function.update (fun _ => .left) i a)]) jp).toReal *
        ((jp i).reward + γ.val * v (h ++ [.act (Function.update (fun _ => .left) i a), .per jp])) := by
  classical
  let chosen : JointAction n := Function.update (fun _ => .left) i a
  have weight : othersProb (fixedProfile n) h chosen i = 1 := by
    apply Finset.prod_eq_one
    intro j member
    simp [fixedProfile, constantAgent, chosen, Function.update_of_ne (Finset.mem_erase.mp member).1]
  simp only [actionValueStep, tsum_fintype]
  rw [Finset.sum_eq_single chosen]
  · simp [chosen, weight]
  · intro ja _ different
    by_cases own : ja i = a
    · have other : ∃ j, j ≠ i ∧ ja j ≠ Action.left := by
        by_contra absent
        push Not at absent
        apply different
        funext j
        by_cases same : j = i
        · subst j; simpa [chosen] using own
        · simpa [chosen, Function.update_of_ne same] using absent j same
      obtain ⟨j, other, different⟩ := other
      have zero : othersProb (fixedProfile n) h ja i = 0 :=
        Finset.prod_eq_zero (i := j) (by simp [other]) (by simp [fixedProfile, constantAgent, different])
      simp [own, zero]
    · simp [own]
  · simp

/-- The finite row interpreter agrees with direct averaging over the two samples. -/
theorem binary_step (outcome : MultiAgentHistory n → Bool → JointPercept n)
    (γ : DiscountFactor) (i : Fin n) (h : MultiAgentHistory n) (a : Action)
    (v : MultiAgentHistory n → ℝ) :
    actionValueStep (binaryEnvironment outcome) (fixedProfile n) γ i h a v =
      (∑ b : Bool, ((outcome (h ++ [.act (Function.update (fun _ => .left) i a)]) b i).reward +
        γ.val * v (h ++ [.act (Function.update (fun _ => .left) i a),
          .per (outcome (h ++ [.act (Function.update (fun _ => .left) i a)]) b)]))) / 2 := by
  rw [fixed_step, binary_expectation]
  simp only [Fintype.sum_bool]
  ring

theorem action_sup (f : Action → ℝ) : (⨆ a, f a) = max (f .left) (max (f .right) (f .stay)) := by
  have bounded := Set.Finite.bddAbove (Set.finite_range f)
  apply le_antisymm
  · apply ciSup_le; intro a; cases a <;> simp
  · exact max_le (le_ciSup bounded _) (max_le (le_ciSup bounded _) (le_ciSup bounded _))

noncomputable def discount : DiscountFactor := ⟨3/4, by norm_num, by norm_num⟩
def middle (a : Action) : MultiAgentHistory 1 := [.act (fun _ => a), .per (fun _ => .mk false false)]

/-- Safe action pays a fair bit now; investment pays one cycle later. -/
def delayedOutcome : MultiAgentHistory 1 → Bool → JointPercept 1
  | [.act _, .per _, .act a], b => fun _ => .mk false (if a 0 = .left then b else false)
  | [.act _, .per _, .act previous, .per _, .act _], _ =>
      fun _ => .mk false (previous 0 == .right)
  | _, _ => fun _ => .mk false false

noncomputable abbrev delayed := binaryEnvironment delayedOutcome

private theorem one_joint (a : Action) :
    Function.update (fun _ : Fin 1 => Action.left) 0 a = fun _ => a :=
  Function.update_eq_const_of_subsingleton 0 a (fun _ => Action.left)

private theorem delayed_middle (first a : Action) (b : Bool) :
    delayedOutcome (middle first ++ [.act (fun _ => a)]) b =
      fun _ => Percept.mk false (if a = .left then b else false) := rfl

private theorem delayed_future (first second a : Action) (jp : JointPercept 1) (b : Bool) :
    delayedOutcome ((middle first ++ [.act (fun _ => second), .per jp]) ++ [.act (fun _ => a)]) b =
      fun _ => Percept.mk false (second == .right) := rfl

private theorem future_value (first second : Action) (jp : JointPercept 1) :
    bestResponseValue delayed (fixedProfile 1) discount 0
      (middle first ++ [.act (fun _ => second), .per jp]) 1 = if second = .right then 1 else 0 := by
  have each (a : Action) : bestResponseQValue delayed (fixedProfile 1) discount 0
      (middle first ++ [.act (fun _ => second), .per jp]) a 1 =
      if second = .right then 1 else 0 := by
    rw [bestResponseQValue_succ, delayed, binary_step]
    simp only [bestResponseValue_zero, mul_zero, add_zero,
      one_joint]
    rw [Fintype.sum_bool]
    simp only [delayed_future, Percept.reward]
    cases second <;> norm_num
  rw [bestResponseValue]
  simp only [each, ciSup_const]

theorem delayed_q_one (first a : Action) :
    bestResponseQValue delayed (fixedProfile 1) discount 0 (middle first) a 1 =
      if a = .left then 1/2 else 0 := by
  rw [bestResponseQValue_succ, delayed, binary_step]
  simp only [bestResponseValue_zero, mul_zero, add_zero,
    one_joint]
  rw [Fintype.sum_bool]
  simp only [delayed_middle, Percept.reward]
  split_ifs <;> norm_num <;> contradiction

theorem delayed_q_two (first a : Action) :
    bestResponseQValue delayed (fixedProfile 1) discount 0 (middle first) a 2 =
      if a = .right then 3/4 else if a = .left then 1/2 else 0 := by
  rw [bestResponseQValue_succ, delayed, binary_step]
  simp only [one_joint, future_value]
  by_cases left : a = Action.left
  · subst a
    have right : Action.left ≠ Action.right := by decide
    norm_num [delayed_middle, Percept.reward, discount, Fintype.sum_bool, right]
  · by_cases right : a = Action.right
    · subst a
      have different : Action.right ≠ Action.left := by decide
      norm_num [delayed_middle, Percept.reward, discount, Fintype.sum_bool, different]
    · norm_num [delayed_middle, Percept.reward, discount, Fintype.sum_bool, left, right]

private theorem one_view_inverse (h : MultiAgentHistory 1) :
    historyToMultiAgent 0 (h.playerView 0) = h := by
  have single {α : Type} [Inhabited α] (f : Fin 1 → α) :
      (fun j : Fin 1 => if j = 0 then f 0 else default) = f := by
    funext j
    have same : j = 0 := Subsingleton.elim _ _
    subst j
    simp
  induction h with
  | nil => rfl
  | cons e rest ih =>
      cases e with
      | act ja => exact congrArg₂ List.cons (congrArg JointHistElem.act (single ja)) ih
      | per jp => exact congrArg₂ List.cons (congrArg JointHistElem.per (single jp)) ih

private theorem one_full (μ : MultiAgentEnvironment 1) (π : MultiAgentPolicy 1) (γ : DiscountFactor) :
    playerIQValueDependsOnlyOnOwnView μ π γ 0 := by
  intro h h' a k _ _ equal
  have same : h = h' := by rw [← one_view_inverse h, ← one_view_inverse h', equal]
  rw [same]

private theorem middle_value (first : Action) :
    bestResponseValue delayed (fixedProfile 1) discount 0 (middle first) 1 = 1/2 := by
  rw [bestResponseValue, action_sup]
  simp only [delayed_q_one]
  have right : Action.right ≠ Action.left := by decide
  have stay : Action.stay ≠ Action.left := by decide
  norm_num [right, stay]

/-- Two-step lookahead invests at the penultimate decision, beyond the terminal cycle. -/
theorem rolling_selects_investment (first : Action) :
    bestResponsePolicy delayed (multiAgentPolicyFromOthers 0 (fun j _ => (fixedProfile 1).agents j))
      discount 0 2 ((middle first).playerView 0) = .right := by
  let canon := multiAgentPolicyFromOthers 0 (fun j _ => (fixedProfile 1).agents j)
  let chosen := bestResponsePolicy delayed canon discount 0 2 ((middle first).playerView 0)
  have table (a : Action) : bestResponseQValue delayed canon discount 0
      (historyToMultiAgent 0 ((middle first).playerView 0)) a 2 =
        if a = .right then 3/4 else if a = .left then 1/2 else 0 := by
    dsimp only [canon]
    rw [one_view_inverse, multiAgentPolicyFromOthers_eq_update, bestResponseQValue_updateAgent_eq]
    exact delayed_q_two first a
  have optimal := Classical.choose_spec (bestResponsePolicy.exists_best_action delayed canon discount 0
    ((middle first).playerView 0) 2) .right
  change bestResponseQValue delayed canon discount 0 _ chosen 2 ≥ _ at optimal
  simp only [table] at optimal
  by_contra different
  rw [if_neg different] at optimal
  split_ifs at optimal <;> norm_num at optimal

noncomputable abbrev rolling : Agent :=
  bestResponseAgent delayed 0 (fun j _ => (fixedProfile 1).agents j) discount 2

private theorem rolling_middle (first : Action) :
    playerValue delayed ((fixedProfile 1).updateAgent 0 rolling) discount 0 (middle first) 1 = 0 := by
  rw [playerValue_deterministic delayed _ discount 0 _ (by rfl) .right]
  · rw [playerQValue_one_eq_updateAgent, playerQValue_one_eq_bestResponseQValue, delayed_q_one]
    have different : Action.right ≠ Action.left := by decide
    simp [different]
  · intro a
    simp only [MultiAgentPolicy.updateAgent, ↓reduceIte, bestResponseAgent_policy_toReal,
      rolling_selects_investment]

/-- Fixed terminal time changes a real payoff, rather than merely renaming a maximizer. -/
theorem deadline_middle (first : Action) :
    playerValue delayed ((fixedProfile 1).updateAgent 0
      (deadlineResponseAgent delayed 0 (fun j _ => (fixedProfile 1).agents j) discount 2))
      discount 0 (middle first) 1 = 1/2 := by
  rw [deadlineResponseAgent_optimal delayed _ discount 0 2 (one_full _ _ _)
    1 (middle first) (by rfl) (by rfl) (by simp [middle, MultiAgentHistory.cycles])]
  exact middle_value first

private theorem delayed_initial (a : Action) (b : Bool) :
    delayedOutcome [.act (fun _ => a)] b = fun _ => Percept.mk false false := rfl

/-- Constant lookahead receives nothing before the two-cycle deadline. -/
theorem rolling_initial :
    playerValue delayed ((fixedProfile 1).updateAgent 0 rolling) discount 0 [] 2 = 0 := by
  have each (a : Action) : playerQValue delayed ((fixedProfile 1).updateAgent 0 rolling)
      discount 0 [] a 2 = 0 := by
    rw [playerQValue_succ, actionValueStep_updateAgent_eq, binary_step]
    simp only [one_joint, List.nil_append, delayed_initial]
    change (∑ _ : Bool, (0 + discount.val * playerValue delayed
      ((fixedProfile 1).updateAgent 0 rolling) discount 0 (middle a) 1)) / 2 = 0
    rw [rolling_middle]
    norm_num
  rw [playerValue_eq_weighted_qValue]
  simp only [each, mul_zero, Finset.sum_const_zero]

private theorem initial_optimum : bestResponseValue delayed (fixedProfile 1) discount 0 [] 2 = 3/8 := by
  have each (a : Action) : bestResponseQValue delayed (fixedProfile 1) discount 0 [] a 2 = 3/8 := by
    rw [bestResponseQValue_succ, binary_step]
    simp only [one_joint, List.nil_append, delayed_initial]
    change (∑ _ : Bool, (0 + discount.val * bestResponseValue delayed
      (fixedProfile 1) discount 0 (middle a) 1)) / 2 = 3/8
    rw [middle_value]
    norm_num [discount]
  rw [bestResponseValue]
  simp only [each, ciSup_const]

/-- The fixed deadline attains the actual optimum, discounted from the initial history. -/
theorem deadline_initial :
    playerValue delayed ((fixedProfile 1).updateAgent 0
      (deadlineResponseAgent delayed 0 (fun j _ => (fixedProfile 1).agents j) discount 2))
      discount 0 [] 2 = 3/8 := by
  rw [deadlineResponseAgent_optimal delayed _ discount 0 2 (one_full _ _ _)
    2 [] (by rfl) (by rfl) (by simp [MultiAgentHistory.cycles])]
  exact initial_optimum

def hiddenHistory (bit : Bool) : MultiAgentHistory 2 :=
  [.act (fun _ => .left), .per (fun j => .mk (if j = 1 then bit else false) false)]

def hiddenOutcome : MultiAgentHistory 2 → Bool → JointPercept 2
  | [.act _, .per past, .act a], _ => fun j => .mk false
      (if j = 0 then decide (a 0 = if (past 1).obs then .right else .left) else false)
  | _, _ => fun _ => .mk false false

private theorem hidden_reward (bit b : Bool) (a : Action) :
    (hiddenOutcome (hiddenHistory bit ++ [.act (Function.update (fun _ => .left) 0 a)]) b 0).reward =
      if a = (if bit then .right else .left) then 1 else 0 := by
  change (Percept.mk false (decide (a = if bit then .right else .left))).reward = _
  simp only [Percept.reward, decide_eq_true_eq]

theorem hidden_q (bit : Bool) (a : Action) :
    bestResponseQValue (binaryEnvironment hiddenOutcome) (fixedProfile 2) discount 0
      (hiddenHistory bit) a 1 = if a = (if bit then .right else .left) then 1 else 0 := by
  rw [bestResponseQValue_succ, binary_step]
  simp only [bestResponseValue_zero, mul_zero, add_zero, hidden_reward, Fintype.sum_bool]
  ring

private theorem hidden_value (agent : Agent) (bit : Bool) :
    playerValue (binaryEnvironment hiddenOutcome) ((fixedProfile 2).updateAgent 0 agent)
      discount 0 (hiddenHistory bit) 1 =
      (agent.policy ((hiddenHistory false).playerView 0) (if bit then .right else .left)).toReal := by
  rw [playerValue_eq_weighted_qValue]
  simp_rw [playerQValue_one_eq_bestResponseQValue, bestResponseQValue_updateAgent_eq, hidden_q]
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte,
    MultiAgentPolicy.updateAgent]
  have same : (hiddenHistory bit).playerView 0 = (hiddenHistory false).playerView 0 := rfl
  rw [same]

/-- Equal player views can require incompatible unique full-information actions. -/
theorem hidden_information_loss (agent : Agent) :
    (hiddenHistory false).playerView 0 = (hiddenHistory true).playerView 0 ∧
    ¬(playerValue (binaryEnvironment hiddenOutcome) ((fixedProfile 2).updateAgent 0 agent)
        discount 0 (hiddenHistory false) 1 = 1 ∧
      playerValue (binaryEnvironment hiddenOutcome) ((fixedProfile 2).updateAgent 0 agent)
        discount 0 (hiddenHistory true) 1 = 1) := by
  refine ⟨rfl, ?_⟩
  simp only [hidden_value, Bool.false_eq_true, ↓reduceIte]
  rintro ⟨left, right⟩
  have normalized : ∑ a, (agent.policy ((hiddenHistory false).playerView 0) a).toReal = 1 := by
    apply ennreal_sum_toReal_eq_one
    simpa only [tsum_fintype] using agent.policy_sum_one _ (by rfl)
  have distinct : Action.left ≠ Action.right := by decide
  have bound := Finset.sum_le_sum_of_subset_of_nonneg
    (f := fun a => (agent.policy ((hiddenHistory false).playerView 0) a).toReal)
    (s := {Action.left, Action.right}) (Finset.subset_univ _) (fun _ _ _ => ENNReal.toReal_nonneg)
  simp only [Finset.sum_pair distinct] at bound
  linarith

theorem hidden_optimum (bit : Bool) :
    bestResponseValue (binaryEnvironment hiddenOutcome) (fixedProfile 2) discount 0 (hiddenHistory bit) 1 = 1 := by
  rw [bestResponseValue]
  simp_rw [hidden_q]
  apply le_antisymm
  · apply ciSup_le; intro a; split_ifs <;> norm_num
  · simpa only [↓reduceIte] using le_ciSup
      (f := fun a : Action => if a = (if bit then .right else .left) then (1 : ℝ) else 0)
      (Set.Finite.bddAbove (Set.finite_range _)) (if bit then .right else .left)

theorem no_local_full_optimal (agent : Agent) :
    ¬∀ bit, playerValue (binaryEnvironment hiddenOutcome) ((fixedProfile 2).updateAgent 0 agent)
      discount 0 (hiddenHistory bit) 1 =
        bestResponseValue (binaryEnvironment hiddenOutcome) (fixedProfile 2) discount 0 (hiddenHistory bit) 1 := by
  intro optimal
  exact (hidden_information_loss agent).2
    ⟨(optimal false).trans (hidden_optimum false), (optimal true).trans (hidden_optimum true)⟩

end DeadlineControls

end Mettapedia.UniversalAI.MultiAgent
