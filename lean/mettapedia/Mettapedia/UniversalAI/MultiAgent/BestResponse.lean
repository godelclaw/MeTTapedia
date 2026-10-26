import Mettapedia.UniversalAI.MultiAgent.Value
import Mettapedia.Computability.ArithmeticalHierarchy.PolicyEncoding

/-!
# Multi-Agent Best Response

This file defines best response policies and their properties in multi-agent settings.

## Main Definitions

* `bestResponsePolicy`: Policy that maximizes player i's Q-value
* `bestResponseAgent`: Agent that plays best response
* `isBestResponse`: Predicate for best response property

## References

- Leike, Taylor & Fallenstein (2016). "A Formal Solution to the Grain of Truth Problem"
- Shoham & Leyton-Brown (2008). "Multiagent Systems", Chapter 3
-/

namespace Mettapedia.UniversalAI.MultiAgent

open Mettapedia.UniversalAI.BayesianAgents

/-! ## Utilities -/

/-- Update multi-agent policy by replacing agent i. -/
def MultiAgentPolicy.updateAgent {n : ℕ}
    (π : MultiAgentPolicy n) (i : Fin n) (agent : Agent) :
    MultiAgentPolicy n where
  agents := fun j => if j = i then agent else π.agents j

/-! ## Best Response Policy -/

/-- Convert single-player history to multi-agent history from player i's perspective.
    Other players' actions/percepts are set to default values. -/
def historyToMultiAgent {n : ℕ} (i : Fin n) (h : History) : MultiAgentHistory n :=
  h.map fun elem =>
    match elem with
    | HistElem.act a => JointHistElem.act (fun j => if j = i then a else default)
    | HistElem.per p => JointHistElem.per (fun j => if j = i then p else default)

/-! ### historyToMultiAgent properties -/

/-- historyToMultiAgent preserves the wellFormed property.
    Single-agent History.wellFormed maps to MultiAgentHistory.wellFormed. -/
theorem historyToMultiAgent_wellFormed {n : ℕ} (i : Fin n) (h : History)
    (hw : History.wellFormed h = true) :
    (historyToMultiAgent i h).wellFormed = true := by
  -- Induction on the wellFormed structure
  match h with
  | [] => rfl
  | [HistElem.act _] =>
    simp only [historyToMultiAgent, List.map, MultiAgentHistory.wellFormed]
  | HistElem.act _ :: HistElem.per _ :: rest =>
    simp only [History.wellFormed] at hw
    simp only [historyToMultiAgent, List.map, MultiAgentHistory.wellFormed]
    exact historyToMultiAgent_wellFormed i rest hw
  | HistElem.per _ :: _ =>
    simp only [History.wellFormed] at hw; cases hw
  | HistElem.act _ :: HistElem.act _ :: _ =>
    simp only [History.wellFormed] at hw; cases hw
termination_by h.length

/-- playerView of historyToMultiAgent returns the original single-agent history. -/
theorem playerView_historyToMultiAgent {n : ℕ} (i : Fin n) (h : History) :
    (historyToMultiAgent i h).playerView i = h := by
  simp only [historyToMultiAgent, MultiAgentHistory.playerView, List.map_map]
  have element (e : HistElem) :
      (match e with
       | .act a => JointHistElem.act (fun j : Fin n => if j = i then a else default)
       | .per e => .per (fun j => if j = i then e else default)).playerView i = e := by
    cases e <;> simp [JointHistElem.playerView]
  simp only [Function.comp_def, element]
  exact List.map_id' h

/-- Select a maximizer of optimal-continuation Q-values at the supplied lookahead. -/
noncomputable def bestResponsePolicy
    (μ : MultiAgentEnvironment n)
    (π : MultiAgentPolicy n)
    (γ : DiscountFactor)
    (i : Fin n)
    (horizon : ℕ) : History → Action :=
  fun h =>
    Classical.choose (exists_best_action μ π γ i h horizon)
  where
    exists_best_action (μ : MultiAgentEnvironment n) (π : MultiAgentPolicy n)
        (γ : DiscountFactor) (i : Fin n) (h : History) (horizon : ℕ) :
        ∃ a : Action, ∀ a' : Action,
          bestResponseQValue μ π γ i (historyToMultiAgent i h) a horizon ≥
          bestResponseQValue μ π γ i (historyToMultiAgent i h) a' horizon := by
      -- Action is a finite nonempty type, so maximum exists
      have ⟨a, _, ha⟩ := Finset.exists_max_image
        (s := (Finset.univ : Finset Action))
        (f := fun a => bestResponseQValue μ π γ i (historyToMultiAgent i h) a horizon)
        ⟨default, Finset.mem_univ _⟩
      exact ⟨a, fun a' => ha a' (Finset.mem_univ a')⟩

/-- Construct multi-agent policy from other agents.
    Uses uniformAgent as placeholder for player i. -/
noncomputable def multiAgentPolicyFromOthers {n : ℕ} (i : Fin n)
    (π_others : (j : Fin n) → j ≠ i → Agent) : MultiAgentPolicy n :=
  { agents := fun j =>
      if hj : j = i then uniformAgent
      else π_others j hj }

/-- Best response agent: agent that plays best response policy. -/
noncomputable def bestResponseAgent {n : ℕ}
    (μ : MultiAgentEnvironment n)
    (i : Fin n)
    (π_others : (j : Fin n) → j ≠ i → Agent)
    (γ : DiscountFactor)
    (horizon : ℕ) : Agent where
  policy := fun h a =>
    if bestResponsePolicy μ (multiAgentPolicyFromOthers i π_others) γ i horizon h = a
    then 1
    else 0
  policy_sum_one := by
    intro h _hw
    rw [tsum_fintype]
    simp [Finset.sum_ite_eq]

/-! ## Best Response Properties -/

/-- A Dirac policy observes exactly the chosen forced-action value. -/
theorem playerValue_deterministic {n : ℕ}
    (μ : MultiAgentEnvironment n)
    (π : MultiAgentPolicy n)
    (γ : DiscountFactor)
    (i : Fin n)
    (h : MultiAgentHistory n)
    (_hw : h.wellFormed = true)
    (action : Action)
    (hdet : ∀ a : Action, ((π.agents i).policy (h.playerView i) a).toReal =
                          if a = action then 1 else 0) :
    playerValue μ π γ i h horizon =
    playerQValue μ π γ i h action horizon := by
  rw [playerValue_eq_weighted_qValue]
  -- Sum simplifies: only the action term contributes (weight 1), others are 0
  simp_rw [hdet]
  simp only [ite_mul, one_mul, zero_mul]
  rw [Finset.sum_ite_eq']
  simp only [Finset.mem_univ, ↓reduceIte]

/-- The selected maximizer realizes the finite supremum at the representative history. -/
theorem bestResponseAction_achieves_bestResponseValue {n : ℕ}
    (μ : MultiAgentEnvironment n)
    (π : MultiAgentPolicy n)
    (γ : DiscountFactor)
    (i : Fin n)
    (h_single : History)
    (horizon : ℕ) :
    let h := historyToMultiAgent i h_single
    let a_star := bestResponsePolicy μ π γ i horizon h_single
    bestResponseQValue μ π γ i h a_star horizon = bestResponseValue μ π γ i h horizon := by
  intro h a_star
  simp only [bestResponseValue]
  exact le_antisymm
    (le_ciSup (f := fun a => bestResponseQValue μ π γ i h a horizon)
      (Set.Finite.bddAbove (Set.finite_range _)) a_star)
    (ciSup_le (Classical.choose_spec
      (bestResponsePolicy.exists_best_action μ π γ i h_single horizon)))

/-- Predicate: π_i is a best response to π_{-i}. -/
def isBestResponse
    (μ : MultiAgentEnvironment n)
    (π : MultiAgentPolicy n)
    (γ : DiscountFactor)
    (i : Fin n)
    (horizon : ℕ) : Prop :=
  ∀ (h : MultiAgentHistory n),
    h.wellFormed = true →
    playerValue μ π γ i h horizon =
    bestResponseValue μ π γ i h horizon

/-! ## Full Information Assumption -/

/-- Full-history optimal Q-values factor through the player's own observation.
This information-sufficiency premise is stronger than knowing the other policies. -/
def playerIQValueDependsOnlyOnOwnView
    (μ : MultiAgentEnvironment n)
    (π : MultiAgentPolicy n)
    (γ : DiscountFactor)
    (i : Fin n) : Prop :=
  ∀ (h₁ h₂ : MultiAgentHistory n) (action : Action) (horizon : ℕ),
    h₁.wellFormed = true → h₂.wellFormed = true →
    h₁.playerView i = h₂.playerView i →
    bestResponseQValue μ π γ i h₁ action horizon =
    bestResponseQValue μ π γ i h₂ action horizon

/-- Information sufficiency identifies Q-values at a history and its padded local view. -/
theorem bestResponseQValue_eq_of_playerView_eq {n : ℕ}
    (μ : MultiAgentEnvironment n)
    (π : MultiAgentPolicy n)
    (γ : DiscountFactor)
    (i : Fin n)
    (h : MultiAgentHistory n)
    (hw : h.wellFormed = true)
    (_hep : h.endsWithPercept = true)
    (action : Action)
    (horizon : ℕ)
    (hfull : playerIQValueDependsOnlyOnOwnView μ π γ i) :
    bestResponseQValue μ π γ i h action horizon =
    bestResponseQValue μ π γ i (historyToMultiAgent i (h.playerView i)) action horizon := by
  exact hfull h _ action horizon hw
    (historyToMultiAgent_wellFormed i _ (MultiAgentHistory.playerView_wellFormed i h hw))
    (playerView_historyToMultiAgent i _).symm

/-! ## Q-Value Policy Independence -/

/-- othersProb is independent of player i's policy.
    This is because othersProb only uses policies for j ≠ i. -/
theorem othersProb_updateAgent_eq {n : ℕ}
    (π : MultiAgentPolicy n)
    (i : Fin n)
    (agent : Agent)
    (h : MultiAgentHistory n)
    (ja : JointAction n) :
    othersProb (π.updateAgent i agent) h ja i = othersProb π h ja i := by
  apply Finset.prod_congr rfl
  intro j member
  simp only [MultiAgentPolicy.updateAgent, if_neg (Finset.mem_erase.mp member).1]

theorem actionValueStep_updateAgent_eq (μ : MultiAgentEnvironment n) (π : MultiAgentPolicy n)
    (γ : DiscountFactor) (i : Fin n) (h : MultiAgentHistory n) (a : Action) (agent : Agent)
    (v : MultiAgentHistory n → ℝ) :
    actionValueStep μ (π.updateAgent i agent) γ i h a v = actionValueStep μ π γ i h a v :=
  actionValueStep_congr μ _ π γ i h a v v
    (fun j different => by simp [MultiAgentPolicy.updateAgent, different]) (fun _ _ => rfl)

/-- playerView is the same for player i regardless of player i's policy.
    This is because playerView only depends on the history structure, not the policy. -/
theorem playerView_updateAgent_eq {n : ℕ}
    (_π : MultiAgentPolicy n)
    (i : Fin n)
    (_agent : Agent)
    (h : MultiAgentHistory n) :
    (h.playerView i) = (h.playerView i) := rfl

/-- At horizon 0, Q-values are all 0, so they don't depend on the policy. -/
theorem playerQValue_zero {n : ℕ}
    (μ : MultiAgentEnvironment n)
    (π : MultiAgentPolicy n)
    (γ : DiscountFactor)
    (i : Fin n)
    (h : MultiAgentHistory n)
    (action : Action) :
    playerQValue μ π γ i h action 0 = 0 := by
  simp only [playerQValue]

/-- bestResponseQValue at horizon 0 is 0. -/
theorem bestResponseQValue_zero {n : ℕ}
    (μ : MultiAgentEnvironment n)
    (π : MultiAgentPolicy n)
    (γ : DiscountFactor)
    (i : Fin n)
    (h : MultiAgentHistory n)
    (action : Action) :
    bestResponseQValue μ π γ i h action 0 = 0 := by
  simp only [bestResponseQValue]

/-- bestResponseValue at horizon 0 is 0. -/
theorem bestResponseValue_zero {n : ℕ}
    (μ : MultiAgentEnvironment n)
    (π : MultiAgentPolicy n)
    (γ : DiscountFactor)
    (i : Fin n)
    (h : MultiAgentHistory n) :
    bestResponseValue μ π γ i h 0 = 0 := by
  simp only [bestResponseValue, bestResponseQValue_zero]
  -- ciSup of constantly 0 is 0
  simp only [ciSup_const]

/-- At horizon 1, Q-values only depend on othersProb (not on recursive playerValue). -/
theorem playerQValue_one_eq_updateAgent {n : ℕ}
    (μ : MultiAgentEnvironment n)
    (π : MultiAgentPolicy n)
    (γ : DiscountFactor)
    (i : Fin n)
    (h : MultiAgentHistory n)
    (action : Action)
    (agent : Agent) :
    playerQValue μ (π.updateAgent i agent) γ i h action 1 =
    playerQValue μ π γ i h action 1 := by
  rw [playerQValue_succ, playerQValue_succ]
  apply actionValueStep_congr
  · intro j different; simp [MultiAgentPolicy.updateAgent, different]
  · intro ja jp; simp only [playerValue]

/-- At horizon 1, bestResponseQValue only depends on othersProb (not on recursive bestResponseValue).
    This is similar to playerQValue_one_eq_updateAgent. -/
theorem bestResponseQValue_one_eq_updateAgent {n : ℕ}
    (μ : MultiAgentEnvironment n)
    (π : MultiAgentPolicy n)
    (γ : DiscountFactor)
    (i : Fin n)
    (h : MultiAgentHistory n)
    (action : Action)
    (agent : Agent) :
    bestResponseQValue μ (π.updateAgent i agent) γ i h action 1 =
    bestResponseQValue μ π γ i h action 1 := by
  rw [bestResponseQValue_succ, bestResponseQValue_succ]
  apply actionValueStep_congr
  · intro j different; simp [MultiAgentPolicy.updateAgent, different]
  · intro ja jp; simp only [bestResponseValue_zero]

/-- At horizon 1, bestResponseValue doesn't depend on player i's policy. -/
theorem bestResponseValue_one_eq_updateAgent {n : ℕ}
    (μ : MultiAgentEnvironment n)
    (π : MultiAgentPolicy n)
    (γ : DiscountFactor)
    (i : Fin n)
    (h : MultiAgentHistory n)
    (agent : Agent) :
    bestResponseValue μ (π.updateAgent i agent) γ i h 1 =
    bestResponseValue μ π γ i h 1 := by
  simp only [bestResponseValue]
  congr 1
  ext a
  exact bestResponseQValue_one_eq_updateAgent μ π γ i h a agent

/-- bestResponseQValue doesn't depend on player i's policy.
    This is because it only uses othersProb (policies for j ≠ i). -/
theorem bestResponseQValue_updateAgent_eq {n : ℕ}
    (μ : MultiAgentEnvironment n)
    (π : MultiAgentPolicy n)
    (γ : DiscountFactor)
    (i : Fin n)
    (h : MultiAgentHistory n)
    (agent : Agent)
    (action : Action)
    (horizon : ℕ) :
    bestResponseQValue μ (π.updateAgent i agent) γ i h action horizon =
    bestResponseQValue μ π γ i h action horizon := by
  induction horizon generalizing h action with
  | zero => simp only [bestResponseQValue_zero]
  | succ k ih =>
      rw [bestResponseQValue_succ, bestResponseQValue_succ]
      apply actionValueStep_congr
      · intro j different; simp [MultiAgentPolicy.updateAgent, different]
      · intro ja jp
        unfold bestResponseValue
        congr 1
        funext a
        exact ih _ a

/-- bestResponseValue doesn't depend on player i's policy.
    This is because bestResponseQValue only uses othersProb (policies for j ≠ i). -/
theorem bestResponseValue_updateAgent_eq {n : ℕ}
    (μ : MultiAgentEnvironment n)
    (π : MultiAgentPolicy n)
    (γ : DiscountFactor)
    (i : Fin n)
    (h : MultiAgentHistory n)
    (agent : Agent)
    (horizon : ℕ) :
    bestResponseValue μ (π.updateAgent i agent) γ i h horizon =
    bestResponseValue μ π γ i h horizon := by
  simp only [bestResponseValue, bestResponseQValue_updateAgent_eq]

/-- Best response is bounded by the optimal value.
    This follows from playerValue_le_bestResponseValue (proven in Value.lean)
    and the fact that bestResponseValue doesn't depend on player i's policy. -/
theorem bestResponse_le_bestResponseValue
    (μ : MultiAgentEnvironment n)
    (π : MultiAgentPolicy n)
    (γ : DiscountFactor)
    (i : Fin n)
    (h : MultiAgentHistory n)
    (hw : h.wellFormed = true)
    (hep : h.endsWithPercept = true)
    (horizon : ℕ) :
    let π' := π.updateAgent i (bestResponseAgent μ i
      (fun j _ => π.agents j) γ horizon)
    playerValue μ π' γ i h horizon ≤
    bestResponseValue μ π γ i h horizon := by
  intro π'
  calc playerValue μ π' γ i h horizon
      ≤ bestResponseValue μ π' γ i h horizon :=
        playerValue_le_bestResponseValue μ π' γ i h hw hep horizon
    _ = bestResponseValue μ π γ i h horizon :=
        bestResponseValue_updateAgent_eq μ π γ i h _ horizon

/-- Equal opponent policies and successor values give equal forced-action values. -/
theorem playerQValue_eq_bestResponseQValue_of_value_eq {n : ℕ}
    (μ : MultiAgentEnvironment n)
    (π : MultiAgentPolicy n)
    (π' : MultiAgentPolicy n)
    (γ : DiscountFactor)
    (i : Fin n)
    (h : MultiAgentHistory n)
    (action : Action)
    (k : ℕ)
    (hπ' : ∀ j, j ≠ i → π'.agents j = π.agents j)
    (hvalue_eq : ∀ (ja : JointAction n) (jp : JointPercept n),
        playerValue μ π' γ i (h ++ [JointHistElem.act ja, JointHistElem.per jp]) k =
        bestResponseValue μ π γ i (h ++ [JointHistElem.act ja, JointHistElem.per jp]) k) :
    playerQValue μ π' γ i h action (k + 1) =
    bestResponseQValue μ π γ i h action (k + 1) := by
  rw [playerQValue_succ, bestResponseQValue_succ]
  exact actionValueStep_congr μ π' π γ i h action _ _ hπ' hvalue_eq

/-- The selected constant-lookahead action is also optimal at every smaller horizon.
This is an additional assumption; a discount below one does not imply it. -/
def horizonConsistentOptimality
    (μ : MultiAgentEnvironment n)
    (π : MultiAgentPolicy n)
    (γ : DiscountFactor)
    (i : Fin n)
    (horizon : ℕ) : Prop :=
  ∀ (h : History) (k : ℕ), k < horizon →
    let h_ma := historyToMultiAgent i h
    let a_star := bestResponsePolicy μ π γ i horizon h
    bestResponseQValue μ π γ i h_ma a_star k =
    ⨆ a, bestResponseQValue μ π γ i h_ma a k

/-- All horizons are consistent: for ANY horizon H, the action optimal at H
    is also optimal at all smaller horizons. This is stronger than
    horizonConsistentOptimality at a single horizon. -/
def allHorizonsConsistent
    (μ : MultiAgentEnvironment n)
    (π : MultiAgentPolicy n)
    (γ : DiscountFactor)
    (i : Fin n) : Prop :=
  ∀ H : ℕ, horizonConsistentOptimality μ π γ i H

/-! ## Sup-Achieving Actions and Value Equality -/

/-- An action is sup-achieving at horizon k if it achieves ⨆ bestResponseQValue at k. -/
def isSupAchievingAt
    (μ : MultiAgentEnvironment n)
    (π : MultiAgentPolicy n)
    (γ : DiscountFactor)
    (i : Fin n)
    (h : MultiAgentHistory n)
    (action : Action)
    (horizon : ℕ) : Prop :=
  bestResponseQValue μ π γ i h action horizon = ⨆ a, bestResponseQValue μ π γ i h a horizon

/-- The bestResponsePolicy plays a sup-achieving action (by definition). -/
theorem bestResponsePolicy_isSupAchieving
    (μ : MultiAgentEnvironment n)
    (π : MultiAgentPolicy n)
    (γ : DiscountFactor)
    (i : Fin n)
    (h : History)
    (horizon : ℕ) :
    isSupAchievingAt μ π γ i (historyToMultiAgent i h)
      (bestResponsePolicy μ π γ i horizon h) horizon := by
  simpa only [isSupAchievingAt, bestResponseValue] using
    bestResponseAction_achieves_bestResponseValue μ π γ i h horizon

/-- Backward induction on a successor-closed family of decision histories and
remaining horizons. Optimality is required only at the current remaining horizon. -/
theorem playerValue_eq_bestResponseValue_on
    (μ : MultiAgentEnvironment n) (π π' : MultiAgentPolicy n) (γ : DiscountFactor)
    (i : Fin n) (others : ∀ j, j ≠ i → π'.agents j = π.agents j)
    (P : MultiAgentHistory n → ℕ → Prop)
    (closed : ∀ h k ja jp, P h (k+1) → P (h ++ [.act ja, .per jp]) k)
    (greedy : ∀ h k, h.wellFormed = true → h.endsWithPercept = true → P h (k+1) →
      ∃ chosen : Action,
        (∀ a, ((π'.agents i).policy (h.playerView i) a).toReal = if a = chosen then 1 else 0) ∧
        isSupAchievingAt μ π γ i h chosen (k+1))
    (horizon : ℕ) (h : MultiAgentHistory n) (hw : h.wellFormed = true)
    (hep : h.endsWithPercept = true) (state : P h horizon) :
    playerValue μ π' γ i h horizon = bestResponseValue μ π γ i h horizon := by
  induction horizon generalizing h with
  | zero => simp only [playerValue, bestResponseValue_zero]
  | succ k ih =>
      obtain ⟨chosen, deterministic, optimal⟩ := greedy h k hw hep state
      calc
        _ = playerQValue μ π' γ i h chosen (k+1) :=
          playerValue_deterministic μ π' γ i h hw chosen deterministic
        _ = bestResponseQValue μ π γ i h chosen (k+1) :=
          playerQValue_eq_bestResponseQValue_of_value_eq μ π π' γ i h chosen k others
            fun ja jp => by
              have valid := MultiAgentHistory.wellFormed_append_act_per h ja jp hw hep
              exact ih _ valid.1 valid.2 (closed h k ja jp state)
        _ = bestResponseValue μ π γ i h (k+1) := by
          simpa only [isSupAchievingAt, bestResponseValue] using optimal

/-- The canonical placeholder for one's own policy changes no opponent. -/
theorem multiAgentPolicyFromOthers_eq_update (π : MultiAgentPolicy n) (i : Fin n) :
    multiAgentPolicyFromOthers i (fun j _ => π.agents j) = π.updateAgent i uniformAgent := by
  ext j
  by_cases same : j = i <;> simp [multiAgentPolicyFromOthers, MultiAgentPolicy.updateAgent, same]

/-- The response is a Dirac policy at the supplied maximizer. -/
theorem bestResponseAgent_policy_toReal (μ : MultiAgentEnvironment n) (i : Fin n)
    (others : (j : Fin n) → j ≠ i → Agent) (γ : DiscountFactor) (H : ℕ)
    (h : History) (a : Action) :
    ((bestResponseAgent μ i others γ H).policy h a).toReal =
      if a = bestResponsePolicy μ (multiAgentPolicyFromOthers i others) γ i H h then 1 else 0 := by
  simp only [bestResponseAgent]
  by_cases equal : a = bestResponsePolicy μ (multiAgentPolicyFromOthers i others) γ i H h
  · simp [equal]
  · simp [equal, Ne.symm equal]

/-- Q-value sufficiency transfers optimality from the chosen representative history. -/
theorem isSupAchievingAt_of_playerView (μ : MultiAgentEnvironment n) (π : MultiAgentPolicy n)
    (γ : DiscountFactor) (i : Fin n) (h : MultiAgentHistory n)
    (hw : h.wellFormed = true) (hep : h.endsWithPercept = true)
    (full : playerIQValueDependsOnlyOnOwnView μ π γ i) (a : Action) (k : ℕ)
    (optimal : isSupAchievingAt μ π γ i (historyToMultiAgent i (h.playerView i)) a k) :
    isSupAchievingAt μ π γ i h a k := by
  unfold isSupAchievingAt at *
  simp_rw [bestResponseQValue_eq_of_playerView_eq μ π γ i h hw hep _ k full]
  exact optimal

/-- A fixed policy optimal at every smaller horizon attains the Bellman value. -/
theorem playerValue_eq_bestResponseValue_of_supAchieving
    (μ : MultiAgentEnvironment n)
    (π : MultiAgentPolicy n)
    (γ : DiscountFactor)
    (i : Fin n)
    (π'_i : Agent)
    (hπ'_others : ∀ j, j ≠ i → (π.updateAgent i π'_i).agents j = π.agents j)
    (horizon : ℕ)
    -- Hypothesis: π'_i is deterministic and plays sup-achieving at EVERY k ≤ horizon
    -- (for wellFormed histories ending with percept)
    (hdet : ∀ h : MultiAgentHistory n, h.wellFormed = true → h.endsWithPercept = true →
        ∀ k : ℕ, k ≤ horizon → ∃ a_chosen : Action,
        (∀ a, (π'_i.policy (h.playerView i) a).toReal = if a = a_chosen then 1 else 0) ∧
        isSupAchievingAt μ π γ i h a_chosen k) :
    ∀ (h : MultiAgentHistory n), h.wellFormed = true → h.endsWithPercept = true →
      playerValue μ (π.updateAgent i π'_i) γ i h horizon =
      bestResponseValue μ π γ i h horizon := by
  intro h hw hep
  apply playerValue_eq_bestResponseValue_on μ π (π.updateAgent i π'_i) γ i hπ'_others
    (fun _ k => k ≤ horizon) (fun _ _ _ _ bound => Nat.le_of_succ_le bound)
    (fun h k hw hep bound => by
      obtain ⟨a, deterministic, optimal⟩ := hdet h hw hep (k+1) bound
      exact ⟨a, by simpa [MultiAgentPolicy.updateAgent] using deterministic, optimal⟩)
    horizon h hw hep (le_refl _)

/-- Constant-lookahead optimality under observation sufficiency and consistency
of its canonical opponent profile at every smaller horizon. -/
theorem bestResponse_achieves_value_aux
    (μ : MultiAgentEnvironment n)
    (π : MultiAgentPolicy n)
    (γ : DiscountFactor)
    (i : Fin n)
    (hfull : playerIQValueDependsOnlyOnOwnView μ π γ i)
    (hcons : allHorizonsConsistent μ π γ i)
    -- Since bestResponseQValue doesn't depend on player i's policy, horizonConsistentOptimality
    -- should hold for any policy differing from π only at position i.
    (hcons_any : ∀ agent, allHorizonsConsistent μ (π.updateAgent i agent) γ i)
    (horizon : ℕ) :
    ∀ (h : MultiAgentHistory n),
      h.wellFormed = true →
      h.endsWithPercept = true →
      let π' := π.updateAgent i (bestResponseAgent μ i
        (fun j _ => π.agents j) γ horizon)
      playerValue μ π' γ i h horizon ≥ bestResponseValue μ π γ i h horizon := by
  intro h hw hep
  let canon := multiAgentPolicyFromOthers i (fun j _ => π.agents j)
  have canon_eq : canon = π.updateAgent i uniformAgent := multiAgentPolicyFromOthers_eq_update π i
  have canon_consistent : allHorizonsConsistent μ canon γ i := by
    rw [canon_eq]
    exact hcons_any uniformAgent
  have hdet (h' : MultiAgentHistory n) (hw' : h'.wellFormed = true)
      (hep' : h'.endsWithPercept = true) (k : ℕ) (hk : k ≤ horizon) :
      ∃ chosen : Action,
        (∀ a, ((bestResponseAgent μ i (fun j _ => π.agents j) γ horizon).policy
          (h'.playerView i) a).toReal = if a = chosen then 1 else 0) ∧
        isSupAchievingAt μ π γ i h' chosen k := by
    refine ⟨bestResponsePolicy μ canon γ i horizon (h'.playerView i),
      bestResponseAgent_policy_toReal μ i _ γ horizon _ , ?_⟩
    apply isSupAchievingAt_of_playerView μ π γ i h' hw' hep' hfull
    have optimal : isSupAchievingAt μ canon γ i (historyToMultiAgent i (h'.playerView i))
        (bestResponsePolicy μ canon γ i horizon (h'.playerView i)) k := by
      rcases hk.eq_or_lt with same | less
      · subst k
        exact bestResponsePolicy_isSupAchieving μ canon γ i _ horizon
      · exact canon_consistent horizon (h'.playerView i) k less
    simpa only [isSupAchievingAt, canon_eq, bestResponseQValue_updateAgent_eq] using optimal
  have equality := playerValue_eq_bestResponseValue_of_supAchieving μ π γ i
    (bestResponseAgent μ i (fun j _ => π.agents j) γ horizon)
    (fun j different => by simp [MultiAgentPolicy.updateAgent, different]) horizon hdet h hw hep
  -- The historical signature also supplies consistency for the unmodified policy.
  have _ := hcons
  exact equality.symm.le

/-- The constant-lookahead response attains the optimum under the stated
information and cross-horizon consistency assumptions. -/
theorem bestResponse_maximizes_value
    (μ : MultiAgentEnvironment n)
    (π : MultiAgentPolicy n)
    (γ : DiscountFactor)
    (i : Fin n)
    (h : MultiAgentHistory n)
    (hw : h.wellFormed = true)
    (hep : h.endsWithPercept = true)
    (horizon : ℕ)
    (hfull : playerIQValueDependsOnlyOnOwnView μ π γ i)
    (hcons : allHorizonsConsistent μ π γ i)
    (hcons_any : ∀ agent, allHorizonsConsistent μ (π.updateAgent i agent) γ i) :
    let π' := π.updateAgent i (bestResponseAgent μ i
      (fun j _ => π.agents j) γ horizon)
    playerValue μ π' γ i h horizon =
    bestResponseValue μ π γ i h horizon := by
  intro π'
  exact le_antisymm (bestResponse_le_bestResponseValue μ π γ i h hw hep horizon)
    (bestResponse_achieves_value_aux μ π γ i hfull hcons hcons_any horizon h hw hep)

/-- Under the stated premises, the constant-lookahead response improves value. -/
theorem bestResponse_improves_value
    (μ : MultiAgentEnvironment n)
    (π : MultiAgentPolicy n)
    (γ : DiscountFactor)
    (i : Fin n)
    (h : MultiAgentHistory n)
    (hw : h.wellFormed = true)
    (hep : h.endsWithPercept = true)
    (horizon : ℕ)
    (hfull : playerIQValueDependsOnlyOnOwnView μ π γ i)
    (hcons : allHorizonsConsistent μ π γ i)
    (hcons_any : ∀ agent, allHorizonsConsistent μ (π.updateAgent i agent) γ i) :
    let π' := π.updateAgent i (bestResponseAgent μ i
      (fun j _ => π.agents j) γ horizon)
    playerValue μ π' γ i h horizon ≥
    playerValue μ π γ i h horizon := by
  intro π'
  rw [bestResponse_maximizes_value μ π γ i h hw hep horizon hfull hcons hcons_any]
  exact playerValue_le_bestResponseValue μ π γ i h hw hep horizon

end Mettapedia.UniversalAI.MultiAgent
