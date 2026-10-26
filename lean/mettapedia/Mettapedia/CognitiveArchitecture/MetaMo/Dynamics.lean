import Mettapedia.CognitiveArchitecture.MetaMo.Commutativity
import Mathlib.Topology.MetricSpace.Contracting
import Mettapedia.GSLT.Dynamics.OrderedListFold

/-!
# Ordered execution, feedback, and equilibrium

The authored dynamics execute decision then appraisal. Fixed scalar schedules
have product-action endpoints but retain ordered intermediate observations.
Contractivity is an additional metric hypothesis, independent of the action laws.
-/

namespace Mettapedia.CognitiveArchitecture.MetaMo

open Mettapedia.Algebra.QuantaleWeakness
open scoped NNReal

variable {Q : Type*} {Θ : Type*}
  [CommMonoid Q] [CompleteLattice Q] [IsCommQuantale Q]
  [CompleteLattice Θ] [QModule Q Θ]

def motivationalDynamics (q_sens q_dec : Q) : Θ → Θ :=
  appraisalFunctor q_sens ∘ decisionFunctor q_dec

/-- The alternative order executes appraisal before decision. -/
def motivationalDynamics' (q_sens q_dec : Q) : Θ → Θ :=
  decisionFunctor q_dec ∘ appraisalFunctor q_sens

theorem motivationalDynamics_eq_dynamics' (q_sens q_dec : Q) :
    motivationalDynamics (Θ := Θ) q_sens q_dec = motivationalDynamics' q_sens q_dec := by
  unfold motivationalDynamics motivationalDynamics'
  exact appraisal_decision_commute_comp q_sens q_dec

@[simp]
theorem motivationalDynamics_apply (q_sens q_dec : Q) (θ : Θ) :
    motivationalDynamics q_sens q_dec θ = q_sens • (q_dec • θ) := rfl

theorem motivationalDynamics_eq_smul (q_sens q_dec : Q) (θ : Θ) :
    motivationalDynamics q_sens q_dec θ = (q_sens * q_dec) • θ := by
  simp only [motivationalDynamics_apply]
  exact (mul_smul q_sens q_dec θ).symm

@[simp]
theorem motivationalDynamics_one_one :
    motivationalDynamics (Θ := Θ) (1 : Q) 1 = id := by
  ext θ
  simp only [motivationalDynamics_apply, one_smul, id_eq]

theorem motivationalDynamics_comp (q_s₁ q_d₁ q_s₂ q_d₂ : Q) :
    motivationalDynamics (Θ := Θ) q_s₁ q_d₁ ∘ motivationalDynamics q_s₂ q_d₂ =
    motivationalDynamics (q_s₁ * q_d₁ * q_s₂) q_d₂ := by
  ext θ
  simp only [Function.comp_apply, motivationalDynamics_eq_smul]
  rw [← mul_smul]
  congr 1
  simp only [mul_comm, mul_left_comm]

def IsMotivationalEquilibrium (q_sens q_dec : Q) (θ_eq : Θ) : Prop :=
  motivationalDynamics q_sens q_dec θ_eq = θ_eq

theorem isMotivationalEquilibrium_iff (q_sens q_dec : Q) (θ_eq : Θ) :
    IsMotivationalEquilibrium q_sens q_dec θ_eq ↔ (q_sens * q_dec) • θ_eq = θ_eq := by
  unfold IsMotivationalEquilibrium
  rw [motivationalDynamics_eq_smul]

section ContractiveCase

variable [EMetricSpace Θ] [CompleteSpace Θ]

/-- Convergence in an extended metric requires a finite-distance starting step. -/
theorem motivational_equilibrium_exists
    (q_sens q_dec : Q) (K : ℝ≥0)
    (h_contract : ContractingWith K (motivationalDynamics (Θ := Θ) q_sens q_dec))
    (θ₀ : Θ) (h_finite : edist θ₀ (motivationalDynamics q_sens q_dec θ₀) ≠ ⊤) :
    ∃ θ_eq : Θ, IsMotivationalEquilibrium q_sens q_dec θ_eq ∧
      Filter.Tendsto (fun n => (motivationalDynamics q_sens q_dec)^[n] θ₀)
        Filter.atTop (nhds θ_eq) := by
  obtain ⟨θ_eq, h_fixed, h_tendsto, _⟩ := ContractingWith.exists_fixedPoint h_contract θ₀ h_finite
  exact ⟨θ_eq, h_fixed, h_tendsto⟩

omit [CompleteSpace Θ] in

/-- Uniqueness holds within a finite-distance component. -/
theorem motivational_equilibrium_unique
    (q_sens q_dec : Q) (K : ℝ≥0)
    (h_contract : ContractingWith K (motivationalDynamics (Θ := Θ) q_sens q_dec))
    {θ₁ θ₂ : Θ}
    (h₁ : IsMotivationalEquilibrium q_sens q_dec θ₁)
    (h₂ : IsMotivationalEquilibrium q_sens q_dec θ₂)
    (h_finite : edist θ₁ θ₂ ≠ ⊤) :
    θ₁ = θ₂ :=
  (h_contract.eq_or_edist_eq_top_of_fixedPoints h₁ h₂).resolve_right h_finite

end ContractiveCase

theorem motivationalDynamics_mono (q_sens q_dec : Q) {θ₁ θ₂ : Θ} (h : θ₁ ≤ θ₂) :
    motivationalDynamics q_sens q_dec θ₁ ≤ motivationalDynamics q_sens q_dec θ₂ := by
  simp only [motivationalDynamics_eq_smul]
  exact smul_mono_right (q_sens * q_dec) h

theorem motivationalDynamics_sup (q_sens q_dec : Q) (θ₁ θ₂ : Θ) :
    motivationalDynamics q_sens q_dec (θ₁ ⊔ θ₂) =
    motivationalDynamics q_sens q_dec θ₁ ⊔ motivationalDynamics q_sens q_dec θ₂ := by
  simp only [motivationalDynamics_eq_smul]
  exact smul_sup (q_sens * q_dec) θ₁ θ₂

/-- In a complete metric space all distances are finite, giving global uniqueness. -/
theorem motivational_equilibrium_existsUnique [MetricSpace Θ] [CompleteSpace Θ]
    (q_sens q_dec : Q) (K : ℝ≥0)
    (contract : ContractingWith K (motivationalDynamics (Θ := Θ) q_sens q_dec)) (initial : Θ) :
    ∃! state : Θ, IsMotivationalEquilibrium q_sens q_dec state := by
  obtain ⟨state, fixed, _⟩ := motivational_equilibrium_exists q_sens q_dec K contract initial
    (edist_ne_top _ _)
  exact ⟨state, fixed, fun other otherFixed =>
    motivational_equilibrium_unique q_sens q_dec K contract otherFixed fixed (edist_ne_top _ _)⟩

/-- Weights execute from left to right; each occurrence is consumed. -/
def runWeights (weights : List Q) (initial : Θ) : Θ :=
  weights.foldl (fun state q => QModule.smul q state) initial

/-- The initial state and every subsequent state remain observable. -/
def weightHistory (weights : List Q) (initial : Θ) : List Θ :=
  weights.scanl (fun state q => QModule.smul q state) initial

theorem runWeights_eq_product (weights : List Q) (initial : Θ) :
    runWeights weights initial = QModule.smul weights.prod initial := by
  induction weights generalizing initial with
  | nil => exact (QModule.smul_one initial).symm
  | cons q rest ih =>
    change runWeights rest (QModule.smul q initial) = _
    rw [ih, ← mul_smul, List.prod_cons, mul_comm q]

theorem runWeights_append (first second : List Q) (initial : Θ) :
    runWeights (first ++ second) initial = runWeights second (runWeights first initial) :=
  List.foldl_append

theorem runWeights_perm {first second : List Q} (perm : first.Perm second) (initial : Θ) :
    runWeights first initial = runWeights second initial := by
  rw [runWeights_eq_product, runWeights_eq_product, perm.prod_eq]

@[simp] theorem weightHistory_length (weights : List Q) (initial : Θ) :
    (weightHistory weights initial).length = weights.length + 1 := List.length_scanl

/-- A history entry observes execution of exactly the supplied prefix. -/
theorem weightHistory_getElem (weights : List Q) (initial : Θ) (i : Nat)
    (h : i < (weightHistory weights initial).length) :
    (weightHistory weights initial)[i] = runWeights (weights.take i) initial :=
  List.getElem_scanl h

theorem motivationalDynamics_eq_runWeights (q_sens q_dec : Q) (initial : Θ) :
    motivationalDynamics q_sens q_dec initial = runWeights [q_dec, q_sens] initial := rfl

/-- A feedback coefficient is recomputed from the state at which the step runs. -/
def feedbackStep (choose : Θ → Q) (state : Θ) : Θ := QModule.smul (choose state) state

/-- A concrete complete execution, obtained from the independent ordered-fold machine. -/
def weightExecution {Q Θ : Type} [CommMonoid Q] [CompleteLattice Q]
    [IsCommQuantale Q] [CompleteLattice Θ] [QModule Q Θ]
    (weights : List Q) (initial : Θ) :
    (Mettapedia.GSLT.Dynamics.OrderedListFold.theory
      (fun state q => QModule.smul q state)).RewritePath
        (.active weights initial) (.done (runWeights weights initial)) :=
  Mettapedia.GSLT.Dynamics.OrderedListFold.runPath _ weights initial

/-- The existing GSLT adapter uses small carriers; the algebra above is universe-polymorphic. -/
theorem weightExecution_complete {Q Θ : Type} [CommMonoid Q] [CompleteLattice Q]
    [IsCommQuantale Q] [CompleteLattice Θ] [QModule Q Θ]
    (weights : List Q) (initial result : Θ)
    (path : (Mettapedia.GSLT.Dynamics.OrderedListFold.theory
      (fun state q => QModule.smul q state)).RewritePath
        (.active weights initial) (.done result)) :
    result = QModule.smul weights.prod initial ∧ path.length = weights.length + 1 := by
  obtain ⟨endpoint, length⟩ :=
    Mettapedia.GSLT.Dynamics.OrderedListFold.complete_path _ weights initial result path
  exact ⟨endpoint.trans (runWeights_eq_product weights initial), length⟩

namespace Controls
open scoped ENNReal

/-- Endpoint equality does not erase intermediate observations. -/
theorem permuted_weights_different_histories :
    runWeights ([2, 3] : List ℝ≥0∞) (1 : ℝ≥0∞) = runWeights ([3, 2] : List ℝ≥0∞) (1 : ℝ≥0∞) ∧
    weightHistory ([2, 3] : List ℝ≥0∞) (1 : ℝ≥0∞) ≠ weightHistory ([3, 2] : List ℝ≥0∞) (1 : ℝ≥0∞) := by
  norm_num [runWeights, weightHistory, List.foldl, List.scanl, QModule.smul]

theorem repeated_weight_changes_result :
    runWeights ([2] : List ℝ≥0∞) (1 : ℝ≥0∞) ≠ runWeights ([2, 2] : List ℝ≥0∞) (1 : ℝ≥0∞) := by
  norm_num [runWeights, List.foldl, QModule.smul]

/-- A square step and a double step do not commute when the weight uses the current state. -/
theorem feedback_does_not_commute :
    feedbackStep (fun x : ℝ≥0∞ => x) (feedbackStep (fun _ : ℝ≥0∞ => (2 : ℝ≥0∞)) (1 : ℝ≥0∞)) ≠
      feedbackStep (fun _ : ℝ≥0∞ => (2 : ℝ≥0∞)) (feedbackStep (fun x : ℝ≥0∞ => x) (1 : ℝ≥0∞)) := by
  change (2 * 1) * (2 * 1) ≠ (2 : ℝ≥0∞) * (1 * 1)
  norm_num

theorem unit_dynamics_multiple_equilibria :
    IsMotivationalEquilibrium (1 : ℝ≥0∞) 1 (0 : ℝ≥0∞) ∧
      IsMotivationalEquilibrium (1 : ℝ≥0∞) 1 (1 : ℝ≥0∞) ∧ (0 : ℝ≥0∞) ≠ 1 := by
  simp [IsMotivationalEquilibrium]

section BinaryJoinBoundary
noncomputable local instance boundaryAction : QModule ℝ≥0∞ Bool where
  smul q b := if q = 0 then true else b
  smul_one b := by simp
  smul_assoc q r b := by
    by_cases hq : q = 0 <;> by_cases hr : r = 0 <;> simp [hq, hr, mul_eq_zero]
  smul_sup q b c := by by_cases hq : q = 0 <;> simp [hq]

/-- A lawful binary-join action need not preserve the empty join. -/
theorem binary_join_not_bottom : QModule.smul (Q := ℝ≥0∞) 0 (⊥ : Bool) ≠ ⊥ := by
  change (if (0 : ℝ≥0∞) = 0 then true else false) ≠ false
  simp

/-- Monotonicity in the scalar cannot be inferred from the base action laws. -/
theorem binary_join_not_scalar_monotone :
    ¬ ∀ q r : ℝ≥0∞, q ≤ r → ∀ b : Bool, QModule.smul q b ≤ QModule.smul r b := by
  intro mono
  have bad := mono 0 1 (by norm_num) false
  change (if (0 : ℝ≥0∞) = 0 then true else false) ≤
    (if (1 : ℝ≥0∞) = 0 then true else false) at bad
  norm_num at bad
  exact (by decide : ¬ (true : Bool) ≤ false) bad
end BinaryJoinBoundary
end Controls

end Mettapedia.CognitiveArchitecture.MetaMo
