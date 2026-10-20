import Mettapedia.PLN.InferenceControl.PremiseSelection.PLNInferenceControlAlgorithms

/-!
# Chapter 13 Worked Examples

Concrete finite fixtures that instantiate the Chapter-13 inference-control pipeline
with explicit scorers, checklist assumptions, and a dependency set.
-/

namespace Mettapedia.PLN.InferenceControl.PremiseSelection.PLNInferenceControlExamples

open Mettapedia.PLN.Evidence
open Mettapedia.PLN.InferenceControl.PremiseSelection
open Mettapedia.PLN.InferenceControl.PremiseSelection.Optimality
open Mettapedia.PLN.InferenceControl.PremiseSelection.PLNInferenceControlCore
open Mettapedia.PLN.InferenceControl.PremiseSelection.PLNInferenceControlAlgorithms

noncomputable section

/-- Finite fixture scorer emphasizing `true` over `false`. -/
def globalPriorBool : Scorer Bool Bool :=
  ⟨fun _ f => if f then ⟨4, 1⟩ else ⟨1, 4⟩⟩

/-- Finite fixture local scorer with weaker but aligned bias. -/
def localPriorBool : Scorer Bool Bool :=
  ⟨fun _ f => if f then ⟨3, 1⟩ else ⟨1, 3⟩⟩

/-- Finite fixture likelihood scorer. -/
def likelihoodBool : Scorer Bool Bool :=
  ⟨fun _ f => if f then ⟨5, 1⟩ else ⟨1, 5⟩⟩

/-- Explicit checklist for the finite Bool fixture. -/
def checklistBool : PriorNBAssumptionChecklist Bool Bool Bool where
  inBin := fun g => g
  finitePool_nonempty := by decide
  localExchangeabilityInBin := True
  topK := 1
  topK_pos := by decide
  topK_le_pool := by decide
  surrogateCoverageObjective := True

def dependencyBool : Finset Bool := {true}

/-- Use pooled chapter-13 score as the Bayes surrogate on the worked fixture. -/
def etaBool : Bool → ℝ :=
  pooledSelectorScore globalPriorBool localPriorBool likelihoodBool true

def deltaZero : Bool → ℝ := fun _ => 0

lemma localExchangeabilityBool :
    checklistBool.localExchangeabilityInBin := by
  trivial

lemma pooledRankingBool :
    BayesOptimalRanking etaBool
      (pooledSelectorScore globalPriorBool localPriorBool likelihoodBool true) := by
  intro x y
  simp [etaBool]

lemma twoStageRankingBool :
    BayesOptimalRanking etaBool
      (twoStageSelectorScore globalPriorBool localPriorBool likelihoodBool true) := by
  have hSel :=
    selector_default_ranking_iff
      (A := checklistBool) (η := etaBool)
      (globalPrior := globalPriorBool) (localPrior := localPriorBool)
      (likelihood := likelihoodBool) (g := true)
      localExchangeabilityBool
  exact hSel.2.2.mp pooledRankingBool

lemma marginBool :
    ∀ x y, etaBool x < etaBool y →
      pooledSelectorScore globalPriorBool localPriorBool likelihoodBool true y
        - pooledSelectorScore globalPriorBool localPriorBool likelihoodBool true x
          > 2 * (0 : ℝ) := by
  intro x y hlt
  have hpos :
      pooledSelectorScore globalPriorBool localPriorBool likelihoodBool true y
        - pooledSelectorScore globalPriorBool localPriorBool likelihoodBool true x
          > 0 := by
    exact sub_pos.mpr (by simpa [etaBool] using hlt)
  simpa using hpos

/-- Worked Chapter-13 theorem:
explicit finite checklist + scorers imply the full algorithmic end-to-end guarantee. -/
theorem bool_end_to_end_algorithmic :
    let G := greedySelect dependencyBool checklistBool.topK
    checklistBool.topK ≤ Fintype.card Bool
      ∧ (∀ g' f',
          0 ≤ (selectorDefaults_halfGate Bool Bool).gate g' f'
            ∧ (selectorDefaults_halfGate Bool Bool).gate g' f' ≤ 1)
      ∧ BayesOptimalRanking etaBool
          (perturbedScore
            (pooledSelectorScore globalPriorBool localPriorBool likelihoodBool true)
            deltaZero)
      ∧ (1 - Real.exp (-1))
          * (Nat.min checklistBool.topK dependencyBool.card : ℝ)
          ≤ dependencyCoverage dependencyBool G := by
  simpa [deltaZero] using
    (inferenceControl_end_to_end_algorithmic
      (A := checklistBool) (η := etaBool)
      (globalPrior := globalPriorBool) (localPrior := localPriorBool)
      (likelihood := likelihoodBool) (g := true)
      localExchangeabilityBool
      (δ := deltaZero) (ε := 0)
      twoStageRankingBool
      (hbound := by intro x; simp [deltaZero])
      (hmargin := marginBool)
      (htie := by intro x y hxy; simp [deltaZero])
      (D := dependencyBool))

/-- Concrete coverage corollary on the fixture:
with one true dependency and `topK = 1`, the greedy selector covers it exactly. -/
theorem bool_coverage_exact_one :
    dependencyCoverage dependencyBool
      (greedySelect dependencyBool checklistBool.topK) = 1 := by
  have hchain :
      GreedyChain dependencyBool checklistBool.topK
        (greedySelect dependencyBool checklistBool.topK) :=
    greedySelect_chain_of_le_card
      (D := dependencyBool) (k := checklistBool.topK)
      checklistBool.topK_le_pool
  have hcov :
      dependencyCoverage dependencyBool
        (greedySelect dependencyBool checklistBool.topK)
        = Nat.min checklistBool.topK dependencyBool.card :=
    greedyChain_coverage_eq_min
      (D := dependencyBool)
      (S := greedySelect dependencyBool checklistBool.topK)
      (i := checklistBool.topK) hchain
  simpa [dependencyBool, checklistBool] using hcov

/-- Finite-3 fixture scorer emphasizing `{0,1}` over `2`. -/
def globalPriorFin3 : Scorer Unit (Fin 3) :=
  ⟨fun _ f => if f = (0 : Fin 3) ∨ f = (1 : Fin 3) then ⟨6, 1⟩ else ⟨1, 6⟩⟩

/-- Finite-3 local scorer, aligned with the same preference. -/
def localPriorFin3 : Scorer Unit (Fin 3) :=
  ⟨fun _ f => if f = (0 : Fin 3) ∨ f = (1 : Fin 3) then ⟨5, 1⟩ else ⟨1, 5⟩⟩

/-- Finite-3 likelihood scorer, aligned with the same preference. -/
def likelihoodFin3 : Scorer Unit (Fin 3) :=
  ⟨fun _ f => if f = (0 : Fin 3) ∨ f = (1 : Fin 3) then ⟨7, 1⟩ else ⟨1, 7⟩⟩

/-- Explicit `topK = 2` checklist on `Fin 3`. -/
def checklistFin3 : PriorNBAssumptionChecklist Unit (Fin 3) Unit where
  inBin := fun _ => ()
  finitePool_nonempty := by decide
  localExchangeabilityInBin := True
  topK := 2
  topK_pos := by decide
  topK_le_pool := by decide
  surrogateCoverageObjective := True

def dependencyFin3 : Finset (Fin 3) := ({0, 1} : Finset (Fin 3))

def etaFin3 : Fin 3 → ℝ :=
  pooledSelectorScore globalPriorFin3 localPriorFin3 likelihoodFin3 ()

def deltaZeroFin3 : Fin 3 → ℝ := fun _ => 0

lemma localExchangeabilityFin3 :
    checklistFin3.localExchangeabilityInBin := by
  trivial

lemma pooledRankingFin3 :
    BayesOptimalRanking etaFin3
      (pooledSelectorScore globalPriorFin3 localPriorFin3 likelihoodFin3 ()) := by
  intro x y
  simp [etaFin3]

lemma twoStageRankingFin3 :
    BayesOptimalRanking etaFin3
      (twoStageSelectorScore globalPriorFin3 localPriorFin3 likelihoodFin3 ()) := by
  have hSel :=
    selector_default_ranking_iff
      (A := checklistFin3) (η := etaFin3)
      (globalPrior := globalPriorFin3) (localPrior := localPriorFin3)
      (likelihood := likelihoodFin3) (g := ())
      localExchangeabilityFin3
  exact hSel.2.2.mp pooledRankingFin3

lemma marginFin3 :
    ∀ x y, etaFin3 x < etaFin3 y →
      pooledSelectorScore globalPriorFin3 localPriorFin3 likelihoodFin3 () y
        - pooledSelectorScore globalPriorFin3 localPriorFin3 likelihoodFin3 () x
          > 2 * (0 : ℝ) := by
  intro x y hlt
  have hpos :
      pooledSelectorScore globalPriorFin3 localPriorFin3 likelihoodFin3 () y
        - pooledSelectorScore globalPriorFin3 localPriorFin3 likelihoodFin3 () x
          > 0 := by
    exact sub_pos.mpr (by simpa [etaFin3] using hlt)
  simpa using hpos

/-- Worked Chapter-13 theorem with nontrivial budget `topK = 2`. -/
theorem fin3_end_to_end_algorithmic_topK2 :
    let G := greedySelect dependencyFin3 checklistFin3.topK
    checklistFin3.topK ≤ Fintype.card (Fin 3)
      ∧ (∀ g' f',
          0 ≤ (selectorDefaults_halfGate Unit (Fin 3)).gate g' f'
            ∧ (selectorDefaults_halfGate Unit (Fin 3)).gate g' f' ≤ 1)
      ∧ BayesOptimalRanking etaFin3
          (perturbedScore
            (pooledSelectorScore globalPriorFin3 localPriorFin3 likelihoodFin3 ())
            deltaZeroFin3)
      ∧ (1 - Real.exp (-1))
          * (Nat.min checklistFin3.topK dependencyFin3.card : ℝ)
          ≤ dependencyCoverage dependencyFin3 G := by
  simpa [deltaZeroFin3] using
    (inferenceControl_end_to_end_algorithmic
      (A := checklistFin3) (η := etaFin3)
      (globalPrior := globalPriorFin3) (localPrior := localPriorFin3)
      (likelihood := likelihoodFin3) (g := ())
      localExchangeabilityFin3
      (δ := deltaZeroFin3) (ε := 0)
      twoStageRankingFin3
      (hbound := by intro x; simp [deltaZeroFin3])
      (hmargin := marginFin3)
      (htie := by intro x y hxy; simp [deltaZeroFin3])
      (D := dependencyFin3))

/-- Concrete `topK = 2` coverage corollary on the `Fin 3` fixture. -/
theorem fin3_coverage_exact_two :
    dependencyCoverage dependencyFin3
      (greedySelect dependencyFin3 checklistFin3.topK) = 2 := by
  have hchain :
      GreedyChain dependencyFin3 checklistFin3.topK
        (greedySelect dependencyFin3 checklistFin3.topK) :=
    greedySelect_chain_of_le_card
      (D := dependencyFin3) (k := checklistFin3.topK)
      checklistFin3.topK_le_pool
  have hcov :
      dependencyCoverage dependencyFin3
        (greedySelect dependencyFin3 checklistFin3.topK)
        = Nat.min checklistFin3.topK dependencyFin3.card :=
    greedyChain_coverage_eq_min
      (D := dependencyFin3)
      (S := greedySelect dependencyFin3 checklistFin3.topK)
      (i := checklistFin3.topK) hchain
  simpa [checklistFin3, dependencyFin3] using hcov

end

end Mettapedia.PLN.InferenceControl.PremiseSelection.PLNInferenceControlExamples
