import Mettapedia.CogArch.Attention.PremiseActivation
import Mettapedia.Algorithms.Retrieval.RetrievalContract

/-!
# Limits of relevance guarantees for activation spreading

Exact rational-valued finite controls. Score convergence does not imply better
recall. A late-payoff bridge need not have concave usefulness. The second
control has five nodes and two useful leaves; a third leaf requires six nodes.
-/

noncomputable section
namespace Mettapedia.CogArch.Attention.SpreadingExamples
open scoped BigOperators
open Mettapedia.ProbabilityTheory.MarkovChain
open Mettapedia.Algorithms.Retrieval.RetrievalContract

inductive HubNode | a | b | h deriving DecidableEq
open HubNode
instance : Fintype HubNode := ⟨{a, b, h}, by intro i; cases i <;> simp⟩

private theorem hub_sum (f : HubNode → ℝ) : ∑ i, f i = f a + f b + f h := by
  change ∑ i ∈ ({a, b, h} : Finset HubNode), f i = _
  simp [Finset.sum_insert, add_assoc]

def hubMatrix : Matrix HubNode HubNode ℝ
  | b, a => 3/5
  | h, a => 2/5
  | h, _ => 1
  | _, _ => 0

def hubWalk : Restart.RestartWalk HubNode where
  P := hubMatrix
  nonneg := by intro i j; cases i <;> cases j <;> norm_num [hubMatrix]
  col_le := by intro j; cases j <;> norm_num [hub_sum, hubMatrix]
  α := 1/2
  α_pos := by norm_num
  α_le := by norm_num

def hubSeed : HubNode → ℝ | a => 1 | _ => 0
def hubFirst : HubNode → ℝ | a => 1/2 | b => 3/10 | h => 1/5
def hubSecond : HubNode → ℝ | a => 1/2 | b => 3/20 | h => 7/20

theorem hub_first : hubWalk.step hubSeed hubSeed = hubFirst := by
  funext i; cases i <;> norm_num [Restart.RestartWalk.step, hubWalk,
    hubMatrix, hubSeed, hubFirst, Matrix.mulVec, dotProduct, hub_sum]

theorem hub_second : hubWalk.step hubSeed hubFirst = hubSecond := by
  funext i; cases i <;> norm_num [Restart.RestartWalk.step, hubWalk,
    hubMatrix, hubSeed, hubFirst, hubSecond, Matrix.mulVec, dotProduct, hub_sum]

theorem hub_fixed : hubWalk.ppr hubSeed = hubSecond := by
  symm
  apply hubWalk.ppr_unique
  funext i; cases i <;> norm_num [Restart.RestartWalk.step, hubWalk,
    hubMatrix, hubSeed, hubSecond, Matrix.mulVec, dotProduct, hub_sum]

/-- The needed B loses its top-two place after another round, at equilibrium. -/
theorem extra_round_lowers_recall :
    IsTopK hubFirst 2 Finset.univ {a, b} ∧
    IsTopK hubSecond 2 Finset.univ {a, h} ∧
    (({a, b} : Finset HubNode) ∩ {b}).card = 1 ∧
    (({a, h} : Finset HubNode) ∩ {b}).card = 0 ∧
    hubWalk.ppr hubSeed = hubSecond := by
  refine ⟨?_, ?_, by decide, by decide, hub_fixed⟩
  · refine ⟨by simp, by decide, ?_⟩
    intro i hi j _ hj
    cases i <;> cases j <;> norm_num [hubFirst] at *
  · refine ⟨by simp, by decide, ?_⟩
    intro i hi j _ hj
    cases i <;> cases j <;> norm_num [hubSecond] at *

inductive BridgeNode | start | x | y | u | v deriving DecidableEq
open BridgeNode
instance : Fintype BridgeNode := ⟨{start, x, y, u, v}, by intro i; cases i <;> simp⟩

private theorem bridge_sum (f : BridgeNode → ℝ) :
    ∑ i, f i = f start + f x + f y + f u + f v := by
  change ∑ i ∈ ({start, x, y, u, v} : Finset BridgeNode), f i = _
  simp [Finset.sum_insert, add_assoc]

def bridgeMatrix : Matrix BridgeNode BridgeNode ℝ
  | start, x => 1
  | x, y => 1
  | y, u => 1/2
  | y, v => 1/2
  | u, u => 1
  | v, v => 1
  | _, _ => 0

def bridgeKernel : FiniteMassTransport.Kernel BridgeNode := by
  letI : DecidableEq BridgeNode := Classical.decEq BridgeNode
  exact ⟨bridgeMatrix, Matrix.mem_rowStochastic_iff_sum.mpr ⟨by
    intro i j; cases i <;> cases j <;> norm_num [bridgeMatrix],
    by intro i; cases i <;> norm_num [bridge_sum, bridgeMatrix]⟩⟩

private theorem bridge_exists (p : BridgeNode → Prop) :
    (∃ i, p i) ↔ p start ∨ p x ∨ p y ∨ p u ∨ p v := by
  constructor
  · rintro ⟨i, hi⟩; cases i <;> tauto
  · intro h; rcases h with h | h | h | h | h <;> exact ⟨_, h⟩

def bridgeHits (n : ℕ) : ℕ :=
  ((PremiseActivation.pool bridgeKernel {start} n) ∩ {u, v}).card

/-- A bridge gives no useful hits at depths 0/1/2, then two hits at depth 3. -/
theorem usefulness_gain_not_concave :
    bridgeHits 0 = 0 ∧ bridgeHits 1 = 0 ∧ bridgeHits 2 = 0 ∧
    bridgeHits 3 = 2 ∧
    bridgeHits 2 - bridgeHits 1 < bridgeHits 3 - bridgeHits 2 := by
  have hp (n : ℕ) (T : Finset BridgeNode)
      (h : ∀ i, i ∈ PremiseActivation.pool bridgeKernel {start} n ↔ i ∈ T) :
      PremiseActivation.pool bridgeKernel {start} n = T := Finset.ext h
  have h0 : PremiseActivation.pool bridgeKernel {start} 0 = {start} := by
    apply hp; intro i; cases i <;> simp [PremiseActivation.pool, FiniteMassTransport.reachable]
  have h1 : PremiseActivation.pool bridgeKernel {start} 1 = {start, x} := by
    apply hp; intro i; cases i <;>
      norm_num [PremiseActivation.pool, FiniteMassTransport.reachable, bridge_exists,
        bridgeKernel, FiniteMassTransport.Kernel.share, bridgeMatrix]
    all_goals decide
  have h2 : PremiseActivation.pool bridgeKernel {start} 2 = {start, x, y} := by
    apply hp; intro i; cases i <;>
      norm_num [PremiseActivation.pool, FiniteMassTransport.reachable, bridge_exists,
        bridgeKernel, FiniteMassTransport.Kernel.share, bridgeMatrix]
    all_goals decide
  have h3 : PremiseActivation.pool bridgeKernel {start} 3 = Finset.univ := by
    apply hp; intro i; cases i <;>
      norm_num [PremiseActivation.pool, FiniteMassTransport.reachable, bridge_exists,
        bridgeKernel, FiniteMassTransport.Kernel.share, bridgeMatrix]
  simp only [bridgeHits, h0, h1, h2, h3]
  decide

end Mettapedia.CogArch.Attention.SpreadingExamples
