import Mettapedia.GSLT.Meredith.InteractiveGSLT
import Mettapedia.GSLT.Meredith.Bisimulation
import Mettapedia.GSLT.Meredith.AgentPopulation

/-! # Interaction Metrics

Quantitative measures of interaction structure in agent populations.
All definitions are List-based to avoid Finset decidability issues. -/

namespace Mettapedia.GSLT.Meredith

open Bisimulation

/-- Count interactions from agent a to agent b. -/
def interactionCount {S : GSLT} {W : Type*}
    (pop : AgentPopulation S W) (a b : BisimQuotient S) : Nat :=
  (pop.interactions a b).length

/-- Total interactions involving agent a (both directions). -/
noncomputable def agentDegree {S : GSLT} {W : Type*}
    (pop : AgentPopulation S W) (a : BisimQuotient S) : Nat :=
  pop.agents.sum (fun b =>
    (pop.interactions a b).length + (pop.interactions b a).length)

/-- Whether two agents have at least one interaction in either direction. -/
def isConnected {S : GSLT} {W : Type*}
    (pop : AgentPopulation S W) (a b : BisimQuotient S) : Bool :=
  !(pop.interactions a b).isEmpty || !(pop.interactions b a).isEmpty

/-- Empty population: zero degree for any agent (vacuously). -/
theorem agentDegree_empty (S : GSLT) (W : Type*) (a : BisimQuotient S) :
    agentDegree (emptyAgentPopulation S W) a = 0 := by
  simp [agentDegree, emptyAgentPopulation]

/-- Empty population: nothing is connected. -/
theorem isConnected_empty (S : GSLT) (W : Type*)
    (a b : BisimQuotient S) :
    isConnected (emptyAgentPopulation S W) a b = false := by
  simp [isConnected, emptyAgentPopulation]

/-- interactionCount on empty population is zero. -/
theorem interactionCount_empty (S : GSLT) (W : Type*)
    (a b : BisimQuotient S) :
    interactionCount (emptyAgentPopulation S W) a b = 0 := by
  simp [interactionCount, emptyAgentPopulation]

/-- Singleton population: zero interaction count between any pair. -/
theorem interactionCount_singleton (S : GSLT) [DecidableEq (BisimQuotient S)]
    (W : Type*) (a b : BisimQuotient S) :
    interactionCount (singletonAgentPopulation S a W) a b = 0 := by
  simp [interactionCount, singletonAgentPopulation]

/-- Singleton population: no connections. -/
theorem isConnected_singleton (S : GSLT) [DecidableEq (BisimQuotient S)]
    (W : Type*) (a b : BisimQuotient S) :
    isConnected (singletonAgentPopulation S a W) a b = false := by
  simp [isConnected, singletonAgentPopulation]

/-- Two-agent population: exactly one interaction from a to b. -/
theorem interactionCount_two (S : GSLT) [DecidableEq (BisimQuotient S)]
    (W : Type*) (a b : BisimQuotient S) (hab : a ≠ b) (w : W) :
    interactionCount (twoAgentPopulation S W a b hab w) a b = 1 := by
  simp [interactionCount, twoAgentPopulation]

/-- Two-agent population: a and b are connected. -/
theorem isConnected_two (S : GSLT) [DecidableEq (BisimQuotient S)]
    (W : Type*) (a b : BisimQuotient S) (hab : a ≠ b) (w : W) :
    isConnected (twoAgentPopulation S W a b hab w) a b = true := by
  simp [isConnected, twoAgentPopulation, hab]

/-- Singleton population: agent a has zero degree. -/
theorem agentDegree_singleton (S : GSLT) [DecidableEq (BisimQuotient S)]
    (W : Type*) (a : BisimQuotient S) :
    agentDegree (singletonAgentPopulation S a W) a = 0 := by
  simp [agentDegree, singletonAgentPopulation]

/-- Two-agent population: agent a has degree 1 (one outgoing interaction). -/
theorem agentDegree_two_a (S : GSLT) [DecidableEq (BisimQuotient S)]
    (W : Type*) (a b : BisimQuotient S) (hab : a ≠ b) (w : W) :
    agentDegree (twoAgentPopulation S W a b hab w) a = 1 := by
  simp [agentDegree, twoAgentPopulation, hab]

/-- Two-agent population: agent b has degree 1 (one incoming interaction). -/
theorem agentDegree_two_b (S : GSLT) [DecidableEq (BisimQuotient S)]
    (W : Type*) (a b : BisimQuotient S) (hab : a ≠ b) (w : W) :
    agentDegree (twoAgentPopulation S W a b hab w) b = 1 := by
  simp [agentDegree, twoAgentPopulation, hab, hab.symm]

/-! ## Cost-tracked population integration theorems -/

/-- Empty cost-tracked population: zero interaction count. -/
theorem interactionCount_emptyRhoCostTracked (a b : BisimQuotient RhoExample.rhoGSLT) :
    interactionCount emptyRhoCostTrackedPopulation.toAgentPopulation a b = 0 := by
  simp [interactionCount, emptyRhoCostTrackedPopulation]

/-- Empty cost-tracked population: nothing connected. -/
theorem isConnected_emptyRhoCostTracked (a b : BisimQuotient RhoExample.rhoGSLT) :
    isConnected emptyRhoCostTrackedPopulation.toAgentPopulation a b = false := by
  simp [isConnected, emptyRhoCostTrackedPopulation]

/-- Empty cost-tracked population: zero degree. -/
theorem agentDegree_emptyRhoCostTracked (a : BisimQuotient RhoExample.rhoGSLT) :
    agentDegree emptyRhoCostTrackedPopulation.toAgentPopulation a = 0 := by
  simp [agentDegree, emptyRhoCostTrackedPopulation]

/-- Singleton cost-tracked population: zero interaction count. -/
theorem interactionCount_singletonRhoCostTracked
    (a b : BisimQuotient RhoExample.rhoGSLT) :
    interactionCount (singletonRhoCostTrackedPopulation a).toAgentPopulation a b = 0 := by
  simp [interactionCount, singletonRhoCostTrackedPopulation]

/-- Singleton cost-tracked population: no connections. -/
theorem isConnected_singletonRhoCostTracked
    (a b : BisimQuotient RhoExample.rhoGSLT) :
    isConnected (singletonRhoCostTrackedPopulation a).toAgentPopulation a b = false := by
  simp [isConnected, singletonRhoCostTrackedPopulation]

/-- Singleton cost-tracked population: zero degree. -/
theorem agentDegree_singletonRhoCostTracked
    (a : BisimQuotient RhoExample.rhoGSLT) :
    agentDegree (singletonRhoCostTrackedPopulation a).toAgentPopulation a = 0 := by
  simp [agentDegree, singletonRhoCostTrackedPopulation]

/-- Two-agent cost-tracked population: zero interaction count (no interactions). -/
theorem interactionCount_twoRhoCostTracked
    (a b : BisimQuotient RhoExample.rhoGSLT) (_hab : a ≠ b) :
    interactionCount (twoRhoCostTrackedPopulation a b _hab).toAgentPopulation a b = 0 := by
  simp [interactionCount, twoRhoCostTrackedPopulation]

/-- Two-agent cost-tracked population: not connected (no interactions). -/
theorem isConnected_twoRhoCostTracked
    (a b : BisimQuotient RhoExample.rhoGSLT) (hab : a ≠ b) :
    isConnected (twoRhoCostTrackedPopulation a b hab).toAgentPopulation a b = false := by
  simp [isConnected, twoRhoCostTrackedPopulation]

end Mettapedia.GSLT.Meredith
