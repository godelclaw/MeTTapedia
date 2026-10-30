import Mathlib.Tactic

/-!
# Context preparation: accounting and representation boundaries

Incident model for a planner that omitted request-index framing and a model-key
lookup that distinguished Python text carriers. Sizes below are measured cost
units, not a proof that byte/token calibration equals a provider tokenizer.
The runtime still checks the fully rendered request before admission.

The central accounting theorem is necessary and sufficient: a planner is sound
for every capacity exactly when its cost upper-bounds the renderer's cost.
Sharing one component calculation repairs the observed framing mismatch;
adding a future rendered field requires re-establishing this bound.

These are executable mathematical models. Runtime correspondence is checked
by separate native regression witnesses; this file does not verify the C/Python
implementations, JSON serialization, or the semantic quality of a handoff.

Separating runtime witnesses: the request-index boundary regression in
`tests/test_context_compaction.py` and the foreign model-key calibration
regression in `tests/test_native_task_context.py` in the agent runtime.
-/

namespace Mettapedia.CognitiveArchitecture.Agent.ContextPreparation

structure Costs where
  fixed : Nat
  history : Nat
  requestIndex : Nat
deriving DecidableEq, Repr

def legacyCost (c : Costs) : Nat := c.fixed + c.history
def renderedCost (c : Costs) : Nat := c.fixed + c.history + c.requestIndex
def sharedCost (c : Costs) : Nat := renderedCost c

inductive Decision where
  | ready | compact
deriving DecidableEq, Repr

def decide (cost capacity : Nat) : Decision :=
  if cost ≤ capacity then .ready else .compact

/-- Every positive omitted index cost supplies a counterexample, independently
of the fixed instructions and transcript size. -/
theorem omitted_cost_counterexample (fixed history index : Nat) (h : 0 < index) :
    let c : Costs := ⟨fixed, history, index⟩
    decide (legacyCost c) (fixed + history) = .ready ∧
      decide (renderedCost c) (fixed + history) = .compact := by
  simp [decide, legacyCost, renderedCost]
  omega

example : decide (legacyCost ⟨100, 800, 20⟩) 910 = .ready ∧
    decide (renderedCost ⟨100, 800, 20⟩) 910 = .compact := by decide

/-- This is the exact obligation, rather than equality with a particular
renderer: a conservative upper bound is also sound. -/
theorem sound_for_all_capacities_iff (planned actual : Nat) :
    (∀ capacity, planned ≤ capacity → actual ≤ capacity) ↔ actual ≤ planned := by
  constructor
  · intro h
    exact h planned (Nat.le_refl _)
  · intro h capacity admitted
    exact Nat.le_trans h admitted

theorem repaired_planner_agrees (c : Costs) (capacity : Nat) :
    decide (sharedCost c) capacity = decide (renderedCost c) capacity := rfl

theorem repaired_ready_fits (c : Costs) (capacity : Nat)
    (h : decide (sharedCost c) capacity = .ready) : renderedCost c ≤ capacity := by
  by_contra notFits
  simp [decide, sharedCost, notFits] at h

inductive Preparation where
  | ready | needsCompaction | unchangedRetry
deriving DecidableEq, Repr

/-- The old control path can refuse rendering after it skipped maintenance. -/
def legacyPrepare (c : Costs) (capacity : Nat) : Preparation :=
  if legacyCost c ≤ capacity then
    if renderedCost c ≤ capacity then .ready else .unchangedRetry
  else .needsCompaction

def repairedPrepare (c : Costs) (capacity : Nat) : Preparation :=
  if sharedCost c ≤ capacity then .ready else .needsCompaction

def repeatLegacy (c : Costs) (capacity : Nat) : Nat → Preparation
  | 0 => legacyPrepare c capacity
  | n + 1 => match repeatLegacy c capacity n with
    | .unchangedRetry => legacyPrepare c capacity
    | result => result

/-- More retries cannot repair an unchanged planner/renderer disagreement. -/
theorem unchanged_retry_forever (c : Costs) (capacity : Nat)
    (h : legacyPrepare c capacity = .unchangedRetry) (n : Nat) :
    repeatLegacy c capacity n = .unchangedRetry := by
  induction n with
  | zero => exact h
  | succ n ih => simp [repeatLegacy, ih, h]

theorem repaired_never_unchanged_retry (c : Costs) (capacity : Nat) :
    repairedPrepare c capacity ≠ .unchangedRetry := by
  unfold repairedPrepare
  split <;> simp

/-- A rendered request is admitted only through the final measured check.
This does not assert that successful compaction is always possible. -/
def admitRendered (measure : String → Nat) (capacity : Nat) (text : String) : Option String :=
  if measure text ≤ capacity then some text else none

theorem final_admission_is_bounded (measure : String → Nat) (capacity : Nat) (input output : String)
    (h : admitRendered measure capacity input = some output) : measure output ≤ capacity := by
  unfold admitRendered at h
  split at h
  · rename_i fits
    cases h
    exact fits
  · simp at h

/-- An unchanged failed view is not a successful empty model response. -/
def mayAcknowledgeInput : Preparation → Bool
  | .ready => true
  | _ => false

theorem preparation_failure_preserves_pending_input :
    mayAcknowledgeInput .unchangedRetry = false ∧
      mayAcknowledgeInput .needsCompaction = false := by decide

/-! ## JSON keys at the host boundary -/

inductive HostText where
  | string (text : String)
  | symbol (text : String)
deriving DecidableEq, Repr

def textKey : HostText → String
  | .string s | .symbol s => s

def legacyLookup {α : Type} (table : String → Option α) : HostText → Option α
  | .string s => table s
  | .symbol _ => none

def normalizedLookup {α : Type} (table : String → Option α) (key : HostText) : Option α :=
  table (textKey key)

theorem legacy_carrier_miss {α : Type} (table : String → Option α)
    (model : String) (value : α) (h : table model = some value) :
    legacyLookup table (.string model) = some value ∧
      legacyLookup table (.symbol model) = none := by
  exact ⟨h, rfl⟩

theorem normalized_lookup_representation_independent {α : Type}
    (table : String → Option α) (model : String) :
    normalizedLookup table (.string model) = normalizedLookup table (.symbol model) := rfl

theorem normalized_lookup_retains_calibration {α : Type}
    (table : String → Option α) (model : String) (value : α)
    (h : table model = some value) :
    normalizedLookup table (.symbol model) = some value := h

end Mettapedia.CognitiveArchitecture.Agent.ContextPreparation
