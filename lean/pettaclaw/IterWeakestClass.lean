import WeakAgentEcology

/-!
# Iter minimality under an explicit class

“Weakest” is meaningful only relative to a class and an order. This file
separates two claims.

First, the transaction rule shared by Iter transformations and the weak open
process core is uniquely determined by two desirable equations: install every
successful candidate exactly, and preserve the current state on failure. The
ordered Iter fold is likewise the unique list runner satisfying the empty and
successor equations below.

Second, the complete reference Iter runtime is not the weakest persistent agent
host. It adds concrete memory, tool, ordering, pacing, and restart policies and
does not satisfy the already-stated necessary PettaClaw host feature check. The
two-equation open process core is weaker: it hosts the Iter transformation fold
exactly while remaining polymorphic in the periphery and its policy ecology.

The public Iter transformation reducer is unchanged between the source revision
modeled by `IterArchitecture` and public master commit
`f4064d97849ecaccac7939315a3f1a68de15c3ef` (2026-08-24). Browser packaging is
outside this theorem boundary.
-/

namespace IterWeakestClass

open WeakSelfHostingCore

/-! ## The weakest transactional replacement rule -/

abbrev Runner (State : Type) := State → Outcome State → State

/-- These are semantic desiderata, not implementation clauses: all successful
successors remain possible, and a failed candidate cannot destroy the current
state. -/
def TransactionalPlasticity {State : Type} (runner : Runner State) : Prop :=
  (∀ before next, runner before (.success next) = next) ∧
    (∀ before, runner before .failure = before)

def replaceOrStutter {State : Type} : Runner State
  | _, .success next => next
  | before, .failure => before

theorem replace_or_stutter_satisfies_transactional_plasticity {State : Type} :
    TransactionalPlasticity (@replaceOrStutter State) := by
  exact ⟨fun _ _ => rfl, fun _ => rfl⟩

/-- No alternative deterministic runner satisfies the two desiderata. This is
stronger than a source-size claim: any additional rejection or fallback policy
would violate at least one equation. -/
theorem replace_or_stutter_is_unique {State : Type}
    (runner : Runner State) (contract : TransactionalPlasticity runner) :
    runner = @replaceOrStutter State := by
  funext before outcome
  cases outcome with
  | success next => exact contract.1 before next
  | failure => exact contract.2 before

/-! ## Iter is the free ordered fold of its one-step reducer -/

abbrev Pipeline :=
  List IterArchitecture.Transformation →
    IterArchitecture.Boundary → IterArchitecture.Boundary

def OrderedFoldContract (pipeline : Pipeline) : Prop :=
  (∀ boundary, pipeline [] boundary = boundary) ∧
    (∀ transformation rest boundary,
      pipeline (transformation :: rest) boundary =
        pipeline rest
          (IterArchitecture.applyTransformation boundary transformation))

theorem iter_pipeline_satisfies_ordered_fold_contract :
    OrderedFoldContract IterArchitecture.applyTransformations := by
  exact ⟨fun _ => rfl, fun _ _ _ => rfl⟩

theorem iter_pipeline_is_unique_ordered_fold
    (pipeline : Pipeline) (contract : OrderedFoldContract pipeline) :
    pipeline = IterArchitecture.applyTransformations := by
  funext transformations boundary
  induction transformations generalizing boundary with
  | nil => exact contract.1 boundary
  | cons transformation rest ih =>
      rw [contract.2 transformation rest boundary]
      exact ih (IterArchitecture.applyTransformation boundary transformation)

/-! ## Exact hosting without making Iter the kernel -/

theorem weak_process_core_hosts_iter_exactly {Root : Type}
    (root : Root) (boundary : IterArchitecture.Boundary)
    (transformations : List IterArchitecture.Transformation) :
    (WeakAgentEcology.runProcesses
      (transformations.map WeakAgentEcology.fromIter)
      ({ root := root, periphery := boundary } :
        WeakAgentEcology.Rooted Root IterArchitecture.Boundary)).periphery =
      IterArchitecture.applyTransformations transformations boundary := by
  exact WeakAgentEcology.iter_pipeline_is_exact root boundary transformations

/-- Full Iter carries concrete host policy and is not a drop-in implementation
of the stated persistent-life requirements. This does not criticize Iter's
chosen policies. It shows why the transactional minimality theorem above must
not be silently widened into a class-independent claim about the complete
runtime. -/
theorem full_reference_iter_requires_persistent_host_adapter :
    ¬ IterArchitecture.meetsPettaCoreRequirements
      IterArchitecture.iterReferenceFeatures := by
  exact IterArchitecture.iter_reference_is_not_drop_in_pettaclaw_host

/-- The weaker ecology loses no history-sensitive controller expressiveness:
using the identity context projection hosts an arbitrary such transition. -/
theorem weak_ecology_hosts_every_history_sensitive_controller
    {Root Event Periphery : Type}
    (state : WeakAgentEcology.Rooted Root Periphery)
    (history : List Event)
    (agent : List Event → Periphery → Outcome Periphery) :
    WeakAgentEcology.turn state WeakAgentEcology.identityContext history agent =
      OpenEndedProcessCore.invoke state (agent history) := by
  exact WeakAgentEcology.every_history_sensitive_agent_is_hostable
    state history agent

end IterWeakestClass

#print axioms IterWeakestClass.replace_or_stutter_is_unique
#print axioms IterWeakestClass.iter_pipeline_is_unique_ordered_fold
#print axioms IterWeakestClass.weak_process_core_hosts_iter_exactly
#print axioms IterWeakestClass.full_reference_iter_requires_persistent_host_adapter
#print axioms IterWeakestClass.weak_ecology_hosts_every_history_sensitive_controller
