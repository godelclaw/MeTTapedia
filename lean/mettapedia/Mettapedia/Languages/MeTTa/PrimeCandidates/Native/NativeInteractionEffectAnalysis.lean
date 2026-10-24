import Mettapedia.GSLT.Causality.ResourceInteraction
import Mathlib.Data.Multiset.UnionInter
import Mettapedia.GSLT.Dynamics.InteractionEventValuation
import Mettapedia.Languages.MeTTa.PrimeCandidates.Native.NativeInteractionFibration

/-!
# Linear-effect analysis for native interaction

Interaction-site names and operational resources are distinct coordinates.
Site predicates classify where an occurrence belongs; a linear-effect
description records the exact multiset occurrences it consumes and produces.
Parallel execution is licensed by the latter: the combined consumption must
fit in one source inventory.

The analysis is executable.  It computes the unique multiset remainder and
returns a proof-relevant separation certificate in `Type`.  A rejected
analysis returns `none`; it does not create a sequential execution.  The Cost
specialization reads its effect description directly from `CostedEvent`, then
converts a successful generic certificate into the product-factorization and
WorkSpan interface of `NativeInteractionFibration`.
-/

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.NativeInteractionEffectAnalysis

open Mettapedia.GSLT
open Mettapedia.GSLT.Causality.ResourceInteraction
open Mettapedia.GSLT.Core.InteractionComposition
open Mettapedia.GSLT.Core.InteractionEvent
open Mettapedia.GSLT.Dynamics.InteractionEventValuation
open Mettapedia.Languages.MeTTa.PrimeCandidates.NativeInteractionFibration
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost

universe uSite uResource uEvent uGround

/-! ## Cost-rho specialization -/

/-- A concrete funded Cost-rho event already contains its complete linear
effect description: interaction location, consumed endpoints and purses, and
produced contractum and purse tails. -/
def costEventEffect {Ground : Type uGround} (event : CostedEvent Ground) :
    LinearEffect (CostName Ground) (CostTerm Ground) where
  site := event.location
  consumed := event.consumed
  produced := event.produced

namespace CostEffectSeparation

variable {Ground : Type uGround} [DecidableEq Ground]
variable {source : CostConfig Ground} {left right : CostedEvent Ground}

/-- Convert generic linear separation into the concrete Cost-rho
factorization certificate. -/
def ofLinear
    (separation : PairSeparation source (costEventEffect left)
      (costEventEffect right)) :
    CostEffectSeparation Ground source left right where
  frame := separation.frame
  source_eq := by
    simpa [PairSeparation.demand, costEventEffect, costWaveSource,
      CostedEvent.consumed] using separation.source_eq

/-- Compute a Cost-rho effect separation from the exact source and the two
typed funded events. -/
def analyze? : Option (CostEffectSeparation Ground source left right) :=
  (PairSeparation.analyze? source (costEventEffect left)
    (costEventEffect right)).map ofLinear

/-- The Cost analysis succeeds exactly when both events' occurrence
multisets fit in the common source. -/
theorem analyze?_isSome_iff :
    (analyze? (source := source) (left := left) (right := right)).isSome =
      true ↔
      left.consumed + right.consumed ≤ source := by
  simp only [analyze?, Option.isSome_map]
  simpa [PairSeparation.demand, costEventEffect] using
    (PairSeparation.analyze?_isSome_iff
      (source := source) (left := costEventEffect left)
      (right := costEventEffect right))

/-- Every previously supplied Cost-rho separation is accepted by the
executable producer. -/
theorem analyze?_complete
    (separation : CostEffectSeparation Ground source left right) :
    (analyze? (source := source) (left := left) (right := right)).isSome =
      true := by
  rw [analyze?_isSome_iff]
  apply Multiset.le_iff_exists_add.mpr
  refine ⟨separation.frame, ?_⟩
  simpa [costWaveSource, add_assoc] using separation.source_eq

/-- Any successful producer result immediately supplies the concrete
commuting diamond. -/
theorem diamond_of_analyze?_eq_some
    {separation : CostEffectSeparation Ground source left right}
    (_result : analyze? (source := source) (left := left) (right := right) =
      some separation) :
    CostedDiamond source left right :=
  separation.diamond

/-- Any successful producer result immediately supplies the one-wave
work/span law. -/
theorem workSpan_of_analyze?_eq_some
    {separation : CostEffectSeparation Ground source left right}
    (_result : analyze? (source := source) (left := left) (right := right) =
      some separation) :
    separation.schedule.workSpan = ⟨2, 1⟩ :=
  separation.schedule_workSpan

end CostEffectSeparation

/-! ## Positive and negative controls -/

namespace Examples

inductive Site where
  | alpha
  | beta
  deriving DecidableEq, Repr

inductive Resource where
  | first
  | second
  deriving DecidableEq, Repr

def sameSiteLeft : LinearEffect Site Resource :=
  ⟨.alpha, {.first}, 0⟩

def sameSiteRight : LinearEffect Site Resource :=
  ⟨.alpha, {.second}, 0⟩

/-- Equal sites do not prevent concurrent ownership when exact resources are
separate. -/
theorem same_site_distinct_resources_accepted :
    (PairSeparation.analyze? ({.first, .second} : Multiset Resource)
      sameSiteLeft sameSiteRight).isSome = true := by
  decide

def distinctSiteLeft : LinearEffect Site Resource :=
  ⟨.alpha, {.first}, 0⟩

def distinctSiteRight : LinearEffect Site Resource :=
  ⟨.beta, {.first}, 0⟩

theorem distinct_sites : distinctSiteLeft.site ≠ distinctSiteRight.site := by
  decide

/-- Distinct sites do not license concurrent ownership when both effects need
the sole occurrence of one linear resource. -/
theorem distinct_sites_shared_resource_rejected :
    (PairSeparation.analyze? ({.first} : Multiset Resource)
      distinctSiteLeft distinctSiteRight).isSome = false := by
  decide

/-- The same-channel funded Cost-rho example is accepted from its event data;
the caller need not supply the frame manually. -/
theorem sameChannel_cost_analysis_succeeds :
    (CostEffectSeparation.analyze?
      (source := NativeInteractionFibration.Examples.source)
      (left := NativeInteractionFibration.Examples.leftEvent)
      (right := NativeInteractionFibration.Examples.rightEvent)).isSome =
        true :=
  CostEffectSeparation.analyze?_complete
    NativeInteractionFibration.Examples.sameChannelSeparation

/-- The contested single-purse example is rejected by the executable
analysis. -/
theorem contested_cost_analysis_rejected :
    (CostEffectSeparation.analyze?
      (source := NativeInteractionFibration.Examples.contestedSource)
      (left := NativeInteractionFibration.Examples.leftEvent)
      (right := NativeInteractionFibration.Examples.leftCompetitor)).isSome =
        false := by
  decide

end Examples

#print axioms PairSeparation.analyze?_isSome_iff
#print axioms PairSeparation.analyze?_complete
#print axioms CostEffectSeparation.analyze?_isSome_iff
#print axioms CostEffectSeparation.diamond_of_analyze?_eq_some
#print axioms Examples.same_site_distinct_resources_accepted
#print axioms Examples.distinct_sites_shared_resource_rejected
#print axioms Examples.contested_cost_analysis_rejected

end Mettapedia.Languages.MeTTa.PrimeCandidates.NativeInteractionEffectAnalysis
