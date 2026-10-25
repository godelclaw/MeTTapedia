import Mettapedia.PLN.WorldModel.SufficientStatisticEncoder
import Mettapedia.PLN.WorldModel.Fixpoint.PLNWorldModelFixpointCascade
import Mettapedia.Hyperseed.VisibleConsequence
import Mettapedia.Hyperseed.Ultrainfinitism

/-!
# Observation ingestion, consequence closure, and visible readouts

Hyperseed is a thin exploration and observation-ingestion layer above the
existing WM foundations. This file carries two compatible interfaces:

- a generic `HyperseedKernel` / trace-fold interface for external agents,
- trace-seeded closure helpers over sufficient-statistics world models.

All visibility profiles observe the same closure and synchronous cascade by
intersection with a region. They do not prune inference. `VisibleConsequence`
characterizes when a restricted executor has exactly this observed behavior.
-/

namespace Mettapedia.Hyperseed

open Mettapedia.PLN.Evidence.EvidenceClass
open Mettapedia.PLN.Evidence
open Mettapedia.PLN.WorldModel
open Mettapedia.PLN.WorldModel.WorldModelAdditive
open Mettapedia.PLN.WorldModel.Fixpoint.PLNWorldModelFixpointClosure
open Mettapedia.PLN.WorldModel.Fixpoint.PLNWorldModelFixpointCascade
open Mettapedia.PLN.WorldModel
open Mettapedia.PLN.WorldModel.SufficientStatisticEncoder

/-! ## Observation envelope -/

/-- An observation tagged with source and timestamp metadata.
Generic over payload, source identifier, and time representation. -/
structure ObservationEnvelope (Obs Source Time : Type*) where
  source : Source
  time : Time
  payload : Obs

/-! ## Hyperseed kernel -/

/-- The Hyperseed exploration kernel: packages an ingestion function, a seed
query set, and a consequence rule pool over an existing WM state/query space.

- `ingest` folds a single observation into the WM state.
- `seedQueries` are the initial query obligations for closure.
- `rules` is the consequence rule pool.
-/
structure HyperseedKernel (Obs State Query : Type*)
    [EvidenceType State] [BinaryWorldModel State Query] where
  ingest : Obs → State → State
  seedQueries : Set Query
  rules : RuleSet State Query

variable {Obs Query : Type*}
variable {Signal Cost : Type*} [Preorder Cost]

/-- Queries directly suggested by an observation trace. -/
def traceSeed (frontier : Obs → Set Query) (σ : Multiset Obs) : Set Query :=
  { q | ∃ o, o ∈ σ ∧ q ∈ frontier o }

@[simp] theorem mem_traceSeed
    (frontier : Obs → Set Query) (σ : Multiset Obs) (q : Query) :
    q ∈ traceSeed frontier σ ↔ ∃ o, o ∈ σ ∧ q ∈ frontier o :=
  Iff.rfl

@[simp] theorem traceSeed_zero
    (frontier : Obs → Set Query) :
    traceSeed frontier (0 : Multiset Obs) = (∅ : Set Query) := by
  ext q
  simp [traceSeed]

@[simp] theorem traceSeed_singleton
    (frontier : Obs → Set Query) (o : Obs) (q : Query) :
    q ∈ traceSeed frontier ({o} : Multiset Obs) ↔ q ∈ frontier o := by
  simp [traceSeed]

/-- Rule pool for Hyperseed over the binary WM induced by a sufficient-statistics
interface. -/
abbrev RulePool
    (S : SufficientStatisticEncoder Obs Query BinaryEvidence) :=
  letI : BinaryWorldModel (Multiset Obs) Query := worldModelOfAtomicEvidence S.observe
  RuleSet (Multiset Obs) Query

section TraceClosure

variable (S : SufficientStatisticEncoder Obs Query BinaryEvidence)
  (frontier : Obs → Set Query) (R : RulePool S) (σ : Multiset Obs)

/-- Hyperseed closure: observation-trace seeding plus WM fixpoint closure on the
binary evidence world model induced by a sufficient-statistics encoder. -/
noncomputable def closureFromTrace : Set Query :=
  letI : BinaryWorldModel (Multiset Obs) Query := worldModelOfAtomicEvidence S.observe
  leastRuleClosure R σ (traceSeed frontier σ)

/-- Fair synchronous Hyperseed cascade from an observation trace. -/
def cascadeFromTrace : ℕ → Set Query :=
  letI : BinaryWorldModel (Multiset Obs) Query := worldModelOfAtomicEvidence S.observe
  immediateIter R σ (traceSeed frontier σ)

theorem seed_subset_closureFromTrace :
    traceSeed frontier σ ⊆ closureFromTrace S frontier R σ := by
  let : BinaryWorldModel (Multiset Obs) Query := worldModelOfAtomicEvidence S.observe
  exact seed_subset_leastRuleClosure (R := R) (W := σ) (seed := traceSeed frontier σ)

theorem mem_closureFromTrace_iff_mem_cascade_card_of_finite
    [Fintype Query]
    (q : Query) :
    q ∈ closureFromTrace S frontier R σ ↔
      q ∈ cascadeFromTrace S frontier R σ (Fintype.card Query) := by
  let : BinaryWorldModel (Multiset Obs) Query := worldModelOfAtomicEvidence S.observe
  exact
    mem_leastRuleClosure_iff_mem_immediateIter_card_of_finite
      (R := R) (W := σ) (seed := traceSeed frontier σ) q

theorem mem_closureFromTrace_implies_eventualDiscovery_of_finite
    [Fintype Query]
    {q : Query}
    (hq : q ∈ closureFromTrace S frontier R σ) :
    ∃ N ≤ Fintype.card Query, q ∈ cascadeFromTrace S frontier R σ N := by
  let : BinaryWorldModel (Multiset Obs) Query := worldModelOfAtomicEvidence S.observe
  exact
    mem_leastRuleClosure_implies_eventual_discovery_of_finite
      (R := R) (W := σ) (seed := traceSeed frontier σ) hq

/-- A trace-seeded closure agrees with restricted inference under the boundary certificate. -/
theorem closureFromTrace_inter_visible (V : Set Query)
    (closed : letI : BinaryWorldModel (Multiset Obs) Query := worldModelOfAtomicEvidence S.observe
      BackwardClosedAt R σ V) :
    closureFromTrace S frontier R σ ∩ V =
      (letI : BinaryWorldModel (Multiset Obs) Query := worldModelOfAtomicEvidence S.observe
       leastRuleClosure (visibleRules R V) σ (traceSeed frontier σ ∩ V)) := by
  let : BinaryWorldModel (Multiset Obs) Query := worldModelOfAtomicEvidence S.observe
  exact leastRuleClosure_inter_visible R σ V closed (traceSeed frontier σ)

/-- The same observation square holds at every synchronous discovery round. -/
theorem cascadeFromTrace_inter_visible (V : Set Query)
    (closed : letI : BinaryWorldModel (Multiset Obs) Query := worldModelOfAtomicEvidence S.observe
      BackwardClosedAt R σ V) (n : ℕ) :
    cascadeFromTrace S frontier R σ n ∩ V =
      (letI : BinaryWorldModel (Multiset Obs) Query := worldModelOfAtomicEvidence S.observe
       immediateIter (visibleRules R V) σ (traceSeed frontier σ ∩ V) n) := by
  let : BinaryWorldModel (Multiset Obs) Query := worldModelOfAtomicEvidence S.observe
  exact immediateIter_inter_visible R σ V closed (traceSeed frontier σ) n

section Static

variable (P : Perspective Query Signal Cost) (B : Cost) (guard : Set Query)

/-- Perspective-filtered Hyperseed closure. This keeps the existing closure
engine but exposes the observer-relative/bounded slice visible from one
perspective. -/
def availableClosureFromTrace : Set Query :=
  closureFromTrace S frontier R σ ∩ availableRegion P B guard

/-- Perspective-filtered Hyperseed cascade. -/
def availableCascadeFromTrace : ℕ → Set Query :=
  fun n => cascadeFromTrace S frontier R σ n ∩ availableRegion P B guard

theorem mem_availableClosureFromTrace_iff
    (q : Query) :
    q ∈ availableClosureFromTrace S frontier R σ P B guard ↔
      q ∈ closureFromTrace S frontier R σ ∧ q ∈ availableRegion P B guard := by
  rfl

theorem availableClosureFromTrace_subset_closureFromTrace :
    availableClosureFromTrace S frontier R σ P B guard ⊆
      closureFromTrace S frontier R σ := by
  exact Set.inter_subset_left

theorem availableClosureFromTrace_subset_availableRegion :
    availableClosureFromTrace S frontier R σ P B guard ⊆
      availableRegion P B guard := by
  exact Set.inter_subset_right

theorem availableCascadeFromTrace_subset_cascadeFromTrace
    (n : ℕ) :
    availableCascadeFromTrace S frontier R σ P B guard n ⊆
      cascadeFromTrace S frontier R σ n := by
  exact Set.inter_subset_left

theorem availableCascadeFromTrace_subset_availableRegion
    (n : ℕ) :
    availableCascadeFromTrace S frontier R σ P B guard n ⊆
      availableRegion P B guard := by
  exact Set.inter_subset_right

theorem availableClosureFromTrace_mono_budget
    {B₁ B₂ : Cost}
    (hB : B₁ ≤ B₂) :
    availableClosureFromTrace S frontier R σ P B₁ guard ⊆
      availableClosureFromTrace S frontier R σ P B₂ guard := by
  exact Set.inter_subset_inter_right _ (availableRegion_mono_budget (P := P) (guard := guard) hB)

theorem availableCascadeFromTrace_mono_budget
    {B₁ B₂ : Cost}
    (hB : B₁ ≤ B₂)
    (n : ℕ) :
    availableCascadeFromTrace S frontier R σ P B₁ guard n ⊆
      availableCascadeFromTrace S frontier R σ P B₂ guard n := by
  exact Set.inter_subset_inter_right _ (availableRegion_mono_budget (P := P) (guard := guard) hB)

theorem availableClosureFromTrace_mono_guard
    {guard guard' : Set Query}
    (hguard : guard ⊆ guard') :
    availableClosureFromTrace S frontier R σ P B guard ⊆
      availableClosureFromTrace S frontier R σ P B guard' := by
  exact Set.inter_subset_inter_right _ (availableRegion_mono_guard (P := P) (B := B) hguard)

theorem availableCascadeFromTrace_mono_guard
    {guard guard' : Set Query}
    (hguard : guard ⊆ guard')
    (n : ℕ) :
    availableCascadeFromTrace S frontier R σ P B guard n ⊆
      availableCascadeFromTrace S frontier R σ P B guard' n := by
  exact Set.inter_subset_inter_right _ (availableRegion_mono_guard (P := P) (B := B) hguard)

theorem closureFromTrace_eq_availableClosureFromTrace_of_subset_availableRegion
    (hClosure : closureFromTrace S frontier R σ ⊆ availableRegion P B guard) :
    closureFromTrace S frontier R σ =
      availableClosureFromTrace S frontier R σ P B guard := by
  exact (Set.inter_eq_left.mpr hClosure).symm

theorem cascadeFromTrace_eq_availableCascadeFromTrace_of_subset_availableRegion
    (n : ℕ)
    (hCascade : cascadeFromTrace S frontier R σ n ⊆ availableRegion P B guard) :
    cascadeFromTrace S frontier R σ n =
      availableCascadeFromTrace S frontier R σ P B guard n := by
  exact (Set.inter_eq_left.mpr hCascade).symm

theorem mem_availableClosureFromTrace_iff_mem_availableCascade_card_of_finite
    [Fintype Query]
    (q : Query) :
    q ∈ availableClosureFromTrace S frontier R σ P B guard ↔
      q ∈ availableCascadeFromTrace S frontier R σ P B guard (Fintype.card Query) := by
  exact and_congr (mem_closureFromTrace_iff_mem_cascade_card_of_finite S frontier R σ q) Iff.rfl

/-- Budget-indexed available closure family for one fixed trace. -/
def availableClosureApproximationFromTrace :
    ClosureApproximation (World := Query) Cost PUnit where
  approx B _ := availableClosureFromTrace S frontier R σ P B guard
  mono := by
    intro B₁ B₂ _ hB
    exact availableClosureFromTrace_mono_budget S frontier R σ P guard hB

end Static

section Stateful

variable (P : StatefulPerspective (Multiset Obs) Query Signal Cost) (B : Cost) (guard : Set Query)

/-- State-conditioned available closure: the admissible region itself may vary
with the current trace/state. This is the minimal Route 2 bridge from Hyperseed
into a regime-indexed WM semantics. -/
def stateAvailableClosureFromTrace : Set Query :=
  closureFromTrace S frontier R σ ∩ availableRegionAt P σ B guard

/-- State-conditioned available cascade. -/
def stateAvailableCascadeFromTrace : ℕ → Set Query :=
  fun n => cascadeFromTrace S frontier R σ n ∩ availableRegionAt P σ B guard

theorem mem_stateAvailableClosureFromTrace_iff

    (q : Query) :
    q ∈ stateAvailableClosureFromTrace S frontier R σ P B guard ↔
      q ∈ closureFromTrace S frontier R σ ∧ q ∈ availableRegionAt P σ B guard := by
  rfl

theorem stateAvailableClosureFromTrace_subset_closureFromTrace :
    stateAvailableClosureFromTrace S frontier R σ P B guard ⊆
      closureFromTrace S frontier R σ := by
  exact Set.inter_subset_left

theorem stateAvailableClosureFromTrace_subset_availableRegionAt :
    stateAvailableClosureFromTrace S frontier R σ P B guard ⊆
      availableRegionAt P σ B guard := by
  exact Set.inter_subset_right

theorem stateAvailableCascadeFromTrace_subset_cascadeFromTrace

    (n : ℕ) :
    stateAvailableCascadeFromTrace S frontier R σ P B guard n ⊆
      cascadeFromTrace S frontier R σ n := by
  exact Set.inter_subset_left

theorem stateAvailableCascadeFromTrace_subset_availableRegionAt

    (n : ℕ) :
    stateAvailableCascadeFromTrace S frontier R σ P B guard n ⊆
      availableRegionAt P σ B guard := by
  exact Set.inter_subset_right

theorem stateAvailableClosureFromTrace_mono_budget

    {B₁ B₂ : Cost}
    (hB : B₁ ≤ B₂) :
    stateAvailableClosureFromTrace S frontier R σ P B₁ guard ⊆
      stateAvailableClosureFromTrace S frontier R σ P B₂ guard := by
  exact Set.inter_subset_inter_right _ (availableRegionAt_mono_budget (P := P) (W := σ) guard hB)

theorem stateAvailableCascadeFromTrace_mono_budget

    {B₁ B₂ : Cost}
    (hB : B₁ ≤ B₂)
    (n : ℕ) :
    stateAvailableCascadeFromTrace S frontier R σ P B₁ guard n ⊆
      stateAvailableCascadeFromTrace S frontier R σ P B₂ guard n := by
  exact Set.inter_subset_inter_right _ (availableRegionAt_mono_budget (P := P) (W := σ) guard hB)

theorem stateAvailableClosureFromTrace_mono_guard

    {guard guard' : Set Query}
    (hguard : guard ⊆ guard') :
    stateAvailableClosureFromTrace S frontier R σ P B guard ⊆
      stateAvailableClosureFromTrace S frontier R σ P B guard' := by
  exact Set.inter_subset_inter_right _ (availableRegionAt_mono_guard (P := P) (W := σ) (B := B) hguard)

theorem stateAvailableCascadeFromTrace_mono_guard

    {guard guard' : Set Query}
    (hguard : guard ⊆ guard')
    (n : ℕ) :
    stateAvailableCascadeFromTrace S frontier R σ P B guard n ⊆
      stateAvailableCascadeFromTrace S frontier R σ P B guard' n := by
  exact Set.inter_subset_inter_right _ (availableRegionAt_mono_guard (P := P) (W := σ) (B := B) hguard)

theorem stateAvailableClosureFromTrace_eq_availableClosureFromTrace_freezePerspective :
    stateAvailableClosureFromTrace S frontier R σ P B guard =
      availableClosureFromTrace S frontier R σ (freezePerspective P σ) B guard := by
  rfl

theorem stateAvailableCascadeFromTrace_eq_availableCascadeFromTrace_freezePerspective

    (n : ℕ) :
    stateAvailableCascadeFromTrace S frontier R σ P B guard n =
      availableCascadeFromTrace S frontier R σ (freezePerspective P σ) B guard n := by
  rfl

theorem closureFromTrace_eq_stateAvailableClosureFromTrace_of_subset_availableRegionAt

    (hClosure : closureFromTrace S frontier R σ ⊆ availableRegionAt P σ B guard) :
    closureFromTrace S frontier R σ =
      stateAvailableClosureFromTrace S frontier R σ P B guard := by
  exact (Set.inter_eq_left.mpr hClosure).symm

theorem cascadeFromTrace_eq_stateAvailableCascadeFromTrace_of_subset_availableRegionAt

    (n : ℕ)
    (hCascade : cascadeFromTrace S frontier R σ n ⊆ availableRegionAt P σ B guard) :
    cascadeFromTrace S frontier R σ n =
      stateAvailableCascadeFromTrace S frontier R σ P B guard n := by
  exact (Set.inter_eq_left.mpr hCascade).symm

theorem mem_stateAvailableClosureFromTrace_iff_mem_stateAvailableCascade_card_of_finite
    [Fintype Query]

    (q : Query) :
    q ∈ stateAvailableClosureFromTrace S frontier R σ P B guard ↔
      q ∈ stateAvailableCascadeFromTrace S frontier R σ P B guard (Fintype.card Query) := by
  exact and_congr (mem_closureFromTrace_iff_mem_cascade_card_of_finite S frontier R σ q) Iff.rfl

end Stateful

section Staged

variable {Idx : Type*} [Preorder Idx] (F : StagedView (World := Query) Idx) (i : Idx)

/-- Stage-filtered Hyperseed closure. -/
def stagedClosureFromTrace : Set Query :=
  closureFromTrace S frontier R σ ∩ F.region i

/-- Stage-filtered Hyperseed cascade. -/
def stagedCascadeFromTrace : ℕ → Set Query :=
  fun n => cascadeFromTrace S frontier R σ n ∩ F.region i

theorem mem_stagedClosureFromTrace_iff
    (q : Query) :
    q ∈ stagedClosureFromTrace S frontier R σ F i ↔
      q ∈ closureFromTrace S frontier R σ ∧ q ∈ F.region i := by
  rfl

theorem stagedClosureFromTrace_subset_closureFromTrace :
    stagedClosureFromTrace S frontier R σ F i ⊆ closureFromTrace S frontier R σ := by
  exact Set.inter_subset_left

theorem stagedClosureFromTrace_subset_region :
    stagedClosureFromTrace S frontier R σ F i ⊆ F.region i := by
  exact Set.inter_subset_right

theorem stagedCascadeFromTrace_subset_cascadeFromTrace
    (n : ℕ) :
    stagedCascadeFromTrace S frontier R σ F i n ⊆ cascadeFromTrace S frontier R σ n := by
  exact Set.inter_subset_left

theorem stagedCascadeFromTrace_subset_region
    (n : ℕ) :
    stagedCascadeFromTrace S frontier R σ F i n ⊆ F.region i := by
  exact Set.inter_subset_right

theorem stagedClosureFromTrace_mono
    {i j : Idx}
    (hij : i ≤ j) :
    stagedClosureFromTrace S frontier R σ F i ⊆
      stagedClosureFromTrace S frontier R σ F j := by
  exact Set.inter_subset_inter_right _ (StagedView.region_mono F hij)

theorem stagedCascadeFromTrace_mono
    {i j : Idx}
    (hij : i ≤ j)
    (n : ℕ) :
    stagedCascadeFromTrace S frontier R σ F i n ⊆
      stagedCascadeFromTrace S frontier R σ F j n := by
  exact Set.inter_subset_inter_right _ (StagedView.region_mono F hij)

theorem closureFromTrace_eq_stagedClosureFromTrace_of_subset_region
    (hClosure : closureFromTrace S frontier R σ ⊆ F.region i) :
    closureFromTrace S frontier R σ =
      stagedClosureFromTrace S frontier R σ F i := by
  exact (Set.inter_eq_left.mpr hClosure).symm

theorem cascadeFromTrace_eq_stagedCascadeFromTrace_of_subset_region
    (n : ℕ)
    (hCascade : cascadeFromTrace S frontier R σ n ⊆ F.region i) :
    cascadeFromTrace S frontier R σ n =
      stagedCascadeFromTrace S frontier R σ F i n := by
  exact (Set.inter_eq_left.mpr hCascade).symm

theorem mem_stagedClosureFromTrace_iff_mem_stagedCascade_card_of_finite
    [Fintype Query]
    (q : Query) :
    q ∈ stagedClosureFromTrace S frontier R σ F i ↔
      q ∈ stagedCascadeFromTrace S frontier R σ F i (Fintype.card Query) := by
  exact and_congr (mem_closureFromTrace_iff_mem_cascade_card_of_finite S frontier R σ q) Iff.rfl

/-- Stage-indexed closure family for one fixed trace. -/
def stagedClosureApproximationFromTrace
    (F : StagedView (World := Query) Idx) :
    ClosureApproximation (World := Query) Idx PUnit where
  approx i _ := stagedClosureFromTrace S frontier R σ F i
  mono := by
    intro i j _ hij
    exact stagedClosureFromTrace_mono S frontier R σ F hij

end Staged

end TraceClosure

end Mettapedia.Hyperseed
