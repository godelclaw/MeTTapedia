import Mathlib.Data.Set.Lattice

/-!
# Perspectives, visibility regions, and staged observations

A perspective supplies signals, reachability, and an effort preorder. Its
available region intersects observability, a cost sublevel set, and a supplied
query region. Stateful perspectives freeze to this same interface; staged
views retain only monotonicity. No finiteness or execution semantics is assumed.
-/

namespace Mettapedia.Hyperseed

universe u v w

/-- A Hyperseed-style perspective/regime.

This is not a finitary "observer object". Instead it is a potentially infinite mode
of access to worlds:

- `signalClass` says which signals are taken seriously,
- `reaches` says which worlds are reachable/observable through which signals,
- `effort` measures the representational/comprehension cost of a world.
-/
structure Perspective (World : Type u) (Signal : Type v) (Cost : Type w)
    [Preorder Cost] where
  signalClass : Set Signal
  reaches : Signal → World → Prop
  effort : World → Cost

/-- Stateful/regime-indexed perspective.

This internalizes observer-relativity into the semantics: signal classes,
reachability, and effort may all vary with the current state/regime.
-/
structure StatefulPerspective (State : Type*) (World : Type u) (Signal : Type v) (Cost : Type w)
    [Preorder Cost] where
  signalClass : State → Set Signal
  reaches : State → Signal → World → Prop
  effort : State → World → Cost

variable {World : Type u} {Signal : Type v} {Cost : Type w} [Preorder Cost]
variable {State : Type*}

/-- Freeze a stateful perspective at one state/regime to recover the plain
perspective interface. -/
def freezePerspective
    (P : StatefulPerspective State World Signal Cost)
    (W : State) : Perspective World Signal Cost where
  signalClass := P.signalClass W
  reaches := P.reaches W
  effort := P.effort W

/-- Generic bounded region as a sublevel set in an ordered cost/access space. -/
def sublevelRegion (c : World → Cost) (B : Cost) : Set World :=
  { x | c x ≤ B }

/-- Larger bounds weakly enlarge any sublevel-set region. -/
theorem sublevelRegion_mono
    (c : World → Cost) {B₁ B₂ : Cost} (hB : B₁ ≤ B₂) :
    sublevelRegion c B₁ ⊆ sublevelRegion c B₂ :=
  fun _ hx => hx.trans hB

variable (P : Perspective World Signal Cost) (B : Cost) (guard : Set World)

/-- The observable universe induced by one perspective. -/
def observableUniverse : Set World :=
  { x | ∃ s ∈ P.signalClass, P.reaches s x }

/-- Budget-bounded comprehensibility region for one perspective. -/
def nearEurycosm : Set World :=
  sublevelRegion P.effort B

/-- Hyperseed-style available region: observable, affordable, and admitted by an
additional guard/credibility region. -/
def availableRegion : Set World :=
  observableUniverse P ∩ (nearEurycosm P B ∩ guard)

/-- Observable universe at one state/regime. -/
def observableUniverseAt
    (P : StatefulPerspective State World Signal Cost)
    (W : State) : Set World :=
  observableUniverse (freezePerspective P W)

/-- Near eurycosm at one state/regime. -/
def nearEurycosmAt
    (P : StatefulPerspective State World Signal Cost)
    (W : State) (B : Cost) : Set World :=
  nearEurycosm (freezePerspective P W) B

/-- Available region at one state/regime. -/
def availableRegionAt
    (P : StatefulPerspective State World Signal Cost)
    (W : State) (B : Cost) (guard : Set World) : Set World :=
  availableRegion (freezePerspective P W) B guard

/-- Membership in the available region is exactly the conjunction of the three
constituent filters. -/
theorem mem_availableRegion_iff (x : World) :
    x ∈ availableRegion P B guard ↔
      x ∈ observableUniverse P ∧ x ∈ nearEurycosm P B ∧ x ∈ guard := by
  rfl

theorem mem_availableRegionAt_iff
    (P : StatefulPerspective State World Signal Cost)
    (W : State) (B : Cost) (guard : Set World) (x : World) :
    x ∈ availableRegionAt P W B guard ↔
      x ∈ observableUniverseAt P W ∧ x ∈ nearEurycosmAt P W B ∧ x ∈ guard := by
  rfl

/-- Worlds observable from a smaller signal class remain observable from a larger
signal class. -/
theorem observableUniverse_mono_of_signalClass_subset
    {P P' : Perspective World Signal Cost}
    (hSig : P.signalClass ⊆ P'.signalClass)
    (hReach : ∀ s x, P.reaches s x → P'.reaches s x) :
    observableUniverse P ⊆ observableUniverse P' := by
  intro x hx
  rcases hx with ⟨s, hs, hreach⟩
  exact ⟨s, hSig hs, hReach s x hreach⟩

theorem observableUniverseAt_mono_of_signalClass_subset
    {P P' : StatefulPerspective State World Signal Cost}
    (W : State)
    (hSig : P.signalClass W ⊆ P'.signalClass W)
    (hReach : ∀ s x, P.reaches W s x → P'.reaches W s x) :
    observableUniverseAt P W ⊆ observableUniverseAt P' W :=
  observableUniverse_mono_of_signalClass_subset hSig hReach

/-- Larger budgets weakly enlarge the near eurycosm. -/
theorem nearEurycosm_mono {B₁ B₂ : Cost} (hB : B₁ ≤ B₂) :
    nearEurycosm P B₁ ⊆ nearEurycosm P B₂ :=
  sublevelRegion_mono P.effort hB

theorem nearEurycosmAt_mono
    (P : StatefulPerspective State World Signal Cost)
    (W : State) {B₁ B₂ : Cost} (hB : B₁ ≤ B₂) :
    nearEurycosmAt P W B₁ ⊆ nearEurycosmAt P W B₂ :=
  nearEurycosm_mono (freezePerspective P W) hB

/-- Reachability along one admitted signal places a world in the observable
universe. -/
theorem mem_observableUniverse_of_mem_signalClass {s : Signal} {x : World}
    (hs : s ∈ P.signalClass) (hreach : P.reaches s x) :
    x ∈ observableUniverse P :=
  ⟨s, hs, hreach⟩

/-- If every observable world is within effort budget `B`, then the observable
universe is contained in the near eurycosm at `B`. -/
theorem observableUniverse_subset_nearEurycosm
    (hB : ∀ x, x ∈ observableUniverse P → P.effort x ≤ B) :
    observableUniverse P ⊆ nearEurycosm P B := by
  intro x hx
  exact hB x hx

/-- The available region always sits inside the observable universe. -/
theorem availableRegion_subset_observableUniverse :
    availableRegion P B guard ⊆ observableUniverse P :=
  Set.inter_subset_left

theorem availableRegionAt_subset_observableUniverseAt
    (P : StatefulPerspective State World Signal Cost)
    (W : State) (B : Cost) (guard : Set World) :
    availableRegionAt P W B guard ⊆ observableUniverseAt P W :=
  availableRegion_subset_observableUniverse (freezePerspective P W) B guard

/-- The available region always sits inside the near eurycosm. -/
theorem availableRegion_subset_nearEurycosm :
    availableRegion P B guard ⊆ nearEurycosm P B :=
  Set.Subset.trans Set.inter_subset_right Set.inter_subset_left

theorem availableRegionAt_subset_nearEurycosmAt
    (P : StatefulPerspective State World Signal Cost)
    (W : State) (B : Cost) (guard : Set World) :
    availableRegionAt P W B guard ⊆ nearEurycosmAt P W B :=
  availableRegion_subset_nearEurycosm (freezePerspective P W) B guard

/-- The available region always sits inside the guard region. -/
theorem availableRegion_subset_guard :
    availableRegion P B guard ⊆ guard :=
  Set.Subset.trans Set.inter_subset_right Set.inter_subset_right

theorem availableRegionAt_subset_guard
    (P : StatefulPerspective State World Signal Cost)
    (W : State) (B : Cost) (guard : Set World) :
    availableRegionAt P W B guard ⊆ guard :=
  availableRegion_subset_guard (freezePerspective P W) B guard

/-- Enlarging the budget weakly enlarges the available region. -/
theorem availableRegion_mono_budget {B₁ B₂ : Cost} (hB : B₁ ≤ B₂) :
    availableRegion P B₁ guard ⊆ availableRegion P B₂ guard := by
  intro x hx
  exact ⟨hx.1, nearEurycosm_mono P hB hx.2.1, hx.2.2⟩

theorem availableRegionAt_mono_budget
    (P : StatefulPerspective State World Signal Cost)
    (W : State) {B₁ B₂ : Cost}
    (guard : Set World) (hB : B₁ ≤ B₂) :
    availableRegionAt P W B₁ guard ⊆ availableRegionAt P W B₂ guard :=
  availableRegion_mono_budget (freezePerspective P W) guard hB

/-- Enlarging the guard region weakly enlarges the available region. -/
theorem availableRegion_mono_guard
    {guard guard' : Set World} (hguard : guard ⊆ guard') :
    availableRegion P B guard ⊆ availableRegion P B guard' := by
  intro x hx
  exact ⟨hx.1, hx.2.1, hguard hx.2.2⟩

theorem availableRegionAt_mono_guard
    (P : StatefulPerspective State World Signal Cost)
    (W : State) (B : Cost)
    {guard guard' : Set World} (hguard : guard ⊆ guard') :
    availableRegionAt P W B guard ⊆ availableRegionAt P W B guard' :=
  availableRegion_mono_guard (freezePerspective P W) B hguard

/-- A stage-indexed filtration of an infinite world space. The stages themselves
may be finite, infinite, or transfinite; only monotonicity matters here. -/
structure StagedView (Idx : Type*) [Preorder Idx] where
  region : Idx → Set World
  mono : ∀ {i j : Idx}, i ≤ j → region i ⊆ region j

/-- Convenience monotonicity lemma for one staged view. -/
theorem StagedView.region_mono
    {Idx : Type*} [Preorder Idx] (F : StagedView (World := World) Idx)
    {i j : Idx} (hij : i ≤ j) :
    F.region i ⊆ F.region j :=
  F.mono hij

/-- A bounded closure family indexed by an order. This is the minimal interface
for finite, infinitary, or transfinite closure approximants. -/
structure ClosureApproximation (Idx : Type*) [Preorder Idx] (Seed : Type*) where
  approx : Idx → Seed → Set World
  mono : ∀ {i j : Idx} (seed : Seed), i ≤ j → approx i seed ⊆ approx j seed

/-- Convenience monotonicity lemma for one closure approximation family. -/
theorem ClosureApproximation.approx_mono
    {Idx : Type*} [Preorder Idx] {Seed : Type*}
    (A : ClosureApproximation (World := World) Idx Seed)
    (seed : Seed) {i j : Idx} (hij : i ≤ j) :
    A.approx i seed ⊆ A.approx j seed :=
  A.mono seed hij

/-- A thin structural skeleton for observer-relative multiverse dynamics.

`candidateWorlds` can be infinite, and `step` is set-valued on purpose: this gives a
proof-friendly nondeterministic shell before choosing measurable or weighted kernels.
-/
structure Multiverse (Event : Type*) where
  candidateWorlds : Set World
  step : World → Event → Set World

/-- Controlled version of the multiverse shell. -/
structure GuidableMultiverse (Event : Type*) (Action : Type*) extends Multiverse (World := World) Event where
  guidedStep : World → Action → Set World

variable {Event Action : Type*}

/-- Any world in the step image of a candidate world remains part of the
one-step reachable shell. -/
def oneStepReachable (M : Multiverse (World := World) Event) : Set World :=
  { x | ∃ w e, w ∈ M.candidateWorlds ∧ x ∈ M.step w e }

theorem mem_oneStepReachable
    (M : Multiverse (World := World) Event) {w x : World} {e : Event}
    (hw : w ∈ M.candidateWorlds) (hx : x ∈ M.step w e) :
    x ∈ oneStepReachable M :=
  ⟨w, e, hw, hx⟩

end Mettapedia.Hyperseed
