import Mettapedia.Coalgebra.StreamFinality

/-!
# Coherent prefix towers and resumable trajectories

Compatible finite prefixes determine exactly one stream. The tower uses the
general inverse-system carrier. A resumable trajectory additionally supplies
a runner and an exact continuation law: coherence alone is not execution.
-/

set_option autoImplicit false

namespace Mettapedia.Coalgebra.CoherentPrefixTower

open Mettapedia.Coalgebra.StreamFinality

universe uLabel

/-- The general coherent tower specialized to finite stream prefixes. -/
abbrev Tower (Label : Type uLabel) :=
  (CoherentFiniteViewSystem.streamPrefixSystem Label).Tower

namespace Tower

variable {Label : Type uLabel}

-- Preserve the original constructor and projection names for callers.
@[match_pattern] abbrev mk :=
  @CoherentFiniteViewSystem.FiniteViewSystem.Tower.mk
    (CoherentFiniteViewSystem.streamPrefixSystem Label)

abbrev view (tower : Tower Label) :=
  CoherentFiniteViewSystem.FiniteViewSystem.Tower.view tower

abbrev coherent (tower : Tower Label) {earlier later : Nat} (bounded : earlier ≤ later) :=
  CoherentFiniteViewSystem.FiniteViewSystem.Tower.coherent tower bounded

@[ext]
theorem ext {first second : Tower Label}
    (views : first.view = second.view) : first = second :=
  CoherentFiniteViewSystem.FiniteViewSystem.Tower.ext _ views

/-- Every stream determines its compatible tower of finite views. -/
def ofStream (stream : Stream Label) : Tower Label where
  view := allPrefixes stream
  coherent := by
    intro earlier later bounded
    exact restrictPrefix_finiteView bounded stream

/-- Read position `index` from any prefix long enough to contain it.  The
successor depth is the canonical such choice. -/
def toStream (tower : Tower Label) : Stream Label :=
  fun index => tower.view (index + 1) ⟨index, Nat.lt_succ_self index⟩

@[simp]
theorem toStream_ofStream (stream : Stream Label) :
    toStream (ofStream stream) = stream := rfl

@[simp]
theorem ofStream_toStream (tower : Tower Label) :
    ofStream (toStream tower) = tower := by
  apply Tower.ext
  funext depth index
  have bounded : index.val + 1 ≤ depth :=
    Nat.succ_le_iff.mpr index.isLt
  have restriction := congrFun (tower.coherent bounded)
    ⟨index.val, Nat.lt_succ_self index.val⟩
  exact restriction.symm

/-- Streams and coherent towers carry exactly the same information. -/
def streamEquiv (Label : Type uLabel) :
    Stream Label ≃ Tower Label where
  toFun := ofStream
  invFun := toStream
  left_inv := toStream_ofStream
  right_inv := ofStream_toStream

theorem ofStream_injective :
    Function.Injective (@ofStream Label) :=
  (streamEquiv Label).injective

theorem ofStream_surjective :
    Function.Surjective (@ofStream Label) :=
  (streamEquiv Label).surjective

theorem toStream_injective :
    Function.Injective (@toStream Label) :=
  (streamEquiv Label).symm.injective

theorem toStream_surjective :
    Function.Surjective (@toStream Label) :=
  (streamEquiv Label).symm.surjective

/-! ## Raw towers contain incoherent families -/

/-- A raw Boolean tower whose depth-one observation is false and whose
depth-two observation at the same position is true. -/
def incoherentBooleanViews : (depth : Nat) → Prefix Bool depth :=
  fun depth _index => if depth = 1 then false else true

theorem incoherentBooleanViews_violate_restriction :
    restrictPrefix (show 1 ≤ 2 by decide) (incoherentBooleanViews 2) ≠
      incoherentBooleanViews 1 := by
  intro equality
  have atZero := congrFun equality ⟨0, by decide⟩
  simp [restrictPrefix, incoherentBooleanViews] at atZero

/-- Consequently no coherent tower has the deliberately incompatible raw
family above. -/
theorem no_tower_has_incoherentBooleanViews :
    ¬ ∃ tower : Tower Bool, tower.view = incoherentBooleanViews := by
  rintro ⟨tower, views⟩
  apply incoherentBooleanViews_violate_restriction
  rw [← views]
  exact tower.coherent (show 1 ≤ 2 by decide)

end Tower

/-! ## Resumable trajectories of an explicit finite runner -/

/-- The complete retained state at every budget, with exact continuation from
each observation boundary. -/
structure ResumableTrajectory {State : Type uLabel}
    (run : Nat → State → State) (start : State) where
  observation : Stream State
  at_zero : observation 0 = start
  resume : ∀ first extra,
    observation (first + extra) = run extra (observation first)

namespace ResumableTrajectory

variable {State : Type uLabel} {run : Nat → State → State} {start : State}

@[ext]
theorem ext {first second : ResumableTrajectory run start}
    (observations : first.observation = second.observation) :
    first = second := by
  cases first
  cases second
  cases observations
  rfl

/-- Actual executions define a trajectory when the runner's zero and budget
composition laws have been proved. -/
abbrev canonical (run : Nat → State → State) (start : State)
    (zero : ∀ state, run 0 state = state)
    (add : ∀ first extra state,
      run (first + extra) state = run extra (run first state)) :
    ResumableTrajectory run start where
  observation fuel := run fuel start
  at_zero := zero start
  resume first extra := add first extra start

@[simp]
theorem canonical_observation (run : Nat → State → State) (start : State)
    (zero : ∀ state, run 0 state = state)
    (add : ∀ first extra state,
      run (first + extra) state = run extra (run first state)) (fuel : Nat) :
    (canonical run start zero add).observation fuel = run fuel start :=
  rfl

/-- Exact continuation determines every observation, without requiring
termination or a bound on the number of answers produced per tick. -/
theorem observation_eq_run (trajectory : ResumableTrajectory run start)
    (fuel : Nat) : trajectory.observation fuel = run fuel start := by
  simpa only [Nat.zero_add, trajectory.at_zero] using trajectory.resume 0 fuel

theorem unique (first second : ResumableTrajectory run start) :
    first = second := by
  apply ext
  funext fuel
  rw [first.observation_eq_run, second.observation_eq_run]

theorem eq_canonical (trajectory : ResumableTrajectory run start)
    (zero : ∀ state, run 0 state = state)
    (add : ∀ first extra state,
      run (first + extra) state = run extra (run first state)) :
    trajectory = canonical run start zero add :=
  unique _ _

/-- Continuing from a saved observation retains the original trajectory's
future, rather than re-running its prefix. -/
def resumeFrom (trajectory : ResumableTrajectory run start) (first : Nat) :
    ResumableTrajectory run (trajectory.observation first) where
  observation extra := trajectory.observation (first + extra)
  at_zero := congrArg trajectory.observation (Nat.add_zero first)
  resume before extra := by
    simpa only [Nat.add_assoc] using trajectory.resume (first + before) extra

@[simp]
theorem resumeFrom_observation (trajectory : ResumableTrajectory run start)
    (first extra : Nat) :
    (trajectory.resumeFrom first).observation extra =
      trajectory.observation (first + extra) :=
  rfl

/-- A relation proved for every finite continuation transports to every pair
of trajectory observations separated by that continuation. -/
theorem relation_after_resume (trajectory : ResumableTrajectory run start)
    (relation : State → State → Prop)
    (preserved : ∀ fuel state, relation state (run fuel state))
    (first extra : Nat) :
    relation (trajectory.observation first)
      (trajectory.observation (first + extra)) := by
  rw [trajectory.resume]
  exact preserved extra (trajectory.observation first)

/-- Publication and receipt-prefix laws remain laws of the concrete runner;
the same continuation interface carries each chosen observer. -/
theorem observer_prefix_after_resume {Event : Type*}
    (trajectory : ResumableTrajectory run start) (observe : State → List Event)
    (grows : ∀ fuel state, (observe state).IsPrefix (observe (run fuel state)))
    (first extra : Nat) :
    (observe (trajectory.observation first)).IsPrefix
      (observe (trajectory.observation (first + extra))) :=
  trajectory.relation_after_resume
    (fun earlier later => (observe earlier).IsPrefix (observe later))
    grows first extra

/-- Settlement is supplied by the runner, not inferred from an empty output
list.  In particular, unresolved obligations need not count as settled. -/
theorem observation_constant_after_settlement
    (trajectory : ResumableTrajectory run start) (settled : State → Prop)
    (stable : ∀ state, settled state → ∀ fuel, run fuel state = state)
    (first extra : Nat) (complete : settled (trajectory.observation first)) :
    trajectory.observation (first + extra) = trajectory.observation first := by
  rw [trajectory.resume]
  exact stable (trajectory.observation first) complete extra

/-- A concrete run invariant propagates from the retained initial state. -/
theorem invariant (trajectory : ResumableTrajectory run start)
    (property : State → Prop)
    (preserved : ∀ fuel state, property state → property (run fuel state))
    (initial : property start) (fuel : Nat) :
    property (trajectory.observation fuel) := by
  rw [trajectory.observation_eq_run]
  exact preserved fuel start initial

/-- The coherent tower retains all finite observations of the complete state. -/
def coherentTower (trajectory : ResumableTrajectory run start) : Tower State :=
  Tower.ofStream trajectory.observation

@[simp]
theorem toStream_coherentTower (trajectory : ResumableTrajectory run start) :
    Tower.toStream trajectory.coherentTower = trajectory.observation :=
  Tower.toStream_ofStream trajectory.observation

/-- Reconstructing the tower also reconstructs its exact continuation law. -/
theorem reconstructed_resume (trajectory : ResumableTrajectory run start)
    (first extra : Nat) :
    Tower.toStream trajectory.coherentTower (first + extra) =
      run extra (Tower.toStream trajectory.coherentTower first) := by
  simpa only [toStream_coherentTower] using trajectory.resume first extra

theorem coherentTower_injective :
    Function.Injective (@coherentTower State run start) :=
  fun _ _ towers => ext (Tower.ofStream_injective towers)

/-! ## Controls -/

namespace Canary

/-- A budget runner retaining its number of completed ticks. -/
def counterRun (fuel state : Nat) : Nat := state + fuel

def counterTrajectory (start : Nat) : ResumableTrajectory counterRun start :=
  canonical counterRun start (fun _ => Nat.add_zero _)
    (fun _ _ _ => (Nat.add_assoc _ _ _).symm)

theorem counter_resume_from_retained_state :
    ((counterTrajectory 7).resumeFrom 3).observation 2 = 12 :=
  rfl

/-- Stream-prefix coherence alone does not assert that a stream follows a
runner: a constant retained counter cannot continue an incrementing run. -/
theorem constant_counter_not_resumable (start : Nat) :
    ¬ ∃ trajectory : ResumableTrajectory counterRun start,
      trajectory.observation = fun _ => start := by
  rintro ⟨trajectory, observations⟩
  have resumed := trajectory.resume 0 1
  rw [congrFun observations 1, congrFun observations 0] at resumed
  exact Nat.ne_add_one start resumed

end Canary

end ResumableTrajectory

end Mettapedia.Coalgebra.CoherentPrefixTower
