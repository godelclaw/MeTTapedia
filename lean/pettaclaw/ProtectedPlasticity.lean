import IterArchitecture

/-!
# ProtectedPlasticity — the minimal Iter–PettaClaw fusion

The theory has exactly three coordinates:

* `K`, the constitution: fixed by every ordinary transition;
* `D`, development: freely rewritten by Iter transformations;
* `L`, life: changed only by PettaClaw wakes and healthy restart.

No catalog, capability lattice, validator, or scheduler is modeled.  Their
implementation may matter, but none is needed for the mathematical
distinction.  Safety here means coordinate separation: arbitrary development
cannot alter constitution or life.  The trusted implementation boundary is
whatever mechanism makes the `K` coordinate unavailable to developmental
code; this file does not pretend that an ordinary same-user subprocess already
provides that boundary.

The two projection theorems are the fusion result.  Erasing life steps from a
mixed trace gives exactly Iter's ordered transformation fold.  Erasing
development steps gives exactly the PettaClaw life trace.  Thus the product is
conservative over both components rather than an opaque embedding of either.
-/

namespace ProtectedPlasticity

open IterArchitecture

/-! ## The three-coordinate theory -/

/-- Constitution, freely transformable development, and lawfully evolving
life.  The types are completely abstract.  In an implementation, `D` may
contain tools, channels, transformations, and memory; no internal organization
of that periphery is needed by the theorem. -/
structure Coordinates (K D L : Type) where
  kernel : K
  development : D
  life : L

/-- An arbitrary endogenous revision has access only to development. -/
def revise {K D L : Type} (state : Coordinates K D L) (change : D → D) :
    Coordinates K D L :=
  { state with development := change state.development }

/-- A lawful life transition has access only to life. -/
def evolve {K D L : Type} (state : Coordinates K D L) (change : L → L) :
    Coordinates K D L :=
  { state with life := change state.life }

/-- The desired "almost full self-modification" property, abstractly and
exactly: any developmental configuration is reachable, but constitution and
life are preserved. -/
theorem arbitrary_development_is_protected {K D L : Type}
    (state : Coordinates K D L) (target : D) :
    let next := revise state (fun _ => target)
    next.kernel = state.kernel ∧ next.life = state.life ∧
      next.development = target := by
  simp [revise]

/-- A finite developmental history. -/
def reviseRun {K D L : Type} :
    List (D → D) → Coordinates K D L → Coordinates K D L
  | [], state => state
  | change :: rest, state => reviseRun rest (revise state change)

/-- Kernel and life survive an arbitrary-length developmental history, not
merely one revision. -/
theorem developmental_trace_preserves_protected_coordinates {K D L : Type}
    (changes : List (D → D)) (state : Coordinates K D L) :
    (reviseRun changes state).kernel = state.kernel ∧
      (reviseRun changes state).life = state.life := by
  induction changes generalizing state with
  | nil => exact ⟨rfl, rfl⟩
  | cons change rest ih =>
      constructor
      · calc
          (reviseRun (change :: rest) state).kernel =
              (reviseRun rest (revise state change)).kernel := rfl
          _ = (revise state change).kernel := (ih (revise state change)).1
          _ = state.kernel := rfl
      · calc
          (reviseRun (change :: rest) state).life =
              (reviseRun rest (revise state change)).life := rfl
          _ = (revise state change).life := (ih (revise state change)).2
          _ = state.life := rfl

/-- Development and life commute without any assumptions on either update.
The result follows only from coordinate separation. -/
theorem revision_evolution_commute {K D L : Type}
    (state : Coordinates K D L) (developmental : D → D) (living : L → L) :
    evolve (revise state developmental) living =
      revise (evolve state living) developmental := by
  rfl

/-- If self-modification instead ranges over the whole state, kernel
preservation is impossible in general.  This tiny counterexample is why the
`K`/`D` boundary—not a capability catalog—is mathematically necessary. -/
theorem unrestricted_whole_state_rewrite_can_change_kernel :
    let state : Coordinates Nat Unit Unit := ⟨0, (), ()⟩
    let rewrite : Coordinates Nat Unit Unit → Coordinates Nat Unit Unit :=
      fun current => { current with kernel := 1 }
    (rewrite state).kernel ≠ state.kernel := by
  decide

/-- The PettaClaw part that persists as the agent's living identity: its
renewal rhythm and its present moment. -/
structure Living where
  rhythm : Claws.Life
  working : PresentMoment.Working
deriving Repr, DecidableEq

/-- The minimal fusion.  `K` is intentionally abstract: the theorem does not
depend on what the protected constitution contains. -/
structure Fusion (K : Type) where
  kernel : K
  development : Boundary
  living : Living

/-- Ordinary fused actions.  There is deliberately no constructor for
rewriting `kernel`.

`transform` is Iter's developmental action.  `wake` and `restart` are the two
PettaClaw life actions used in the existing models. -/
inductive Action
  | transform (transformation : Transformation)
  | wake (event : Claws.Ev)
  | restart

/-- One fused transition. -/
def step {K : Type} (heartbeat : Nat) (state : Fusion K) : Action → Fusion K
  | .transform transformation =>
      { state with
        development := applyTransformation state.development transformation }
  | .wake event =>
      { state with
        living :=
          { state.living with
            rhythm := (Claws.wakeMax heartbeat state.living.rhythm event).1 } }
  | .restart =>
      { state with
        living :=
          { state.living with
            working := PresentMoment.resetH state.living.working } }

/-- Execute a finite mixed trace. -/
def run {K : Type} (heartbeat : Nat) : List Action → Fusion K → Fusion K
  | [], state => state
  | action :: rest, state => run heartbeat rest (step heartbeat state action)

/-! ## Protected arbitrary development -/

theorem step_preserves_kernel {K : Type} (heartbeat : Nat)
    (state : Fusion K) (action : Action) :
    (step heartbeat state action).kernel = state.kernel := by
  cases action <;> rfl

/-- No finite mixture of self-transformation, life, and healthy restart can
rewrite the protected constitution. -/
theorem run_preserves_kernel {K : Type} (heartbeat : Nat)
    (actions : List Action) (state : Fusion K) :
    (run heartbeat actions state).kernel = state.kernel := by
  induction actions generalizing state with
  | nil => rfl
  | cons action rest ih =>
      calc
        (run heartbeat (action :: rest) state).kernel =
            (run heartbeat rest (step heartbeat state action)).kernel := rfl
        _ = (step heartbeat state action).kernel :=
          ih (step heartbeat state action)
        _ = state.kernel := step_preserves_kernel heartbeat state action

/-- A constant transformation witnesses full freedom over the developmental
coordinate. -/
def developTo (target : Boundary) : Action :=
  .transform (fun _ => some target)

/-- The concrete Iter-boundary instance of protected development. -/
theorem arbitrary_iter_boundary_development_is_protected {K : Type}
    (heartbeat : Nat)
    (state : Fusion K) (target : Boundary) :
    let next := step heartbeat state (developTo target)
    next.kernel = state.kernel ∧
      next.living = state.living ∧
      next.development = target := by
  simp [step, developTo, applyTransformation]

/-! ## The Iter projection -/

/-- Erase life actions, retaining Iter transformations in their trace order. -/
def developmentActions : List Action → List Transformation
  | [] => []
  | .transform transformation :: rest =>
      transformation :: developmentActions rest
  | .wake _ :: rest => developmentActions rest
  | .restart :: rest => developmentActions rest

/-- A mixed fused trace projects exactly to Iter's ordered transformation
fold.  PettaClaw life steps stutter at this projection. -/
theorem development_projection {K : Type} (heartbeat : Nat)
    (actions : List Action) (state : Fusion K) :
    (run heartbeat actions state).development =
      applyTransformations (developmentActions actions) state.development := by
  induction actions generalizing state with
  | nil => rfl
  | cons action rest ih =>
      cases action with
      | transform transformation =>
          simpa [run, step, developmentActions, applyTransformations] using
            ih (step heartbeat state (.transform transformation))
      | wake event =>
          simpa [run, step, developmentActions] using
            ih (step heartbeat state (.wake event))
      | restart =>
          simpa [run, step, developmentActions] using
            ih (step heartbeat state .restart)

/-! ## The PettaClaw projection -/

inductive LifeAction
  | wake (event : Claws.Ev)
  | restart

def lifeStep (heartbeat : Nat) (living : Living) : LifeAction → Living
  | .wake event =>
      { living with rhythm := (Claws.wakeMax heartbeat living.rhythm event).1 }
  | .restart =>
      { living with working := PresentMoment.resetH living.working }

def lifeRun (heartbeat : Nat) : List LifeAction → Living → Living
  | [], living => living
  | action :: rest, living =>
      lifeRun heartbeat rest (lifeStep heartbeat living action)

/-- Erase Iter transformations, retaining PettaClaw life actions in order. -/
def lifeActions : List Action → List LifeAction
  | [] => []
  | .transform _ :: rest => lifeActions rest
  | .wake event :: rest => .wake event :: lifeActions rest
  | .restart :: rest => .restart :: lifeActions rest

/-- A mixed fused trace projects exactly to the PettaClaw life trace.  Every
self-transformation is a stuttering step at the living-identity projection. -/
theorem life_projection {K : Type} (heartbeat : Nat)
    (actions : List Action) (state : Fusion K) :
    (run heartbeat actions state).living =
      lifeRun heartbeat (lifeActions actions) state.living := by
  induction actions generalizing state with
  | nil => rfl
  | cons action rest ih =>
      cases action with
      | transform transformation =>
          simpa [run, step, lifeActions] using
            ih (step heartbeat state (.transform transformation))
      | wake event =>
          simpa [run, step, lifeActions, lifeRun, lifeStep] using
            ih (step heartbeat state (.wake event))
      | restart =>
          simpa [run, step, lifeActions, lifeRun, lifeStep] using
            ih (step heartbeat state .restart)

/-! ## Independence and continuity -/

/-- Development and life evolution commute because they occupy different
coordinates.  This is the algebraic core of the fusion. -/
theorem transformation_wake_commute {K : Type} (heartbeat : Nat)
    (state : Fusion K) (transformation : Transformation) (event : Claws.Ev) :
    step heartbeat (step heartbeat state (.transform transformation)) (.wake event) =
      step heartbeat (step heartbeat state (.wake event)) (.transform transformation) := by
  rfl

theorem transformation_restart_commute {K : Type} (heartbeat : Nat)
    (state : Fusion K) (transformation : Transformation) :
    step heartbeat (step heartbeat state (.transform transformation)) .restart =
      step heartbeat (step heartbeat state .restart) (.transform transformation) := by
  rfl

/-- Inside the declared persistable window, healthy restart is a stuttering
step on the entire fused state. -/
theorem healthy_restart_is_stutter {K : Type} (heartbeat : Nat)
    (state : Fusion K)
    (within : state.living.working.lastResults.length ≤ PresentMoment.cap) :
    step heartbeat state .restart = state := by
  have continuity := PresentMoment.continuity state.living.working within
  cases state with
  | mk kernel development living =>
      cases living with
      | mk rhythm working =>
          simp only [step]
          simp only at continuity within
          rw [continuity]

/-! ## The sharp distinction witnessed by the concrete architectures -/

/-- Seed Iter erases event origin, while PettaClaw's life transition observes
the difference between a human arm and autonomous/sibling work. -/
theorem origin_is_transformationally_erased_but_livingly_observed
    (pace : Pace) :
    beginCycle pace (some .human) = beginCycle pace (some .sibling) ∧
      (Claws.wakeMax 60 ⟨5, 0⟩ (.human 10)).1 ≠
        (Claws.wake 60 ⟨5, 0⟩ .work).1 := by
  exact ⟨event_origins_indistinguishable pace .human .sibling,
    pettaclaw_is_origin_sensitive⟩

/-- Seed Iter's `nop` returns to autonomous task selection, whereas PettaClaw
rest establishes zero energy.  Plastic continuation and sovereign rest are
therefore distinct properties. -/
theorem continuation_is_not_sovereign_rest (pace : Pace) :
    (finishCycle pace false true).2 = .slow ∧
      (beginCycle (finishCycle pace false true).1 none).2 = .selectTask ∧
      (Claws.wake 60 ⟨5, 0⟩ .rest).1.energy = 0 := by
  exact ⟨(nop_is_not_stable_rest pace).1,
    (nop_is_not_stable_rest pace).2,
    pettaclaw_rest_zeroes_current_burst⟩

end ProtectedPlasticity

/-! ## Axiom audit -/
#print axioms ProtectedPlasticity.step_preserves_kernel
#print axioms ProtectedPlasticity.run_preserves_kernel
#print axioms ProtectedPlasticity.arbitrary_development_is_protected
#print axioms ProtectedPlasticity.developmental_trace_preserves_protected_coordinates
#print axioms ProtectedPlasticity.revision_evolution_commute
#print axioms ProtectedPlasticity.unrestricted_whole_state_rewrite_can_change_kernel
#print axioms ProtectedPlasticity.arbitrary_iter_boundary_development_is_protected
#print axioms ProtectedPlasticity.development_projection
#print axioms ProtectedPlasticity.life_projection
#print axioms ProtectedPlasticity.transformation_wake_commute
#print axioms ProtectedPlasticity.healthy_restart_is_stutter
#print axioms ProtectedPlasticity.origin_is_transformationally_erased_but_livingly_observed
#print axioms ProtectedPlasticity.continuation_is_not_sovereign_rest
