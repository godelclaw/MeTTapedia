import Mettapedia.GSLT.Contracts.FrameUpdate
import Mettapedia.GSLT.Logic.SeparationProduct
import Mettapedia.GSLT.Core.LooseRelationEquipment

/-!
# Reified authority and frame-preserving actions

Authority is an element of a separation algebra; what it says about the
machine is its *reification*, a set of states.  An action is a relation on
states.  The **action judgement** of the Views framework (Dinsdale-Young,
Birkedal, Gardner, Parkinson and Yang, *Views: compositional reasoning for
concurrent programs*, POPL 2013, Definition 11 and Property G) asks that an
action taking authority `p` to `q` preserve every frame:

  for every `r` separate from `p`, the action maps the states of `p + r` into
  the states of `q + r`.

Here composition is total and separateness is explicit, so the judgement also
asks that `q` stay separate from every such `r` whenever the action can run.
An action that cannot run from any state of `p + r` satisfies the judgement
vacuously: the judgement is a safety property and says nothing about progress.

## What follows from the judgement alone

* The judgement contains the local one (`local_`), frames (`frame`), composes
  sequentially (`seq`), and holds for the idle action (`idle`).
* Its authority shadow is a frame-preserving update whenever the action can
  run beside every frame (`frameUpdate_of_enabled`).
* **Interleaving soundness** (`parallel`): two straight-line threads whose
  steps satisfy the judgement, started from separate authority, end in the
  combination of their final authority under every interleaving.  Each step of
  one thread treats the other thread's current authority as its frame.  This
  is the content of the parallel rule of the Views framework, and of the
  rely–guarantee coexistence condition: what one thread may do is bounded by
  what the other's authority tolerates.

## Controls

On two exclusively owned cells (`TwoCells`):

* writing an owned cell preserves every frame (`writeFirst_preserves`);
* writing the other cell satisfies the local judgement (`writeSecond_local`)
  but breaks the frame of whoever owns that cell
  (`writeSecond_not_preserves`).  A check of the thread's own view alone is not
  frame preservation.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Contracts

open Mettapedia.GSLT.SeparationAlgebra
open Mettapedia.GSLT.SeparationAlgebra.SepAlgebra
open scoped Mettapedia.GSLT.SeparationAlgebra

universe u v w

variable {α : Type u} [Zero α] [Add α] [SepAlgebra α] {S : Type v}

/-- **The action judgement**: from authority `p`, the action ends in authority
`q` and preserves every frame. -/
def ActionPreserves (reify : α → Set S) (act : S → S → Prop) (p q : α) : Prop :=
  ∀ r, p ## r → ∀ s ∈ reify (p + r), ∀ s', act s s' → q ## r ∧ s' ∈ reify (q + r)

/-- Run one action, then another. -/
def seqAct (first second : S → S → Prop) : S → S → Prop :=
  fun s s'' => ∃ s', first s s' ∧ second s' s''

namespace ActionPreserves

variable {reify : α → Set S} {act act' : S → S → Prop} {p q t : α}

/-- The judgement contains the local one, with the empty frame. -/
theorem local_ (judgement : ActionPreserves reify act p q) :
    ∀ s ∈ reify p, ∀ s', act s s' → s' ∈ reify q := by
  intro s holds s' step
  have holds' : s ∈ reify (p + 0) := by rwa [SepAlgebra.add_zero]
  have result := (judgement 0 (separate_zero p) s holds' s' step).2
  rwa [SepAlgebra.add_zero] at result

/-- The idle action preserves every frame. -/
theorem idle (reify : α → Set S) (p : α) : ActionPreserves reify (fun s s' => s = s') p p := by
  rintro r separate s holds s' rfl
  exact ⟨separate, holds⟩

/-- **Sequential composition.** -/
theorem seq (first : ActionPreserves reify act p q) (second : ActionPreserves reify act' q t) :
    ActionPreserves reify (seqAct act act') p t := by
  rintro r separate s holds s'' ⟨s', step, step'⟩
  obtain ⟨separateQ, middle⟩ := first r separate s holds s' step
  exact second r separateQ s' middle s'' step'

/-- **The frame rule.** -/
theorem frame (judgement : ActionPreserves reify act p q) {f : α} (separateF : p ## f) :
    ActionPreserves reify act (p + f) (q + f) := by
  intro r separate s holds s' step
  obtain ⟨separatePFr, separateFR⟩ := separate_add_right separateF separate
  have regroup : p + f + r = p + (f + r) := add_assoc_of_separate separateF separate
  rw [regroup] at holds
  obtain ⟨separateQ, result⟩ := judgement (f + r) separatePFr s holds s' step
  obtain ⟨separateQFR, separateQF⟩ := separate_add_left separateFR separateQ
  refine ⟨separateQFR, ?_⟩
  rwa [add_assoc_of_separate separateQF separateQFR]

/-- **The authority shadow**: an action that can run beside every frame of
`p` is a frame-preserving update from `p` to `q`. -/
theorem frameUpdate_of_enabled (judgement : ActionPreserves reify act p q)
    (enabled : ∀ r, p ## r → ∃ s ∈ reify (p + r), ∃ s', act s s') : FrameUpdate p q := by
  intro r separate
  obtain ⟨s, holds, s', step⟩ := enabled r separate
  exact (judgement r separate s holds s' step).1

/-! ## Changing the resource and state representation

The existing separation transport supplies the resource map and its back law.
The state relation and reification square are independent representation
obligations. Target steps reflect to source steps; frame lifting then proves
the target action judgement. This does not infer observation, progress or cost
preservation from the frame rule.
-/

open Mettapedia.GSLT.Logic.SeparationTransport
open Mettapedia.GSLT.LooseRelationEquipment

/-- A reification square through the existing proof-relevant state relation.
Every target state in a transported view has a related source state in that
view; related source states in the view reify in the target. This does not
require the two state representations to be isomorphic. -/
def ReifiesThrough {β : Type w} [Zero β] [Add β] [SepAlgebra β] {T : Type v}
    (resources : Hom α β) (relation : Loose S T)
    (sourceView : α → Set S) (targetView : β → Set T) : Prop :=
  ∀ authority target, target ∈ targetView (resources authority) ↔
    ∃ source, source ∈ sourceView authority ∧ Nonempty (relation source target)

/-- Target action steps reflect along a selected relation witness. The
post-state may have a different representation while retaining its witness. -/
def ReflectsThrough {T : Type v} (relation : Loose S T)
    (sourceAct : S → S → Prop) (targetAct : T → T → Prop) : Prop :=
  ∀ source target, relation source target → ∀ target', targetAct target target' →
    ∃ source', sourceAct source source' ∧ Nonempty (relation source' target')

/-- Reification squares compose with the actual middle state and both
relation witnesses retained by horizontal composition. -/
theorem ReifiesThrough.comp {β γ : Type w}
    [Zero β] [Add β] [SepAlgebra β] [Zero γ] [Add γ] [SepAlgebra γ]
    {T U : Type v} {first : Hom α β} {second : Hom β γ}
    {earlier : Loose S T} {later : Loose T U}
    {sourceView : α → Set S} {middleView : β → Set T} {targetView : γ → Set U}
    (firstSquare : ReifiesThrough first earlier sourceView middleView)
    (secondSquare : ReifiesThrough second later middleView targetView) :
    ReifiesThrough (Hom.comp second first)
      (LooseRelationEquipment.comp earlier later) sourceView targetView := by
  intro authority target
  constructor
  · intro member
    obtain ⟨middle, middleMember, ⟨laterWitness⟩⟩ :=
      (secondSquare (first authority) target).mp member
    obtain ⟨source, sourceMember, ⟨earlierWitness⟩⟩ :=
      (firstSquare authority middle).mp middleMember
    exact ⟨source, sourceMember, ⟨⟨middle, earlierWitness, laterWitness⟩⟩⟩
  · rintro ⟨source, sourceMember, ⟨⟨middle, earlierWitness, laterWitness⟩⟩⟩
    exact (secondSquare (first authority) target).mpr
      ⟨middle, (firstSquare authority middle).mpr
        ⟨source, sourceMember, ⟨earlierWitness⟩⟩, ⟨laterWitness⟩⟩

theorem ReflectsThrough.comp {T U : Type v}
    {earlier : Loose S T} {later : Loose T U}
    {sourceAct : S → S → Prop} {middleAct : T → T → Prop} {targetAct : U → U → Prop}
    (firstReflects : ReflectsThrough earlier sourceAct middleAct)
    (secondReflects : ReflectsThrough later middleAct targetAct) :
    ReflectsThrough (LooseRelationEquipment.comp earlier later) sourceAct targetAct := by
  rintro source target ⟨middle, earlierWitness, laterWitness⟩ target' step
  obtain ⟨middle', middleStep, ⟨laterWitness'⟩⟩ :=
    secondReflects middle target laterWitness target' step
  obtain ⟨source', sourceStep, ⟨earlierWitness'⟩⟩ :=
    firstReflects source middle earlierWitness middle' middleStep
  exact ⟨source', sourceStep, ⟨⟨middle', earlierWitness', laterWitness'⟩⟩⟩

theorem transport_relation {β : Type w} [Zero β] [Add β] [SepAlgebra β] {T : Type v}
    {sourceView : α → Set S} {targetView : β → Set T}
    {sourceAct : S → S → Prop} {targetAct : T → T → Prop} {p q : α}
    (resources : Hom α β) (lifts : resources.LiftsExtensions)
    (relation : Loose S T) (square : ReifiesThrough resources relation sourceView targetView)
    (reflects : ReflectsThrough relation sourceAct targetAct)
    (judgement : ActionPreserves sourceView sourceAct p q) :
    ActionPreserves targetView targetAct (resources p) (resources q) := by
  intro frame separate before member after step
  obtain ⟨sourceFrame, sourceSeparate, image⟩ := lifts p frame separate
  have beforeMapped : before ∈ targetView (resources (p + sourceFrame)) := by
    simpa only [resources.map_add sourceSeparate, image] using member
  obtain ⟨source, sourceMember, ⟨beforeWitness⟩⟩ :=
    (square (p + sourceFrame) before).mp beforeMapped
  obtain ⟨source', sourceStep, ⟨afterWitness⟩⟩ :=
    reflects source before beforeWitness after step
  obtain ⟨afterSeparate, afterSource⟩ :=
    judgement sourceFrame sourceSeparate source sourceMember source' sourceStep
  refine ⟨by simpa only [image] using resources.map_separate afterSeparate, ?_⟩
  have afterMapped := (square (q + sourceFrame) after).mpr
    ⟨source', afterSource, ⟨afterWitness⟩⟩
  simpa only [resources.map_add afterSeparate, image] using afterMapped

/-- The authority and machine-state components of an adapter compose through
the library's existing resource map and loose relation composition. -/
theorem transport_relation_comp {β γ : Type w}
    [Zero β] [Add β] [SepAlgebra β] [Zero γ] [Add γ] [SepAlgebra γ]
    {T U : Type v} {sourceView : α → Set S} {middleView : β → Set T}
    {targetView : γ → Set U} {sourceAct : S → S → Prop}
    {middleAct : T → T → Prop} {targetAct : U → U → Prop} {p q : α}
    (first : Hom α β) (second : Hom β γ)
    (firstLifts : first.LiftsExtensions) (secondLifts : second.LiftsExtensions)
    (earlier : Loose S T) (later : Loose T U)
    (firstSquare : ReifiesThrough first earlier sourceView middleView)
    (secondSquare : ReifiesThrough second later middleView targetView)
    (firstReflects : ReflectsThrough earlier sourceAct middleAct)
    (secondReflects : ReflectsThrough later middleAct targetAct)
    (judgement : ActionPreserves sourceView sourceAct p q) :
    ActionPreserves targetView targetAct (Hom.comp second first p) (Hom.comp second first q) :=
  transport_relation (Hom.comp second first)
    (Hom.comp_liftsExtensions second first secondLifts firstLifts)
    (LooseRelationEquipment.comp earlier later)
    (firstSquare.comp secondSquare) (firstReflects.comp secondReflects) judgement

theorem transport {β : Type w} [Zero β] [Add β] [SepAlgebra β] {T : Type v}
    {sourceView : α → Set S} {targetView : β → Set T}
    {sourceAct : S → S → Prop} {targetAct : T → T → Prop} {p q : α}
    (resources : Hom α β) (lifts : resources.LiftsExtensions)
    (states : S ≃ T)
    (square : ∀ authority state,
      states state ∈ targetView (resources authority) ↔ state ∈ sourceView authority)
    (reflects : ∀ before after, targetAct before after →
      sourceAct (states.symm before) (states.symm after))
    (judgement : ActionPreserves sourceView sourceAct p q) :
    ActionPreserves targetView targetAct (resources p) (resources q) := by
  apply transport_relation resources lifts (companion states) ?_ ?_ judgement
  · intro authority target
    constructor
    · intro member
      refine ⟨states.symm target, ?_, ⟨⟨⟨states.apply_symm_apply target⟩⟩⟩⟩
      exact (square authority (states.symm target)).mp
        (by simpa only [states.apply_symm_apply] using member)
    · rintro ⟨source, member, ⟨same⟩⟩
      rw [← same.down.down]
      exact (square authority source).mpr member
  · intro source target same target' step
    refine ⟨states.symm target', ?_, ⟨⟨⟨states.apply_symm_apply target'⟩⟩⟩⟩
    have equal : source = states.symm target := by
      rw [← same.down.down, states.symm_apply_apply]
    rw [equal]
    exact reflects target target' step

/-- Reification squares compose using the existing resource maps and state
equivalences. No authority is reconstructed from a label. -/
theorem transport_square_comp {β γ : Type w}
    [Zero β] [Add β] [SepAlgebra β] [Zero γ] [Add γ] [SepAlgebra γ]
    {T U : Type v} (sourceView : α → Set S) (middleView : β → Set T)
    (targetView : γ → Set U) (first : Hom α β) (second : Hom β γ)
    (sourceStates : S ≃ T) (targetStates : T ≃ U)
    (firstSquare : ∀ authority state,
      sourceStates state ∈ middleView (first authority) ↔ state ∈ sourceView authority)
    (secondSquare : ∀ authority state,
      targetStates state ∈ targetView (second authority) ↔ state ∈ middleView authority) :
    ∀ authority state,
      (sourceStates.trans targetStates) state ∈ targetView (Hom.comp second first authority) ↔
        state ∈ sourceView authority := by
  intro authority state
  exact (secondSquare (first authority) (sourceStates state)).trans (firstSquare authority state)

/-- Transported frame judgements compose through the actual middle action.
The source/middle/target relations remain separately supplied semantics. -/
theorem transport_comp {β γ : Type w}
    [Zero β] [Add β] [SepAlgebra β] [Zero γ] [Add γ] [SepAlgebra γ]
    {T U : Type v} {sourceView : α → Set S} {middleView : β → Set T}
    {targetView : γ → Set U} {sourceAct : S → S → Prop}
    {middleAct : T → T → Prop} {targetAct : U → U → Prop} {p q : α}
    (first : Hom α β) (second : Hom β γ)
    (firstLifts : first.LiftsExtensions) (secondLifts : second.LiftsExtensions)
    (sourceStates : S ≃ T) (targetStates : T ≃ U)
    (firstSquare : ∀ authority state,
      sourceStates state ∈ middleView (first authority) ↔ state ∈ sourceView authority)
    (secondSquare : ∀ authority state,
      targetStates state ∈ targetView (second authority) ↔ state ∈ middleView authority)
    (firstReflects : ∀ before after, middleAct before after →
      sourceAct (sourceStates.symm before) (sourceStates.symm after))
    (secondReflects : ∀ before after, targetAct before after →
      middleAct (targetStates.symm before) (targetStates.symm after))
    (judgement : ActionPreserves sourceView sourceAct p q) :
    ActionPreserves targetView targetAct (Hom.comp second first p) (Hom.comp second first q) :=
  transport second secondLifts targetStates secondSquare secondReflects
    (transport first firstLifts sourceStates firstSquare firstReflects judgement)

end ActionPreserves

/-! ## Straight-line threads and their interleavings -/

/-- A chain of authority through a list of actions, each step satisfying the
action judgement. -/
inductive Chain (reify : α → Set S) : List (S → S → Prop) → α → α → Prop where
  | nil (p : α) : Chain reify [] p p
  | cons {act : S → S → Prop} {acts : List (S → S → Prop)} {p m q : α} :
      ActionPreserves reify act p m → Chain reify acts m q → Chain reify (act :: acts) p q

/-- Run a list of actions in order. -/
def RunList : List (S → S → Prop) → S → S → Prop
  | [], s, s' => s = s'
  | act :: acts, s, s'' => ∃ s', act s s' ∧ RunList acts s' s''

/-- The interleavings of two lists. -/
inductive Interleaving {β : Type w} : List β → List β → List β → Prop where
  | nil : Interleaving [] [] []
  | left {x : β} {first second merged : List β} :
      Interleaving first second merged → Interleaving (x :: first) second (x :: merged)
  | right {x : β} {first second merged : List β} :
      Interleaving first second merged → Interleaving first (x :: second) (x :: merged)

/-- **Interleaving soundness.**  Two threads whose steps satisfy the action
judgement, started from separate authority, end in the combination of their
final authority, whichever way their steps are interleaved. -/
theorem parallel {reify : α → Set S} {first second merged : List (S → S → Prop)}
    (order : Interleaving first second merged) :
    ∀ {p₁ q₁ p₂ q₂ : α}, Chain reify first p₁ q₁ → Chain reify second p₂ q₂ → p₁ ## p₂ →
      ∀ s ∈ reify (p₁ + p₂), ∀ s', RunList merged s s' → q₁ ## q₂ ∧ s' ∈ reify (q₁ + q₂) := by
  induction order with
  | nil =>
      intro p₁ q₁ p₂ q₂ chain₁ chain₂ separate s holds s' run
      cases chain₁
      cases chain₂
      cases run
      exact ⟨separate, holds⟩
  | @left act first second merged _ ih =>
      intro p₁ q₁ p₂ q₂ chain₁ chain₂ separate s holds s'' run
      cases chain₁ with
      | cons step rest =>
          obtain ⟨s', move, run'⟩ := run
          obtain ⟨separate', holds'⟩ := step p₂ separate s holds s' move
          exact ih rest chain₂ separate' s' holds' s'' run'
  | @right act first second merged _ ih =>
      intro p₁ q₁ p₂ q₂ chain₁ chain₂ separate s holds s'' run
      cases chain₂ with
      | cons step rest =>
          obtain ⟨s', move, run'⟩ := run
          rw [SepAlgebra.add_comm separate] at holds
          obtain ⟨separate', holds'⟩ := step p₁ (separate_symm separate) s holds s' move
          rw [SepAlgebra.add_comm separate'] at holds'
          exact ih chain₁ rest (separate_symm separate') s' holds' s'' run'

/-! ## Controls: two exclusively owned cells -/

namespace TwoCells

/-- Ownership of two cells, each either unowned or owned with a value. -/
abbrev Authority := Excl Bool × Excl Bool

/-- A state assigns a value to each cell. -/
abbrev State := Bool × Bool

/-- The states consistent with the owned cells. -/
def reify (x : Authority) : Set State :=
  {s | (∀ v, x.1 = .own v → s.1 = v) ∧ (∀ v, x.2 = .own v → s.2 = v)}

/-- Write `true` into the first cell. -/
def writeFirst : State → State → Prop := fun s s' => s' = (true, s.2)

/-- Write `true` into the second cell. -/
def writeSecond : State → State → Prop := fun s s' => s' = (s.1, true)

/-- **Positive control**: the owner of the first cell may write it. -/
theorem writeFirst_preserves :
    ActionPreserves reify writeFirst ((.own false, .empty) : Authority) (.own true, .empty) := by
  rintro ⟨r₁, r₂⟩ ⟨separate₁, -⟩ s ⟨own₁, own₂⟩ s' rfl
  have r₁empty : r₁ = .empty := by
    rcases separate₁ with owned | empty
    · cases owned
    · exact empty
  subst r₁empty
  refine ⟨⟨Or.inr rfl, Or.inl rfl⟩, ?_, ?_⟩
  · intro v owned
    cases owned
    rfl
  · intro v owned
    exact own₂ v owned

/-- The second-cell write satisfies the judgement with the empty frame. -/
theorem writeSecond_local :
    ∀ s ∈ reify ((.own false, .empty) : Authority), ∀ s', writeSecond s s' →
      s' ∈ reify ((.own false, .empty) : Authority) := by
  rintro s ⟨own₁, -⟩ s' rfl
  refine ⟨fun v owned => own₁ v owned, ?_⟩
  intro v owned
  cases owned

/-- **Negative control**: writing a cell one does not own breaks the frame of
its owner. -/
theorem writeSecond_not_preserves :
    ¬ ActionPreserves reify writeSecond ((.own false, .empty) : Authority) (.own false, .empty) := by
  intro judgement
  have separate : ((.own false, .empty) : Authority) ## (.empty, .own false) :=
    ⟨Or.inr rfl, Or.inl rfl⟩
  have holds : ((false, false) : State) ∈
      reify (((.own false, .empty) : Authority) + (.empty, .own false)) := by
    refine ⟨?_, ?_⟩
    · intro v owned
      cases owned
      rfl
    · intro v owned
      cases owned
      rfl
  obtain ⟨-, after⟩ := judgement _ separate (false, false) holds (false, true) rfl
  have wrong := after.2 false rfl
  cases wrong

open Mettapedia.GSLT.Logic.SeparationTransport

/-- Exchange the two resource locations without changing either cell's right. -/
def swapAuthority : Hom Authority Authority where
  toFun authority := (authority.2, authority.1)
  map_zero := rfl
  map_add _ := rfl
  map_separate separate := ⟨separate.2, separate.1⟩

theorem swapAuthority_liftsExtensions : swapAuthority.LiftsExtensions := by
  intro authority frame separate
  exact ⟨(frame.2, frame.1), ⟨separate.2, separate.1⟩, rfl⟩

theorem swap_reification_square (authority : Authority) (state : State) :
    (Equiv.prodComm Bool Bool) state ∈ reify (swapAuthority authority) ↔ state ∈ reify authority :=
  ⟨fun holds => ⟨holds.2, holds.1⟩, fun holds => ⟨holds.2, holds.1⟩⟩

theorem swap_step_reflection (before after : State) (step : writeSecond before after) :
    writeFirst ((Equiv.prodComm Bool Bool).symm before)
      ((Equiv.prodComm Bool Bool).symm after) := by
  cases step
  rfl

/-- A non-identity location encoding transports the actual owned write law. -/
theorem writeSecond_preserves_owned_second :
    ActionPreserves reify writeSecond ((.empty, .own false) : Authority) (.empty, .own true) :=
  ActionPreserves.transport swapAuthority swapAuthority_liftsExtensions
    (Equiv.prodComm Bool Bool) swap_reification_square swap_step_reflection writeFirst_preserves

/-! ### A relational representation with an observable effect log -/

abbrev LoggedState := State × List Bool

def loggedReify (authority : Authority) : Set LoggedState :=
  {state | state.1 ∈ reify authority}

/-- The relation forgets the effect log, while retaining the actual cell
state. Its fibres admit arbitrary logs, so it is not the cell swap encoding. -/
def logRelation : LooseRelationEquipment.Loose State LoggedState :=
  fun source target => LooseRelationEquipment.EqWitness source target.1

theorem log_reification_square :
    ActionPreserves.ReifiesThrough (Hom.id Authority) logRelation reify loggedReify := by
  intro authority target
  constructor
  · intro member
    exact ⟨target.1, member, ⟨⟨⟨rfl⟩⟩⟩⟩
  · rintro ⟨source, member, ⟨same⟩⟩
    change target.1 ∈ reify authority
    rwa [← same.down.down]

def emit (event : Bool) : LoggedState → LoggedState → Prop :=
  fun before after => after = (before.1, before.2 ++ [event])

theorem emit_reflects_cell_idle (event : Bool) :
    ActionPreserves.ReflectsThrough logRelation (fun before after => before = after) (emit event) := by
  intro source target same target' step
  subst target'
  exact ⟨source, rfl, ⟨same⟩⟩

/-- Frame safety transports even when the target adds observable events that
the resource reification does not mention. -/
theorem emit_preserves (event : Bool) (authority : Authority) :
    ActionPreserves loggedReify (emit event) authority authority :=
  ActionPreserves.transport_relation (Hom.id Authority) Hom.id_liftsExtensions
    logRelation log_reification_square (emit_reflects_cell_idle event)
    (ActionPreserves.idle reify authority)

/-- Both event orders preserve the same owned cells, yet a log observer
distinguishes them. Frame preservation alone grants no commutation licence. -/
theorem frame_safety_does_not_determine_effect_order :
    let authority : Authority := (.own false, .own false)
    let initial : LoggedState := ((false, false), [])
    ActionPreserves loggedReify (emit false) authority authority ∧
    ActionPreserves loggedReify (emit true) authority authority ∧
    initial ∈ loggedReify authority ∧
    seqAct (emit false) (emit true) initial ((false, false), [false, true]) ∧
    seqAct (emit true) (emit false) initial ((false, false), [true, false]) ∧
    ([false, true] : List Bool) ≠ [true, false] := by
  refine ⟨emit_preserves _ _, emit_preserves _ _, ?_, ?_, ?_, by decide⟩
  · constructor <;> intro value owned <;> cases owned <;> rfl
  · exact ⟨((false, false), [false]), rfl, rfl⟩
  · exact ⟨((false, false), [true]), rfl, rfl⟩

/-! ### A world transport without the required frame back law -/

def forgetSecondAuthority : Hom Authority Authority where
  toFun authority := (authority.1, .empty)
  map_zero := rfl
  map_add _ := rfl
  map_separate separate := ⟨separate.1, Or.inl rfl⟩

private def representative : Excl Bool → Bool
  | .empty => false
  | .own value => value

def firstCellRelation : LooseRelationEquipment.Loose State State :=
  fun source target => LooseRelationEquipment.EqWitness source.1 target.1

/-- Forgetting the second right has an actual relational reification square;
that square still does not provide arbitrary target frames. -/
theorem forgetSecond_reifies :
    ActionPreserves.ReifiesThrough forgetSecondAuthority firstCellRelation reify reify := by
  intro authority target
  constructor
  · intro member
    refine ⟨(target.1, representative authority.2), ⟨member.1, ?_⟩, ⟨⟨⟨rfl⟩⟩⟩⟩
    intro value owned
    rw [owned]
    rfl
  · rintro ⟨source, member, ⟨same⟩⟩
    refine ⟨?_, ?_⟩
    · intro value owned
      exact same.down.down.symm.trans (member.1 value owned)
    · intro value owned
      cases owned

def writeBoth : State → State → Prop := fun _ after => after = (true, true)

theorem writeBoth_reflects_first :
    ActionPreserves.ReflectsThrough firstCellRelation writeFirst writeBoth := by
  intro source target _ target' step
  subst target'
  exact ⟨(true, source.2), rfl, ⟨⟨⟨rfl⟩⟩⟩⟩

/-- The missing frame lift is observable: the reflected action overwrites an
independent owner of the forgotten cell, although the source write is safe. -/
theorem writeBoth_not_preserves :
    ¬ ActionPreserves reify writeBoth
      (forgetSecondAuthority ((.own false, .empty) : Authority))
      (forgetSecondAuthority ((.own true, .empty) : Authority)) := by
  intro judgement
  have separate : ((.own false, .empty) : Authority) ## (.empty, .own false) :=
    ⟨Or.inr rfl, Or.inl rfl⟩
  have holds : ((false, false) : State) ∈
      reify (((.own false, .empty) : Authority) + (.empty, .own false)) := by
    constructor <;> intro value owned <;> cases owned <;> rfl
  obtain ⟨_, after⟩ := judgement _ separate (false, false) holds (true, true) rfl
  cases after.2 false rfl

theorem forgetSecond_does_not_lift_frames : ¬ forgetSecondAuthority.LiftsExtensions := by
  intro lifts
  exact writeBoth_not_preserves (ActionPreserves.transport_relation forgetSecondAuthority lifts
    firstCellRelation forgetSecond_reifies writeBoth_reflects_first writeFirst_preserves)

end TwoCells

/-! ## Axiom audit -/

#print axioms ActionPreserves.frame
#print axioms ActionPreserves.seq
#print axioms ActionPreserves.frameUpdate_of_enabled
#print axioms parallel
#print axioms TwoCells.writeFirst_preserves
#print axioms TwoCells.writeSecond_not_preserves
#print axioms ActionPreserves.transport
#print axioms ActionPreserves.ReifiesThrough.comp
#print axioms ActionPreserves.ReflectsThrough.comp
#print axioms ActionPreserves.transport_relation
#print axioms ActionPreserves.transport_relation_comp
#print axioms ActionPreserves.transport_square_comp
#print axioms ActionPreserves.transport_comp
#print axioms TwoCells.writeSecond_preserves_owned_second
#print axioms TwoCells.log_reification_square
#print axioms TwoCells.emit_preserves
#print axioms TwoCells.frame_safety_does_not_determine_effect_order
#print axioms TwoCells.forgetSecond_reifies
#print axioms TwoCells.writeBoth_reflects_first
#print axioms TwoCells.writeBoth_not_preserves
#print axioms TwoCells.forgetSecond_does_not_lift_frames

end Mettapedia.GSLT.Contracts
