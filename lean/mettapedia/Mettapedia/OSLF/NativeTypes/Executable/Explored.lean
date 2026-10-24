import Mettapedia.OSLF.NativeTypes.Executable.Finite

/-!
# Exact verdicts from a finite exploration

A finite exploration lists states and the transitions found between them. It decides future
modal formulas about a source span, which may be infinite, at the source states of an invariant
(`good`, for instance well-sortedness), when these conditions hold:
- steps from good states end at good states (`ForwardClosed`);
- every listed state is good (`Exact.good`);
- every listed transition is a source transition from a good state, up to an equivalence
  (`Exact.valid`);
- every source transition out of a listed state is listed, up to the equivalence (`Exact.covers`);
- every listed transition ends at a listed state (`Exact.closed`);
- the equivalence matches futures on good states: equivalent good states have equivalent
  successors (`FutureMatchingOn`).

The good states form a sub-system whose inclusion lifts outgoing steps (`inclusion_sourceLifts`).
The exploration and that sub-system both map onto the sub-system's quotient with outgoing lifting
(`Exploration.observation_sourceLifts`, `quotient_sourceLifts_iff`). A future formula whose atoms
respect the equivalence has one truth value at a good source state and at every listed state
equivalent to it (`Exploration.satisfies_iff`), and the finite checker decides it
(`check_positive_iff`, `check_negative_iff`).

The equivalence may be the source's own equations; then finiteness means the source has finitely
many reachable classes. It may also be coarser, an abstraction: then the source may have infinitely
many reachable states, and future matching is the condition that the abstraction loses no answer.

Past modalities are refused (`FutureOnly`): an exploration from one root covers outgoing
transitions only.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Executable.Explored

open Mettapedia.OSLF.Framework.DerivedModalities
open Mettapedia.GSLT.ObservationSpans
open Mettapedia.Logic.ModalMuCalculus
open Mettapedia.GSLT.LanguageDef.CertificateGSLT.MuCalculusBoundary
open Mettapedia.OSLF.NativeTypes.Decision
open Mettapedia.OSLF.NativeTypes.Semantics.ModalFormula
open Reference.Core (Outcome)

universe u v e f

/-! ## Future formulas -/

/-- The formula uses only future traversals. -/
def FutureOnly : {n : Nat} → Formula Traversal n → Bool
  | _, .tt | _, .ff | _, .var _ => true
  | _, .neg inner | _, .mu inner | _, .nu inner => FutureOnly inner
  | _, .conj left right | _, .disj left right => FutureOnly left && FutureOnly right
  | _, .diamond direction inner | _, .box direction inner =>
      direction == .future && FutureOnly inner

/-- **Outgoing lifting covers every future formula.** -/
theorem covers_of_futureOnly {X : Type u} {Y : Type v} {A : ReductionSpan.{u, e} X}
    {B : ReductionSpan.{v, f} Y} (observation : SpanMap A B) (lifts : observation.SourceLifts) :
    ∀ {n : Nat} (formula : Formula Traversal n), FutureOnly formula = true →
      CoversFormula observation formula
  | _, .tt, _ | _, .ff, _ | _, .var _, _ => trivial
  | _, .neg inner, future | _, .mu inner, future | _, .nu inner, future =>
      covers_of_futureOnly observation lifts inner future
  | _, .conj left right, future | _, .disj left right, future => by
      obtain ⟨first, second⟩ := Bool.and_eq_true_iff.mp future
      exact ⟨covers_of_futureOnly observation lifts left first,
        covers_of_futureOnly observation lifts right second⟩
  | _, .diamond direction inner, future | _, .box direction inner, future => by
      obtain ⟨forward, rest⟩ := Bool.and_eq_true_iff.mp future
      cases direction
      · exact ⟨lifts, covers_of_futureOnly observation lifts inner rest⟩
      · exact absurd forward (by decide)

/-! ## Good states -/

section Good

variable {X : Type u} (A : ReductionSpan.{u, e} X) (same : Setoid X) (good : X → Prop)

/-- Steps from good states end at good states. -/
def ForwardClosed : Prop := ∀ event : A.Edge, good (A.source event) → good (A.target event)

/-- **Equivalent good states have equivalent successors.** -/
def FutureMatchingOn : Prop :=
  ∀ ⦃left right : X⦄, good left → good right → same.r left right →
    ∀ event : A.Edge, A.source event = left →
      ∃ matched : A.Edge, A.source matched = right ∧ same.r (A.target event) (A.target matched)

/-- The good states, with the transitions between them. -/
def restrict : ReductionSpan.{u, e} {state : X // good state} where
  Edge := {event : A.Edge // good (A.source event) ∧ good (A.target event)}
  source event := ⟨A.source event.1, event.2.1⟩
  target event := ⟨A.target event.1, event.2.2⟩

/-- The good states inside the source. -/
def inclusion : SpanMap (restrict A good) A where
  states := Subtype.val
  events := Subtype.val
  source_comm _ := rfl
  target_comm _ := rfl

/-- The equivalence on good states. -/
abbrev restrictedSame : Setoid {state : X // good state} := Setoid.comap Subtype.val same

end Good

section GoodFacts

variable {X : Type u} {A : ReductionSpan.{u, e} X} {same : Setoid X} {good : X → Prop}

theorem futureMatchingOn_of_futureMatching (matching : FutureMatching A same) :
    FutureMatchingOn A same good :=
  fun _ _ _ _ related event starts => matching related event starts

theorem inclusion_sourceLifts (closed : ForwardClosed A good) : (inclusion A good).SourceLifts := by
  intro state event starts
  have sourceGood : good (A.source event) := by rw [starts]; exact state.2
  exact ⟨⟨event, sourceGood, closed event sourceGood⟩, Subtype.ext starts, rfl⟩

theorem restricted_futureMatching (closed : ForwardClosed A good) (matching : FutureMatchingOn A same good) :
    FutureMatching (restrict A good) (restrictedSame same good) := by
  intro left right related event starts
  have sourceIs : A.source event.1 = left.1 := congrArg Subtype.val starts
  obtain ⟨matched, matchedSource, matchedTarget⟩ :=
    matching left.2 right.2 related event.1 sourceIs
  have sourceGood : good (A.source matched) := by rw [matchedSource]; exact right.2
  exact ⟨⟨matched, sourceGood, closed matched sourceGood⟩, Subtype.ext matchedSource, matchedTarget⟩

end GoodFacts

/-! ## Explorations -/

/-- Listed states, and transitions found between them. -/
structure Exploration (X : Type u) where
  states : List X
  edges : List (X × X)

namespace Exploration

/-- What an exploration must satisfy to stand for the good states of a source. -/
structure Exact {X : Type u} (exploration : Exploration X) (A : ReductionSpan.{u, e} X) (same : Setoid X)
    (good : X → Prop) : Prop where
  statesGood : ∀ state ∈ exploration.states, good state
  closed : ∀ edge ∈ exploration.edges, edge.2 ∈ exploration.states
  valid : ∀ edge ∈ exploration.edges,
    ∃ event : A.Edge, good (A.source event) ∧ same.r (A.source event) edge.1 ∧
      same.r (A.target event) edge.2
  covers : ∀ state ∈ exploration.states, ∀ event : A.Edge, A.source event = state →
    ∃ target, (state, target) ∈ exploration.edges ∧ same.r (A.target event) target

section Finite

variable {X : Type u} (exploration : Exploration X)

/-- Positions in the list of states. -/
abbrev Index := Fin exploration.states.length

/-- The finite transition system: an edge between two positions whose states are a listed
transition. -/
def span : ReductionSpan exploration.Index where
  Edge := {pair : exploration.Index × exploration.Index //
    (exploration.states.get pair.1, exploration.states.get pair.2) ∈ exploration.edges}
  source edge := edge.1.1
  target edge := edge.1.2

/-- The table the finite checker reads. -/
def table [DecidableEq X] : FiniteGraph.Table exploration.span where
  edge source target := decide ((exploration.states.get source, exploration.states.get target) ∈
    exploration.edges)
  exact source target := by
    rw [decide_eq_true_iff]
    constructor
    · intro member
      exact ⟨⟨(source, target), member⟩, rfl, rfl⟩
    · rintro ⟨⟨⟨first, second⟩, member⟩, rfl, rfl⟩
      exact member

variable {exploration}

theorem get_mem (index : exploration.Index) : exploration.states.get index ∈ exploration.states :=
  List.mem_iff_get.mpr ⟨index, rfl⟩

end Finite

section Observation

variable {X : Type u} {A : ReductionSpan.{u, e} X} {same : Setoid X} {good : X → Prop}
variable {exploration : Exploration X}

/-- Each position observed as the class of its state among the good states; each finite edge as a
source transition it stands for. -/
noncomputable def observation (exact : exploration.Exact A same good) (closed : ForwardClosed A good) :
    SpanMap exploration.span (quotientSpan (restrict A good) (restrictedSame same good)) where
  states index := Quotient.mk _ ⟨exploration.states.get index, exact.statesGood _ (get_mem index)⟩
  events edge :=
    ⟨Classical.choose (exact.valid _ edge.2), (Classical.choose_spec (exact.valid _ edge.2)).1,
      closed _ (Classical.choose_spec (exact.valid _ edge.2)).1⟩
  source_comm edge := Quotient.sound (Classical.choose_spec (exact.valid _ edge.2)).2.1
  target_comm edge := Quotient.sound (Classical.choose_spec (exact.valid _ edge.2)).2.2

/-- **Every transition of a listed state's class is found from that state.** -/
theorem observation_sourceLifts (exact : exploration.Exact A same good) (closed : ForwardClosed A good)
    (matching : FutureMatchingOn A same good) : (observation exact closed).SourceLifts := by
  intro index event starts
  have related : same.r (A.source event.1) (exploration.states.get index) := by
    have exactly := Quotient.exact starts
    exact exactly
  obtain ⟨matched, matchedSource, matchedTarget⟩ :=
    matching event.2.1 (exact.statesGood _ (get_mem index)) related event.1 rfl
  obtain ⟨target, member, reached⟩ := exact.covers _ (get_mem index) matched matchedSource
  obtain ⟨position, found⟩ := List.mem_iff_get.mp (exact.closed _ member)
  refine ⟨⟨(index, position), by rw [found]; exact member⟩, rfl, ?_⟩
  apply Quotient.sound
  change same.r (exploration.states.get position) (A.target event.1)
  rw [found]
  exact same.symm (same.trans matchedTarget reached)

end Observation

end Exploration

/-! ## Atoms -/

/-- Atoms that respect the equivalence. -/
structure Atoms {X : Type u} (same : Setoid X) (n : Nat) where
  holds : Fin n → X → Bool
  invariant : ∀ index {left right : X}, same.r left right → holds index left = holds index right

namespace Atoms

variable {X : Type u} {same : Setoid X} {n : Nat} (atoms : Atoms same n) (good : X → Prop)

/-- The source environment. -/
def meaning : Env X n := fun index => {state | atoms.holds index state = true}

/-- The classes of good states the atoms describe. -/
def classes : Env (Quotient (restrictedSame same good)) n :=
  fun index => {class_ | ∃ state : {state : X // good state},
    Quotient.mk _ state = class_ ∧ atoms.holds index state.1 = true}

theorem pull_classes :
    pullEnvironment (Quotient.mk (restrictedSame same good)) (atoms.classes good) =
      pullEnvironment Subtype.val atoms.meaning := by
  funext index
  ext state
  constructor
  · rintro ⟨other, sameClass, holds⟩
    have related := Quotient.exact sameClass
    exact (atoms.invariant index related).symm.trans holds
  · intro holds
    exact ⟨state, rfl, holds⟩

end Atoms

/-! ## The checker and its verdicts -/

namespace Exploration

variable {X : Type u} {same : Setoid X} (exploration : Exploration X) {n : Nat}

/-- The finite environment: the positions whose states satisfy each atom. -/
def environment (atoms : Atoms same n) : FiniteMuCalculus.Environment exploration.Index n :=
  fun index => Finset.univ.filter fun position => atoms.holds index (exploration.states.get position) = true

/-- **The finite checker on an exploration.** -/
def check [DecidableEq X] (formula : Formula Traversal n) (atoms : Atoms same n) (budget : Nat)
    (index : exploration.Index) :
    Option (Outcome (satisfies (transitionSystem exploration.span)
      (exploration.environment atoms).meaning formula index)) :=
  Finite.check exploration.table formula (exploration.environment atoms) budget index

variable {A : ReductionSpan.{u, e} X} {good : X → Prop} {exploration}

theorem environment_meaning (exact : exploration.Exact A same good) (closed : ForwardClosed A good)
    (atoms : Atoms same n) :
    (exploration.environment atoms).meaning =
      pullEnvironment (observation exact closed).states (atoms.classes good) := by
  funext index
  ext position
  simp only [FiniteMuCalculus.Environment.meaning, environment, Finset.coe_filter, Finset.mem_univ,
    true_and, Set.mem_ofPred_eq, pullEnvironment, Set.mem_preimage, Atoms.classes]
  constructor
  · intro holds
    exact ⟨_, rfl, holds⟩
  · rintro ⟨other, sameClass, holds⟩
    have related := Quotient.exact sameClass
    exact (atoms.invariant index related).symm.trans holds

/-- **One truth value at a good source state and at every listed state equivalent to it**, for
every future formula whose atoms respect the equivalence. -/
theorem satisfies_iff (exact : exploration.Exact A same good) (closed : ForwardClosed A good)
    (matching : FutureMatchingOn A same good) (formula : Formula Traversal n)
    (future : FutureOnly formula = true) (positive : fixedPointsPositive formula = true)
    (atoms : Atoms same n) (index : exploration.Index) {source : X} (sourceGood : good source)
    (related : same.r source (exploration.states.get index)) :
    satisfies (transitionSystem exploration.span) (exploration.environment atoms).meaning formula index ↔
      satisfies (transitionSystem A) atoms.meaning formula source := by
  have explored := satisfies_pullback (observation exact closed) formula
    (covers_of_futureOnly _ (observation_sourceLifts exact closed matching) formula future) positive
    (atoms.classes good) index
  have quotiented := satisfies_pullback (quotientMap (restrict A good) (restrictedSame same good)) formula
    (covers_of_futureOnly _ ((quotient_sourceLifts_iff _ _).mpr (restricted_futureMatching closed matching))
      formula future) positive (atoms.classes good) ⟨source, sourceGood⟩
  have included := satisfies_pullback (inclusion A good) formula
    (covers_of_futureOnly _ (inclusion_sourceLifts closed) formula future) positive atoms.meaning
    ⟨source, sourceGood⟩
  have sameClass : (quotientMap (restrict A good) (restrictedSame same good)).states ⟨source, sourceGood⟩ =
      (observation exact closed).states index :=
    Quotient.sound related
  rw [environment_meaning exact closed atoms]
  calc satisfies (transitionSystem exploration.span)
          (pullEnvironment (observation exact closed).states (atoms.classes good)) formula index
      ↔ satisfies (transitionSystem (quotientSpan (restrict A good) (restrictedSame same good)))
          (atoms.classes good) formula ((observation exact closed).states index) := explored.symm
    _ ↔ satisfies (transitionSystem (quotientSpan (restrict A good) (restrictedSame same good)))
          (atoms.classes good) formula
          ((quotientMap (restrict A good) (restrictedSame same good)).states ⟨source, sourceGood⟩) := by
        rw [sameClass]
    _ ↔ satisfies (transitionSystem (restrict A good))
          (pullEnvironment (Quotient.mk (restrictedSame same good)) (atoms.classes good)) formula
          ⟨source, sourceGood⟩ := quotiented
    _ ↔ satisfies (transitionSystem (restrict A good)) (pullEnvironment Subtype.val atoms.meaning) formula
          ⟨source, sourceGood⟩ := by rw [atoms.pull_classes good]
    _ ↔ _ := included.symm

/-- **A positive verdict is the source property.** -/
theorem check_positive_iff [DecidableEq X] (exact : exploration.Exact A same good)
    (closed : ForwardClosed A good) (matching : FutureMatchingOn A same good)
    (formula : Formula Traversal n) (future : FutureOnly formula = true)
    (positive : fixedPointsPositive formula = true) (atoms : Atoms same n) (budget : Nat)
    (index : exploration.Index) {source : X} (sourceGood : good source)
    (related : same.r source (exploration.states.get index))
    (enough : FiniteMuCalculus.requiredBudget (State := exploration.Index) formula ≤ budget) :
    (exploration.check formula atoms budget index).map Outcome.answer = some (some true) ↔
      satisfies (transitionSystem A) atoms.meaning formula source :=
  (Finite.check_positive_iff exploration.table formula positive _ budget index enough).trans
    (satisfies_iff exact closed matching formula future positive atoms index sourceGood related)

/-- **A negative verdict is the failure of the source property.** -/
theorem check_negative_iff [DecidableEq X] (exact : exploration.Exact A same good)
    (closed : ForwardClosed A good) (matching : FutureMatchingOn A same good)
    (formula : Formula Traversal n) (future : FutureOnly formula = true)
    (positive : fixedPointsPositive formula = true) (atoms : Atoms same n) (budget : Nat)
    (index : exploration.Index) {source : X} (sourceGood : good source)
    (related : same.r source (exploration.states.get index))
    (enough : FiniteMuCalculus.requiredBudget (State := exploration.Index) formula ≤ budget) :
    (exploration.check formula atoms budget index).map Outcome.answer = some (some false) ↔
      ¬ satisfies (transitionSystem A) atoms.meaning formula source :=
  (Finite.check_negative_iff exploration.table formula positive _ budget index enough).trans
    (not_congr (satisfies_iff exact closed matching formula future positive atoms index sourceGood related))

end Exploration

/-! ## A theory's own equations match futures -/

/-- **Steps of a GSLT respect its equations**, so its own equations match futures. -/
theorem gslt_futureMatching (theory : Mettapedia.GSLT.GSLT) :
    FutureMatching (Mettapedia.OSLF.Framework.GSLTTypeSynthesis.gsltSpan theory) theory.equations := by
  intro left right related event starts
  obtain ⟨reached, step, sameTarget⟩ := theory.rewrites_resp_left (starts ▸ related) event.step
  exact ⟨⟨right, reached, step⟩, rfl, sameTarget⟩

end Mettapedia.OSLF.NativeTypes.Executable.Explored
