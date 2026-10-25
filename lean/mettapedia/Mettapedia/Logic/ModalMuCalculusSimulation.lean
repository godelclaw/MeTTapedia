import Mettapedia.Logic.ModalMuCalculus

/-!
# Simulations preserve the existential μ-calculus

A relation between the states of two transition systems is a simulation when every transition from a
related state is matched, label for label, by a transition of the second system between related
states. Along a simulation, every formula built without negation and without boxes that holds at a
state holds at every state related to it (`satisfies_of_simulation`), least and greatest fixed points
included:

- a least fixed point is the intersection of the closed sets. A closed set of the target pulls back to
  a closed set of the source: the states whose related states all lie in it;
- a greatest fixed point is the union of the invariant sets. An invariant set of the source pushes
  forward to an invariant set of the target: the states related to one of its states.

Formulas without negation and without diamonds go the other way (`satisfies_of_simulation_universal`):
when one holds at a state of the simulating system, it holds at every state related to it. A box there
covers every matched transition, and the fixed points transfer as above with the roles of the two systems
exchanged.

A map that preserves transitions is the special case of its graph. So a small system that a large one
maps into decides two things for it:
- it refutes existential formulas: when one fails at the image of a state, it fails at the state
  (`not_satisfies_of_preserves`);
- it proves universal ones: when one holds at the image of a state, it holds at the state
  (`satisfies_of_preserves_universal`).

Nothing more is transferred:
- a box over the source's transitions says nothing about the target's extra ones (`box_not_preserved`);
- an existential formula can hold at the image of a state where it fails (`diamond_not_reflected`).
-/

set_option autoImplicit false

namespace Mettapedia.Logic.ModalMuCalculus

universe u v w

variable {S : Type u} {T : Type v} {Act : Type w}

/-- Whether a formula uses neither negation nor boxes. -/
def Formula.existential : {n : ℕ} → Formula Act n → Bool
  | _, .tt => true
  | _, .ff => true
  | _, .neg _ => false
  | _, .conj first second => first.existential && second.existential
  | _, .disj first second => first.existential && second.existential
  | _, .diamond _ body => body.existential
  | _, .box _ _ => false
  | _, .mu body => body.existential
  | _, .nu body => body.existential
  | _, .var _ => true

/-- **A simulation**: every transition from a related state is matched by a transition with the same
label between related states. -/
def IsSimulation (source : LTS S Act) (target : LTS T Act) (relation : S → T → Prop) : Prop :=
  ∀ state image, relation state image → ∀ action next, source.trans state action next →
    ∃ nextImage, target.trans image action nextImage ∧ relation next nextImage

/-- Environments related along a relation: a state in a predicate of the source is related only to
states in the target's. -/
def EnvRelated {n : ℕ} (relation : S → T → Prop) (sourceEnv : Env S n) (targetEnv : Env T n) : Prop :=
  ∀ index state image, relation state image → state ∈ sourceEnv index → image ∈ targetEnv index

theorem EnvRelated.extend {n : ℕ} {relation : S → T → Prop} {sourceEnv : Env S n} {targetEnv : Env T n}
    (related : EnvRelated relation sourceEnv targetEnv) {first : Set S} {second : Set T}
    (inside : ∀ state image, relation state image → state ∈ first → image ∈ second) :
    EnvRelated relation (sourceEnv.extend first) (targetEnv.extend second) := by
  intro index state image relates member
  unfold Env.extend at member ⊢
  split
  · rename_i zero
    simp only [zero, ↓reduceDIte] at member
    exact inside state image relates member
  · rename_i nonzero
    simp only [nonzero, ↓reduceDIte] at member
    exact related _ state image relates member

/-- **Simulations preserve the existential μ-calculus**: a formula without negation or boxes that
holds at a state holds at every state related to it. -/
theorem satisfies_of_simulation {source : LTS S Act} {target : LTS T Act} {relation : S → T → Prop}
    (simulates : IsSimulation source target relation) :
    ∀ {n : ℕ} (formula : Formula Act n), formula.existential = true →
      ∀ {sourceEnv : Env S n} {targetEnv : Env T n}, EnvRelated relation sourceEnv targetEnv →
        ∀ state image, relation state image →
          satisfies source sourceEnv formula state → satisfies target targetEnv formula image
  | _, .tt, _, _, _, _, _, _, _, _ => trivial
  | _, .ff, _, _, _, _, _, _, _, holds => holds
  | _, .neg _, existential, _, _, _, _, _, _, _ => by simp [Formula.existential] at existential
  | _, .box _ _, existential, _, _, _, _, _, _, _ => by simp [Formula.existential] at existential
  | _, .conj first second, existential, _, _, related, state, image, relates, holds => by
    simp only [Formula.existential, Bool.and_eq_true] at existential
    exact ⟨satisfies_of_simulation simulates first existential.1 related state image relates holds.1,
      satisfies_of_simulation simulates second existential.2 related state image relates holds.2⟩
  | _, .disj first second, existential, _, _, related, state, image, relates, holds => by
    simp only [Formula.existential, Bool.and_eq_true] at existential
    rcases holds with left | right
    · exact Or.inl (satisfies_of_simulation simulates first existential.1 related state image relates left)
    · exact Or.inr (satisfies_of_simulation simulates second existential.2 related state image relates right)
  | _, .diamond action body, existential, _, _, related, state, image, relates, holds => by
    obtain ⟨next, step, nextHolds⟩ := holds
    obtain ⟨nextImage, imageStep, nextRelates⟩ := simulates state image relates action next step
    exact ⟨nextImage, imageStep,
      satisfies_of_simulation simulates body existential related next nextImage nextRelates nextHolds⟩
  | _, .var index, _, _, _, related, state, image, relates, holds => related index state image relates holds
  | _, .mu body, existential, _, _, related, state, image, relates, holds => by
    intro closed closedHolds
    let pulled : Set _ := {other | ∀ otherImage, relation other otherImage → otherImage ∈ closed}
    have inside : ∀ other otherImage, relation other otherImage → other ∈ pulled → otherImage ∈ closed :=
      fun _ otherImage otherRelates member => member otherImage otherRelates
    have pulledHolds := holds pulled fun next nextHolds nextImage nextRelates =>
      closedHolds nextImage (satisfies_of_simulation simulates body existential (related.extend inside)
        next nextImage nextRelates nextHolds)
    exact pulledHolds image relates
  | _, .nu body, existential, _, _, related, state, image, relates, holds => by
    obtain ⟨invariant, member, preserved⟩ := holds
    let pushed : Set _ := {other | ∃ origin ∈ invariant, relation origin other}
    have inside : ∀ origin other, relation origin other → origin ∈ invariant → other ∈ pushed :=
      fun origin _ originRelates originMember => ⟨origin, originMember, originRelates⟩
    refine ⟨pushed, inside state image relates member, ?_⟩
    rintro other ⟨origin, originMember, originRelates⟩
    exact satisfies_of_simulation simulates body existential (related.extend inside)
      origin other originRelates (preserved origin originMember)

/-- **A simulating system refutes**: when an existential formula fails at a state related to another,
it fails at the other. -/
theorem not_satisfies_of_simulation {source : LTS S Act} {target : LTS T Act} {relation : S → T → Prop}
    (simulates : IsSimulation source target relation) {n : ℕ} {formula : Formula Act n}
    (existential : formula.existential = true) {sourceEnv : Env S n} {targetEnv : Env T n}
    (related : EnvRelated relation sourceEnv targetEnv) {state : S} {image : T} (relates : relation state image)
    (fails : ¬ satisfies target targetEnv formula image) : ¬ satisfies source sourceEnv formula state :=
  fun holds => fails (satisfies_of_simulation simulates formula existential related state image relates holds)

/-! ## The universal fragment goes the other way -/

/-- Whether a formula uses neither negation nor diamonds. -/
def Formula.universal : {n : ℕ} → Formula Act n → Bool
  | _, .tt => true
  | _, .ff => true
  | _, .neg _ => false
  | _, .conj first second => first.universal && second.universal
  | _, .disj first second => first.universal && second.universal
  | _, .diamond _ _ => false
  | _, .box _ body => body.universal
  | _, .mu body => body.universal
  | _, .nu body => body.universal
  | _, .var _ => true

/-- Environments related backward along a relation: a state related to one in a predicate of the target
lies in the source's. -/
def EnvRelatedBack {n : ℕ} (relation : S → T → Prop) (sourceEnv : Env S n) (targetEnv : Env T n) : Prop :=
  ∀ index state image, relation state image → image ∈ targetEnv index → state ∈ sourceEnv index

theorem EnvRelatedBack.extend {n : ℕ} {relation : S → T → Prop} {sourceEnv : Env S n} {targetEnv : Env T n}
    (related : EnvRelatedBack relation sourceEnv targetEnv) {first : Set S} {second : Set T}
    (inside : ∀ state image, relation state image → image ∈ second → state ∈ first) :
    EnvRelatedBack relation (sourceEnv.extend first) (targetEnv.extend second) := by
  intro index state image relates member
  unfold Env.extend at member ⊢
  split
  · rename_i zero
    simp only [zero, ↓reduceDIte] at member
    exact inside state image relates member
  · rename_i nonzero
    simp only [nonzero, ↓reduceDIte] at member
    exact related _ state image relates member

/-- **Simulations carry the universal μ-calculus back**: a formula without negation or diamonds that
holds at a state of the simulating system holds at every state related to it. -/
theorem satisfies_of_simulation_universal {source : LTS S Act} {target : LTS T Act} {relation : S → T → Prop}
    (simulates : IsSimulation source target relation) :
    ∀ {n : ℕ} (formula : Formula Act n), formula.universal = true →
      ∀ {sourceEnv : Env S n} {targetEnv : Env T n}, EnvRelatedBack relation sourceEnv targetEnv →
        ∀ state image, relation state image →
          satisfies target targetEnv formula image → satisfies source sourceEnv formula state
  | _, .tt, _, _, _, _, _, _, _, _ => trivial
  | _, .ff, _, _, _, _, _, _, _, holds => holds
  | _, .neg _, universal, _, _, _, _, _, _, _ => by simp [Formula.universal] at universal
  | _, .diamond _ _, universal, _, _, _, _, _, _, _ => by simp [Formula.universal] at universal
  | _, .conj first second, universal, _, _, related, state, image, relates, holds => by
    simp only [Formula.universal, Bool.and_eq_true] at universal
    exact ⟨satisfies_of_simulation_universal simulates first universal.1 related state image relates holds.1,
      satisfies_of_simulation_universal simulates second universal.2 related state image relates holds.2⟩
  | _, .disj first second, universal, _, _, related, state, image, relates, holds => by
    simp only [Formula.universal, Bool.and_eq_true] at universal
    rcases holds with left | right
    · exact Or.inl (satisfies_of_simulation_universal simulates first universal.1 related state image relates left)
    · exact Or.inr (satisfies_of_simulation_universal simulates second universal.2 related state image relates right)
  | _, .box action body, universal, _, _, related, state, image, relates, holds => by
    intro next step
    obtain ⟨nextImage, imageStep, nextRelates⟩ := simulates state image relates action next step
    exact satisfies_of_simulation_universal simulates body universal related next nextImage nextRelates
      (holds nextImage imageStep)
  | _, .var index, _, _, _, related, state, image, relates, holds => related index state image relates holds
  | _, .mu body, universal, _, _, related, state, image, relates, holds => by
    intro closed closedHolds
    let pushed : Set _ := {other | ∀ origin, relation origin other → origin ∈ closed}
    have inside : ∀ origin other, relation origin other → other ∈ pushed → origin ∈ closed :=
      fun origin _ originRelates member => member origin originRelates
    have pushedHolds := holds pushed fun other otherHolds origin originRelates =>
      closedHolds origin (satisfies_of_simulation_universal simulates body universal (related.extend inside)
        origin other originRelates otherHolds)
    exact pushedHolds state relates
  | _, .nu body, universal, _, _, related, state, image, relates, holds => by
    obtain ⟨invariant, member, preserved⟩ := holds
    let pulled : Set _ := {origin | ∃ other ∈ invariant, relation origin other}
    have inside : ∀ origin other, relation origin other → other ∈ invariant → origin ∈ pulled :=
      fun _ other originRelates otherMember => ⟨other, otherMember, originRelates⟩
    refine ⟨pulled, inside state image relates member, ?_⟩
    rintro origin ⟨other, otherMember, originRelates⟩
    exact satisfies_of_simulation_universal simulates body universal (related.extend inside)
      origin other originRelates (preserved other otherMember)

/-! ## Maps -/

/-- A map preserves transitions when every transition of the source has one with the same label
between the images. -/
def PreservesTransitions (source : LTS S Act) (target : LTS T Act) (map : S → T) : Prop :=
  ∀ state action next, source.trans state action next → target.trans (map state) action (map next)

/-- The graph of a map that preserves transitions is a simulation. -/
theorem PreservesTransitions.isSimulation {source : LTS S Act} {target : LTS T Act} {map : S → T}
    (preserves : PreservesTransitions source target map) :
    IsSimulation source target fun state image => map state = image := by
  rintro state _ rfl action next step
  exact ⟨map next, preserves state action next step, rfl⟩

/-- **Maps that preserve transitions preserve the existential μ-calculus**, for environments whose
source predicates map into the target's. -/
theorem satisfies_of_preserves {source : LTS S Act} {target : LTS T Act} {map : S → T}
    (preserves : PreservesTransitions source target map) {n : ℕ} (formula : Formula Act n)
    (existential : formula.existential = true) {sourceEnv : Env S n} {targetEnv : Env T n}
    (inside : ∀ index state, state ∈ sourceEnv index → map state ∈ targetEnv index) (state : S)
    (holds : satisfies source sourceEnv formula state) : satisfies target targetEnv formula (map state) :=
  satisfies_of_simulation preserves.isSimulation formula existential
    (fun index state _ relates member => relates ▸ inside index state member) state _ rfl holds

/-- **A system that a map preserves transitions into refutes**: when an existential formula fails at
the image of a state, it fails at the state. -/
theorem not_satisfies_of_preserves {source : LTS S Act} {target : LTS T Act} {map : S → T}
    (preserves : PreservesTransitions source target map) {n : ℕ} {formula : Formula Act n}
    (existential : formula.existential = true) {sourceEnv : Env S n} {targetEnv : Env T n}
    (inside : ∀ index state, state ∈ sourceEnv index → map state ∈ targetEnv index) {state : S}
    (fails : ¬ satisfies target targetEnv formula (map state)) : ¬ satisfies source sourceEnv formula state :=
  fun holds => fails (satisfies_of_preserves preserves formula existential inside state holds)

/-- **A system that a map preserves transitions into proves universal formulas**: a formula without
negation or diamonds that holds at the image of a state holds at the state, for environments whose
source predicates contain the preimages of the target's. -/
theorem satisfies_of_preserves_universal {source : LTS S Act} {target : LTS T Act} {map : S → T}
    (preserves : PreservesTransitions source target map) {n : ℕ} (formula : Formula Act n)
    (universal : formula.universal = true) {sourceEnv : Env S n} {targetEnv : Env T n}
    (inside : ∀ index state, map state ∈ targetEnv index → state ∈ sourceEnv index) (state : S)
    (holds : satisfies target targetEnv formula (map state)) : satisfies source sourceEnv formula state :=
  satisfies_of_simulation_universal preserves.isSimulation formula universal
    (fun index state _ relates member => inside index state (relates ▸ member)) state _ rfl holds

/-! ## Nothing more is transferred -/

/-- One state with no transitions. -/
def stuck : LTS Unit Unit where
  trans _ _ _ := False

/-- One state with a loop. -/
def looping : LTS Unit Unit where
  trans _ _ _ := True

theorem stuck_preserved : PreservesTransitions stuck looping id := fun _ _ _ step => step.elim

/-- **A box need not survive a simulation**: "every step reaches nowhere" holds where nothing steps,
and fails at its image, which loops. -/
theorem box_not_preserved :
    satisfies stuck Env.empty (.box () .ff) () ∧ ¬ satisfies looping Env.empty (.box () .ff) () := by
  refine ⟨fun _ step => step.elim, fun holds => ?_⟩
  exact holds () trivial

/-- **An existential formula need not be reflected**: "some step" holds at the image, which loops, and
fails where nothing steps. -/
theorem diamond_not_reflected :
    satisfies looping Env.empty (.diamond () .tt) () ∧ ¬ satisfies stuck Env.empty (.diamond () .tt) () := by
  refine ⟨⟨(), trivial, trivial⟩, ?_⟩
  rintro ⟨_, step, _⟩
  exact step

end Mettapedia.Logic.ModalMuCalculus
