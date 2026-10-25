import Mettapedia.Coalgebra.FiniteViewComputationalTrinity
import Mettapedia.Coalgebra.StreamGSLT

/-!
# Coalgebraic behavior in the computational trinity

This is the stream instance of `FiniteViewComputationalTrinity`. Final
unfolding supplies the operational-to-behavior map; compatible prefixes give
the view map. The existing stream GSLT supplies operational transitions.

Streams and coherent prefix towers are equivalent. State identity agrees
exactly with behavior only when unfolding is both faithful and complete.
The witnesses below retain agreement with that unfolding, and the controls
separate loss of operational identity from incomplete behavior coverage.

-/

set_option autoImplicit false

namespace Mettapedia.Coalgebra.ComputationalTrinity

open CategoryTheory
open Mettapedia.Coalgebra.StreamFinality
open Mettapedia.Coalgebra.StreamGSLT
open Mettapedia.Coalgebra.CoherentPrefixTower
open Mettapedia.Coalgebra.CoherentFiniteViewSystem
open Mettapedia.Computability.ComputationalTrinity

universe u

variable {Label : Type u}

abbrev Context := Discrete PUnit

/-! ## The three faces and their comparison -/

def stateFace
    (coalgebra : Coalgebra.{u, u} Label) :
    Face.{0, 0, u} Context :=
  (Functor.const Contextᵒᵖ).obj coalgebra.Carrier

def behaviorFace (Label : Type u) :
    Face.{0, 0, u} Context :=
  (Functor.const Contextᵒᵖ).obj (Stream Label)

def towerFace (Label : Type u) :
    Face.{0, 0, u} Context :=
  (Functor.const Contextᵒᵖ).obj (Tower Label)

def stateToBehavior
    (coalgebra : Coalgebra.{u, u} Label) :
    stateFace coalgebra ⟶ behaviorFace Label :=
  (Functor.const Contextᵒᵖ).map
    (↾(unfold coalgebra : coalgebra.Carrier → Stream Label))

def behaviorToTower (Label : Type u) :
    behaviorFace Label ⟶ towerFace Label :=
  (Functor.const Contextᵒᵖ).map
    (↾(Tower.ofStream : Stream Label → Tower Label))

def stateToTower
    (coalgebra : Coalgebra.{u, u} Label) :
    stateFace coalgebra ⟶ towerFace Label :=
  (Functor.const Contextᵒᵖ).map
    (↾(Tower.ofStream ∘ unfold coalgebra))

/-- Operational states, final behavior, and coherent finite-view towers form
a commuting comparison without any exactness assumption. -/
def comparison
    (coalgebra : Coalgebra.{u, u} Label) :
    Comparison.{0, 0, u} Context :=
  (FiniteViewComputationalTrinity.comparison
    (unfold coalgebra) (streamObservation Label)).transportSpace
    ((Functor.const Contextᵒᵖ).mapIso (streamTowerEquiv Label).toIso)

/-- Transport recovers all three independently defined stream interpretation maps. -/
theorem comparison_maps_agree (coalgebra : Coalgebra.{u, u} Label) :
    (comparison coalgebra).programToLogic = stateToBehavior coalgebra ∧
      (comparison coalgebra).logicToSpace = behaviorToTower Label ∧
      (comparison coalgebra).programToSpace = stateToTower coalgebra :=
  ⟨rfl, rfl, rfl⟩

/-! ## Exactness property bag -/

/-- Every stream behavior is represented by some operational state. -/
def BehaviorallyComplete
    (coalgebra : Coalgebra.{u, u} Label) : Prop :=
  Function.Surjective (unfold coalgebra)

/-- Operational state identity and stream behavior coincide exactly. -/
def BehaviorallyExact
    (coalgebra : Coalgebra.{u, u} Label) : Prop :=
  Function.Bijective (unfold coalgebra)

theorem behaviorallyExact_iff_faithful_and_complete
    (coalgebra : Coalgebra.{u, u} Label) :
    BehaviorallyExact coalgebra ↔
      BehaviorallyFaithful coalgebra ∧ BehaviorallyComplete coalgebra :=
  Iff.rfl

/-- The behavior-to-tower face is always exact: coherence removes precisely
the spurious raw towers. -/
def behaviorTowerIso (Label : Type u) :
    behaviorFace Label ≅ towerFace Label :=
  (Functor.const Contextᵒᵖ).mapIso (Tower.streamEquiv Label).toIso

@[simp]
theorem behaviorTowerIso_hom (Label : Type u) :
    (behaviorTowerIso Label).hom = behaviorToTower Label :=
  rfl

/-- A compatible operational/behavioral isomorphism is stronger than merely
postulating some isomorphism between the carrier types: its forward map must
be the independently defined final unfolding. -/
structure ExactBehaviorWitness
    (coalgebra : Coalgebra.{u, u} Label) where
  isomorphism : stateFace coalgebra ≅ behaviorFace Label
  agrees : isomorphism.hom = stateToBehavior coalgebra

namespace ExactBehaviorWitness

variable {coalgebra : Coalgebra.{u, u} Label}

theorem behaviorallyExact
    (witness : ExactBehaviorWitness coalgebra) :
    BehaviorallyExact coalgebra :=
  FiniteViewComputationalTrinity.constantIso_bijective (unfold coalgebra)
    witness.isomorphism witness.agrees

/-- A compatible operational/behavioral isomorphism and the canonical
behavior/tower equivalence yield an exact computational trinity. -/
def exactTrinity (witness : ExactBehaviorWitness coalgebra) :
    Exact.{0, 0, u} Context where
  program := stateFace coalgebra
  logic := behaviorFace Label
  space := towerFace Label
  programLogic := witness.isomorphism
  logicSpace := behaviorTowerIso Label

theorem exactTrinity_programLogic_agrees
    (witness : ExactBehaviorWitness coalgebra) :
    witness.exactTrinity.programLogic.hom = stateToBehavior coalgebra :=
  witness.agrees

end ExactBehaviorWitness

/-- A bijective unfolding constructs the compatible exact-behavior witness.
The inverse is selected from the supplied surjectivity proof. -/
noncomputable def exactBehaviorWitnessOfBehaviorallyExact
    (coalgebra : Coalgebra.{u, u} Label)
    (exact : BehaviorallyExact coalgebra) :
    ExactBehaviorWitness coalgebra := by
  let generic := FiniteViewComputationalTrinity.exactTrinityWitnessOfBijective
    (unfold coalgebra) (streamObservation Label) exact (streamObservation_exact Label)
  exact ⟨generic.stateBehavior, generic.stateBehavior_agrees⟩

/-- Exact operational/behavioral compatibility exists exactly when unfolding
is bijective. -/
theorem exactBehaviorWitness_nonempty_iff
    (coalgebra : Coalgebra.{u, u} Label) :
    Nonempty (ExactBehaviorWitness coalgebra) ↔
      BehaviorallyExact coalgebra := by
  constructor
  · rintro ⟨witness⟩
    exact witness.behaviorallyExact
  · intro exact
    exact ⟨exactBehaviorWitnessOfBehaviorallyExact coalgebra exact⟩

/-! ## Information loss is exactly behavioral collision -/

theorem comparison_loses_iff_behavior_collision
    (coalgebra : Coalgebra.{u, u} Label) :
    (comparison coalgebra).LosesProgramInformation ↔
      ∃ left right : coalgebra.Carrier,
        left ≠ right ∧ unfold coalgebra left = unfold coalgebra right := by
  exact (Comparison.transportSpace_loses_iff
    (FiniteViewComputationalTrinity.comparison (unfold coalgebra) (streamObservation Label))
    ((Functor.const Contextᵒᵖ).mapIso (streamTowerEquiv Label).toIso)).trans
      ((FiniteViewComputationalTrinity.comparison_loses_iff_composite_collision
        (unfold coalgebra) (streamObservation Label)).trans
          (by simp only [(streamObservation_exact Label).1.eq_iff]))

theorem faithful_not_loses
    (coalgebra : Coalgebra.{u, u} Label)
    (faithful : BehaviorallyFaithful coalgebra) :
    ¬ (comparison coalgebra).LosesProgramInformation := by
  rw [comparison_loses_iff_behavior_collision]
  rintro ⟨left, right, different, sameBehavior⟩
  exact different (faithful sameBehavior)

/-! ## Independence canaries -/

namespace Canary

/-- Only constant Boolean streams are represented. -/
def constantBoolCoalgebra : Coalgebra Bool where
  Carrier := Bool
  observe := _root_.id
  next := _root_.id

theorem unfold_constantBool (label : Bool) :
    unfold constantBoolCoalgebra label = constant label := by
  funext depth
  induction depth with
  | zero => rfl
  | succ depth inductionHypothesis => exact inductionHypothesis

theorem constantBool_faithful :
    BehaviorallyFaithful constantBoolCoalgebra := by
  change Function.Injective (unfold constantBoolCoalgebra)
  rw [funext unfold_constantBool]
  exact FiniteViewComputationalTrinity.Canary.constantBehavior_injective

theorem constantBool_not_complete :
    ¬ BehaviorallyComplete constantBoolCoalgebra := by
  change ¬ Function.Surjective (unfold constantBoolCoalgebra)
  rw [funext unfold_constantBool]
  exact FiniteViewComputationalTrinity.Canary.constantBehavior_not_surjective

/-- Add an operational tag which final stream behavior deliberately ignores. -/
def taggedStreamCoalgebra : Coalgebra Bool where
  Carrier := Stream Bool × Bool
  observe := fun state => head state.1
  next := fun state => (tail state.1, state.2)

def taggedProjectionHom :
    Hom taggedStreamCoalgebra (streamCoalgebra Bool) where
  toFun := Prod.fst
  observe_preserved := by intro state; rfl
  next_preserved := by intro state; rfl

theorem unfold_taggedStream (state : taggedStreamCoalgebra.Carrier) :
    unfold taggedStreamCoalgebra state = state.1 := by
  exact congrFun (hom_to_stream_eq_unfold taggedStreamCoalgebra taggedProjectionHom).symm state

theorem taggedStream_complete :
    BehaviorallyComplete taggedStreamCoalgebra := by
  change Function.Surjective (unfold taggedStreamCoalgebra)
  rw [funext unfold_taggedStream]
  exact FiniteViewComputationalTrinity.Canary.taggedBehavior_surjective

theorem taggedStream_not_faithful :
    ¬ BehaviorallyFaithful taggedStreamCoalgebra := by
  change ¬ Function.Injective (unfold taggedStreamCoalgebra)
  rw [funext unfold_taggedStream]
  exact FiniteViewComputationalTrinity.Canary.taggedBehavior_not_injective

theorem unfold_streamCoalgebra_eq_id (Label : Type u) :
    unfold (streamCoalgebra Label) = _root_.id := by
  exact
    (hom_to_stream_eq_unfold (streamCoalgebra Label)
      (Hom.id (streamCoalgebra Label))).symm

theorem streamCoalgebra_exact (Label : Type u) :
    BehaviorallyExact (streamCoalgebra Label) := by
  unfold BehaviorallyExact
  rw [unfold_streamCoalgebra_eq_id]
  exact Function.bijective_id

/-- Faithfulness and completeness are independent, while the final stream
coalgebra has both. -/
theorem faithfulness_completeness_independent :
    (BehaviorallyFaithful constantBoolCoalgebra ∧
      ¬ BehaviorallyComplete constantBoolCoalgebra) ∧
    (¬ BehaviorallyFaithful taggedStreamCoalgebra ∧
      BehaviorallyComplete taggedStreamCoalgebra) ∧
    BehaviorallyExact (streamCoalgebra Bool) :=
  ⟨⟨constantBool_faithful, constantBool_not_complete⟩,
    ⟨taggedStream_not_faithful, taggedStream_complete⟩,
    streamCoalgebra_exact Bool⟩

/-- Absence of information loss is weaker than exact trinity: the constant
coalgebra is faithful but does not represent every Boolean stream. -/
theorem faithful_comparison_need_not_be_exact :
    ¬ (comparison constantBoolCoalgebra).LosesProgramInformation ∧
      ¬ BehaviorallyExact constantBoolCoalgebra := by
  refine ⟨faithful_not_loses constantBoolCoalgebra constantBool_faithful, ?_⟩
  intro exact
  exact constantBool_not_complete exact.2

end Canary


end Mettapedia.Coalgebra.ComputationalTrinity
