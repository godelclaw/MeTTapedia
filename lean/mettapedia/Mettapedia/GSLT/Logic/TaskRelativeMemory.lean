import Mettapedia.GSLT.Logic.PrivilegedView
import Mettapedia.GSLT.Core.PolicyFamilySufficiency
import Mathlib.Data.Setoid.Basic
import Mathlib.SetTheory.Cardinal.Finite

/-!
# Memory relative to future observations

Tests consist of an allowed input word followed by a declared observation.
Their answer vector is the existing word behaviour. Its quotient retains
exactly the distinctions needed for those tests, and every sufficient memory
determines that quotient. The recovering map is unique on used memory values;
unused values need no arbitrary interpretation.

Answer sufficiency and recursive implementation are separate: a supplied
memory update must commute with the source update. The canonical quotient has
such an update because the tests include every continuation. An arbitrary
restricted test family need not have this closure property.

The generic predictive quotient is classical Myhill--Nerode theory; see also
Qinyou Wang, *Fiber Fingerprints of Hidden Learning-State Dynamics* (2026),
https://arxiv.org/abs/2608.15976. The applications to evidence and future task
intersections are developed separately.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.TaskRelativeMemory

open Mettapedia.GSLT.Core
open Mettapedia.GSLT.Core.NonFactorization
open Mettapedia.GSLT.PrivilegedView

universe u v w z m

variable {State : Type u} {Input : Type v} {Query : Type w} {Result : Query → Type z}

/-- All finite continuations, followed by one of the requested observations. -/
def futureFamily (step : State → Input → State) (observe : (q : Query) → State → Result q) :
    PolicyFamily State where
  Policy := List Input × Query
  Result test := Result test.2
  decide test state := observe test.2 (test.1.foldl step state)

/-- The existing word behaviour, with a vector of current observations. -/
abbrev profile (step : State → Input → State) (observe : (q : Query) → State → Result q) :=
  wordBehaviour step (fun state q => observe q state)

variable (step : State → Input → State) (observe : (q : Query) → State → Result q)

theorem profile_eq_iff (first second : State) :
    profile step observe first = profile step observe second ↔
      (futureFamily step observe).PolicyEquivalent first second := by
  constructor
  · intro same test
    exact congrFun (congrFun same test.1) test.2
  · intro same
    funext word q
    exact same (word, q)

theorem supports_iff_constant [Nonempty State] {Memory : Type m} (memory : State → Memory) :
    (futureFamily step observe).SupportsReadout memory ↔
      ConstantOnFibers memory (profile step observe) := by
  rw [PolicyFamily.supportsReadout_iff_compatible]
  exact forall_congr' fun first => forall_congr' fun second =>
    forall_congr' fun _ => (profile_eq_iff step observe first second).symm

/-- The Nerode quotient for the declared input and observation types. -/
abbrev MemoryQuotient := Quotient (Setoid.ker (profile step observe))

def classify : State → MemoryQuotient step observe := Quotient.mk _

@[simp] theorem classify_eq_iff (first second : State) :
    classify step observe first = classify step observe second ↔
      profile step observe first = profile step observe second := Quotient.eq

/-- Equality of future profiles is preserved by every allowed input. -/
theorem profile_step {first second : State}
    (same : profile step observe first = profile step observe second) (input : Input) :
    profile step observe (step first input) = profile step observe (step second input) :=
  stableUnder_wordBehaviour first second same input

/-- The memory quotient is the existing word-context relative equivalence. -/
theorem classify_eq_iff_relative (first second : State) :
    classify step observe first = classify step observe second ↔
      (⊤ : AdmissibleContextCongruence.AdmissibleClass (wordRules step)).RelEquiv
        (evaluationObservations (fun state q => observe q state)) first second := by
  rw [classify_eq_iff]
  exact (relEquiv_iff_wordBehaviour_eq step (fun state q => observe q state)).symm

def quotientStep (state : MemoryQuotient step observe) (input : Input) :
    MemoryQuotient step observe :=
  Quotient.map (fun source => step source input)
    (fun _ _ same => profile_step step observe same input) state

def quotientObserve (q : Query) : MemoryQuotient step observe → Result q :=
  Quotient.lift (observe q) (fun _ _ same => congrFun (congrFun same []) q)

@[simp] theorem quotientStep_classify (state : State) (input : Input) :
    quotientStep step observe (classify step observe state) input =
      classify step observe (step state input) := rfl

@[simp] theorem quotientObserve_classify (q : Query) (state : State) :
    quotientObserve step observe q (classify step observe state) = observe q state := rfl

theorem classify_supports : (futureFamily step observe).SupportsReadout (classify step observe) := by
  refine ⟨⟨fun test => Quotient.lift
    (fun state => observe test.2 (test.1.foldl step state)) ?_, fun _ _ => rfl⟩⟩
  intro first second same
  exact congrFun (congrFun same test.1) test.2

/-- Canonical recovery of the minimal state from a represented memory value. -/
noncomputable def decodeUsed {Memory : Type m} (memory : State → Memory)
    (_sufficient : ConstantOnFibers memory (profile step observe)) :
    Set.range memory → MemoryQuotient step observe :=
  fun value => classify step observe value.property.choose

theorem decodeUsed_memory {Memory : Type m} (memory : State → Memory)
    (sufficient : ConstantOnFibers memory (profile step observe)) (state : State) :
    decodeUsed step observe memory sufficient ⟨memory state, state, rfl⟩ =
      classify step observe state := by
  apply Quotient.sound
  exact sufficient _ state (Exists.choose_spec (show ∃ source, memory source = memory state from
    ⟨state, rfl⟩))

theorem decodeUsed_unique {Memory : Type m} (memory : State → Memory)
    (sufficient : ConstantOnFibers memory (profile step observe))
    (decode : Set.range memory → MemoryQuotient step observe)
    (agrees : ∀ state, decode ⟨memory state, state, rfl⟩ = classify step observe state) :
    decode = decodeUsed step observe memory sufficient := by
  funext value
  obtain ⟨value, state, rfl⟩ := value
  exact (agrees state).trans (decodeUsed_memory step observe memory sufficient state).symm

theorem decodeUsed_surjective {Memory : Type m} (memory : State → Memory)
    (sufficient : ConstantOnFibers memory (profile step observe)) :
    Function.Surjective (decodeUsed step observe memory sufficient) := by
  intro value
  induction value using Quotient.ind with
  | _ state => exact ⟨⟨memory state, state, rfl⟩, decodeUsed_memory step observe memory sufficient state⟩

/-- Minimality counts used memory values, not arbitrary unused codes. -/
theorem quotient_card_le_used {Memory : Type m} (memory : State → Memory)
    [Finite (Set.range memory)]
    (sufficient : ConstantOnFibers memory (profile step observe)) :
    Nat.card (MemoryQuotient step observe) ≤ Nat.card (Set.range memory) :=
  Nat.card_le_card_of_surjective _ (decodeUsed_surjective step observe memory sufficient)

/-- The quotient and the realized answer profiles are equivalent presentations. -/
noncomputable def quotientEquivProfiles :
    MemoryQuotient step observe ≃ Set.range (profile step observe) :=
  Setoid.quotientKerEquivRange _

/-- A recursively implemented memory retains its update and observation laws. -/
structure Realization {Memory : Type m} (memory : State → Memory) where
  update : Memory → Input → Memory
  read : (q : Query) → Memory → Result q
  update_agrees : ∀ state input, update (memory state) input = memory (step state input)
  read_agrees : ∀ q state, read q (memory state) = observe q state

theorem Realization.foldl_agrees {Memory : Type m} {memory : State → Memory}
    (realization : Realization step observe memory) (word : List Input) (state : State) :
    word.foldl realization.update (memory state) = memory (word.foldl step state) := by
  induction word generalizing state with
  | nil => rfl
  | cons input word ih =>
    simpa only [List.foldl_cons, realization.update_agrees] using ih (step state input)

def Realization.futureRealization {Memory : Type m} {memory : State → Memory}
    (realization : Realization step observe memory) :
    (futureFamily step observe).ReadoutRealization memory where
  run test value := realization.read test.2 (test.1.foldl realization.update value)
  agrees test state := by
    rw [realization.foldl_agrees, realization.read_agrees]
    rfl

/-- Removing terminal queries cannot require more memory. -/
theorem profile_reindex {Requested : Type*} (select : Requested → Query)
    {first second : State} (same : profile step observe first = profile step observe second) :
    profile step (fun q => observe (select q)) first =
      profile step (fun q => observe (select q)) second := by
  funext word q
  exact congrFun (congrFun same word) (select q)

end Mettapedia.GSLT.TaskRelativeMemory
