import Mettapedia.TypeTheory.ContextualCBPVNeed

/-!
# Licensed bubbles: the license is the agreement condition

A licensed bubble applies a requested strategy at a binding site only where the
answers do not change. The default at a call argument is need and the default
at a `let` is value. For a producer choosing among `c ≥ 1` values whose value
the consumer demands `n` times, a site is licensed by a test on `n` and `c`
(`licensed`). The test holds exactly when the requested strategy and the
default give the same multiset of answers (`licensed_iff`).

The cases are the three agreement lines of the handlers:
* value against need (`value_need_agree_iff`): demanded at least once, or one value;
* need against name (`need_name_agree_iff`): demanded at most once, or one value;
* value against name (`value_name_agree_iff`, new here): demanded exactly once, or
  one value.

The test is exact for every consumer that demands the value `n` times and then
computes any function of the values it received (`licensed_iff_map`): where the
test holds the answers agree, and where it fails even their numbers differ.

A coin demanded twice is the negative example of the last line: value gives two
pairs and name four (`coin_twice_value_name`). Demanded once, the two agree
(`coin_once_value_name`).

The elaborator of the draft library `lib/prime/cbpv.metta` decides each site
of a licensed bubble by this test (`cbpv:agree`).
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.ContextualCBPV

open Mettapedia.GSLT.Dynamics.ContextualEffectHandlers

namespace Demand.Profiles

open Demand

variable {Value : Type}

theorem tuples_one (values : List Value) :
    tuples 1 values = values.map fun value => [value] := by
  simp only [tuples, List.map_cons, List.map_nil]
  exact flatMap_singleton_eq_map values fun value => [value]

theorem tuples_single (first : Value) (count : Nat) :
    tuples count [first] = [List.replicate count first] := by
  induction count with
  | zero => rfl
  | succ count ih => simp [tuples, ih, List.replicate_succ]

/-- **Value and name agree exactly when the producer is demanded once or has
one value.** -/
theorem value_name_agree_iff (first : Value) (rest : List Value) (count : Nat) :
    ((answersOf (eager (choice first rest) (uses count [])) : Multiset (List Value)) =
        answersOf (resample (choice first rest) (uses count []))) ↔
      (count = 1 ∨ rest = []) := by
  rw [answersOf_eager_uses, answersOf_resample_uses]
  simp only [List.reverse_nil, List.nil_append, List.map_id']
  constructor
  · intro equal
    have cards := congrArg Multiset.card equal
    simp only [Multiset.coe_card, List.length_map, tuples_length] at cards
    by_contra neither
    have notOne : count ≠ 1 := fun one => neither (Or.inl one)
    have nonempty : rest ≠ [] := fun empty => neither (Or.inr empty)
    have two : 2 ≤ (first :: rest).length := by
      cases rest with
      | nil => exact absurd rfl nonempty
      | cons _ _ => simp
    rcases count with _ | _ | count
    · rw [pow_zero] at cards
      omega
    · exact notOne rfl
    · have grow : (first :: rest).length < (first :: rest).length ^ (count + 1 + 1) := by
        calc (first :: rest).length = (first :: rest).length ^ 1 := (pow_one _).symm
          _ < (first :: rest).length ^ (count + 1 + 1) :=
            Nat.pow_lt_pow_right (by omega) (by omega)
      omega
  · rintro (rfl | rfl)
    · rw [tuples_one]
      rfl
    · rw [tuples_single]
      rfl

end Demand.Profiles

namespace Demand

section MapAnswer

variable {State Value Answer Other Intent : Type}

/-- Apply a function to every answer of a consumer. -/
def mapAnswer (function : Answer → Other) :
    Demand State Value Answer Intent → Demand State Value Other Intent
  | .pure answer => .pure (function answer)
  | .choose left right => .choose (mapAnswer function left) (mapAnswer function right)
  | .read next => .read fun state => mapAnswer function (next state)
  | .write state next => .write state (mapAnswer function next)
  | .intent request next => .intent request (mapAnswer function next)
  | .demand next => .demand fun value => mapAnswer function (next value)

theorem fill_mapAnswer (function : Answer → Other) (value : Value)
    (consumer : Demand State Value Answer Intent) :
    fill value (consumer.mapAnswer function) = (fill value consumer).map function := by
  induction consumer with
  | pure answer => rfl
  | choose left right leftIH rightIH =>
      simp only [mapAnswer, fill, leftIH, rightIH]
      rfl
  | read next ih =>
      simp only [mapAnswer, fill, ih]
      rfl
  | write state next ih =>
      simp only [mapAnswer, fill, ih]
      rfl
  | intent request next ih =>
      simp only [mapAnswer, fill, ih]
      rfl
  | demand next ih => simp only [mapAnswer, fill, ih]

variable (producer : Program State Value Intent)

theorem share_mapAnswer (function : Answer → Other)
    (consumer : Demand State Value Answer Intent) :
    share producer (consumer.mapAnswer function) = (share producer consumer).map function := by
  induction consumer with
  | pure answer => rfl
  | choose left right leftIH rightIH =>
      simp only [mapAnswer, share, leftIH, rightIH]
      rfl
  | read next ih =>
      simp only [mapAnswer, share, ih]
      rfl
  | write state next ih =>
      simp only [mapAnswer, share, ih]
      rfl
  | intent request next ih =>
      simp only [mapAnswer, share, ih]
      rfl
  | demand next _ =>
      simp only [mapAnswer, share, fill_mapAnswer]
      unfold Program.map
      rw [ContextualComputationKleisli.Program.bind_assoc]

theorem resample_mapAnswer (function : Answer → Other)
    (consumer : Demand State Value Answer Intent) :
    resample producer (consumer.mapAnswer function) = (resample producer consumer).map function := by
  induction consumer with
  | pure answer => rfl
  | choose left right leftIH rightIH =>
      simp only [mapAnswer, resample, leftIH, rightIH]
      rfl
  | read next ih =>
      simp only [mapAnswer, resample, ih]
      rfl
  | write state next ih =>
      simp only [mapAnswer, resample, ih]
      rfl
  | intent request next ih =>
      simp only [mapAnswer, resample, ih]
      rfl
  | demand next ih =>
      simp only [mapAnswer, resample, ih]
      unfold Program.map
      rw [ContextualComputationKleisli.Program.bind_assoc]

theorem eager_mapAnswer (function : Answer → Other)
    (consumer : Demand State Value Answer Intent) :
    eager producer (consumer.mapAnswer function) = (eager producer consumer).map function := by
  unfold eager
  simp only [fill_mapAnswer]
  unfold Program.map
  rw [ContextualComputationKleisli.Program.bind_assoc]

end MapAnswer

end Demand

namespace Demand.Profiles

theorem answersOf_map {Answer Other : Type} (program : Program Unit Answer Unit)
    (function : Answer → Other) :
    answersOf (program.map function) = (answersOf program).map function := by
  unfold Program.map
  rw [answersOf_bind]
  exact flatMap_singleton_eq_map _ _

end Demand.Profiles

namespace Demand.License

open Demand Demand.Profiles

variable {Value : Type}

/-- How a binding site binds its producer. -/
inductive Strategy where
  | value
  | need
  | name
  deriving DecidableEq

/-- The binding of a producer to a consumer by a strategy. -/
def Strategy.bind {Answer : Type} :
    Strategy → Program Unit Value Unit → Demand Unit Value Answer Unit →
      Program Unit Answer Unit
  | .value, producer, consumer => eager producer consumer
  | .need, producer, consumer => share producer consumer
  | .name, producer, consumer => resample producer consumer

/-- The default a requested strategy is compared with: need at a call argument
(for a requested value), value at a `let` (for a requested need or name). -/
def Strategy.default : Strategy → Strategy
  | .value => .need
  | .need => .value
  | .name => .value

/-- The license test on the uses `n` of the bound value and the number `c` of
its producer's values. -/
def licensed : Strategy → Nat → Nat → Bool
  | .value, n, c => decide (1 ≤ n) || decide (c = 1)
  | .need, n, c => decide (1 ≤ n) || decide (c = 1)
  | .name, n, c => (decide (1 ≤ n) || decide (c = 1)) && (decide (n ≤ 1) || decide (c ≤ 1))

/-- **The license holds exactly when the requested strategy and the default
give the same answers**, for a producer choosing among `first :: rest` and a
consumer demanding its value `count` times. -/
theorem licensed_iff (strategy : Strategy) (first : Value) (rest : List Value) (count : Nat) :
    licensed strategy count (rest.length + 1) = true ↔
      ((answersOf (strategy.bind (choice first rest) (uses count [])) : Multiset (List Value)) =
        answersOf (strategy.default.bind (choice first rest) (uses count []))) := by
  have single : rest.length + 1 = 1 ↔ rest = [] := by
    simp [List.length_eq_zero_iff]
  cases strategy with
  | value =>
      simp only [licensed, Strategy.bind, Strategy.default, Bool.or_eq_true, decide_eq_true_eq]
      rw [value_need_agree_iff, single]
  | need =>
      simp only [licensed, Strategy.bind, Strategy.default, Bool.or_eq_true, decide_eq_true_eq]
      rw [single, @eq_comm (Multiset (List Value)), value_need_agree_iff]
  | name =>
      simp only [licensed, Strategy.bind, Strategy.default, Bool.and_eq_true, Bool.or_eq_true,
        decide_eq_true_eq]
      rw [@eq_comm (Multiset (List Value)), value_name_agree_iff]
      have atMost : rest.length + 1 ≤ 1 ↔ rest = [] := by
        simp [List.length_eq_zero_iff]
      rw [single, atMost]
      by_cases empty : rest = []
      · simp [empty]
      · simp only [empty, or_false]
        omega

theorem Strategy.bind_mapAnswer {Answer Other : Type} (strategy : Strategy)
    (producer : Program Unit Value Unit) (function : Answer → Other)
    (consumer : Demand Unit Value Answer Unit) :
    strategy.bind producer (consumer.mapAnswer function) =
      (strategy.bind producer consumer).map function := by
  cases strategy
  · exact eager_mapAnswer producer function consumer
  · exact share_mapAnswer producer function consumer
  · exact resample_mapAnswer producer function consumer

/-- Where the test fails, the two strategies give different numbers of answers. -/
theorem length_ne_of_not_licensed (strategy : Strategy) (first : Value) (rest : List Value)
    (count : Nat) (failed : licensed strategy count (rest.length + 1) = false) :
    (answersOf (strategy.bind (choice first rest) (uses count []))).length ≠
      (answersOf (strategy.default.bind (choice first rest) (uses count []))).length := by
  have eagerLength : (answersOf (eager (choice first rest) (uses count []))).length =
      rest.length + 1 := by
    rw [answersOf_eager_uses]
    simp
  have shareLength : (answersOf (share (choice first rest) (uses count []))).length =
      if count = 0 then 1 else rest.length + 1 := by
    rcases count with _ | count
    · rfl
    · rw [answersOf_share_uses_succ]
      simp
  have resampleLength : (answersOf (resample (choice first rest) (uses count []))).length =
      (rest.length + 1) ^ count := by
    rw [answersOf_resample_uses]
    simp [tuples_length]
  cases strategy with
  | value =>
      simp only [licensed, Bool.or_eq_false_iff, decide_eq_false_iff_not] at failed
      simp only [Strategy.bind, Strategy.default, eagerLength, shareLength]
      split <;> omega
  | need =>
      simp only [licensed, Bool.or_eq_false_iff, decide_eq_false_iff_not] at failed
      simp only [Strategy.bind, Strategy.default, eagerLength, shareLength]
      split <;> omega
  | name =>
      simp only [licensed, Bool.and_eq_false_iff, Bool.or_eq_false_iff,
        decide_eq_false_iff_not] at failed
      simp only [Strategy.bind, Strategy.default, eagerLength, resampleLength]
      intro equal
      rcases count with _ | _ | count
      · rw [pow_zero] at equal
        omega
      · omega
      · have grow : rest.length + 1 < (rest.length + 1) ^ (count + 1 + 1) := by
          calc rest.length + 1 = (rest.length + 1) ^ 1 := (pow_one _).symm
            _ < (rest.length + 1) ^ (count + 1 + 1) :=
              Nat.pow_lt_pow_right (by omega) (by omega)
        omega

/-- **The license is exact for every consumer that demands the value `count`
times and computes a function of the values.** -/
theorem licensed_iff_map {Other : Type} (strategy : Strategy) (first : Value) (rest : List Value)
    (count : Nat) (function : List Value → Other) :
    licensed strategy count (rest.length + 1) = true ↔
      ((answersOf (strategy.bind (choice first rest) ((uses count []).mapAnswer function)) :
          Multiset Other) =
        answersOf (strategy.default.bind (choice first rest) ((uses count []).mapAnswer function))) := by
  rw [Strategy.bind_mapAnswer, Strategy.bind_mapAnswer, answersOf_map, answersOf_map]
  constructor
  · intro holds
    have agree := (licensed_iff strategy first rest count).mp holds
    have mapped := congrArg (Multiset.map function) agree
    simpa only [Multiset.map_coe] using mapped
  · intro agree
    by_contra notHolds
    have failed : licensed strategy count (rest.length + 1) = false := by
      simpa using notHolds
    have cards := congrArg Multiset.card agree
    simp only [Multiset.coe_card, List.length_map] at cards
    exact length_ne_of_not_licensed strategy first rest count failed cards

/-! ## Controls -/

/-- A coin, demanded twice: value gives two pairs and name four. -/
theorem coin_twice_value_name :
    (answersOf (Strategy.value.bind (choice false [true]) (uses 2 []))).length = 2 ∧
      (answersOf (Strategy.name.bind (choice false [true]) (uses 2 []))).length = 4 := by
  constructor <;> rfl

/-- A coin demanded twice is not licensed for name at a `let`. -/
theorem coin_twice_not_licensed : licensed .name 2 2 = false := rfl

/-- Demanded once, value and name agree, and the license holds. -/
theorem coin_once_value_name :
    ((answersOf (Strategy.name.bind (choice false [true]) (uses 1 [])) : Multiset (List Bool)) =
      answersOf (Strategy.value.bind (choice false [true]) (uses 1 []))) ∧
      licensed .name 1 2 = true :=
  ⟨(licensed_iff .name false [true] 1).mp rfl, rfl⟩

/-- An unused coin is licensed neither for need at a `let` nor for value at an
argument, and a single value is licensed everywhere. -/
theorem coin_unused_not_licensed :
    licensed .need 0 2 = false ∧ licensed .value 0 2 = false ∧
      licensed .need 0 1 = true ∧ licensed .name 3 1 = true :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- A coin bound by `let` and used twice: resample is not licensed there, and
whatever the body builds from the two uses, the answers differ. -/
theorem coin_used_twice_any_body {Other : Type} (body : List Bool → Other) :
    (answersOf (Strategy.name.bind (choice false [true]) ((uses 2 []).mapAnswer body)) :
        Multiset Other) ≠
      answersOf (Strategy.value.bind (choice false [true]) ((uses 2 []).mapAnswer body)) := by
  intro agree
  have holds := (licensed_iff_map .name false [true] 2 body).mpr agree
  exact absurd holds (by decide)

/-- Used once, resample is licensed, and the answers agree for every body. -/
theorem coin_used_once_any_body {Other : Type} (body : List Bool → Other) :
    (answersOf (Strategy.name.bind (choice false [true]) ((uses 1 []).mapAnswer body)) :
        Multiset Other) =
      answersOf (Strategy.value.bind (choice false [true]) ((uses 1 []).mapAnswer body)) :=
  (licensed_iff_map .name false [true] 1 body).mp rfl

end Demand.License

#print axioms Demand.Profiles.value_name_agree_iff
#print axioms Demand.License.licensed_iff
#print axioms Demand.License.coin_once_value_name
#print axioms Demand.License.licensed_iff_map

end Mettapedia.TypeTheory.ContextualCBPV
