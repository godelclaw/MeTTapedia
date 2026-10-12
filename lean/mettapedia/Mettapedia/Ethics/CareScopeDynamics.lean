import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Logic.Relation
import Mathlib.Order.Closure
import Mathlib.Order.Monotone.Basic
import Mettapedia.Ethics.RecipientCenteredCare

/-!
# Development of care scopes by relational expansion

The state of this dynamics is a set of persons.  One round retains the
current scope and includes every person connected from a current member by
an admitted propagation relation.  The relation and this update policy are
explicit hypotheses about development; they are not consequences of
intelligence, intention coherence, or intrinsic concern.

The eventual scope is exactly relational reachability from the seed.  This
construction is exposed as Mathlib's `ClosureOperator`, rather than a new
closure framework.  Every finite instance stabilizes.  Connected instances
spread any nonempty scope to everyone; a genuinely linked but disconnected
instance has a proper nonempty absorbing scope.

These are a conditional steelman and a dynamic countermodel for a two-polarity
developmental hypothesis.  They do not prove that moral development has this
update rule, or that only universal and self-exclusive concern can persist.
Care intensity, motives and recipient wellbeing require additional structure.
Finite-set scopes can enter this interface by the ordinary coercion to sets.

Reference: Garden of Minds, "Good and Evil".
-/

set_option autoImplicit false

namespace Mettapedia.Ethics.CareScopeDynamics

universe u

section General

variable {Person : Type u}

/-- One development round retains the current scope and adds all admitted
out-neighbors of its members.  It does not silently shrink a recipient's
agency or identify scope membership with wellbeing. -/
def round (propagatesCare : Person -> Person -> Prop) (scope : Set Person) :
    Set Person :=
  scope ∪ {recipient | exists source, source ∈ scope /\ propagatesCare source recipient}

/-- The actual iterated update, retaining its round count. -/
def evolve (propagatesCare : Person -> Person -> Prop) (seed : Set Person) :
    Nat -> Set Person
  | 0 => seed
  | n + 1 => round propagatesCare (evolve propagatesCare seed n)

/-- Relational closure of a scope, constructed from finite propagation paths. -/
def reachabilityClosure (propagatesCare : Person -> Person -> Prop)
    (seed : Set Person) : Set Person :=
  {recipient | exists source, source ∈ seed /\
    Relation.ReflTransGen propagatesCare source recipient}

theorem round_extensive (propagatesCare : Person -> Person -> Prop)
    (scope : Set Person) : scope ⊆ round propagatesCare scope :=
  fun _ member => Or.inl member

theorem round_monotone (propagatesCare : Person -> Person -> Prop) :
    Monotone (round propagatesCare) := by
  intro first second includes recipient member
  rcases member with already | ⟨source, member, propagation⟩
  · exact Or.inl (includes already)
  · exact Or.inr ⟨source, includes member, propagation⟩

theorem round_monotone_relation {first second : Person -> Person -> Prop}
    (includes : forall source recipient, first source recipient ->
      second source recipient) (scope : Set Person) :
    round first scope ⊆ round second scope := by
  intro recipient member
  rcases member with already | ⟨source, member, propagation⟩
  · exact Or.inl already
  · exact Or.inr ⟨source, member, includes source recipient propagation⟩

theorem evolve_monotone_time (propagatesCare : Person -> Person -> Prop)
    (seed : Set Person) : Monotone (evolve propagatesCare seed) :=
  monotone_nat_of_le_succ fun n =>
    round_extensive propagatesCare (evolve propagatesCare seed n)

theorem seed_subset_evolve (propagatesCare : Person -> Person -> Prop)
    (seed : Set Person) (n : Nat) : seed ⊆ evolve propagatesCare seed n :=
  evolve_monotone_time propagatesCare seed (Nat.zero_le n)

theorem evolve_monotone_seed (propagatesCare : Person -> Person -> Prop)
    (n : Nat) : Monotone (fun seed => evolve propagatesCare seed n) := by
  induction n with
  | zero => exact fun _ _ includes => includes
  | succ n inductionHypothesis =>
      intro first second includes
      exact round_monotone propagatesCare (inductionHypothesis includes)

theorem closure_extensive (propagatesCare : Person -> Person -> Prop)
    (seed : Set Person) : seed ⊆ reachabilityClosure propagatesCare seed :=
  fun person member => ⟨person, member, .refl⟩

theorem closure_monotone (propagatesCare : Person -> Person -> Prop) :
    Monotone (reachabilityClosure propagatesCare) := by
  intro first second includes recipient member
  rcases member with ⟨source, member, path⟩
  exact ⟨source, includes member, path⟩

/-- Closure retains every newly admitted out-neighbor. -/
theorem closure_propagates (propagatesCare : Person -> Person -> Prop)
    (seed : Set Person) {source recipient : Person}
    (member : source ∈ reachabilityClosure propagatesCare seed)
    (propagation : propagatesCare source recipient) :
    recipient ∈ reachabilityClosure propagatesCare seed := by
  rcases member with ⟨origin, originMember, path⟩
  exact ⟨origin, originMember, path.tail propagation⟩

theorem closure_idempotent (propagatesCare : Person -> Person -> Prop)
    (seed : Set Person) :
    reachabilityClosure propagatesCare (reachabilityClosure propagatesCare seed) =
      reachabilityClosure propagatesCare seed := by
  apply Set.Subset.antisymm
  · rintro recipient ⟨middle, ⟨origin, member, firstPath⟩, secondPath⟩
    exact ⟨origin, member, firstPath.trans secondPath⟩
  · exact closure_extensive propagatesCare (reachabilityClosure propagatesCare seed)

/-- The particular relational construction supplies the standard three
closure laws.  Its implementation is reachability, not the identity map. -/
def closureOperator (propagatesCare : Person -> Person -> Prop) :
    ClosureOperator (Set Person) where
  toFun := reachabilityClosure propagatesCare
  monotone' := closure_monotone propagatesCare
  le_closure' := closure_extensive propagatesCare
  idempotent' := closure_idempotent propagatesCare

/-- Every actual finite round has its reachability justification. -/
theorem evolve_subset_closure (propagatesCare : Person -> Person -> Prop)
    (seed : Set Person) (n : Nat) :
    evolve propagatesCare seed n ⊆ reachabilityClosure propagatesCare seed := by
  induction n with
  | zero => exact closure_extensive propagatesCare seed
  | succ n inductionHypothesis =>
      intro recipient member
      rcases member with already | ⟨source, member, propagation⟩
      · exact inductionHypothesis already
      · exact closure_propagates propagatesCare seed
          (inductionHypothesis member) propagation

/-- Every reachable person enters the actual dynamics at a finite round. -/
theorem reachable_eventually_enters (propagatesCare : Person -> Person -> Prop)
    (seed : Set Person) {origin recipient : Person}
    (member : origin ∈ seed)
    (path : Relation.ReflTransGen propagatesCare origin recipient) :
    exists n, recipient ∈ evolve propagatesCare seed n := by
  induction path with
  | refl => exact ⟨0, member⟩
  | @tail middle target _ propagation inductionHypothesis =>
      rcases inductionHypothesis with ⟨n, enters⟩
      exact ⟨n + 1, Or.inr ⟨middle, enters, propagation⟩⟩

/-- Iteration and reachability agree extensionally; the reverse implication
constructs a finite round from the path rather than assuming convergence. -/
theorem eventually_enters_iff_reachable
    (propagatesCare : Person -> Person -> Prop) (seed : Set Person)
    (recipient : Person) :
    (exists n, recipient ∈ evolve propagatesCare seed n) ↔
      recipient ∈ reachabilityClosure propagatesCare seed := by
  constructor
  · rintro ⟨n, member⟩
    exact evolve_subset_closure propagatesCare seed n member
  · rintro ⟨origin, member, path⟩
    exact reachable_eventually_enters propagatesCare seed member path

/-- A one-round absorbing scope already contains every person reachable from
it.  No fixed-point hypothesis about the whole future is needed. -/
theorem closure_subset_of_round_fixed
    (propagatesCare : Person -> Person -> Prop) (scope : Set Person)
    (fixed : round propagatesCare scope = scope) :
    reachabilityClosure propagatesCare scope ⊆ scope := by
  rintro recipient ⟨origin, member, path⟩
  induction path with
  | refl => exact member
  | @tail middle target _ propagation inductionHypothesis =>
      rw [← fixed]
      exact Or.inr ⟨middle, inductionHypothesis, propagation⟩

theorem round_fixed_iff_closed (propagatesCare : Person -> Person -> Prop)
    (scope : Set Person) :
    round propagatesCare scope = scope ↔
      (closureOperator propagatesCare).IsClosed scope := by
  change round propagatesCare scope = scope ↔
    reachabilityClosure propagatesCare scope = scope
  constructor
  · intro fixed
    exact Set.Subset.antisymm
      (closure_subset_of_round_fixed propagatesCare scope fixed)
      (closure_extensive propagatesCare scope)
  · intro closed
    apply Set.Subset.antisymm
    · intro recipient member
      have reachable : recipient ∈ reachabilityClosure propagatesCare scope :=
        evolve_subset_closure propagatesCare scope 1 member
      rw [closed] at reachable
      exact reachable
    · exact round_extensive propagatesCare scope

/-- Once an actual round is absorbing, iteration retains the same scope. -/
theorem evolve_of_round_fixed (propagatesCare : Person -> Person -> Prop)
    (scope : Set Person) (fixed : round propagatesCare scope = scope) (n : Nat) :
    evolve propagatesCare scope n = scope := by
  induction n with
  | zero => rfl
  | succ n inductionHypothesis =>
      change round propagatesCare (evolve propagatesCare scope n) = scope
      rw [inductionHypothesis, fixed]

/-- The dynamics reaches its least closed extension on a finite person type.
The proof gathers the finitely many individually constructed entry rounds. -/
theorem finite_reaches_closure [Finite Person]
    (propagatesCare : Person -> Person -> Prop) (seed : Set Person) :
    exists n, evolve propagatesCare seed n = reachabilityClosure propagatesCare seed := by
  classical
  let _ := Fintype.ofFinite Person
  have collect : forall persons : Finset Person, exists n,
      ∀ person ∈ persons, person ∈ reachabilityClosure propagatesCare seed ->
        person ∈ evolve propagatesCare seed n := by
    intro persons
    induction persons using Finset.induction_on with
    | empty => exact ⟨0, by simp⟩
    | @insert person persons _ inductionHypothesis =>
        rcases inductionHypothesis with ⟨n, entered⟩
        by_cases reachable : person ∈ reachabilityClosure propagatesCare seed
        · rcases (eventually_enters_iff_reachable propagatesCare seed person).2
            reachable with ⟨m, member⟩
          refine ⟨max n m, ?_⟩
          intro recipient inInsert recipientReachable
          rcases Finset.mem_insert.mp inInsert with equal | inPersons
          · subst recipient
            exact evolve_monotone_time propagatesCare seed (Nat.le_max_right n m) member
          · exact evolve_monotone_time propagatesCare seed (Nat.le_max_left n m)
              (entered recipient inPersons recipientReachable)
        · refine ⟨n, ?_⟩
          intro recipient inInsert recipientReachable
          rcases Finset.mem_insert.mp inInsert with equal | inPersons
          · subst recipient
            exact False.elim (reachable recipientReachable)
          · exact entered recipient inPersons recipientReachable
  rcases collect Finset.univ with ⟨n, entered⟩
  refine ⟨n, Set.Subset.antisymm (evolve_subset_closure propagatesCare seed n) ?_⟩
  intro person member
  exact entered person (Finset.mem_univ person) member

/-- Every subsequent round agrees with the attained closure. -/
theorem finite_stabilization [Finite Person]
    (propagatesCare : Person -> Person -> Prop) (seed : Set Person) :
    exists n, forall later, n ≤ later ->
      evolve propagatesCare seed later = reachabilityClosure propagatesCare seed := by
  rcases finite_reaches_closure propagatesCare seed with ⟨n, attained⟩
  refine ⟨n, ?_⟩
  intro later follows
  apply Set.Subset.antisymm (evolve_subset_closure propagatesCare seed later)
  rw [← attained]
  exact evolve_monotone_time propagatesCare seed follows

/-- Connectivity is a property of the admitted relation, independent of the
chosen care seed or of any claim about intrinsic concern. -/
def Connected (propagatesCare : Person -> Person -> Prop) : Prop :=
  forall first second, Relation.ReflTransGen propagatesCare first second

theorem connected_closure_eq_univ (propagatesCare : Person -> Person -> Prop)
    (connected : Connected propagatesCare) (seed : Set Person)
    (nonempty : seed.Nonempty) : reachabilityClosure propagatesCare seed = Set.univ := by
  apply Set.eq_univ_of_forall
  intro recipient
  rcases nonempty with ⟨origin, member⟩
  exact ⟨origin, member, connected origin recipient⟩

/-- Universal scope follows from genuine relational connectivity plus the
declared expansion policy.  Neither premise is inferred from intelligence. -/
theorem connected_eventually_universal [Finite Person]
    (propagatesCare : Person -> Person -> Prop)
    (connected : Connected propagatesCare) (seed : Set Person)
    (nonempty : seed.Nonempty) :
    exists n, forall later, n ≤ later -> evolve propagatesCare seed later = Set.univ := by
  rcases finite_stabilization propagatesCare seed with ⟨n, stabilizes⟩
  refine ⟨n, ?_⟩
  intro later follows
  exact (stabilizes later follows).trans
    (connected_closure_eq_univ propagatesCare connected seed nonempty)

end General

/-! ## Actual development and an intermediate absorbing scope -/

namespace Controls

open RecipientCenteredCare.Controls (Person)
open Mettapedia.Cybernetics.IntentionCoherence

instance : Fintype Person where
  elems := {.self, .ally, .outsider}
  complete person := by cases person <;> simp

/-- Reciprocal care propagation inside one group; no links to the outsider. -/
def groupRelation (first second : Person) : Prop :=
  (first = .self /\ second = .ally) ∨
  (first = .ally /\ second = .self)

def initialScope : Set Person := (RecipientCenteredCare.Controls.selfishScope : Set Person)

def intermediateScope : Set Person :=
  (RecipientCenteredCare.Controls.intermediateScope : Set Person)

@[simp]
theorem mem_initialScope (person : Person) : person ∈ initialScope ↔ person = .self := by
  simp [initialScope, RecipientCenteredCare.Controls.selfishScope]

@[simp]
theorem mem_intermediateScope (person : Person) :
    person ∈ intermediateScope ↔ person = .self ∨ person = .ally := by
  simp [intermediateScope, RecipientCenteredCare.Controls.intermediateScope]

theorem group_has_actual_links :
    groupRelation .self .ally /\ groupRelation .ally .self :=
  ⟨Or.inl ⟨rfl, rfl⟩, Or.inr ⟨rfl, rfl⟩⟩

/-- Scope growth actually occurs; the intermediate state is not an identity
update presented as a developmental construction. -/
theorem group_first_round_expands :
    round groupRelation initialScope = intermediateScope := by
  ext person
  cases person <;> simp [round, groupRelation]

theorem intermediate_scope_is_absorbing :
    round groupRelation intermediateScope = intermediateScope := by
  ext person
  cases person <;> simp [round, groupRelation]

theorem intermediate_scope_nonempty_proper :
    intermediateScope.Nonempty /\ intermediateScope ≠ Set.univ := by
  constructor
  · exact ⟨.self, by simp⟩
  · intro universal
    have outside : Person.outsider ∈ intermediateScope := by rw [universal]; trivial
    simp at outside

/-- The intermediate fixed scope has a genuine basin: every nonempty seed
inside the linked group reaches it in one round.  This claim keeps the
propagation relation fixed; it asserts no robustness to adding new links. -/
theorem group_round_from_nonempty_subscope (scope : Set Person)
    (inside : scope ⊆ intermediateScope) (nonempty : scope.Nonempty) :
    round groupRelation scope = intermediateScope := by
  apply Set.Subset.antisymm
  · have growsWithin := round_monotone groupRelation inside
    rw [intermediate_scope_is_absorbing] at growsWithin
    exact growsWithin
  · rcases nonempty with ⟨origin, member⟩
    have originCases : origin = .self ∨ origin = .ally := by
      simpa using inside member
    intro recipient inScope
    have recipientCases : recipient = .self ∨ recipient = .ally := by
      simpa using inScope
    rcases originCases with rfl | rfl
    · rcases recipientCases with rfl | rfl
      · exact Or.inl member
      · exact Or.inr ⟨.self, member, group_has_actual_links.1⟩
    · rcases recipientCases with rfl | rfl
      · exact Or.inr ⟨.ally, member, group_has_actual_links.2⟩
      · exact Or.inl member

/-- Every nonempty subscope of the group enters and remains in that same
proper intermediate basin. -/
theorem group_subscope_basin (scope : Set Person)
    (inside : scope ⊆ intermediateScope) (nonempty : scope.Nonempty) (n : Nat) :
    evolve groupRelation scope (n + 1) = intermediateScope := by
  induction n with
  | zero => exact group_round_from_nonempty_subscope scope inside nonempty
  | succ n inductionHypothesis =>
      change round groupRelation (evolve groupRelation scope (n + 1)) = _
      rw [inductionHypothesis]
      exact intermediate_scope_is_absorbing

/-- Every positive round attains and retains the proper intermediate scope. -/
theorem group_development_stabilizes_intermediately (n : Nat) :
    evolve groupRelation initialScope (n + 1) = intermediateScope := by
  induction n with
  | zero => exact group_first_round_expands
  | succ n inductionHypothesis =>
      change round groupRelation (evolve groupRelation initialScope (n + 1)) = _
      rw [inductionHypothesis]
      exact intermediate_scope_is_absorbing

theorem group_never_reaches_universal :
    ¬ exists n, evolve groupRelation initialScope n = Set.univ := by
  rintro ⟨n, universal⟩
  cases n with
  | zero =>
      change initialScope = Set.univ at universal
      have outside : Person.outsider ∈ initialScope := by rw [universal]; trivial
      simp at outside
  | succ n =>
      exact intermediate_scope_nonempty_proper.2
        ((group_development_stabilizes_intermediately n).symm.trans universal)

theorem group_not_connected : ¬ Connected groupRelation := by
  intro connected
  rcases connected_eventually_universal groupRelation connected initialScope
    ⟨.self, by simp⟩ with ⟨n, universal⟩
  exact group_never_reaches_universal ⟨n, universal n (Nat.le_refl n)⟩

/-- The supplied finite dynamics genuinely admits a third, intermediate
fixed scope.  Excluding it needs assumptions about the propagation relation. -/
theorem linked_intermediate_development_countermodel :
    groupRelation .self .ally /\
    initialScope ≠ intermediateScope /\
    intermediateScope.Nonempty /\ intermediateScope ≠ Set.univ /\
    (forall n, evolve groupRelation initialScope (n + 1) = intermediateScope) := by
  refine ⟨group_has_actual_links.1, ?_, intermediate_scope_nonempty_proper.1,
    intermediate_scope_nonempty_proper.2, group_development_stabilizes_intermediately⟩
  intro equal
  have ally : Person.ally ∈ initialScope := by rw [equal]; simp
  simp at ally

/-- The already constructed coherent two-task plan and the developmental
fixed scope use the same persons and authored scope.  Its actual completed
task set agrees with the growing graph dynamics at every positive round,
while remaining a proper scope.  This neither attributes intrinsic concern
to task completion nor imposes the graph update on the execution itself. -/
theorem coherent_execution_and_absorbing_scope :
    (RecipientCenteredCare.Controls.scopedPlan
      RecipientCenteredCare.Controls.intermediateScope).CoherentAt ∅ /\
    (Plan.run ∅ [Person.self, Person.ally] : Set Person) = intermediateScope /\
    (forall n, evolve groupRelation initialScope (n + 1) =
      (Plan.run ∅ [Person.self, Person.ally] : Set Person)) /\
    (Plan.run ∅ [Person.self, Person.ally] : Set Person) ≠ Set.univ := by
  have completed := RecipientCenteredCare.Controls.coherent_intermediate_scope_exists.2.2.2
  have sameScope := congrArg (fun scope : Finset Person => (scope : Set Person)) completed
  change (Plan.run ∅ [Person.self, Person.ally] : Set Person) = intermediateScope at sameScope
  refine ⟨RecipientCenteredCare.Controls.intermediate_plan_is_coherent,
    sameScope, ?_, ?_⟩
  · intro n
    exact (group_development_stabilizes_intermediately n).trans sameScope.symm
  · rw [sameScope]
    exact intermediate_scope_nonempty_proper.2

/-- A three-person cycle supplies connectivity rather than assuming the
universal developmental outcome. -/
def cycleRelation (first second : Person) : Prop :=
  (first = .self /\ second = .ally) ∨
  (first = .ally /\ second = .outsider) ∨
  (first = .outsider /\ second = .self)

theorem cycle_connected : Connected cycleRelation := by
  intro first second
  cases first <;> cases second
  · exact .refl
  · exact .single (Or.inl ⟨rfl, rfl⟩)
  · have firstPath : Relation.ReflTransGen cycleRelation .self .ally :=
      .single (Or.inl ⟨rfl, rfl⟩)
    exact firstPath.tail (Or.inr (Or.inl ⟨rfl, rfl⟩))
  · have firstPath : Relation.ReflTransGen cycleRelation .ally .outsider :=
      .single (Or.inr (Or.inl ⟨rfl, rfl⟩))
    exact firstPath.tail (Or.inr (Or.inr ⟨rfl, rfl⟩))
  · exact .refl
  · exact .single (Or.inr (Or.inl ⟨rfl, rfl⟩))
  · exact .single (Or.inr (Or.inr ⟨rfl, rfl⟩))
  · have firstPath : Relation.ReflTransGen cycleRelation .outsider .self :=
      .single (Or.inr (Or.inr ⟨rfl, rfl⟩))
    exact firstPath.tail (Or.inl ⟨rfl, rfl⟩)
  · exact .refl

theorem cycle_first_round : round cycleRelation initialScope = intermediateScope := by
  ext person
  cases person <;> simp [round, cycleRelation]

/-- The same initial scope develops to everyone once its actual relation
crosses the group boundary. -/
theorem cycle_two_rounds_universal :
    evolve cycleRelation initialScope 2 = Set.univ := by
  change round cycleRelation (round cycleRelation initialScope) = Set.univ
  rw [cycle_first_round]
  ext person
  cases person <;> simp [round, cycleRelation]

theorem cycle_any_nonempty_scope_eventually_universal (scope : Set Person)
    (nonempty : scope.Nonempty) :
    exists n, forall later, n ≤ later -> evolve cycleRelation scope later = Set.univ :=
  connected_eventually_universal cycleRelation cycle_connected scope nonempty

end Controls

end Mettapedia.Ethics.CareScopeDynamics

#print axioms Mettapedia.Ethics.CareScopeDynamics.eventually_enters_iff_reachable
#print axioms Mettapedia.Ethics.CareScopeDynamics.finite_stabilization
#print axioms Mettapedia.Ethics.CareScopeDynamics.connected_eventually_universal
#print axioms Mettapedia.Ethics.CareScopeDynamics.Controls.linked_intermediate_development_countermodel
#print axioms Mettapedia.Ethics.CareScopeDynamics.Controls.group_subscope_basin
#print axioms Mettapedia.Ethics.CareScopeDynamics.Controls.coherent_execution_and_absorbing_scope
#print axioms Mettapedia.Ethics.CareScopeDynamics.Controls.cycle_any_nonempty_scope_eventually_universal
