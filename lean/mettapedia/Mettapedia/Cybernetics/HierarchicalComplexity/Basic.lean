import Mathlib.GroupTheory.Perm.Basic
import Mathlib.SetTheory.Ordinal.Family

/-!
# Hierarchical complexity from schedule sensitivity

An organization supplies schedule outcomes and a proof of invariance or
sensitivity. Occurrence families may be infinite; coordination adds one to
the supremum of child ranks. Commons--Pekker's published natural-number model
is the separately justified finite specialization, not this transfinite extension.

References:

- M. L. Commons and A. Pekker, *Presenting the Formal Theory of Hierarchical
  Complexity* (2008), for the permutation test and axioms A1--A3, HC1--HC3.
- M. L. Commons, P. M. Trudeau, S. A. Stein, F. A. Richards, and S. R. Krause,
  *Hierarchical Complexity of Tasks Shows the Existence of Developmental
  Stages* (1998), for the task-relative interpretation of hierarchical order.
-/

set_option autoImplicit false

namespace Mettapedia.Cybernetics.HierarchicalComplexity

universe u v

variable {Outcome : Type v} {Occurrence : Type u}

/-- Schedules of an occurrence family are permutations of its occurrences. -/
abbrev Schedule (Occurrence : Type u) := Equiv.Perm Occurrence

/-- A compound action has at least two distinct occurrences. -/
def HasAtLeastTwo (Occurrence : Type u) : Prop :=
  ∃ first second : Occurrence, first ≠ second

namespace HasAtLeastTwo

theorem nonempty (hasAtLeastTwo : HasAtLeastTwo Occurrence) : Nonempty Occurrence := by
  obtain ⟨first, _, _⟩ := hasAtLeastTwo
  exact ⟨first⟩

end HasAtLeastTwo

/-- A schedule semantics is a readout for every permutation of the occurrence
family.  It abstracts from any particular evaluator while retaining exactly
the observation needed by the Commons--Pekker permutation test. -/
abbrev ScheduleSemantics (Occurrence : Type u) (Outcome : Type v) :=
  Schedule Occurrence → Outcome

/-- A chain is insensitive to the order in which its occurrences are
scheduled. -/
def IsChain (semantics : ScheduleSemantics Occurrence Outcome) : Prop :=
  ∀ first second, semantics first = semantics second

/-- A coordination carries positive evidence of order sensitivity. -/
def IsCoordination (semantics : ScheduleSemantics Occurrence Outcome) : Prop :=
  ∃ first second, semantics first ≠ semantics second

/-- Chain and coordination are disjoint. -/
theorem IsChain.not_coordination {semantics : ScheduleSemantics Occurrence Outcome}
    (chain : IsChain semantics) : ¬ IsCoordination semantics := by
  rintro ⟨first, second, different⟩
  exact different (chain first second)

/-- Positive order sensitivity is precisely failure of invariance. -/
theorem isCoordination_iff_not_isChain (semantics : ScheduleSemantics Occurrence Outcome) :
    IsCoordination semantics ↔ ¬ IsChain semantics := by
  classical
  simp only [IsCoordination, IsChain, not_forall]

/-- Classically, every schedule semantics is invariant or order-sensitive. -/
theorem chain_or_coordination (semantics : ScheduleSemantics Occurrence Outcome) :
    IsChain semantics ∨ IsCoordination semantics := by
  rw [isCoordination_iff_not_isChain]
  exact Classical.em _

/-- An organization stores which side of the permutation test it inhabits.
The constructors certify the classification; their schedule readouts remain available. -/
inductive Organization
    (Occurrence : Type u) (Outcome : Type v) :
    Type (max u v) where
  | chain (semantics : ScheduleSemantics Occurrence Outcome)
      (invariant : IsChain semantics)
  | coordination (semantics : ScheduleSemantics Occurrence Outcome)
      (sensitive : IsCoordination semantics)

namespace Organization

/-- The schedule readout without its certificate. It determines the classification,
whose reconstruction on unrestricted schedules is classical. -/
def semantics : Organization Occurrence Outcome → ScheduleSemantics Occurrence Outcome
  | .chain semantics _ => semantics
  | .coordination semantics _ => semantics

def isCoordination : Organization Occurrence Outcome → Bool
  | .chain _ _ => false
  | .coordination _ _ => true

@[simp] theorem semantics_chain (semantics : ScheduleSemantics Occurrence Outcome)
    (invariant : IsChain semantics) :
    Organization.semantics (.chain semantics invariant) = semantics := rfl

@[simp] theorem semantics_coordination (semantics : ScheduleSemantics Occurrence Outcome)
    (sensitive : IsCoordination semantics) :
    Organization.semantics (.coordination semantics sensitive) = semantics := rfl

end Organization

/-! ## Infinitely branching action trees -/

/-- Well-founded trees over arbitrary occurrence families; `Outcome` is the
chosen schedule observation. -/
inductive Action (Outcome : Type v) : Type (max (u + 1) v) where
  | simple : Action Outcome
  | compound (Occurrence : Type u)
      (hasAtLeastTwo : HasAtLeastTwo Occurrence)
      (child : Occurrence → Action Outcome)
      (organization : Organization Occurrence Outcome) : Action Outcome

namespace Action

/-- The ambient ordinal rank.  A chain takes the supremum of its children;
a coordination creates the successor of that supremum. -/
noncomputable def rank : Action.{u, v} Outcome → Ordinal.{u} :=
  Action.rec 0 (fun _ _ _ organization childRank =>
    match organization with
    | .chain _ _ => ⨆ occurrence, childRank occurrence
    | .coordination _ _ =>
        Order.succ (⨆ occurrence, childRank occurrence))

section Families
variable (hasAtLeastTwo : HasAtLeastTwo Occurrence)
    (child : Occurrence → Action.{u, v} Outcome)
    (organization : Organization Occurrence Outcome)
    (semantics : ScheduleSemantics Occurrence Outcome)
    (invariant : IsChain semantics) (sensitive : IsCoordination semantics)

/-- The supremum of the ranks of an immediate child family. -/
noncomputable def childSup : Ordinal.{u} :=
  ⨆ occurrence, rank (child occurrence)

/-- The supremum of a nonempty homogeneous child family is its common rank. -/
theorem childSup_eq_of_equalRank [Nonempty Occurrence] (reference : Occurrence)
    (equalRank : ∀ occurrence,
      Action.rank (child occurrence) = Action.rank (child reference)) :
    (⨆ occurrence, Action.rank (child occurrence)) =
      Action.rank (child reference) := by
  simp only [equalRank, ciSup_const]

/-- Occurrence-indexed simple leaves, before any cardinality readout. -/
def SimpleLeaves : Action.{u, v} Outcome → Type u :=
  Action.rec PUnit (fun _ _ _ _ childLeaves => Sigma childLeaves)

@[simp] theorem simpleLeaves_simple : SimpleLeaves (.simple : Action.{u, v} Outcome) = PUnit := rfl

@[simp] theorem simpleLeaves_compound :
    SimpleLeaves (.compound Occurrence hasAtLeastTwo child organization) =
      Sigma (fun occurrence => SimpleLeaves (child occurrence)) := rfl

/-- Simple-action amount before any finite projection. -/
noncomputable def simpleLeafCardinal (action : Action.{u, v} Outcome) : Cardinal.{u} :=
  Cardinal.mk (SimpleLeaves action)

@[simp] theorem simpleLeafCardinal_simple :
    simpleLeafCardinal (.simple : Action.{u, v} Outcome) = 1 := by
  simp [simpleLeafCardinal]

theorem simpleLeafCardinal_compound : simpleLeafCardinal
      (.compound Occurrence hasAtLeastTwo child organization) =
      Cardinal.sum (fun occurrence => simpleLeafCardinal (child occurrence)) := by
  simpa only [simpleLeafCardinal, simpleLeaves_compound] using
    Cardinal.mk_sigma (fun occurrence => SimpleLeaves (child occurrence))

@[simp] theorem rank_simple : rank (.simple : Action.{u, v} Outcome) = 0 := rfl

@[simp] theorem rank_chain : rank (.compound Occurrence hasAtLeastTwo child
      (.chain semantics invariant)) = ⨆ i, rank (child i) := rfl

@[simp] theorem rank_coordination : rank (.compound Occurrence hasAtLeastTwo child
      (.coordination semantics sensitive)) = Order.succ (⨆ i, rank (child i)) := rfl

/-- Every child rank is bounded by the rank of an invariant compound action. -/
theorem child_rank_le_chain (occurrence : Occurrence) : rank (child occurrence) ≤
      rank (.compound Occurrence hasAtLeastTwo child
        (.chain semantics invariant)) := by
  exact Ordinal.le_iSup (fun index => rank (child index)) occurrence

/-- Coordination strictly exceeds every child, even at an unattained supremum. -/
theorem child_rank_lt_coordination (occurrence : Occurrence) : rank (child occurrence) <
      rank (.compound Occurrence hasAtLeastTwo child
        (.coordination semantics sensitive)) := by
  exact Order.lt_succ_iff.mpr (Ordinal.le_iSup (fun index => rank (child index)) occurrence)

/-- Equal child ranks at coordination nodes are an additional admissibility
condition, separate from the ambient tree constructor. -/
def CommonsAdmissible : Action.{u, v} Outcome → Prop
  | .simple => True
  | .compound _ _ child (.chain _ _) =>
      ∀ occurrence, CommonsAdmissible (child occurrence)
  | .compound _ _ child (.coordination _ _) =>
      (∀ occurrence, CommonsAdmissible (child occurrence)) ∧
      ∀ first second, rank (child first) = rank (child second)

@[simp] theorem commonsAdmissible_simple : CommonsAdmissible
      (Action.simple : Action.{u, v} Outcome) := trivial

end Families

/-- Reflexive-transitive containment in an action tree. -/
inductive IsSubaction :
    Action.{u, v} Outcome →
      Action.{u, v} Outcome → Prop where
  | refl (action) : IsSubaction action action
  | immediate
      {Occurrence : Type u}
      (hasAtLeastTwo : HasAtLeastTwo Occurrence)
      (child : Occurrence → Action.{u, v} Outcome)
      (organization : Organization Occurrence Outcome)
      (occurrence : Occurrence) :
      IsSubaction (child occurrence)
        (.compound Occurrence hasAtLeastTwo child organization)
  | trans {first second third} :
      IsSubaction first second → IsSubaction second third →
        IsSubaction first third

end Action

/-! ## Limit formation is not successor coordination -/

namespace LimitCanary

theorem binary_hasAtLeastTwo : HasAtLeastTwo (Fin 2) := ⟨0, 1, by decide⟩

/-- The schedule outcome records where occurrence zero is sent. -/
def binarySemantics : ScheduleSemantics (Fin 2) (Fin 2) :=
  fun schedule => schedule 0

/-- Swapping the two occurrences changes the binary schedule outcome. -/
theorem binarySensitive : IsCoordination binarySemantics := by
  refine ⟨Equiv.refl (Fin 2), Equiv.swap 0 1, ?_⟩
  simp [binarySemantics]

/-- A canonical action of every finite order. -/
def finiteTower : Nat → Action.{0, 0} (Fin 2)
  | 0 => .simple
  | n + 1 =>
      .compound (Fin 2) binary_hasAtLeastTwo (fun _ => finiteTower n)
        (.coordination binarySemantics binarySensitive)

@[simp] theorem rank_finiteTower (n : Nat) : Action.rank (finiteTower n) = (n : Ordinal) := by
  induction n with
  | zero => rfl
  | succ n inductionHypothesis =>
      rw [finiteTower, Action.rank_coordination]
      rw [inductionHypothesis, ciSup_const]
      rw [Order.succ_eq_add_one, Nat.cast_add_one]

@[simp] theorem commonsAdmissible_finiteTower (n : Nat) :
    Action.CommonsAdmissible (finiteTower n) := by
  induction n with
  | zero => trivial
  | succ n inductionHypothesis =>
      exact ⟨fun _ => inductionHypothesis, fun _ _ => rfl⟩

def constantSemantics : ScheduleSemantics Nat (Fin 2) := fun _ => 0

theorem constantInvariant : IsChain constantSemantics :=
  fun _ _ => rfl

theorem nat_hasAtLeastTwo : HasAtLeastTwo Nat :=
  ⟨0, 1, Nat.zero_ne_one⟩

/-- A countable chain whose child ranks are unbounded below `omega`. -/
def limitChain : Action.{0, 0} (Fin 2) :=
  .compound Nat nat_hasAtLeastTwo finiteTower
    (.chain constantSemantics constantInvariant)

/-- The invariant chain reaches a limit ordinal even though no coordination
occurs at its root. -/
theorem rank_limitChain : Action.rank limitChain = Ordinal.omega0 := by
  rw [limitChain, Action.rank_chain]
  simpa only [rank_finiteTower] using Ordinal.iSup_natCast

/-- An unattained supremum can exceed every child: finite maximality is
essential to the claim that chains do not raise order. -/
theorem every_child_strictly_below_limitChain (n : Nat) :
    Action.rank (finiteTower n) < Action.rank limitChain := by
  rw [rank_finiteTower, rank_limitChain]
  exact Ordinal.natCast_lt_omega0 n

/-- Chains need no homogeneity; every coordinated descendant here is homogeneous. -/
theorem commonsAdmissible_limitChain : Action.CommonsAdmissible limitChain :=
  fun n => commonsAdmissible_finiteTower n

end LimitCanary

end Mettapedia.Cybernetics.HierarchicalComplexity
