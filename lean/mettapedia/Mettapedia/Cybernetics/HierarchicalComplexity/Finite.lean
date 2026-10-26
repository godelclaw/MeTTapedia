import Mathlib.Order.ConditionallyCompleteLattice.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Finite.Sigma
import Mathlib.SetTheory.Cardinal.Finite
import Mettapedia.Cybernetics.HierarchicalComplexity.Basic

/-!
# The finite Commons--Pekker hierarchy as a specialization

Finite branching gives a natural-number projection of the ambient ordinal
rank. Commons admissibility supplies the coordination homogeneity needed for
the predecessor theorem and the exact exponential simple-leaf minimum.

Reference:

- M. L. Commons and A. Pekker, *Presenting the Formal Theory of Hierarchical
  Complexity* (2008).
-/

set_option autoImplicit false

namespace Mettapedia.Cybernetics.HierarchicalComplexity

universe u v

variable {Outcome : Type v} {Occurrence : Type u}

namespace Action

/-- Every immediate occurrence family is finite, recursively. -/
def FinitelyBranching : Action.{u, v} Outcome → Prop :=
  Action.rec True (fun Occurrence _ _ _ childFinite =>
    _root_.Finite Occurrence ∧ ∀ occurrence, childFinite occurrence)

@[simp] theorem finitelyBranching_simple : FinitelyBranching
      (Action.simple : Action.{u, v} Outcome) := trivial

@[simp] theorem finitelyBranching_compound (hasAtLeastTwo : HasAtLeastTwo Occurrence)
    (child : Occurrence → Action.{u, v} Outcome)
    (organization : Organization Occurrence Outcome) :
    FinitelyBranching
      (.compound Occurrence hasAtLeastTwo child organization) ↔
      _root_.Finite Occurrence ∧ ∀ occurrence, FinitelyBranching (child occurrence) :=
  Iff.rfl

variable (action : Action.{u, v} Outcome)
    (finite : FinitelyBranching action) (admissible : CommonsAdmissible action)
include finite

/-- Finite branching forces the ambient ordinal rank below `omega`. -/
theorem rank_lt_omega0_of_finitelyBranching : rank action < Ordinal.omega0 := by
  induction action with
  | simple => exact Ordinal.natCast_lt_omega0 0
  | compound I two child o ih =>
      let : _root_.Finite I := finite.1
      let : Nonempty I := two.nonempty
      obtain ⟨i, hi⟩ := exists_eq_ciSup_of_finite (f := fun i => rank (child i))
      have below := ih i (finite.2 i)
      cases o with
      | chain _ _ => simpa only [rank_chain, ← hi] using below
      | coordination _ _ =>
          simpa only [rank_coordination, ← hi] using Ordinal.isSuccLimit_omega0.succ_lt below

theorem finite_simpleLeaves : _root_.Finite (SimpleLeaves action) := by
  induction action with
  | simple => exact inferInstanceAs (_root_.Finite PUnit)
  | compound I two child o ih =>
      let : _root_.Finite I := finite.1
      let : ∀ i, _root_.Finite (SimpleLeaves (child i)) := fun i => ih i (finite.2 i)
      exact inferInstanceAs (_root_.Finite (Sigma fun i => SimpleLeaves (child i)))

include admissible

/-- Finite Commons actions of rank `n` have at least `2^n` simple leaves. -/
theorem pow_two_le_natCard_simpleLeaves_of_rank_eq
    (n : Nat) (rankEqual : rank action = (n : Ordinal)) :
    2 ^ n ≤ Nat.card (SimpleLeaves action) := by
  classical
  induction action generalizing n with
  | simple =>
      have zero : n = 0 := Nat.cast_injective (by simpa only [rank_simple, Nat.cast_zero] using rankEqual.symm)
      subst n; simp [SimpleLeaves]
  | compound I two child o ih =>
      let : _root_.Finite I := finite.1
      let : Nonempty I := two.nonempty
      let : Fintype I := Fintype.ofFinite I
      let : ∀ i, _root_.Finite (SimpleLeaves (child i)) := fun i => finite_simpleLeaves _ (finite.2 i)
      change 2 ^ n ≤ Nat.card (Sigma fun i => SimpleLeaves (child i))
      rw [Nat.card_sigma]
      cases o with
      | chain f invariant =>
          obtain ⟨i, hi⟩ := exists_eq_ciSup_of_finite (f := fun i => rank (child i))
          exact (ih i (finite.2 i) (admissible i) n (hi.trans rankEqual)).trans
            (Finset.single_le_sum (f := fun k => Nat.card (SimpleLeaves (child k)))
              (fun _ _ => Nat.zero_le _) (Finset.mem_univ i))
      | coordination f sensitive =>
          have witnesses := two
          obtain ⟨i, j, different⟩ := witnesses
          obtain ⟨m, hm⟩ := Ordinal.lt_omega0.mp (rank_lt_omega0_of_finitelyBranching _ (finite.2 i))
          rw [rank_coordination, childSup_eq_of_equalRank child i (fun k => admissible.2 k i),
            hm, Order.succ_eq_add_one, ← Nat.cast_add_one] at rankEqual
          have lower (k : I) := ih k (finite.2 k) (admissible.1 k) m ((admissible.2 k i).trans hm)
          have pair : Nat.card (SimpleLeaves (child i)) + Nat.card (SimpleLeaves (child j)) ≤
              ∑ k, Nat.card (SimpleLeaves (child k)) := by
            rw [← Finset.sum_pair (f := fun k => Nat.card (SimpleLeaves (child k))) different]
            exact Finset.sum_le_sum_of_subset (Finset.subset_univ _)
          have bound := (Nat.add_le_add (lower i) (lower j)).trans pair
          have same : n = m + 1 := (Nat.cast_injective rankEqual).symm
          simpa only [same, pow_succ, Nat.mul_two] using bound

/-- Finite attainment and HC2 expose a subaction at the predecessor order. -/
theorem exists_subaction_rank_pred (n : Nat) (rankEqual : rank action = ((n + 1 : Nat) : Ordinal)) :
    ∃ subaction,
      IsSubaction subaction action ∧
      FinitelyBranching subaction ∧
      CommonsAdmissible subaction ∧
      rank subaction = (n : Ordinal) := by
  induction action generalizing n with
  | simple =>
      exact (Nat.zero_ne_add_one n (Nat.cast_injective (by simpa only [rank_simple, Nat.cast_zero] using rankEqual))).elim
  | compound I two child o ih =>
      let : _root_.Finite I := finite.1
      let : Nonempty I := two.nonempty
      cases o with
      | chain f invariant =>
          obtain ⟨i, hi⟩ := exists_eq_ciSup_of_finite (f := fun i => rank (child i))
          obtain ⟨sub, contained, hf, ha, hr⟩ := ih i (finite.2 i) (admissible i) n (hi.trans rankEqual)
          exact ⟨sub, .trans contained (.immediate two child (.chain f invariant) i), hf, ha, hr⟩
      | coordination f sensitive =>
          have witnesses := two
          obtain ⟨i, _, _⟩ := witnesses
          have same : Order.succ (rank (child i)) = Order.succ (n : Ordinal) := by
            simpa only [rank_coordination, childSup_eq_of_equalRank child i (fun k => admissible.2 k i),
              Nat.cast_add_one, Order.succ_eq_add_one] using rankEqual
          exact ⟨child i, .immediate two child (.coordination f sensitive) i,
            finite.2 i, admissible.1 i, Order.succ_injective same⟩

end Action

/-! ## The source-faithful finite view -/

namespace Finite

/-- The ambient tree with finite branching and Commons admissibility. -/
structure Action (Outcome : Type v) where
  toAmbient :
    HierarchicalComplexity.Action.{u, v} Outcome
  finitelyBranching : toAmbient.FinitelyBranching
  commonsAdmissible : toAmbient.CommonsAdmissible

namespace Action

variable (action : Finite.Action.{u, v} Outcome)

/-- The natural-number order whose ordinal cast is the ambient rank. -/
noncomputable def order : Nat :=
  Classical.choose (Ordinal.lt_omega0.mp
    (HierarchicalComplexity.Action.rank_lt_omega0_of_finitelyBranching
      action.toAmbient action.finitelyBranching))

/-- Natural order projects exactly the ambient rank. -/
theorem rank_eq_natCast_order : action.toAmbient.rank = (action.order : Ordinal) :=
  Classical.choose_spec (Ordinal.lt_omega0.mp
    (HierarchicalComplexity.Action.rank_lt_omega0_of_finitelyBranching
      action.toAmbient action.finitelyBranching))

/-- Natural-order comparison is exactly comparison of the ambient ranks. -/
theorem order_eq_iff (n : Nat) : action.order = n ↔ action.toAmbient.rank = (n : Ordinal) := by
  rw [rank_eq_natCast_order]
  exact (Nat.cast_injective (R := Ordinal)).eq_iff.symm

theorem order_le_iff_rank_le (other : Finite.Action.{u, v} Outcome) :
    action.order ≤ other.order ↔ action.toAmbient.rank ≤ other.toAmbient.rank := by
  rw [action.rank_eq_natCast_order, other.rank_eq_natCast_order]
  exact Nat.cast_le.symm

/-- HC1: the simple action has order zero. -/
def simple (Outcome : Type v) : Finite.Action.{u, v} Outcome :=
  ⟨.simple, trivial, trivial⟩

@[simp] theorem order_simple (Outcome : Type v) :
    (simple Outcome : Finite.Action.{u, v} Outcome).order = 0 := by
  apply Nat.cast_injective (R := Ordinal)
  rw [← rank_eq_natCast_order]
  rfl

section Constructors
variable [finiteOccurrence : _root_.Finite Occurrence]
    (hasAtLeastTwo : HasAtLeastTwo Occurrence)
    (child : Occurrence → Finite.Action.{u, v} Outcome)
    (semantics : ScheduleSemantics Occurrence Outcome)
    (invariant : IsChain semantics) (sensitive : IsCoordination semantics)
    (equalOrder : ∀ first second, (child first).order = (child second).order)

/-- Form a finite chain from finite Commons children. -/
def chain : Finite.Action.{u, v} Outcome where
  toAmbient := .compound Occurrence hasAtLeastTwo
    (fun occurrence => (child occurrence).toAmbient)
    (.chain semantics invariant)
  finitelyBranching :=
    ⟨finiteOccurrence, fun occurrence => (child occurrence).finitelyBranching⟩
  commonsAdmissible :=
    fun occurrence => (child occurrence).commonsAdmissible

/-- Finite coordination requires explicit child-order homogeneity (HC2). -/
def coordination : Finite.Action.{u, v} Outcome where
  toAmbient := .compound Occurrence hasAtLeastTwo
    (fun occurrence => (child occurrence).toAmbient)
    (.coordination semantics sensitive)
  finitelyBranching :=
    ⟨finiteOccurrence, fun occurrence => (child occurrence).finitelyBranching⟩
  commonsAdmissible := by
    refine ⟨fun occurrence => (child occurrence).commonsAdmissible, ?_⟩
    intro first second
    rw [(child first).rank_eq_natCast_order,
      (child second).rank_eq_natCast_order, equalOrder first second]

/-- HC3: a finite chain attains the maximum child order. -/
theorem chain_order_is_child_maximum : (∃ occurrence,
      (chain hasAtLeastTwo child semantics invariant).order =
        (child occurrence).order) ∧
    ∀ occurrence,
      (child occurrence).order ≤
        (chain hasAtLeastTwo child semantics invariant).order := by
  let : Nonempty Occurrence := hasAtLeastTwo.nonempty
  obtain ⟨i, hi⟩ := exists_eq_ciSup_of_finite (f := fun i => (child i).toAmbient.rank)
  refine ⟨⟨i, ?_⟩, fun j => (order_le_iff_rank_le _ _).mpr ?_⟩
  · apply (order_eq_iff _ _).mpr
    exact hi.symm.trans (child i).rank_eq_natCast_order
  · exact HierarchicalComplexity.Action.child_rank_le_chain hasAtLeastTwo _ semantics invariant j

/-- HC3: homogeneous coordination adds one to the common child order. -/
theorem coordination_order_eq_child_add_one (occurrence : Occurrence) :
    (coordination hasAtLeastTwo child semantics sensitive equalOrder).order =
      (child occurrence).order + 1 := by
  let : Nonempty Occurrence := hasAtLeastTwo.nonempty
  apply (order_eq_iff _ _).mpr
  change Order.succ (⨆ i, (child i).toAmbient.rank) = ((_ + 1 : Nat) : Ordinal)
  rw [HierarchicalComplexity.Action.childSup_eq_of_equalRank
    (fun i => (child i).toAmbient) occurrence (fun i => ?_),
    (child occurrence).rank_eq_natCast_order, Nat.cast_add_one, Order.succ_eq_add_one]
  rw [(child _).rank_eq_natCast_order, (child occurrence).rank_eq_natCast_order, equalOrder]

end Constructors

/-- Number of simple leaves in the finite projection. -/
noncomputable def simpleLeafCount : Nat :=
  Nat.card (HierarchicalComplexity.Action.SimpleLeaves action.toAmbient)

/-- The exponential lower bound at the action's own order. -/
theorem pow_two_order_le_simpleLeafCount : 2 ^ action.order ≤ action.simpleLeafCount := by
  exact HierarchicalComplexity.Action.pow_two_le_natCard_simpleLeaves_of_rank_eq
    action.toAmbient action.finitelyBranching action.commonsAdmissible
      action.order action.rank_eq_natCast_order

/-- C3: finite orders are trichotomous. -/
theorem order_trichotomy (first second : Finite.Action.{u, v} Outcome) :
    first.order < second.order ∨ first.order = second.order ∨
      second.order < first.order :=
  lt_trichotomy first.order second.order

/-- C4: strict comparison of finite orders is transitive. -/
theorem order_lt_trans {first second third : Finite.Action.{u, v} Outcome}
    (firstSecond : first.order < second.order)
    (secondThird : second.order < third.order) :
    first.order < third.order :=
  firstSecond.trans secondThird

end Action

/-! ## C2: no gaps in the realized finite spectrum -/

def RealizesOrder (Outcome : Type v) (n : Nat) : Prop :=
  ∃ action : Finite.Action.{u, v} Outcome, action.order = n

/-- C2 strengthened: realizing `n+1` exposes a realized predecessor. -/
theorem realizesOrder_pred_of_succ {n : Nat} (higher : RealizesOrder.{u, v} Outcome (n + 1)) :
    RealizesOrder.{u, v} Outcome n := by
  obtain ⟨action, actionOrder⟩ := higher
  have actionRank : action.toAmbient.rank = ((n + 1 : Nat) : Ordinal) := by
    rw [action.rank_eq_natCast_order, actionOrder]
  obtain ⟨subaction, _, subFinite, subAdmissible, subRank⟩ :=
    HierarchicalComplexity.Action.exists_subaction_rank_pred
      action.toAmbient action.finitelyBranching action.commonsAdmissible n actionRank
  let finiteSubaction : Finite.Action.{u, v} Outcome :=
    ⟨subaction, subFinite, subAdmissible⟩
  refine ⟨finiteSubaction, ?_⟩
  exact (Finite.Action.order_eq_iff _ _).mpr subRank

/-- Commons and Pekker's stated C2 form. -/
theorem no_gaps {n : Nat} (_lower : RealizesOrder.{u, v} Outcome n)
    (higher : RealizesOrder.{u, v} Outcome (n + 2)) :
    RealizesOrder.{u, v} Outcome (n + 1) := realizesOrder_pred_of_succ higher

/-! ## The exact `phi n = 2^n` minimum -/

namespace Phi

open HierarchicalComplexity.LimitCanary

@[simp] theorem finitelyBranching_finiteTower (n : Nat) :
    HierarchicalComplexity.Action.FinitelyBranching (finiteTower n) := by
  induction n with
  | zero => trivial
  | succ n inductionHypothesis =>
      exact ⟨inferInstance, fun _ => inductionHypothesis⟩

/-- The binary witness, regarded through the finite Commons specialization. -/
def binaryTower (n : Nat) : Finite.Action.{0, 0} (Fin 2) :=
  ⟨finiteTower n, finitelyBranching_finiteTower n, commonsAdmissible_finiteTower n⟩

@[simp] theorem order_binaryTower (n : Nat) : (binaryTower n).order = n := by
  exact (Finite.Action.order_eq_iff _ _).mpr (rank_finiteTower n)

@[simp] theorem natCard_simpleLeaves_finiteTower (n : Nat) :
    Nat.card (HierarchicalComplexity.Action.SimpleLeaves (finiteTower n)) =
      2 ^ n := by
  induction n with
  | zero => simp [finiteTower, HierarchicalComplexity.Action.SimpleLeaves]
  | succ n ih =>
      change Nat.card (Sigma fun _ : Fin 2 => HierarchicalComplexity.Action.SimpleLeaves (finiteTower n)) = _
      rw [Nat.card_congr (Equiv.sigmaEquivProd (Fin 2) _), Nat.card_prod, Nat.card_fin, ih, pow_succ]
      exact Nat.mul_comm _ _

@[simp] theorem simpleLeafCount_binaryTower (n : Nat) : (binaryTower n).simpleLeafCount = 2 ^ n :=
  natCard_simpleLeaves_finiteTower n

/-- `count` is a realized minimum simple-leaf count at order `n`. -/
def IsMinimumSimpleLeafCount (n count : Nat) : Prop :=
  (∃ action : Finite.Action.{0, 0} (Fin 2),
      action.order = n ∧ action.simpleLeafCount = count) ∧
  ∀ action : Finite.Action.{0, 0} (Fin 2),
    action.order = n → count ≤ action.simpleLeafCount

/-- The binary tower attains Commons--Pekker's minimum `phi_n = 2^n`. -/
theorem phi_eq_pow_two (n : Nat) : IsMinimumSimpleLeafCount n (2 ^ n) := by
  refine ⟨⟨binaryTower n, order_binaryTower n, simpleLeafCount_binaryTower n⟩, ?_⟩
  intro action orderEqual
  simpa only [orderEqual] using action.pow_two_order_le_simpleLeafCount

end Phi

end Finite

end Mettapedia.Cybernetics.HierarchicalComplexity
