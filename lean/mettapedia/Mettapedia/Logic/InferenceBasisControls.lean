import Mettapedia.Logic.InferenceBasis
import Lean.Elab.Tactic.Omega

/-!
# Incomparable minimal inference bases

Two finite rule sets generate every natural-number judgment: zero/successor,
and one/predecessor/add-two. Both are irredundant, but their primitive names
are disjoint. Consequently no least sufficient subset exists under literal
primitive inclusion. Their consequence relations agree, even for arbitrary
open hypotheses. This is a control for the distinction between semantic
generation and primitive inclusion, not a claim about MM0's minimality.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.InferenceBasis.Controls

inductive Operation where
  | zero | successor | one | predecessor | addTwo
deriving DecidableEq, Repr

def family : RuleFamily Operation Nat
  | .zero, premises, result => premises = [] ∧ result = 0
  | .successor, premises, result => ∃ n, premises = [n] ∧ result = n + 1
  | .one, premises, result => premises = [] ∧ result = 1
  | .predecessor, premises, result => ∃ n, premises = [n + 1] ∧ result = n
  | .addTwo, premises, result => ∃ n, premises = [n] ∧ result = n + 2

def first : Finset Operation := {.zero, .successor}
def second : Finset Operation := {.one, .predecessor, .addTwo}
def available : Finset Operation := first ∪ second

theorem first_derives (context : List Nat) (n : Nat) : From family first context n := by
  induction n with
  | zero => exact apply_rule (family := family) (operation := Operation.zero) (premises := []) (by simp [first]) ⟨rfl, rfl⟩ (by simp)
  | succ n ih =>
      exact apply_rule (family := family) (premises := [n]) (operation := Operation.successor) (by simp [first]) ⟨n, rfl, rfl⟩
        (by simpa using ih)

theorem second_one (context : List Nat) : From family second context 1 :=
  apply_rule (family := family) (premises := []) (operation := Operation.one) (by simp [second]) ⟨rfl, rfl⟩ (by simp)

theorem second_zero (context : List Nat) : From family second context 0 :=
  apply_rule (family := family) (premises := [1]) (operation := Operation.predecessor) (by simp [second]) ⟨0, rfl, rfl⟩
    (by simpa using second_one context)

theorem second_derives (context : List Nat) (n : Nat) : From family second context n := by
  induction n using Nat.twoStepInduction with
  | zero => exact second_zero context
  | one => exact second_one context
  | more n ih _ =>
      exact apply_rule (family := family) (premises := [n]) (operation := Operation.addTwo) (by simp [second]) ⟨n, rfl, rfl⟩
        (by simpa using ih)

theorem first_generates : Generates family first available :=
  fun _ _ premises result _ => first_derives premises result

theorem second_generates : Generates family second available :=
  fun _ _ premises result _ => second_derives premises result

theorem first_irredundant : Irredundant family first := by
  intro operation member
  have cases : operation = .zero ∨ operation = .successor := by
    simpa [first] using member
  rcases cases with rfl | rfl
  · refine not_implements_of_invariant (fun _ => False) ?_ [] 0 ?_ ?_ ?_
    · intro op used premises result rule children
      have same : op = .successor := by cases op <;> simp_all [first]
      cases same
      obtain ⟨n, rfl, _⟩ := rule
      exact children n (by simp)
    · exact ⟨rfl, rfl⟩
    · simp
    · simp
  · refine not_implements_of_invariant (fun n => n = 0) ?_ [0] 1 ?_ ?_ ?_
    · intro op used premises result rule _
      have same : op = .zero := by cases op <;> simp_all [first]
      cases same
      exact rule.2
    · exact ⟨0, rfl, rfl⟩
    · simp
    · decide

theorem second_irredundant : Irredundant family second := by
  intro operation member
  have cases : operation = .one ∨ operation = .predecessor ∨ operation = .addTwo := by
    simpa [second] using member
  rcases cases with rfl | rfl | rfl
  · refine not_implements_of_invariant (fun _ => False) ?_ [] 1 ?_ ?_ ?_
    · intro op used premises result rule children
      have cases : op = .predecessor ∨ op = .addTwo := by cases op <;> simp_all [second]
      rcases cases with rfl | rfl
      · obtain ⟨n, rfl, _⟩ := rule
        exact children (n + 1) (by simp)
      · obtain ⟨n, rfl, _⟩ := rule
        exact children n (by simp)
    · exact ⟨rfl, rfl⟩
    · simp
    · simp
  · refine not_implements_of_invariant (fun n => n % 2 = 1) ?_ [1] 0 ?_ ?_ ?_
    · intro op used premises result rule children
      have cases : op = .one ∨ op = .addTwo := by cases op <;> simp_all [second]
      rcases cases with rfl | rfl
      · rw [rule.2]
      · obtain ⟨n, rfl, rfl⟩ := rule
        simpa using children n (by simp)
    · exact ⟨0, rfl, rfl⟩
    · simp
    · decide
  · refine not_implements_of_invariant (fun n => n ≤ 1) ?_ [0] 2 ?_ ?_ ?_
    · intro op used premises result rule children
      have cases : op = .one ∨ op = .predecessor := by cases op <;> simp_all [second]
      rcases cases with rfl | rfl
      · rw [rule.2]
      · obtain ⟨n, rfl, rfl⟩ := rule
        have bound := children (result + 1) (by simp)
        omega
    · exact ⟨0, rfl, rfl⟩
    · simp
    · decide

theorem two_minimal_bases :
    MinimalGenerating family available first ∧ MinimalGenerating family available second :=
  ⟨first_irredundant.minimal_of_generates Finset.subset_union_left first_generates,
    second_irredundant.minimal_of_generates Finset.subset_union_right second_generates⟩

theorem same_consequences (context : List Nat) (n : Nat) :
    From family first context n ↔ From family second context n :=
  ⟨fun _ => second_derives context n, fun _ => first_derives context n⟩

theorem primitive_bases_incomparable : ¬ first ⊆ second ∧ ¬ second ⊆ first := by
  constructor
  · intro included
    have impossible := included (show Operation.zero ∈ first by decide)
    simp [second] at impossible
  · intro included
    have impossible := included (show Operation.one ∈ second by decide)
    simp [first] at impossible

theorem empty_has_no_closed_derivation (n : Nat) : ¬ From family ∅ [] n := by
  intro derived
  apply derived.least (fun _ => False)
  intro premises result rule _
  simp [Rules] at rule

/-- A least sufficient subset would have to lie in both disjoint bases. -/
theorem no_least_generating_basis :
    ¬ ∃ basis : Finset Operation, Generates family basis available ∧
      ∀ other, Generates family other available → basis ⊆ other := by
  rintro ⟨basis, generates, least⟩
  have inFirst := least first first_generates
  have inSecond := least second second_generates
  have empty : basis = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro op member
    have both : op ∈ first ∧ op ∈ second := ⟨inFirst member, inSecond member⟩
    cases op <;> simp [first, second] at both
  subst basis
  exact empty_has_no_closed_derivation 0
    (generates .zero (by simp [available, first]) [] 0 ⟨rfl, rfl⟩)

end Mettapedia.Logic.InferenceBasis.Controls
