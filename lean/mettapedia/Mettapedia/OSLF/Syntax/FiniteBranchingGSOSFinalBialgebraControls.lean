import Mettapedia.OSLF.Syntax.FiniteBranchingGSOSFinalBialgebra
import Mettapedia.OSLF.Syntax.FiniteBranchingFinalSemanticsControls

/-!
# A final algebra action with two independently distinguishable futures

The actual choice law acts on independently unfolded delayed coalgebras.
Both arguments initially offer the same action, but only one continuation
offers a later action. The final compatible action retains both complete
future trees, and omitting either distinct continuation fails its readout.

A second control leaves the format. With inaction, interleaving composition
and an operator whose silent step tests its two arguments for syntactic
equality, `0 | 0` and `0` are bisimilar, but the test separates them:
bisimilarity is not a congruence. Since the semantics of every GSOS law makes
bisimilarity a congruence, no law has these transitions on closed terms.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.OSLF.FiniteBranching.FinalBialgebra.Controls

open _root_.CategoryTheory Mettapedia.CategoryTheory Mettapedia.TypeTheory
open GSOSControls
open Classical

def leftAt (state : Nat) : FiniteActionTree.Tree Nat PUnit :=
  (FinalSemantics.observe Mettapedia.OSLF.FiniteBranching.Controls.signature
    Mettapedia.OSLF.FiniteBranching.Controls.actions
    FinalSemantics.Controls.delayedLeft).f PUnit.unit () state

def rightAt (state : Nat) : FiniteActionTree.Tree Nat PUnit :=
  (FinalSemantics.observe Mettapedia.OSLF.FiniteBranching.Controls.signature
    Mettapedia.OSLF.FiniteBranching.Controls.actions
    FinalSemantics.Controls.delayedRight).f PUnit.unit () state

theorem left_initial_step : FiniteActionTree.Tree.step (leftAt 0) 7 = {leftAt 1} := by
  rw [leftAt, FinalSemantics.observe_step]
  change FinitePowerset.map _ ({1} : Finset Nat) = _
  exact FinitePowerset.map_singleton _ _

theorem right_initial_step : FiniteActionTree.Tree.step (rightAt 0) 7 = {rightAt 1} := by
  rw [rightAt, FinalSemantics.observe_step]
  change FinitePowerset.map _ ({1} : Finset Nat) = _
  exact FinitePowerset.map_singleton _ _

theorem left_later_step : FiniteActionTree.Tree.step (leftAt 1) 9 = {leftAt 2} := by
  rw [leftAt, FinalSemantics.observe_step]
  change FinitePowerset.map _
    (if (1 : Nat) = 0 then if (9 : Nat) = 7 then ({1} : Finset Nat) else ∅
      else if (1 : Nat) = 1 ∧ (9 : Nat) = 9 then {2} else ∅) = _
  simp only [show (1 : Nat) ≠ 0 by decide, ↓reduceIte]
  exact FinitePowerset.map_singleton _ _

theorem right_later_step : FiniteActionTree.Tree.step (rightAt 1) 9 = ∅ := by
  rw [rightAt, FinalSemantics.observe_step]
  change FinitePowerset.map _
    (if (1 : Nat) = 0 ∧ (9 : Nat) = 7 then ({1} : Finset Nat) else ∅) = ∅
  simp [FinitePowerset.map]

theorem later_readouts_differ : leftAt 1 ≠ rightAt 1 := by
  intro same
  have related := (FinalSemantics.kernel_iff_bisimilar
    Mettapedia.OSLF.FiniteBranching.Controls.signature
    Mettapedia.OSLF.FiniteBranching.Controls.actions
    FinalSemantics.Controls.delayedLeft FinalSemantics.Controls.delayedRight
    PUnit.unit () 1 1).1 same
  exact FinalSemantics.Controls.later_states_are_not_bisimilar related

abbrev finalColours : signature.Families := (FinalSemantics.finalObject signature actions).V

def twoFutureInput : signature.Term finalColours () :=
  choose (pure (leftAt 0)) (pure (rightAt 0))

def actual : FiniteActionTree.Tree Nat PUnit :=
  (finalAlgebra law).a.f PUnit.unit () twoFutureInput

theorem action_pure (tree : FiniteActionTree.Tree Nat PUnit) :
    (finalAlgebra law).a.f PUnit.unit () (pure (X := finalColours) tree) = tree :=
  congrArg (fun arrow => arrow PUnit.unit () tree) (action_unit law)

theorem complete_two_future_readout :
    FiniteActionTree.Tree.step actual 7 = {leftAt 1, rightAt 1} := by
  rw [actual, action_successors, twoFutureInput, operational_choice]
  change FinitePowerset.map ((finalAlgebra law).a.f PUnit.unit ())
    (FinitePowerset.map (pure (X := finalColours)) (FiniteActionTree.Tree.step (leftAt 0) 7) ∪
      FinitePowerset.map (pure (X := finalColours)) (FiniteActionTree.Tree.step (rightAt 0) 7)) = _
  rw [left_initial_step, right_initial_step, FinitePowerset.map_singleton,
    FinitePowerset.map_singleton]
  simp only [FinitePowerset.map, Finset.singleton_union, Finset.image_insert,
    Finset.image_singleton, action_pure]

theorem both_distinct_futures_retained :
    leftAt 1 ∈ FiniteActionTree.Tree.step actual 7 ∧
      rightAt 1 ∈ FiniteActionTree.Tree.step actual 7 ∧ leftAt 1 ≠ rightAt 1 := by
  rw [complete_two_future_readout]
  exact ⟨by simp, by simp, later_readouts_differ⟩

theorem actual_successor_count : (FiniteActionTree.Tree.step actual 7).card = 2 := by
  rw [complete_two_future_readout]
  simp [later_readouts_differ]

theorem omitting_the_later_enabled_future_fails :
    FiniteActionTree.Tree.step actual 7 ≠ {rightAt 1} := by
  intro omitted
  have member := both_distinct_futures_retained.1
  rw [omitted, Finset.mem_singleton] at member
  exact later_readouts_differ member

end Mettapedia.OSLF.FiniteBranching.FinalBialgebra.Controls

namespace Mettapedia.OSLF.FiniteBranching.FinalBialgebra.EqualityTestControl

open _root_.CategoryTheory Mettapedia.CategoryTheory Mettapedia.TypeTheory
open Mettapedia.OSLF.DeterministicGSOS (Signature)
open Classical

/-- Inaction, binary composition, and a binary equality test. -/
inductive Operator where
  | idle
  | both
  | same

abbrev signature : Signature.{0} where
  Srt := Unit
  Operator := fun _ => Operator
  Position := fun operator => match operator with
    | .idle => Empty
    | .both => Bool
    | .same => Bool
  argument := fun _ _ => ()
  finite operator := by cases operator <;> infer_instance

/-- One silent action. -/
abbrev actions : signature.Srt → Type := fun _ => Unit

abbrev Closed := signature.ClosedTerm ()

def idle : Closed :=
  IndexedPolynomial.Free.node signature.polynomial Operator.idle (fun position => position.elim)

def both (left right : Closed) : Closed :=
  IndexedPolynomial.Free.node signature.polynomial Operator.both
    (fun position => if position then right else left)

def same (left right : Closed) : Closed :=
  IndexedPolynomial.Free.node signature.polynomial Operator.same
    (fun position => if position then right else left)

/-- The successors of one constructor from its arguments and their successors:
composition interleaves, and the test steps to `idle` exactly when its two
arguments are the same closed term. -/
def successors : (shape : Operator) → (Bool → Closed × Finset Closed) → Finset Closed
  | .idle, _ => ∅
  | .both, children =>
      FinitePowerset.map (fun next => both next (children true).1) (children false).2 ∪
        FinitePowerset.map (fun next => both (children false).1 next) (children true).2
  | .same, children => if (children false).1 = (children true).1 then {idle} else ∅

/-- Evaluate a closed term to itself and its successors, by structural recursion. -/
def evaluate (term : Closed) : Closed × Finset Closed :=
  IndexedPolynomial.Free.fold signature.polynomial
    (carrier := fun _ _ => Closed × Finset Closed) (fun _ _ hole => PEmpty.elim hole)
    { act := fun _ _ layer =>
        (IndexedPolynomial.Free.node signature.polynomial layer.1
            (fun position => (layer.2 position).1),
          match layer with
          | ⟨.idle, _⟩ => ∅
          | ⟨.both, children⟩ => successors .both children
          | ⟨.same, children⟩ => successors .same children) }
    PUnit.unit () term

theorem evaluate_source (term : Closed) : (evaluate term).1 = term := by
  have agree := IndexedPolynomial.Free.fold_unique signature.polynomial
    (fun _ _ hole => IndexedPolynomial.Free.pure signature.polynomial hole)
    (IndexedPolynomial.Free.algebra signature.polynomial)
    (fun base sort plan => match base, sort with
      | PUnit.unit, () => (evaluate plan).1)
    (fun _ _ hole => PEmpty.elim hole) (fun base sort _ _ => by cases base; cases sort; rfl)
    PUnit.unit () term
  exact agree.trans (IndexedPolynomial.Free.bind_pure_right signature.polynomial term)

/-- The successors of a closed term. -/
def step (term : Closed) : Finset Closed := (evaluate term).2

theorem step_idle : step idle = ∅ := rfl

theorem step_both (left right : Closed) :
    step (both left right) =
      FinitePowerset.map (fun next => both next right) (step left) ∪
        FinitePowerset.map (fun next => both left next) (step right) := by
  change successors .both (fun position => evaluate (if position then right else left)) = _
  simp only [successors, if_true, Bool.false_eq_true, if_false, evaluate_source]
  rfl

theorem step_same (left right : Closed) :
    step (same left right) = if left = right then {idle} else ∅ := by
  change successors .same (fun position => evaluate (if position then right else left)) = _
  simp only [successors, if_true, Bool.false_eq_true, if_false, evaluate_source]

/-- The closed transition system of these rules. -/
def system : Endofunctor.Coalgebra (behaviourFunctor signature actions) where
  V := signature.polynomial.Free signature.noVariables
  str := fun base sort => match base, sort with
    | PUnit.unit, () => ↾(fun term _ => step term)

theorem both_idle_ne_idle : both idle idle ≠ idle := by
  intro equal
  cases equal

theorem step_both_idle : step (both idle idle) = ∅ := by
  rw [step_both, step_idle]
  rfl

/-- The closed terms, as a family. -/
abbrev ClosedFamily : signature.Families := signature.polynomial.Free signature.noVariables

/-- A transition structure on closed terms. -/
abbrev Transitions :=
  ClosedFamily ⟶ (behaviourFunctor signature actions).obj ClosedFamily

/-- Closed terms with a given transition structure. -/
abbrev onClosed (transitions : Transitions) :
    Endofunctor.Coalgebra (behaviourFunctor signature actions) :=
  ⟨ClosedFamily, transitions⟩

/-- Two dead closed terms are bisimilar for any transitions that agree with `step`. -/
theorem dead_bisimilar (transitions : Transitions)
    (agree : ∀ term label, transitions PUnit.unit () term label = step term)
    {first second : Closed} (firstDead : step first = ∅) (secondDead : step second = ∅) :
    Bisimulation.Bisimilar (onClosed transitions) (onClosed transitions) PUnit.unit ()
      first second := by
  refine ⟨fun base sort => match base, sort with
    | PUnit.unit, () => fun left right => step left = ∅ ∧ step right = ∅, ?_,
    firstDead, secondDead⟩
  intro base sort
  cases base
  cases sort
  rintro left right ⟨leftDead, rightDead⟩ label
  change FinitePowerset.Related _ (transitions PUnit.unit () left label)
    (transitions PUnit.unit () right label)
  rw [agree, agree, leftDead, rightDead]
  exact ⟨fun _ member => absurd member (Finset.notMem_empty _),
    fun _ member => absurd member (Finset.notMem_empty _)⟩

/-- For any transitions that agree with `step`, the test separates `0 | 0` from `0`. -/
theorem same_separates (transitions : Transitions)
    (agree : ∀ term label, transitions PUnit.unit () term label = step term) :
    ¬ Bisimulation.Bisimilar (onClosed transitions) (onClosed transitions) PUnit.unit ()
      (same (both idle idle) idle) (same idle idle) := by
  intro related
  have available := Bisimulation.bisimilar_availability (S := signature) (Actions := actions)
    PUnit.unit () related ()
  change transitions PUnit.unit () _ () = ∅ ↔ transitions PUnit.unit () _ () = ∅ at available
  rw [agree, agree, step_same, step_same, if_neg both_idle_ne_idle, if_pos rfl] at available
  exact Finset.singleton_ne_empty idle (available.mp rfl)

/-- Bisimilarity of these rules is not a congruence: the arguments are pairwise
bisimilar, the tests are not. -/
theorem equalityTest_breaks_congruence :
    Bisimulation.Bisimilar system system PUnit.unit () (both idle idle) idle ∧
      Bisimulation.Bisimilar system system PUnit.unit () idle idle ∧
      ¬ Bisimulation.Bisimilar system system PUnit.unit ()
        (same (both idle idle) idle) (same idle idle) :=
  ⟨dead_bisimilar system.str (fun _ _ => rfl) step_both_idle step_idle,
    Bisimulation.bisimilar_refl system PUnit.unit () idle,
    same_separates system.str (fun _ _ => rfl)⟩

/-- No GSOS law has the transitions of the equality test on closed terms. -/
theorem no_law_presents_equalityTest :
    ¬ ∃ law : Law signature actions, ∀ term label,
      (closedOperational law).str PUnit.unit () term label = step term := by
  rintro ⟨law, agree⟩
  apply same_separates (closedOperational law).str agree
  have composed := dead_bisimilar (closedOperational law).str agree step_both_idle step_idle
  change Bisimulation.Bisimilar (closedOperational law) (closedOperational law) PUnit.unit ()
    (same (both idle idle) idle) (same idle idle)
  change Bisimulation.Bisimilar (closedOperational law) (closedOperational law) PUnit.unit ()
    (both idle idle) idle at composed
  rw [← semantics_eq_iff_bisimilar] at composed ⊢
  rw [semantics_readout] at composed ⊢
  apply FinalSemantics.constructor_kernel_congruent (lawEquiv _ _ law) _ PUnit.unit () Operator.same
  intro position
  cases position
  · exact composed
  · rfl

end Mettapedia.OSLF.FiniteBranching.FinalBialgebra.EqualityTestControl
