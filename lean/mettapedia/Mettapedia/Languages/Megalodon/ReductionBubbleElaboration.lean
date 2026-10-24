import Mettapedia.Languages.Megalodon.FuelledConversionWitness
import Mettapedia.TypeTheory.BubbleElaboration

/-!
# Mathdata reduction steps as a bubble with graded explicit receipts

Every reduction step of the Mathdata conversion profile that the explicit
definition-conversion kernel accepts can be declared as a step of one bubble
(`bubbles`). Its conversion trees elaborate into signed paths of checked
reduction articles (`checkedPaths`, `elaborate`): reflexivity is the empty
path, symmetry reverses and flips, transitivity appends. These are the
explicit witnesses of `FuelledConversionWitness`.

* **Exact receipts** (`elaborate_checked`, `elaborate_sound`). Every elaborated
  path is accepted by the edge checker, and its endpoints are related by the
  equivalence closure of checked reductions.
* **The grade is the recorded work** (`elaborate_length`). The number of edges
  in the elaborated path is the number of declared steps in the tree. The
  proof is naturality (`BubbleElaboration.sound_natural`) along the receipt map
  that forgets a path to its length.
* **The grade is the budget** (`elaborate_bounded`). The bounded witness checker
  accepts the elaborated path exactly when its budget is at least the work.
* **Fuelled search produces graded receipts** (`seek_receipt`). A path found by
  the bounded definition search is a receipt of this global equality within
  the search budget.
* **A fixed budget is not a bubble** (`Controls.budget_one_not_a_bubble`). The
  budget-one recognizer of the control environment is not the equivalence
  closure of any relation, because it relates `a` to `b` and `b` to `c` but not
  `a` to `c`; the two-step receipt is accepted exactly from budget two
  (`Controls.two_step_receipt`).

A conversion relation alone therefore does not determine a budgeted checker:
the budget is a grading of the receipts, additive under transitivity.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Megalodon.ReductionBubbleElaboration

open Mettapedia.Languages.Megalodon.MathdataKernel
open Mettapedia.Languages.Megalodon.ConversionElaboration
open Mettapedia.Languages.Megalodon.FuelledConversionWitness
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.BubbleConversion
open Mettapedia.TypeTheory.BubbleElaboration

/-! ## The bubble and its receipts -/

/-- One fibre of Mathdata terms, one bubble, and as declared steps the
reduction steps whose article the definition-conversion kernel accepts. -/
abbrev bubbles (declarations : List TermDecl) : Bubbles.{0, 0, 0, 0} Unit where
  State _ := Tm
  Bubble := Unit
  Step _ {_} source target :=
    {step : ConversionElaboration.Step //
      step.source = source ∧ step.target = target ∧ step.Valid declarations}

/-- Signed paths of checked reduction articles between two terms. -/
abbrev checkedPaths (declarations : List TermDecl) :
    (bubbles declarations).GlobalEquality.{0, 0, 0, 0, 0} where
  Eq source target := {edges : List Edge // checkPath declarations source target edges = true}
  refl _ := ⟨[], decide_eq_true rfl⟩
  symm receipt :=
    ⟨receipt.1.reverse.map Edge.flip, checkPath_reverse declarations _ _ receipt.1 receipt.2⟩
  trans first second :=
    ⟨first.1 ++ second.1, checkPath_append declarations _ _ _ first.1 second.1 first.2 second.2⟩

/-- A declared step is the one-edge path of its own article. -/
def justify (declarations : List TermDecl) {source target : Tm}
    (step : (bubbles declarations).Step () (index := ()) source target) :
    (checkedPaths declarations).Eq (index := ()) source target :=
  ⟨[⟨step.1, false⟩], by
    obtain ⟨reduction, sourceEq, targetEq, valid⟩ := step
    have edgeChecked : checkEdge declarations ⟨reduction, false⟩ = true := valid
    subst sourceEq targetEq
    simp only [checkPath, Edge.source, Edge.target, Bool.false_eq_true, if_false,
      edgeChecked, decide_true, Bool.and_self]⟩

/-- The explicit receipt of a conversion tree of the bubble. -/
def elaborate (declarations : List TermDecl) {source target : Tm}
    (path : (bubbles declarations).Conv () (index := ()) source target) :
    (checkedPaths declarations).Eq (index := ()) source target :=
  (bubbles declarations).sound (checkedPaths declarations) (justify declarations) path

/-- **Every elaborated path is accepted by the edge checker.** -/
theorem elaborate_checked (declarations : List TermDecl) {source target : Tm}
    (path : (bubbles declarations).Conv () (index := ()) source target) :
    checkPath declarations source target (elaborate declarations path).1 = true :=
  (elaborate declarations path).2

/-- **The endpoints of every tree are related by checked reductions.** -/
theorem elaborate_sound (declarations : List TermDecl) {source target : Tm}
    (path : (bubbles declarations).Conv () (index := ()) source target) :
    Conversion declarations source target :=
  checkPath_sound declarations source target _ (elaborate_checked declarations path)

/-! ## The grade is the recorded work -/

/-- Forgetting a path to its number of edges preserves the three operations. -/
def lengthMap (declarations : List TermDecl) :
    EqualityHom (Hom.identity (bubbles declarations)) (checkedPaths declarations)
      (countEquality (bubbles declarations)) where
  map receipt := receipt.1.length
  map_refl _ := rfl
  map_symm receipt := by
    change (receipt.1.reverse.map Edge.flip).length = receipt.1.length
    rw [List.length_map, List.length_reverse]
  map_trans first second := by
    change (first.1 ++ second.1).length = first.1.length + second.1.length
    rw [List.length_append]

/-- **The number of edges of an elaborated path is the number of declared
steps of its tree.** -/
theorem elaborate_length (declarations : List TermDecl) {source target : Tm}
    (path : (bubbles declarations).Conv () (index := ()) source target) :
    (elaborate declarations path).1.length = stepCount path := by
  have natural := sound_natural (Hom.identity (bubbles declarations)) (lengthMap declarations) ()
    (justify declarations) (fun _ => (1 : ℕ)) (fun _ => rfl) path
  rw [← sound_count (bubbles declarations) path]
  exact natural.symm.trans (congrArg
    (fun tree : (bubbles declarations).Conv () (index := ()) source target =>
      (bubbles declarations).sound (countEquality (bubbles declarations)) (fun _ => (1 : ℕ)) tree)
    (Hom.mapConv_identity () path))

/-- **The bounded witness checker accepts an elaborated path exactly from the
budget equal to the recorded work.** -/
theorem elaborate_bounded (declarations : List TermDecl) (budget : ℕ) {source target : Tm}
    (path : (bubbles declarations).Conv () (index := ()) source target) :
    checkBounded declarations budget source target (elaborate declarations path).1 = some true ↔
      stepCount path ≤ budget := by
  rw [bounded_accepted_iff, elaborate_length]
  exact ⟨fun accepted => accepted.1, fun fits => ⟨fits, elaborate_checked declarations path⟩⟩

/-- **Fuelled search produces graded receipts.** A path found by the bounded
definition search is a receipt of the checked-path equality within the
search budget. -/
theorem seek_receipt (environment : Environment) (budget : ℕ) (source target : Tm)
    (edges : List Edge) (found : seek environment budget source target = .found edges) :
    ∃ receipt : (checkedPaths environment.terms).Eq (index := ()) source target,
      receipt.1 = edges ∧ receipt.1.length ≤ budget :=
  let sound := seek_sound environment budget source target edges found
  ⟨⟨edges, sound.2⟩, rfl, sound.1⟩

/-! ## Controls -/

namespace Controls

open FuelledConversionWitness.Controls

/-- The checked unfolding of `a` to `b` in the control environment. -/
def unfoldA : (bubbles environment.terms).Step () (index := ()) (.named "a") (.named "b") :=
  ⟨deltaStep environment.terms "a" .prop (.named "b"), rfl, rfl,
    deltaStep_valid environment.terms (by rfl)⟩

/-- The checked unfolding of `b` to `c` in the control environment. -/
def unfoldB : (bubbles environment.terms).Step () (index := ()) (.named "b") (.named "c") :=
  ⟨deltaStep environment.terms "b" .prop (.named "c"), rfl, rfl,
    deltaStep_valid environment.terms (by rfl)⟩

/-- The two-step tree from `a` to `c`. -/
def twoSteps : (bubbles environment.terms).Conv () (index := ()) (.named "a") (.named "c") :=
  .trans (.step unfoldA) (.step unfoldB)

/-- **The two-step receipt is accepted exactly from budget two.** -/
theorem two_step_receipt :
    stepCount twoSteps = 2 ∧
      checkBounded environment.terms 2 (.named "a") (.named "c")
          (elaborate environment.terms twoSteps).1 = some true ∧
      checkBounded environment.terms 1 (.named "a") (.named "c")
          (elaborate environment.terms twoSteps).1 ≠ some true := by
  have work : stepCount twoSteps = 2 := by
    simp only [twoSteps, stepCount_trans, stepCount_step]
  refine ⟨work, (elaborate_bounded environment.terms 2 twoSteps).2 (by rw [work]),
    fun accepted => ?_⟩
  have fits := (elaborate_bounded environment.terms 1 twoSteps).1 accepted
  rw [work] at fits
  omega

/-- **A fixed budget is not a bubble.** No relation has the budget-one
recognizer of the control environment as its equivalence closure: the
recognizer relates `a` to `b` and `b` to `c` at budget one, but not `a` to
`c`. -/
theorem budget_one_not_a_bubble (relation : Tm → Tm → Prop) :
    ¬ ∀ left right, recognizes environment 1 left right = true ↔
      Relation.EqvGen relation left right := by
  intro presents
  have first := (presents _ _).1 first_at_one
  have second := (presents _ _).1 second_at_one
  have composite := (presents (.named "a") (.named "c")).2 (Relation.EqvGen.trans _ _ _ first second)
  rw [composite_not_at_one] at composite
  cases composite

end Controls

/-! ## Axiom audit -/

#print axioms elaborate_checked
#print axioms elaborate_sound
#print axioms elaborate_length
#print axioms elaborate_bounded
#print axioms seek_receipt
#print axioms Controls.two_step_receipt
#print axioms Controls.budget_one_not_a_bubble

end Mettapedia.Languages.Megalodon.ReductionBubbleElaboration
