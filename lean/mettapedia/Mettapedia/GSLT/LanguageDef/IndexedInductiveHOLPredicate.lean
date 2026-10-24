import Mettapedia.GSLT.LanguageDef.IndexedInductiveHOLFacts
import Mettapedia.Logic.HOL.PredicateFixedPoint
import Mettapedia.Logic.HOL.PolynomialPredicate
import Mettapedia.Logic.HOL.Semantics.ModelPropertySoundness

/-!
# Least-predicate interpretation of admitted indexed constructor families

The constructor operator is built from the actual polynomial layers of an
admitted first-order constructor document. Its children retain their indices.
The standard HOL carrier is the Option-lifted tagged source family, so empty
source families remain representable without assuming their inhabitance.

The least-predicate formula denotes exactly the valid, present source values.
Monotonicity follows from the actual child occurrence condition, and the
retained HOL fixed-point schema is sound in this model. The absent value and
an empty recursive-only family supply separating controls.

This is a semantic interpretation. The primitive operator reading is compared below with an actual typed
constructor/child-relation program. Neither supplies a native constructor definition; generating its datatype-specific definition and native
monotonicity/recursion certificates remains a separate obligation. Registered
nested-container extensions are not added to this first-order admission route.
-/

set_option autoImplicit false
namespace Mettapedia.GSLT.LanguageDef.IndexedInductive.HOLFacts.PredicateInterpretation
open Mettapedia.TypeTheory.IndexedPolynomial
open Mettapedia.TypeTheory.IndexedPolynomial.Description
open Mettapedia.Logic.HOL
variable {I : Interface.{0}} {context : List I.SortCode}
variable (admitted : Admitted I context) (environment : Env I.Value context)

/-- A present tagged family value, with an explicit absent point. -/
abbrev Carrier := ULift.{1} (Option (Source admitted environment))

/-- Each actual recursive position retains its required family index. -/
def child (layer : Layer admitted environment)
    (position : admitted.polynomial.Position layer.2.1) : Carrier admitted environment :=
  .up (some ⟨admitted.polynomial.next layer.2.1 position, layer.2.2 position⟩)

/-- One constructor layer whose complete recursive children satisfy the predicate. -/
def step (property : Carrier admitted environment → Prop)
    (point : Carrier admitted environment) : Prop :=
  ∃ layer : Layer admitted environment,
    point.down = some (Interpretation.constructSource layer) ∧
      ∀ position, property (child admitted environment layer position)

abbrev element : Ty Unit := .base ()
inductive Const : Ty Unit → Type where
  | operator : Const ((element ⇒ .prop) ⇒ element ⇒ .prop)

def model : HenkinModel.{0, 0, 0} Unit Const :=
  .standard (fun _ => Carrier admitted environment)
    (fun symbol => match symbol with
      | .operator => fun property point =>
          .up (step admitted environment (fun candidate => (property candidate).down) point))

def emptyValuation : (model admitted environment).Valuation [] := fun impossible => nomatch impossible

def member (point : Carrier admitted environment) : Prop :=
  ((model admitted environment).denote
    (PredicateFixedPoint.least (.const .operator))
    (emptyValuation admitted environment) point).down

theorem step_monotone (first second : Carrier admitted environment → Prop)
    (inclusion : ∀ point, first point → second point) :
    ∀ point, step admitted environment first point → step admitted environment second point := by
  intro point present
  rcases present with ⟨layer, root, children⟩
  exact ⟨layer, root, fun position => inclusion _ (children position)⟩

theorem model_monotone : (model admitted environment).models
    (PredicateFixedPoint.monotone (.const .operator)) := by
  intro first _ second _ inclusion point _ present
  exact step_monotone admitted environment _ _ (fun candidate => inclusion candidate trivial) point present

theorem closed_contains (property : Carrier admitted environment → Prop)
    (closed : ∀ point, step admitted environment property point → property point)
    (index : I.Index) (value : admitted.Family environment index) :
    property (.up (some ⟨index, value⟩)) := by
  exact @Fix.rec _ _ admitted.polynomial environment
    (fun index value => property (.up (some ⟨index, value⟩)))
    (fun {index} shape children hypotheses =>
      closed _ ⟨⟨index, shape, children⟩, rfl, hypotheses⟩) index value

/-- Induction on the actual admitted fixed family proves exact guarded coverage. -/
theorem member_iff_valid (point : Carrier admitted environment) :
    member admitted environment point ↔ point.down.isSome := by
  constructor
  · intro present
    exact present (fun candidate => .up candidate.down.isSome) trivial (by
      intro candidate _ generated
      change step admitted environment (fun value => value.down.isSome) candidate at generated
      change candidate.down.isSome = true
      rcases generated with ⟨layer, root, _⟩
      rw [root]
      rfl)
  · intro valid property _ closed
    cases point with
    | up value =>
        cases value with
        | none => cases valid
        | some source =>
            exact closed_contains admitted environment (fun candidate => (property candidate).down)
              (fun candidate generated => closed candidate trivial generated) source.1 source.2

/-- The previously retained source proof applies to this constructed operator. -/
theorem model_fixed_point : (model admitted environment).models
    (PredicateFixedPoint.equation (.const .operator)) := by
  have schema := Soundness.extTheorem_sound_of_fullDomains
    (PredicateFixedPoint.fixed_point_schema (Const := Const) element).erase
    (model admitted environment) (HenkinModel.fullDomains_standard _ _)
  exact schema
    (fun property point => .up (step admitted environment (fun candidate => (property candidate).down) point))
    trivial (model_monotone admitted environment)

theorem none_not_member : ¬ member admitted environment (.up none) := by
  intro present
  have impossible := (member_iff_valid admitted environment (.up none)).mp present
  cases impossible

namespace Controls
open IndexedInductiveNatVec

def naturalTwo : Carrier Natural.admitted PUnit.unit :=
  .up (some (NaturalControl.sourceEquiv.symm ⟨Natural.succ (Natural.succ Natural.zero)⟩))

theorem natural_two_member : member Natural.admitted PUnit.unit naturalTwo :=
  (member_iff_valid Natural.admitted PUnit.unit naturalTwo).mpr rfl

theorem natural_model_monotone : (model Natural.admitted PUnit.unit).models
    (PredicateFixedPoint.monotone (.const .operator)) :=
  model_monotone Natural.admitted PUnit.unit

theorem natural_membership : member Natural.admitted PUnit.unit naturalTwo ↔
    naturalTwo.down.isSome := member_iff_valid Natural.admitted PUnit.unit naturalTwo

theorem natural_model_fixed_point : (model Natural.admitted PUnit.unit).models
    (PredicateFixedPoint.equation (.const .operator)) :=
  model_fixed_point Natural.admitted PUnit.unit

theorem natural_none_not_member : ¬ member Natural.admitted PUnit.unit (.up none) :=
  none_not_member Natural.admitted PUnit.unit

abbrev emptyAdmitted := InhabitanceBoundary.recursiveOnly

theorem empty_no_member (point : Carrier emptyAdmitted PUnit.unit) :
    ¬ member emptyAdmitted PUnit.unit point := by
  intro present
  have valid := (member_iff_valid emptyAdmitted PUnit.unit point).mp present
  cases point with
  | up value =>
      cases value with
      | none => cases valid
      | some source => exact InhabitanceBoundary.source_empty.false source

end Controls

#print axioms model_monotone
#print axioms member_iff_valid
#print axioms model_fixed_point
#print axioms Controls.natural_two_member
#print axioms Controls.empty_no_member
end Mettapedia.GSLT.LanguageDef.IndexedInductive.HOLFacts.PredicateInterpretation


namespace Mettapedia.GSLT.LanguageDef.IndexedInductive.HOLFacts.PolynomialPredicateInterpretation
open Mettapedia.TypeTheory.IndexedPolynomial.Description
open Mettapedia.Logic.HOL
variable {I : Interface.{0}} {context : List I.SortCode}
variable (admitted : Admitted I context) (environment : Env I.Value context)

inductive Base where
  | source | layer

abbrev sourceTy : Ty Base := .base .source
abbrev layerTy : Ty Base := .base .layer

inductive Const : Ty Base → Type where
  | constructs : Const (layerTy ⇒ sourceTy ⇒ .prop)
  | child : Const (layerTy ⇒ sourceTy ⇒ .prop)

abbrev LayerCarrier := ULift.{1} (Option (Layer admitted environment))

def carrier : Base → Type 1
  | .source => PredicateInterpretation.Carrier admitted environment
  | .layer => LayerCarrier admitted environment

def constructs (layer : LayerCarrier admitted environment)
    (point : PredicateInterpretation.Carrier admitted environment) : Prop :=
  ∃ actual, layer.down = some actual ∧ point.down = some (Interpretation.constructSource actual)

def child (layer : LayerCarrier admitted environment)
    (point : PredicateInterpretation.Carrier admitted environment) : Prop :=
  ∃ actual : Layer admitted environment, ∃ position,
    layer.down = some actual ∧ point = PredicateInterpretation.child admitted environment actual position

def model : HenkinModel.{0, 0, 0} Base Const :=
  .standard (carrier admitted environment) (fun symbol => match symbol with
    | .constructs => fun layer point => .up (constructs admitted environment layer point)
    | .child => fun layer point => .up (child admitted environment layer point))

def emptyValuation : (model admitted environment).Valuation [] := fun impossible => nomatch impossible

def operatorSyntax : ClosedTerm Const (PredicateFixedPoint.Operator sourceTy) :=
  PolynomialPredicate.operator (.const .constructs) (.const .child)

theorem denote_operator
    (property : PredicateInterpretation.Carrier admitted environment → ULift.{1} Prop)
    (point : PredicateInterpretation.Carrier admitted environment) :
    ((model admitted environment).denote operatorSyntax
      (emptyValuation admitted environment) property point).down ↔
        PredicateInterpretation.step admitted environment (fun candidate => (property candidate).down) point := by
  change (∃ layer : LayerCarrier admitted environment, True ∧
    constructs admitted environment layer point ∧
      ∀ candidate, True → child admitted environment layer candidate → (property candidate).down) ↔ _
  constructor
  · rintro ⟨layer, _, ⟨actual, layerEq, root⟩, children⟩
    exact ⟨actual, root, fun position =>
      children _ trivial ⟨actual, position, layerEq, rfl⟩⟩
  · rintro ⟨actual, root, children⟩
    refine ⟨.up (some actual), trivial, ⟨actual, rfl, root⟩, ?_⟩
    rintro candidate _ ⟨other, position, sameLayer, sameChild⟩
    have same : actual = other := Option.some.inj sameLayer
    cases same
    rw [sameChild]
    exact children position

def member (point : PredicateInterpretation.Carrier admitted environment) : Prop :=
  ((model admitted environment).denote (PredicateFixedPoint.least operatorSyntax)
    (emptyValuation admitted environment) point).down

theorem member_iff_valid (point : PredicateInterpretation.Carrier admitted environment) :
    member admitted environment point ↔ point.down.isSome := by
  rw [← PredicateInterpretation.member_iff_valid admitted environment point]
  constructor
  · intro present property _ closed
    exact present property trivial (by
      intro candidate _ generated
      exact closed candidate trivial ((denote_operator admitted environment property candidate).mp generated))
  · intro present property _ closed
    exact present property trivial (by
      intro candidate _ generated
      exact closed candidate trivial ((denote_operator admitted environment property candidate).mpr generated))

namespace Controls
open IndexedInductiveNatVec

theorem natural_operator_agrees :
    ((model Natural.admitted PUnit.unit).denote operatorSyntax
      (emptyValuation Natural.admitted PUnit.unit)
      (fun candidate => .up candidate.down.isSome)
      PredicateInterpretation.Controls.naturalTwo).down ↔
        PredicateInterpretation.step Natural.admitted PUnit.unit
          (fun candidate => candidate.down.isSome) PredicateInterpretation.Controls.naturalTwo :=
  denote_operator Natural.admitted PUnit.unit _ _

theorem natural_membership :
    member Natural.admitted PUnit.unit PredicateInterpretation.Controls.naturalTwo ↔
      PredicateInterpretation.Controls.naturalTwo.down.isSome :=
  member_iff_valid Natural.admitted PUnit.unit _

theorem natural_two_member :
    member Natural.admitted PUnit.unit PredicateInterpretation.Controls.naturalTwo :=
  natural_membership.mpr rfl

theorem natural_none_not_member : ¬ member Natural.admitted PUnit.unit (.up none) := by
  intro present
  have impossible := (member_iff_valid Natural.admitted PUnit.unit (.up none)).mp present
  cases impossible

theorem empty_no_member
    (point : PredicateInterpretation.Carrier InhabitanceBoundary.recursiveOnly PUnit.unit) :
    ¬ member InhabitanceBoundary.recursiveOnly PUnit.unit point := by
  intro present
  have valid := (member_iff_valid InhabitanceBoundary.recursiveOnly PUnit.unit point).mp present
  cases point with
  | up value =>
      cases value with
      | none => cases valid
      | some source => exact InhabitanceBoundary.source_empty.false source

end Controls

#print axioms denote_operator
#print axioms member_iff_valid
#print axioms Controls.natural_two_member
#print axioms Controls.natural_none_not_member
#print axioms Controls.empty_no_member
end Mettapedia.GSLT.LanguageDef.IndexedInductive.HOLFacts.PolynomialPredicateInterpretation
