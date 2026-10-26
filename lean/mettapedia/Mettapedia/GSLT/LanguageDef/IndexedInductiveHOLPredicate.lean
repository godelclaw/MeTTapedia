import Mettapedia.GSLT.LanguageDef.IndexedInductiveHOLFacts
import Mettapedia.Logic.HOL.PredicateFixedPoint
import Mettapedia.Logic.HOL.PolynomialPredicate
import Mettapedia.Logic.HOL.Semantics.ModelPropertySoundness
import Mettapedia.Logic.HOL.Semantics.PointedPredicate
import Mettapedia.Logic.HOL.Semantics.IndexedPolynomialPredicate
import Mettapedia.TypeTheory.IndexedPolynomialNaturalSlotRepresentation
import Mettapedia.Logic.HOL.Embedding.RelativizedCarrier
import Mathlib.Logic.Equiv.Option

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

def model : HenkinModel.{0, 0, 0} Unit PolynomialPredicate.OperatorSignature.Const :=
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
    (PredicateFixedPoint.fixed_point_schema (Const := PolynomialPredicate.OperatorSignature.Const) PolynomialPredicate.OperatorSignature.element).erase
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

/-! The same retained pointed-predicate syntax has a guarded interpretation
at every admitted first-order family. Its carrier admits an absent point,
while its presence predicate recovers exactly the actual tagged source.
This semantic equivalence does not construct native relation definitions or
an executable inverse. -/

namespace Mettapedia.GSLT.LanguageDef.IndexedInductive.HOLFacts.PolynomialPredicateInterpretation.Pointed
open Mettapedia.TypeTheory.IndexedPolynomial.Description
open Mettapedia.Logic.HOL
variable {I : Interface.{0}} {context : List I.SortCode}
variable (admitted : Admitted I context) (environment : Env I.Value context)

abbrev rawTy : Ty Base := PointedPredicate.Carrier sourceTy

def predicateSyntax : ClosedTerm Const (rawTy ⇒ .prop) :=
  PointedPredicate.predicate (PredicateFixedPoint.least operatorSyntax)

abbrev GuardedCarrier :=
  {value : Ty.denote (model admitted environment).Carrier rawTy //
    ((model admitted environment).denote predicateSyntax (emptyValuation admitted environment) value).down}

def sourceRefinementEquiv :
    {point : PredicateInterpretation.Carrier admitted environment // member admitted environment point} ≃
      Source admitted environment :=
  (Equiv.subtypeEquiv Equiv.ulift (by
    intro point
    rw [member_iff_valid]
    cases point with
    | up value => cases value <;> simp [Embedding.RelativizedCarrier.Valid])).trans
      (Embedding.RelativizedCarrier.carrierEquiv _)

/-- The inverse is semantic; no source constructor decoder is generated. -/
noncomputable def carrierEquivalence :
    GuardedCarrier admitted environment ≃ Option (Source admitted environment) :=
  (PointedPredicate.Semantics.denotationEquivalence (model admitted environment)
    (fun _ _ => trivial) (PredicateFixedPoint.least operatorSyntax)
    (emptyValuation admitted environment)).symm.trans
      (Equiv.optionCongr (sourceRefinementEquiv admitted environment))

def Presence (value : GuardedCarrier admitted environment) : Prop :=
  PointedPredicate.Semantics.Present (member admitted environment) value.val

def presenceSyntax : Formula Const [rawTy] :=
  PointedPredicate.present (weaken (PredicateFixedPoint.least operatorSyntax)) (.var .vz)

theorem presence_denotation (value : GuardedCarrier admitted environment) :
    ((model admitted environment).denote presenceSyntax
      ((model admitted environment).extend (emptyValuation admitted environment) value.val)).down ↔
        Presence admitted environment value := by
  rw [presenceSyntax, PointedPredicate.Semantics.denote_present (model admitted environment) (fun _ _ => trivial)]
  simp only [Soundness.denote_weaken, HenkinModel.denote, PreModel.denote, PreModel.extend]
  rfl

theorem presence_iff_source (value : GuardedCarrier admitted environment) :
    Presence admitted environment value ↔ ∃ source : Source admitted environment,
      value.val = PointedPredicate.Semantics.encode (ULift.up (some source)) := by
  constructor
  · rintro ⟨point, inside, same⟩
    have valid := (member_iff_valid admitted environment point).mp inside
    cases point with
    | up point =>
      cases point with
      | none => cases valid
      | some source => exact ⟨source, same⟩
  · rintro ⟨source, same⟩
    exact ⟨.up (some source), (member_iff_valid admitted environment _).mpr rfl, same⟩

def absent : GuardedCarrier admitted environment :=
  ⟨PointedPredicate.Semantics.absent _,
    (PointedPredicate.Semantics.denote_predicate (model admitted environment)
      (fun _ _ => trivial) (PredicateFixedPoint.least operatorSyntax)
      (emptyValuation admitted environment) _).mpr (.inl rfl)⟩

theorem absent_not_present : ¬ Presence admitted environment (absent admitted environment) :=
  PointedPredicate.Semantics.absent_not_present _

namespace Controls
open IndexedInductiveNatVec

theorem empty_carrier_inhabited : Nonempty (GuardedCarrier InhabitanceBoundary.recursiveOnly PUnit.unit) :=
  ⟨absent _ _⟩

theorem empty_no_present (value : GuardedCarrier InhabitanceBoundary.recursiveOnly PUnit.unit) :
    ¬ Presence InhabitanceBoundary.recursiveOnly PUnit.unit value := by
  intro claimed
  obtain ⟨source, _⟩ := (presence_iff_source _ _ value).mp claimed
  exact InhabitanceBoundary.source_empty.false source

def naturalTwo : GuardedCarrier Natural.admitted PUnit.unit :=
  ⟨PointedPredicate.Semantics.encode PredicateInterpretation.Controls.naturalTwo,
    (PointedPredicate.Semantics.denote_predicate (model Natural.admitted PUnit.unit)
      (fun _ _ => trivial) (PredicateFixedPoint.least operatorSyntax)
      (emptyValuation Natural.admitted PUnit.unit) _).mpr
      (.inr ⟨_, PolynomialPredicateInterpretation.Controls.natural_two_member, rfl⟩)⟩

theorem natural_two_present : Presence Natural.admitted PUnit.unit naturalTwo :=
  ⟨_, PolynomialPredicateInterpretation.Controls.natural_two_member, rfl⟩

theorem natural_two_not_absent : naturalTwo ≠ absent Natural.admitted PUnit.unit := by
  intro same
  exact absent_not_present _ _ (same ▸ natural_two_present)

def naturalSourceRefinementEquiv :
    {point : PredicateInterpretation.Carrier Natural.admitted PUnit.unit //
      member Natural.admitted PUnit.unit point} ≃ Source Natural.admitted PUnit.unit :=
  sourceRefinementEquiv Natural.admitted PUnit.unit

noncomputable def naturalCarrierEquivalence :
    GuardedCarrier Natural.admitted PUnit.unit ≃ Option (Source Natural.admitted PUnit.unit) :=
  carrierEquivalence Natural.admitted PUnit.unit

theorem natural_presence_denotation :
    ((model Natural.admitted PUnit.unit).denote presenceSyntax
      ((model Natural.admitted PUnit.unit).extend
        (emptyValuation Natural.admitted PUnit.unit) naturalTwo.val)).down ↔
      Presence Natural.admitted PUnit.unit naturalTwo :=
  presence_denotation Natural.admitted PUnit.unit naturalTwo

theorem natural_presence_iff_source :
    Presence Natural.admitted PUnit.unit naturalTwo ↔ ∃ source : Source Natural.admitted PUnit.unit,
      naturalTwo.val = PointedPredicate.Semantics.encode (ULift.up (some source)) :=
  presence_iff_source Natural.admitted PUnit.unit naturalTwo

end Controls
#print axioms sourceRefinementEquiv
#print axioms carrierEquivalence
#print axioms presence_denotation
#print axioms presence_iff_source
#print axioms absent_not_present
#print axioms Controls.empty_carrier_inhabited
#print axioms Controls.empty_no_present
#print axioms Controls.natural_two_present
end Mettapedia.GSLT.LanguageDef.IndexedInductive.HOLFacts.PolynomialPredicateInterpretation.Pointed

/-! Typed operations and explicit owner guards define the constructor/child
relations used above. Tagged recursive positions retain their original layer
and family index. The operation interpretation is semantic; the native data
representation of those operations remains a separate obligation. -/

namespace Mettapedia.GSLT.LanguageDef.IndexedInductive.HOLFacts.PolynomialPredicateInterpretation.Operations
open Mettapedia.TypeTheory.IndexedPolynomial.Description
open Mettapedia.Logic.HOL
variable {I : Interface.{0}} {context : List I.SortCode}
variable (admitted : Admitted I context) (environment : Env I.Value context)

abbrev Position := Σ layer : Layer admitted environment, admitted.polynomial.Position layer.2.1
abbrev PositionCarrier := ULift.{1} (Option (Position admitted environment))

def validLayer (layer : LayerCarrier admitted environment) : Prop := layer.down.isSome

def build (layer : LayerCarrier admitted environment) : PredicateInterpretation.Carrier admitted environment :=
  .up (layer.down.map Interpretation.constructSource)

def validPosition (layer : LayerCarrier admitted environment) (position : PositionCarrier admitted environment) : Prop :=
  match position.down with
  | none => False
  | some point => layer.down = some point.1

def childAt (_layer : LayerCarrier admitted environment) (position : PositionCarrier admitted environment) :
    PredicateInterpretation.Carrier admitted environment :=
  match position.down with
  | none => .up none
  | some point => PredicateInterpretation.child admitted environment point.1 point.2

theorem constructs_iff (layer : LayerCarrier admitted environment)
    (point : PredicateInterpretation.Carrier admitted environment) :
    constructs admitted environment layer point ↔
      validLayer admitted environment layer ∧ point = build admitted environment layer := by
  cases layer with
  | up layer =>
    cases point with
    | up point =>
      cases layer <;> simp [constructs, validLayer, build]

theorem child_iff (layer : LayerCarrier admitted environment)
    (point : PredicateInterpretation.Carrier admitted environment) :
    child admitted environment layer point ↔
      ∃ position, validPosition admitted environment layer position ∧
        point = childAt admitted environment layer position := by
  constructor
  · rintro ⟨actual, position, layerEq, same⟩
    exact ⟨.up (some ⟨actual, position⟩), layerEq, same⟩
  · rintro ⟨⟨position⟩, valid, same⟩
    cases position with
    | none => exact valid.elim
    | some position =>
      rcases position with ⟨actual, position⟩
      exact ⟨actual, position, valid, same⟩

inductive Base where
  | source | layer | position
abbrev sourceTy : Ty Base := .base .source
abbrev layerTy : Ty Base := .base .layer
abbrev positionTy : Ty Base := .base .position

inductive Const : Ty Base → Type where
  | validLayer : Const (layerTy ⇒ .prop)
  | build : Const (layerTy ⇒ sourceTy)
  | validPosition : Const (layerTy ⇒ positionTy ⇒ .prop)
  | childAt : Const (layerTy ⇒ positionTy ⇒ sourceTy)

def carrier : Base → Type 1
  | .source => PredicateInterpretation.Carrier admitted environment
  | .layer => LayerCarrier admitted environment
  | .position => PositionCarrier admitted environment

def model : HenkinModel.{0, 0, 0} Base Const :=
  .standard (carrier admitted environment) (fun symbol => match symbol with
    | .validLayer => fun layer => .up (validLayer admitted environment layer)
    | .build => build admitted environment
    | .validPosition => fun layer position => .up (validPosition admitted environment layer position)
    | .childAt => childAt admitted environment)

def emptyValuation : (model admitted environment).Valuation [] := fun impossible => nomatch impossible

def constructorSyntax : ClosedTerm Const (layerTy ⇒ sourceTy ⇒ .prop) :=
  PolynomialPredicate.Relations.constructorRelation (.const .validLayer) (.const .build)

def childSyntax : ClosedTerm Const (layerTy ⇒ sourceTy ⇒ .prop) :=
  PolynomialPredicate.Relations.childRelation (.const .validPosition) (.const .childAt)

theorem denote_constructor (layer : LayerCarrier admitted environment)
    (point : PredicateInterpretation.Carrier admitted environment) :
    ((model admitted environment).denote constructorSyntax (emptyValuation admitted environment) layer point).down ↔
      constructs admitted environment layer point := by
  exact (constructs_iff admitted environment layer point).symm

theorem denote_child (layer : LayerCarrier admitted environment)
    (point : PredicateInterpretation.Carrier admitted environment) :
    ((model admitted environment).denote childSyntax (emptyValuation admitted environment) layer point).down ↔
      child admitted environment layer point := by
  change (∃ position, True ∧ validPosition admitted environment layer position ∧
    point = childAt admitted environment layer position) ↔ _
  simp only [true_and]
  exact (child_iff admitted environment layer point).symm


def operatorSyntax : ClosedTerm Const (PredicateFixedPoint.Operator sourceTy) :=
  PolynomialPredicate.operator constructorSyntax childSyntax

theorem denote_operator
    (property : PredicateInterpretation.Carrier admitted environment → ULift.{1} Prop)
    (point : PredicateInterpretation.Carrier admitted environment) :
    ((model admitted environment).denote operatorSyntax
      (emptyValuation admitted environment) property point).down ↔
      PredicateInterpretation.step admitted environment (fun value => (property value).down) point := by
  change (∃ layer, True ∧
    (validLayer admitted environment layer ∧ point = build admitted environment layer) ∧
    ∀ candidate, True →
      (∃ position, True ∧ validPosition admitted environment layer position ∧
        candidate = childAt admitted environment layer position) →
      (property candidate).down) ↔ _
  simp only [true_and, true_implies]
  simp_rw [← constructs_iff admitted environment, ← child_iff admitted environment]
  constructor
  · rintro ⟨layer, ⟨actual, sameLayer, samePoint⟩, children⟩
    exact ⟨actual, samePoint, fun position =>
      children _ ⟨actual, position, sameLayer, rfl⟩⟩
  · rintro ⟨actual, samePoint, children⟩
    refine ⟨.up (some actual), ⟨actual, rfl, samePoint⟩, ?_⟩
    rintro candidate ⟨other, position, sameLayer, sameChild⟩
    have equal : actual = other := Option.some.inj sameLayer
    cases equal
    rw [sameChild]
    exact children position

#print axioms denote_operator

theorem absent_layer_refused (point : PredicateInterpretation.Carrier admitted environment) :
    ¬ constructs admitted environment (.up none) point := by
  rw [constructs_iff]
  simp [validLayer]

theorem absent_position_refused (layer : LayerCarrier admitted environment) :
    ¬ validPosition admitted environment layer (.up none) := by
  exact id

theorem wrong_owner_refused (first second : Layer admitted environment)
    (position : admitted.polynomial.Position second.2.1) (different : first ≠ second) :
    ¬ validPosition admitted environment (.up (some first)) (.up (some ⟨second, position⟩)) := by
  intro same
  exact different (Option.some.inj same)

theorem erasing_layer_guard_admits_absence :
    (build admitted environment (.up none) = (.up none)) ∧
      ¬ constructs admitted environment (.up none) (.up none) :=
  ⟨rfl, absent_layer_refused admitted environment _⟩

#print axioms constructs_iff
#print axioms child_iff
#print axioms denote_constructor
#print axioms denote_child
#print axioms wrong_owner_refused
#print axioms erasing_layer_guard_admits_absence


namespace Controls
open IndexedInductiveNatVec

def zeroLayer : Layer Natural.admitted PUnit.unit :=
  ⟨(), Mettapedia.TypeTheory.IndexedPolynomial.Fix.out Natural.polynomial Natural.zero⟩

def successorLayer : Layer Natural.admitted PUnit.unit :=
  ⟨(), Mettapedia.TypeTheory.IndexedPolynomial.Fix.out Natural.polynomial (Natural.succ Natural.zero)⟩

def successorPosition : Position Natural.admitted PUnit.unit := ⟨successorLayer, none⟩

theorem natural_constructs :
    constructs Natural.admitted PUnit.unit (.up (some successorLayer))
      (build Natural.admitted PUnit.unit (.up (some successorLayer))) :=
  (constructs_iff _ _ _ _).mpr ⟨rfl, rfl⟩

theorem natural_child :
    child Natural.admitted PUnit.unit (.up (some successorLayer))
      (childAt Natural.admitted PUnit.unit (.up (some successorLayer)) (.up (some successorPosition))) :=
  (child_iff _ _ _ _).mpr ⟨.up (some successorPosition), rfl, rfl⟩

theorem natural_constructor_denotation :
    ((model Natural.admitted PUnit.unit).denote constructorSyntax (emptyValuation Natural.admitted PUnit.unit)
      (.up (some successorLayer)) (build Natural.admitted PUnit.unit (.up (some successorLayer)))).down :=
  (denote_constructor _ _ _ _).mpr natural_constructs

theorem natural_child_denotation :
    ((model Natural.admitted PUnit.unit).denote childSyntax (emptyValuation Natural.admitted PUnit.unit)
      (.up (some successorLayer))
      (childAt Natural.admitted PUnit.unit (.up (some successorLayer)) (.up (some successorPosition)))).down :=
  (denote_child _ _ _ _).mpr natural_child

theorem natural_wrong_owner_refused :
    ¬ validPosition Natural.admitted PUnit.unit (.up (some zeroLayer)) (.up (some successorPosition)) := by
  apply wrong_owner_refused
  intro same
  have indexes := congrArg (fun value : Layer Natural.admitted PUnit.unit => value.2.1.1.val) same
  change (0 : Nat) = 1 at indexes
  omega

theorem natural_guard_required :
    (build Natural.admitted PUnit.unit (.up none) = (.up none)) ∧
      ¬ constructs Natural.admitted PUnit.unit (.up none) (.up none) :=
  erasing_layer_guard_admits_absence _ _


theorem natural_operator_denotation :
    ((model Natural.admitted PUnit.unit).denote operatorSyntax
      (emptyValuation Natural.admitted PUnit.unit)
      (fun point => .up point.down.isSome)
      (build Natural.admitted PUnit.unit (.up (some successorLayer)))).down ↔
    PredicateInterpretation.step Natural.admitted PUnit.unit
      (fun point => point.down.isSome)
      (build Natural.admitted PUnit.unit (.up (some successorLayer))) :=
  denote_operator Natural.admitted PUnit.unit _ _

end Controls

end Mettapedia.GSLT.LanguageDef.IndexedInductive.HOLFacts.PolynomialPredicateInterpretation.Operations

/-! ## Admitted-family clients of the raw-tree HOL interpretation -/
namespace Mettapedia.GSLT.LanguageDef.IndexedInductive.HOLFacts.RawPredicateInterpretation.Controls
open Mettapedia.Logic.HOL.PolynomialPredicate.RawInterpretation
open Mettapedia.TypeTheory.IndexedPolynomial
abbrev naturalPositions := Description.naturalSlots IndexedInductiveNatVec.Natural.constructors
noncomputable def naturalTwo : Carrier IndexedInductiveNatVec.Natural.polynomial naturalPositions PUnit.unit :=
  sourcePoint IndexedInductiveNatVec.Natural.polynomial naturalPositions PUnit.unit ()
    (IndexedInductiveNatVec.Natural.succ (IndexedInductiveNatVec.Natural.succ IndexedInductiveNatVec.Natural.zero))

theorem natural_two_member : member IndexedInductiveNatVec.Natural.polynomial naturalPositions PUnit.unit naturalTwo :=
  sourcePoint_member IndexedInductiveNatVec.Natural.polynomial naturalPositions PUnit.unit () _

theorem natural_absent_tree_refused :
    ¬ member IndexedInductiveNatVec.Natural.polynomial naturalPositions PUnit.unit
      (.up (some ⟨(), GuardedRaw.absent IndexedInductiveNatVec.Natural.polynomial naturalPositions PUnit.unit⟩)) :=
  absent_tree_not_member IndexedInductiveNatVec.Natural.polynomial naturalPositions PUnit.unit ()


private abbrev naturalPolynomial := IndexedInductiveNatVec.Natural.polynomial

def zeroShape : naturalPolynomial.Shape PUnit.unit () := by
  refine ⟨⟨0, by decide⟩, ?_⟩
  change ULift (PLift (() = ()))
  exact ⟨⟨rfl⟩⟩

def succShape : naturalPolynomial.Shape PUnit.unit () := by
  refine ⟨⟨1, by decide⟩, ?_⟩
  change ULift (PLift (() = ()))
  exact ⟨⟨rfl⟩⟩

def zeroRaw : GuardedRaw.Tree naturalPolynomial naturalPositions PUnit.unit :=
  .roll (some ⟨(), zeroShape⟩) (fun _ => GuardedRaw.absent naturalPolynomial naturalPositions PUnit.unit)

theorem zero_valid : GuardedRaw.Valid naturalPolynomial naturalPositions zeroRaw () := by
  refine ⟨rfl, ?_, ?_⟩
  · intro slot missing
    rfl
  · intro impossible
    exact PEmpty.elim impossible

def hiddenTailSuccessor : GuardedRaw.Tree naturalPolynomial naturalPositions PUnit.unit :=
  .roll (some ⟨(), succShape⟩) (fun _ => zeroRaw)

theorem hidden_tail_children_valid (position : naturalPolynomial.Position succShape) :
    GuardedRaw.Valid naturalPolynomial naturalPositions zeroRaw (naturalPolynomial.next succShape position) := by
  have same : naturalPolynomial.next succShape position = () := Subsingleton.elim (α := Unit) _ _
  rw [same]
  exact zero_valid

theorem zero_not_absent : zeroRaw ≠ GuardedRaw.absent naturalPolynomial naturalPositions PUnit.unit := by
  intro same
  have incompatible := congrArg
    (fun tree => (Fix.out (GuardedRaw.polynomial naturalPolynomial naturalPositions) tree).1) same
  cases incompatible

theorem hidden_tail_refused : ¬ GuardedRaw.Valid naturalPolynomial naturalPositions hiddenTailSuccessor () := by
  intro indexed
  have missing : (naturalPositions.coding succShape).decode (1 : Nat) = none := rfl
  exact zero_not_absent (indexed.2.1 (1 : Nat) missing)

theorem natural_representation_roundtrip :
    ((Description.naturalSlotRepresentation IndexedInductiveNatVec.Natural.constructors).toEquiv PUnit.unit ()).symm
      ((Description.naturalSlotRepresentation IndexedInductiveNatVec.Natural.constructors).toEquiv PUnit.unit ()
        (IndexedInductiveNatVec.Natural.succ (IndexedInductiveNatVec.Natural.succ IndexedInductiveNatVec.Natural.zero))) =
      IndexedInductiveNatVec.Natural.succ (IndexedInductiveNatVec.Natural.succ IndexedInductiveNatVec.Natural.zero) :=
  ((Description.naturalSlotRepresentation IndexedInductiveNatVec.Natural.constructors).toEquiv PUnit.unit ()).symm_apply_apply _

theorem hidden_tail_not_member :
    ¬ member naturalPolynomial naturalPositions PUnit.unit (.up (some ⟨(), hiddenTailSuccessor⟩)) :=
  fun present => hidden_tail_refused ((member_iff_valid naturalPolynomial naturalPositions PUnit.unit _).mp present)

def naturalSlotVerdicts : List (String × Bool) :=
  [("natural.zero.no-slot", ((naturalPositions.coding zeroShape).decode (0 : Nat)).isNone),
   ("natural.successor.slot-zero", ((naturalPositions.coding succShape).decode (0 : Nat)).isSome),
   ("natural.successor.outside-refused", ((naturalPositions.coding succShape).decode (1 : Nat)).isNone),
   ("natural.successor.slot-roundtrip", match (naturalPositions.coding succShape).decode (0 : Nat) with
      | none => false
      | some position => Nat.beq ((naturalPositions.coding succShape).encode position) 0)]

end Mettapedia.GSLT.LanguageDef.IndexedInductive.HOLFacts.RawPredicateInterpretation.Controls

#print axioms Mettapedia.GSLT.LanguageDef.IndexedInductive.HOLFacts.RawPredicateInterpretation.Controls.natural_two_member
#print axioms Mettapedia.GSLT.LanguageDef.IndexedInductive.HOLFacts.RawPredicateInterpretation.Controls.natural_absent_tree_refused
