import Mettapedia.GSLT.LanguageDef.IndexedInductiveHOLFacts
import Mettapedia.Logic.HOL.GuardedRetraction
import Mettapedia.Logic.HOL.Semantics.ModelPropertySoundness

/-!
# Guarded constructor retractions for admitted indexed families

The actual polynomial constructor layer and the selected family interpretation
give a constructor/destructor retraction. Strict Option lifting supplies
inhabited target carriers while a source-validity predicate retains the
possibly empty original layer. The two sorts and all three operations are
interpreted in one standard HOL model at the same admitted signature/environment.

This constructs the semantic premise of the guarded retraction inference.
A native proof of each datatype's definition/retraction law remains a separate
obligation; validity in this model is not a native checker receipt.
-/

set_option autoImplicit false
namespace Mettapedia.GSLT.LanguageDef.IndexedInductive.HOLFacts.Retraction
open Mettapedia.TypeTheory.IndexedPolynomial.Description
open Mettapedia.Logic.HOL
variable {I : Interface.{0}} {context : List I.SortCode}
variable {admitted : Admitted I context} {environment : Env I.Value context}

def out (interpretation : Interpretation admitted environment) (value : interpretation.Carrier) :
    Layer admitted environment :=
  Interpretation.outSource (interpretation.sourceEquiv.symm value)

@[simp] theorem out_construct (interpretation : Interpretation admitted environment)
    (layer : Layer admitted environment) : out interpretation (interpretation.construct layer) = layer := by
  simp only [out, Interpretation.construct, Equiv.symm_apply_apply, Interpretation.outSource_constructSource]

def pointedConstruct (interpretation : Interpretation admitted environment) :
    Option (Layer admitted environment) → Option interpretation.Carrier := Option.map interpretation.construct

def pointedOut (interpretation : Interpretation admitted environment) :
    Option interpretation.Carrier → Option (Layer admitted environment) := Option.map (out interpretation)

def valid (value : Option (Layer admitted environment)) : Prop := value.isSome

theorem roundtrip (interpretation : Interpretation admitted environment)
    (value : Option (Layer admitted environment)) : pointedOut interpretation (pointedConstruct interpretation value) = value := by
  cases value with
  | none => rfl
  | some layer => simp only [pointedOut, pointedConstruct, Option.map_some, out_construct]

theorem pointed_injective (interpretation : Interpretation admitted environment) :
    Function.Injective (pointedConstruct interpretation) :=
  Function.LeftInverse.injective (roundtrip interpretation)

inductive Base where
  | layer | source
  deriving DecidableEq, Repr

abbrev layerTy : Ty Base := .base .layer
abbrev sourceTy : Ty Base := .base .source

inductive Const : Ty Base → Type where
  | construct : Const (layerTy ⇒ sourceTy)
  | out : Const (sourceTy ⇒ layerTy)
  | valid : Const (layerTy ⇒ .prop)

def carrier (interpretation : Interpretation admitted environment) : Base → Type 1
  | .layer => ULift.{1} (Option (Layer admitted environment))
  | .source => Option interpretation.Carrier

def constants (interpretation : Interpretation admitted environment) :
    {type : Ty Base} → Const type → Ty.denote.{0, 0} (carrier interpretation) type
  | _, .construct => fun value => pointedConstruct interpretation value.down
  | _, .out => fun value => ⟨pointedOut interpretation value⟩
  | _, .valid => fun value => ⟨valid value.down⟩

def model (interpretation : Interpretation admitted environment) : HenkinModel.{0, 0, 0} Base Const :=
  HenkinModel.standard (carrier interpretation) (constants interpretation)

theorem full_domains (interpretation : Interpretation admitted environment) : (model interpretation).FullDomains :=
  HenkinModel.fullDomains_standard _ _

theorem base_inhabited (interpretation : Interpretation admitted environment) (sort : Base) :
    Nonempty (carrier interpretation sort) := by
  cases sort with
  | layer => exact ⟨⟨none⟩⟩
  | source => exact ⟨none⟩

def retractionLaw : ClosedFormula Const :=
  GuardedRetraction.law (.const .construct) (.const .out) (.const .valid)

def noConfusion : ClosedFormula Const :=
  .all (σ := layerTy) (.all (σ := layerTy)
    (.imp (.app (.const .valid) (.var (.vs .vz)))
      (.imp (.app (.const .valid) (.var .vz))
        (.imp (.eq (.app (.const .construct) (.var (.vs .vz))) (.app (.const .construct) (.var .vz)))
          (.eq (.var (.vs .vz)) (.var .vz))))))

def noConfusionProof : ProofSyntax Const [retractionLaw] noConfusion := by
  refine .allI (.allI (.impI (.impI (.impI ?_))))
  exact GuardedRetraction.reflectEquality (.const .construct) (.const .out) (.const .valid)
    (.var (.vs .vz)) (.var .vz)
    (.hyp ⟨3, by simp [weakenHyps]⟩) (.hyp ⟨2, by simp [weakenHyps]⟩)
    (.hyp ⟨1, by simp [weakenHyps]⟩) (.hyp ⟨0, by simp [weakenHyps]⟩)

def conditionalProof : ProofSyntax Const [] (.imp retractionLaw noConfusion) :=
  .impI noConfusionProof

theorem models_retraction (interpretation : Interpretation admitted environment) :
    (model interpretation).models retractionLaw := by
  intro value _ _
  apply ULift.ext
  exact roundtrip interpretation value.down

theorem models_noConfusion (interpretation : Interpretation admitted environment) :
    (model interpretation).models noConfusion := by
  have implication := Soundness.extTheorem_sound_of_fullDomains conditionalProof.erase
    (model interpretation) (full_domains interpretation)
  exact implication (models_retraction interpretation)

namespace Controls

def naturalLayer : Layer IndexedInductiveNatVec.Natural.admitted PUnit.unit :=
  Interpretation.outSource (NaturalControl.sourceEquiv.symm ⟨IndexedInductiveNatVec.Natural.zero⟩)

theorem natural_valid : valid (some naturalLayer) := rfl

theorem natural_roundtrip :
    pointedOut NaturalControl.interpretation (pointedConstruct NaturalControl.interpretation (some naturalLayer)) =
      some naturalLayer := roundtrip NaturalControl.interpretation _

theorem natural_out_construct : out NaturalControl.interpretation
    (NaturalControl.interpretation.construct naturalLayer) = naturalLayer :=
  out_construct NaturalControl.interpretation naturalLayer

theorem natural_injective : Function.Injective (pointedConstruct NaturalControl.interpretation) :=
  pointed_injective NaturalControl.interpretation

theorem natural_full_domains : (model NaturalControl.interpretation).FullDomains :=
  full_domains NaturalControl.interpretation

theorem natural_base_inhabited : Nonempty (carrier NaturalControl.interpretation .layer) :=
  base_inhabited NaturalControl.interpretation .layer

theorem natural_models_retraction : (model NaturalControl.interpretation).models retractionLaw :=
  models_retraction NaturalControl.interpretation

theorem natural_models_noConfusion : (model NaturalControl.interpretation).models noConfusion :=
  models_noConfusion NaturalControl.interpretation

abbrev emptyAdmitted := InhabitanceBoundary.recursiveOnly
abbrev emptyEnvironment := PUnit.unit

theorem empty_guard_refuses (candidate : Option (Layer emptyAdmitted emptyEnvironment)) : ¬ valid candidate := by
  cases candidate with
  | none => simp only [valid, Option.isSome_none, Bool.false_eq_true, not_false_eq_true]
  | some layer => exact (InhabitanceBoundary.source_empty.false (Interpretation.constructSource layer)).elim

theorem empty_target_inhabited : Nonempty
    (carrier (Interpretation.tagged emptyAdmitted emptyEnvironment) .layer) := ⟨⟨none⟩⟩

end Controls

#print axioms roundtrip
#print axioms pointed_injective
#print axioms models_retraction
#print axioms models_noConfusion
#print axioms conditionalProof
#print axioms Controls.natural_roundtrip
#print axioms Controls.empty_guard_refuses
end Mettapedia.GSLT.LanguageDef.IndexedInductive.HOLFacts.Retraction
