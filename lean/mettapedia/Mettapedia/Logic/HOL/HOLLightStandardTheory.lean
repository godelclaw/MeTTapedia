import Mettapedia.Logic.HOL.StandardAxiomProperties
import Mettapedia.Logic.HOL.TypeDefinitionSemantics

/-!
# A constructed model of the HOL Light standard commitments

These sentences are the Church-HOL readings of `ETA_AX`, `SELECT_AX` and
`INFINITY_AX` in HOL Light revision
`924faf0c3471a04174ffdeb8576ce7cabcb92d64`. Type polymorphism is schematic:
eta and selection range externally over all simple types. Selection is an
actual typed constant interpreted by the constructed choice operation.

This supplies the standard-theory model obligation. Source-term admission,
the source kernel and proof-artifact replay are separate interpretations.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HOL.HOLLightStandardTheory

universe u v w

abbrev Base := Unit

/-- Hilbert selection is schematic at every simple type. -/
inductive Symbol (Base : Type u) : Ty Base → Type u where
  | select (type : Ty Base) : Symbol Base ((type ⇒ .prop) ⇒ type)

abbrev Sentence := ClosedFormula (Symbol Base)

/-- The source eta axiom at the specified domain and codomain. -/
def etaFormula {Base : Type u} {Const : Ty Base → Type v}
    (domain codomain : Ty Base) : ClosedFormula Const :=
  .all (.eq (.lam (.app (.var (.vs .vz)) (.var .vz)))
    (.var .vz : Term Const [domain ⇒ codomain] (domain ⇒ codomain)))

/-- The source selection axiom, retaining the actual selected constant. -/
def selectionFormula {Base : Type u} (type : Ty Base) : ClosedFormula (Symbol Base) :=
  .all (.all (.imp
    (.app (.var (.vs .vz)) (.var .vz))
    (.app (.var (.vs .vz))
      (.app (.const (Symbol.select type)) (.var (.vs .vz))))))

/-- Infinity uses a genuine injection with an omitted point. -/
def infinityFormula : Sentence :=
  StandardAxiomProperties.infinityFormula ()

/-- The source standard axioms remain an explicit object-theory union. -/
def theory : ClosedTheorySet (Symbol Base) :=
  {sentence | (∃ domain codomain, sentence = etaFormula domain codomain) ∨
    (∃ type, sentence = selectionFormula type) ∨ sentence = infinityFormula}

private abbrev natural := HenkinModel.ModelPropertyCanary.naturalBaseModel

/-- Construct selection from the actual full carrier domains and retained
base inhabitants, independently of any proposed selection constant. -/
noncomputable def selectionOperation {B : Type u}
    (carriers : B → Type (max (u + 1) w)) (inhabitants : ∀ base, carriers base) :
    (type : Ty B) → Ty.denote carriers ((type ⇒ .prop) ⇒ type) :=
  let precursor : HenkinModel.{u, u, w} B (fun _ => ULift.{u} Empty) :=
    HenkinModel.standard carriers (fun symbol => nomatch symbol.down)
  (HenkinModel.HilbertChoice.ofFullInhabitedDomains
    (HenkinModel.fullDomains_standard carriers
      (fun (symbol : ULift.{u} Empty) => nomatch symbol.down))
    (precursor.inhabitedDomains_of_fullDomains
      (HenkinModel.fullDomains_standard _ _) inhabitants)).choose

theorem selectionOperation_specified {B : Type u}
    (carriers : B → Type (max (u + 1) w)) (inhabitants : ∀ base, carriers base)
    (type : Ty B) (predicate : Ty.denote carriers (type ⇒ .prop))
    (existsWitness : ∃ value, (predicate value).down) :
    (predicate (selectionOperation carriers inhabitants type predicate)).down := by
  let precursor : HenkinModel.{u, u, w} B (fun _ => ULift.{u} Empty) :=
    HenkinModel.standard carriers (fun symbol => nomatch symbol.down)
  let choice := HenkinModel.HilbertChoice.ofFullInhabitedDomains
    (HenkinModel.fullDomains_standard carriers
      (fun (symbol : ULift.{u} Empty) => nomatch symbol.down))
    (precursor.inhabitedDomains_of_fullDomains (HenkinModel.fullDomains_standard _ _) inhabitants)
  exact choice.specified type predicate (by trivial)
    (existsWitness.imp fun _ holds => ⟨by trivial, holds⟩)

noncomputable def selectionInterpretation {B : Type u}
    (carriers : B → Type (max (u + 1) w)) (inhabitants : ∀ base, carriers base) :
    {type : Ty B} → Symbol B type → Ty.denote carriers type
  | _, .select type => selectionOperation carriers inhabitants type

/-- The actual selected constant is installed in the common HOL model. -/
noncomputable def selectionModel {B : Type u}
    (carriers : B → Type (max (u + 1) w)) (inhabitants : ∀ base, carriers base) :
    HenkinModel.{u, u, w} B (Symbol B) :=
  HenkinModel.standard carriers (selectionInterpretation carriers inhabitants)

theorem selectionModel_fullDomains {B : Type u}
    (carriers : B → Type (max (u + 1) w)) (inhabitants : ∀ base, carriers base) :
    (selectionModel carriers inhabitants).FullDomains :=
  HenkinModel.fullDomains_standard _ _

theorem models_eta_in {B : Type u} {C : Ty B → Type v}
    (current : HenkinModel.{u, v, w} B C) (domain codomain : Ty B) :
    current.models (etaFormula domain codomain) := by
  change ∀ function, current.adm (domain ⇒ codomain) function →
    current.Eqv (domain ⇒ codomain) (fun value => function value) function
  intro function functionAdmissible value admissible
  exact current.eqv_refl (current.app_mem functionAdmissible admissible)

theorem selectionModel_models_eta {B : Type u}
    (carriers : B → Type (max (u + 1) w)) (inhabitants : ∀ base, carriers base)
    (domain codomain : Ty B) :
    (selectionModel carriers inhabitants).models (etaFormula domain codomain) :=
  models_eta_in _ _ _

theorem selectionModel_models_selection {B : Type u}
    (carriers : B → Type (max (u + 1) w)) (inhabitants : ∀ base, carriers base)
    (type : Ty B) :
    (selectionModel carriers inhabitants).models (selectionFormula type) := by
  change ∀ predicate, (selectionModel carriers inhabitants).adm (type ⇒ .prop) predicate →
    ∀ value, (selectionModel carriers inhabitants).adm type value →
      (predicate value).down →
        (predicate (selectionOperation carriers inhabitants type predicate)).down
  intro predicate _ value _ holds
  exact selectionOperation_specified carriers inhabitants type predicate ⟨value, holds⟩

noncomputable def interpret : {type : Ty Base} →
    Symbol Base type → Ty.denote.{0, 0} natural.Carrier type :=
  selectionInterpretation natural.Carrier (fun _ => ULift.up (0 : Nat))

/-- The actual infinite full-domain model, including each selection symbol. -/
noncomputable def model : HenkinModel.{0, 0, 0} Base (Symbol Base) :=
  selectionModel natural.Carrier (fun _ => ULift.up (0 : Nat))

theorem fullDomains : model.FullDomains :=
  HenkinModel.fullDomains_standard _ _

noncomputable def inhabitedDomains : model.InhabitedDomains :=
  model.inhabitedDomains_of_fullDomains fullDomains
    (fun _ => ULift.up (0 : Nat))

theorem extensional : model.FunctionsRespectEqv :=
  model.functionsRespectEqv_of_fullDomains fullDomains

def infinityWitness : model.DedekindInfinityWitness () where
  successor := HenkinModel.ModelPropertyCanary.naturalBaseModel_infinity.successor
  successor_admissible := fullDomains _ _
  successor_injective := HenkinModel.ModelPropertyCanary.naturalBaseModel_infinity.successor_injective
  omitted := HenkinModel.ModelPropertyCanary.naturalBaseModel_infinity.omitted
  omitted_not_image := HenkinModel.ModelPropertyCanary.naturalBaseModel_infinity.omitted_not_image

/-- Every simple type has its constructed admissible inhabitant. -/
theorem all_types_inhabited (type : Ty Base) :
    ∃ value, model.adm type value :=
  ⟨inhabitedDomains.witness type, inhabitedDomains.witness_admissible type⟩

theorem models_eta (domain codomain : Ty Base) :
    model.models (etaFormula domain codomain) :=
  selectionModel_models_eta _ _ _ _

theorem models_selection (type : Ty Base) :
    model.models (selectionFormula type) :=
  selectionModel_models_selection _ _ _

theorem models_infinity : model.models infinityFormula :=
  StandardAxiomProperties.models_infinityFormula model () infinityWitness

/-- Every selected standard axiom is validated by the constructed model. -/
theorem models_theory : ∀ sentence ∈ theory, model.models sentence := by
  intro sentence membership
  rcases membership with ⟨domain, codomain, rfl⟩ | ⟨type, rfl⟩ | rfl
  · exact models_eta domain codomain
  · exact models_selection type
  · exact models_infinity

/-- General proof soundness in the concrete standard model. -/
theorem provable_sound {sentence : Sentence}
    (proof : theory.Provable sentence) : model.models sentence :=
  StandardAxiomProperties.provable_sound_of_models model extensional theory models_theory proof

theorem consistent : theory.Consistent := by
  intro falseProof
  exact model.models_bot (provable_sound falseProof)

/-- The theory has a genuine infinite-carrier realization, not just a
finite replay or a supplied semantic-properties interface. -/
theorem infinite_carrier : Infinite (model.Carrier ()) := by
  change Infinite HenkinModel.ModelPropertyCanary.LiftedNat
  infer_instance

namespace Controls

/-- The actually constructed subtype contains both two and three. -/
theorem nontrivial_defined_carrier :
    ∃ left right : WitnessedTypeDefinition.Carrier (fun n : Nat => 2 ≤ n), left ≠ right := by
  refine ⟨⟨2, by decide⟩, ⟨3, by decide⟩, ?_⟩
  intro equal
  have impossible : (2 : Nat) = 3 := congrArg Subtype.val equal
  exact (by decide : (2 : Nat) ≠ 3) impossible

/-- A point outside the new subtype is sent to its admitted witness. -/
theorem abstraction_outside :
    WitnessedTypeDefinition.representation
      (WitnessedTypeDefinition.abstraction (fun n : Nat => 2 ≤ n) 2 (by decide) 1) = 2 := by
  simp [WitnessedTypeDefinition.abstraction, WitnessedTypeDefinition.representation]

/-- Excluded empty-carrier instantiation is genuinely incompatible with
total Hilbert selection in the existing full-domain empty model. -/
theorem empty_carrier_refutes_choice :
    ¬ HenkinModel.ModelPropertyCanary.emptyBaseModel.models
      (StandardAxiomProperties.choiceFormula
        (Const := HenkinModel.ModelPropertyCanary.NoConstants Unit) (.base ())) :=
  StandardAxiomProperties.Canary.empty_model_refutes_base_choice_formula

/-- A finite inhabited base has choice but cannot satisfy infinity. -/
theorem finite_choice_refutes_infinity :
    HenkinModel.ModelPropertyCanary.booleanBaseModel.HasHilbertChoice ∧
      ¬ HenkinModel.ModelPropertyCanary.booleanBaseModel.HasDedekindInfiniteBase () :=
  ⟨⟨HenkinModel.ModelPropertyCanary.booleanBaseModel_choice⟩,
    HenkinModel.ModelPropertyCanary.booleanBaseModel_not_infinite⟩

end Controls

end Mettapedia.Logic.HOL.HOLLightStandardTheory
