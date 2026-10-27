import Mettapedia.OSLF.NativeTypes.GeneratedLogic.LocalDriverReading
import Mettapedia.OSLF.NativeTypes.Instances.Lambda.Driver
import Mettapedia.OSLF.NativeTypes.Instances.Lambda.ReferenceAgreement

/-!
# The λ-calculus driver, read at the front door

The λ driver's terms are intrinsically scoped closed λ-terms; its steps are the selected steps (β, under a binder, on
either side of an application); its tests are constructor tests on the encodings. It is read by steps in the reference
structure of the authored λ language restricted to the selected rules:

- **closed encodings are states** (`encode_state`) and the reference structure steps them exactly as the selection
  does (`step_iff`), by the agreement of the selected steps with the reference relation
  (`Instances.Lambda.ReferenceAgreement.step_iff`);
- **every step of an encoding reaches an encoding** (`image`), so the encoding is a step morphism from the structure
  it pulls back (`Embeddings.pullbackMorphism`);
- **its constructor tests are test formulas** (`test_iff`): constructor formulas where the sort profile admits closed
  terms, since `App` and `Lam` are represented declarations, the second through its abstraction over one variable; and
  `⊥` where the profile refuses closed terms, at whose sort no closed term lives (`syntaxMask_closed`).

The parts of an abstraction are open terms, not closed ones, so the encoding renders by a step morphism and not by a
bounded morphism: the reading is by steps (`reading`).
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.GeneratedLogic.LambdaReading

open Mettapedia.OSLF.Binding LambdaContextualRung LambdaScopedAuthoringComparison
open Mettapedia.OSLF.MeTTaIL Syntax
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.MeTTaIL.Engine (RelationEnv)
open Mettapedia.OSLF.NativeTypes.Generation (Generated structuralDeclaration)
open Mettapedia.OSLF.NativeTypes.Instances.Lambda.ReferenceAgreement (selectedLanguage)
open Mettapedia.OSLF.NativeTypes.Instances.Lambda.Frontier (Selection SelectedStep)
open Mettapedia.OSLF.NativeTypes.Instances.Lambda.Driver (Configuration driver)
open LocalReading

/-! ## Closed encodings -/

theorem encode_metadata : {Γ : Ctx sig} → (source : Term sig Γ .term) →
    (encodeTerm source).hasCanonicalBinderMetadata = true
  | _, .var _ => rfl
  | _, .op .app (.cons function (.cons argument .nil)) => by
      change ((encodeTerm function).hasCanonicalBinderMetadata &&
        ((encodeTerm argument).hasCanonicalBinderMetadata && true)) = true
      rw [encode_metadata function, encode_metadata argument]
      rfl
  | _, .op .lam (.cons body .nil) => by
      change ((none : Option String).isNone && (encodeTerm body).hasCanonicalBinderMetadata && true) = true
      rw [encode_metadata body]
      rfl
termination_by _ source => Mettapedia.OSLF.NativeTypes.Instances.Lambda.Frontier.nodeCount source
decreasing_by
  all_goals simp only [Mettapedia.OSLF.NativeTypes.Instances.Lambda.Frontier.nodeCount,
    Mettapedia.OSLF.NativeTypes.Instances.Lambda.Frontier.argumentNodeCount]; omega

/-- **A closed λ-term's encoding is a well-sorted closed term** of the authored language. -/
theorem encode_typed (source : Term sig [] .term) :
    OpenPatternWellSorted LambdaAuthoredFullRuleProfile.language FreeTypeContext.empty [] (.base "Term")
      (encodeTerm source) :=
  ⟨LambdaAuthoredTypingComparison.encodeTerm_hasType source, encode_metadata source,
    Mettapedia.OSLF.NativeTypes.Instances.Lambda.Decode.encode_object source, LambdaPatternRendering.encodeTerm_scoped source⟩

theorem encode_state (source : Term sig [] .term) : IsState (encodeTerm source) := isState_of_typed (encode_typed source)

theorem equationFree (selection : Selection) : (selectedLanguage selection).isEquationFree = true := rfl

/-- **The reference structure steps a closed λ-term exactly as the selection does.** -/
theorem step_iff (relEnv : RelationEnv) (selection : Selection) (source target : Term sig [] .term) :
    (referenceStructure relEnv (selectedLanguage selection)).step (encodeTerm source) .any
        (encodeTerm target) ↔ SelectedStep selection [] source target := by
  rw [reference_step_any_iff (equationFree selection)]
  constructor
  · rintro ⟨-, -, step⟩
    obtain ⟨result, same, selected⟩ := (Mettapedia.OSLF.NativeTypes.Instances.Lambda.ReferenceAgreement.step_iff
      selection source _).mp step
    rw [Mettapedia.OSLF.NativeTypes.Instances.Lambda.Decode.encode_injective _ _ same]
    exact selected
  · intro selected
    exact ⟨encode_state source, encode_state target,
      Mettapedia.OSLF.NativeTypes.Instances.Lambda.ReferenceAgreement.complete selection selected⟩

/-- A step with a label of the term's own is a step. -/
theorem step_any_of_step {relEnv : RelationEnv} {language : LanguageDef} {source : Pattern} {label : StepLabel}
    (own : label.isContext = false) {target : Pattern}
    (held : (referenceStructure relEnv language).step source label target) :
    (referenceStructure relEnv language).step source .any target := by
  obtain ⟨sourceState, targetState, redex, contractum, witness, toRedex, redexState, valid, contractumState, toTarget,
    -⟩ := held
  exact ⟨sourceState, targetState, redex, contractum, witness, (placed_iff rfl).mpr ((placed_iff own).mp toRedex),
    redexState, valid, contractumState, toTarget, rfl⟩

/-- **Every step of a closed encoding reaches an encoding.** -/
theorem image (relEnv : RelationEnv) (selection : Selection) (source : Term sig [] .term) (label : StepLabel)
    (target : Pattern) (own : label.isContext = false)
    (held : (referenceStructure relEnv (selectedLanguage selection)).step (encodeTerm source) label target) :
    ∃ result : Term sig [] .term, encodeTerm result = target := by
  obtain ⟨-, -, step⟩ := (reference_step_any_iff (equationFree selection)).mp (step_any_of_step own held)
  obtain ⟨result, rfl, -⟩ := (Mettapedia.OSLF.NativeTypes.Instances.Lambda.ReferenceAgreement.step_iff selection
    source target).mp step
  exact ⟨result, rfl⟩

/-! ## Tests -/

/-- The λ driver's generated presentation at a configuration. -/
abbrev configured (configuration : Configuration) : Generated :=
  Mettapedia.OSLF.NativeTypes.Instances.Lambda.Driver.generated configuration

theorem configured_language (configuration : Configuration) :
    (configured configuration).snapshot.language = LambdaAuthoredFullRuleProfile.language := by
  rw [Mettapedia.OSLF.NativeTypes.Instances.Lambda.Driver.original_snapshot]
  rfl

theorem configured_free (configuration : Configuration) :
    (configured configuration).snapshot.free = FreeTypeContext.empty := by
  rw [Mettapedia.OSLF.NativeTypes.Instances.Lambda.Driver.original_snapshot]
  funext name
  rfl

/-- **At a well-sorted closed term the λ syntax mask admits exactly the sort `⋆`.** -/
theorem syntaxMask_closed (configuration : Configuration) {type : TypeExpr} {source : Pattern}
    (typed : OpenPatternWellSorted (configured configuration).snapshot.language (configured configuration).snapshot.free []
      type source) (carrier : TypeExpr) (sort : Mettapedia.OSLF.Framework.ModalHypercube.HSort) :
    Mettapedia.OSLF.NativeTypes.Instances.Lambda.Driver.syntaxMask [] carrier sort source = decide (sort = .star) := by
  rw [configured_free] at typed
  cases source with
  | bvar slot =>
    cases typed.1 with
    | bvar found => simp at found
  | fvar name =>
    cases typed.1 with
    | fvar found => cases found
  | _ => rfl

/-- Whether a declaration's sorts admit closed terms: its output sort and every input sort are `⋆`. -/
def admitsClosed (configuration : Configuration) (index : Fin (configured configuration).snapshot.language.terms.length) :
    Bool :=
  decide (Mettapedia.OSLF.NativeTypes.Generation.structuralOutputSort (configured configuration) index = .star) &&
    (List.finRange _).all fun position =>
      decide (Mettapedia.OSLF.NativeTypes.Generation.structuralInputSort (configured configuration) index position = .star)

/-- **The formula of a constructor test**: the constructor formula where the declaration's sorts admit closed terms, and
`⊥` elsewhere, where the test holds of no closed term. -/
def testFormula (configuration : Configuration) (index : Fin (configured configuration).snapshot.language.terms.length) :
    Formula 0 :=
  if admitsClosed configuration index then constructorFormula (structuralDeclaration (configured configuration) index)
  else .bot

theorem testFormula_forward (configuration : Configuration)
    (index : Fin (configured configuration).snapshot.language.terms.length) :
    (testFormula configuration index).forward = true := by
  unfold testFormula
  split_ifs
  · exact forward_constructorFormula _
  · rfl

theorem declarations_represented :
    ∀ rule ∈ LambdaAuthoredFullRuleProfile.language.terms, RepresentedDeclaration rule ∧ rule.category = "Term" := by
  have checked : LambdaAuthoredFullRuleProfile.language.terms.all
      (fun rule => isRepresentedDeclaration rule && rule.category == "Term") = true := by decide +kernel
  intro rule member
  have both := List.all_eq_true.mp checked rule member
  simp only [Bool.and_eq_true, beq_iff_eq] at both
  exact ⟨representedDeclaration_of_check both.1, both.2⟩

theorem declaration_represented (configuration : Configuration)
    (index : Fin (configured configuration).snapshot.language.terms.length) :
    RepresentedDeclaration (structuralDeclaration (configured configuration) index) ∧
      (structuralDeclaration (configured configuration) index).category = "Term" :=
  declarations_represented _ (configured_language configuration ▸ List.getElem_mem index.isLt)

/-- The λ driver looks up only tests accepting everything. -/
theorem lookup_accepts {label : String} {leaf : Mettapedia.OSLF.NativeTypes.Instances.Lambda.Generated.Leaf}
    (found : Mettapedia.OSLF.NativeTypes.Instances.Lambda.Generated.former? label = some leaf) :
    ∀ position pattern, leaf.accepts position pattern = true := by
  have member := List.mem_of_find?_eq_some found
  simp only [Mettapedia.OSLF.NativeTypes.Instances.Lambda.Generated.formers, List.mem_map, List.mem_finRange,
    true_and] at member
  obtain ⟨index, rfl⟩ := member
  intro _ _
  rfl

/-- **A constructor test of the λ driver is its test formula** at the closed term's encoding. -/
theorem test_iff (relEnv : RelationEnv) (configuration : Configuration)
    (leaf : Mettapedia.OSLF.NativeTypes.Instances.Lambda.Generated.Leaf)
    (accepts : ∀ position pattern, leaf.accepts position pattern = true) (source : Term sig [] .term) :
    ((driver configuration []).tests leaf).predicate.1 source ↔
      (referenceStructure relEnv (selectedLanguage configuration.rules)).sat Env.closed
        (testFormula configuration leaf.index) (encodeTerm source) := by
  obtain ⟨represented, category⟩ := declaration_represented configuration leaf.index
  have typed : OpenPatternWellSorted (configured configuration).snapshot.language
      (configured configuration).snapshot.free [] (.base (structuralDeclaration (configured configuration)
        leaf.index).category) (encodeTerm source) := by
    rw [category, configured_language, configured_free]
    exact encode_typed source
  refine (Mettapedia.OSLF.NativeTypes.Instances.Lambda.Driver.native_structural_meaning configuration [] leaf
    source).trans ?_
  unfold testFormula
  split_ifs with admits
  · simp only [admitsClosed, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_finRange,
      true_implies] at admits
    have admitsAt : MaskAdmitsAt (configured configuration)
        Mettapedia.OSLF.NativeTypes.Instances.Lambda.Driver.syntaxMask leaf.index := by
      refine ⟨fun part partTyped => ?_, fun position part partTyped => ?_⟩
      · rw [syntaxMask_closed configuration partTyped, admits.1]
        rfl
      · rw [syntaxMask_closed configuration partTyped, admits.2 position]
        rfl
    exact structural_iff (configured configuration)
      (Mettapedia.OSLF.NativeTypes.Instances.Lambda.Driver.no_equations configuration)
      Mettapedia.OSLF.NativeTypes.Instances.Lambda.Driver.syntaxMask (by rw [configured_language]; rfl)
      (configured_free configuration) (equationFree configuration.rules) rfl leaf.index admitsAt leaf.accepts
      accepts
      represented typed
  · refine iff_of_false ?_ id
    simp only [admitsClosed, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_finRange,
      true_implies, not_and, not_forall] at admits
    by_cases output : Mettapedia.OSLF.NativeTypes.Generation.structuralOutputSort (configured configuration)
        leaf.index = .star
    · obtain ⟨position, input⟩ := admits output
      exact structural_refused_input (configured configuration)
        (Mettapedia.OSLF.NativeTypes.Instances.Lambda.Driver.no_equations configuration)
        Mettapedia.OSLF.NativeTypes.Instances.Lambda.Driver.syntaxMask leaf.index leaf.accepts represented.2 position
        (fun part partTyped => by rw [syntaxMask_closed configuration partTyped]; exact decide_eq_false input) typed
    · exact structural_refused_output (configured configuration)
        Mettapedia.OSLF.NativeTypes.Instances.Lambda.Driver.syntaxMask leaf.index leaf.accepts
        (fun part partTyped => by rw [syntaxMask_closed configuration partTyped]; exact decide_eq_false output) typed

/-! ## The reading -/

/-- **The λ driver's faithful reading by steps**, at every configuration. -/
def reading (configuration : Configuration) (relEnv : RelationEnv := RelationEnv.empty) :
    Embeddings.FaithfulSteps (driver configuration []) relEnv (selectedLanguage configuration.rules)
      (fun leaf => testVariable (configured configuration) leaf.index true)
      (fun leaf => testVariable (configured configuration) leaf.index false) where
  structure_ := Embeddings.pullback (referenceStructure relEnv (selectedLanguage configuration.rules)) encodeTerm
  region _ := True
  steps source _ target := step_iff relEnv configuration.rules source target
  closed _ _ _ _ := trivial
  rendering := Embeddings.pullbackMorphism _ encodeTerm (image relEnv configuration.rules)
  renders := rfl
  covers leaf := ∀ position pattern, leaf.accepts position pattern = true
  test leaf := testFormula configuration leaf.index
  testAgrees leaf accepts source _ := test_iff relEnv configuration leaf accepts source
  closing := closingOf (configured configuration) (testFormula configuration)
  closesPositive leaf := closingOf_positive (configured configuration) _ leaf.index
  closesNegative leaf := closingOf_negative (configured configuration) _ leaf.index
  closingForward := closingOf_forward (configured configuration) _ (testFormula_forward configuration)

theorem reading_covered (configuration : Configuration) (relEnv : RelationEnv := RelationEnv.empty) :
    ∀ name leaf, (driver configuration []).lookup name = some leaf → (reading configuration relEnv).covers leaf :=
  fun _ _ found => lookup_accepts found

end Mettapedia.OSLF.NativeTypes.GeneratedLogic.LambdaReading
