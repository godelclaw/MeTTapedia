import Mettapedia.OSLF.NativeTypes.GeneratedLogic.RhoCanonicalForms
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.LocalDriverReading
import Mettapedia.OSLF.NativeTypes.Instances.Rho.Driver

/-!
# The ρ driver read in ρ's language

The ρ driver runs closed processes modulo canonical equality, with communication by reflective matching and semantic
substitution. Its reading by steps (`reading`) is the native structure of ρ in ρ's own reading (`Rho.reading`):

- **its steps are the structure's steps** (`step_iff`): a driver step is a step of ρ's interpreted rules between
  processes canonically equal to its ends, which in ρ's reading are its equivalent redexes and contracta;
- **its constructor tests are constructor formulas modulo the equations** (`test_iff`): "built by `X`" holds at a
  process when some equivalent term is `X` applied to arguments of `X`'s parameter types; the parallel constructor's
  test holds of every process, and its formula says that the process splits as a bag, by the singleton law.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.GeneratedLogic.Rho

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine (RelationEnv)
open Mettapedia.OSLF.MeTTaIL.ReferenceStep
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.Canonical (canonicalize canonicalizeList)
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefSemanticAgreement
  (rhoReflectiveGSLT presentedRhoProcessEquiv presentedRhoStep_iff)
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefGSLT (RhoProcess)
open Mettapedia.OSLF.NativeTypes.Instances.Rho.TypedEquations
open Mettapedia.OSLF.NativeTypes.GeneratedLogic.LocalReading (constructorFormula paramFormulas)
open Mettapedia.OSLF.MeTTaIL.ScopedPattern (isWellScopedAt_of_binderSafeAt)

variable {relEnv : RelationEnv}

/-- Every process of the driver is admitted. -/
theorem admitted_term (source : rhoReflectiveGSLT.Term) : process source.1 = true :=
  Mettapedia.OSLF.NativeTypes.Instances.Rho.DecisionBackend.every_carrier_admitted source

theorem state_of_admitted {term : Pattern} (admitted : process term = true) : IsState term :=
  ⟨closed_of_process admitted, (process_iff.mp admitted).2.1⟩

/-- The driver's process of an admitted pattern. -/
def termOf (term : Pattern) (admitted : process term = true) : rhoReflectiveGSLT.Term :=
  presentedRhoProcessEquiv.symm (Mettapedia.OSLF.NativeTypes.Instances.Rho.Canonical.admittedProcess term admitted)

theorem termOf_pattern (term : Pattern) (admitted : process term = true) : (termOf term admitted).1 = term := by
  rw [← Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefSemanticAgreement.presentedRhoProcessEquiv_pattern]
  simp only [termOf,
    Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefSemanticAgreement.presentedRhoProcessEquiv_apply_symm]
  rfl

/-! ## Steps -/

/-- **A driver step is a step of ρ's native structure, in ρ's reading.** -/
theorem step_iff (source target : rhoReflectiveGSLT.Term) :
    (referenceStructure relEnv rhoCalc reading).step source.1 .any target.1 ↔ rhoReflectiveGSLT.Step source target := by
  rw [presentedRhoStep_iff]
  have sourceAdmitted := admitted_term source
  have targetAdmitted := admitted_term target
  constructor
  · rintro ⟨-, -, redex, contractum, witness, before, -, valid, -, after, -⟩
    have redexAdmitted := process_invariant sourceAdmitted before
    have contractumAdmitted := process_of_step redexAdmitted valid.2
    refine ⟨Mettapedia.OSLF.NativeTypes.Instances.Rho.Canonical.admittedProcess redex redexAdmitted,
      Mettapedia.OSLF.NativeTypes.Instances.Rho.Canonical.admittedProcess contractum contractumAdmitted, ?_, valid.2, ?_⟩
    · exact canonicalize_eq_of_objectEquivalent before
    · exact canonicalize_eq_of_objectEquivalent after
  · rintro ⟨redex, contractum, before, primitive, after⟩
    have redexAdmitted : process redex.1 = true :=
      (Mettapedia.OSLF.NativeTypes.Instances.Rho.Canonical.admit_exact redex.1).mpr redex.2
    have contractumAdmitted : process contractum.1 = true :=
      (Mettapedia.OSLF.NativeTypes.Instances.Rho.Canonical.admit_exact contractum.1).mpr contractum.2
    refine ⟨state_of_admitted sourceAdmitted, state_of_admitted targetAdmitted, redex.1, contractum.1, .base [],
      (objectEquivalent_iff (domain_of_process sourceAdmitted) (domain_of_process redexAdmitted)).mpr before,
      state_of_admitted redexAdmitted, ⟨rfl, primitive⟩, state_of_admitted contractumAdmitted,
      (objectEquivalent_iff (domain_of_process contractumAdmitted) (domain_of_process targetAdmitted)).mpr after, rfl⟩

/-- **The structure's steps from a driver process end at driver processes.** -/
theorem image (source : rhoReflectiveGSLT.Term) (label : StepLabel) (target : Pattern) (own : label.isContext = false)
    (step : (referenceStructure relEnv rhoCalc reading).step source.1 label target) :
    ∃ other : rhoReflectiveGSLT.Term, other.1 = target := by
  obtain ⟨-, -, redex, contractum, witness, before, -, valid, -, after, -⟩ := step
  rw [placed_iff own] at before
  have contractumAdmitted := process_of_step (process_invariant (admitted_term source) before) valid.2
  have targetAdmitted := process_invariant contractumAdmitted after
  exact ⟨termOf target targetAdmitted, termOf_pattern target targetAdmitted⟩

/-! ## Constructor tests -/

open Mettapedia.OSLF.NativeTypes.Instances.Rho.OrderedDecomposition (Value)
open Mettapedia.OSLF.NativeTypes.Structural (ConstructorValue)

/-- **The formula of a ρ constructor test**: the constructor formula, read modulo the equations; for the parallel
constructor, splitting as a bag. -/
def ruleFormula (rule : GrammarRule) : Formula 0 :=
  if usesBareCollection? rule then .split .hashBag .top .top else constructorFormula rule

theorem ruleFormula_forward (rule : GrammarRule) : (ruleFormula rule).forward = true := by
  unfold ruleFormula
  split_ifs
  · rfl
  · exact LocalReading.forward_constructorFormula rule

/-- Arguments typed at their parameters' types satisfy the parameters' formulas, in every reading. -/
theorem satAll_paramFormulas {anyReading : LanguageReading} :
    ∀ {params : List TermParam} {parts : List Pattern}, LocalReading.ArgumentsTyped rhoCalc params parts →
      (referenceStructure relEnv rhoCalc anyReading).satAll Env.closed (paramFormulas params) parts
  | _, _, .nil => trivial
  | _, _, .cons (type := type) parameterType object typed rest => by
    refine ⟨?_, satAll_paramFormulas rest⟩
    simp only [parameterType]
    exact ⟨object, _, Relation.EqvGen.refl _, carrierTyped_of_wellSorted typed⟩

/-- **A constructor's test is its constructor formula, modulo ρ's equations**, at an admitted process. -/
theorem ordinary_iff {rule : GrammarRule} (member : rule ∈ rhoCalc.terms) (notBare : ¬ UsesBareCollection rule)
    (notQuote : rule.label ≠ "NQuote") {source : Pattern} (admitted : process source = true) :
    (∃ value : Value FreeTypeContext.empty [] rule, canonicalize source = canonicalize value.val.pattern) ↔
      (referenceStructure relEnv rhoCalc reading).sat Env.closed (constructorFormula rule) source := by
  show _ ↔ ∃ parts, (IsObject source ∧ ObjectEquivalent relEnv rhoCalc reading source (.apply rule.label parts)) ∧
    (referenceStructure relEnv rhoCalc reading).satAll Env.closed (paramFormulas rule.params) parts
  constructor
  · rintro ⟨⟨value, valueObject⟩, same⟩
    cases value with
    | ordinary arguments _ typed =>
      change canonicalize source = canonicalize (.apply rule.label arguments) at same
      rw [Mettapedia.Languages.ProcessCalculi.RhoCalculus.Canonical.canonicalize_apply_general _ _
        (fun quote => notQuote quote.1)] at same
      have canonAdmitted := process_canonicalize admitted
      rw [same] at canonAdmitted
      obtain ⟨canonTyped, canonObject, canonSealed⟩ := process_iff.mp canonAdmitted
      obtain ⟨rule', member', label, -, -, partsTyped⟩ := hasType_apply_inversion canonTyped
      have sameRule := rhoCalc_labelDeterministic member' member label.symm
      subst sameRule
      have metadata := metadata_proc canonTyped canonObject
      have scope := isWellScopedAt_of_binderSafeAt "NQuote" canonSealed
      simp only [isObjectPattern] at canonObject
      simp only [Pattern.hasCanonicalBinderMetadata] at metadata
      simp only [Pattern.isWellScopedAt] at scope
      refine ⟨canonicalizeList arguments, ⟨(process_iff.mp admitted).2.1, ?_⟩,
        satAll_paramFormulas (LocalReading.argumentsTyped_of_typed partsTyped canonObject metadata scope)⟩
      have toCanonical := equivalent_canonicalize (relEnv := relEnv) (domain_of_process admitted)
      rw [same] at toCanonical
      exact toCanonical
    | collection _ _ _ _ _ shape _ =>
      exact absurd ((usesBareCollection?_eq_true_iff rule).mp (by rw [usesBareCollection?, shape])) notBare
  · rintro ⟨parts, ⟨-, equivalent⟩, -⟩
    have builtAdmitted := process_invariant admitted equivalent
    obtain ⟨builtTyped, builtObject, -⟩ := process_iff.mp builtAdmitted
    obtain ⟨rule', member', label, notBare', -, partsTyped⟩ := hasType_apply_inversion builtTyped
    have sameRule := rhoCalc_labelDeterministic member' member label.symm
    subst sameRule
    exact ⟨⟨.ordinary parts notBare' partsTyped, builtObject⟩, canonicalize_eq_of_objectEquivalent equivalent⟩

/-- **The parallel constructor's test holds of every admitted process, as does splitting as a bag.** -/
theorem parallel_iff {rule : GrammarRule} (shape : rule.bareParams = [.simple "ps" (.collection .hashBag TypeExpr.proc)])
    {source : Pattern} (admitted : process source = true) :
    (∃ value : Value FreeTypeContext.empty [] rule, canonicalize source = canonicalize value.val.pattern) ↔
      (referenceStructure relEnv rhoCalc reading).sat Env.closed (.split .hashBag .top .top) source := by
  obtain ⟨typed, object, sealed⟩ := process_iff.mp admitted
  have good : Good FreeTypeContext.empty [] 0 source := ⟨object, typed, sealed⟩
  refine iff_of_true ⟨⟨.collection "ps" .hashBag TypeExpr.proc [source] none shape (.cons typed (.nil _ _)),
    by simpa [ConstructorValue.pattern, isObjectPattern, isObjectPatternList] using object⟩, ?_⟩ ?_
  · change canonicalize source = canonicalize (.collection .hashBag [source] none)
    simp only [Mettapedia.Languages.ProcessCalculi.RhoCalculus.Canonical.canonicalize, canonicalizeList]
    exact (Mettapedia.OSLF.NativeTypes.Instances.Rho.CarrierEquations.bag_argument_collapses source).symm
  · have chain := typed_collapseBag (relEnv := relEnv) (free := FreeTypeContext.empty) (bound := []) (depth := 0)
      (elements := [source]) (by simpa using good)
    refine ⟨.collection .hashBag [source] none, .collection .hashBag [] none, ⟨object, [source], [], ?_, rfl, rfl⟩,
      trivial, trivial⟩
    exact objectEquivalent_of_chain judged_proc (.symm _ _ chain)

/-- **Each of ρ's process constructors tests its formula**, at an admitted process. -/
theorem rule_iff {rule : GrammarRule} (member : rule ∈ rhoCalc.terms) (category : rule.category = "Proc")
    {source : Pattern} (admitted : process source = true) :
    (∃ value : Value FreeTypeContext.empty [] rule, canonicalize source = canonicalize value.val.pattern) ↔
      (referenceStructure relEnv rhoCalc reading).sat Env.closed (ruleFormula rule) source := by
  have ordinary : ∀ {rule : GrammarRule}, rule ∈ rhoCalc.terms → usesBareCollection? rule = false →
      rule.label ≠ "NQuote" →
      ((∃ value : Value FreeTypeContext.empty [] rule, canonicalize source = canonicalize value.val.pattern) ↔
        (referenceStructure relEnv rhoCalc reading).sat Env.closed (ruleFormula rule) source) := by
    intro rule member notBare notQuote
    rw [ruleFormula, if_neg (by rw [notBare]; decide)]
    exact ordinary_iff member (fun bare => by
      rw [← usesBareCollection?_eq_true_iff, notBare] at bare
      cases bare) notQuote admitted
  have rhoMember := member
  simp only [rhoCalc, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ordinary rhoMember rfl (by decide)
  · exact ordinary rhoMember rfl (by decide)
  · simp at category
  · rw [ruleFormula, if_pos (by decide)]
    exact parallel_iff rfl admitted
  · exact ordinary rhoMember rfl (by decide)
  · exact ordinary rhoMember rfl (by decide)

/-! ## The reading -/

open Mettapedia.OSLF.NativeTypes.Instances.Rho.Driver (driver)
open Mettapedia.OSLF.NativeTypes.Instances.Rho.DriverSource (chosen)

abbrev Configuration := Mettapedia.OSLF.NativeTypes.Instances.Rho.DriverSource.Configuration

/-- **A test of the ρ driver is its formula**, when its inputs accept everything. -/
theorem test_iff (configuration : Configuration) (leaf : Mettapedia.OSLF.NativeTypes.Instances.Rho.Driver.Leaf)
    (accepts : ∀ position actual, (leaf.inputs position).meaning actual) (source : rhoReflectiveGSLT.Term) :
    ((driver configuration).tests leaf).predicate.1 source ↔
      (referenceStructure relEnv rhoCalc reading).sat Env.closed (ruleFormula chosen.language.terms[leaf.index])
        source.1 := by
  have member : chosen.language.terms[leaf.index] ∈ rhoCalc.terms := List.getElem_mem leaf.index.isLt
  refine Iff.trans ?_ (rule_iff member leaf.carrier (admitted_term source))
  show (∃ value, _ ∧ _) ↔ _
  exact ⟨fun ⟨value, same, _⟩ => ⟨value, same⟩, fun ⟨value, same⟩ => ⟨value, same, fun position => accepts _ _⟩⟩

/-- The variables of the ρ driver's tests. -/
abbrev positive (leaf : Mettapedia.OSLF.NativeTypes.Instances.Rho.Driver.Leaf) :=
  LocalReading.pairVariable leaf.index true

abbrev negative (leaf : Mettapedia.OSLF.NativeTypes.Instances.Rho.Driver.Leaf) :=
  LocalReading.pairVariable leaf.index false

/-- The closing formulas of the ρ driver's tests. -/
def closing : Fin (2 * chosen.language.terms.length) → Formula 0 :=
  LocalReading.pairClosing fun index => ruleFormula chosen.language.terms[index]

/-- **The ρ driver's reading by steps, in ρ's reading**: its processes in ρ's native structure, its steps the
structure's, and each test whose inputs accept everything its constructor formula. -/
def driverReading (configuration : Configuration) (relEnv : RelationEnv := RelationEnv.empty) :
    Embeddings.FaithfulSteps (driver configuration) relEnv rhoCalc positive negative reading where
  structure_ := Embeddings.pullback (referenceStructure relEnv rhoCalc reading) Subtype.val
  region _ := True
  steps source _ target := step_iff source target
  closed _ _ _ _ := trivial
  rendering := Embeddings.pullbackMorphism _ Subtype.val image
  renders := rfl
  covers leaf := ∀ position actual, (leaf.inputs position).meaning actual
  test leaf := ruleFormula chosen.language.terms[leaf.index]
  testAgrees leaf accepts source _ := test_iff configuration leaf accepts source
  closing := closing
  closesPositive leaf := LocalReading.pairClosing_positive _ leaf.index
  closesNegative leaf := LocalReading.pairClosing_negative _ leaf.index
  closingForward := LocalReading.pairClosing_forward _ fun _ => ruleFormula_forward _

/-- **The driver looks up only tests accepting everything.** -/
theorem lookup_accepts (configuration : Configuration) {name : String}
    {leaf : Mettapedia.OSLF.NativeTypes.Instances.Rho.Driver.Leaf} (found : (driver configuration).lookup name = some leaf) :
    ∀ position actual, (leaf.inputs position).meaning actual := by
  have member := List.mem_of_find?_eq_some found
  simp only [Mettapedia.OSLF.NativeTypes.Instances.Rho.Driver.formers, List.mem_filterMap, List.mem_finRange,
    true_and] at member
  obtain ⟨index, built⟩ := member
  split at built
  · cases built
    intro _ _
    trivial
  · cases built

theorem driverReading_covered (configuration : Configuration) (relEnv : RelationEnv := RelationEnv.empty) :
    ∀ name leaf, (driver configuration).lookup name = some leaf → (driverReading configuration relEnv).covers leaf :=
  fun _ _ found => lookup_accepts configuration found

end Mettapedia.OSLF.NativeTypes.GeneratedLogic.Rho
