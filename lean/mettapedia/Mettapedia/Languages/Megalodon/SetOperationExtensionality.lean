import Mettapedia.Languages.Megalodon.SetOperationSemantics
import Mettapedia.Languages.Megalodon.ProofCompilation
import Mettapedia.Languages.Megalodon.NormalizationTermination

/-!
# Scoped extensionality in the common material Megalodon profile

A finite list of simple-type pairs selects monomorphic instances of the
maintained functional-extensionality schema. Propositional extensionality is
declared separately. Their meanings are proved in the supplied material
interpretation; neither foundation nor anti-foundation is added.

Adding these known propositions preserves the six operation declarations.
The source interpretation uses the existing context pullback and actual
material values. Compiler acceptance remains a separate obligation from
semantic validity of these explicitly declared guest axioms.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.Megalodon.SetOperationExtensionality

open Mettapedia.Logic.HOL
open Embedding.ZFSetHenkinInterpretation
open MathdataKernel HenkinTermInterpretation
open SetOperationProofCompilation (base type)

universe w

def functionalName (index : Nat) : Name := "func_ext_" ++ toString index

def facts (instances : List (Ty Base × Ty Base)) : List KnownDecl :=
  ⟨"prop_ext", ExtensionalityAxioms.Native.propositional⟩ ::
    instances.zipIdx.map (fun (pair, index) =>
      ⟨functionalName index, ExtensionalityAxioms.Native.functional
        (reifyType pair.1) (reifyType pair.2)⟩)

def environment (instances : List (Ty Base × Ty Base)) : Environment :=
  { SetOperationProofCompilation.environment with known := facts instances }

def forgetConstant {instances : List (Ty Base × Ty Base)} {value : Ty Base} :
    Constant (environment instances) value →
      Constant SetOperationProofCompilation.environment value
  | .named name entry lookup typed => .named name entry lookup typed
  | .primitive index lookup => .primitive index lookup

def extendConstant (instances : List (Ty Base × Ty Base)) {value : Ty Base} :
    Constant SetOperationProofCompilation.environment value →
      Constant (environment instances) value
  | .named name entry lookup typed => .named name entry lookup typed
  | .primitive index lookup => .primitive index lookup

theorem forget_extend (instances : List (Ty Base × Ty Base)) {value : Ty Base}
    (constant : Constant SetOperationProofCompilation.environment value) :
    forgetConstant (extendConstant instances constant) = constant := by
  cases constant <;> rfl

def symbol (instances : List (Ty Base × Ty Base)) {value : Ty Unit} (constant : Symbol value) :
    Constant (environment instances) (type value) :=
  extendConstant instances (SetOperationProofCompilation.symbol constant)

def term (instances : List (Ty Base × Ty Base)) {gamma : Ctx Unit} {value : Ty Unit}
    (expression : Term Symbol gamma value) :
    Term (Constant (environment instances)) (gamma.map type) (type value) :=
  mapTypes base (symbol instances) expression

def proof (instances : List (Ty Base × Ty Base)) {gamma : Ctx Unit}
    {assumptions : List (Formula Symbol gamma)} {conclusion : Formula Symbol gamma}
    (source : ProofSyntax Symbol assumptions conclusion) :
    ProofSyntax (Constant (environment instances))
      (assumptions.map (term instances)) (term instances conclusion) :=
  ProofSyntax.mapTypes base (symbol instances) source

/-- Missing schema instances remain undeclared names, which the checker must
refuse. Supplying an instance list is not an assertion of compiler acceptance. -/
def functionalInstanceName (instances : List (Ty Base × Ty Base)) (domain result : Tp) : Name :=
  functionalName
    ((instances.map (fun pair => (reifyType pair.1, reifyType pair.2))).idxOf (domain, result))

def functionalProof (instances : List (Ty Base × Ty Base)) (domain result : Tp) : Pf :=
  .known (functionalInstanceName instances domain result)

def compile (instances : List (Ty Base × Ty Base)) {gamma : Ctx Unit}
    {assumptions : List (Formula Symbol gamma)} {conclusion : Formula Symbol gamma}
    (source : ProofSyntax Symbol assumptions conclusion) : Pf :=
  ProofCompilation.compile (functionalProof instances) (.known "prop_ext") (proof instances source)

/-- Compute a successful native normalization budget for every encoded
material HOL term. The actual common declaration table is opaque. -/
def normalizeTerm (instances : List (Ty Base × Ty Base)) {gamma : Ctx Unit} {value : Ty Unit}
    (expression : Term Symbol gamma value) :
    {completed : Nat × Tm //
      MathdataKernel.normalize (environment instances) completed.1
        (HOLTermEncoding.native (term instances expression)) = some completed.2} :=
  NormalizationTermination.completeNative (HOLTermEncoding.encode (term instances expression))
    (HOLTermEncoding.native_erased _)
    (fun name entry _ lookup => SetOperationSemantics.lookup_opaque name entry lookup)

theorem proof_nodeCount (instances : List (Ty Base × Ty Base)) {gamma : Ctx Unit}
    {assumptions : List (Formula Symbol gamma)} {conclusion : Formula Symbol gamma}
    (source : ProofSyntax Symbol assumptions conclusion) :
    (proof instances source).nodeCount = source.nodeCount :=
  ProofSyntax.nodeCount_mapTypes base (symbol instances) source

theorem term_substitution (instances : List (Ty Base × Ty Base))
    {gamma delta : Ctx Unit} (substitution : Subst Symbol gamma delta)
    (translated : Subst (Constant (environment instances)) (gamma.map type) (delta.map type))
    (compatible : ∀ {value} (index : Var gamma value),
      term instances (substitution index) = translated (index.mapTypes base))
    {value : Ty Unit} (expression : Term Symbol gamma value) :
    term instances (subst substitution expression) = subst translated (term instances expression) :=
  mapTypes_subst base (symbol instances) substitution translated compatible expression

theorem missing_functional_refused (domain result : Tp) (fuel depth : Nat)
    (terms : List Tp) (hypotheses : List Tm) :
    inferProof (environment []) fuel depth terms hypotheses
      (functionalProof [] domain result) = none := rfl

noncomputable def model (instances : List (Ty Base × Ty Base))
    (source : HenkinModel.{0, 0, w} Unit Symbol) :
    HenkinModel.{0, 0, w} Base (Constant (environment instances)) :=
  HenkinModel.standard (SetOperationSemantics.model source).Carrier
    (fun constant => (SetOperationSemantics.model source).constDen (forgetConstant constant))

theorem fullDomains (instances : List (Ty Base × Ty Base))
    (source : HenkinModel.{0, 0, w} Unit Symbol) : (model instances source).FullDomains :=
  HenkinModel.fullDomains_standard _ _

theorem sourceReduct_standard (instances : List (Ty Base × Ty Base))
    (source : HenkinModel.{0, 0, w} Unit Symbol) :
    HenkinModel.standardTypeReduct base (symbol instances) (model instances source) =
      HenkinModel.standard source.Carrier source.constDen := by
  apply HenkinModel.standard_ext rfl
  intro value constant
  refine (Ty.denoteSubstituteEquiv_symm_apply_heq _ _ _ _).trans ?_
  refine (Ty.denoteSubstituteEquiv_symm_apply_heq _ _ _ _).trans ?_
  cases constant <;> rfl

theorem sourceReduct_eq (instances : List (Ty Base × Ty Base))
    (source : HenkinModel.{0, 0, w} Unit Symbol) (full : source.FullDomains) :
    HenkinModel.standardTypeReduct base (symbol instances) (model instances source) = source :=
  (sourceReduct_standard instances source).trans (HenkinModel.standard_eq_of_fullDomains source full)

/-- Declared guest extensionality changes no material operation or open-term value. -/
theorem denote_term (instances : List (Ty Base × Ty Base))
    (source : HenkinModel.{0, 0, w} Unit Symbol) (full : source.FullDomains)
    {gamma : Ctx Unit} {value : Ty Unit} (expression : Term Symbol gamma value)
    (values : (model instances source).Valuation (gamma.map type)) :
    Ty.denoteSubstituteEquiv base (model instances source).Carrier value
      (source.denote expression (SetOperationSemantics.sourceValuation source values)) =
      (model instances source).denote (term instances expression) values := by
  have comparison := HenkinModel.denote_mapTypes base (symbol instances) (model instances source)
    (fullDomains instances source) expression values
  have denotations : HEq
      @(HenkinModel.standardTypeReduct base (symbol instances) (model instances source)).denote
      @source.denote := by rw [sourceReduct_eq instances source full]
  rw [eq_of_heq denotations] at comparison
  exact comparison

/-- Every listed fact is independently interpreted; no fact's truth is an
assumption passed through from its declaration. -/
theorem fact_valid (instances : List (Ty Base × Ty Base))
    (source : HenkinModel.{0, 0, w} Unit Symbol) (fact : KnownDecl)
    (present : fact ∈ facts instances) :
    ∃ proposition : ClosedFormula (Constant (environment instances)),
      erase proposition = some fact.proposition ∧ (model instances source).models proposition := by
  simp only [facts, List.mem_cons] at present
  rcases present with rfl | present
  · exact ExtensionalityAxioms.Native.propositional_valid _
  · obtain ⟨⟨⟨domain, result⟩, index⟩, _, rfl⟩ := List.mem_map.mp present
    exact ExtensionalityAxioms.Native.functional_valid _
      ((model instances source).functionsRespectEqv_of_fullDomains (fullDomains instances source))
      domain result

theorem knownValidity (instances : List (Ty Base × Ty Base))
    (source : HenkinModel.{0, 0, w} Unit Symbol) :
    NativeProof.KnownValidity (model instances source) := by
  intro name raw lookup
  have find (entries : List KnownDecl)
      (valid : ∀ fact ∈ entries,
        ∃ proposition : ClosedFormula (Constant (environment instances)),
          erase proposition = some fact.proposition ∧ (model instances source).models proposition)
      (found : lookupKnownList? entries name = some raw) :
      ∃ proposition : ClosedFormula (Constant (environment instances)),
        erase proposition = some raw ∧ (model instances source).models proposition := by
    induction entries with
    | nil => simp [lookupKnownList?] at found
    | cons head tail ih =>
        simp only [lookupKnownList?] at found
        split at found
        · cases found
          exact valid head (List.mem_cons_self)
        · exact ih (fun fact present => valid fact (List.mem_cons_of_mem _ present)) found
  exact find (facts instances) (fact_valid instances source) lookup

theorem checkedDefinitions (instances : List (Ty Base × Ty Base)) :
    CheckedPlainDefinitions (environment instances) where
  body name entry body lookup defined _ := by
    have unfoldingAbsent := SetOperationSemantics.lookup_opaque name entry lookup
    rw [unfoldingAbsent] at defined
    contradiction

theorem definitionEquations (instances : List (Ty Base × Ty Base))
    (source : HenkinModel.{0, 0, w} Unit Symbol) :
    DefinitionEquations (checkedDefinitions instances) (model instances source) where
  equation name entry lookup _ body defined := by
    have unfoldingAbsent := SetOperationSemantics.lookup_opaque name entry lookup
    rw [unfoldingAbsent] at defined
    contradiction

/-- The computed native result has one typed reading that preserves actual
values in every full-domain interpretation of the common material signature.
The normalized syntax is chosen before any set or hyperset model is supplied. -/
theorem normalizeTerm_meaning (instances : List (Ty Base × Ty Base))
    {gamma : Ctx Unit} {value : Ty Unit} (expression : Term Symbol gamma value) :
    ∃ output : Term (Constant (environment instances)) (gamma.map type) (type value),
      erase output = some (normalizeTerm instances expression).1.2 ∧
      ∀ (source : HenkinModel.{0, 0, w} Unit Symbol), source.FullDomains →
        ∀ values : (model instances source).Valuation (gamma.map type),
          (model instances source).denote output values =
            Ty.denoteSubstituteEquiv base (model instances source).Carrier value
              (source.denote expression (SetOperationSemantics.sourceValuation source values)) := by
  obtain ⟨output, erased, meaning⟩ := nativeNormalize_interpretation (checkedDefinitions instances)
    (HOLTermEncoding.encode (term instances expression)) (HOLTermEncoding.native_erased _)
    (normalizeTerm instances expression).2
  refine ⟨output, erased, ?_⟩
  intro source full values
  exact (meaning (model instances source) (definitionEquations instances source) values).trans
    ((HOLTermEncoding.denote_encode _ (fullDomains instances source) _ values).trans
      (denote_term instances source full expression values).symm)

theorem denote_encoded_formula (instances : List (Ty Base × Ty Base))
    (source : HenkinModel.{0, 0, w} Unit Symbol) (full : source.FullDomains)
    {gamma : Ctx Unit} (formula : Formula Symbol gamma)
    (values : (model instances source).Valuation (gamma.map type)) :
    (model instances source).denote (HOLTermEncoding.encode (term instances formula)) values =
      source.denote formula (SetOperationSemantics.sourceValuation source values) :=
  (HOLTermEncoding.denote_encode _ (fullDomains instances source) _ values).trans
    (denote_term instances source full formula values).symm

/-- The guest extensionality axioms have been validated in this model before
native proof soundness is applied. Their declarations supply no material
foundation or anti-foundation premise. -/
theorem accepted_material (instances : List (Ty Base × Ty Base))
    (source : HenkinModel.{0, 0, w} Unit Symbol) (full : source.FullDomains)
    {gamma : Ctx Unit} (assumptions : List (Formula Symbol gamma))
    (conclusion : Formula Symbol gamma) {program : Pf} {fuel depth : Nat}
    (fragment : NativeProof.Fragment (environment instances) depth program)
    (accepted : checkProof (environment instances) fuel depth ((gamma.map type).map reifyType)
      (assumptions.map (fun formula => HOLTermEncoding.native (term instances formula)))
      program (HOLTermEncoding.native (term instances conclusion)) = true)
    (values : (model instances source).Valuation (gamma.map type))
    (satisfied : Soundness.SatisfiesHyps source
      (SetOperationSemantics.sourceValuation source values) assumptions) :
    (source.denote conclusion (SetOperationSemantics.sourceValuation source values)).down := by
  have erased : NativeProof.ErasedHypotheses
      (assumptions.map (fun formula => HOLTermEncoding.encode (term instances formula)))
      (assumptions.map (fun formula => HOLTermEncoding.native (term instances formula))) := by
    change (assumptions.map (fun formula => HOLTermEncoding.encode (term instances formula))).map erase =
      (assumptions.map (fun formula => HOLTermEncoding.native (term instances formula))).map some
    simp only [List.map_map]
    apply List.map_congr_left
    intro formula _
    exact HOLTermEncoding.native_erased _
  have encodedSatisfied : Soundness.SatisfiesHyps (model instances source) values
      (assumptions.map (fun formula => HOLTermEncoding.encode (term instances formula))) := by
    intro formula member
    obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp member
    rw [denote_encoded_formula instances source full]
    exact satisfied original originalMember
  have valid := NativeProof.checkProof_sound (checkedDefinitions instances) (model instances source)
    (definitionEquations instances source) (knownValidity instances source) fragment erased
    (HOLTermEncoding.encode (term instances conclusion)) (HOLTermEncoding.native_erased _)
    accepted values (fun _ => fullDomains instances source _ _) encodedSatisfied
  rwa [denote_encoded_formula instances source full] at valid

theorem accepted_closed (instances : List (Ty Base × Ty Base))
    (source : HenkinModel.{0, 0, w} Unit Symbol) (full : source.FullDomains)
    (assumptions : List (ClosedFormula Symbol)) (conclusion : ClosedFormula Symbol)
    {program : Pf} {fuel depth : Nat}
    (fragment : NativeProof.Fragment (environment instances) depth program)
    (accepted : checkProof (environment instances) fuel depth []
      (assumptions.map (fun formula => HOLTermEncoding.native (term instances formula)))
      program (HOLTermEncoding.native (term instances conclusion)) = true)
    (satisfied : ∀ formula ∈ assumptions, source.models formula) :
    source.models conclusion := by
  have closedTruth (formula : ClosedFormula Symbol) (values : source.Valuation []) :
      source.models formula ↔ (source.denote formula values).down := by
    simp only [HenkinModel.models, PreModel.models]
    apply Iff.of_eq
    apply congrArg (fun valuation : source.Valuation [] => (source.denote formula valuation).down)
    funext value index
    nomatch index
  have hypotheses : Soundness.SatisfiesHyps source
      (SetOperationSemantics.sourceValuation source (gamma := []) (fun index => nomatch index)) assumptions := by
    intro formula present
    exact (closedTruth formula _).mp (satisfied formula present)
  have valid := accepted_material instances source full assumptions conclusion fragment accepted
    (fun index => nomatch index) hypotheses
  exact (closedTruth conclusion _).mpr valid

theorem refused_of_countermodel (instances : List (Ty Base × Ty Base))
    (source : HenkinModel.{0, 0, w} Unit Symbol) (full : source.FullDomains)
    (assumptions : List (ClosedFormula Symbol)) (conclusion : ClosedFormula Symbol)
    {program : Pf} {fuel depth : Nat}
    (fragment : NativeProof.Fragment (environment instances) depth program)
    (satisfied : ∀ formula ∈ assumptions, source.models formula)
    (refuted : ¬ source.models conclusion) :
    checkProof (environment instances) fuel depth []
      (assumptions.map (fun formula => HOLTermEncoding.native (term instances formula)))
      program (HOLTermEncoding.native (term instances conclusion)) = false := by
  apply Bool.eq_false_iff.mpr
  intro accepted
  exact refuted (accepted_closed instances source full assumptions conclusion fragment accepted satisfied)

open Mettapedia.TypeTheory.MaterialSets.Hypersets

/-- Guest extensionality still does not select global membership induction. -/
theorem setInduction_refused (instances : List (Ty Base × Ty Base))
    (presentation : HSet.Presentation.{w}) {program : Pf} {fuel depth : Nat}
    (fragment : NativeProof.Fragment (environment instances) depth program) :
    checkProof (environment instances) fuel depth []
      (Embedding.HypersetHenkinInterpretation.operationTheory.map
        (fun formula => HOLTermEncoding.native (term instances formula)))
      program (HOLTermEncoding.native (term instances setInduction)) = false :=
  refused_of_countermodel instances (Embedding.HypersetHenkinInterpretation.model presentation)
    (Embedding.HypersetHenkinInterpretation.fullDomains presentation) _ _ fragment
    (Embedding.HypersetHenkinInterpretation.operationTheory_valid presentation)
    (Embedding.HypersetHenkinInterpretation.setInduction_invalid presentation)

theorem selfMember_refused (instances : List (Ty Base × Ty Base))
    (presentation : HSet.Presentation.{w}) {program : Pf} {fuel depth : Nat}
    (fragment : NativeProof.Fragment (environment instances) depth program) :
    checkProof (environment instances) fuel depth []
      (Embedding.HypersetHenkinInterpretation.operationTheory.map
        (fun formula => HOLTermEncoding.native (term instances formula)))
      program (HOLTermEncoding.native (term instances Embedding.HypersetHenkinInterpretation.selfMember)) = false :=
  refused_of_countermodel instances (Embedding.WellFoundedHypersetInterpretation.model presentation)
    (Embedding.WellFoundedHypersetInterpretation.fullDomains presentation) _ _ fragment
    (Embedding.HypersetHenkinInterpretation.wellFounded_operationTheory_valid presentation)
    (Embedding.HypersetHenkinInterpretation.wellFounded_refutes_selfMember presentation)

theorem negated_setInduction_refused (instances : List (Ty Base × Ty Base))
    (presentation : HSet.Presentation.{w}) {program : Pf} {fuel depth : Nat}
    (fragment : NativeProof.Fragment (environment instances) depth program) :
    checkProof (environment instances) fuel depth []
      (Embedding.HypersetHenkinInterpretation.operationTheory.map
        (fun formula => HOLTermEncoding.native (term instances formula)))
      program (HOLTermEncoding.native (term instances (.not setInduction))) = false :=
  refused_of_countermodel instances (Embedding.WellFoundedHypersetInterpretation.model presentation)
    (Embedding.WellFoundedHypersetInterpretation.fullDomains presentation) _ _ fragment
    (Embedding.HypersetHenkinInterpretation.wellFounded_operationTheory_valid presentation)
    (fun negative => negative (Embedding.WellFoundedHypersetInterpretation.setInduction_valid presentation))

theorem negated_selfMember_refused (instances : List (Ty Base × Ty Base))
    (presentation : HSet.Presentation.{w}) {program : Pf} {fuel depth : Nat}
    (fragment : NativeProof.Fragment (environment instances) depth program) :
    checkProof (environment instances) fuel depth []
      (Embedding.HypersetHenkinInterpretation.operationTheory.map
        (fun formula => HOLTermEncoding.native (term instances formula)))
      program (HOLTermEncoding.native (term instances (.not Embedding.HypersetHenkinInterpretation.selfMember))) = false :=
  refused_of_countermodel instances (Embedding.HypersetHenkinInterpretation.model presentation)
    (Embedding.HypersetHenkinInterpretation.fullDomains presentation) _ _ fragment
    (Embedding.HypersetHenkinInterpretation.operationTheory_valid presentation)
    (fun negative => negative (Embedding.HypersetHenkinInterpretation.selfMember_valid presentation))

#print axioms forget_extend
#print axioms sourceReduct_standard
#print axioms denote_term
#print axioms fact_valid
#print axioms knownValidity
#print axioms accepted_material
#print axioms accepted_closed
#print axioms setInduction_refused
#print axioms selfMember_refused
#print axioms negated_setInduction_refused
#print axioms negated_selfMember_refused
#print axioms missing_functional_refused
#print axioms normalizeTerm
#print axioms normalizeTerm_meaning

end Mettapedia.Languages.Megalodon.SetOperationExtensionality
