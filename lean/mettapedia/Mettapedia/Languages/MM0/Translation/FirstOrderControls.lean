import Mettapedia.Languages.MM0.Translation.FirstOrderCertificates
import Mettapedia.Languages.MM0.Translation.FirstOrderModules
import Mettapedia.Languages.MM0.Translation.FirstOrderPrinting
import Mettapedia.GSLT.LanguageDef.ModuleAlgebra.SortedFirstOrderAuthoring
import Mettapedia.GSLT.LanguageDef.ModuleAlgebra.UpstreamTheoryQuotation

/-!
# First-order MM0 translation controls

The existing module quotation authors the syntax. The controls compare its
named, many-sorted declarations with the generated MM0 signature and exercise
open contexts, mixed-sort substitutions, missing variables and conflicting
declaration names. Typed inference rules generate real MM0 axioms; concrete
certificates check against them and reflect to the source derivability relation.
Wrong sorts, reordered children and future rule references are refused.
No independently restated term grammar is used.

The last section authors the propositional connectives of the upstream
`set.mm0` as definitions. The generated theory holds an MM0 definition for
each and none for a primitive connective. A certificate with one conversion
step is accepted by the source checker and, compiled, by the MM0 checker; a
wrong unfolding and a forged conversion are refused by both. A language
with an equation that is not a definition is not admitted.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MM0.Translation.FirstOrderControls

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.LanguageDefDSL
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.LanguageDef.ModuleAlgebra.UpstreamTheoryQuotation
open Kernel FirstOrderSyntax FirstOrderTyping
open Mettapedia.GSLT.LanguageDef.SortedFirstOrderRules
open Mettapedia.GSLT.LanguageDef.DefinitionalEquations
open FirstOrderRules

def syntaxModule : QuotedTheory := moduleTheory! Theory ImplicationSyntax() {
  Types { wff; set; }
  Exports { wff; set; }
  Terms {
    truth . |- "T" : wff;
    imp . ph:wff, ps:wff |- "(" ph "->" ps ")" : wff;
    emptySet . |- "{}" : set;
  }
}

theorem syntax_admitted : Signature.check syntaxModule.toLanguageDef = true := by decide

def syntaxSignature : Signature :=
  (Signature.admit? syntaxModule.toLanguageDef).get
    ((Signature.admit?_isSome_iff _).mpr syntax_admitted)

theorem constructor_names_retained : syntaxSignature.names = ["truth", "imp", "emptySet"] := by
  rfl

theorem implication_declaration_compiled :
    syntaxSignature.termSignature 1 = some {
      arguments := [.regular 0 ∅, .regular 0 ∅]
      resultSort := 0
      dependencies := ∅ } := by rfl

theorem notation_retained :
    (syntaxSignature.language.terms[1]?).map (·.syntaxPattern) = some
      [.terminal "(", .nonTerminal "ph", .terminal "->", .nonTerminal "ps", .terminal ")"] := by
  rfl

def openImplication : Pattern := .apply "imp" [.apply "truth" [], .bvar 0]

def encodedImplication : Preterm := .app (.app (.term 1) (.term 0)) (.var 0)

theorem implication_encoded :
    Encodes syntaxSignature.names openImplication encodedImplication := by
  apply encode_sound
  rw [constructor_names_retained]
  simp [openImplication, encodedImplication, encode, encodeList, index?, Preterm.applyArgs]

theorem open_context_encoded :
    ContextEncodes syntaxSignature.sorts [.base "wff"] [.regular 0 ∅] :=
  (context?_eq_some_iff _ _ _).mp (by decide)

theorem implication_source_typed :
    HasType syntaxSignature.language FreeTypeContext.empty [.base "wff"]
      openImplication (.base "wff") := by
  apply (typing_iff (sort := 0) implication_encoded open_context_encoded (by decide)).mpr
  exact Preterm.infer_sound (by decide)

theorem implication_round_trip :
    decode syntaxSignature.names encodedImplication = some openImplication :=
  implication_encoded.decode

theorem mixed_sort_substitution_admitted :
    Substitution.checkAdmissible syntaxSignature.termSignature
      [.regular 0 ∅, .regular 1 ∅] [] [.term 0, .term 2] = true := by decide

theorem wrong_sort_substitution_refused :
    Substitution.checkAdmissible syntaxSignature.termSignature
      [.regular 0 ∅, .regular 1 ∅] [] [.term 2, .term 0] = false := by decide

theorem wrong_sort_implication_refused :
    Preterm.infer syntaxSignature.termSignature []
      (.app (.app (.term 1) (.term 0)) (.term 2)) = none := by decide

theorem missing_context_variable_refused :
    Preterm.infer syntaxSignature.termSignature [.regular 0 ∅]
      (.app (.app (.term 1) (.term 0)) (.var 1)) = none := by decide

theorem incomplete_application_refused_as_formula :
    ¬ Preterm.HasType syntaxSignature.termSignature [] (.app (.term 1) (.term 0)) [] 0 := by
  intro typing
  have observed := typing.eval
  have actual : Preterm.infer syntaxSignature.termSignature [] (.app (.term 1) (.term 0)) =
      some ([.regular 0 ∅], 0) := by decide
  rw [actual] at observed
  cases observed

def conflictingSyntax : LanguageDef := {
  syntaxModule.toLanguageDef with
  «terms» := syntaxModule.terms ++ [
    { label := "truth", category := "set", params := [], syntaxPattern := [.terminal "bad"] }] }

theorem conflicting_name_refused : Signature.check conflictingSyntax = false := by decide

def missingSortSyntax : QuotedTheory := moduleTheory! Theory MissingSortSyntax() {
  Types { wff; }
  Terms {
    bad . ph:missing |- "bad" ph : wff;
  }
}

theorem missing_parameter_sort_refused :
    Signature.check missingSortSyntax.toLanguageDef = false := by decide

def truthIntroduction : Rule := {
  row := { id := "truth_intro", vars := [], premises := [], conclusion := .apply "truth" [] }
  variableTypes := [] }

def implicationIdentity : Rule := {
  row := {
    id := "imp_identity"
    vars := ["ph"]
    premises := []
    conclusion := .apply "imp" [.fvar "ph", .fvar "ph"] }
  variableTypes := [.base "wff"] }

def implicationElimination : Rule := {
  row := {
    id := "modus_ponens"
    vars := ["ph", "ps"]
    premises := [.fvar "ph", .apply "imp" [.fvar "ph", .fvar "ps"]]
    conclusion := .fvar "ps" }
  variableTypes := [.base "wff", .base "wff"] }

private theorem statement_of_check {boundTypes : List TypeExpr} {context : Context}
    {pattern : Pattern} {expression : Preterm}
    (contexts : context? syntaxSignature.sorts boundTypes = some context)
    (encoded : encode syntaxSignature.names pattern = some expression)
    (typed : Preterm.infer syntaxSignature.termSignature context expression = some ([], 0)) :
    Statement syntaxSignature.language ["wff"] boundTypes pattern := by
  refine ⟨"wff", by simp, ?_⟩
  exact (typing_iff (encode_sound encoded)
    ((context?_eq_some_iff _ _ _).mp contexts) (by decide)).mpr
    (Preterm.infer_sound typed)

theorem truth_introduction_formed : truthIntroduction.WellFormed syntaxSignature.language ["wff"] := by
  refine ⟨by decide, rfl, ?_, .nil, .constructor .nil, ?_, ?_⟩
  · simp [truthIntroduction]
  · simp [truthIntroduction]
  · exact statement_of_check (context := []) (expression := .term 0) (by decide)
      (by decide +kernel) (by decide)

theorem implication_identity_formed : implicationIdentity.WellFormed syntaxSignature.language ["wff"] := by
  refine ⟨by decide, rfl, ?_, .nil,
    .constructor (.cons (.metavariable (by simp [implicationIdentity]))
      (.cons (.metavariable (by simp [implicationIdentity])) .nil)), ?_, ?_⟩
  · intro type member
    simp only [implicationIdentity, List.mem_singleton] at member
    subst type
    exact ⟨"wff", rfl, by decide⟩
  · simp [implicationIdentity]
  · apply statement_of_check (context := [.regular 0 ∅])
      (expression := .app (.app (.term 1) (.var 0)) (.var 0)) (by decide)
    · decide +kernel
    · decide

theorem implication_elimination_formed :
    implicationElimination.WellFormed syntaxSignature.language ["wff"] := by
  refine ⟨by decide, rfl, ?_,
    .cons (.metavariable (by simp [implicationElimination]))
      (.cons (.constructor (.cons (.metavariable (by simp [implicationElimination]))
        (.cons (.metavariable (by simp [implicationElimination])) .nil))) .nil),
    .metavariable (by simp [implicationElimination]), ?_, ?_⟩
  · intro type member
    have same : type = .base "wff" := by simpa [implicationElimination] using member
    subst type
    exact ⟨"wff", rfl, by decide⟩
  · intro pattern member
    rcases (show pattern = .fvar "ph" ∨
        pattern = .apply "imp" [.fvar "ph", .fvar "ps"] by
          simpa [implicationElimination] using member) with rfl | rfl
    · apply statement_of_check (context := [.regular 0 ∅, .regular 0 ∅])
        (expression := .var 0) (by decide)
      · decide +kernel
      · decide
    · apply statement_of_check (context := [.regular 0 ∅, .regular 0 ∅])
        (expression := .app (.app (.term 1) (.var 0)) (.var 1)) (by decide)
      · decide +kernel
      · decide
  · apply statement_of_check (context := [.regular 0 ∅, .regular 0 ∅])
      (expression := .var 1) (by decide)
    · decide +kernel
    · decide

def implicationPresentation : Presentation where
  syntaxSignature := syntaxSignature
  judgmentSorts := ["wff"]
  rules := [truthIntroduction, implicationIdentity, implicationElimination]
  definitional := checkDefinitional_sound (by decide +kernel)
  noRewrites := rfl
  ordinaryPolicies := by
    intro constructor member
    change constructor ∈ syntaxModule.terms at member
    have all : syntaxModule.terms.all (fun row =>
        decide (row.evalPolicy? = none ∧ row.algebra? = none)) = true := by decide +kernel
    exact of_decide_eq_true ((List.all_eq_true.mp all) constructor member)
  declaredJudgments := by
    intro sortName member
    simp only [List.mem_singleton] at member
    subst sortName
    decide
  distinctRules := by decide
  formedRules := by
    intro rule member
    rcases (show rule = truthIntroduction ∨ rule = implicationIdentity ∨
        rule = implicationElimination by simpa using member) with rfl | rfl | rfl
    · exact truth_introduction_formed
    · exact implication_identity_formed
    · exact implication_elimination_formed

def truthCertificate : ProofWitness := .theoremApp 0 [] []

def identityCertificate (argument : Preterm) : ProofWitness := .theoremApp 1 [argument] []

def eliminationCertificate : ProofWitness :=
  .theoremApp 2 [.term 0, .term 0] [truthCertificate, identityCertificate (.term 0)]

theorem compiled_truth_certificate_accepted :
    ProofWitness.check implicationPresentation.theory.termSignature
      implicationPresentation.theory.definitionSignature implicationPresentation.theory.theoremSignature
      [] [] truthCertificate (.term 0) = true := by decide +kernel

theorem compiled_elimination_certificate_accepted :
    ProofWitness.check implicationPresentation.theory.termSignature
      implicationPresentation.theory.definitionSignature implicationPresentation.theory.theoremSignature
      [] [] eliminationCertificate (.term 0) = true := by decide +kernel

theorem elimination_reflects_to_source :
    Mettapedia.GSLT.LanguageDef.SortedFirstOrderRules.Derives syntaxSignature.language
      implicationPresentation.rules [] [] (.apply "truth" []) := by
  apply (Presentation.derivability_iff_checked_of_equationFree
    (presentation := implicationPresentation) rfl
    (.nil) (.nil) (encode_sound (expression := .term 0) (by
      simp [encode, encodeList, index?, constructor_names_retained, Preterm.applyArgs, implicationPresentation]))).mpr
  exact ⟨eliminationCertificate, compiled_elimination_certificate_accepted⟩

theorem reordered_children_refused :
    ProofWitness.check implicationPresentation.theory.termSignature
      implicationPresentation.theory.definitionSignature implicationPresentation.theory.theoremSignature
      [] [] (.theoremApp 2 [.term 0, .term 0]
        [identityCertificate (.term 0), truthCertificate]) (.term 0) = false := by decide +kernel

theorem wrong_sort_rule_instance_refused :
    ProofWitness.proof? implicationPresentation.theory.termSignature
      implicationPresentation.theory.definitionSignature implicationPresentation.theory.theoremSignature
      [] [] (identityCertificate (.term 2)) = none := by decide +kernel

theorem future_rule_reference_refused :
    ProofWitness.proof? implicationPresentation.theory.termSignature
      implicationPresentation.theory.definitionSignature implicationPresentation.theory.theoremSignature
      [] [] (.theoremApp 3 [] []) = none := by decide +kernel

theorem open_certificate_accepted :
    ProofWitness.check implicationPresentation.theory.termSignature
      implicationPresentation.theory.definitionSignature implicationPresentation.theory.theoremSignature
      [.regular 0 ∅, .regular 1 ∅] [.var 0]
      (.theoremApp 2 [.var 0, .var 0] [.hyp 0, identityCertificate (.var 0)]) (.var 0) = true := by decide +kernel

open Mettapedia.GSLT.LanguageDef.CertificateGSLT

def namedTruthCertificate : RawOpenProof := .node ⟨⟨"truth_intro"⟩, []⟩ []

def namedIdentityCertificate (argument : Pattern) : RawOpenProof :=
  .node ⟨⟨"imp_identity"⟩, [argument]⟩ []

def namedEliminationCertificate : RawOpenProof :=
  .node ⟨⟨"modus_ponens"⟩, [.apply "truth" [], .apply "truth" []]⟩
    [namedTruthCertificate, namedIdentityCertificate (.apply "truth" [])]

theorem named_certificate_compiles :
    FirstOrderCertificates.compile? implicationPresentation namedEliminationCertificate =
      some eliminationCertificate := by
  simp [FirstOrderCertificates.compile?, FirstOrderCertificates.compileChildren?,
    namedEliminationCertificate, namedTruthCertificate, namedIdentityCertificate,
    eliminationCertificate, truthCertificate, identityCertificate, implicationPresentation,
    truthIntroduction, implicationIdentity, implicationElimination,
    constructor_names_retained, index?, encodeList, encode, Preterm.applyArgs]

theorem named_certificate_source_checked :
    SortedFirstOrderRules.proof? syntaxSignature.language implicationPresentation.rules
      [] [] namedEliminationCertificate = some (.apply "truth" []) := by decide +kernel

theorem named_certificate_target_checked :
    FirstOrderCertificates.checkCompiled implicationPresentation [] []
      namedEliminationCertificate (.term 0) = true := by decide +kernel

theorem named_wrong_sort_refused_at_source :
    SortedFirstOrderRules.proof? syntaxSignature.language implicationPresentation.rules
      [] [] (namedIdentityCertificate (.apply "emptySet" [])) = none := by decide +kernel

theorem named_wrong_sort_refused_at_target :
    FirstOrderCertificates.checkCompiled implicationPresentation [] []
      (namedIdentityCertificate (.apply "emptySet" []))
      (.app (.app (.term 1) (.term 2)) (.term 2)) = false := by decide +kernel

theorem unknown_named_rule_refused :
    FirstOrderCertificates.compile? implicationPresentation (.node ⟨⟨"future_rule"⟩, []⟩ []) =
      none := by decide +kernel

theorem extra_child_refused :
    FirstOrderCertificates.checkCompiled implicationPresentation [] []
      (.node ⟨⟨"truth_intro"⟩, []⟩ [namedTruthCertificate]) (.term 0) = false := by decide +kernel

theorem open_named_certificate_compiles :
    FirstOrderCertificates.compile? implicationPresentation
      (.node ⟨⟨"modus_ponens"⟩, [.bvar 0, .bvar 0]⟩
        [.premise 0, namedIdentityCertificate (.bvar 0)]) =
      some (.theoremApp 2 [.var 0, .var 0] [.hyp 0, identityCertificate (.var 0)]) := by
  simp [FirstOrderCertificates.compile?, FirstOrderCertificates.compileChildren?,
    namedIdentityCertificate, identityCertificate, implicationPresentation,
    truthIntroduction, implicationIdentity, implicationElimination,
    constructor_names_retained, index?, encodeList, encode]

theorem open_named_certificate_source_checked :
    SortedFirstOrderRules.proof? syntaxSignature.language implicationPresentation.rules
      [.base "wff", .base "set"] [.bvar 0]
      (.node ⟨⟨"modus_ponens"⟩, [.bvar 0, .bvar 0]⟩
        [.premise 0, namedIdentityCertificate (.bvar 0)]) = some (.bvar 0) := by decide +kernel

theorem bad_local_occurrence_refused :
    FirstOrderCertificates.checkCompiled implicationPresentation [.regular 0 ∅] [.var 0]
      (.premise 1) (.var 0) = false := by decide +kernel

/-! ## Origin-sensitive composition and real reference relocation -/

open FirstOrderModules

def moduleEntry (origin : String) (body : Declaration) :
    ModuleAlgebra.Entry String String Declaration := ⟨origin, body.exposedName, body⟩

def baseEntries : Finset (ModuleAlgebra.Entry String String Declaration) := {
  moduleEntry "Syntax.wff" (.sort (.plain "wff") true),
  moduleEntry "Syntax.set" (.sort (.plain "set") false),
  moduleEntry "Syntax.truth" (.constructor ((syntaxModule.terms[0]?).get (by decide))),
  moduleEntry "Syntax.imp" (.constructor ((syntaxModule.terms[1]?).get (by decide))),
  moduleEntry "Syntax.emptySet" (.constructor ((syntaxModule.terms[2]?).get (by decide))) }

def leftModule : Module String :=
  ⟨baseEntries ∪ {moduleEntry "Introduction.truth" (.axiom truthIntroduction)}, by decide +kernel⟩

def rightModule : Module String :=
  ⟨baseEntries ∪ {moduleEntry "Identity.imp" (.axiom implicationIdentity),
    moduleEntry "Elimination.imp" (.axiom implicationElimination)}, by decide +kernel⟩

def joinedModule : Module String := ⟨leftModule.val ∪ rightModule.val, by decide +kernel⟩

theorem source_diamond_join : ModuleAlgebra.join leftModule rightModule = some joinedModule :=
  ModuleAlgebra.join_eq_some_iff.mpr rfl

theorem left_module_supported : SupportedModule implicationPresentation leftModule := by decide +kernel

theorem right_module_supported : SupportedModule implicationPresentation rightModule := by decide +kernel

theorem compiled_diamond_agrees :
    (compileModule? implicationPresentation leftModule).bind (fun left =>
      (compileModule? implicationPresentation rightModule).bind (ModuleAlgebra.join left)) =
        compileModule? implicationPresentation joinedModule :=
  compile_join left_module_supported right_module_supported source_diamond_join

theorem joined_module_keeps_shared_origins :
    (ModuleAlgebra.origins joinedModule.val).card = 8 := by decide +kernel

def conflictingModule : Module String :=
  ⟨{moduleEntry "Syntax.wff" (.sort (.plain "wff") false)}, by decide⟩

theorem conflicting_sort_refuses_join : ModuleAlgebra.join leftModule conflictingModule = none := by
  decide +kernel

theorem wrong_provability_flag_refused :
    FirstOrderModules.compile? implicationPresentation (.sort (.plain "wff") false) = none := by
  decide +kernel

def reorderedSignature : Signature :=
  (Signature.admit? { syntaxModule.toLanguageDef with
      «types» := [.plain "set", .plain "wff"]
      «terms» := [((syntaxModule.terms[2]?).get (by decide)),
        ((syntaxModule.terms[0]?).get (by decide)), ((syntaxModule.terms[1]?).get (by decide))] }).get
    (by decide +kernel)

theorem constructor_relocation_matches_recompilation :
    (declaration? syntaxSignature.sorts ((syntaxModule.terms[1]?).get (by decide))).bind
      (TermDecl.relocate? (references? syntaxSignature.sorts reorderedSignature.sorts)) =
        declaration? reorderedSignature.sorts ((syntaxModule.terms[1]?).get (by decide)) := by
  decide +kernel

theorem axiom_relocation_matches_recompilation :
    (rule? syntaxSignature implicationElimination).bind
      (TheoremDecl.relocate? (references? syntaxSignature.sorts reorderedSignature.sorts)
        (references? syntaxSignature.names reorderedSignature.names)) =
      rule? reorderedSignature implicationElimination := by decide +kernel

theorem unresolved_constructor_relocation_refused :
    Preterm.relocateTerms? (references? ["truth", "missing"] ["truth"]) (.term 1) = none := by
  decide

def reorderedPresentation : Presentation :=
  (Presentation.admit? reorderedSignature.language ["wff"]
    [implicationElimination, truthIntroduction, implicationIdentity]).get (by decide +kernel)

def leftPresentation : Presentation :=
  (Presentation.admit? syntaxSignature.language ["wff"] [truthIntroduction]).get (by decide +kernel)

def rightPresentation : Presentation :=
  (Presentation.admit? syntaxSignature.language ["wff"]
    [implicationIdentity, implicationElimination]).get (by decide +kernel)

theorem certificate_relocation_matches_recompilation :
    (FirstOrderCertificates.compile? implicationPresentation namedEliminationCertificate).bind
      (FirstOrderCertificates.relocate?
        (references? implicationPresentation.syntaxSignature.names reorderedPresentation.syntaxSignature.names)
        (references? (implicationPresentation.rules.map (fun row => row.row.id))
          (reorderedPresentation.rules.map (fun row => row.row.id)))) =
      FirstOrderCertificates.compile? reorderedPresentation namedEliminationCertificate := by
  have total : (FirstOrderCertificates.compile? reorderedPresentation namedEliminationCertificate).isSome = true := by
    decide +kernel
  cases after : FirstOrderCertificates.compile? reorderedPresentation namedEliminationCertificate with
  | none => simp [after] at total
  | some image =>
      rw [named_certificate_compiles, Option.bind_some]
      exact FirstOrderCertificates.compile_relocate named_certificate_compiles after

theorem relocated_module_join_agrees :
    ModuleAlgebra.join
      (relocateModule leftPresentation reorderedPresentation
        (ModuleAlgebra.mapBodies (FirstOrderModules.compile? leftPresentation) leftModule))
      (relocateModule rightPresentation reorderedPresentation
        (ModuleAlgebra.mapBodies (FirstOrderModules.compile? rightPresentation) rightModule)) =
      some (ModuleAlgebra.mapBodies (FirstOrderModules.compile? reorderedPresentation) joinedModule) :=
  compile_join_relocated (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) source_diamond_join

theorem unknown_rule_relocation_refused :
    FirstOrderCertificates.relocate? (some ·) (references? ["missing"] ["truth_intro"])
      (.theoremApp 0 [] []) = none := by decide +kernel

/-! ## The shared module surface and human-facing MM0 notation -/

open ModuleAlgebra.SortedFirstOrderAuthoring

def quotedInferenceTheory : QuotedInferenceTheory := inferenceTheory! Theory ImplicationSyntax() {
  Types { wff; set; }
  Exports { wff; set; }
  Terms {
    truth . |- "T" : wff;
    imp . ph:wff, ps:wff |- "(" ph "->" ps ")" : wff;
    emptySet . |- "{}" : set;
  }
  Judgments { wff; }
  Inferences {
    truth_intro () : [] => truth;
    imp_identity (ph:wff) : [] => (imp ph ph);
    modus_ponens (ph:wff, ps:wff) : [ph, (imp ph ps)] => ps;
  }
}

theorem quotation_keeps_syntax : quotedInferenceTheory.toLanguageDef = syntaxModule.toLanguageDef := by
  rfl

theorem quotation_resolves_rules : ModuleAlgebra.SortedFirstOrderAuthoring.rules quotedInferenceTheory =
    implicationPresentation.rules := by decide +kernel

theorem quotation_keeps_provable_sorts :
    ModuleAlgebra.SortedFirstOrderAuthoring.judgmentSorts quotedInferenceTheory = ["wff"] := by rfl

theorem printed_names_retained :
    FirstOrderPrinting.constructorNames implicationPresentation = ["truth", "imp", "emptySet"] := by
  decide +kernel

theorem printed_infix_formula :
    FirstOrderPrinting.expression? implicationPresentation ["ph"]
      (.app (.app (.term 1) (.term 0)) (.var 0)) = some "((T) -> ph)" := by decide +kernel

theorem printed_standard_prefix_formula :
    FirstOrderPrinting.expression? implicationPresentation ["ph"]
      (.app (.app (.term 1) (.term 0)) (.var 0)) false = some "(imp (truth) ph)" := by decide +kernel

theorem printed_rule_keeps_formals_and_premises :
    FirstOrderPrinting.axiomDeclaration? implicationPresentation
      (2, ((rule? syntaxSignature implicationElimination).get (by decide +kernel))) =
      some "axiom modus_ponens (ph: wff) (ps: wff):\n  $ ph $ >\n  $ (ph -> ps) $ >\n  $ ps $;" := by
  decide +kernel

theorem invalid_printed_reference_refused :
    FirstOrderPrinting.expression? implicationPresentation [] (.term 9) = none := by decide +kernel

theorem partial_constructor_printing_refused :
    FirstOrderPrinting.expression? implicationPresentation [] (.app (.term 1) (.term 0)) = none := by
  decide +kernel

theorem variable_head_printing_refused :
    FirstOrderPrinting.expression? implicationPresentation ["ph"] (.app (.var 0) (.term 0)) = none := by
  decide +kernel

theorem qualified_identifier_fallback :
    FirstOrderPrinting.externalName ["A.ph"] "term" 2 "A.ph" = "mm0__term_2" := by decide

theorem constructor_name_cannot_capture_local :
    FirstOrderPrinting.parameterNames ["truth"] ["truth"] = ["mm0__var_0"] := by decide +kernel

theorem quoted_rules_admitted :
    (FirstOrderModules.admitQuotation? quotedInferenceTheory).isSome = true := by decide +kernel

theorem wrong_formal_sort_refused :
    Rule.check syntaxSignature.language ["wff"]
      { implicationIdentity with variableTypes := [.base "set"] } = false := by decide +kernel

theorem undeclared_metavariable_refused :
    Rule.check syntaxSignature.language ["wff"]
      { truthIntroduction with row := { truthIntroduction.row with conclusion := .fvar "missing" } } =
      false := by decide +kernel

theorem malformed_unused_premise_refused :
    Rule.check syntaxSignature.language ["wff"]
      { truthIntroduction with row := {
        truthIntroduction.row with premises := [.apply "emptySet" []] } } = false := by decide +kernel

theorem undeclared_judgment_sort_refused :
    Presentation.check syntaxSignature.language ["missing"] [] = false := by decide +kernel

theorem repeated_rule_name_refused :
    Presentation.check syntaxSignature.language ["wff"]
      [truthIntroduction, truthIntroduction] = false := by decide +kernel

/-! ## Definitions: the propositional connectives of `set.mm0` -/

namespace Definitions

open Mettapedia.GSLT.LanguageDef.SortedFirstOrderConversion
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open FirstOrderConversion

/-- Implication and negation are primitive. The biconditional, conjunction
and disjunction are defined as in the upstream `set.mm0`. -/
def propositional : QuotedInferenceTheory := inferenceTheory! Theory Propositional() {
  Types { wff; }
  Exports { wff; }
  Terms {
    wi . ph:wff, ps:wff |- "(" ph "->" ps ")" : wff;
    wn . ph:wff |- "~" ph : wff;
    wb . ph:wff, ps:wff |- "(" ph "<->" ps ")" : wff;
    wa . ph:wff, ps:wff |- "(" ph "/\\" ps ")" : wff;
    wo . ph:wff, ps:wff |- "(" ph "\\/" ps ")" : wff;
  }
  Equations {
    (wb ph ps) == (wn (wi (wi ph ps) (wn (wi ps ph))));
    (wa ph ps) == (wn (wi ph (wn ps)));
    (wo ph ps) == (wi (wn ph) ps);
  }
  Judgments { wff; }
  Inferences {
    ax_1 (ph:wff, ps:wff) : [] => (wi ph (wi ps ph));
    ax_2 (ph:wff, ps:wff, ch:wff) : [] =>
      (wi (wi ph (wi ps ch)) (wi (wi ph ps) (wi ph ch)));
    ax_3 (ph:wff, ps:wff) : [] => (wi (wi (wn ph) (wn ps)) (wi ps ph));
    ax_mp (ph:wff, ps:wff) : [ph, (wi ph ps)] => ps;
  }
}

theorem admitted : (FirstOrderModules.admitQuotation? propositional).isSome = true := by
  decide +kernel

def presentation : Presentation := (FirstOrderModules.admitQuotation? propositional).get admitted

theorem definitions_read : presentation.rows.map (·.head) = ["wb", "wa", "wo"] := by
  decide +kernel

def wi (left right : Pattern) : Pattern := .apply "wi" [left, right]
def wn (inner : Pattern) : Pattern := .apply "wn" [inner]
def wa (left right : Pattern) : Pattern := .apply "wa" [left, right]

def p : Pattern := .bvar 0
def q : Pattern := .bvar 1

/-- The primitive form of the conjunction of the two variables. -/
def body : Pattern := wn (wi p (wn q))

def sourceContext : List TypeExpr := [.base "wff", .base "wff"]
def targetContext : Context := [.regular 0 ∅, .regular 0 ∅]

/-! ### The generated theory -/

/-- Conjunction is the fourth constructor. Its MM0 body is its definition
with the formals numbered, and it has no dummy variable. -/
theorem conjunction_body :
    presentation.theory.definitionSignature 3 =
      some ⟨[], .app (.term 1) (.app (.app (.term 0) (.var 0)) (.app (.term 1) (.var 1)))⟩ := by
  decide +kernel

theorem primitive_has_no_body :
    presentation.theory.definitionSignature 0 = none ∧
      presentation.theory.definitionSignature 1 = none := by decide +kernel

/-- Sorts, the two primitive constructors, the three definitions in
authored order, then the four axioms. -/
theorem admission_order :
    (FirstOrderAdmission.admissions presentation).map (fun admission =>
      match admission with
      | .sort _ _ => "sort"
      | .term _ _ => "term"
      | .definition _ _ _ => "def"
      | .axiomDecl _ _ => "axiom"
      | .theoremDecl _ _ _ _ => "theorem") =
      ["sort", "term", "term", "def", "def", "def", "axiom", "axiom", "axiom", "axiom"] := by
  decide +kernel

/-- The generated declarations are admitted in that order from the empty
MM0 theory. -/
theorem theory_admitted :
    Theory.run? {} (FirstOrderAdmission.admissions presentation) =
      some (FirstOrderAdmission.chronological presentation) :=
  (Theory.run_eq_some_iff _ _ _).mpr (FirstOrderAdmission.admitted presentation)

/-! ### A certificate with a conversion step -/

/-- The usual five-step proof of `body -> body`. -/
def identityProof : ModuloProof :=
  .node ⟨⟨"ax_mp"⟩, [wi body (wi body body), wi body body]⟩
    [.node ⟨⟨"ax_1"⟩, [body, body]⟩ [],
      .node ⟨⟨"ax_mp"⟩,
          [wi body (wi (wi body body) body), wi (wi body (wi body body)) (wi body body)]⟩
        [.node ⟨⟨"ax_1"⟩, [body, wi body body]⟩ [],
          .node ⟨⟨"ax_2"⟩, [body, wi body body, body]⟩ []]]

/-- `(p /\ q) -> ~(p -> ~q)`: the identity proof, then one conversion under
the implication. -/
def conjunctionElimination : ModuloProof := .convert (wi (wa p q) body) identityProof

def encoded (pattern : Pattern) : Preterm :=
  (encode presentation.syntaxSignature.names pattern).getD (.var 0)

theorem accepted_at_source :
    proofModulo? presentation.rows presentation.syntaxSignature.language presentation.rules
      sourceContext [] conjunctionElimination = some (wi (wa p q) body) := by decide +kernel

/-- The compiled certificate, conversion included, is accepted by the MM0
checker in the generated theory. -/
theorem accepted_by_mm0 :
    FirstOrderCertificates.checkCompiledModulo presentation [] targetContext []
      conjunctionElimination (encoded (wi (wa p q) body)) = true := by decide +kernel

/-- The theorem is derivable modulo the definitions: the MM0 acceptance
reflects to the source. -/
theorem derivable_at_source :
    DerivesModulo (fun _ _ _ => []) presentation.syntaxSignature.language presentation.rules
      sourceContext [] (wi (wa p q) body) := by
  have contexts : ContextEncodes presentation.syntaxSignature.sorts sourceContext targetContext :=
    (context?_eq_some_iff _ _ _).mp (by decide +kernel)
  have target : Encodes presentation.syntaxSignature.names (wi (wa p q) body)
      (encoded (wi (wa p q) body)) := encode_sound (by decide +kernel)
  exact (derivesModulo_iff_accepted presentation.definitionalRows presentation.distinctRules _).mpr
    ⟨_, ((FirstOrderCertificates.checkCompiledModulo_iff contexts .nil target).mp
      accepted_by_mm0)⟩

/-! ### What is refused -/

/-- Swapping the two formulas is not the definition: refused at the source. -/
theorem wrong_unfolding_refused_at_source :
    proofModulo? presentation.rows presentation.syntaxSignature.language presentation.rules
      sourceContext [] (.convert (wi (wa q p) body) identityProof) = none := by decide +kernel

/-- And refused by the MM0 checker after compilation. -/
theorem wrong_unfolding_refused_by_mm0 :
    FirstOrderCertificates.checkCompiledModulo presentation [] targetContext []
      (.convert (wi (wa q p) body) identityProof) (encoded (wi (wa q p) body)) = false := by
  decide +kernel

/-- A conversion that merely asserts its target, with no unfolding, is not
accepted for the identity proof. -/
theorem forged_conversion_refused :
    ((FirstOrderCertificates.compileModulo? presentation [] identityProof).map (fun child =>
      ProofWitness.check presentation.theory.termSignature presentation.theory.definitionSignature
        presentation.theory.theoremSignature targetContext []
        (.conversion (.refl (encoded (wi (wa p q) body))) child)
        (encoded (wi (wa p q) body)))) = some false := by decide +kernel

/-- Commutativity is an equation and not a definition. The backend does not
admit the language. -/
def commutative : QuotedInferenceTheory := inferenceTheory! Theory Commutative() {
  Types { wff; }
  Exports { wff; }
  Terms {
    wn . ph:wff |- "~" ph : wff;
    wa . ph:wff, ps:wff |- "(" ph "/\\" ps ")" : wff;
  }
  Equations { (wa ph ps) == (wa ps ph); }
  Judgments { wff; }
  Inferences { }
}

theorem commutative_refused : (FirstOrderModules.admitQuotation? commutative).isSome = false := by
  decide +kernel

/-! ### Printed text -/

theorem definition_printed :
    (FirstOrderAdmission.definitionRows presentation)[1]?.bind
      (FirstOrderPrinting.definitionDeclaration? presentation) =
      some "def wa (ph: wff) (ps: wff): wff = $ (wn (wi ph (wn ps))) $;" := by decide +kernel

theorem theory_printed : (FirstOrderPrinting.theory? presentation).isSome = true := by
  decide +kernel

end Definitions

end Mettapedia.Languages.MM0.Translation.FirstOrderControls
