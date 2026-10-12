import Mettapedia.GSLT.LanguageDef.ModuleAlgebra.NativeAuthoring
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.RuleExecutionProgram
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.MatchAutomataSourceExecution
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.ContextualRuleExecution

/-!
# Checked imports and complete language-fragment execution in PeTTa

The retained source assembles all four declaration families through the
canonical list append operation. The corresponding module operation is
`NativeAuthoring.assembleRaw`; it precedes whole-language validation and
nullary resolution. Explicit import contracts implement the existing coherent
origin and structural-view operations through the shared checked list union.
The first identical declaration is kept; conflicting declarations are refused.
Declaration identity is separate from the ordered rule occurrences in its
body. This bridge treats declaration rows as opaque data: supplied row encoders
are explicit, and assembly neither interprets nor discards their payloads.
Checked body projection, assembly and contextual execution compose through the
retained source calls to the actual GSLT of the assembled language.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.ModuleAssemblyExecution

open Mettapedia.GSLT.LanguageDef
open MeTTaILFirstOrderRuleCompilation (PatternPlan)
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst matchAtom)
open Effects (State)
open Eval CettaWire
open scoped ProgramQuotation

private abbrev a (head : String) (arguments : List Atom) : Atom :=
  .expression (.symbol head :: arguments)
private abbrev v (name : String) : Atom := .var name
private abbrev encoded (term : Term) : Atom := CettaWireAtom.encode term
private abbrev rowValue {α : Type} (encode : α → Term) (rows : List α) : Atom :=
  encoded (encodeList encode rows)

def source : ProgramQuotation.QuotedProgram :=
  petta_source_file%
    "../../../../../../../../../hyperon/cetta-mm0-metta-20261004/lib/gslt_module.metta"
    sha256 "19c1ccfee0b2fe53809c61c1e6e0a89f6ec2ce89e9bced74dfc0d3ef95f509ee"

def program : SpaceSemantics.Program := RuleExecutionProgram.program.append source.program

private def existingHead (head : String) : Bool :=
  head != "eval" && !(head.startsWith "gslt:module:")

private theorem existing_closed : ProgramClosed existingHead RuleExecutionProgram.program := by
  constructor
  · decide +kernel
  · have within : RuleExecutionProgram.program.equations.all (fun equation =>
        !existingHead equation.head || codeWithin existingHead equation.body) = true := by
      decide +kernel
    intro equation member supported
    have checked := List.all_eq_true.mp within equation member
    simpa only [supported, Bool.not_true, Bool.false_or] using checked

private theorem existing_agreement :
    ProgramAgreementOn existingHead RuleExecutionProgram.program program := by
  apply appended_program_agreement
  · intro equation member
    have fresh : source.program.equations.all (fun equation => !existingHead equation.head) = true := by
      decide +kernel
    have checked := List.all_eq_true.mp fresh equation member
    cases result : existingHead equation.head with
    | false => rfl
    | true => simp [result] at checked
  · intro name types member
    have fresh : source.program.declarations.all (fun declaration => match declaration with
        | .expression [.symbol ":", .symbol head, .expression (.symbol "->" :: _)] =>
            !existingHead head
        | _ => true) = true := by
      decide +kernel
    have checked := List.all_eq_true.mp fresh
      (.expression [.symbol ":", .symbol name, .expression (.symbol "->" :: types)]) member
    cases result : existingHead name with
    | false => rfl
    | true => simp [result] at checked

/-- Loading the assembler preserves supported existing rule and matcher runs.
Captured payloads remain data and are not inspected for function names. -/
theorem existing_captured_returns {caller : Subst} {before after : State} {code answer : Atom}
    (supported : codeWithin existingHead code = true)
    (checked : PureReturns RuleExecutionProgram.program caller before code after answer) :
    PureReturns program caller before code after answer :=
  path_of_closed_agreement existing_closed existing_agreement ⟨supported, rfl⟩ checked

theorem no_initializers : source.program.initializers = [] := by decide +kernel

/-- Encode every family of actual source declarations, with explicit row
encoders. Assembly is independent of their syntax and operational admission. -/
def languageTerm (types : TypeDecl → Term) (terms : GrammarRule → Term)
    (equations : Equation → Term) (rewrites : RewriteRule → Term) (language : LanguageDef) : Term :=
  .application "GSLTLanguageDefWireV1" [.string language.name,
    encodeList types language.types, encodeList terms language.terms,
    encodeList equations language.equations, encodeList rewrites language.rewrites]

private def equation : SpaceSemantics.Equation := source.program.equations[0]'(by decide +kernel)
private def environment (name : String) (fragments : Atom) : Subst :=
  [("fragments", fragments), ("name", encoded (.string name))]

private theorem assemble_clause (name : String) (fragments : Atom) :
    clauses program "gslt:module:assemble" [encoded (.string name), fragments] =
      [.evaluate (environment name fragments) equation.body] := by
  rw [clauses_use_only_the_named_equations]
  change (program.equations.filter (fun row => row.head == "gslt:module:assemble")).filterMap _ = _
  rw [show program.equations.filter (fun row => row.head == "gslt:module:assemble") = [equation] from rfl]
  have formals : equation.arguments = [v "name", v "fragments"] := by decide +kernel
  simp [formals, environment, SpaceSemantics.matchValue,
    SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]

private theorem assemble_call (caller : Subst) (state : State) (name : String)
    (fragments first second answer : Atom)
    (captured : [first, second].map (applySubst caller) = [encoded (.string name), fragments])
    (returned : PureReturns program (environment name fragments) state equation.body state answer) :
    PureReturns program caller state (a "gslt:module:assemble" [first, second]) state answer := by
  apply PureData.raw_authored_call_return program caller (environment name fragments) state state
    "gslt:module:assemble" [first, second] equation.body answer
    (by decide) (by decide) (by decide) (by decide +kernel) _ _ returned
  · intro index bounded
    have positions : index = 0 ∨ index = 1 := by
      simp only [List.length_cons, List.length_nil] at bounded
      omega
    rcases positions with rfl | rfl <;> decide +kernel
  · rw [captured]
    exact assemble_clause name fragments

private theorem append_captured_returns (caller : Subst) (state : State) (left right : List Term)
    (first second : String)
    (captured : [v first, v second].map (applySubst caller) =
      [encoded (encodeList id left), encoded (encodeList id right)]) :
    PureReturns program caller state (a "gslt:automata:append" [v first, v second]) state
      (encoded (encodeList id (left ++ right))) :=
  existing_captured_returns (by simp [codeWithin, expressionHeadWithin, atomsWithin, existingHead])
    (RuleExecutionProgram.automata_captured_returns
      (by simp [codeWithin, expressionHeadWithin, atomsWithin, RuleExecutionProgram.matcherHead])
      (MatchAutomataSourceExecution.append_captured_returns caller state left right (v first) (v second) captured))

private def outputBody : Atom :=
  a "Some" [a "GSLTLanguageDefWireV1"
    [v "name", v "all-types", v "all-terms", v "all-equations", v "all-rewrites"]]
private def mergePairs : List Atom :=
  [.expression [v "all-types", a "gslt:automata:append" [v "types", v "tail-types"]],
   .expression [v "all-terms", a "gslt:automata:append" [v "terms", v "tail-terms"]],
   .expression [v "all-equations", a "gslt:automata:append" [v "equations", v "tail-equations"]],
   .expression [v "all-rewrites", a "gslt:automata:append" [v "rewrites", v "tail-rewrites"]]]
private def mergeBody : Atom := a "let*" [.expression mergePairs, outputBody]
private def resultCases : SpaceSemantics.Cases :=
  [(a "Some" [a "GSLTLanguageDefWireV1"
      [v "assembled", v "tail-types", v "tail-terms", v "tail-equations", v "tail-rewrites"]], mergeBody),
   (v "bad", .symbol "None")]
private def recursiveBody : Atom :=
  a "case" [a "gslt:module:assemble" [v "name", v "rest"],
    .expression (resultCases.map fun row => .expression [row.1, row.2])]
private def fragmentCases : SpaceSemantics.Cases :=
  [(.symbol "LNil", a "Some" [a "GSLTLanguageDefWireV1"
      [v "name", .symbol "LNil", .symbol "LNil", .symbol "LNil", .symbol "LNil"]]),
   (a "LCons" [a "GSLTLanguageDefWireV1"
      [v "local", v "types", v "terms", v "equations", v "rewrites"], v "rest"], recursiveBody),
   (v "bad", .symbol "None")]

private theorem body_shape : equation.body =
    a "case" [v "fragments", .expression (fragmentCases.map fun row => .expression [row.1, row.2])] := by
  decide +kernel

private theorem some_wire_template (fields : List Atom)
    (templates : ∀ field ∈ fields, PureData.Template program field) :
    PureData.Template program (a "Some" [a "GSLTLanguageDefWireV1" fields]) := by
  apply PureData.Template.constructor "Some" _ (by decide +kernel) (by decide)
  intro field member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  subst field
  exact PureData.Template.constructor "GSLTLanguageDefWireV1" fields
    (by decide +kernel) (by decide) templates

private theorem output_template : PureData.Template program outputBody := by
  apply some_wire_template
  intro field member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl <;> exact .captured _

private theorem merge_body_returns (caller : Subst) (state : State) (name : String)
    (types tailTypes terms tailTerms equationRows tailEquations rewrites tailRewrites : List Term)
    (captured :
      [v "name", v "types", v "tail-types", v "terms", v "tail-terms",
        v "equations", v "tail-equations", v "rewrites", v "tail-rewrites"].map (applySubst caller) =
      [encoded (.string name), rowValue id types, rowValue id tailTypes,
        rowValue id terms, rowValue id tailTerms, rowValue id equationRows, rowValue id tailEquations,
        rowValue id rewrites, rowValue id tailRewrites])
    (fresh : ∀ name ∈ ["all-types", "all-terms", "all-equations", "all-rewrites"],
      Subst.lookup caller name = none) :
    PureReturns program caller state mergeBody state
      (a "Some" [a "GSLTLanguageDefWireV1" [encoded (.string name),
        rowValue id (types ++ tailTypes), rowValue id (terms ++ tailTerms),
        rowValue id (equationRows ++ tailEquations), rowValue id (rewrites ++ tailRewrites)]]) := by
  let first := ("all-types", rowValue id (types ++ tailTypes)) :: caller
  let second := ("all-terms", rowValue id (terms ++ tailTerms)) :: first
  let third := ("all-equations", rowValue id (equationRows ++ tailEquations)) :: second
  let fourth := ("all-rewrites", rowValue id (rewrites ++ tailRewrites)) :: third
  have values := List.cons.inj captured
  have names := values.1
  have rows := List.cons.inj values.2
  have heads := List.cons.inj rows.2
  have constructors := List.cons.inj heads.2
  have constructorTails := List.cons.inj constructors.2
  have equalities := List.cons.inj constructorTails.2
  have equalityTails := List.cons.inj equalities.2
  have reductions := List.cons.inj equalityTails.2
  have reductionTails := List.cons.inj reductions.2
  simp only [applySubst, Subst.lookup] at names rows heads constructors constructorTails equalities equalityTails reductions reductionTails
  have freshTypes := fresh "all-types" (by simp)
  have freshTerms := fresh "all-terms" (by simp)
  have freshEquations := fresh "all-equations" (by simp)
  have freshRewrites := fresh "all-rewrites" (by simp)
  simp only [Subst.lookup] at freshTypes freshTerms freshEquations freshRewrites
  apply let_star_returns program caller state state mergePairs outputBody
    (a "let" [v "all-types", a "gslt:automata:append" [v "types", v "tail-types"],
      a "let" [v "all-terms", a "gslt:automata:append" [v "terms", v "tail-terms"],
        a "let" [v "all-equations", a "gslt:automata:append" [v "equations", v "tail-equations"],
          a "let" [v "all-rewrites", a "gslt:automata:append" [v "rewrites", v "tail-rewrites"], outputBody]]]])
    _ rfl
  apply let_returns program caller first state state state _ _ _ _ _
    (append_captured_returns caller state types tailTypes "types" "tail-types"
      (by simp [applySubst, Subst.lookup, rows.1, heads.1]))
    (by simp [SpaceSemantics.matchValue, matchAtom, Subst.lookup, first, freshTypes])
  apply let_returns program first second state state state _ _ _ _ _
    (append_captured_returns first state terms tailTerms "terms" "tail-terms"
      (by simp [first, applySubst, Subst.lookup, constructors.1, constructorTails.1]))
    (by simp [SpaceSemantics.matchValue, matchAtom, Subst.lookup, second, first, freshTerms])
  apply let_returns program second third state state state _ _ _ _ _
    (append_captured_returns second state equationRows tailEquations "equations" "tail-equations"
      (by simp [second, first, applySubst, Subst.lookup, equalities.1, equalityTails.1]))
    (by simp [SpaceSemantics.matchValue, matchAtom, Subst.lookup, third, second, first, freshEquations])
  apply let_returns program third fourth state state state _ _ _ _ _
    (append_captured_returns third state rewrites tailRewrites "rewrites" "tail-rewrites"
      (by simp [third, second, first, applySubst, Subst.lookup, reductions.1, reductionTails.1]))
    (by simp [SpaceSemantics.matchValue, matchAtom, Subst.lookup, fourth, third, second, first, freshRewrites])
  simpa [fourth, third, second, first, outputBody, applySubst, applySubst.applySubstList,
    Subst.lookup, names] using PureData.template_return program fourth state _ output_template

private theorem assemble_body_returns (state : State) (name : String)
    (types : TypeDecl → Term) (terms : GrammarRule → Term)
    (equationRows : Equation → Term) (rewrites : RewriteRule → Term) :
    ∀ fragments : List LanguageDef,
      PureReturns program (environment name (rowValue (languageTerm types terms equationRows rewrites) fragments))
        state equation.body state
        (a "Some" [encoded (languageTerm types terms equationRows rewrites
          (ModuleAlgebra.NativeAuthoring.assembleRaw name fragments))]) := by
  intro fragments
  induction fragments with
  | nil =>
      let caller := environment name (.symbol "LNil")
      rw [body_shape]
      apply case_returns program caller caller state state state (v "fragments") (.symbol "LNil")
        (a "Some" [a "GSLTLanguageDefWireV1"
          [v "name", .symbol "LNil", .symbol "LNil", .symbol "LNil", .symbol "LNil"]])
        _ _ fragmentCases (read_cases_encoded _) _ _ _
      · simpa [caller, environment, applySubst, Subst.lookup] using variable_returns program caller state "fragments"
      · simp [fragmentCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
      · simpa [languageTerm, ModuleAlgebra.NativeAuthoring.assembleRaw_rows,
          encodeList, CettaWireAtom.encode, CettaWireAtom.encodeMany, applySubst,
          applySubst.applySubstList, Subst.lookup, caller, environment] using
          PureData.template_return program caller state _
            (some_wire_template [v "name", .symbol "LNil", .symbol "LNil", .symbol "LNil", .symbol "LNil"]
              (by
                intro field member
                simp only [List.mem_cons, List.not_mem_nil, or_false] at member
                rcases member with rfl | rfl | rfl | rfl | rfl
                · exact .captured _
                all_goals exact PureData.Template.symbol "LNil"))
  | cons fragment rest ih =>
      let restValue := rowValue (languageTerm types terms equationRows rewrites) rest
      let caller := environment name (rowValue (languageTerm types terms equationRows rewrites) (fragment :: rest))
      let selected := [("rest", restValue), ("rewrites", rowValue rewrites fragment.rewrites),
        ("equations", rowValue equationRows fragment.equations), ("terms", rowValue terms fragment.terms),
        ("types", rowValue types fragment.types), ("local", encoded (.string fragment.name))] ++ caller
      let tail := ModuleAlgebra.NativeAuthoring.assembleRaw name rest
      let below := [("tail-rewrites", rowValue rewrites tail.rewrites),
        ("tail-equations", rowValue equationRows tail.equations), ("tail-terms", rowValue terms tail.terms),
        ("tail-types", rowValue types tail.types), ("assembled", encoded (.string name))] ++ selected
      rw [body_shape]
      apply case_returns program caller selected state state state (v "fragments")
        (rowValue (languageTerm types terms equationRows rewrites) (fragment :: rest)) recursiveBody
        _ _ fragmentCases (read_cases_encoded _) _ _ _
      · simpa [caller, environment, applySubst, Subst.lookup] using variable_returns program caller state "fragments"
      · simp [fragmentCases, selected, caller, environment, restValue, languageTerm, rowValue, encodeList,
          encoded, CettaWireAtom.encode, CettaWireAtom.encodeMany, SpaceSemantics.selectCase,
          SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]
      · apply case_returns program selected below state state state
          (a "gslt:module:assemble" [v "name", v "rest"])
          (a "Some" [encoded (languageTerm types terms equationRows rewrites tail)]) mergeBody
          _ _ resultCases (read_cases_encoded _) _ _ _
        · exact assemble_call selected state name restValue _ _ _
            (by simp [selected, caller, environment, restValue, applySubst, Subst.lookup]) ih
        · simp [resultCases, below, tail, selected, caller, environment, languageTerm,
            ModuleAlgebra.NativeAuthoring.assembleRaw_rows,
            encoded, CettaWireAtom.encode, CettaWireAtom.encodeMany, SpaceSemantics.selectCase,
            SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]
        · simpa [languageTerm, ModuleAlgebra.NativeAuthoring.assembleRaw_rows, tail, ← List.map_append,
            rowValue, encoded, CettaWireAtom.encode, CettaWireAtom.encodeMany, encodeList_map, Function.comp_def]
            using merge_body_returns below state name
              (fragment.types.map types) (tail.types.map types)
              (fragment.terms.map terms) (tail.terms.map terms)
              (fragment.equations.map equationRows) (tail.equations.map equationRows)
              (fragment.rewrites.map rewrites) (tail.rewrites.map rewrites)
              (by simp [below, selected, caller, environment, tail, languageTerm, encodeList_map,
                applySubst, Subst.lookup])
              (by
                intro key member
                simp only [List.mem_cons, List.not_mem_nil, or_false] at member
                rcases member with rfl | rfl | rfl | rfl <;>
                  simp [below, selected, caller, environment, Subst.lookup])

/-- The actual source assembles every row of every supplied fragment in order.
Its result is the existing complete-row module operation, with no validation
or contextual permission inferred from assembling the data. -/
theorem assemble_returns (state : State) (name : String)
    (types : TypeDecl → Term) (terms : GrammarRule → Term)
    (equationRows : Equation → Term) (rewrites : RewriteRule → Term)
    (fragments : List LanguageDef) :
    PureReturns program [] state
      (a "gslt:module:assemble" [encoded (.string name),
        rowValue (languageTerm types terms equationRows rewrites) fragments]) state
      (a "Some" [encoded (languageTerm types terms equationRows rewrites
        (ModuleAlgebra.NativeAuthoring.assembleRaw name fragments))]) :=
  assemble_call [] state name _ _ _ _ (by simp [CettaWireAtom.applySubst_encode])
    (assemble_body_returns state name types terms equationRows rewrites fragments)

theorem assemble_captured_returns (caller : Subst) (state : State) (name : String)
    (types : TypeDecl → Term) (terms : GrammarRule → Term)
    (equationRows : Equation → Term) (rewrites : RewriteRule → Term)
    (fragments : List LanguageDef) (first second : Atom)
    (captured : [first, second].map (applySubst caller) =
      [encoded (.string name), rowValue (languageTerm types terms equationRows rewrites) fragments]) :
    PureReturns program caller state (a "gslt:module:assemble" [first, second]) state
      (a "Some" [encoded (languageTerm types terms equationRows rewrites
        (ModuleAlgebra.NativeAuthoring.assembleRaw name fragments))]) :=
  assemble_call caller state name _ _ _ _ captured
    (assemble_body_returns state name types terms equationRows rewrites fragments)

theorem assemble_completed_iff (state : State) (name : String)
    (types : TypeDecl → Term) (terms : GrammarRule → Term)
    (equationRows : Equation → Term) (rewrites : RewriteRule → Term)
    (fragments : List LanguageDef) (after : State) (answers input output : List Atom) :
    (∃ fuel, Eval.run program fuel
      { state, control := .evaluate [] (a "gslt:module:assemble" [encoded (.string name),
          rowValue (languageTerm types terms equationRows rewrites) fragments]) } =
      .complete after answers input output) ↔
      after = state ∧
      answers = [a "Some" [encoded (languageTerm types terms equationRows rewrites
        (ModuleAlgebra.NativeAuthoring.assembleRaw name fragments))]] ∧ input = [] ∧ output = [] :=
  pure_returns_completed_iff program [] state state _ _
    (assemble_returns state name types terms equationRows rewrites fragments) after answers input output

theorem assemble_derivation_iff (state : State) (name : String)
    (types : TypeDecl → Term) (terms : GrammarRule → Term)
    (equationRows : Equation → Term) (rewrites : RewriteRule → Term)
    (fragments : List LanguageDef) (after : State) (answers input output : List Atom) :
    DeclarativeSpec.Runs program
      { state, control := .evaluate [] (a "gslt:module:assemble" [encoded (.string name),
          rowValue (languageTerm types terms equationRows rewrites) fragments]) }
      (.complete after answers input output) ↔
      after = state ∧
      answers = [a "Some" [encoded (languageTerm types terms equationRows rewrites
        (ModuleAlgebra.NativeAuthoring.assembleRaw name fragments))]] ∧ input = [] ∧ output = [] :=
  pure_returns_derivation_iff program [] state state _ _
    (assemble_returns state name types terms equationRows rewrites fragments) after answers input output

/-- A fragment outside the declared wire cannot manufacture a language. -/
theorem unsupported_fragment_returns_none (state : State) (name : String) :
    PureReturns program [] state (a "gslt:module:assemble"
      [encoded (.string name), rowValue id [.symbol "BrokenFragment"]]) state (.symbol "None") := by
  let fragments := rowValue id [.symbol "BrokenFragment"]
  let caller := environment name fragments
  let selected := ("bad", fragments) :: caller
  apply assemble_call [] state name fragments _ _ _ (by
    change [applySubst [] (encoded (.string name)), applySubst [] fragments] =
      [encoded (.string name), fragments]
    unfold fragments
    simp only [CettaWireAtom.applySubst_encode])
  rw [body_shape]
  apply case_returns program caller selected state state state (v "fragments") fragments
    (.symbol "None") (.symbol "None") _ fragmentCases (read_cases_encoded _) _ _ _
  · simpa [caller, environment, applySubst, Subst.lookup] using variable_returns program caller state "fragments"
  · simp [fragmentCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
      SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup, fragments, encodeList,
      encoded, CettaWireAtom.encode, selected, caller, environment]
  · exact symbol_returns program selected state "None"

/-- The assembly wire retains the exact rewrite rows consumed by contextual
execution. Equation-free admission is required only at that execution entry. -/
theorem languageTerm_rewriteProjection (types : TypeDecl → Term) (terms : GrammarRule → Term)
    (equations : Equation → Term) (contexts fields : RewriteRule → Term)
    (language : LanguageDef) (equationFree : language.equations = []) :
    languageTerm types terms equations (MatchAutomataExecution.rewriteRowTerm contexts fields) language =
      MatchAutomataExecution.matchingProjectionTerm language
        (encodeList types language.types) (encodeList terms language.terms) (.symbol "LNil") contexts fields := by
  simp only [languageTerm, MatchAutomataExecution.matchingProjectionTerm,
    MatchAutomataExecution.rewriteRowsTerm, equationFree, encodeList]

private def reductEquation : SpaceSemantics.Equation :=
  source.program.equations[1]'(by decide +kernel)
private def reductEnvironment (name : String) (fragments : Atom)
    (strategy : MeTTaILMatchAutomataExecution.Strategy)
    (rows : List Mettapedia.OSLF.MeTTaIL.GeneralPremise.ProviderRow) (depth : Nat)
    (subject : PatternPlan) : Subst :=
  [("subject", encoded (InferenceCettaWire.encodePattern subject.erase)),
   ("depth", encoded (.natural depth)), ("rows", encoded (RelationPremiseExecution.providerRowsTerm rows)),
   ("strategy", encoded (ContextualRuleExecution.strategyTerm strategy)),
   ("fragments", fragments), ("name", encoded (.string name))]
private def reductBody : Atom :=
  a "gslt:rule:language-contextual-reducts" [v "strategy", v "assembled", v "rows", v "depth", v "subject"]
private def reductCases : SpaceSemantics.Cases :=
  [(a "Some" [v "assembled"], reductBody), (v "bad", .symbol "None")]

/-- Module generation and execution compose through the actual source calls.
Recursive premises consult the assembled language, rather than a union of
frontiers computed independently in each fragment. -/
theorem reducts_captured_returns (caller : Subst) (state : State) (name : String)
    (types : TypeDecl → Term) (terms : GrammarRule → Term) (equations : Equation → Term)
    (contexts fields : RewriteRule → Term) (fragments : List LanguageDef)
    (strategy : MeTTaILMatchAutomataExecution.Strategy)
    (rows : List Mettapedia.OSLF.MeTTaIL.GeneralPremise.ProviderRow)
    (providerAdmitted : RuleTraceExecution.providerFirstOrder rows = true)
    (admitted : ContextualRuleExecution.languageAdmitted
      (ModuleAlgebra.NativeAuthoring.assembleRaw name fragments) = true)
    (projected : ∀ rule ∈ (ModuleAlgebra.NativeAuthoring.assembleRaw name fragments).rewrites,
      ContextualRuleExecution.premisesTerm? rule.premises = some (fields rule))
    (depth : Nat) (subject : PatternPlan) (arguments : List Atom)
    (captured : arguments.map (applySubst caller) =
      [encoded (.string name),
       rowValue (languageTerm types terms equations (MatchAutomataExecution.rewriteRowTerm contexts fields)) fragments,
       encoded (ContextualRuleExecution.strategyTerm strategy), encoded (RelationPremiseExecution.providerRowsTerm rows),
       encoded (.natural depth), encoded (InferenceCettaWire.encodePattern subject.erase)]) :
    PureReturns program caller state (a "gslt:module:reducts" arguments) state
      (encoded (InferenceCettaWire.encodePatterns (MeTTaILMatchAutomataExecution.runAt strategy
        (Mettapedia.OSLF.MeTTaIL.ContextualStep.engineBasePremises (RelationPremiseExecution.providerEnv rows))
        (ModuleAlgebra.NativeAuthoring.assembleRaw name fragments) depth subject))) := by
  let language := ModuleAlgebra.NativeAuthoring.assembleRaw name fragments
  let fragmentValue := rowValue
    (languageTerm types terms equations (MatchAutomataExecution.rewriteRowTerm contexts fields)) fragments
  let callee := reductEnvironment name fragmentValue strategy rows depth subject
  let assembled := encoded (languageTerm types terms equations
    (MatchAutomataExecution.rewriteRowTerm contexts fields) language)
  let selected := ("assembled", assembled) :: callee
  have equationFree : language.equations = [] := by
    have empty := (ContextualRuleExecution.language_admitted_iff language).mp admitted |>.1
    simp only [LanguageDef.isEquationFree, Bool.and_eq_true, List.isEmpty_iff] at empty
    exact empty.1.1.1
  have sameWire := languageTerm_rewriteProjection types terms equations contexts fields language equationFree
  have contextual := existing_captured_returns
    (by simp [codeWithin, expressionHeadWithin, atomsWithin, existingHead])
    (ContextualRuleExecution.language_contextual_captured_returns selected state strategy language
      (encodeList types language.types) (encodeList terms language.terms) contexts fields rows
      providerAdmitted admitted projected depth subject
      [v "strategy", v "assembled", v "rows", v "depth", v "subject"]
      (by simp [selected, callee, reductEnvironment, assembled, sameWire, applySubst, Subst.lookup]))
  apply PureData.raw_authored_call_return program caller callee state state
    "gslt:module:reducts" arguments reductEquation.body _
    (by decide) (by decide) (by decide) (by decide +kernel) _ _ _
  · have length : arguments.length = 6 := by
      have := congrArg List.length captured
      simpa using this
    intro index bounded
    rw [length] at bounded
    interval_cases index <;> decide +kernel
  · rw [captured, clauses_use_only_the_named_equations]
    change (program.equations.filter (fun row => row.head == "gslt:module:reducts")).filterMap _ = _
    rw [show program.equations.filter (fun row => row.head == "gslt:module:reducts") = [reductEquation] from rfl]
    have formals : reductEquation.arguments =
        [v "name", v "fragments", v "strategy", v "rows", v "depth", v "subject"] := by decide +kernel
    simp [formals, callee, reductEnvironment, fragmentValue, SpaceSemantics.matchValue,
      SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]
  · have shape : reductEquation.body = a "case"
        [a "gslt:module:assemble" [v "name", v "fragments"],
         .expression (reductCases.map fun row => .expression [row.1, row.2])] := by decide +kernel
    rw [shape]
    apply case_returns program callee selected state state state
      (a "gslt:module:assemble" [v "name", v "fragments"])
      (a "Some" [assembled]) reductBody _ _ reductCases (read_cases_encoded _) _ _ contextual
    · exact assemble_captured_returns callee state name types terms equations
        (MatchAutomataExecution.rewriteRowTerm contexts fields) fragments (v "name") (v "fragments")
        (by simp [callee, reductEnvironment, fragmentValue, applySubst, Subst.lookup])
    · simp [reductCases, selected, callee, reductEnvironment, SpaceSemantics.selectCase,
        SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]

def reductsQueryTerm (name : String) (types : TypeDecl → Term) (terms : GrammarRule → Term)
    (equations : Equation → Term) (contexts fields : RewriteRule → Term)
    (fragments : List LanguageDef) (strategy : MeTTaILMatchAutomataExecution.Strategy)
    (rows : List Mettapedia.OSLF.MeTTaIL.GeneralPremise.ProviderRow) (depth : Nat)
    (subject : PatternPlan) : Term :=
  .application "gslt:module:reducts" [.string name,
    encodeList (languageTerm types terms equations (MatchAutomataExecution.rewriteRowTerm contexts fields)) fragments,
    ContextualRuleExecution.strategyTerm strategy, RelationPremiseExecution.providerRowsTerm rows,
    .natural depth, InferenceCettaWire.encodePattern subject.erase]

theorem reducts_returns (state : State) (name : String)
    (types : TypeDecl → Term) (terms : GrammarRule → Term) (equations : Equation → Term)
    (contexts fields : RewriteRule → Term) (fragments : List LanguageDef)
    (strategy : MeTTaILMatchAutomataExecution.Strategy)
    (rows : List Mettapedia.OSLF.MeTTaIL.GeneralPremise.ProviderRow)
    (providerAdmitted : RuleTraceExecution.providerFirstOrder rows = true)
    (admitted : ContextualRuleExecution.languageAdmitted
      (ModuleAlgebra.NativeAuthoring.assembleRaw name fragments) = true)
    (projected : ∀ rule ∈ (ModuleAlgebra.NativeAuthoring.assembleRaw name fragments).rewrites,
      ContextualRuleExecution.premisesTerm? rule.premises = some (fields rule))
    (depth : Nat) (subject : PatternPlan) :
    PureReturns program [] state
      (encoded (reductsQueryTerm name types terms equations contexts fields fragments strategy rows depth subject)) state
      (encoded (InferenceCettaWire.encodePatterns (MeTTaILMatchAutomataExecution.runAt strategy
        (Mettapedia.OSLF.MeTTaIL.ContextualStep.engineBasePremises (RelationPremiseExecution.providerEnv rows))
        (ModuleAlgebra.NativeAuthoring.assembleRaw name fragments) depth subject))) := by
  simpa only [reductsQueryTerm, CettaWireAtom.encode, CettaWireAtom.encodeMany] using
    reducts_captured_returns [] state name types terms equations contexts fields fragments strategy rows
      providerAdmitted admitted projected depth subject _ (by simp [applySubst, CettaWireAtom.encode])

theorem reducts_completed_iff (state : State) (name : String)
    (types : TypeDecl → Term) (terms : GrammarRule → Term) (equations : Equation → Term)
    (contexts fields : RewriteRule → Term) (fragments : List LanguageDef)
    (strategy : MeTTaILMatchAutomataExecution.Strategy)
    (rows : List Mettapedia.OSLF.MeTTaIL.GeneralPremise.ProviderRow)
    (providerAdmitted : RuleTraceExecution.providerFirstOrder rows = true)
    (admitted : ContextualRuleExecution.languageAdmitted
      (ModuleAlgebra.NativeAuthoring.assembleRaw name fragments) = true)
    (projected : ∀ rule ∈ (ModuleAlgebra.NativeAuthoring.assembleRaw name fragments).rewrites,
      ContextualRuleExecution.premisesTerm? rule.premises = some (fields rule))
    (depth : Nat) (subject : PatternPlan) (after : State) (answers input output : List Atom) :
    (∃ fuel, Eval.run program fuel
      { state, control := .evaluate []
          (encoded (reductsQueryTerm name types terms equations contexts fields fragments strategy rows depth subject)) } =
      .complete after answers input output) ↔
    after = state ∧ answers = [encoded (InferenceCettaWire.encodePatterns
      (MeTTaILMatchAutomataExecution.runAt strategy
        (Mettapedia.OSLF.MeTTaIL.ContextualStep.engineBasePremises (RelationPremiseExecution.providerEnv rows))
        (ModuleAlgebra.NativeAuthoring.assembleRaw name fragments) depth subject))] ∧ input = [] ∧ output = [] :=
  pure_returns_completed_iff program [] state state _ _
    (reducts_returns state name types terms equations contexts fields fragments strategy rows
      providerAdmitted admitted projected depth subject) after answers input output

theorem reducts_derivation_iff (state : State) (name : String)
    (types : TypeDecl → Term) (terms : GrammarRule → Term) (equations : Equation → Term)
    (contexts fields : RewriteRule → Term) (fragments : List LanguageDef)
    (strategy : MeTTaILMatchAutomataExecution.Strategy)
    (rows : List Mettapedia.OSLF.MeTTaIL.GeneralPremise.ProviderRow)
    (providerAdmitted : RuleTraceExecution.providerFirstOrder rows = true)
    (admitted : ContextualRuleExecution.languageAdmitted
      (ModuleAlgebra.NativeAuthoring.assembleRaw name fragments) = true)
    (projected : ∀ rule ∈ (ModuleAlgebra.NativeAuthoring.assembleRaw name fragments).rewrites,
      ContextualRuleExecution.premisesTerm? rule.premises = some (fields rule))
    (depth : Nat) (subject : PatternPlan) (after : State) (answers input output : List Atom) :
    DeclarativeSpec.Runs program
      { state, control := .evaluate []
          (encoded (reductsQueryTerm name types terms equations contexts fields fragments strategy rows depth subject)) }
      (.complete after answers input output) ↔
    after = state ∧ answers = [encoded (InferenceCettaWire.encodePatterns
      (MeTTaILMatchAutomataExecution.runAt strategy
        (Mettapedia.OSLF.MeTTaIL.ContextualStep.engineBasePremises (RelationPremiseExecution.providerEnv rows))
        (ModuleAlgebra.NativeAuthoring.assembleRaw name fragments) depth subject))] ∧ input = [] ∧ output = [] :=
  pure_returns_derivation_iff program [] state state _ _
    (reducts_returns state name types terms equations contexts fields fragments strategy rows
      providerAdmitted admitted projected depth subject) after answers input output

/-- A reduct belongs to the frontier of an actually completed assembled run. -/
def ObservesReduct (state : State) (name : String)
    (types : TypeDecl → Term) (terms : GrammarRule → Term) (equations : Equation → Term)
    (contexts fields : RewriteRule → Term) (fragments : List LanguageDef)
    (strategy : MeTTaILMatchAutomataExecution.Strategy)
    (rows : List Mettapedia.OSLF.MeTTaIL.GeneralPremise.ProviderRow)
    (subject : PatternPlan) (target : Pattern) : Prop :=
  ∃ depth, ∃ reducts : List Pattern,
    DeclarativeSpec.Runs program
      { state, control := .evaluate []
          (encoded (reductsQueryTerm name types terms equations contexts fields fragments strategy rows depth subject)) }
      (.complete state [encoded (InferenceCettaWire.encodePatterns reducts)] [] []) ∧ target ∈ reducts

/-- Preservation and reflection between assembled MeTTa executions and the
actual GSLT of the assembled language, under its explicit source profile. -/
theorem observes_reduct_iff_gslt_step (state : State) (name : String)
    (types : TypeDecl → Term) (terms : GrammarRule → Term) (equations : Equation → Term)
    (contexts fields : RewriteRule → Term) (fragments : List LanguageDef)
    (strategy : MeTTaILMatchAutomataExecution.Strategy)
    (rows : List Mettapedia.OSLF.MeTTaIL.GeneralPremise.ProviderRow)
    (providerAdmitted : RuleTraceExecution.providerFirstOrder rows = true)
    (admitted : ContextualRuleExecution.languageAdmitted
      (ModuleAlgebra.NativeAuthoring.assembleRaw name fragments) = true)
    (projected : ∀ rule ∈ (ModuleAlgebra.NativeAuthoring.assembleRaw name fragments).rewrites,
      ContextualRuleExecution.premisesTerm? rule.premises = some (fields rule))
    (subject : PatternPlan) (target : Pattern) :
    ObservesReduct state name types terms equations contexts fields fragments strategy rows subject target ↔
      (Mettapedia.OSLF.Framework.TypeSynthesis.langGSLTUsing (RelationPremiseExecution.providerEnv rows)
        (ModuleAlgebra.NativeAuthoring.assembleRaw name fragments)).Step subject.erase target := by
  rw [← MeTTaILMatchAutomataExecution.runAt_iff_gslt_step strategy (RelationPremiseExecution.providerEnv rows)
    (ModuleAlgebra.NativeAuthoring.assembleRaw name fragments)
    ((ContextualRuleExecution.language_admitted_iff _).mp admitted).1 subject target]
  constructor
  · rintro ⟨depth, reducts, executed, member⟩
    have result := (reducts_derivation_iff state name types terms equations contexts fields fragments strategy rows
      providerAdmitted admitted projected depth subject state _ [] []).mp executed
    have sameEncoded := List.cons.inj result.2.1 |>.1
    have same := InferenceCettaWire.encodePatterns_injective
      (CettaWireAtom.encode_injective _ _ sameEncoded)
    exact ⟨depth, by simpa only [same] using member⟩
  · rintro ⟨depth, member⟩
    exact ⟨depth, _, (reducts_derivation_iff state name types terms equations contexts fields fragments strategy rows
      providerAdmitted admitted projected depth subject state _ [] []).mpr ⟨rfl, rfl, rfl, rfl⟩, member⟩

namespace Imports

open ModuleAlgebra
open ModuleAlgebra.NativeAuthoring

private abbrev WireEntry := Entry Term Term Term
private abbrev entryValue (entry : WireEntry) : Atom := encoded (importEntryTerm entry)
private abbrev entriesValue (entries : List WireEntry) : Atom := rowValue importEntryTerm entries
private abbrev modeValue (contract : ImportContract) : Atom := encoded contract.wireTerm

def resultTerm : Option (List WireEntry) → Term
  | none => .symbol "None"
  | some entries => .application "Some" [encodeList importEntryTerm entries]

theorem resultTerm_injective : Function.Injective resultTerm := by
  intro first second same
  cases first with
  | none => cases second <;> simp_all [resultTerm]
  | some left =>
      cases second with
      | none => simp [resultTerm] at same
      | some right =>
          have fields := (Term.application.inj same).2
          have lists := (List.cons.inj fields).1
          exact congrArg some (encodeList_injective importEntryTerm importEntryTerm_injective lists)

private inductive TripleHelper where | compatible | insert | fold | join

private def TripleHelper.head : TripleHelper → String
  | .compatible => "gslt:module:compatible"
  | .insert => "gslt:module:insert"
  | .fold => "gslt:module:fold"
  | .join => "gslt:module:join"

private def TripleHelper.formals : TripleHelper → String × String
  | .compatible => ("left", "right")
  | .insert => ("entry", "kept")
  | .fold => ("kept", "incoming")
  | .join => ("left", "right")

private def namedEquations (head : String) : List SpaceSemantics.Equation :=
  program.equations.filter (fun equation => equation.head == head)

private def tripleEquation (helper : TripleHelper) : SpaceSemantics.Equation :=
  (namedEquations helper.head)[0]'(by cases helper <;> decide +kernel)

private def tripleEnvironment (helper : TripleHelper) (mode left right : Atom) : Subst :=
  [(helper.formals.2, right), (helper.formals.1, left), ("mode", mode)]

private theorem triple_clause (helper : TripleHelper) (mode left right : Atom) :
    clauses program helper.head [mode, left, right] =
      [.evaluate (tripleEnvironment helper mode left right) (tripleEquation helper).body] := by
  rw [clauses_use_only_the_named_equations]
  change (namedEquations helper.head).filterMap _ = _
  have only : namedEquations helper.head = [tripleEquation helper] := by
    cases helper <;> rfl
  rw [only]
  have formals : (tripleEquation helper).arguments =
      [v "mode", v helper.formals.1, v helper.formals.2] := by
    cases helper <;> decide +kernel
  cases helper <;> simp [formals, tripleEnvironment, TripleHelper.formals,
    SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]

private theorem triple_call (helper : TripleHelper) (caller : Subst) (state : State)
    (mode left right one two three answer : Atom)
    (captured : [one, two, three].map (applySubst caller) = [mode, left, right])
    (returned : PureReturns program (tripleEnvironment helper mode left right) state
      (tripleEquation helper).body state answer) :
    PureReturns program caller state (a helper.head [one, two, three]) state answer := by
  apply PureData.raw_authored_call_return program caller
    (tripleEnvironment helper mode left right) state state helper.head [one, two, three]
    (tripleEquation helper).body answer (by cases helper <;> decide)
    (by cases helper <;> decide) (by cases helper <;> decide)
    (by cases helper <;> decide +kernel) _ _ returned
  · intro index bounded
    have positions : index = 0 ∨ index = 1 ∨ index = 2 := by
      simp only [List.length_cons, List.length_nil] at bounded
      omega
    rcases positions with rfl | rfl | rfl <;> cases helper <;> decide +kernel
  · rw [captured]
    exact triple_clause helper mode left right

private theorem triple_capture (helper : TripleHelper) (caller : Subst) (state : State)
    (mode left right one two three answer : Atom)
    (captured : [one, two, three].map (applySubst caller) = [mode, left, right])
    (closed : [mode, left, right].map (applySubst []) = [mode, left, right])
    (returned : PureReturns program [] state (a helper.head [mode, left, right]) state answer) :
    PureReturns program caller state (a helper.head [one, two, three]) state answer := by
  apply PureData.raw_capture_returns program [] caller state state helper.head
    [mode, left, right] [one, two, three] answer (by cases helper <;> decide +kernel)
    _ (by cases helper <;> decide) _ returned
  · intro index bounded
    have positions : index = 0 ∨ index = 1 ∨ index = 2 := by
      simp only [List.length_cons, List.length_nil] at bounded
      omega
    rcases positions with rfl | rfl | rfl <;> cases helper <;> decide +kernel
  · exact closed.trans captured.symm

private def coherentBody : Atom :=
  a "if" [a "==" [v "left", v "right"], Effects.boolean true,
    a "if" [a "==" [v "origin", v "other-origin"], Effects.boolean false,
      a "if" [a "==" [v "label", v "other-label"], Effects.boolean false, Effects.boolean true]]]

private def viewBody : Atom :=
  a "if" [a "==" [v "label", v "other-label"], a "==" [v "left", v "right"], Effects.boolean true]

private def compatibleModeCases : SpaceSemantics.Cases :=
  [(.symbol "CoherentOriginV1", coherentBody),
   (.symbol "StructuralOriginViewV1", viewBody), (v "bad", Effects.boolean false)]

private def compatiblePairCases : SpaceSemantics.Cases :=
  [(.expression [a "ModuleEntry" [v "origin", v "label", v "body"],
      a "ModuleEntry" [v "other-origin", v "other-label", v "other-body"]],
      a "case" [v "mode", .expression (compatibleModeCases.map fun row => .expression [row.1, row.2])]),
   (v "bad", Effects.boolean false)]

private theorem compatible_shape : (tripleEquation .compatible).body =
    a "case" [.expression [v "left", v "right"],
      .expression (compatiblePairCases.map fun row => .expression [row.1, row.2])] := by
  decide +kernel

private theorem decide_if_returns (caller : Subst) (state : State) (condition yes no answer : Atom)
    (proposition : Prop) [Decidable proposition]
    (tested : PureReturns program caller state condition state (Effects.boolean (decide proposition)))
    (chosen : PureReturns program caller state (if proposition then yes else no) state answer) :
    PureReturns program caller state (a "if" [condition, yes, no]) state answer := by
  apply if_returns program caller state state state _ _ _ _ _ tested
  have guard (value : Bool) : (Effects.boolean value == Effects.boolean true) = value := by
    cases value <;> rfl
  rw [guard]
  simpa only [decide_eq_true_eq] using chosen

private theorem compatible_body_returns (contract : ImportContract) (first second : WireEntry)
    (state : State) :
    PureReturns program (tripleEnvironment .compatible (modeValue contract) (entryValue first) (entryValue second))
      state (tripleEquation .compatible).body state
      (Effects.boolean (contract.entryCompatible first second)) := by
  let caller := tripleEnvironment .compatible (modeValue contract) (entryValue first) (entryValue second)
  let selected : Subst :=
    [("other-body", encoded second.body), ("other-label", encoded second.label),
     ("other-origin", encoded second.origin), ("body", encoded first.body),
     ("label", encoded first.label), ("origin", encoded first.origin)] ++ caller
  rw [compatible_shape]
  apply case_returns program caller selected state state state
    (.expression [v "left", v "right"]) (.expression [entryValue first, entryValue second])
    (a "case" [v "mode", .expression (compatibleModeCases.map fun row => .expression [row.1, row.2])])
    _ _ compatiblePairCases (read_cases_encoded _) _ _ _
  · simpa [caller, tripleEnvironment, TripleHelper.formals, applySubst, Subst.lookup] using
      PureData.variables_return program caller state ["left", "right"]
  · simp [compatiblePairCases, entryValue, importEntryTerm, CettaWireAtom.encode, CettaWireAtom.encodeMany,
      SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
      matchAtom, Subst.lookup, selected, caller, tripleEnvironment, TripleHelper.formals]
  · have modeReturned : PureReturns program selected state (v "mode") state (modeValue contract) := by
      simpa [selected, caller, tripleEnvironment, TripleHelper.formals, applySubst, Subst.lookup] using
        variable_returns program selected state "mode"
    have wholeCompared : PureReturns program selected state (a "==" [v "left", v "right"]) state
        (Effects.boolean (decide (first = second))) := by
      simpa only [importEntryTerm_eq] using
        CettaWireAtom.equality_captured_returns program selected state
          (importEntryTerm first) (importEntryTerm second) "left" "right"
          (by simp [selected, caller, tripleEnvironment, TripleHelper.formals, applySubst, Subst.lookup])
          (by simp [selected, caller, tripleEnvironment, TripleHelper.formals, applySubst, Subst.lookup])
    have originCompared := CettaWireAtom.equality_captured_returns program selected state
      first.origin second.origin "origin" "other-origin"
      (by simp [selected, applySubst, Subst.lookup]) (by simp [selected, applySubst, Subst.lookup])
    have labelCompared := CettaWireAtom.equality_captured_returns program selected state
      first.label second.label "label" "other-label"
      (by simp [selected, applySubst, Subst.lookup]) (by simp [selected, applySubst, Subst.lookup])
    cases contract with
    | coherentOrigin =>
        apply case_returns program selected selected state state state (v "mode") (modeValue .coherentOrigin)
          coherentBody _ _ compatibleModeCases (read_cases_encoded _) modeReturned _ _
        · simp [compatibleModeCases, modeValue, ImportContract.wireTerm, CettaWireAtom.encode,
            SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
        · rw [ImportContract.coherentOrigin_formula]
          unfold coherentBody
          apply decide_if_returns selected state _ _ _ _ (first = second) wholeCompared
          by_cases same : first = second
          · simpa only [if_pos same, Effects.boolean] using grounded_returns program selected state (.bool true)
          · simp only [if_neg same]
            apply decide_if_returns selected state _ _ _ _ (first.origin = second.origin) originCompared
            by_cases origin : first.origin = second.origin
            · simpa only [if_pos origin, Effects.boolean] using grounded_returns program selected state (.bool false)
            · simp only [if_neg origin]
              apply decide_if_returns selected state _ _ _ _ (first.label = second.label) labelCompared
              by_cases label : first.label = second.label
              · simpa only [if_pos label, Effects.boolean] using grounded_returns program selected state (.bool false)
              · simpa only [if_neg label, Effects.boolean] using grounded_returns program selected state (.bool true)
    | structuralView =>
        apply case_returns program selected selected state state state (v "mode") (modeValue .structuralView)
          viewBody _ _ compatibleModeCases (read_cases_encoded _) modeReturned _ _
        · simp [compatibleModeCases, modeValue, ImportContract.wireTerm, CettaWireAtom.encode,
            SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
        · rw [ImportContract.structuralView_formula]
          unfold viewBody
          apply decide_if_returns selected state _ _ _ _ (first.label = second.label) labelCompared
          by_cases label : first.label = second.label
          · simpa only [if_pos label] using wholeCompared
          · simpa only [if_neg label, Effects.boolean] using grounded_returns program selected state (.bool true)

theorem compatible_returns (contract : ImportContract) (first second : WireEntry) (state : State) :
    PureReturns program [] state (a "gslt:module:compatible"
      [modeValue contract, entryValue first, entryValue second]) state
      (Effects.boolean (contract.entryCompatible first second)) :=
  triple_call .compatible [] state _ _ _ _ _ _ _ (by simp)
    (compatible_body_returns contract first second state)

theorem compatible_captured_returns (contract : ImportContract) (first second : WireEntry)
    (caller : Subst) (state : State) (one two three : Atom)
    (captured : [one, two, three].map (applySubst caller) =
      [modeValue contract, entryValue first, entryValue second]) :
    PureReturns program caller state (a "gslt:module:compatible" [one, two, three]) state
      (Effects.boolean (contract.entryCompatible first second)) :=
  triple_capture .compatible caller state _ _ _ _ _ _ _ captured (by simp)
    (compatible_returns contract first second state)

private theorem some_template (body : Atom) (inner : PureData.Template program body) :
    PureData.Template program (a "Some" [body]) := by
  apply PureData.Template.constructor "Some" _ (by decide +kernel) (by decide)
  intro field member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  subst field
  exact inner

private theorem cons_template (first rest : Atom)
    (one : PureData.Template program first) (two : PureData.Template program rest) :
    PureData.Template program (a "LCons" [first, rest]) := by
  apply PureData.Template.constructor "LCons" _ (by decide +kernel) (by decide)
  intro field member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact one
  · exact two

private def insertTailBody : Atom := a "Some" [a "LCons" [v "first", v "tail"]]
private def insertTailCases : SpaceSemantics.Cases :=
  [(a "Some" [v "tail"], insertTailBody), (v "bad", .symbol "None")]
private def insertContinue : Atom :=
  a "if" [a "gslt:module:compatible" [v "mode", v "first", v "entry"],
    a "case" [a "gslt:module:insert" [v "mode", v "entry", v "rest"],
      .expression (insertTailCases.map fun row => .expression [row.1, row.2])], .symbol "None"]
private def insertChoice : Atom :=
  a "if" [a "==" [v "entry", v "first"], a "Some" [v "kept"], insertContinue]
private def insertKeptCases : SpaceSemantics.Cases :=
  [(.symbol "LNil", a "Some" [a "LCons" [v "entry", .symbol "LNil"]]),
   (a "LCons" [v "first", v "rest"], insertChoice), (v "bad", .symbol "None")]
private def insertEntryCases : SpaceSemantics.Cases :=
  [(a "ModuleEntry" [v "origin", v "label", v "body"],
    a "case" [v "kept", .expression (insertKeptCases.map fun row => .expression [row.1, row.2])]),
   (v "bad", .symbol "None")]

private theorem insert_shape : (tripleEquation .insert).body =
    a "case" [v "entry", .expression (insertEntryCases.map fun row => .expression [row.1, row.2])] := by
  decide +kernel

private theorem insert_body_returns (contract : ImportContract) (entry : WireEntry) (state : State) :
    ∀ kept : List WireEntry,
      PureReturns program (tripleEnvironment .insert (modeValue contract) (entryValue entry) (entriesValue kept))
        state (tripleEquation .insert).body state
        (encoded (resultTerm (List.insertCompatible? contract.entryCompatible entry kept))) := by
  intro kept
  induction kept with
  | nil =>
      let caller := tripleEnvironment .insert (modeValue contract) (entryValue entry) (entriesValue [])
      let selected : Subst := [("body", encoded entry.body), ("label", encoded entry.label),
        ("origin", encoded entry.origin)] ++ caller
      rw [insert_shape]
      apply case_returns program caller selected state state state (v "entry") (entryValue entry)
        (a "case" [v "kept", .expression (insertKeptCases.map fun row => .expression [row.1, row.2])])
        _ _ insertEntryCases (read_cases_encoded _) _ _ _
      · simpa [caller, tripleEnvironment, TripleHelper.formals, applySubst, Subst.lookup] using
          variable_returns program caller state "entry"
      · simp [insertEntryCases, entryValue, importEntryTerm, CettaWireAtom.encode, CettaWireAtom.encodeMany,
          selected, caller, tripleEnvironment, TripleHelper.formals, SpaceSemantics.selectCase,
          SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]
      · apply case_returns program selected selected state state state (v "kept") (.symbol "LNil")
          (a "Some" [a "LCons" [v "entry", .symbol "LNil"]]) _ _ insertKeptCases
          (read_cases_encoded _) _ _ _
        · simpa [selected, caller, tripleEnvironment, TripleHelper.formals, entriesValue,
            rowValue, encodeList, CettaWireAtom.encode, applySubst, Subst.lookup] using
            variable_returns program selected state "kept"
        · simp [insertKeptCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
        · simpa [List.insertCompatible?, resultTerm, entriesValue, rowValue, encodeList,
            CettaWireAtom.encode, CettaWireAtom.encodeMany, applySubst, applySubst.applySubstList,
            Subst.lookup, List.find?_cons, selected, caller, tripleEnvironment, TripleHelper.formals,
            entryValue] using
            PureData.template_return program selected state
              (a "Some" [a "LCons" [v "entry", .symbol "LNil"]])
              (some_template _ (cons_template _ _ (.captured "entry") (.symbol "LNil")))
  | cons first rest ih =>
      let caller := tripleEnvironment .insert (modeValue contract) (entryValue entry) (entriesValue (first :: rest))
      let selected : Subst := [("body", encoded entry.body), ("label", encoded entry.label),
        ("origin", encoded entry.origin)] ++ caller
      let below : Subst := [("rest", entriesValue rest), ("first", entryValue first)] ++ selected
      rw [insert_shape]
      apply case_returns program caller selected state state state (v "entry") (entryValue entry)
        (a "case" [v "kept", .expression (insertKeptCases.map fun row => .expression [row.1, row.2])])
        _ _ insertEntryCases (read_cases_encoded _) _ _ _
      · simpa [caller, tripleEnvironment, TripleHelper.formals, applySubst, Subst.lookup] using
          variable_returns program caller state "entry"
      · simp [insertEntryCases, entryValue, importEntryTerm, CettaWireAtom.encode, CettaWireAtom.encodeMany,
          selected, caller, tripleEnvironment, TripleHelper.formals, SpaceSemantics.selectCase,
          SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]
      · apply case_returns program selected below state state state (v "kept") (entriesValue (first :: rest))
          insertChoice _ _ insertKeptCases (read_cases_encoded _) _ _ _
        · simpa [selected, caller, tripleEnvironment, TripleHelper.formals, applySubst, Subst.lookup] using
            variable_returns program selected state "kept"
        · simp [insertKeptCases, below, entriesValue, rowValue, encodeList, entryValue,
            CettaWireAtom.encode, CettaWireAtom.encodeMany, SpaceSemantics.selectCase,
            SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup,
            selected, caller, tripleEnvironment, TripleHelper.formals]
        · unfold insertChoice
          have compared : PureReturns program below state (a "==" [v "entry", v "first"]) state
              (Effects.boolean (decide (entry = first))) := by
            simpa only [importEntryTerm_eq] using
              CettaWireAtom.equality_captured_returns program below state
                (importEntryTerm entry) (importEntryTerm first) "entry" "first"
                (by simp [below, selected, caller, tripleEnvironment, TripleHelper.formals,
                  applySubst, Subst.lookup]) (by simp [below, applySubst, Subst.lookup])
          apply decide_if_returns below state _ _ _ _ (entry = first) compared
          by_cases same : entry = first
          · simp only [if_pos same, List.insertCompatible?, resultTerm]
            simpa [entriesValue, rowValue, encodeList, CettaWireAtom.encode, CettaWireAtom.encodeMany,
                applySubst, applySubst.applySubstList, Subst.lookup,
                below, selected, caller, tripleEnvironment, TripleHelper.formals, List.find?_cons] using
              PureData.template_return program below state _ (some_template _ (.captured "kept"))
          · simp only [if_neg same, List.insertCompatible?]
            unfold insertContinue
            have allowed := compatible_captured_returns contract first entry below state
              (v "mode") (v "first") (v "entry")
              (by simp [below, selected, caller, tripleEnvironment, TripleHelper.formals,
                applySubst, Subst.lookup])
            apply if_returns program below state state state _ _ _ _ _ allowed
            have guard (value : Bool) : (Effects.boolean value == Effects.boolean true) = value := by
              cases value <;> rfl
            rw [guard]
            cases accepted : contract.entryCompatible first entry with
            | false =>
                simpa only [Bool.false_eq_true, ite_false, resultTerm, CettaWireAtom.encode] using
                  symbol_returns program below state "None"
            | true =>
                simp only [ite_true]
                have recursive := triple_call .insert below state (modeValue contract) (entryValue entry)
                  (entriesValue rest) (v "mode") (v "entry") (v "rest") _
                  (by simp [below, selected, caller, tripleEnvironment, TripleHelper.formals,
                    applySubst, Subst.lookup]) ih
                cases next : List.insertCompatible? contract.entryCompatible entry rest with
                | none =>
                    let failed : Subst := ("bad", .symbol "None") :: below
                    apply case_returns program below failed state state state _ (.symbol "None")
                      (.symbol "None") _ _ insertTailCases (read_cases_encoded _)
                      (by simpa only [TripleHelper.head, next, resultTerm, CettaWireAtom.encode] using recursive) _ _
                    · simp [insertTailCases, failed, below, selected, caller, tripleEnvironment,
                        TripleHelper.formals, SpaceSemantics.selectCase,
                        SpaceSemantics.matchValue, matchAtom, Subst.lookup]
                    · simpa only [next, Option.map_none, resultTerm, CettaWireAtom.encode] using
                        symbol_returns program failed state "None"
                | some tail =>
                    let returned : Subst := ("tail", entriesValue tail) :: below
                    apply case_returns program below returned state state state _
                      (a "Some" [entriesValue tail]) insertTailBody _ _ insertTailCases (read_cases_encoded _)
                      (by simpa only [TripleHelper.head, next, resultTerm, CettaWireAtom.encode,
                        CettaWireAtom.encodeMany] using recursive) _ _
                    · simp [insertTailCases, returned, below, selected, caller, tripleEnvironment,
                        TripleHelper.formals, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
                        SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]
                    · simpa [next, resultTerm, insertTailBody, entriesValue, rowValue, encodeList,
                        CettaWireAtom.encode, CettaWireAtom.encodeMany, applySubst, applySubst.applySubstList,
                        Subst.lookup, returned, below, List.find?_cons] using
                        PureData.template_return program returned state _
                          (some_template _ (cons_template _ _ (.captured "first") (.captured "tail")))

theorem insert_returns (contract : ImportContract) (entry : WireEntry) (kept : List WireEntry) (state : State) :
    PureReturns program [] state (a "gslt:module:insert"
      [modeValue contract, entryValue entry, entriesValue kept]) state
      (encoded (resultTerm (List.insertCompatible? contract.entryCompatible entry kept))) :=
  triple_call .insert [] state _ _ _ _ _ _ _ (by simp) (insert_body_returns contract entry state kept)

theorem insert_captured_returns (contract : ImportContract) (entry : WireEntry) (kept : List WireEntry)
    (caller : Subst) (state : State) (one two three : Atom)
    (captured : [one, two, three].map (applySubst caller) =
      [modeValue contract, entryValue entry, entriesValue kept]) :
    PureReturns program caller state (a "gslt:module:insert" [one, two, three]) state
      (encoded (resultTerm (List.insertCompatible? contract.entryCompatible entry kept))) :=
  triple_capture .insert caller state _ _ _ _ _ _ _ captured (by simp)
    (insert_returns contract entry kept state)

private def foldNextCases : SpaceSemantics.Cases :=
  [(a "Some" [v "next"], a "gslt:module:fold" [v "mode", v "next", v "rest"]),
   (v "bad", .symbol "None")]
private def foldContinue : Atom :=
  a "case" [a "gslt:module:insert" [v "mode", v "entry", v "kept"],
    .expression (foldNextCases.map fun row => .expression [row.1, row.2])]
private def foldCases : SpaceSemantics.Cases :=
  [(.symbol "LNil", a "Some" [v "kept"]),
   (a "LCons" [v "entry", v "rest"], foldContinue), (v "bad", .symbol "None")]

private theorem fold_shape : (tripleEquation .fold).body =
    a "case" [v "incoming", .expression (foldCases.map fun row => .expression [row.1, row.2])] := by
  decide +kernel

private theorem fold_body_returns (contract : ImportContract) (state : State) :
    ∀ incoming kept : List WireEntry,
      PureReturns program (tripleEnvironment .fold (modeValue contract) (entriesValue kept) (entriesValue incoming))
        state (tripleEquation .fold).body state
        (encoded (resultTerm (List.unionCompatible? contract.entryCompatible kept incoming))) := by
  intro incoming
  induction incoming with
  | nil =>
      intro kept
      let caller := tripleEnvironment .fold (modeValue contract) (entriesValue kept) (entriesValue [])
      rw [fold_shape]
      apply case_returns program caller caller state state state (v "incoming") (.symbol "LNil")
        (a "Some" [v "kept"]) _ _ foldCases (read_cases_encoded _) _ _ _
      · simpa [caller, tripleEnvironment, TripleHelper.formals, entriesValue, rowValue,
          encodeList, CettaWireAtom.encode, applySubst, Subst.lookup] using
          variable_returns program caller state "incoming"
      · simp [foldCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
      · simpa [List.unionCompatible?, resultTerm, entriesValue, rowValue, CettaWireAtom.encode,
          CettaWireAtom.encodeMany, applySubst, applySubst.applySubstList, Subst.lookup,
          caller, tripleEnvironment, TripleHelper.formals] using
          PureData.template_return program caller state _ (some_template _ (.captured "kept"))
  | cons entry rest ih =>
      intro kept
      let caller := tripleEnvironment .fold (modeValue contract) (entriesValue kept) (entriesValue (entry :: rest))
      let selected : Subst := [("rest", entriesValue rest), ("entry", entryValue entry)] ++ caller
      rw [fold_shape]
      apply case_returns program caller selected state state state (v "incoming")
        (entriesValue (entry :: rest)) foldContinue _ _ foldCases (read_cases_encoded _) _ _ _
      · simpa [caller, tripleEnvironment, TripleHelper.formals, applySubst, Subst.lookup] using
          variable_returns program caller state "incoming"
      · simp [foldCases, selected, entriesValue, rowValue, encodeList, CettaWireAtom.encode,
          CettaWireAtom.encodeMany, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
          SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup, caller,
          tripleEnvironment, TripleHelper.formals]
      · unfold foldContinue
        have inserted := insert_captured_returns contract entry kept selected state
          (v "mode") (v "entry") (v "kept")
          (by simp [selected, caller, tripleEnvironment, TripleHelper.formals, applySubst, Subst.lookup])
        cases next : List.insertCompatible? contract.entryCompatible entry kept with
        | none =>
            let failed : Subst := ("bad", .symbol "None") :: selected
            apply case_returns program selected failed state state state _ (.symbol "None")
              (.symbol "None") _ _ foldNextCases (read_cases_encoded _)
              (by simpa only [next, resultTerm, CettaWireAtom.encode] using inserted) _ _
            · simp [foldNextCases, failed, selected, caller, tripleEnvironment, TripleHelper.formals,
                SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom, Subst.lookup]
            · simpa [List.unionCompatible?, next, resultTerm, CettaWireAtom.encode] using
                symbol_returns program failed state "None"
        | some entries =>
            let returned : Subst := ("next", entriesValue entries) :: selected
            apply case_returns program selected returned state state state _
              (a "Some" [entriesValue entries]) (a "gslt:module:fold" [v "mode", v "next", v "rest"])
              _ _ foldNextCases (read_cases_encoded _)
              (by simpa only [next, resultTerm, CettaWireAtom.encode, CettaWireAtom.encodeMany] using inserted) _ _
            · simp [foldNextCases, returned, selected, caller, tripleEnvironment, TripleHelper.formals,
                SpaceSemantics.selectCase, SpaceSemantics.matchValue,
                SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]
            · simpa [List.unionCompatible?, next, TripleHelper.head] using
                triple_call .fold returned state (modeValue contract) (entriesValue entries) (entriesValue rest)
                  (v "mode") (v "next") (v "rest") _
                  (by simp [returned, selected, caller, tripleEnvironment, TripleHelper.formals,
                    applySubst, Subst.lookup]) (ih entries)

theorem fold_returns (contract : ImportContract) (kept incoming : List WireEntry) (state : State) :
    PureReturns program [] state (a "gslt:module:fold"
      [modeValue contract, entriesValue kept, entriesValue incoming]) state
      (encoded (resultTerm (List.unionCompatible? contract.entryCompatible kept incoming))) :=
  triple_call .fold [] state _ _ _ _ _ _ _ (by simp) (fold_body_returns contract state incoming kept)

theorem fold_captured_returns (contract : ImportContract) (kept incoming : List WireEntry)
    (caller : Subst) (state : State) (one two three : Atom)
    (captured : [one, two, three].map (applySubst caller) =
      [modeValue contract, entriesValue kept, entriesValue incoming]) :
    PureReturns program caller state (a "gslt:module:fold" [one, two, three]) state
      (encoded (resultTerm (List.unionCompatible? contract.entryCompatible kept incoming))) :=
  triple_capture .fold caller state _ _ _ _ _ _ _ captured (by simp)
    (fold_returns contract kept incoming state)

private def checkEquation : SpaceSemantics.Equation :=
  (namedEquations "gslt:module:check")[0]'(by decide +kernel)
private def checkEnvironment (mode entries : Atom) : Subst := [("entries", entries), ("mode", mode)]
private def checkBody : Atom := a "gslt:module:fold" [v "mode", .symbol "LNil", v "entries"]
private def checkCases : SpaceSemantics.Cases :=
  [(.symbol "CoherentOriginV1", checkBody), (.symbol "StructuralOriginViewV1", checkBody),
   (v "bad", .symbol "None")]

private theorem check_shape : checkEquation.body =
    a "case" [v "mode", .expression (checkCases.map fun row => .expression [row.1, row.2])] := by
  decide +kernel

private theorem check_clause (mode entries : Atom) :
    clauses program "gslt:module:check" [mode, entries] =
      [.evaluate (checkEnvironment mode entries) checkEquation.body] := by
  rw [clauses_use_only_the_named_equations]
  change (namedEquations "gslt:module:check").filterMap _ = _
  rw [show namedEquations "gslt:module:check" = [checkEquation] from rfl]
  have formals : checkEquation.arguments = [v "mode", v "entries"] := by decide +kernel
  simp [formals, checkEnvironment, SpaceSemantics.matchValue,
    SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]

private theorem check_call (caller : Subst) (state : State) (mode entries first second answer : Atom)
    (captured : [first, second].map (applySubst caller) = [mode, entries])
    (returned : PureReturns program (checkEnvironment mode entries) state checkEquation.body state answer) :
    PureReturns program caller state (a "gslt:module:check" [first, second]) state answer := by
  apply PureData.raw_authored_call_return program caller (checkEnvironment mode entries) state state
    "gslt:module:check" [first, second] checkEquation.body answer
    (by decide) (by decide) (by decide) (by decide +kernel) _ _ returned
  · intro index bounded
    have positions : index = 0 ∨ index = 1 := by
      simp only [List.length_cons, List.length_nil] at bounded
      omega
    rcases positions with rfl | rfl <;> decide +kernel
  · rw [captured]
    exact check_clause mode entries

private theorem check_body_returns (contract : ImportContract) (entries : List WireEntry) (state : State) :
    PureReturns program (checkEnvironment (modeValue contract) (entriesValue entries))
      state checkEquation.body state (encoded (resultTerm (contract.check? entries))) := by
  let caller := checkEnvironment (modeValue contract) (entriesValue entries)
  rw [check_shape]
  apply case_returns program caller caller state state state (v "mode") (modeValue contract)
    checkBody _ _ checkCases (read_cases_encoded _) _ _ _
  · simpa [caller, checkEnvironment, applySubst, Subst.lookup] using
      variable_returns program caller state "mode"
  · cases contract <;> simp [checkCases, modeValue, ImportContract.wireTerm, CettaWireAtom.encode,
      SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
  · simpa only [checkBody, ImportContract.check?] using
      fold_captured_returns contract [] entries caller state (v "mode") (.symbol "LNil") (v "entries")
        (by simp [caller, checkEnvironment, entriesValue, rowValue, encodeList,
          CettaWireAtom.encode, applySubst, Subst.lookup])

theorem check_returns (contract : ImportContract) (entries : List WireEntry) (state : State) :
    PureReturns program [] state (a "gslt:module:check" [modeValue contract, entriesValue entries]) state
      (encoded (resultTerm (contract.check? entries))) :=
  check_call [] state _ _ _ _ _ (by simp) (check_body_returns contract entries state)

theorem check_captured_returns (contract : ImportContract) (entries : List WireEntry)
    (caller : Subst) (state : State) (first second : Atom)
    (captured : [first, second].map (applySubst caller) = [modeValue contract, entriesValue entries]) :
    PureReturns program caller state (a "gslt:module:check" [first, second]) state
      (encoded (resultTerm (contract.check? entries))) :=
  check_call caller state _ _ _ _ _ captured (check_body_returns contract entries state)

private def joinCases : SpaceSemantics.Cases :=
  [(a "Some" [v "kept"], a "gslt:module:fold" [v "mode", v "kept", v "right"]),
   (v "bad", .symbol "None")]
private theorem join_shape : (tripleEquation .join).body =
    a "case" [a "gslt:module:check" [v "mode", v "left"],
      .expression (joinCases.map fun row => .expression [row.1, row.2])] := by
  decide +kernel

private theorem join_stages (contract : ImportContract) (first second : List WireEntry) :
    contract.join? first second =
      (contract.check? first).bind (fun kept => List.unionCompatible? contract.entryCompatible kept second) :=
  List.unionCompatible?_append contract.entryCompatible [] first second

private theorem join_body_returns (contract : ImportContract) (first second : List WireEntry) (state : State) :
    PureReturns program (tripleEnvironment .join (modeValue contract) (entriesValue first) (entriesValue second))
      state (tripleEquation .join).body state (encoded (resultTerm (contract.join? first second))) := by
  let caller := tripleEnvironment .join (modeValue contract) (entriesValue first) (entriesValue second)
  rw [join_shape]
  have checked := check_captured_returns contract first caller state (v "mode") (v "left")
    (by simp [caller, tripleEnvironment, TripleHelper.formals, applySubst, Subst.lookup])
  cases accepted : contract.check? first with
  | none =>
      let failed : Subst := ("bad", .symbol "None") :: caller
      apply case_returns program caller failed state state state _ (.symbol "None") (.symbol "None")
        _ _ joinCases (read_cases_encoded _)
        (by simpa only [accepted, resultTerm, CettaWireAtom.encode] using checked) _ _
      · simp [joinCases, failed, caller, tripleEnvironment, TripleHelper.formals,
          SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom, Subst.lookup]
      · simpa only [join_stages, accepted, Option.bind_none, resultTerm, CettaWireAtom.encode] using
          symbol_returns program failed state "None"
  | some kept =>
      let selected : Subst := ("kept", entriesValue kept) :: caller
      apply case_returns program caller selected state state state _ (a "Some" [entriesValue kept])
        (a "gslt:module:fold" [v "mode", v "kept", v "right"]) _ _ joinCases (read_cases_encoded _)
        (by simpa only [accepted, resultTerm, CettaWireAtom.encode, CettaWireAtom.encodeMany] using checked) _ _
      · simp [joinCases, selected, caller, tripleEnvironment, TripleHelper.formals,
          SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
          matchAtom, Subst.lookup]
      · simpa only [join_stages, accepted, Option.bind_some] using
          fold_captured_returns contract kept second selected state (v "mode") (v "kept") (v "right")
            (by simp [selected, caller, tripleEnvironment, TripleHelper.formals, applySubst, Subst.lookup])

theorem join_returns (contract : ImportContract) (first second : List WireEntry) (state : State) :
    PureReturns program [] state (a "gslt:module:join"
      [modeValue contract, entriesValue first, entriesValue second]) state
      (encoded (resultTerm (contract.join? first second))) :=
  triple_call .join [] state _ _ _ _ _ _ _ (by simp) (join_body_returns contract first second state)

theorem join_captured_returns (contract : ImportContract) (first second : List WireEntry)
    (caller : Subst) (state : State) (one two three : Atom)
    (captured : [one, two, three].map (applySubst caller) =
      [modeValue contract, entriesValue first, entriesValue second]) :
    PureReturns program caller state (a "gslt:module:join" [one, two, three]) state
      (encoded (resultTerm (contract.join? first second))) :=
  triple_capture .join caller state _ _ _ _ _ _ _ captured (by simp)
    (join_returns contract first second state)

theorem check_completed_iff (contract : ImportContract) (entries : List WireEntry)
    (state after : State) (answers input output : List Atom) :
    (∃ fuel, run program fuel
      {state, control := .evaluate [] (a "gslt:module:check" [modeValue contract, entriesValue entries])} =
        .complete after answers input output) ↔
      after = state ∧ answers = [encoded (resultTerm (contract.check? entries))] ∧ input = [] ∧ output = [] :=
  pure_returns_completed_iff program [] state state _ _ (check_returns contract entries state)
    after answers input output

theorem check_derivation_iff (contract : ImportContract) (entries : List WireEntry)
    (state after : State) (answers input output : List Atom) :
    DeclarativeSpec.Runs program
      {state, control := .evaluate [] (a "gslt:module:check" [modeValue contract, entriesValue entries])}
        (.complete after answers input output) ↔
      after = state ∧ answers = [encoded (resultTerm (contract.check? entries))] ∧ input = [] ∧ output = [] :=
  pure_returns_derivation_iff program [] state state _ _ (check_returns contract entries state)
    after answers input output

theorem join_completed_iff (contract : ImportContract) (first second : List WireEntry)
    (state after : State) (answers input output : List Atom) :
    (∃ fuel, run program fuel {state, control := .evaluate [] (a "gslt:module:join"
      [modeValue contract, entriesValue first, entriesValue second])} =
        .complete after answers input output) ↔
      after = state ∧ answers = [encoded (resultTerm (contract.join? first second))] ∧ input = [] ∧ output = [] :=
  pure_returns_completed_iff program [] state state _ _ (join_returns contract first second state)
    after answers input output

theorem join_derivation_iff (contract : ImportContract) (first second : List WireEntry)
    (state after : State) (answers input output : List Atom) :
    DeclarativeSpec.Runs program {state, control := .evaluate [] (a "gslt:module:join"
      [modeValue contract, entriesValue first, entriesValue second])}
        (.complete after answers input output) ↔
      after = state ∧ answers = [encoded (resultTerm (contract.join? first second))] ∧ input = [] ∧ output = [] :=
  pure_returns_derivation_iff program [] state state _ _ (join_returns contract first second state)
    after answers input output

theorem check_returns_some_iff (contract : ImportContract) (entries kept : List WireEntry) (state : State) :
    DeclarativeSpec.Runs program
      {state, control := .evaluate [] (a "gslt:module:check" [modeValue contract, entriesValue entries])}
      (.complete state [encoded (resultTerm (some kept))] [] []) ↔ contract.check? entries = some kept := by
  constructor
  · intro executed
    have observation := (check_derivation_iff contract entries state state _ [] []).mp executed
    have same := CettaWireAtom.encode_injective _ _ (List.cons.inj observation.2.1).1
    exact resultTerm_injective same.symm
  · intro checked
    exact (check_derivation_iff contract entries state state _ [] []).mpr
      ⟨rfl, by rw [checked], rfl, rfl⟩

/-- Source acceptance is precisely the selected established import contract. -/
theorem check_accepts_iff (contract : ImportContract) (entries : List WireEntry) (state : State) :
    (∃ kept, DeclarativeSpec.Runs program
      {state, control := .evaluate [] (a "gslt:module:check" [modeValue contract, entriesValue entries])}
      (.complete state [encoded (resultTerm (some kept))] [] [])) ↔
      match contract with
      | .coherentOrigin => ModuleAlgebra.Valid entries.toFinset
      | .structuralView => OriginView.Valid entries.toFinset := by
  constructor
  · rintro ⟨kept, executed⟩
    apply (ImportContract.check_isSome_iff contract entries).mp
    rw [(check_returns_some_iff contract entries kept state).mp executed]
    rfl
  · intro accepted
    have isSome := (ImportContract.check_isSome_iff contract entries).mpr accepted
    cases checked : contract.check? entries with
    | none => simp [checked] at isSome
    | some kept => exact ⟨kept, (check_returns_some_iff contract entries kept state).mpr checked⟩

theorem join_returns_some_iff (contract : ImportContract) (first second kept : List WireEntry) (state : State) :
    DeclarativeSpec.Runs program
      {state, control := .evaluate [] (a "gslt:module:join"
        [modeValue contract, entriesValue first, entriesValue second])}
      (.complete state [encoded (resultTerm (some kept))] [] []) ↔ contract.join? first second = some kept := by
  constructor
  · intro executed
    have observation := (join_derivation_iff contract first second state state _ [] []).mp executed
    have same := CettaWireAtom.encode_injective _ _ (List.cons.inj observation.2.1).1
    exact resultTerm_injective same.symm
  · intro joined
    exact (join_derivation_iff contract first second state state _ [] []).mpr
      ⟨rfl, by rw [joined], rfl, rfl⟩

/-- A source-accepted join contains exactly the imported declaration set. Its
first-occurrence order and body rule multiplicity are handled independently. -/
theorem joined_declarations (contract : ImportContract) (first second kept : List WireEntry) (state : State)
    (executed : DeclarativeSpec.Runs program
      {state, control := .evaluate [] (a "gslt:module:join"
        [modeValue contract, entriesValue first, entriesValue second])}
      (.complete state [encoded (resultTerm (some kept))] [] [])) :
    kept.toFinset = first.toFinset ∪ second.toFinset :=
  contract.join_toFinset first second kept ((join_returns_some_iff contract first second kept state).mp executed)

private def bodiesEquation : SpaceSemantics.Equation :=
  (namedEquations "gslt:module:bodies")[0]'(by decide +kernel)
private def bodiesEnvironment (entries : Atom) : Subst := [("entries", entries)]
private def bodiesContinue : Atom :=
  a "let" [v "tail", a "gslt:module:bodies" [v "rest"], a "LCons" [v "body", v "tail"]]
private def bodiesCases : SpaceSemantics.Cases :=
  [(.symbol "LNil", .symbol "LNil"),
   (a "LCons" [a "ModuleEntry" [v "origin", v "label", v "body"], v "rest"], bodiesContinue)]

private theorem bodies_shape : bodiesEquation.body =
    a "case" [v "entries", .expression (bodiesCases.map fun row => .expression [row.1, row.2])] := by
  decide +kernel

private theorem bodies_clause (entries : Atom) :
    clauses program "gslt:module:bodies" [entries] =
      [.evaluate (bodiesEnvironment entries) bodiesEquation.body] := by
  rw [clauses_use_only_the_named_equations]
  change (namedEquations "gslt:module:bodies").filterMap _ = _
  rw [show namedEquations "gslt:module:bodies" = [bodiesEquation] from rfl]
  have formals : bodiesEquation.arguments = [v "entries"] := by decide +kernel
  simp [formals, bodiesEnvironment, SpaceSemantics.matchValue,
    SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]

private theorem bodies_call (caller : Subst) (state : State) (entries argument answer : Atom)
    (captured : applySubst caller argument = entries)
    (returned : PureReturns program (bodiesEnvironment entries) state bodiesEquation.body state answer) :
    PureReturns program caller state (a "gslt:module:bodies" [argument]) state answer := by
  apply PureData.raw_authored_call_return program caller (bodiesEnvironment entries) state state
    "gslt:module:bodies" [argument] bodiesEquation.body answer
    (by decide) (by decide) (by decide) (by decide +kernel) _ _ returned
  · intro index bounded
    have only : index = 0 := by simpa using bounded
    subst index
    decide +kernel
  · simp only [List.map_cons, List.map_nil, captured]
    exact bodies_clause entries

private theorem bodies_body_returns (state : State) :
    ∀ entries : List WireEntry,
      PureReturns program (bodiesEnvironment (entriesValue entries)) state bodiesEquation.body state
        (rowValue Entry.body entries) := by
  intro entries
  induction entries with
  | nil =>
      let caller := bodiesEnvironment (.symbol "LNil")
      rw [bodies_shape]
      apply case_returns program caller caller state state state (v "entries") (.symbol "LNil")
        (.symbol "LNil") _ _ bodiesCases (read_cases_encoded _) _ _ _
      · simpa [caller, bodiesEnvironment, applySubst, Subst.lookup] using
          variable_returns program caller state "entries"
      · simp [bodiesCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
      · exact symbol_returns program caller state "LNil"
  | cons entry rest ih =>
      let caller := bodiesEnvironment (entriesValue (entry :: rest))
      let selected := [("rest", entriesValue rest), ("body", encoded entry.body),
        ("label", encoded entry.label), ("origin", encoded entry.origin)] ++ caller
      let finished := ("tail", rowValue Entry.body rest) :: selected
      rw [bodies_shape]
      apply case_returns program caller selected state state state (v "entries")
        (entriesValue (entry :: rest)) bodiesContinue _ _ bodiesCases (read_cases_encoded _) _ _ _
      · simpa [caller, bodiesEnvironment, applySubst, Subst.lookup] using
          variable_returns program caller state "entries"
      · simp [bodiesCases, selected, caller, bodiesEnvironment, entriesValue, rowValue,
          importEntryTerm, encodeList, CettaWireAtom.encode, CettaWireAtom.encodeMany,
          SpaceSemantics.selectCase, SpaceSemantics.matchValue,
          SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]
      · unfold bodiesContinue
        apply let_returns program selected finished state state state _ _ _ _ _
          (bodies_call selected state (entriesValue rest) (v "rest") _
            (by simp [selected, applySubst, Subst.lookup]) ih) _ _
        · simp [finished, selected, caller, bodiesEnvironment,
            SpaceSemantics.matchValue, matchAtom, Subst.lookup]
        · simpa [finished, selected, caller, bodiesEnvironment, rowValue, encodeList,
            CettaWireAtom.encode, CettaWireAtom.encodeMany, applySubst, applySubst.applySubstList,
            Subst.lookup] using
            PureData.template_return program finished state (a "LCons" [v "body", v "tail"])
              (cons_template (v "body") (v "tail") (.captured _) (.captured _))

/-- Project declaration bodies without evaluating or deduplicating their rows. -/
theorem bodies_returns (entries : List WireEntry) (state : State) :
    PureReturns program [] state (a "gslt:module:bodies" [entriesValue entries]) state
      (rowValue Entry.body entries) :=
  bodies_call [] state _ _ _ (by simp) (bodies_body_returns state entries)

theorem bodies_captured_returns (entries : List WireEntry) (caller : Subst) (state : State)
    (argument : Atom) (captured : applySubst caller argument = entriesValue entries) :
    PureReturns program caller state (a "gslt:module:bodies" [argument]) state
      (rowValue Entry.body entries) :=
  bodies_call caller state _ _ _ captured (bodies_body_returns state entries)

private def importEquation : SpaceSemantics.Equation :=
  (namedEquations "gslt:module:import-reducts")[0]'(by decide +kernel)
private def importEnvironment (mode name first second strategy rows depth subject : Atom) : Subst :=
  [("subject", subject), ("depth", depth), ("rows", rows), ("strategy", strategy),
   ("right", second), ("left", first), ("name", name), ("mode", mode)]
private def importContinue : Atom :=
  a "let" [v "fragments", a "gslt:module:bodies" [v "entries"],
    a "gslt:module:reducts" [v "name", v "fragments", v "strategy", v "rows", v "depth", v "subject"]]
private def importCases : SpaceSemantics.Cases :=
  [(a "Some" [v "entries"], importContinue), (v "bad", .symbol "None")]

private theorem import_shape : importEquation.body =
    a "case" [a "gslt:module:join" [v "mode", v "left", v "right"],
      .expression (importCases.map fun row => .expression [row.1, row.2])] := by
  decide +kernel

private theorem import_clause (mode name first second strategy rows depth subject : Atom) :
    clauses program "gslt:module:import-reducts" [mode, name, first, second, strategy, rows, depth, subject] =
      [.evaluate (importEnvironment mode name first second strategy rows depth subject) importEquation.body] := by
  rw [clauses_use_only_the_named_equations]
  change (namedEquations "gslt:module:import-reducts").filterMap _ = _
  rw [show namedEquations "gslt:module:import-reducts" = [importEquation] from rfl]
  have formals : importEquation.arguments =
      [v "mode", v "name", v "left", v "right", v "strategy", v "rows", v "depth", v "subject"] := by
    decide +kernel
  simp [formals, importEnvironment, SpaceSemantics.matchValue,
    SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]

private theorem import_call (caller : Subst) (state : State)
    (mode name first second strategy rows depth subject answer : Atom) (arguments : List Atom)
    (captured : arguments.map (applySubst caller) = [mode, name, first, second, strategy, rows, depth, subject])
    (returned : PureReturns program (importEnvironment mode name first second strategy rows depth subject)
      state importEquation.body state answer) :
    PureReturns program caller state (a "gslt:module:import-reducts" arguments) state answer := by
  apply PureData.raw_authored_call_return program caller
    (importEnvironment mode name first second strategy rows depth subject) state state
    "gslt:module:import-reducts" arguments importEquation.body answer
    (by decide) (by decide) (by decide) (by decide +kernel) _ _ returned
  · have length : arguments.length = 8 := by
      have counted := congrArg List.length captured
      simpa using counted
    intro index bounded
    rw [length] at bounded
    interval_cases index <;> decide +kernel
  · rw [captured]
    exact import_clause mode name first second strategy rows depth subject

/-- An import conflict refuses execution before inspecting the proposed
strategy, providers, depth or subject. Captured values remain opaque. -/
theorem refused_captured_returns (contract : ImportContract) (first second : List WireEntry)
    (refused : contract.join? first second = none) (caller : Subst) (state : State)
    (name strategy rows depth subject : Atom) (arguments : List Atom)
    (captured : arguments.map (applySubst caller) =
      [modeValue contract, name, entriesValue first, entriesValue second, strategy, rows, depth, subject]) :
    PureReturns program caller state (a "gslt:module:import-reducts" arguments) state (.symbol "None") := by
  let callee := importEnvironment (modeValue contract) name (entriesValue first) (entriesValue second)
    strategy rows depth subject
  let selected := ("bad", .symbol "None") :: callee
  apply import_call caller state _ _ _ _ _ _ _ _ _ arguments captured
  rw [import_shape]
  apply case_returns program callee selected state state state
    (a "gslt:module:join" [v "mode", v "left", v "right"]) (.symbol "None") (.symbol "None")
    _ _ importCases (read_cases_encoded _) _ _ (symbol_returns program selected state "None")
  · simpa only [refused, resultTerm, CettaWireAtom.encode] using
      join_captured_returns contract first second callee state (v "mode") (v "left") (v "right")
        (by simp [callee, importEnvironment, applySubst, Subst.lookup])
  · simp [importCases, selected, callee, importEnvironment, SpaceSemantics.selectCase,
      SpaceSemantics.matchValue, matchAtom, Subst.lookup]

def queryTerm (contract : ImportContract) (name : String) (first second : List WireEntry)
    (strategy : MeTTaILMatchAutomataExecution.Strategy)
    (rows : List Mettapedia.OSLF.MeTTaIL.GeneralPremise.ProviderRow) (depth : Nat)
    (subject : PatternPlan) : Term :=
  .application "gslt:module:import-reducts" [contract.wireTerm, .string name,
    encodeList importEntryTerm first, encodeList importEntryTerm second,
    ContextualRuleExecution.strategyTerm strategy, RelationPremiseExecution.providerRowsTerm rows,
    .natural depth, InferenceCettaWire.encodePattern subject.erase]

/-- Checked declarations are projected once, then executed as one complete
language. The explicit body projection retains the original row encoders;
no equality of languages is inferred from an arbitrary encoder. -/
theorem reducts_captured_returns (contract : ImportContract) (first second kept : List WireEntry)
    (joined : contract.join? first second = some kept) (caller : Subst) (state : State) (name : String)
    (types : TypeDecl → Term) (terms : GrammarRule → Term) (equations : Equation → Term)
    (contexts fields : RewriteRule → Term) (fragments : List LanguageDef)
    (bodies : kept.map Entry.body = fragments.map
      (languageTerm types terms equations (MatchAutomataExecution.rewriteRowTerm contexts fields)))
    (strategy : MeTTaILMatchAutomataExecution.Strategy)
    (rows : List Mettapedia.OSLF.MeTTaIL.GeneralPremise.ProviderRow)
    (providerAdmitted : RuleTraceExecution.providerFirstOrder rows = true)
    (admitted : ContextualRuleExecution.languageAdmitted
      (ModuleAlgebra.NativeAuthoring.assembleRaw name fragments) = true)
    (projected : ∀ rule ∈ (ModuleAlgebra.NativeAuthoring.assembleRaw name fragments).rewrites,
      ContextualRuleExecution.premisesTerm? rule.premises = some (fields rule))
    (depth : Nat) (subject : PatternPlan) (arguments : List Atom)
    (captured : arguments.map (applySubst caller) =
      [modeValue contract, encoded (.string name), entriesValue first, entriesValue second,
       encoded (ContextualRuleExecution.strategyTerm strategy), encoded (RelationPremiseExecution.providerRowsTerm rows),
       encoded (.natural depth), encoded (InferenceCettaWire.encodePattern subject.erase)]) :
    PureReturns program caller state (a "gslt:module:import-reducts" arguments) state
      (encoded (InferenceCettaWire.encodePatterns (MeTTaILMatchAutomataExecution.runAt strategy
        (Mettapedia.OSLF.MeTTaIL.ContextualStep.engineBasePremises (RelationPremiseExecution.providerEnv rows))
        (ModuleAlgebra.NativeAuthoring.assembleRaw name fragments) depth subject))) := by
  let callee := importEnvironment (modeValue contract) (encoded (.string name))
    (entriesValue first) (entriesValue second) (encoded (ContextualRuleExecution.strategyTerm strategy))
    (encoded (RelationPremiseExecution.providerRowsTerm rows)) (encoded (.natural depth))
    (encoded (InferenceCettaWire.encodePattern subject.erase))
  let selected := ("entries", entriesValue kept) :: callee
  let finished := ("fragments", rowValue Entry.body kept) :: selected
  have projection : rowValue Entry.body kept =
      rowValue (languageTerm types terms equations (MatchAutomataExecution.rewriteRowTerm contexts fields)) fragments := by
    simpa only [encodeList_map, Function.comp_def, id_eq] using
      congrArg (fun values => encoded (encodeList id values)) bodies
  apply import_call caller state _ _ _ _ _ _ _ _ _ arguments captured
  rw [import_shape]
  apply case_returns program callee selected state state state
    (a "gslt:module:join" [v "mode", v "left", v "right"])
    (a "Some" [entriesValue kept]) importContinue _ _ importCases (read_cases_encoded _) _ _ _
  · simpa only [joined, resultTerm, CettaWireAtom.encode, CettaWireAtom.encodeMany] using
      join_captured_returns contract first second callee state (v "mode") (v "left") (v "right")
        (by simp [callee, importEnvironment, applySubst, Subst.lookup])
  · simp [importCases, selected, callee, importEnvironment, SpaceSemantics.selectCase,
      SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]
  · unfold importContinue
    apply let_returns program selected finished state state state _ _ _ _ _
      (bodies_captured_returns kept selected state (v "entries")
        (by simp [selected, applySubst, Subst.lookup])) _ _
    · simp [finished, selected, callee, importEnvironment,
        SpaceSemantics.matchValue, matchAtom, Subst.lookup]
    · exact ModuleAssemblyExecution.reducts_captured_returns finished state name types terms equations
        contexts fields fragments strategy rows providerAdmitted admitted projected depth subject
        [v "name", v "fragments", v "strategy", v "rows", v "depth", v "subject"]
        (by simp [finished, selected, callee, importEnvironment, projection, applySubst, Subst.lookup])

theorem reducts_returns (contract : ImportContract) (first second kept : List WireEntry)
    (joined : contract.join? first second = some kept) (state : State) (name : String)
    (types : TypeDecl → Term) (terms : GrammarRule → Term) (equations : Equation → Term)
    (contexts fields : RewriteRule → Term) (fragments : List LanguageDef)
    (bodies : kept.map Entry.body = fragments.map
      (languageTerm types terms equations (MatchAutomataExecution.rewriteRowTerm contexts fields)))
    (strategy : MeTTaILMatchAutomataExecution.Strategy)
    (rows : List Mettapedia.OSLF.MeTTaIL.GeneralPremise.ProviderRow)
    (providerAdmitted : RuleTraceExecution.providerFirstOrder rows = true)
    (admitted : ContextualRuleExecution.languageAdmitted
      (ModuleAlgebra.NativeAuthoring.assembleRaw name fragments) = true)
    (projected : ∀ rule ∈ (ModuleAlgebra.NativeAuthoring.assembleRaw name fragments).rewrites,
      ContextualRuleExecution.premisesTerm? rule.premises = some (fields rule))
    (depth : Nat) (subject : PatternPlan) :
    PureReturns program [] state (encoded (queryTerm contract name first second strategy rows depth subject)) state
      (encoded (InferenceCettaWire.encodePatterns (MeTTaILMatchAutomataExecution.runAt strategy
        (Mettapedia.OSLF.MeTTaIL.ContextualStep.engineBasePremises (RelationPremiseExecution.providerEnv rows))
        (ModuleAlgebra.NativeAuthoring.assembleRaw name fragments) depth subject))) := by
  simpa only [queryTerm, CettaWireAtom.encode, CettaWireAtom.encodeMany] using
    reducts_captured_returns contract first second kept joined [] state name types terms equations
      contexts fields fragments bodies strategy rows providerAdmitted admitted projected depth subject _
      (by simp [applySubst, CettaWireAtom.encode])

theorem reducts_completed_iff (contract : ImportContract) (first second kept : List WireEntry)
    (joined : contract.join? first second = some kept) (state : State) (name : String)
    (types : TypeDecl → Term) (terms : GrammarRule → Term) (equations : Equation → Term)
    (contexts fields : RewriteRule → Term) (fragments : List LanguageDef)
    (bodies : kept.map Entry.body = fragments.map
      (languageTerm types terms equations (MatchAutomataExecution.rewriteRowTerm contexts fields)))
    (strategy : MeTTaILMatchAutomataExecution.Strategy)
    (rows : List Mettapedia.OSLF.MeTTaIL.GeneralPremise.ProviderRow)
    (providerAdmitted : RuleTraceExecution.providerFirstOrder rows = true)
    (admitted : ContextualRuleExecution.languageAdmitted
      (ModuleAlgebra.NativeAuthoring.assembleRaw name fragments) = true)
    (projected : ∀ rule ∈ (ModuleAlgebra.NativeAuthoring.assembleRaw name fragments).rewrites,
      ContextualRuleExecution.premisesTerm? rule.premises = some (fields rule))
    (depth : Nat) (subject : PatternPlan) (after : State) (answers input output : List Atom) :
    (∃ fuel, run program fuel
      {state, control := .evaluate [] (encoded (queryTerm contract name first second strategy rows depth subject))} =
        .complete after answers input output) ↔
      after = state ∧ answers = [encoded (InferenceCettaWire.encodePatterns
        (MeTTaILMatchAutomataExecution.runAt strategy
          (Mettapedia.OSLF.MeTTaIL.ContextualStep.engineBasePremises (RelationPremiseExecution.providerEnv rows))
          (ModuleAlgebra.NativeAuthoring.assembleRaw name fragments) depth subject))] ∧ input = [] ∧ output = [] :=
  pure_returns_completed_iff program [] state state _ _
    (reducts_returns contract first second kept joined state name types terms equations contexts fields
      fragments bodies strategy rows providerAdmitted admitted projected depth subject) after answers input output

theorem reducts_derivation_iff (contract : ImportContract) (first second kept : List WireEntry)
    (joined : contract.join? first second = some kept) (state : State) (name : String)
    (types : TypeDecl → Term) (terms : GrammarRule → Term) (equations : Equation → Term)
    (contexts fields : RewriteRule → Term) (fragments : List LanguageDef)
    (bodies : kept.map Entry.body = fragments.map
      (languageTerm types terms equations (MatchAutomataExecution.rewriteRowTerm contexts fields)))
    (strategy : MeTTaILMatchAutomataExecution.Strategy)
    (rows : List Mettapedia.OSLF.MeTTaIL.GeneralPremise.ProviderRow)
    (providerAdmitted : RuleTraceExecution.providerFirstOrder rows = true)
    (admitted : ContextualRuleExecution.languageAdmitted
      (ModuleAlgebra.NativeAuthoring.assembleRaw name fragments) = true)
    (projected : ∀ rule ∈ (ModuleAlgebra.NativeAuthoring.assembleRaw name fragments).rewrites,
      ContextualRuleExecution.premisesTerm? rule.premises = some (fields rule))
    (depth : Nat) (subject : PatternPlan) (after : State) (answers input output : List Atom) :
    DeclarativeSpec.Runs program
      {state, control := .evaluate [] (encoded (queryTerm contract name first second strategy rows depth subject))}
        (.complete after answers input output) ↔
      after = state ∧ answers = [encoded (InferenceCettaWire.encodePatterns
        (MeTTaILMatchAutomataExecution.runAt strategy
          (Mettapedia.OSLF.MeTTaIL.ContextualStep.engineBasePremises (RelationPremiseExecution.providerEnv rows))
          (ModuleAlgebra.NativeAuthoring.assembleRaw name fragments) depth subject))] ∧ input = [] ∧ output = [] :=
  pure_returns_derivation_iff program [] state state _ _
    (reducts_returns contract first second kept joined state name types terms equations contexts fields
      fragments bodies strategy rows providerAdmitted admitted projected depth subject) after answers input output

/-- A retained source import executes one frontier of its checked language. -/
def ObservesReduct (contract : ImportContract) (state : State) (name : String)
    (first second : List WireEntry) (strategy : MeTTaILMatchAutomataExecution.Strategy)
    (rows : List Mettapedia.OSLF.MeTTaIL.GeneralPremise.ProviderRow) (subject : PatternPlan) (target : Pattern) : Prop :=
  ∃ depth, ∃ reducts : List Pattern,
    DeclarativeSpec.Runs program
      {state, control := .evaluate [] (encoded (queryTerm contract name first second strategy rows depth subject))}
        (.complete state [encoded (InferenceCettaWire.encodePatterns reducts)] [] []) ∧ target ∈ reducts

/-- Checked origin-sensitive composition preserves and reflects the actual
GSLT step of the assembled language. Its structural join grants no rewrite
permission beyond the assembled source rules and their ordered premises. -/
theorem observes_reduct_iff_gslt_step (contract : ImportContract) (first second kept : List WireEntry)
    (joined : contract.join? first second = some kept) (state : State) (name : String)
    (types : TypeDecl → Term) (terms : GrammarRule → Term) (equations : Equation → Term)
    (contexts fields : RewriteRule → Term) (fragments : List LanguageDef)
    (bodies : kept.map Entry.body = fragments.map
      (languageTerm types terms equations (MatchAutomataExecution.rewriteRowTerm contexts fields)))
    (strategy : MeTTaILMatchAutomataExecution.Strategy)
    (rows : List Mettapedia.OSLF.MeTTaIL.GeneralPremise.ProviderRow)
    (providerAdmitted : RuleTraceExecution.providerFirstOrder rows = true)
    (admitted : ContextualRuleExecution.languageAdmitted
      (ModuleAlgebra.NativeAuthoring.assembleRaw name fragments) = true)
    (projected : ∀ rule ∈ (ModuleAlgebra.NativeAuthoring.assembleRaw name fragments).rewrites,
      ContextualRuleExecution.premisesTerm? rule.premises = some (fields rule))
    (subject : PatternPlan) (target : Pattern) :
    ObservesReduct contract state name first second strategy rows subject target ↔
      (Mettapedia.OSLF.Framework.TypeSynthesis.langGSLTUsing (RelationPremiseExecution.providerEnv rows)
        (ModuleAlgebra.NativeAuthoring.assembleRaw name fragments)).Step subject.erase target := by
  rw [← MeTTaILMatchAutomataExecution.runAt_iff_gslt_step strategy (RelationPremiseExecution.providerEnv rows)
    (ModuleAlgebra.NativeAuthoring.assembleRaw name fragments)
    ((ContextualRuleExecution.language_admitted_iff _).mp admitted).1 subject target]
  constructor
  · rintro ⟨depth, reducts, executed, member⟩
    have result := (reducts_derivation_iff contract first second kept joined state name types terms equations
      contexts fields fragments bodies strategy rows providerAdmitted admitted projected depth subject state _ [] []).mp executed
    have sameEncoded := List.cons.inj result.2.1 |>.1
    have same := InferenceCettaWire.encodePatterns_injective
      (CettaWireAtom.encode_injective _ _ sameEncoded)
    exact ⟨depth, by simpa only [same] using member⟩
  · rintro ⟨depth, member⟩
    exact ⟨depth, _, (reducts_derivation_iff contract first second kept joined state name types terms equations
      contexts fields fragments bodies strategy rows providerAdmitted admitted projected depth subject state _ [] []).mpr
        ⟨rfl, rfl, rfl, rfl⟩, member⟩

end Imports

#print axioms existing_captured_returns
#print axioms assemble_returns
#print axioms assemble_captured_returns
#print axioms assemble_completed_iff
#print axioms assemble_derivation_iff
#print axioms unsupported_fragment_returns_none
#print axioms languageTerm_rewriteProjection
#print axioms reducts_captured_returns
#print axioms reducts_returns
#print axioms reducts_completed_iff
#print axioms reducts_derivation_iff
#print axioms observes_reduct_iff_gslt_step
#print axioms Imports.compatible_returns
#print axioms Imports.resultTerm_injective
#print axioms Imports.compatible_captured_returns
#print axioms Imports.insert_returns
#print axioms Imports.insert_captured_returns
#print axioms Imports.fold_returns
#print axioms Imports.fold_captured_returns
#print axioms Imports.check_returns
#print axioms Imports.check_captured_returns
#print axioms Imports.check_completed_iff
#print axioms Imports.check_derivation_iff
#print axioms Imports.join_returns
#print axioms Imports.join_captured_returns
#print axioms Imports.join_completed_iff
#print axioms Imports.join_derivation_iff
#print axioms Imports.check_returns_some_iff
#print axioms Imports.check_accepts_iff
#print axioms Imports.join_returns_some_iff
#print axioms Imports.joined_declarations
#print axioms Imports.bodies_returns
#print axioms Imports.bodies_captured_returns
#print axioms Imports.refused_captured_returns
#print axioms Imports.reducts_captured_returns
#print axioms Imports.reducts_returns
#print axioms Imports.reducts_completed_iff
#print axioms Imports.reducts_derivation_iff
#print axioms Imports.observes_reduct_iff_gslt_step

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.ModuleAssemblyExecution
