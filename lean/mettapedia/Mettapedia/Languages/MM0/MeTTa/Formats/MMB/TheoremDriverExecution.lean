import Mettapedia.Languages.MM0.MeTTa.Formats.MMB.TheoremApplicationExecution

/-!
# Original binary theorem command: lookup, decoding and application

The unchanged authored command resolves the current logical theorem identity,
reads its physical declaration, decodes the original signature, consumes ordered
expression/proof entries and executes the original pointer matcher and recorder.
These laws retain arbitrary caller captures, saved chronology, duplicate children
and the optional heap save. Missing logical identities or physical rows produce
one explicit refusal after both original lookups execute.

Signature syntax, allocation/reference coherence and logical proof validity remain
separate obligations. Successful pop/match traces are original source-operation
evidence; chronological logical authority is still earned through the original
shared-proof service. General malformed-signature/pop refusals, conversion
continuations and whole-file declaration admission remain separate joins.
-/

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 1800000

namespace Mettapedia.Languages.MM0.MeTTa.MMBTheoremDriverExecution
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst matchAtom)
open Mettapedia.Languages.MeTTa.PeTTa
open Eval
open Effects (State boolean)
open Store (natural)
open ListAccess (listValue optionValue)
open MMBProofRunExecution (stateValue expressionValue provedValue)
open MMBTheoremMatchExecution (theoremValue Match)
open MMBTheoremApplicationExecution (childEntries resultValue)
open MMBRecordedWitnessAuthority (savedValue)
open Kernel (Preterm ProofWitness)
abbrev program := MMBTheoremApplicationExecution.program
private def sourceEquation : SpaceSemantics.Equation :=
  ((MMBExecution.binarySource.program.equations.filter (·.head == "mm0:mmb:proof-theorem")).head?).getD
    ⟨"",[],.symbol "None"⟩
private def field (body : Atom) (index : Nat) : Atom :=
  match body with | .expression values => values[index]?.getD (.symbol "None") | _ => .symbol "None"
private def casesOf (body : Atom) : SpaceSemantics.Cases :=
  match body with | .expression [_,_,.expression rows] => (readCases rows).getD [] | _ => []
private def firstBody (body : Atom) : Atom := ((casesOf body)[0]?.getD (.symbol "None",.symbol "None")).2
private def lookupCase := field sourceEquation.body 2
private def lookupCases := casesOf lookupCase
private def foundBody := firstBody lookupCase
private def signatureCase := field foundBody 3
private def signatureCases := casesOf signatureCase
private def signatureCall : Atom := .expression [.symbol "mm0:mmb:theorem-signature",.var "resolver",
  .expression [.symbol "MM0:MMBTables",.var "sorts",.var "terms",.var "theorems"],.var "tableEntry"]
private def declarationCall : Atom := .expression [.symbol "MM0:MMBTheorem",
  .expression [.symbol "MM0:L",.var "args"],.var "unify"]
private def lookupPairs : List Atom := [
  .expression [.var "found",.expression [.symbol "mm0:mmu:theorem",.var "resolver",.var "binary"]],
  .expression [.var "entry",.expression [.symbol "mm0:data-at",.var "theorems",.var "binary"]]]
private theorem source_unique : program.equations.filter (·.head == "mm0:mmb:proof-theorem") = [sourceEquation] := by decide +kernel
private theorem source_formals : sourceEquation.arguments =
  [.var "resolver",.expression [.symbol "MM0:MMBTables",.var "sorts",.var "terms",.var "theorems"],.var "context",
   .expression [.symbol "MM0:MMBPState",.var "next",.var "arity",.var "count",.expression [.symbol "MM0:L",.var "stack"],
     .var "heap",.var "dummies",.var "hyps",.var "saved"],.var "binary",.var "save"] := by decide
private theorem source_shape : sourceEquation.body = .expression [.symbol "let*",.expression lookupPairs,lookupCase] := by decide
private theorem lookup_shape : lookupCase = .expression [.symbol "case",.expression [.var "found",.var "entry"],
  .expression (lookupCases.map fun row => .expression [row.1,row.2])] := by decide
private theorem lookup_cases_shape : lookupCases = [
  (.expression [.expression [.symbol "Some",.var "id"],.expression [.symbol "Some",
    .expression [.symbol "MM0:MMBTheorem",.expression [.symbol "MM0:L",.var "args"],.var "unify"]]],foundBody),
  (.var "bad",.symbol "None")] := by decide
private theorem found_shape : foundBody = .expression [.symbol "let",.var "tableEntry",declarationCall,signatureCase] := by decide
private theorem signature_shape : signatureCase = .expression [.symbol "case",signatureCall,
  .expression (signatureCases.map fun row => .expression [row.1,row.2])] := by decide
private theorem signature_cases_shape : signatureCases = [
  (.expression [.symbol "Some",.expression [.symbol "MM0:L",.expression [.symbol "MM0:Theorem",.var "formal",
    .expression [.symbol "MM0:L",.var "premises"],.var "claim"]]],MMBTheoremApplicationExecution.applicationBody),
  (.var "bad",.symbol "None")] := by decide
private def bodyEnvironment (resolver context tableSorts : Atom) (tableTerms tableTheorems : List Atom)
    (next arity count : Nat) (stack heap dummies hypotheses saved : List Atom) (binary : Nat) (save : Bool) : Subst :=
  [("save",boolean save),("binary",natural binary),("saved",listValue saved),("hyps",listValue hypotheses),
   ("dummies",listValue dummies),("heap",listValue heap),("stack",.expression stack),
   ("count",natural count),("arity",natural arity),("next",natural next),("context",context),
   ("theorems",listValue tableTheorems),("terms",listValue tableTerms),("sorts",tableSorts),("resolver",resolver)]
private theorem source_clause (resolver context tableSorts : Atom) (tableTerms tableTheorems : List Atom)
    (next arity count : Nat) (stack heap dummies hypotheses saved : List Atom) (binary : Nat) (save : Bool) :
    clauses program "mm0:mmb:proof-theorem" [resolver,
      .expression [.symbol "MM0:MMBTables",tableSorts,listValue tableTerms,listValue tableTheorems],context,
      stateValue next arity count stack heap dummies hypotheses saved,natural binary,boolean save] =
    [.evaluate (bodyEnvironment resolver context tableSorts tableTerms tableTheorems next arity count
      stack heap dummies hypotheses saved binary save) sourceEquation.body] := by
  rw [clauses_use_only_the_named_equations,source_unique]
  simp [source_formals,bodyEnvironment,stateValue,listValue,SpaceSemantics.matchValue,SpaceSemantics.matchValue.matchValues,matchAtom,Subst.lookup]

private theorem lookup_prefix_returns (state : State) (published context tableSorts images : Atom)
    (sorts terms theorems : List MMUResolution.Binding) (nextSort nextTerm nextTheorem : Nat)
    (tableTerms tableTheorems : List Atom) (binary next arity count : Nat)
    (stack heap dummies hypotheses saved : List Atom) (save : Bool) (answer : Atom)
    (continuation : PureReturns program (("entry",optionValue (tableTheorems[binary]?))::
      ("found",optionValue (MMUResolution.lookup theorems (natural binary)))::
      bodyEnvironment (MMBTheoremSignatureExecution.resolverValue published sorts terms theorems nextSort nextTerm nextTheorem images)
        context tableSorts tableTerms tableTheorems next arity count stack heap dummies hypotheses saved binary save)
      state lookupCase state answer) :
    PureReturns program (bodyEnvironment (MMBTheoremSignatureExecution.resolverValue published sorts terms theorems
      nextSort nextTerm nextTheorem images) context tableSorts tableTerms tableTheorems next arity count
      stack heap dummies hypotheses saved binary save) state sourceEquation.body state answer := by
  let resolver := MMBTheoremSignatureExecution.resolverValue published sorts terms theorems nextSort nextTerm nextTheorem images
  let bindings := bodyEnvironment resolver context tableSorts tableTerms tableTheorems next arity count stack heap dummies hypotheses saved binary save
  let found := ("found",optionValue (MMUResolution.lookup theorems (natural binary)))::bindings
  let entered := ("entry",optionValue (tableTheorems[binary]?))::found
  rw [source_shape]
  apply let_star_returns program bindings state state lookupPairs lookupCase _ answer rfl
  apply let_returns program bindings found state state state (.var "found") _ _ _ answer
  · exact MMBTheoremExecution.theorem_lookup_returns bindings state published (MMUResolution.bindingsValue sorts)
      (MMUResolution.bindingsValue terms) theorems nextSort nextTerm nextTheorem images (natural binary) "resolver" "binary" rfl rfl
  · simp [SpaceSemantics.matchBinding,SpaceSemantics.matchValue,matchAtom,Subst.lookup,found,bindings,bodyEnvironment]
  · apply let_returns program found entered state state state (.var "entry") _ _ _ answer
    · exact MMBProofRunExecution.checker_returns (by decide +kernel)
        (ListAccess.data_at_list_returns found state tableTheorems binary "theorems" "binary" rfl rfl)
    · simp [SpaceSemantics.matchBinding,SpaceSemantics.matchValue,matchAtom,Subst.lookup,entered,found,bindings,bodyEnvironment]
    · exact continuation

private theorem declaration_returns (bindings : Subst) (state : State) (arguments codes : List Atom) (ending : Atom)
    (argsCaptured : applySubst bindings (.var "args") = .expression arguments)
    (unifyCaptured : applySubst bindings (.var "unify") = .expression [.symbol "MM0:MMBStream",listValue codes,ending]) :
    PureReturns program bindings state declarationCall state (theoremValue (listValue arguments) codes ending) := by
  apply data_call_returns program bindings state state "MM0:MMBTheorem" _ _ (by decide +kernel) _ (by decide)
  apply evaluated_argument_returns program bindings state state state .data (.symbol "MM0:MMBTheorem")
    (.symbol "MM0:MMBTheorem") _ _ [] 0 rfl (symbol_returns program bindings state "MM0:MMBTheorem")
  apply evaluated_argument_returns program bindings state state state .data (.expression [.symbol "MM0:L",.var "args"])
    (listValue arguments) _ _ _ 1 rfl
  · simpa only [argsCaptured,listValue] using unary_constructor_returns program bindings state "MM0:L" "args" (by decide +kernel) (by decide)
  · apply variable_arguments_return program bindings state state .data ["unify"] _ 2 _
    simpa only [unifyCaptured,theoremValue,listValue,List.map_cons,List.map_nil,List.append_nil,List.nil_append,List.cons_append,List.length_cons,List.length_nil,Nat.add_zero] using data_arguments_values_return program bindings state
      [.symbol "MM0:MMBTheorem",listValue arguments,applySubst bindings (.var "unify")] 3


private theorem signature_continuation_returns (state : State) (bindings : Subst)
    (context : Kernel.Context) (hypotheses : List Preterm) (claim answer : Atom)
    (freshFormal : Subst.lookup bindings "formal" = none)
    (freshPremises : Subst.lookup bindings "premises" = none)
    (freshClaim : Subst.lookup bindings "claim" = none)
    (signature : PureReturns program bindings state signatureCall state
      (optionValue (some (listValue [.symbol "MM0:Theorem",Data.context context,
        listValue (hypotheses.map Data.preterm),claim]))))
    (continuation : PureReturns program
      (("claim",claim)::("premises",.expression (hypotheses.map Data.preterm))::("formal",Data.context context)::bindings)
      state MMBTheoremApplicationExecution.applicationBody state answer) :
    PureReturns program bindings state signatureCase state answer := by
  rw [signature_shape]
  apply case_returns program bindings
    (("claim",claim)::("premises",.expression (hypotheses.map Data.preterm))::("formal",Data.context context)::bindings)
    state state state signatureCall _ MMBTheoremApplicationExecution.applicationBody _ _
    signatureCases (read_cases_encoded signatureCases) signature
  · simp only [Subst.lookup] at freshFormal freshPremises freshClaim
    simp [signature_cases_shape,optionValue,listValue,SpaceSemantics.selectCase,SpaceSemantics.matchValue,
      SpaceSemantics.matchValue.matchValues,matchAtom,Subst.lookup,freshFormal,freshPremises,freshClaim]
  · exact continuation

private theorem body_decoded_returns (state : State) (published callerContext images tableSorts : Atom)
    (sorts terms theorems : List MMUResolution.Binding) (nextSort nextTerm nextTheorem : Nat)
    (tableTerms tableTheorems : List Atom) (binary next arity allocation identifier : Nat)
    (base : List Preterm) (recorded : List Sharing.Entry) (parameters : List Preterm)
    (children : List (ProofWitness × Atom)) (remaining heap dummies hypotheses arguments : List Atom)
    (claim : Preterm) (node : Atom) (save : Bool) (beforeArguments beforeChildren : List Atom)
    (declarationArguments : List Formats.MMB.ExprType) (commands unread : List Formats.MMB.UnifyCmd)
    (codes : List Atom) (ending : Atom) (declarationContext : Kernel.Context)
    (declarationConclusion : Preterm) (decodedState : Formats.MMB.Statements.Decoding)
    (declarationHypotheses : List Preterm) (result : Option (List Atom))
    (resolved : MMUResolution.lookup theorems (natural binary) = some (natural identifier))
    (declared : tableTheorems[binary]? = some (theoremValue
      (listValue (MMBTheoremSignatureExecution.typeValues (MMBTheoremSignatureExecution.canonicalTypes declarationArguments))) codes ending))
    (encoded : List.Forall₂ MMBTheoremSignatureExecution.CommandImage commands codes)
    (numerical : MMUResolution.NumericalMap sorts)
    (valid : MMBTheoremSignatureExecution.PrefixValid declarationArguments)
    (contextChecked : Kernel.Context.relocateSorts? (MMBTheoremSignatureExecution.resolvedIds sorts)
      (Formats.MMB.Statements.context declarationArguments) = some declarationContext)
    (decoded : Formats.MMB.Statements.decodeExpr (MMBTheoremSignatureExecution.tableArity tableTerms) declarationArguments.length
      (2*commands.length+2) (Formats.MMB.Statements.initial declarationArguments.length) commands
      (MMBTheoremSignatureExecution.resolvedIds terms) (MMBTheoremSignatureExecution.resolvedIds sorts) =
      some (declarationConclusion,decodedState,unread))
    (noDummies : decodedState.dummies = [])
    (decodedHypotheses : Formats.MMB.Statements.decodeHyps (MMBTheoremSignatureExecution.tableArity tableTerms) declarationArguments.length
      (2*commands.length+2) decodedState unread (MMBTheoremSignatureExecution.resolvedIds terms)
      (MMBTheoremSignatureExecution.resolvedIds sorts) = some declarationHypotheses)
    (argumentsPopped : MMBTheoremCommandExecution.Pops .expressions
      (MMBTheoremSignatureExecution.typeValues (MMBTheoremSignatureExecution.canonicalTypes declarationArguments)).length
      beforeArguments (some (arguments,beforeChildren)))
    (childrenPopped : MMBTheoremCommandExecution.Pops .proofs declarationHypotheses.length
      beforeChildren (some (childEntries children,remaining)))
    (claims : MMBProofRunExecution.ExpressionClaims arguments (parameters.map Data.preterm))
    (trace : Match callerContext
      (MMBTheoremSignatureExecution.resolverValue published sorts terms theorems nextSort nextTerm nextTheorem images)
      arguments codes (children.map Prod.snd) (expressionValue allocation (Data.preterm claim) node) result) :
    PureReturns program (bodyEnvironment
      (MMBTheoremSignatureExecution.resolverValue published sorts terms theorems nextSort nextTerm nextTheorem images)
      callerContext tableSorts tableTerms tableTheorems next arity base.length
      (expressionValue allocation (Data.preterm claim) node::beforeArguments) heap dummies hypotheses (savedValue recorded) binary save)
      state sourceEquation.body state
      (if result.isSome then resultValue next arity allocation identifier base recorded parameters (children.map Prod.fst)
        remaining heap dummies hypotheses claim node save else .symbol "None") := by
  let resolver := MMBTheoremSignatureExecution.resolverValue published sorts terms theorems nextSort nextTerm nextTheorem images
  let formalArguments := MMBTheoremSignatureExecution.typeValues (MMBTheoremSignatureExecution.canonicalTypes declarationArguments)
  let declaration := theoremValue (listValue formalArguments) codes ending
  let bindings := bodyEnvironment resolver callerContext tableSorts tableTerms tableTheorems next arity base.length
    (expressionValue allocation (Data.preterm claim) node::beforeArguments) heap dummies hypotheses (savedValue recorded) binary save
  let entered := ("entry",optionValue (some declaration))::("found",optionValue (some (natural identifier)))::bindings
  let selected := ("unify",.expression [.symbol "MM0:MMBStream",listValue codes,ending])::
    ("args",.expression formalArguments)::("id",natural identifier)::entered
  let prepared := ("tableEntry",declaration)::selected
  let signatureBound := ("claim",Data.preterm declarationConclusion)::("premises",.expression (declarationHypotheses.map Data.preterm))::
    ("formal",Data.context declarationContext)::prepared
  apply lookup_prefix_returns state published callerContext tableSorts images sorts terms theorems nextSort nextTerm nextTheorem
    tableTerms tableTheorems binary next arity base.length _ heap dummies hypotheses (savedValue recorded) save _
  change PureReturns program (("entry",optionValue (tableTheorems[binary]?))::
    ("found",optionValue (MMUResolution.lookup theorems (natural binary)))::bindings) state lookupCase state _
  rw [resolved,declared]
  rw [lookup_shape]
  apply case_returns program entered selected state state state (.expression [.var "found",.var "entry"])
    (.expression [optionValue (some (natural identifier)),optionValue (some declaration)]) foundBody _ _
    lookupCases (read_cases_encoded lookupCases)
  · simpa [entered,bindings,bodyEnvironment,applySubst,Subst.lookup] using tuple_variables_return program entered state ["found","entry"]
  · simp [lookup_cases_shape,entered,bindings,bodyEnvironment,declaration,theoremValue,listValue,optionValue,selected,
      SpaceSemantics.selectCase,SpaceSemantics.matchValue,SpaceSemantics.matchValue.matchValues,matchAtom,Subst.lookup]
  · rw [found_shape]
    apply let_returns program selected prepared state state state (.var "tableEntry") declarationCall signatureCase declaration _
    · exact declaration_returns selected state formalArguments codes ending rfl rfl
    · simp [SpaceSemantics.matchBinding,SpaceSemantics.matchValue,matchAtom,Subst.lookup,prepared,selected,entered,bindings,bodyEnvironment]
    · apply signature_continuation_returns state prepared declarationContext declarationHypotheses (Data.preterm declarationConclusion) _ rfl rfl rfl
      · let prior : Subst := [("r",resolver),("t",MMBTheoremSignatureExecution.tablesValue tableSorts (listValue tableTerms) (listValue tableTheorems)),("d",declaration)]
        have signature := MMBTheoremSignatureExecution.theorem_signature_decoded_returns prior state published sorts terms theorems
          nextSort nextTerm nextTheorem images tableSorts (listValue tableTheorems) tableTerms declarationArguments commands unread codes ending
          declarationContext declarationConclusion decodedState declarationHypotheses encoded numerical valid contextChecked decoded noDummies decodedHypotheses
          "r" "t" "d" rfl rfl rfl
        apply captured_call_returns program prior prepared state state "mm0:mmb:theorem-signature"
          [.var "r",.var "t",.var "d"] [.var "resolver",.expression [.symbol "MM0:MMBTables",.var "sorts",.var "terms",.var "theorems"],.var "tableEntry"] _
          (by decide +kernel) (by decide) _ _ _ signature
        · intro offset argument found
          have member := List.mem_of_getElem? found
          simp only [List.mem_cons,List.not_mem_nil,or_false] at member
          rcases member with rfl|rfl|rfl <;> exact Or.inr rfl
        · intro offset argument found
          have member := List.mem_of_getElem? found
          simp only [List.mem_cons,List.not_mem_nil,or_false] at member
          rcases member with rfl|rfl|rfl
          · exact Or.inr rfl
          · have bound := (getElem?_eq_some_iff.mp found).choose
            have index : offset = 0 ∨ offset = 1 ∨ offset = 2 := by simp only [List.length_cons,List.length_nil] at bound; omega
            rcases index with rfl|rfl|rfl <;> simp at found
            exact Or.inl (by decide +kernel)
          · exact Or.inr rfl
        · simp [prior,prepared,selected,entered,bindings,bodyEnvironment,applySubst,applySubst.applySubstList,Subst.lookup,MMBTheoremSignatureExecution.tablesValue]
      · change PureReturns program signatureBound state MMBTheoremApplicationExecution.applicationBody state _
        apply MMBTheoremApplicationExecution.captured_returns state signatureBound next arity allocation identifier base recorded parameters children
          remaining heap dummies hypotheses arguments claim node save resolver callerContext (listValue formalArguments) ending codes result
          formalArguments (declarationHypotheses.map Data.preterm) beforeArguments beforeChildren
        all_goals try first | assumption | rfl
        · simpa only [List.length_map] using childrenPopped
        · intro name member
          simp only [List.mem_cons,List.mem_nil_iff,or_false] at member
          rcases member with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
            simp [signatureBound,prepared,selected,entered,bindings,bodyEnvironment,Subst.lookup]

/-- The complete original theorem command executes current logical lookup,
physical declaration selection, actual signature decoding, ordered stack pops,
source pointer matching and chronological recording. Incoming proof witnesses
remain subject to original chronological validation. -/
theorem returns (bindings : Subst) (state : State) (published callerContext images tableSorts : Atom)
    (sorts terms theorems : List MMUResolution.Binding) (nextSort nextTerm nextTheorem : Nat)
    (tableTerms tableTheorems : List Atom) (binary next arity allocation identifier : Nat)
    (base : List Preterm) (recorded : List Sharing.Entry) (parameters : List Preterm)
    (children : List (ProofWitness × Atom)) (remaining heap dummies hypotheses arguments : List Atom)
    (claim : Preterm) (node : Atom) (save : Bool) (beforeArguments beforeChildren : List Atom)
    (declarationArguments : List Formats.MMB.ExprType) (commands unread : List Formats.MMB.UnifyCmd)
    (codes : List Atom) (ending : Atom) (declarationContext : Kernel.Context)
    (declarationConclusion : Preterm) (decodedState : Formats.MMB.Statements.Decoding)
    (declarationHypotheses : List Preterm) (result : Option (List Atom))
    (resolved : MMUResolution.lookup theorems (natural binary) = some (natural identifier))
    (declared : tableTheorems[binary]? = some (theoremValue
      (listValue (MMBTheoremSignatureExecution.typeValues (MMBTheoremSignatureExecution.canonicalTypes declarationArguments))) codes ending))
    (encoded : List.Forall₂ MMBTheoremSignatureExecution.CommandImage commands codes)
    (numerical : MMUResolution.NumericalMap sorts)
    (valid : MMBTheoremSignatureExecution.PrefixValid declarationArguments)
    (contextChecked : Kernel.Context.relocateSorts? (MMBTheoremSignatureExecution.resolvedIds sorts)
      (Formats.MMB.Statements.context declarationArguments) = some declarationContext)
    (decoded : Formats.MMB.Statements.decodeExpr (MMBTheoremSignatureExecution.tableArity tableTerms) declarationArguments.length
      (2*commands.length+2) (Formats.MMB.Statements.initial declarationArguments.length) commands
      (MMBTheoremSignatureExecution.resolvedIds terms) (MMBTheoremSignatureExecution.resolvedIds sorts) =
      some (declarationConclusion,decodedState,unread))
    (noDummies : decodedState.dummies = [])
    (decodedHypotheses : Formats.MMB.Statements.decodeHyps (MMBTheoremSignatureExecution.tableArity tableTerms) declarationArguments.length
      (2*commands.length+2) decodedState unread (MMBTheoremSignatureExecution.resolvedIds terms)
      (MMBTheoremSignatureExecution.resolvedIds sorts) = some declarationHypotheses)
    (argumentsPopped : MMBTheoremCommandExecution.Pops .expressions
      (MMBTheoremSignatureExecution.typeValues (MMBTheoremSignatureExecution.canonicalTypes declarationArguments)).length
      beforeArguments (some (arguments,beforeChildren)))
    (childrenPopped : MMBTheoremCommandExecution.Pops .proofs declarationHypotheses.length
      beforeChildren (some (childEntries children,remaining)))
    (claims : MMBProofRunExecution.ExpressionClaims arguments (parameters.map Data.preterm))
    (trace : Match callerContext
      (MMBTheoremSignatureExecution.resolverValue published sorts terms theorems nextSort nextTerm nextTheorem images)
      arguments codes (children.map Prod.snd) (expressionValue allocation (Data.preterm claim) node) result)
    (resolverName tablesName contextName stateName binaryName saveName : String)
    (resolverCaptured : applySubst bindings (.var resolverName) =
      MMBTheoremSignatureExecution.resolverValue published sorts terms theorems nextSort nextTerm nextTheorem images)
    (tablesCaptured : applySubst bindings (.var tablesName) =
      .expression [.symbol "MM0:MMBTables",tableSorts,listValue tableTerms,listValue tableTheorems])
    (contextCaptured : applySubst bindings (.var contextName) = callerContext)
    (stateCaptured : applySubst bindings (.var stateName) = stateValue next arity base.length
      (expressionValue allocation (Data.preterm claim) node::beforeArguments) heap dummies hypotheses (savedValue recorded))
    (binaryCaptured : applySubst bindings (.var binaryName) = natural binary)
    (saveCaptured : applySubst bindings (.var saveName) = boolean save) :
    PureReturns program bindings state (.expression [.symbol "mm0:mmb:proof-theorem",.var resolverName,.var tablesName,
      .var contextName,.var stateName,.var binaryName,.var saveName]) state
      (if result.isSome then resultValue next arity allocation identifier base recorded parameters (children.map Prod.fst)
        remaining heap dummies hypotheses claim node save else .symbol "None") := by
  apply authored_variable_call_returns program bindings
    (bodyEnvironment (MMBTheoremSignatureExecution.resolverValue published sorts terms theorems nextSort nextTerm nextTheorem images)
      callerContext tableSorts tableTerms tableTheorems next arity base.length
      (expressionValue allocation (Data.preterm claim) node::beforeArguments) heap dummies hypotheses (savedValue recorded) binary save)
    state state "mm0:mmb:proof-theorem" [resolverName,tablesName,contextName,stateName,binaryName,saveName]
    sourceEquation.body _ (by decide +kernel) (by decide +kernel) (by decide +kernel) _ _ (by decide)
  · simpa [resolverCaptured,tablesCaptured,contextCaptured,stateCaptured,binaryCaptured,saveCaptured] using
      source_clause (MMBTheoremSignatureExecution.resolverValue published sorts terms theorems nextSort nextTerm nextTheorem images)
        callerContext tableSorts tableTerms tableTheorems next arity base.length
        (expressionValue allocation (Data.preterm claim) node::beforeArguments) heap dummies hypotheses (savedValue recorded) binary save
  · exact body_decoded_returns state published callerContext images tableSorts sorts terms theorems nextSort nextTerm nextTheorem
      tableTerms tableTheorems binary next arity allocation identifier base recorded parameters children remaining heap dummies hypotheses arguments
      claim node save beforeArguments beforeChildren declarationArguments commands unread codes ending declarationContext declarationConclusion decodedState
      declarationHypotheses result resolved declared encoded numerical valid contextChecked decoded noDummies decodedHypotheses argumentsPopped childrenPopped claims trace

theorem completed_iff (bindings : Subst) (state after : State) (answers inputs outputs : List Atom) (published callerContext images tableSorts : Atom)
    (sorts terms theorems : List MMUResolution.Binding) (nextSort nextTerm nextTheorem : Nat)
    (tableTerms tableTheorems : List Atom) (binary next arity allocation identifier : Nat)
    (base : List Preterm) (recorded : List Sharing.Entry) (parameters : List Preterm)
    (children : List (ProofWitness × Atom)) (remaining heap dummies hypotheses arguments : List Atom)
    (claim : Preterm) (node : Atom) (save : Bool) (beforeArguments beforeChildren : List Atom)
    (declarationArguments : List Formats.MMB.ExprType) (commands unread : List Formats.MMB.UnifyCmd)
    (codes : List Atom) (ending : Atom) (declarationContext : Kernel.Context)
    (declarationConclusion : Preterm) (decodedState : Formats.MMB.Statements.Decoding)
    (declarationHypotheses : List Preterm) (result : Option (List Atom))
    (resolved : MMUResolution.lookup theorems (natural binary) = some (natural identifier))
    (declared : tableTheorems[binary]? = some (theoremValue
      (listValue (MMBTheoremSignatureExecution.typeValues (MMBTheoremSignatureExecution.canonicalTypes declarationArguments))) codes ending))
    (encoded : List.Forall₂ MMBTheoremSignatureExecution.CommandImage commands codes)
    (numerical : MMUResolution.NumericalMap sorts)
    (valid : MMBTheoremSignatureExecution.PrefixValid declarationArguments)
    (contextChecked : Kernel.Context.relocateSorts? (MMBTheoremSignatureExecution.resolvedIds sorts)
      (Formats.MMB.Statements.context declarationArguments) = some declarationContext)
    (decoded : Formats.MMB.Statements.decodeExpr (MMBTheoremSignatureExecution.tableArity tableTerms) declarationArguments.length
      (2*commands.length+2) (Formats.MMB.Statements.initial declarationArguments.length) commands
      (MMBTheoremSignatureExecution.resolvedIds terms) (MMBTheoremSignatureExecution.resolvedIds sorts) =
      some (declarationConclusion,decodedState,unread))
    (noDummies : decodedState.dummies = [])
    (decodedHypotheses : Formats.MMB.Statements.decodeHyps (MMBTheoremSignatureExecution.tableArity tableTerms) declarationArguments.length
      (2*commands.length+2) decodedState unread (MMBTheoremSignatureExecution.resolvedIds terms)
      (MMBTheoremSignatureExecution.resolvedIds sorts) = some declarationHypotheses)
    (argumentsPopped : MMBTheoremCommandExecution.Pops .expressions
      (MMBTheoremSignatureExecution.typeValues (MMBTheoremSignatureExecution.canonicalTypes declarationArguments)).length
      beforeArguments (some (arguments,beforeChildren)))
    (childrenPopped : MMBTheoremCommandExecution.Pops .proofs declarationHypotheses.length
      beforeChildren (some (childEntries children,remaining)))
    (claims : MMBProofRunExecution.ExpressionClaims arguments (parameters.map Data.preterm))
    (trace : Match callerContext
      (MMBTheoremSignatureExecution.resolverValue published sorts terms theorems nextSort nextTerm nextTheorem images)
      arguments codes (children.map Prod.snd) (expressionValue allocation (Data.preterm claim) node) result)
    (resolverName tablesName contextName stateName binaryName saveName : String)
    (resolverCaptured : applySubst bindings (.var resolverName) =
      MMBTheoremSignatureExecution.resolverValue published sorts terms theorems nextSort nextTerm nextTheorem images)
    (tablesCaptured : applySubst bindings (.var tablesName) =
      .expression [.symbol "MM0:MMBTables",tableSorts,listValue tableTerms,listValue tableTheorems])
    (contextCaptured : applySubst bindings (.var contextName) = callerContext)
    (stateCaptured : applySubst bindings (.var stateName) = stateValue next arity base.length
      (expressionValue allocation (Data.preterm claim) node::beforeArguments) heap dummies hypotheses (savedValue recorded))
    (binaryCaptured : applySubst bindings (.var binaryName) = natural binary)
    (saveCaptured : applySubst bindings (.var saveName) = boolean save) :
    (∃ fuel, Eval.run program fuel {state,control := .evaluate bindings (.expression [.symbol "mm0:mmb:proof-theorem",.var resolverName,.var tablesName,.var contextName,
        .var stateName,.var binaryName,.var saveName])} = .complete after answers inputs outputs) ↔
    after = state ∧ answers = [if result.isSome then resultValue next arity allocation identifier base recorded parameters
      (children.map Prod.fst) remaining heap dummies hypotheses claim node save else .symbol "None"] ∧ inputs = [] ∧ outputs = [] := by
  have returned := returns bindings state published callerContext images tableSorts sorts terms theorems nextSort nextTerm nextTheorem
    tableTerms tableTheorems binary next arity allocation identifier base recorded parameters children remaining heap dummies hypotheses arguments
    claim node save beforeArguments beforeChildren declarationArguments commands unread codes ending declarationContext declarationConclusion decodedState
    declarationHypotheses result resolved declared encoded numerical valid contextChecked decoded noDummies decodedHypotheses argumentsPopped childrenPopped claims trace
    resolverName tablesName contextName stateName binaryName saveName resolverCaptured tablesCaptured contextCaptured stateCaptured binaryCaptured saveCaptured
  exact pure_returns_completed_iff program bindings state state _ _ returned after answers inputs outputs

private theorem lookup_refused_body_returns (state : State) (published callerContext images tableSorts : Atom)
    (sorts terms theorems : List MMUResolution.Binding) (nextSort nextTerm nextTheorem : Nat)
    (tableTerms tableTheorems : List Atom) (binary next arity count : Nat)
    (stack heap dummies hypotheses saved : List Atom) (save : Bool)
    (failure : MMUResolution.lookup theorems (natural binary) = none ∨ tableTheorems[binary]? = none) :
    PureReturns program (bodyEnvironment (MMBTheoremSignatureExecution.resolverValue published sorts terms theorems
      nextSort nextTerm nextTheorem images) callerContext tableSorts tableTerms tableTheorems next arity count
      stack heap dummies hypotheses saved binary save) state sourceEquation.body state (.symbol "None") := by
  let resolver := MMBTheoremSignatureExecution.resolverValue published sorts terms theorems nextSort nextTerm nextTheorem images
  let bindings := bodyEnvironment resolver callerContext tableSorts tableTerms tableTheorems next arity count stack heap dummies hypotheses saved binary save
  let entered := ("entry",optionValue (tableTheorems[binary]?))::("found",optionValue (MMUResolution.lookup theorems (natural binary)))::bindings
  let denied := ("bad",.expression [optionValue (MMUResolution.lookup theorems (natural binary)),optionValue (tableTheorems[binary]?)])::entered
  apply lookup_prefix_returns state published callerContext tableSorts images sorts terms theorems nextSort nextTerm nextTheorem
    tableTerms tableTheorems binary next arity count stack heap dummies hypotheses saved save (.symbol "None")
  rw [lookup_shape]
  apply case_returns program entered denied state state state (.expression [.var "found",.var "entry"])
    (.expression [optionValue (MMUResolution.lookup theorems (natural binary)),optionValue (tableTheorems[binary]?)])
    (.symbol "None") _ _ lookupCases (read_cases_encoded lookupCases)
  · simpa [entered,bindings,bodyEnvironment,applySubst,Subst.lookup] using tuple_variables_return program entered state ["found","entry"]
  · rcases failure with absent | absent
    · simp [lookup_cases_shape,SpaceSemantics.selectCase,SpaceSemantics.matchValue,
        SpaceSemantics.matchValue.matchValues,matchAtom,Subst.lookup,optionValue,absent,denied,entered,bindings,bodyEnvironment]
    · cases resolved : MMUResolution.lookup theorems (natural binary) with
      | none => simp [lookup_cases_shape,SpaceSemantics.selectCase,SpaceSemantics.matchValue,
          SpaceSemantics.matchValue.matchValues,matchAtom,Subst.lookup,optionValue,absent,resolved,denied,entered,bindings,bodyEnvironment]
      | some identifier => simp [lookup_cases_shape,SpaceSemantics.selectCase,SpaceSemantics.matchValue,
          SpaceSemantics.matchValue.matchValues,matchAtom,Subst.lookup,optionValue,absent,resolved,denied,entered,bindings,bodyEnvironment]
  · exact symbol_returns program denied state "None"

/-- An unavailable current logical ID or physical declaration yields the
original explicit None answer after both original lookups have executed. -/
theorem lookup_refused_returns (bindings : Subst) (state : State) (published callerContext images tableSorts : Atom)
    (sorts terms theorems : List MMUResolution.Binding) (nextSort nextTerm nextTheorem : Nat)
    (tableTerms tableTheorems : List Atom) (binary next arity count : Nat)
    (stack heap dummies hypotheses saved : List Atom) (save : Bool)
    (failure : MMUResolution.lookup theorems (natural binary) = none ∨ tableTheorems[binary]? = none)
    (resolverName tablesName contextName stateName binaryName saveName : String)
    (resolverCaptured : applySubst bindings (.var resolverName) =
      MMBTheoremSignatureExecution.resolverValue published sorts terms theorems nextSort nextTerm nextTheorem images)
    (tablesCaptured : applySubst bindings (.var tablesName) =
      .expression [.symbol "MM0:MMBTables",tableSorts,listValue tableTerms,listValue tableTheorems])
    (contextCaptured : applySubst bindings (.var contextName) = callerContext)
    (stateCaptured : applySubst bindings (.var stateName) = stateValue next arity count stack heap dummies hypotheses saved)
    (binaryCaptured : applySubst bindings (.var binaryName) = natural binary)
    (saveCaptured : applySubst bindings (.var saveName) = boolean save) :
    PureReturns program bindings state (.expression [.symbol "mm0:mmb:proof-theorem",.var resolverName,.var tablesName,
      .var contextName,.var stateName,.var binaryName,.var saveName]) state (.symbol "None") := by
  apply authored_variable_call_returns program bindings
    (bodyEnvironment (MMBTheoremSignatureExecution.resolverValue published sorts terms theorems nextSort nextTerm nextTheorem images)
      callerContext tableSorts tableTerms tableTheorems next arity count stack heap dummies hypotheses saved binary save)
    state state "mm0:mmb:proof-theorem" [resolverName,tablesName,contextName,stateName,binaryName,saveName]
    sourceEquation.body _ (by decide +kernel) (by decide +kernel) (by decide +kernel) _ _ (by decide)
  · simpa [resolverCaptured,tablesCaptured,contextCaptured,stateCaptured,binaryCaptured,saveCaptured] using
      source_clause (MMBTheoremSignatureExecution.resolverValue published sorts terms theorems nextSort nextTerm nextTheorem images)
        callerContext tableSorts tableTerms tableTheorems next arity count stack heap dummies hypotheses saved binary save
  · exact lookup_refused_body_returns state published callerContext images tableSorts sorts terms theorems nextSort nextTerm nextTheorem
      tableTerms tableTheorems binary next arity count stack heap dummies hypotheses saved save failure


/-- Successful original pops make the retained suffix an actual sublist of
the incoming source stack. No projected list is supplied independently. -/
private theorem remaining_member {argumentCount proofCount : Nat}
    {beforeArguments arguments beforeChildren children remaining : List Atom}
    (argumentsPopped : MMBTheoremCommandExecution.Pops .expressions argumentCount beforeArguments (some (arguments,beforeChildren)))
    (childrenPopped : MMBTheoremCommandExecution.Pops .proofs proofCount beforeChildren (some (children,remaining)))
    (entry : Atom) (member : entry ∈ remaining) : entry ∈ beforeArguments := by
  rw [argumentsPopped.ordered.2,childrenPopped.ordered.2]
  exact List.mem_append_right _ (List.mem_append_right _ member)

/-- The source's recorded result preserves both expression-allocation
coherence and chronological proof-reference claims. Neither property states
that the stored initializer has passed the logical checker. -/
theorem record_authority (history : List Atom) (base : List Preterm) (recorded : List Sharing.Entry)
    (allocation identifier argumentCount proofCount : Nat) (parameters : List Preterm) (children : List ProofWitness)
    (claim : Preterm) (node : Atom) (save : Bool)
    (beforeArguments arguments beforeChildren poppedChildren remaining heap hypotheses : List Atom)
    (argumentsPopped : MMBTheoremCommandExecution.Pops .expressions argumentCount beforeArguments (some (arguments,beforeChildren)))
    (childrenPopped : MMBTheoremCommandExecution.Pops .proofs proofCount beforeChildren (some (poppedChildren,remaining)))
    (coherent : MMBAllocationExecution.StateCoherent history
      (expressionValue allocation (Data.preterm claim) node::beforeArguments) heap hypotheses)
    (stackReferences : MMBRecordedWitnessAuthority.ProvedReferences base recorded beforeArguments)
    (heapReferences : MMBRecordedWitnessAuthority.ProvedReferences base recorded heap) :
    let entry : Sharing.Entry := ⟨some claim,.theoremApp identifier parameters children⟩
    let root := provedValue (Proof.witnessValue (.hyp (base.length+recorded.length)))
      (expressionValue allocation (Data.preterm claim) node)
    MMBAllocationExecution.StateCoherent history (root::remaining) (if save then heap++[root] else heap) hypotheses ∧
      MMBRecordedWitnessAuthority.ProvedReferences base (recorded++[entry]) (root::remaining) ∧
      MMBRecordedWitnessAuthority.ProvedReferences base (recorded++[entry]) (if save then heap++[root] else heap) := by
  let entry : Sharing.Entry := ⟨some claim,.theoremApp identifier parameters children⟩
  let root := provedValue (Proof.witnessValue (.hyp (base.length+recorded.length)))
    (expressionValue allocation (Data.preterm claim) node)
  have target : MMBAllocationExecution.AuthorizedExpression history (expressionValue allocation (Data.preterm claim) node) :=
    MMBAllocationExecution.AuthorizedEntry.expression_authorized (coherent.2.1 _ (by simp))
  have rootAuthorized : MMBAllocationExecution.AuthorizedEntry history root := .proved _ _ target
  have remainingReferences : MMBRecordedWitnessAuthority.ProvedReferences base recorded remaining := by
    intro witness target member
    exact stackReferences witness target (remaining_member argumentsPopped childrenPopped _ member)
  have rootReference := MMBRecordedWitnessAuthority.ReferenceClaim.record base recorded allocation claim node
    (.theoremApp identifier parameters children)
  have stackCoherent : MMBAllocationExecution.StateCoherent history (root::remaining) heap hypotheses := by
    refine ⟨coherent.1,?_,coherent.2.2.1,coherent.2.2.2⟩
    intro value member
    rcases List.mem_cons.mp member with rfl|member
    · exact rootAuthorized
    · exact coherent.2.1 value (List.mem_cons_of_mem _ (remaining_member argumentsPopped childrenPopped _ member))
  refine ⟨?_,remainingReferences.append.prepend rootReference,?_⟩
  · cases save with
    | false => exact stackCoherent
    | true => exact stackCoherent.save
  · cases save with
    | false => exact heapReferences.append
    | true =>
        intro witness target member
        rcases List.mem_append.mp member with old|fresh
        · exact (heapReferences witness target old).append
        · have fields : witness = Proof.witnessValue (.hyp (base.length+recorded.length)) ∧
              target = expressionValue allocation (Data.preterm claim) node := by
            simpa only [List.mem_singleton,root,provedValue,Atom.expression.injEq,List.cons.injEq,and_true,true_and] using fresh
          simpa only [fields.1,fields.2] using rootReference

end Mettapedia.Languages.MM0.MeTTa.MMBTheoremDriverExecution
