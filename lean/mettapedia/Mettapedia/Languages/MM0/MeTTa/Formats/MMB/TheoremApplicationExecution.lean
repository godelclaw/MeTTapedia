import Mettapedia.Languages.MM0.MeTTa.Formats.MMB.TheoremMatchExecution
import Mettapedia.Languages.MM0.MeTTa.Formats.MMB.RecordedWitnessAuthority

/-!
# Original binary theorem-application continuation

These laws execute the unchanged quoted continuation after signature decoding:
target selection, code-derived expression and proof pops, original ordered field
projections, assertion matching, chronological recording and optional heap save.
They retain pointer identities, complete initializer data, duplicate children,
caller captures and explicit refusal observations.

Recording is distinct from validating a proof. Logical authority is obtained by
submitting every saved initializer to the original chronological service. The
outer declaration lookup/signature composition, conversion continuation and
whole proof-run admission remain separate joins.
-/

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 1800000

namespace Mettapedia.Languages.MM0.MeTTa.MMBTheoremApplicationExecution
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst matchAtom)
open Mettapedia.Languages.MeTTa.PeTTa
open Eval
open Effects (State boolean)
open Store (natural)
open ListAccess (listValue optionValue)
open MMBProofRunExecution (stateValue expressionValue provedValue)
open MMBTheoremMatchExecution (theoremValue Match)
open MMBRecordedWitnessAuthority (savedValue)
open Kernel (Preterm ProofWitness)
abbrev program := MMBTheoremMatchExecution.program
private def sourceEquation : SpaceSemantics.Equation :=
  ((MMBExecution.binarySource.program.equations.filter (·.head == "mm0:mmb:proof-theorem")).head?).getD
    ⟨"",[],.symbol "None"⟩
private def field (body : Atom) (index : Nat) : Atom :=
  match body with | .expression values => values[index]?.getD (.symbol "None") | _ => .symbol "None"
private def casesOf (body : Atom) : SpaceSemantics.Cases :=
  match body with | .expression [_,_,.expression rows] => (readCases rows).getD [] | _ => []
private def firstBody (body : Atom) : Atom := ((casesOf body)[0]?.getD (.symbol "None",.symbol "None")).2
private def foundBody := firstBody (field sourceEquation.body 2)
private def signatureBody := firstBody (field foundBody 3)
private def poppedTarget := firstBody signatureBody
private def poppedArguments := firstBody poppedTarget
private def poppedChildren := firstBody poppedArguments
private def projected := firstBody (field poppedChildren 2)
private def tail := field projected 2
private def saveCase := field tail 2
private def saveCases := casesOf saveCase
private def savedBody := firstBody saveCase
private def finishBody := field savedBody 2
private def savePairs : List Atom :=
  [.expression [.var "witness",.expression [.symbol "MM0:L",.expression [.symbol "MM0:TheoremApp",
      .var "id",.var "parameters",.var "witnesses"]]],
   .expression [.var "before",.expression [.symbol "MM0:MMBPState",.var "next",.var "arity",.var "count",
      .var "remaining",.var "heap",.var "dummies",.var "hyps",.var "saved"]]]
private def finishPairs : List Atom :=
  [.expression [.var "result",.expression [.symbol "index-atom",.var "pushed",natural 0]],
   .expression [.var "finalHeap",.expression [.symbol "if",.var "save",
      .expression [.symbol "mm0:mmb:snoc",.var "h",.var "result"],.var "h"]]]
private theorem tail_shape : tail = .expression [.symbol "let*",.expression savePairs,saveCase] := by decide +kernel
private theorem save_shape : saveCase = .expression [.symbol "case",
  .expression [.symbol "mm0:mmb:save-proof",.var "before",.var "target",.var "witness"],
  .expression (saveCases.map fun row => .expression [row.1,row.2])] := by decide
private theorem save_cases_shape : saveCases =
  [(.expression [.symbol "Some",.expression [.symbol "MM0:MMBPState",.var "n",.var "a",.var "c",
      .expression [.symbol "MM0:L",.var "pushed"],.var "h",.var "d",.var "hs",.var "ss"]],savedBody),
   (.var "bad",.symbol "None")] := by decide
private theorem saved_shape : savedBody = .expression [.symbol "let*",.expression finishPairs,finishBody] := by decide
private theorem finish_shape : finishBody = .expression [.symbol "Some",.expression [.symbol "MM0:MMBPState",
  .var "n",.var "a",.var "c",.expression [.symbol "MM0:L",.var "pushed"],.var "finalHeap",.var "d",.var "hs",.var "ss"]] := by decide

/-- The source record stores the initializer and places its fresh reference
on the stack; saved application additionally appends that same reference to
its physical heap. The initializer remains subject to original validation. -/
def resultValue (next arity allocation identifier : Nat) (base : List Preterm) (recorded : List Sharing.Entry)
    (parameters : List Preterm) (children : List ProofWitness)
    (stack heap dummies hypotheses : List Atom) (claim : Preterm) (node : Atom) (save : Bool) : Atom :=
  let target := expressionValue allocation (Data.preterm claim) node
  let root := provedValue (Proof.witnessValue (.hyp (base.length+recorded.length))) target
  optionValue (some (stateValue next arity base.length (root::stack)
    (if save then heap++[root] else heap) dummies hypotheses
    (savedValue (recorded++[⟨some claim,.theoremApp identifier parameters children⟩]))))

private def savedEnvironment (next arity allocation : Nat) (base : List Preterm) (recorded : List Sharing.Entry)
    (stack heap dummies hypotheses : List Atom) (claim : Preterm) (node : Atom) (initializer : ProofWitness)
    (earlier : Subst) : Subst :=
  [("ss",listValue (savedValue (recorded++[⟨some claim,initializer⟩]))),("hs",listValue hypotheses),
   ("d",listValue dummies),("h",listValue heap),
   ("pushed",.expression (provedValue (Proof.witnessValue (.hyp (base.length+recorded.length)))
       (expressionValue allocation (Data.preterm claim) node)::stack)),
   ("c",natural base.length),("a",natural arity),("n",natural next)] ++ earlier

private theorem saved_body_returns (state : State) (next arity allocation : Nat)
    (base : List Preterm) (recorded : List Sharing.Entry) (stack heap dummies hypotheses : List Atom)
    (claim : Preterm) (node : Atom) (initializer : ProofWitness) (save : Bool) (earlier : Subst)
    (saveCaptured : applySubst earlier (.var "save") = boolean save)
    (freshResult : Subst.lookup earlier "result" = none)
    (freshHeap : Subst.lookup earlier "finalHeap" = none) :
    PureReturns program (savedEnvironment next arity allocation base recorded stack heap dummies hypotheses claim node initializer earlier)
      state savedBody state
      (optionValue (some (stateValue next arity base.length
        (provedValue (Proof.witnessValue (.hyp (base.length+recorded.length)))
          (expressionValue allocation (Data.preterm claim) node)::stack)
        (if save then heap++[provedValue (Proof.witnessValue (.hyp (base.length+recorded.length)))
          (expressionValue allocation (Data.preterm claim) node)] else heap)
        dummies hypotheses (savedValue (recorded++[⟨some claim,initializer⟩]))))) := by
  let root := provedValue (Proof.witnessValue (.hyp (base.length+recorded.length)))
      (expressionValue allocation (Data.preterm claim) node)
  simp only [applySubst,Subst.lookup] at saveCaptured
  simp only [Subst.lookup] at freshResult freshHeap
  let bindings := savedEnvironment next arity allocation base recorded stack heap dummies hypotheses claim node initializer earlier
  let indexed := ("result",root)::bindings
  let finished := ("finalHeap",listValue (if save then heap++[root] else heap))::indexed
  let nested := (.expression [.symbol "let",.var "result",.expression [.symbol "index-atom",.var "pushed",natural 0],
    .expression [.symbol "let",.var "finalHeap",.expression [.symbol "if",.var "save",
      .expression [.symbol "mm0:mmb:snoc",.var "h",.var "result"],.var "h"],finishBody]] : Atom)
  rw [saved_shape]
  apply let_star_returns program bindings state state finishPairs finishBody nested _ rfl
  apply let_returns program bindings indexed state state state (.var "result") _ _ root _
  · apply native_binary_call_returns program bindings state state state state "index-atom" (.var "pushed") (natural 0)
      (.expression (root::stack)) (natural 0) root
      (by decide) (by decide) (by decide +kernel) (by decide +kernel) _ _ _ (by decide)
    · exact variable_returns program bindings state "pushed"
    · exact grounded_returns program bindings state (.int 0)
    · simp [natural]
  · simp [SpaceSemantics.matchBinding,SpaceSemantics.matchValue,matchAtom,Subst.lookup,indexed,bindings,savedEnvironment,freshResult]
  · apply let_returns program indexed finished state state state (.var "finalHeap") _ finishBody
      (listValue (if save then heap++[root] else heap)) _
    · apply if_returns program indexed state state state (.var "save") (boolean save) _ _ _
      · simpa [indexed,bindings,savedEnvironment,applySubst,Subst.lookup,saveCaptured] using variable_returns program indexed state "save"
      · cases save with
        | false => exact variable_returns program indexed state "h"
        | true => exact MMBProofRunExecution.snoc_returns indexed state heap root "h" "result" rfl rfl
    · simp [SpaceSemantics.matchBinding,SpaceSemantics.matchValue,matchAtom,Subst.lookup,finished,indexed,bindings,savedEnvironment,freshHeap]
    · rw [finish_shape]
      apply unary_constructor_of_returns program finished state state "Some" _ _ (by decide +kernel) (by decide)
      apply data_call_returns program finished state state "MM0:MMBPState" _ _ (by decide +kernel) _ (by decide)
      apply evaluated_argument_returns program finished state state state .data
        (.symbol "MM0:MMBPState") (.symbol "MM0:MMBPState") _ _ [] 0 rfl
        (symbol_returns program finished state "MM0:MMBPState")
      apply evaluated_argument_returns program finished state state state .data (.var "n") (natural next) _ _ _ 1 rfl
        (variable_returns program finished state "n")
      apply evaluated_argument_returns program finished state state state .data (.var "a") (natural arity) _ _ _ 2 rfl
        (variable_returns program finished state "a")
      apply evaluated_argument_returns program finished state state state .data (.var "c") (natural base.length) _ _ _ 3 rfl
        (variable_returns program finished state "c")
      apply evaluated_argument_returns program finished state state state .data
        (.expression [.symbol "MM0:L",.var "pushed"]) (listValue (root::stack)) _ _ _ 4 rfl
      · exact unary_constructor_returns program finished state "MM0:L" "pushed" (by decide +kernel) (by decide)
      · apply variable_arguments_return program finished state state .data ["finalHeap","d","hs","ss"] _ 5
        simpa [finished,indexed,bindings,savedEnvironment,applySubst,Subst.lookup,root,stateValue,listValue,optionValue] using
          data_arguments_values_return program finished state _ 9


private theorem save_case_returns (state : State) (earlier : Subst) (next arity allocation : Nat)
    (base : List Preterm) (recorded : List Sharing.Entry) (stack heap dummies hypotheses : List Atom)
    (claim : Preterm) (node : Atom) (initializer : ProofWitness) (save : Bool)
    (beforeCaptured : applySubst earlier (.var "before") =
      stateValue next arity base.length stack heap dummies hypotheses (savedValue recorded))
    (targetCaptured : applySubst earlier (.var "target") = expressionValue allocation (Data.preterm claim) node)
    (witnessCaptured : applySubst earlier (.var "witness") = Proof.witnessValue initializer)
    (saveCaptured : applySubst earlier (.var "save") = boolean save)
    (fresh : ∀ name ∈ ["n","a","c","pushed","h","d","hs","ss","result","finalHeap"], Subst.lookup earlier name = none) :
    PureReturns program earlier state saveCase state
      (optionValue (some (stateValue next arity base.length
        (provedValue (Proof.witnessValue (.hyp (base.length+recorded.length)))
          (expressionValue allocation (Data.preterm claim) node)::stack)
        (if save then heap++[provedValue (Proof.witnessValue (.hyp (base.length+recorded.length)))
          (expressionValue allocation (Data.preterm claim) node)] else heap)
        dummies hypotheses (savedValue (recorded++[⟨some claim,initializer⟩]))))) := by
  have freshLookup := fresh
  simp only [Subst.lookup] at freshLookup
  let root := provedValue (Proof.witnessValue (.hyp (base.length+recorded.length)))
    (expressionValue allocation (Data.preterm claim) node)
  let bound := savedEnvironment next arity allocation base recorded stack heap dummies hypotheses claim node initializer earlier
  rw [save_shape]
  apply case_returns program earlier bound state state state _
    (optionValue (some (stateValue next arity base.length (root::stack) heap dummies hypotheses
      (savedValue (recorded++[⟨some claim,initializer⟩]))))) savedBody _ _ saveCases (read_cases_encoded saveCases)
  · exact MMBRecordedWitnessAuthority.save_proof_recorded_returns earlier state next arity allocation base recorded
      stack heap dummies hypotheses claim node initializer "before" "target" "witness"
      beforeCaptured targetCaptured witnessCaptured
  · simp [save_cases_shape,root,stateValue,listValue,optionValue,SpaceSemantics.selectCase,
      SpaceSemantics.matchValue,SpaceSemantics.matchValue.matchValues,matchAtom,Subst.lookup,
      bound,savedEnvironment,freshLookup]
  · exact saved_body_returns state next arity allocation base recorded stack heap dummies hypotheses claim node initializer
      save earlier saveCaptured (fresh "result" (by simp)) (fresh "finalHeap" (by simp))


private theorem tail_returns (state : State) (earlier : Subst) (next arity allocation identifier : Nat)
    (base : List Preterm) (recorded : List Sharing.Entry) (parameters : List Preterm) (children : List ProofWitness)
    (stack heap dummies hypotheses : List Atom) (claim : Preterm) (node : Atom) (save : Bool)
    (nextCaptured : applySubst earlier (.var "next") = natural next)
    (arityCaptured : applySubst earlier (.var "arity") = natural arity)
    (countCaptured : applySubst earlier (.var "count") = natural base.length)
    (remainingCaptured : applySubst earlier (.var "remaining") = listValue stack)
    (heapCaptured : applySubst earlier (.var "heap") = listValue heap)
    (dummiesCaptured : applySubst earlier (.var "dummies") = listValue dummies)
    (hypothesesCaptured : applySubst earlier (.var "hyps") = listValue hypotheses)
    (savedCaptured : applySubst earlier (.var "saved") = listValue (savedValue recorded))
    (idCaptured : applySubst earlier (.var "id") = natural identifier)
    (parametersCaptured : applySubst earlier (.var "parameters") = ListSubstitution.expressionsValue parameters)
    (childrenCaptured : applySubst earlier (.var "witnesses") = listValue (children.map Proof.witnessValue))
    (targetCaptured : applySubst earlier (.var "target") = expressionValue allocation (Data.preterm claim) node)
    (saveCaptured : applySubst earlier (.var "save") = boolean save)
    (fresh : ∀ name ∈ ["witness","before","n","a","c","pushed","h","d","hs","ss","result","finalHeap"],
      Subst.lookup earlier name = none) :
    PureReturns program earlier state tail state
      (resultValue next arity allocation identifier base recorded parameters children stack heap dummies hypotheses claim node save) := by
  have freshLookup := fresh
  simp only [Subst.lookup] at freshLookup
  have nextCapture := nextCaptured
  have arityCapture := arityCaptured
  have countCapture := countCaptured
  have remainingCapture := remainingCaptured
  have heapCapture := heapCaptured
  have dummiesCapture := dummiesCaptured
  have hypothesesCapture := hypothesesCaptured
  have savedCapture := savedCaptured
  have idCapture := idCaptured
  have parametersCapture := parametersCaptured
  have childrenCapture := childrenCaptured
  simp only [applySubst,Subst.lookup] at nextCapture arityCapture countCapture remainingCapture heapCapture
  simp only [applySubst,Subst.lookup] at dummiesCapture hypothesesCapture savedCapture idCapture parametersCapture childrenCapture
  let initializer := ProofWitness.theoremApp identifier parameters children
  let witnessed := ("witness",Proof.witnessValue initializer)::earlier
  let prior := stateValue next arity base.length stack heap dummies hypotheses (savedValue recorded)
  let prepared := ("before",prior)::witnessed
  let witnessExpression := (.expression [.symbol "MM0:L",.expression [.symbol "MM0:TheoremApp",
    .var "id",.var "parameters",.var "witnesses"]] : Atom)
  let stateExpression := (.expression [.symbol "MM0:MMBPState",.var "next",.var "arity",.var "count",
    .var "remaining",.var "heap",.var "dummies",.var "hyps",.var "saved"] : Atom)
  let nested := (.expression [.symbol "let",.var "witness",witnessExpression,
    .expression [.symbol "let",.var "before",stateExpression,saveCase]] : Atom)
  rw [tail_shape]
  apply let_star_returns program earlier state state savePairs saveCase nested _ rfl
  apply let_returns program earlier witnessed state state state (.var "witness") witnessExpression _
    (Proof.witnessValue initializer) _
  · simp only [witnessExpression,initializer,Proof.witnessValue,ListAccess.listValue]
    apply unary_constructor_of_returns program earlier state state "MM0:L" _ _ (by decide +kernel) (by decide)
    simpa [Proof.witnessValue,initializer,ListAccess.listValue,applySubst,Subst.lookup,idCapture,parametersCapture,childrenCapture] using
      constructor_variables_return program earlier state "MM0:TheoremApp" ["id","parameters","witnesses"]
        (by decide +kernel) (by decide)
  · simp [SpaceSemantics.matchBinding,SpaceSemantics.matchValue,matchAtom,Subst.lookup,witnessed,freshLookup]
  · apply let_returns program witnessed prepared state state state (.var "before") stateExpression saveCase prior _
    · simpa [stateExpression,witnessed,prior,stateValue,applySubst,Subst.lookup,nextCapture,arityCapture,countCapture,
        remainingCapture,heapCapture,dummiesCapture,hypothesesCapture,savedCapture] using
        constructor_variables_return program witnessed state "MM0:MMBPState"
          ["next","arity","count","remaining","heap","dummies","hyps","saved"] (by decide +kernel) (by decide)
    · simp [SpaceSemantics.matchBinding,SpaceSemantics.matchValue,matchAtom,Subst.lookup,prepared,witnessed,freshLookup]
    · unfold resultValue
      apply save_case_returns state prepared next arity allocation base recorded stack heap dummies hypotheses claim node initializer save
      · rfl
      · simpa [prepared,witnessed,applySubst,Subst.lookup] using targetCaptured
      · rfl
      · simpa [prepared,witnessed,applySubst,Subst.lookup] using saveCaptured
      · intro name member
        simp only [List.mem_cons,List.mem_nil_iff,or_false] at member
        rcases member with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
          simpa [prepared,witnessed,Subst.lookup] using fresh _ (by simp)


private def guardNames := ["resolver","context","tableEntry","arguments","expected","target"]
private theorem projected_shape : projected = .expression [.symbol "if",
    .expression (.symbol "mm0:mmb:match-theorem" :: guardNames.map Atom.var),tail,.symbol "None"] := by decide +kernel
private theorem passive_variables (names : List String) (head : String) :
    ∀ offset argument, (names.map Atom.var)[offset]? = some argument →
      argumentIsRaw program head offset = true ∨ passiveArgument argument = true := by
  intro offset argument found
  simp only [List.getElem?_map] at found
  cases selected : names[offset]? with
  | none => simp [selected] at found
  | some name => simp [selected] at found; subst argument; exact .inr rfl

private theorem projected_returns (state : State) (earlier : Subst) (next arity allocation identifier : Nat)
    (base : List Preterm) (recorded : List Sharing.Entry) (parameters : List Preterm) (children : List ProofWitness)
    (stack heap dummies hypotheses : List Atom) (claim : Preterm) (node : Atom) (save : Bool)
    (resolver context declarationArguments endPosition : Atom) (arguments codes expected : List Atom)
    (result : Option (List Atom))
    (nextCaptured : applySubst earlier (.var "next") = natural next)
    (arityCaptured : applySubst earlier (.var "arity") = natural arity)
    (countCaptured : applySubst earlier (.var "count") = natural base.length)
    (remainingCaptured : applySubst earlier (.var "remaining") = listValue stack)
    (heapCaptured : applySubst earlier (.var "heap") = listValue heap)
    (dummiesCaptured : applySubst earlier (.var "dummies") = listValue dummies)
    (hypothesesCaptured : applySubst earlier (.var "hyps") = listValue hypotheses)
    (savedCaptured : applySubst earlier (.var "saved") = listValue (savedValue recorded))
    (idCaptured : applySubst earlier (.var "id") = natural identifier)
    (parametersCaptured : applySubst earlier (.var "parameters") = ListSubstitution.expressionsValue parameters)
    (childrenCaptured : applySubst earlier (.var "witnesses") = listValue (children.map Proof.witnessValue))
    (targetCaptured : applySubst earlier (.var "target") = expressionValue allocation (Data.preterm claim) node)
    (saveCaptured : applySubst earlier (.var "save") = boolean save)
    (resolverCaptured : applySubst earlier (.var "resolver") = resolver)
    (contextCaptured : applySubst earlier (.var "context") = context)
    (declarationCaptured : applySubst earlier (.var "tableEntry") = theoremValue declarationArguments codes endPosition)
    (argumentsCaptured : applySubst earlier (.var "arguments") = listValue arguments)
    (expectedCaptured : applySubst earlier (.var "expected") = listValue expected)
    (fresh : ∀ name ∈ ["witness","before","n","a","c","pushed","h","d","hs","ss","result","finalHeap"],
      Subst.lookup earlier name = none)
    (trace : Match context resolver arguments codes expected (expressionValue allocation (Data.preterm claim) node) result) :
    PureReturns program earlier state projected state
      (if result.isSome then
        resultValue next arity allocation identifier base recorded parameters children stack heap dummies hypotheses claim node save
       else .symbol "None") := by
  have resolverCapture := resolverCaptured
  have contextCapture := contextCaptured
  have declarationCapture := declarationCaptured
  have argumentsCapture := argumentsCaptured
  have expectedCapture := expectedCaptured
  have targetCapture := targetCaptured
  simp only [applySubst,Subst.lookup] at resolverCapture contextCapture declarationCapture argumentsCapture expectedCapture targetCapture
  have tested : PureReturns program earlier state
      (.expression (.symbol "mm0:mmb:match-theorem" :: guardNames.map Atom.var)) state (boolean result.isSome) := by
    apply captured_call_returns program
      (MMBTheoremMatchExecution.callBindings resolver context (theoremValue declarationArguments codes endPosition)
        (listValue arguments) (listValue expected) (expressionValue allocation (Data.preterm claim) node)) earlier
      state state "mm0:mmb:match-theorem"
      (["resolver","context","declaration","arguments","hypotheses","target"].map Atom.var)
      (guardNames.map Atom.var) (boolean result.isSome)
      (by decide +kernel) (by decide) (passive_variables _ _) (passive_variables _ _) _
      (MMBTheoremMatchExecution.returns state resolver context declarationArguments endPosition arguments codes expected
        allocation (Data.preterm claim) node result trace)
    simp [guardNames,MMBTheoremMatchExecution.callBindings,applySubst,Subst.lookup,
      resolverCapture,contextCapture,declarationCapture,argumentsCapture,expectedCapture,targetCapture]
  rw [projected_shape]
  apply if_returns program earlier state state state _ (boolean result.isSome) tail (.symbol "None") _ tested
  cases result with
  | none => simpa [boolean] using symbol_returns program earlier state "None"
  | some slots =>
    simpa [boolean] using tail_returns state earlier next arity allocation identifier base recorded parameters children
      stack heap dummies hypotheses claim node save nextCaptured arityCaptured countCaptured remainingCaptured heapCaptured
      dummiesCaptured hypothesesCaptured savedCaptured idCaptured parametersCaptured childrenCaptured targetCaptured saveCaptured fresh


private def projectionPairs : List Atom :=
  [.expression [.var "target",.expression [.symbol "MM0:MMBExpression",.var "pointer",.var "expression",.var "node"]],
   .expression [.var "conclusions",.expression [.symbol "mm0:mmb:proof-conclusions",.var "children"]],
   .expression [.var "values",.expression [.symbol "mm0:mmb:expression-values",.var "arguments"]],
   .expression [.var "proofs",.expression [.symbol "mm0:mmb:proof-values",.var "children"]]]
private def projectionCase := field poppedChildren 2
private def projectionCases := casesOf projectionCase
private theorem popped_children_shape : poppedChildren = .expression [.symbol "let*",.expression projectionPairs,projectionCase] := by decide +kernel
private theorem projection_case_shape : projectionCase = .expression [.symbol "case",
    .expression (["conclusions","values","proofs"].map Atom.var),
    .expression (projectionCases.map fun row => .expression [row.1,row.2])] := by decide
private theorem projection_cases_shape : projectionCases =
  [(.expression [.expression [.symbol "Some",.var "expected"],.expression [.symbol "Some",.var "parameters"],
      .expression [.symbol "Some",.var "witnesses"]],projected),(.var "bad",.symbol "None")] := by decide

def childEntries (children : List (ProofWitness × Atom)) : List Atom :=
  children.map fun child => provedValue (Proof.witnessValue child.1) child.2

private theorem popped_children_returns (state : State) (earlier : Subst) (next arity allocation identifier : Nat)
    (base : List Preterm) (recorded : List Sharing.Entry) (parameters : List Preterm) (children : List (ProofWitness × Atom))
    (stack heap dummies hypotheses arguments : List Atom) (claim : Preterm) (node : Atom) (save : Bool)
    (resolver context declarationArguments endPosition : Atom) (codes : List Atom) (result : Option (List Atom))
    (nextCaptured : applySubst earlier (.var "next") = natural next)
    (arityCaptured : applySubst earlier (.var "arity") = natural arity)
    (countCaptured : applySubst earlier (.var "count") = natural base.length)
    (remainingCaptured : applySubst earlier (.var "remaining") = listValue stack)
    (heapCaptured : applySubst earlier (.var "heap") = listValue heap)
    (dummiesCaptured : applySubst earlier (.var "dummies") = listValue dummies)
    (hypothesesCaptured : applySubst earlier (.var "hyps") = listValue hypotheses)
    (savedCaptured : applySubst earlier (.var "saved") = listValue (savedValue recorded))
    (idCaptured : applySubst earlier (.var "id") = natural identifier)
    (pointerCaptured : applySubst earlier (.var "pointer") = natural allocation)
    (expressionCaptured : applySubst earlier (.var "expression") = Data.preterm claim)
    (nodeCaptured : applySubst earlier (.var "node") = node)
    (childrenCaptured : applySubst earlier (.var "children") = listValue (childEntries children))
    (saveCaptured : applySubst earlier (.var "save") = boolean save)
    (resolverCaptured : applySubst earlier (.var "resolver") = resolver)
    (contextCaptured : applySubst earlier (.var "context") = context)
    (declarationCaptured : applySubst earlier (.var "tableEntry") = theoremValue declarationArguments codes endPosition)
    (argumentsCaptured : applySubst earlier (.var "arguments") = listValue arguments)
    (fresh : ∀ name ∈ ["target","conclusions","values","proofs","expected","parameters","witnesses",
      "witness","before","n","a","c","pushed","h","d","hs","ss","result","finalHeap"],
      Subst.lookup earlier name = none)
    (claims : MMBProofRunExecution.ExpressionClaims arguments (parameters.map Data.preterm))
    (trace : Match context resolver arguments codes (children.map Prod.snd)
      (expressionValue allocation (Data.preterm claim) node) result) :
    PureReturns program earlier state poppedChildren state
      (if result.isSome then
        resultValue next arity allocation identifier base recorded parameters (children.map Prod.fst)
          stack heap dummies hypotheses claim node save
       else .symbol "None") := by
  have freshLookup := fresh
  simp only [Subst.lookup] at freshLookup
  have pointerCapture := pointerCaptured
  have expressionCapture := expressionCaptured
  have nodeCapture := nodeCaptured
  have argumentsCapture := argumentsCaptured
  have childrenCapture := childrenCaptured
  simp only [applySubst,Subst.lookup] at pointerCapture expressionCapture nodeCapture argumentsCapture childrenCapture
  let target := expressionValue allocation (Data.preterm claim) node
  let expected := listValue (children.map Prod.snd)
  let values := ListSubstitution.expressionsValue parameters
  let witnesses := listValue ((children.map Prod.fst).map Proof.witnessValue)
  let targeted := ("target",target)::earlier
  let concluded := ("conclusions",optionValue (some expected))::targeted
  let valued := ("values",optionValue (some values))::concluded
  let proofed := ("proofs",optionValue (some witnesses))::valued
  let branched := ("witnesses",witnesses)::("parameters",values)::("expected",expected)::proofed
  let nested := (.expression [.symbol "let",.var "target",
    .expression [.symbol "MM0:MMBExpression",.var "pointer",.var "expression",.var "node"],
    .expression [.symbol "let",.var "conclusions",.expression [.symbol "mm0:mmb:proof-conclusions",.var "children"],
    .expression [.symbol "let",.var "values",.expression [.symbol "mm0:mmb:expression-values",.var "arguments"],
    .expression [.symbol "let",.var "proofs",.expression [.symbol "mm0:mmb:proof-values",.var "children"],projectionCase]]]] : Atom)
  rw [popped_children_shape]
  apply let_star_returns program earlier state state projectionPairs projectionCase nested _ rfl
  apply let_returns program earlier targeted state state state (.var "target") _ _ target _
  · simpa [target,expressionValue,applySubst,Subst.lookup,pointerCapture,expressionCapture,nodeCapture] using
      constructor_variables_return program earlier state "MM0:MMBExpression" ["pointer","expression","node"]
        (by decide +kernel) (by decide)
  · simp [SpaceSemantics.matchBinding,SpaceSemantics.matchValue,matchAtom,Subst.lookup,targeted,freshLookup]
  · apply let_returns program targeted concluded state state state (.var "conclusions") _ _ (optionValue (some expected)) _
    · simpa [expected,List.map_map,Function.comp_def] using
        MMBTheoremCommandExecution.proof_conclusions_returns targeted state
          (children.map fun child => (Proof.witnessValue child.1,child.2)) (.var "children")
          (by simpa [targeted,applySubst,Subst.lookup,childEntries,MMBTheoremCommandExecution.provedEntries,List.map_map,Function.comp_def] using childrenCaptured)
    · simp [SpaceSemantics.matchBinding,SpaceSemantics.matchValue,matchAtom,Subst.lookup,concluded,targeted,freshLookup]
    · apply let_returns program concluded valued state state state (.var "values") _ _ (optionValue (some values)) _
      · exact MMBProofRunExecution.expression_values_returns concluded state arguments (parameters.map Data.preterm)
          (.var "arguments") (by simpa [concluded,targeted,applySubst,Subst.lookup] using argumentsCaptured) claims
      · simp [SpaceSemantics.matchBinding,SpaceSemantics.matchValue,matchAtom,Subst.lookup,valued,concluded,targeted,freshLookup]
      · apply let_returns program valued proofed state state state (.var "proofs") _ _ (optionValue (some witnesses)) _
        · simpa [witnesses,List.map_map,Function.comp_def] using
            MMBTheoremCommandExecution.proof_values_returns valued state
              (children.map fun child => (Proof.witnessValue child.1,child.2)) (.var "children")
              (by simpa [valued,concluded,targeted,applySubst,Subst.lookup,childEntries,MMBTheoremCommandExecution.provedEntries,List.map_map,Function.comp_def] using childrenCaptured)
        · simp [SpaceSemantics.matchBinding,SpaceSemantics.matchValue,matchAtom,Subst.lookup,proofed,valued,concluded,targeted,freshLookup]
        · rw [projection_case_shape]
          apply case_returns program proofed branched state state state _
            (.expression [optionValue (some expected),optionValue (some values),optionValue (some witnesses)]) projected _ _
            projectionCases (read_cases_encoded projectionCases)
          · simpa [proofed,valued,concluded,targeted,applySubst,Subst.lookup] using
              tuple_variables_return program proofed state ["conclusions","values","proofs"]
          · simp [projection_cases_shape,SpaceSemantics.selectCase,SpaceSemantics.matchValue,
              SpaceSemantics.matchValue.matchValues,matchAtom,Subst.lookup,proofed,valued,concluded,targeted,branched,
              optionValue,freshLookup]
          · apply projected_returns state branched next arity allocation identifier base recorded parameters (children.map Prod.fst)
              stack heap dummies hypotheses claim node save resolver context declarationArguments endPosition arguments codes
              (children.map Prod.snd) result
            all_goals try first | assumption | rfl
            · intro name member
              simp only [List.mem_cons,List.mem_nil_iff,or_false] at member
              rcases member with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
                simpa [branched,proofed,valued,concluded,targeted,Subst.lookup] using fresh _ (by simp)


private theorem computed_pop_returns (bindings : Subst) (state : State)
    (kind : MMBTheoremCommandExecution.StackKind) (formalArguments stack : List Atom)
    (result : Option (List Atom × List Atom)) (countName : String) (stackExpression : Atom)
    (argsCaptured : applySubst bindings (.var countName) = .expression formalArguments)
    (stackCaptured : applySubst bindings stackExpression = listValue stack)
    (popped : MMBTheoremCommandExecution.Pops kind formalArguments.length stack result) :
    PureReturns program bindings state (.expression [.symbol "mm0:mmb:pop-many",kind.value,
      .expression [.symbol "size-atom",.var countName],stackExpression]) state
      (MMBTheoremCommandExecution.poppedValue result) := by
  let prior : Subst := [("kind",kind.value),("number",natural formalArguments.length),("items",listValue stack)]
  have original := MMBTheoremCommandExecution.pop_many_returns prior state kind formalArguments.length stack
    result "kind" "number" "items" rfl rfl rfl popped
  have finished := captured_function_arguments_returns program prior bindings state state "mm0:mmb:pop-many"
    (["kind","number","items"].map Atom.var) 3 _ (by decide +kernel) (by decide)
    (passive_variables _ _) original
  apply call_returns program bindings state state "mm0:mmb:pop-many" _ _ (by decide +kernel) _ (by decide)
  apply raw_argument_answers program bindings state state "mm0:mmb:pop-many" kind.value
    [.expression [.symbol "size-atom",.var countName],stackExpression] [] 0 [_] (by decide +kernel)
  apply evaluated_argument_returns program bindings state state state (.function "mm0:mmb:pop-many")
    (.expression [.symbol "size-atom",.var countName]) (natural formalArguments.length) _ _ _ 1 (by decide +kernel)
  · apply native_variable_call_returns program bindings state state "size-atom" [countName]
      (natural formalArguments.length) (by decide) (by decide) _ (by decide)
    change StdLib.apply state "size-atom" [applySubst bindings (.var countName)] = .ok (state,[natural formalArguments.length])
    rw [argsCaptured]
    rfl
  · apply raw_argument_answers program bindings state state "mm0:mmb:pop-many" stackExpression [] _ 2 [_] (by decide +kernel)
    change (theory program).MultiStep
      {state,control := .arguments bindings (.function "mm0:mmb:pop-many") []
        [applySubst bindings kind.value,natural formalArguments.length,applySubst bindings stackExpression] 3}
      (Eval.finished state [MMBTheoremCommandExecution.poppedValue result] [] [])
    rw [stackCaptured]
    cases kind <;> simpa [prior,MMBTheoremCommandExecution.StackKind.value,applySubst,Subst.lookup] using finished

private def proofPopCases := casesOf poppedArguments
private theorem proof_pop_shape : poppedArguments = .expression [.symbol "case",
  .expression [.symbol "mm0:mmb:pop-many",.symbol "MM0:MMBProofs",
    .expression [.symbol "size-atom",.var "premises"],.var "afterArguments"],
  .expression (proofPopCases.map fun row => .expression [row.1,row.2])] := by decide +kernel
private theorem proof_pop_cases_shape : proofPopCases =
  [(.expression [.symbol "Some",.expression [.symbol "MM0:MMBPopped",.var "children",.var "remaining"]],poppedChildren),
   (.var "bad",.symbol "None")] := by decide

private theorem proof_pop_refused_returns (state : State) (earlier : Subst) (formalPremises stack : List Atom)
    (premisesCaptured : applySubst earlier (.var "premises") = .expression formalPremises)
    (stackCaptured : applySubst earlier (.var "afterArguments") = listValue stack)
    (badFresh : Subst.lookup earlier "bad" = none)
    (popped : MMBTheoremCommandExecution.Pops .proofs formalPremises.length stack none) :
    PureReturns program earlier state poppedArguments state (.symbol "None") := by
  simp only [Subst.lookup] at badFresh
  rw [proof_pop_shape]
  apply case_returns program earlier (("bad",.symbol "None")::earlier) state state state _ (.symbol "None")
    (.symbol "None") _ _ proofPopCases (read_cases_encoded proofPopCases)
  · exact computed_pop_returns earlier state .proofs formalPremises stack none "premises" (.var "afterArguments")
      premisesCaptured stackCaptured popped
  · simp [proof_pop_cases_shape,SpaceSemantics.selectCase,SpaceSemantics.matchValue,matchAtom,Subst.lookup,badFresh]
  · exact symbol_returns _ _ _ _

private theorem proof_pop_returns (state : State) (earlier : Subst) (next arity allocation identifier : Nat)
    (base : List Preterm) (recorded : List Sharing.Entry) (parameters : List Preterm) (children : List (ProofWitness × Atom))
    (stack heap dummies hypotheses arguments : List Atom) (claim : Preterm) (node : Atom) (save : Bool)
    (resolver context declarationArguments endPosition : Atom) (codes : List Atom) (result : Option (List Atom))
    (formalPremises beforeChildren : List Atom)
    (nextCaptured : applySubst earlier (.var "next") = natural next)
    (arityCaptured : applySubst earlier (.var "arity") = natural arity)
    (countCaptured : applySubst earlier (.var "count") = natural base.length)
    (heapCaptured : applySubst earlier (.var "heap") = listValue heap)
    (dummiesCaptured : applySubst earlier (.var "dummies") = listValue dummies)
    (hypothesesCaptured : applySubst earlier (.var "hyps") = listValue hypotheses)
    (savedCaptured : applySubst earlier (.var "saved") = listValue (savedValue recorded))
    (idCaptured : applySubst earlier (.var "id") = natural identifier)
    (pointerCaptured : applySubst earlier (.var "pointer") = natural allocation)
    (expressionCaptured : applySubst earlier (.var "expression") = Data.preterm claim)
    (nodeCaptured : applySubst earlier (.var "node") = node)
    (saveCaptured : applySubst earlier (.var "save") = boolean save)
    (resolverCaptured : applySubst earlier (.var "resolver") = resolver)
    (contextCaptured : applySubst earlier (.var "context") = context)
    (declarationCaptured : applySubst earlier (.var "tableEntry") = theoremValue declarationArguments codes endPosition)
    (argumentsCaptured : applySubst earlier (.var "arguments") = listValue arguments)
    (premisesCaptured : applySubst earlier (.var "premises") = .expression formalPremises)
    (stackCaptured : applySubst earlier (.var "afterArguments") = listValue beforeChildren)
    (popped : MMBTheoremCommandExecution.Pops .proofs formalPremises.length beforeChildren (some (childEntries children,stack)))
    (fresh : ∀ name ∈ ["children","remaining","target","conclusions","values","proofs","expected","parameters","witnesses",
      "witness","before","n","a","c","pushed","h","d","hs","ss","result","finalHeap"],
      Subst.lookup earlier name = none)
    (claims : MMBProofRunExecution.ExpressionClaims arguments (parameters.map Data.preterm))
    (trace : Match context resolver arguments codes (children.map Prod.snd)
      (expressionValue allocation (Data.preterm claim) node) result) :
    PureReturns program earlier state poppedArguments state
      (if result.isSome then
        resultValue next arity allocation identifier base recorded parameters (children.map Prod.fst)
          stack heap dummies hypotheses claim node save
       else .symbol "None") := by
  have freshLookup := fresh
  simp only [Subst.lookup] at freshLookup
  let bound := ("remaining",listValue stack)::("children",listValue (childEntries children))::earlier
  rw [proof_pop_shape]
  apply case_returns program earlier bound state state state _
    (MMBTheoremCommandExecution.poppedValue (some (childEntries children,stack))) poppedChildren _ _
    proofPopCases (read_cases_encoded proofPopCases)
  · exact computed_pop_returns earlier state .proofs formalPremises beforeChildren
      (some (childEntries children,stack)) "premises" (.var "afterArguments") premisesCaptured stackCaptured popped
  · simp [proof_pop_cases_shape,MMBTheoremCommandExecution.poppedValue,SpaceSemantics.selectCase,
      SpaceSemantics.matchValue,SpaceSemantics.matchValue.matchValues,matchAtom,Subst.lookup,bound,optionValue,freshLookup]
  · apply popped_children_returns state bound next arity allocation identifier base recorded parameters children
      stack heap dummies hypotheses arguments claim node save resolver context declarationArguments endPosition codes result
    all_goals try first | assumption | rfl
    · intro name member
      simp only [List.mem_cons,List.mem_nil_iff,or_false] at member
      rcases member with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        simpa [bound,Subst.lookup] using fresh _ (by simp)


private def argumentPopCases := casesOf poppedTarget
private theorem argument_pop_shape : poppedTarget = .expression [.symbol "case",
  .expression [.symbol "mm0:mmb:pop-many",.symbol "MM0:MMBExpressions",
    .expression [.symbol "size-atom",.var "args"],.expression [.symbol "MM0:L",.var "rest"]],
  .expression (argumentPopCases.map fun row => .expression [row.1,row.2])] := by decide +kernel
private theorem argument_pop_cases_shape : argumentPopCases =
  [(.expression [.symbol "Some",.expression [.symbol "MM0:MMBPopped",.var "arguments",.var "afterArguments"]],poppedArguments),
   (.var "bad",.symbol "None")] := by decide

private theorem argument_pop_refused_returns (state : State) (earlier : Subst) (formalArguments stack : List Atom)
    (argumentsCaptured : applySubst earlier (.var "args") = .expression formalArguments)
    (stackCaptured : applySubst earlier (.var "rest") = .expression stack)
    (badFresh : Subst.lookup earlier "bad" = none)
    (popped : MMBTheoremCommandExecution.Pops .expressions formalArguments.length stack none) :
    PureReturns program earlier state poppedTarget state (.symbol "None") := by
  simp only [Subst.lookup] at badFresh
  simp only [applySubst] at stackCaptured
  rw [argument_pop_shape]
  apply case_returns program earlier (("bad",.symbol "None")::earlier) state state state _ (.symbol "None")
    (.symbol "None") _ _ argumentPopCases (read_cases_encoded argumentPopCases)
  · exact computed_pop_returns earlier state .expressions formalArguments stack none "args"
      (.expression [.symbol "MM0:L",.var "rest"]) argumentsCaptured
      (by simp [applySubst,applySubst.applySubstList,listValue,stackCaptured]) popped
  · simp [argument_pop_cases_shape,SpaceSemantics.selectCase,SpaceSemantics.matchValue,matchAtom,Subst.lookup,badFresh]
  · exact symbol_returns _ _ _ _

private theorem argument_pop_returns (state : State) (earlier : Subst) (next arity allocation identifier : Nat)
    (base : List Preterm) (recorded : List Sharing.Entry) (parameters : List Preterm) (children : List (ProofWitness × Atom))
    (stack heap dummies hypotheses arguments : List Atom) (claim : Preterm) (node : Atom) (save : Bool)
    (resolver context declarationArguments endPosition : Atom) (codes : List Atom) (result : Option (List Atom))
    (formalArguments formalPremises beforeArguments beforeChildren : List Atom)
    (nextCaptured : applySubst earlier (.var "next") = natural next)
    (arityCaptured : applySubst earlier (.var "arity") = natural arity)
    (countCaptured : applySubst earlier (.var "count") = natural base.length)
    (heapCaptured : applySubst earlier (.var "heap") = listValue heap)
    (dummiesCaptured : applySubst earlier (.var "dummies") = listValue dummies)
    (hypothesesCaptured : applySubst earlier (.var "hyps") = listValue hypotheses)
    (savedCaptured : applySubst earlier (.var "saved") = listValue (savedValue recorded))
    (idCaptured : applySubst earlier (.var "id") = natural identifier)
    (pointerCaptured : applySubst earlier (.var "pointer") = natural allocation)
    (expressionCaptured : applySubst earlier (.var "expression") = Data.preterm claim)
    (nodeCaptured : applySubst earlier (.var "node") = node)
    (saveCaptured : applySubst earlier (.var "save") = boolean save)
    (resolverCaptured : applySubst earlier (.var "resolver") = resolver)
    (contextCaptured : applySubst earlier (.var "context") = context)
    (declarationCaptured : applySubst earlier (.var "tableEntry") = theoremValue declarationArguments codes endPosition)
    (premisesCaptured : applySubst earlier (.var "premises") = .expression formalPremises)
    (argsCaptured : applySubst earlier (.var "args") = .expression formalArguments)
    (stackCaptured : applySubst earlier (.var "rest") = .expression beforeArguments)
    (argumentsPopped : MMBTheoremCommandExecution.Pops .expressions formalArguments.length beforeArguments (some (arguments,beforeChildren)))
    (popped : MMBTheoremCommandExecution.Pops .proofs formalPremises.length beforeChildren (some (childEntries children,stack)))
    (fresh : ∀ name ∈ ["arguments","afterArguments","children","remaining","target","conclusions","values","proofs","expected","parameters","witnesses",
      "witness","before","n","a","c","pushed","h","d","hs","ss","result","finalHeap"],
      Subst.lookup earlier name = none)
    (claims : MMBProofRunExecution.ExpressionClaims arguments (parameters.map Data.preterm))
    (trace : Match context resolver arguments codes (children.map Prod.snd)
      (expressionValue allocation (Data.preterm claim) node) result) :
    PureReturns program earlier state poppedTarget state
      (if result.isSome then
        resultValue next arity allocation identifier base recorded parameters (children.map Prod.fst)
          stack heap dummies hypotheses claim node save
       else .symbol "None") := by
  have freshLookup := fresh
  simp only [Subst.lookup] at freshLookup
  let bound := ("afterArguments",listValue beforeChildren)::("arguments",listValue arguments)::earlier
  simp only [applySubst] at stackCaptured
  rw [argument_pop_shape]
  apply case_returns program earlier bound state state state _
    (MMBTheoremCommandExecution.poppedValue (some (arguments,beforeChildren))) poppedArguments _ _
    argumentPopCases (read_cases_encoded argumentPopCases)
  · exact computed_pop_returns earlier state .expressions formalArguments beforeArguments
      (some (arguments,beforeChildren)) "args" (.expression [.symbol "MM0:L",.var "rest"]) argsCaptured
      (by simp [applySubst,applySubst.applySubstList,listValue,stackCaptured]) argumentsPopped
  · simp [argument_pop_cases_shape,MMBTheoremCommandExecution.poppedValue,SpaceSemantics.selectCase,
      SpaceSemantics.matchValue,SpaceSemantics.matchValue.matchValues,matchAtom,Subst.lookup,bound,optionValue,freshLookup]
  · apply proof_pop_returns state bound next arity allocation identifier base recorded parameters children
      stack heap dummies hypotheses arguments claim node save resolver context declarationArguments endPosition codes result
      formalPremises beforeChildren
    all_goals try first | assumption | rfl
    · intro name member
      simp only [List.mem_cons,List.mem_nil_iff,or_false] at member
      rcases member with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        simpa [bound,Subst.lookup] using fresh _ (by simp)


private def targetCases := casesOf signatureBody
private theorem target_case_shape : signatureBody = .expression [.symbol "case",.var "stack",
  .expression (targetCases.map fun row => .expression [row.1,row.2])] := by decide +kernel
private theorem target_cases_shape : targetCases =
  [(.expression [.symbol "cons",.expression [.symbol "MM0:MMBExpression",.var "pointer",.var "expression",.var "node"],.var "rest"],poppedTarget),
   (.var "bad",.symbol "None")] := by decide

/-- The original theorem-application continuation after signature decoding.
The initial stack is still consumed by the unchanged source case and pop calls. -/
def applicationBody : Atom := signatureBody

/-- Exact source fields retained at the signature boundary. -/
def applicationBindings (resolver context : Atom) (next arity identifier : Nat)
    (base : List Preterm) (recorded : List Sharing.Entry) (formalArguments formalPremises codes stack heap dummies hypotheses : List Atom)
    (endPosition : Atom) (save : Bool) : Subst :=
  [("save",boolean save),("saved",listValue (savedValue recorded)),("hyps",listValue hypotheses),
   ("dummies",listValue dummies),("heap",listValue heap),("stack",.expression stack),
   ("count",natural base.length),("arity",natural arity),("next",natural next),
   ("premises",.expression formalPremises),("args",.expression formalArguments),("id",natural identifier),
   ("tableEntry",theoremValue (listValue formalArguments) codes endPosition),("context",context),("resolver",resolver)]

/-- The unchanged continuation executes under any original caller environment
that supplies its captured fields and preserves freshness of its lexical names. -/
theorem captured_returns (state : State) (earlier : Subst) (next arity allocation identifier : Nat)
    (base : List Preterm) (recorded : List Sharing.Entry) (parameters : List Preterm) (children : List (ProofWitness × Atom))
    (stack heap dummies hypotheses arguments : List Atom) (claim : Preterm) (node : Atom) (save : Bool)
    (resolver context declarationArguments endPosition : Atom) (codes : List Atom) (result : Option (List Atom))
    (formalArguments formalPremises beforeArguments beforeChildren : List Atom)
    (nextCaptured : applySubst earlier (.var "next") = natural next)
    (arityCaptured : applySubst earlier (.var "arity") = natural arity)
    (countCaptured : applySubst earlier (.var "count") = natural base.length)
    (heapCaptured : applySubst earlier (.var "heap") = listValue heap)
    (dummiesCaptured : applySubst earlier (.var "dummies") = listValue dummies)
    (hypothesesCaptured : applySubst earlier (.var "hyps") = listValue hypotheses)
    (savedCaptured : applySubst earlier (.var "saved") = listValue (savedValue recorded))
    (idCaptured : applySubst earlier (.var "id") = natural identifier)
    (saveCaptured : applySubst earlier (.var "save") = boolean save)
    (resolverCaptured : applySubst earlier (.var "resolver") = resolver)
    (contextCaptured : applySubst earlier (.var "context") = context)
    (declarationCaptured : applySubst earlier (.var "tableEntry") = theoremValue declarationArguments codes endPosition)
    (premisesCaptured : applySubst earlier (.var "premises") = .expression formalPremises)
    (argsCaptured : applySubst earlier (.var "args") = .expression formalArguments)
    (stackCaptured : applySubst earlier (.var "stack") =
      .expression (expressionValue allocation (Data.preterm claim) node::beforeArguments))
    (argumentsPopped : MMBTheoremCommandExecution.Pops .expressions formalArguments.length beforeArguments (some (arguments,beforeChildren)))
    (popped : MMBTheoremCommandExecution.Pops .proofs formalPremises.length beforeChildren (some (childEntries children,stack)))
    (fresh : ∀ name ∈ ["pointer","expression","node","rest","arguments","afterArguments","children","remaining","target","conclusions","values","proofs","expected","parameters","witnesses",
      "witness","before","n","a","c","pushed","h","d","hs","ss","result","finalHeap"],
      Subst.lookup earlier name = none)
    (claims : MMBProofRunExecution.ExpressionClaims arguments (parameters.map Data.preterm))
    (trace : Match context resolver arguments codes (children.map Prod.snd)
      (expressionValue allocation (Data.preterm claim) node) result) :
    PureReturns program earlier state applicationBody state
      (if result.isSome then
        resultValue next arity allocation identifier base recorded parameters (children.map Prod.fst)
          stack heap dummies hypotheses claim node save
       else .symbol "None") := by
  have freshLookup := fresh
  simp only [Subst.lookup] at freshLookup
  let bound := ("rest",.expression beforeArguments)::("node",node)::("expression",Data.preterm claim)::("pointer",natural allocation)::earlier
  rw [applicationBody,target_case_shape]
  apply case_returns program earlier bound state state state (.var "stack")
    (.expression (expressionValue allocation (Data.preterm claim) node::beforeArguments)) poppedTarget _ _
    targetCases (read_cases_encoded targetCases)
  · simpa only [stackCaptured] using variable_returns program earlier state "stack"
  · simp [target_cases_shape,expressionValue,SpaceSemantics.selectCase,
      SpaceSemantics.matchValue,SpaceSemantics.matchValue.matchValues,matchAtom,Subst.lookup,bound,freshLookup]
  · apply argument_pop_returns state bound next arity allocation identifier base recorded parameters children stack heap dummies
      hypotheses arguments claim node save resolver context declarationArguments endPosition codes result
      formalArguments formalPremises beforeArguments beforeChildren
    all_goals try first | assumption | rfl
    · intro name member
      simp only [List.mem_cons,List.mem_nil_iff,or_false] at member
      rcases member with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        simpa [bound,Subst.lookup] using fresh _ (by simp)

/-- Successful original stack consumption and both original recursive matcher
phases determine the entire application output, including matcher refusal. -/
theorem returns (state : State) (resolver context : Atom) (next arity allocation identifier : Nat)
    (base : List Preterm) (recorded : List Sharing.Entry) (parameters : List Preterm) (children : List (ProofWitness × Atom))
    (remaining heap dummies hypotheses arguments : List Atom) (claim : Preterm) (node : Atom) (save : Bool)
    (formalArguments formalPremises beforeArguments beforeChildren codes : List Atom) (endPosition : Atom)
    (result : Option (List Atom))
    (argumentsPopped : MMBTheoremCommandExecution.Pops .expressions formalArguments.length beforeArguments (some (arguments,beforeChildren)))
    (childrenPopped : MMBTheoremCommandExecution.Pops .proofs formalPremises.length beforeChildren (some (childEntries children,remaining)))
    (claims : MMBProofRunExecution.ExpressionClaims arguments (parameters.map Data.preterm))
    (trace : Match context resolver arguments codes (children.map Prod.snd)
      (expressionValue allocation (Data.preterm claim) node) result) :
    PureReturns program
      (applicationBindings resolver context next arity identifier base recorded formalArguments formalPremises codes
        (expressionValue allocation (Data.preterm claim) node::beforeArguments) heap dummies hypotheses endPosition save)
      state applicationBody state
      (if result.isSome then
        resultValue next arity allocation identifier base recorded parameters (children.map Prod.fst)
          remaining heap dummies hypotheses claim node save
       else .symbol "None") := by
  let earlier := applicationBindings resolver context next arity identifier base recorded formalArguments formalPremises codes
    (expressionValue allocation (Data.preterm claim) node::beforeArguments) heap dummies hypotheses endPosition save
  let bound := ("rest",.expression beforeArguments)::("node",node)::("expression",Data.preterm claim)::("pointer",natural allocation)::earlier
  rw [applicationBody,target_case_shape]
  apply case_returns program earlier bound state state state (.var "stack")
    (.expression (expressionValue allocation (Data.preterm claim) node::beforeArguments)) poppedTarget _ _
    targetCases (read_cases_encoded targetCases)
  · exact variable_returns program earlier state "stack"
  · simp [target_cases_shape,earlier,applicationBindings,expressionValue,SpaceSemantics.selectCase,
      SpaceSemantics.matchValue,SpaceSemantics.matchValue.matchValues,matchAtom,Subst.lookup,bound]
  · apply argument_pop_returns state bound next arity allocation identifier base recorded parameters children remaining heap dummies
      hypotheses arguments claim node save resolver context (listValue formalArguments) endPosition codes result
      formalArguments formalPremises beforeArguments beforeChildren
    all_goals try first | assumption | rfl
    · intro name member
      simp only [List.mem_cons,List.mem_nil_iff,or_false] at member
      rcases member with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        simp [bound,earlier,applicationBindings,Subst.lookup]


/-- An expression-pop refusal is the original `None` observation, with the
same outer execution state and no recorder side effect. -/
theorem arguments_refused_returns (state : State) (resolver context : Atom) (next arity allocation identifier : Nat)
    (base : List Preterm) (recorded : List Sharing.Entry) (formalArguments formalPremises beforeArguments codes heap dummies hypotheses : List Atom)
    (claim : Preterm) (node endPosition : Atom) (save : Bool)
    (popped : MMBTheoremCommandExecution.Pops .expressions formalArguments.length beforeArguments none) :
    PureReturns program
      (applicationBindings resolver context next arity identifier base recorded formalArguments formalPremises codes
        (expressionValue allocation (Data.preterm claim) node::beforeArguments) heap dummies hypotheses endPosition save)
      state applicationBody state (.symbol "None") := by
  let earlier := applicationBindings resolver context next arity identifier base recorded formalArguments formalPremises codes
    (expressionValue allocation (Data.preterm claim) node::beforeArguments) heap dummies hypotheses endPosition save
  let bound := ("rest",.expression beforeArguments)::("node",node)::("expression",Data.preterm claim)::("pointer",natural allocation)::earlier
  rw [applicationBody,target_case_shape]
  apply case_returns program earlier bound state state state (.var "stack")
    (.expression (expressionValue allocation (Data.preterm claim) node::beforeArguments)) poppedTarget _ _
    targetCases (read_cases_encoded targetCases)
  · exact variable_returns program earlier state "stack"
  · simp [target_cases_shape,earlier,applicationBindings,expressionValue,SpaceSemantics.selectCase,
      SpaceSemantics.matchValue,SpaceSemantics.matchValue.matchValues,matchAtom,Subst.lookup,bound]
  · exact argument_pop_refused_returns state bound formalArguments beforeArguments rfl rfl rfl popped

/-- Proof-pop underflow or wrong-kind refusal follows the successful original
expression pop; the partially consumed source stack is not committed. -/
theorem proofs_refused_returns (state : State) (resolver context : Atom) (next arity allocation identifier : Nat)
    (base : List Preterm) (recorded : List Sharing.Entry) (formalArguments formalPremises beforeArguments arguments beforeChildren codes heap dummies hypotheses : List Atom)
    (claim : Preterm) (node endPosition : Atom) (save : Bool)
    (argumentsPopped : MMBTheoremCommandExecution.Pops .expressions formalArguments.length beforeArguments (some (arguments,beforeChildren)))
    (popped : MMBTheoremCommandExecution.Pops .proofs formalPremises.length beforeChildren none) :
    PureReturns program
      (applicationBindings resolver context next arity identifier base recorded formalArguments formalPremises codes
        (expressionValue allocation (Data.preterm claim) node::beforeArguments) heap dummies hypotheses endPosition save)
      state applicationBody state (.symbol "None") := by
  let earlier := applicationBindings resolver context next arity identifier base recorded formalArguments formalPremises codes
    (expressionValue allocation (Data.preterm claim) node::beforeArguments) heap dummies hypotheses endPosition save
  let bound := ("rest",.expression beforeArguments)::("node",node)::("expression",Data.preterm claim)::("pointer",natural allocation)::earlier
  let consumed := ("afterArguments",listValue beforeChildren)::("arguments",listValue arguments)::bound
  rw [applicationBody,target_case_shape]
  apply case_returns program earlier bound state state state (.var "stack")
    (.expression (expressionValue allocation (Data.preterm claim) node::beforeArguments)) poppedTarget _ _
    targetCases (read_cases_encoded targetCases)
  · exact variable_returns program earlier state "stack"
  · simp [target_cases_shape,earlier,applicationBindings,expressionValue,SpaceSemantics.selectCase,
      SpaceSemantics.matchValue,SpaceSemantics.matchValue.matchValues,matchAtom,Subst.lookup,bound]
  · rw [argument_pop_shape]
    apply case_returns program bound consumed state state state _
      (MMBTheoremCommandExecution.poppedValue (some (arguments,beforeChildren))) poppedArguments _ _
      argumentPopCases (read_cases_encoded argumentPopCases)
    · exact computed_pop_returns bound state .expressions formalArguments beforeArguments
        (some (arguments,beforeChildren)) "args" (.expression [.symbol "MM0:L",.var "rest"]) rfl rfl argumentsPopped
    · simp [argument_pop_cases_shape,MMBTheoremCommandExecution.poppedValue,SpaceSemantics.selectCase,
        SpaceSemantics.matchValue,SpaceSemantics.matchValue.matchValues,matchAtom,Subst.lookup,consumed,bound,earlier,
        applicationBindings,optionValue]
    · exact proof_pop_refused_returns state consumed formalPremises beforeChildren rfl rfl rfl popped

/-- Empty input has the source's explicit refusal, not an exhausted budget. -/
theorem empty_refused_returns (state : State) (resolver context : Atom) (next arity identifier : Nat)
    (base : List Preterm) (recorded : List Sharing.Entry) (formalArguments formalPremises codes heap dummies hypotheses : List Atom)
    (endPosition : Atom) (save : Bool) :
    PureReturns program
      (applicationBindings resolver context next arity identifier base recorded formalArguments formalPremises codes
        [] heap dummies hypotheses endPosition save) state applicationBody state (.symbol "None") := by
  let earlier := applicationBindings resolver context next arity identifier base recorded formalArguments formalPremises codes
    [] heap dummies hypotheses endPosition save
  rw [applicationBody,target_case_shape]
  apply case_returns program earlier (("bad",.expression [])::earlier) state state state (.var "stack") (.expression [])
    (.symbol "None") _ _ targetCases (read_cases_encoded targetCases)
  · exact variable_returns program earlier state "stack"
  · simp [target_cases_shape,earlier,applicationBindings,SpaceSemantics.selectCase,
      SpaceSemantics.matchValue,matchAtom,Subst.lookup]
  · exact symbol_returns _ _ _ _

/-- A proved entry at the target position is rejected before either pop or
recording. Its witness tag does not authorize using it as an expression. -/
theorem proved_target_refused_returns (state : State) (resolver context : Atom) (next arity identifier : Nat)
    (base : List Preterm) (recorded : List Sharing.Entry) (formalArguments formalPremises codes rest heap dummies hypotheses : List Atom)
    (witness target endPosition : Atom) (save : Bool) :
    PureReturns program
      (applicationBindings resolver context next arity identifier base recorded formalArguments formalPremises codes
        (provedValue witness target::rest) heap dummies hypotheses endPosition save) state applicationBody state (.symbol "None") := by
  let earlier := applicationBindings resolver context next arity identifier base recorded formalArguments formalPremises codes
    (provedValue witness target::rest) heap dummies hypotheses endPosition save
  rw [applicationBody,target_case_shape]
  apply case_returns program earlier (("bad",.expression (provedValue witness target::rest))::earlier) state state state
    (.var "stack") (.expression (provedValue witness target::rest)) (.symbol "None") _ _ targetCases (read_cases_encoded targetCases)
  · exact variable_returns program earlier state "stack"
  · simp [target_cases_shape,earlier,applicationBindings,provedValue,SpaceSemantics.selectCase,
      SpaceSemantics.matchValue,SpaceSemantics.matchValue.matchValues,matchAtom,Subst.lookup]
  · exact symbol_returns _ _ _ _


/-- Original completed observations retain the whole output state, exact
ordered saved data, one answer and empty I/O. -/
theorem completed_iff (state after : State) (answers inputs outputs : List Atom)
    (resolver context : Atom) (next arity allocation identifier : Nat)
    (base : List Preterm) (recorded : List Sharing.Entry) (parameters : List Preterm) (children : List (ProofWitness × Atom))
    (remaining heap dummies hypotheses arguments : List Atom) (claim : Preterm) (node : Atom) (save : Bool)
    (formalArguments formalPremises beforeArguments beforeChildren codes : List Atom) (endPosition : Atom)
    (result : Option (List Atom))
    (argumentsPopped : MMBTheoremCommandExecution.Pops .expressions formalArguments.length beforeArguments (some (arguments,beforeChildren)))
    (childrenPopped : MMBTheoremCommandExecution.Pops .proofs formalPremises.length beforeChildren (some (childEntries children,remaining)))
    (claims : MMBProofRunExecution.ExpressionClaims arguments (parameters.map Data.preterm))
    (trace : Match context resolver arguments codes (children.map Prod.snd)
      (expressionValue allocation (Data.preterm claim) node) result) :
    (∃ fuel, Eval.run program fuel {state,control := .evaluate (applicationBindings resolver context next arity identifier base recorded formalArguments formalPremises codes
        (expressionValue allocation (Data.preterm claim) node::beforeArguments) heap dummies hypotheses endPosition save) applicationBody} = .complete after answers inputs outputs) ↔
    after = state ∧
      answers = [if result.isSome then resultValue next arity allocation identifier base recorded parameters
        (children.map Prod.fst) remaining heap dummies hypotheses claim node save else .symbol "None"] ∧
      inputs = [] ∧ outputs = [] :=
  pure_returns_completed_iff program _ state state applicationBody _
    (returns state resolver context next arity allocation identifier base recorded parameters children remaining heap dummies hypotheses
      arguments claim node save formalArguments formalPremises beforeArguments beforeChildren codes endPosition result
      argumentsPopped childrenPopped claims trace) after answers inputs outputs

/-- Logical authority for the newly recorded result follows from acceptance of
its complete original chronological submission. Every earlier saved row is
still checked, and arbitrary incoming proved atoms are not validity evidence. -/
theorem source_checked_result_derives (tables : Proof.Tables) (context : Kernel.Context)
    (recorded : List Sharing.Entry) (identifier : Nat) (parameters : List Preterm) (children : List ProofWitness)
    (claim : Preterm) (before after : State) (fuel : Nat) (input : Sharing.Input tables before)
    (completed : Eval.run program fuel
      (Sharing.requestConfiguration before tables context
        (recorded++[⟨some claim,.theoremApp identifier parameters children⟩])
        (.hyp (tables.values.length+recorded.length)) claim) = .complete after [boolean true] [] []) :
    Kernel.Derives (Presentation.ComputationalTyping.signatureOf tables.entries)
      (Unfolding.definitionSignature tables.bodies) (Proof.theoremSignature tables.declarations) context tables.values claim := by
  have checked := (MMBRecordedWitnessAuthority.checked_iff_loaded_source_accepts tables context
    (recorded++[⟨some claim,.theoremApp identifier parameters children⟩])
    (.hyp (tables.values.length+recorded.length)) claim before input).mpr ⟨after,fuel,completed⟩
  apply MMBRecordedWitnessAuthority.claimedScope_derives checked (tables.values.length+recorded.length) claim
  rw [MMBRecordedWitnessAuthority.claimedScope_append,List.getElem?_append_right]
  · simp [MMBRecordedWitnessAuthority.claimedScope]
  · simp [MMBRecordedWitnessAuthority.claimedScope]

end Mettapedia.Languages.MM0.MeTTa.MMBTheoremApplicationExecution
