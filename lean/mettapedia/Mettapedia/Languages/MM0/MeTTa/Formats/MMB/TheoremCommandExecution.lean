import Mettapedia.Languages.MM0.MeTTa.Formats.MMB.TheoremExecution
import Mettapedia.Languages.MeTTa.PeTTa.StdLibCalls

/-!
# Ordered binary theorem-command preparation

These laws follow the original quoted MMB source operations used by theorem
commands. Proof-entry projections preserve every witness and conclusion in
physical order; recording preserves the original saved-proof chronology.
Projection and recording do not validate incoming witnesses. Binary signature
decoding, structural matching and final chronological checking are separate
parts of the complete theorem-command correspondence.
-/

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 800000

namespace Mettapedia.Languages.MM0.MeTTa.MMBTheoremCommandExecution

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst matchAtom)
open Mettapedia.Languages.MeTTa.PeTTa
open Eval
open Effects (State boolean)
open Store (natural)
open ListAccess (listValue optionValue)
open MMBProofRunExecution (stateValue expressionValue provedValue)

abbrev program := MMBTheoremExecution.program

private def sourceEquation (head : String) : SpaceSemantics.Equation :=
  ((MMBExecution.binarySource.program.equations.filter (·.head == head)).head?).getD
    ⟨"", [], .symbol "None"⟩
private def casesOf (body : Atom) : SpaceSemantics.Cases :=
  match body with
  | .expression [_, _, .expression rows] => (readCases rows).getD []
  | _ => []

/-- Which original field of each proved entry is being projected. -/
inductive Projection where
  | witness
  | conclusion
  deriving DecidableEq

private def Projection.head : Projection → String
  | .witness => "mm0:mmb:proof-values"
  | .conclusion => "mm0:mmb:proof-conclusions"
private def Projection.name : Projection → String
  | .witness => "proof"
  | .conclusion => "expression"
def Projection.field : Projection → Atom × Atom → Atom
  | .witness, entry => entry.1
  | .conclusion, entry => entry.2

/-- The actual original proved-entry constructors; their fields are inert data. -/
def provedEntries (entries : List (Atom × Atom)) : List Atom :=
  entries.map fun entry => provedValue entry.1 entry.2

private def valuesEquation (projection : Projection) := sourceEquation projection.head
private def valuesCases (projection : Projection) := casesOf (valuesEquation projection).body
private def valuesCons (projection : Projection) := ((valuesCases projection)[1]'(by cases projection <;> decide)).2
private def valuesConsCases (projection : Projection) := casesOf (valuesCons projection)
private def valuesTail (projection : Projection) := ((valuesConsCases projection)[0]'(by cases projection <;> decide)).2
private def valuesEnvironment (entries : List (Atom × Atom)) : Subst :=
  [("entries", .expression (provedEntries entries))]
private theorem values_unique (projection : Projection) :
    program.equations.filter (·.head == projection.head) = [valuesEquation projection] := by
  cases projection <;> decide +kernel
private theorem values_formals (projection : Projection) : (valuesEquation projection).arguments =
    [.expression [.symbol "MM0:L", .var "entries"]] := by cases projection <;> decide
private theorem values_shape (projection : Projection) : (valuesEquation projection).body =
    .expression [.symbol "case", .var "entries", .expression ((valuesCases projection).map fun row => .expression [row.1, row.2])] := by
  cases projection <;> decide
private theorem values_cases_shape (projection : Projection) : valuesCases projection =
    [(.expression [], .expression [.symbol "Some", .expression [.symbol "MM0:L", .expression []]]),
     (.expression [.symbol "cons", .expression [.symbol "MM0:MMBProved", .var "proof", .var "expression"], .var "rest"],
       valuesCons projection), (.var "bad", .symbol "None")] := by cases projection <;> decide
private theorem values_cons_shape (projection : Projection) : valuesCons projection =
    .expression [.symbol "case", .expression [.symbol projection.head, .expression [.symbol "MM0:L", .var "rest"]],
      .expression ((valuesConsCases projection).map fun row => .expression [row.1, row.2])] := by cases projection <;> decide
private theorem values_cons_cases_shape (projection : Projection) : valuesConsCases projection =
    [(.expression [.symbol "Some", .var "tail"], valuesTail projection), (.var "bad", .symbol "None")] := by
  cases projection <;> decide
private theorem values_tail_shape (projection : Projection) : valuesTail projection =
    .expression [.symbol "let", .var "values", .expression [.symbol "mm0:list-cons", .var projection.name, .var "tail"],
      .expression [.symbol "Some", .var "values"]] := by cases projection <;> decide
private theorem values_clause (projection : Projection) (entries : List (Atom × Atom)) :
    clauses program projection.head [listValue (provedEntries entries)] =
      [.evaluate (valuesEnvironment entries) (valuesEquation projection).body] := by
  rw [clauses_use_only_the_named_equations, values_unique]
  simp [values_formals, valuesEnvironment, listValue, SpaceSemantics.matchValue,
    SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]

private theorem raw_values_from_body (projection : Projection) (bindings : Subst) (state : State)
    (entries : List (Atom × Atom)) (argument : Atom)
    (captured : applySubst bindings argument = listValue (provedEntries entries))
    (body : PureReturns program (valuesEnvironment entries) state (valuesEquation projection).body state
      (optionValue (some (listValue (entries.map projection.field))))) :
    PureReturns program bindings state (.expression [.symbol projection.head, argument]) state
      (optionValue (some (listValue (entries.map projection.field)))) := by
  apply raw_call_returns program bindings state state projection.head [argument] _
    (by cases projection <;> decide +kernel) _ _ (by cases projection <;> decide)
  · intro offset bounded
    have eq : offset = 0 := by simpa using bounded
    subst offset
    cases projection <;> decide +kernel
  · simp only [List.length_cons, List.length_nil, List.map_cons, List.map_nil, captured]
    exact authored_function_arguments_return program bindings (valuesEnvironment entries) state state projection.head
      [listValue (provedEntries entries)] 1 (valuesEquation projection).body _
      (by cases projection <;> decide) (by cases projection <;> decide) (values_clause projection entries) body

private theorem values_body_returns (projection : Projection) (state : State) (entries : List (Atom × Atom)) :
    PureReturns program (valuesEnvironment entries) state (valuesEquation projection).body state
      (optionValue (some (listValue (entries.map projection.field)))) := by
  induction entries with
  | nil =>
      rw [values_shape]
      let bindings := valuesEnvironment []
      apply case_returns program bindings bindings state state state (.var "entries") (.expression [])
        (.expression [.symbol "Some", .expression [.symbol "MM0:L", .expression []]]) _ _
        (valuesCases projection) (read_cases_encoded (valuesCases projection))
      · exact variable_returns program bindings state "entries"
      · simp [values_cases_shape, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
          SpaceSemantics.matchValue.matchValues]
      · apply unary_constructor_of_returns program bindings state state "Some" _ _ (by decide +kernel) (by decide)
        exact empty_constructor_returns program bindings state "MM0:L" (by decide +kernel) (by decide)
  | cons entry entries ih =>
      let bindings := valuesEnvironment (entry :: entries)
      let bound := ("rest", .expression (provedEntries entries)) :: ("expression", entry.2) :: ("proof", entry.1) :: bindings
      let tailed := ("tail", listValue (entries.map projection.field)) :: bound
      let valued := ("values", listValue (projection.field entry :: entries.map projection.field)) :: tailed
      rw [values_shape]
      apply case_returns program bindings bound state state state (.var "entries")
        (.expression (provedEntries (entry :: entries))) (valuesCons projection) _ _
        (valuesCases projection) (read_cases_encoded (valuesCases projection))
      · exact variable_returns program bindings state "entries"
      · simp [values_cases_shape, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
          SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup, bindings, bound,
          valuesEnvironment, provedEntries, provedValue]
      · rw [values_cons_shape]
        apply case_returns program bound tailed state state state _
          (optionValue (some (listValue (entries.map projection.field)))) (valuesTail projection) _ _
          (valuesConsCases projection) (read_cases_encoded (valuesConsCases projection))
        · apply raw_values_from_body projection bound state entries (.expression [.symbol "MM0:L", .var "rest"]) _ ih
          simp [bound, bindings, valuesEnvironment, applySubst, applySubst.applySubstList, Subst.lookup, listValue]
        · simp [values_cons_cases_shape, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
            SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup, tailed, bound,
            bindings, valuesEnvironment, optionValue]
        · rw [values_tail_shape]
          apply let_returns program tailed valued state state state (.var "values") _ _
            (listValue (projection.field entry :: entries.map projection.field)) _
          · apply MMBProofRunExecution.checker_returns (by cases projection <;> decide +kernel)
            apply ListAccess.cons_captured_returns tailed state (projection.field entry)
              (entries.map projection.field) projection.name "tail"
            · cases projection <;> simp [tailed, bound, bindings, valuesEnvironment, Projection.name,
                Projection.field, applySubst, Subst.lookup]
            · simp [tailed, applySubst, Subst.lookup]
          · simp [SpaceSemantics.matchValue, matchAtom, valued, tailed, bound, bindings, valuesEnvironment, Subst.lookup]
          · simpa [valued, applySubst, Subst.lookup, optionValue] using
              unary_constructor_returns program valued state "Some" "values" (by decide +kernel) (by decide)

/-- The original proof-entry projection, preserving all fields in their supplied
order without evaluating or validating their captured contents. -/
theorem proof_projection_returns (projection : Projection) (bindings : Subst) (state : State)
    (entries : List (Atom × Atom)) (argument : Atom)
    (captured : applySubst bindings argument = listValue (provedEntries entries)) :
    PureReturns program bindings state (.expression [.symbol projection.head, argument]) state
      (optionValue (some (listValue (entries.map projection.field)))) :=
  raw_values_from_body projection bindings state entries argument captured (values_body_returns projection state entries)

/-- Witnesses remain in the original physical order, including duplicates. -/
theorem proof_values_returns (bindings : Subst) (state : State) (entries : List (Atom × Atom))
    (argument : Atom) (captured : applySubst bindings argument = listValue (provedEntries entries)) :
    PureReturns program bindings state (.expression [.symbol "mm0:mmb:proof-values", argument]) state
      (optionValue (some (listValue (entries.map Prod.fst)))) :=
  proof_projection_returns .witness bindings state entries argument captured

/-- Conclusions are the original expression-entry atoms, not their preterm
fields; expression-values performs that subsequent projection separately. -/
theorem proof_conclusions_returns (bindings : Subst) (state : State) (entries : List (Atom × Atom))
    (argument : Atom) (captured : applySubst bindings argument = listValue (provedEntries entries)) :
    PureReturns program bindings state (.expression [.symbol "mm0:mmb:proof-conclusions", argument]) state
      (optionValue (some (listValue (entries.map Prod.snd)))) :=
  proof_projection_returns .conclusion bindings state entries argument captured


/-- Exact original save-proof output. The new initializer is not validated
until chronological submission checks it. -/
def saveProofResult (next arity count allocation : Nat)
    (stack heap dummies hypotheses saved : List Atom) (claim node witness : Atom) : Atom :=
  optionValue (some (stateValue next arity count
    (provedValue (Hypothesis.witness (count + saved.length)) (expressionValue allocation claim node) :: stack)
    heap dummies hypotheses (.expression [.symbol "MM0:Saved", optionValue (some claim), witness] :: saved)))

private def saveProofEquation := sourceEquation "mm0:mmb:save-proof"
private def saveProofCases := casesOf saveProofEquation.body
private def saveProofBody := (saveProofCases[0]'(by decide)).2
private def saveEnvironment (next arity count allocation : Nat)
    (stack heap dummies hypotheses saved : List Atom) (claim node witness : Atom) : Subst :=
  [("witness", witness), ("node", node), ("claim", claim), ("id", natural allocation),
    ("saved", listValue saved), ("hyps", listValue hypotheses), ("dummies", listValue dummies),
    ("heap", listValue heap), ("stack", listValue stack), ("count", natural count),
    ("arity", natural arity), ("next", natural next)]
private theorem saveProof_unique : program.equations.filter (·.head == "mm0:mmb:save-proof") = [saveProofEquation] := by
  decide +kernel
private theorem saveProof_formals : saveProofEquation.arguments =
    [.expression [.symbol "MM0:MMBPState", .var "next", .var "arity", .var "count", .var "stack", .var "heap",
      .var "dummies", .var "hyps", .var "saved"],
     .expression [.symbol "MM0:MMBExpression", .var "id", .var "claim", .var "node"], .var "witness"] := by decide
private theorem saveProof_shape : saveProofEquation.body =
    .expression [.symbol "case", .expression [.symbol "mm0:mmu:record-proof", .var "saved", .var "count",
      .expression [.symbol "Some", .var "claim"], .var "witness"],
      .expression (saveProofCases.map fun row => .expression [row.1, row.2])] := by decide
private theorem saveProof_cases_shape : saveProofCases =
    [(.expression [.symbol "Some", .expression [.symbol "MM0:MMUProof", .var "after", .var "root"]], saveProofBody),
     (.var "bad", .symbol "None")] := by decide
private theorem saveProof_body_shape : saveProofBody =
    .expression [.symbol "let", .var "pushed", .expression [.symbol "mm0:list-cons",
      .expression [.symbol "MM0:MMBProved", .var "root",
        .expression [.symbol "MM0:MMBExpression", .var "id", .var "claim", .var "node"]], .var "stack"],
      .expression [.symbol "Some", .expression [.symbol "MM0:MMBPState", .var "next", .var "arity", .var "count",
        .var "pushed", .var "heap", .var "dummies", .var "hyps", .var "after"]]] := by decide
private theorem saveProof_clause (next arity count allocation : Nat)
    (stack heap dummies hypotheses saved : List Atom) (claim node witness : Atom) :
    clauses program "mm0:mmb:save-proof"
      [stateValue next arity count stack heap dummies hypotheses saved, expressionValue allocation claim node, witness] =
      [.evaluate (saveEnvironment next arity count allocation stack heap dummies hypotheses saved claim node witness)
        saveProofEquation.body] := by
  rw [clauses_use_only_the_named_equations, saveProof_unique]
  simp [saveProof_formals, stateValue, expressionValue, listValue, SpaceSemantics.matchValue,
    SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup, saveEnvironment]

private theorem saveProof_body_returns (state : State) (next arity count allocation : Nat)
    (stack heap dummies hypotheses saved : List Atom) (claim node witness : Atom) :
    PureReturns program (saveEnvironment next arity count allocation stack heap dummies hypotheses saved claim node witness)
      state saveProofEquation.body state
      (saveProofResult next arity count allocation stack heap dummies hypotheses saved claim node witness) := by
  let bindings := saveEnvironment next arity count allocation stack heap dummies hypotheses saved claim node witness
  let initializer := Atom.expression [Atom.symbol "MM0:Saved", optionValue (some claim), witness]
  let root := Hypothesis.witness (count + saved.length)
  let target := expressionValue allocation claim node
  let proof := provedValue root target
  let recorded := ("root", root) :: ("after", listValue (initializer :: saved)) :: bindings
  let pushed := ("pushed", listValue (proof :: stack)) :: recorded
  rw [saveProof_shape]
  apply case_returns program bindings recorded state state state _
    (MMBTheoremExecution.recordResult saved count (optionValue (some claim)) witness) saveProofBody _ _
    saveProofCases (read_cases_encoded saveProofCases)
  · let prior : Subst := [("witness", witness), ("goal", optionValue (some claim)), ("count", natural count), ("saved", listValue saved)]
    have returned := MMBTheoremExecution.record_proof_returns prior state saved count (optionValue (some claim)) witness
      "saved" "count" "goal" "witness" rfl rfl rfl rfl
    apply captured_call_returns program prior bindings state state "mm0:mmu:record-proof"
      [.var "saved", .var "count", .var "goal", .var "witness"]
      [.var "saved", .var "count", .expression [.symbol "Some", .var "claim"], .var "witness"] _
      (by decide +kernel) (by decide) _ _ _ returned
    · intro offset argument found
      have bounded : offset < 4 := by
        have inside := (getElem?_eq_some_iff.mp found).choose
        simpa using inside
      interval_cases offset <;> simp at found <;> subst argument <;> right <;> rfl
    · intro offset argument found
      have bounded : offset < 4 := by
        have inside := (getElem?_eq_some_iff.mp found).choose
        simpa using inside
      interval_cases offset
      · simp at found; subst argument; right; rfl
      · simp at found; subst argument; right; rfl
      · left; decide +kernel
      · simp at found; subst argument; right; rfl
    · simp [prior, bindings, saveEnvironment, applySubst, applySubst.applySubstList, Subst.lookup, optionValue]
  · simp [saveProof_cases_shape, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
      SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup, recorded, bindings, saveEnvironment,
      MMBTheoremExecution.recordResult, root, initializer, optionValue]
  · rw [saveProof_body_shape]
    apply let_returns program recorded pushed state state state (.var "pushed") _ _ (listValue (proof :: stack)) _
    · let prior : Subst := [("tail", listValue stack), ("head", proof)]
      have returned := MMBProofRunExecution.checker_returns (by decide +kernel)
        (ListAccess.cons_captured_returns prior state proof stack "head" "tail" rfl rfl)
      apply captured_call_returns program prior recorded state state "mm0:list-cons"
        [.var "head", .var "tail"]
        [.expression [.symbol "MM0:MMBProved", .var "root",
          .expression [.symbol "MM0:MMBExpression", .var "id", .var "claim", .var "node"]], .var "stack"] _
        (by decide +kernel) (by decide) _ _ _ returned
      · intro offset argument found
        have bounded : offset < 2 := by
          have inside := (getElem?_eq_some_iff.mp found).choose
          simpa using inside
        interval_cases offset <;> simp at found <;> subst argument <;> right <;> rfl
      · intro offset argument found
        have bounded : offset < 2 := by
          have inside := (getElem?_eq_some_iff.mp found).choose
          simpa using inside
        interval_cases offset <;> left <;> decide +kernel
      · simp [prior, recorded, bindings, saveEnvironment, proof, provedValue, target, expressionValue,
          applySubst, applySubst.applySubstList, Subst.lookup]
    · simp [SpaceSemantics.matchValue, matchAtom, Subst.lookup, pushed, recorded, bindings, saveEnvironment]
    · apply unary_constructor_of_returns program pushed state state "Some" _ _ (by decide +kernel) (by decide)
      simpa [pushed, recorded, bindings, saveEnvironment, proof, provedValue, target, expressionValue, root, initializer,
        saveProofResult, stateValue, optionValue, applySubst, Subst.lookup] using
        constructor_variables_return program pushed state "MM0:MMBPState"
          ["next", "arity", "count", "pushed", "heap", "dummies", "hyps", "after"] (by decide +kernel) (by decide)

/-- The original source save-proof operation preserves the expression's
allocation and node, remaining stack, heap, dummy and hypothesis data, and every
saved initializer. It does not certify the supplied witness. -/
theorem save_proof_returns (bindings : Subst) (state : State) (next arity count allocation : Nat)
    (stack heap dummies hypotheses saved : List Atom) (claim node witness : Atom)
    (stateName targetName witnessName : String)
    (stateCaptured : applySubst bindings (.var stateName) = stateValue next arity count stack heap dummies hypotheses saved)
    (targetCaptured : applySubst bindings (.var targetName) = expressionValue allocation claim node)
    (witnessCaptured : applySubst bindings (.var witnessName) = witness) :
    PureReturns program bindings state
      (.expression [.symbol "mm0:mmb:save-proof", .var stateName, .var targetName, .var witnessName]) state
      (saveProofResult next arity count allocation stack heap dummies hypotheses saved claim node witness) := by
  apply authored_variable_call_returns program bindings
    (saveEnvironment next arity count allocation stack heap dummies hypotheses saved claim node witness) state state
    "mm0:mmb:save-proof" [stateName, targetName, witnessName] saveProofEquation.body _
    (by decide +kernel) (by decide +kernel) (by decide +kernel) _
    (saveProof_body_returns state next arity count allocation stack heap dummies hypotheses saved claim node witness) (by decide)
  simpa [stateCaptured, targetCaptured, witnessCaptured] using
    saveProof_clause next arity count allocation stack heap dummies hypotheses saved claim node witness


/-- The original theorem command requests one of these two stack entry kinds. -/
inductive StackKind where
  | expressions
  | proofs
  deriving DecidableEq

def StackKind.value : StackKind → Atom
  | .expressions => .symbol "MM0:MMBExpressions"
  | .proofs => .symbol "MM0:MMBProofs"

/-- Source constructor discipline, independent of proof validity and typing. -/
def StackKind.accepts : StackKind → Atom → Bool
  | .expressions, .expression [.symbol "MM0:MMBExpression", _, _, _] => true
  | .proofs, .expression [.symbol "MM0:MMBProved", _, _] => true
  | _, _ => false

/-- Ordered stack consumption: the source stack stores the last authored item
first. Wrong-kind entries and underflow refuse before the remaining suffix is
examined. This relation supplies no logical validity for proved-entry fields. -/
inductive Pops (kind : StackKind) : Nat → List Atom → Option (List Atom × List Atom) → Prop where
  | zero (stack : List Atom) : Pops kind 0 stack (some ([], stack))
  | empty (count : Nat) : Pops kind (count + 1) [] none
  | wrong (count : Nat) (first : Atom) (rest : List Atom)
      (rejected : kind.accepts first = false) : Pops kind (count + 1) (first :: rest) none
  | failed {count : Nat} {first : Atom} {rest : List Atom}
      (accepted : kind.accepts first = true) (earlier : Pops kind count rest none) :
      Pops kind (count + 1) (first :: rest) none
  | next {count : Nat} {first : Atom} {rest items remaining : List Atom}
      (accepted : kind.accepts first = true) (earlier : Pops kind count rest (some (items, remaining))) :
      Pops kind (count + 1) (first :: rest) (some (items ++ [first], remaining))

theorem Pops.total (kind : StackKind) (count : Nat) (stack : List Atom) :
    ∃ result, Pops kind count stack result := by
  induction count generalizing stack with
  | zero => exact ⟨_, .zero stack⟩
  | succ count ih =>
      cases stack with
      | nil => exact ⟨_, .empty count⟩
      | cons first rest =>
          cases accepted : kind.accepts first with
          | false => exact ⟨_, .wrong count first rest accepted⟩
          | true =>
              obtain ⟨result, earlier⟩ := ih rest
              cases result with
              | none => exact ⟨_, .failed accepted earlier⟩
              | some pair => exact ⟨_, .next accepted earlier⟩

/-- Exact physical occurrence count and declaration order, without setification. -/
theorem Pops.ordered {kind : StackKind} {count : Nat} {stack items remaining : List Atom}
    (popped : Pops kind count stack (some (items, remaining))) :
    items.length = count ∧ stack = items.reverse ++ remaining := by
  generalize resultEq : some (items, remaining) = result at popped
  induction popped generalizing items remaining with
  | zero stack =>
      cases resultEq
      simp
  | empty => cases resultEq
  | wrong => cases resultEq
  | failed => cases resultEq
  | @next count first rest earlier leftover accepted popped ih =>
      have same := Option.some.inj resultEq
      cases same
      obtain ⟨length, ordered⟩ := ih rfl
      simp [length, ordered, List.reverse_append]

/-- Readout of the original popped constructor, not another stack evaluator. -/
def poppedValue : Option (List Atom × List Atom) → Atom
  | none => .symbol "None"
  | some (items, remaining) => optionValue (some (.expression [.symbol "MM0:MMBPopped", listValue items, listValue remaining]))

private def popEquation := sourceEquation "mm0:mmb:pop-many"
private def popElse : Atom := match popEquation.body with
  | .expression [_, _, _, no] => no
  | _ => .symbol "None"
private def popCases := casesOf popElse
private def popCons := (popCases[0]'(by decide)).2
private def popAccepted : Atom := match popCons with
  | .expression [_, _, yes, _] => yes
  | _ => .symbol "None"
private def popRecursiveCases := casesOf popAccepted
private def popSuccess := (popRecursiveCases[0]'(by decide)).2
private def popKindCases : SpaceSemantics.Cases :=
  [(.expression [.symbol "MM0:MMBExpressions", .expression [.symbol "MM0:MMBExpression", .var "id", .var "term", .var "node"]], boolean true),
   (.expression [.symbol "MM0:MMBProofs", .expression [.symbol "MM0:MMBProved", .var "proof", .var "expression"]], boolean true),
   (.var "bad", boolean false)]
private def popKindTest : Atom := .expression [.symbol "case", .expression [.var "kind", .var "first"],
  .expression (popKindCases.map fun row => .expression [row.1, row.2])]
private def popEnvironment (kind : StackKind) (count : Nat) (stack : List Atom) : Subst :=
  [("stack", .expression stack), ("count", natural count), ("kind", kind.value)]
private def popBound (kind : StackKind) (count : Nat) (first : Atom) (rest : List Atom) : Subst :=
  ("rest", .expression rest) :: ("first", first) :: popEnvironment kind (count + 1) (first :: rest)
private theorem pop_unique : program.equations.filter (·.head == "mm0:mmb:pop-many") = [popEquation] := by decide +kernel
private theorem pop_formals : popEquation.arguments =
    [.var "kind", .var "count", .expression [.symbol "MM0:L", .var "stack"]] := by decide
private theorem pop_shape : popEquation.body =
    .expression [.symbol "if", .expression [.symbol "==", .var "count", natural 0],
      .expression [.symbol "Some", .expression [.symbol "MM0:MMBPopped",
        .expression [.symbol "MM0:L", .expression []], .expression [.symbol "MM0:L", .var "stack"]]], popElse] := by decide
private theorem pop_else_shape : popElse =
    .expression [.symbol "case", .var "stack", .expression (popCases.map fun row => .expression [row.1, row.2])] := by decide
private theorem pop_cases_shape : popCases =
    [(.expression [.symbol "cons", .var "first", .var "rest"], popCons), (.var "bad", .symbol "None")] := by decide
private theorem pop_cons_shape : popCons =
    .expression [.symbol "if", popKindTest, popAccepted, .symbol "None"] := by decide
private theorem pop_accepted_shape : popAccepted =
    .expression [.symbol "case", .expression [.symbol "mm0:mmb:pop-many", .var "kind",
      .expression [.symbol "-", .var "count", natural 1], .expression [.symbol "MM0:L", .var "rest"]],
      .expression (popRecursiveCases.map fun row => .expression [row.1, row.2])] := by decide
private theorem pop_recursive_cases_shape : popRecursiveCases =
    [(.expression [.symbol "Some", .expression [.symbol "MM0:MMBPopped", .var "earlier", .var "remaining"]], popSuccess),
     (.var "bad", .symbol "None")] := by decide
private theorem pop_success_shape : popSuccess =
    .expression [.symbol "let", .var "items", .expression [.symbol "mm0:mmb:snoc", .var "earlier", .var "first"],
      .expression [.symbol "Some", .expression [.symbol "MM0:MMBPopped", .var "items", .var "remaining"]]] := by decide
private theorem pop_clause (kind : StackKind) (count : Nat) (stack : List Atom) :
    clauses program "mm0:mmb:pop-many" [kind.value, natural count, listValue stack] =
      [.evaluate (popEnvironment kind count stack) popEquation.body] := by
  rw [clauses_use_only_the_named_equations, pop_unique]
  simp [pop_formals, popEnvironment, listValue, SpaceSemantics.matchValue,
    SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]

local macro "pop_selector_finish" : tactic => `(tactic|
  first
  | solve | simp [StackKind.value, StackKind.accepts, popKindCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
      SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup, popBound, popEnvironment]
  | (rename_i name
     by_cases isExpression : name = "MM0:MMBExpression"
     · subst name
       simp [StackKind.value, StackKind.accepts, popKindCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
         SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup, popBound, popEnvironment]
     · by_cases isProof : name = "MM0:MMBProved"
       · subst name
         simp [StackKind.value, StackKind.accepts, popKindCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
           SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup, popBound, popEnvironment]
       · have expressionDifferent := Ne.symm isExpression
         have proofDifferent := Ne.symm isProof
         simp_all [StackKind.value, StackKind.accepts, popKindCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
           SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup, popBound, popEnvironment]))
private theorem pop_kind_selected (kind : StackKind) (count : Nat) (first : Atom) (rest : List Atom) :
    ∃ bindings, SpaceSemantics.selectCase (popBound kind count first rest) (.expression [StackKind.value kind, first]) popKindCases =
      some (bindings, boolean (StackKind.accepts kind first)) := by
  cases kind <;> cases first with
  | symbol value => simp [StackKind.value, StackKind.accepts, popKindCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
      SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup, popBound, popEnvironment]
  | grounded value => simp [StackKind.value, StackKind.accepts, popKindCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
      SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup, popBound, popEnvironment]
  | var value => simp [StackKind.value, StackKind.accepts, popKindCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
      SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup, popBound, popEnvironment]
  | expression xs =>
      rcases xs with _ | ⟨head, xs⟩
      · simp [StackKind.value, StackKind.accepts, popKindCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
          SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup, popBound, popEnvironment]
      rcases xs with _ | ⟨first, xs⟩
      · cases head <;> pop_selector_finish
      rcases xs with _ | ⟨second, xs⟩
      · cases head <;> pop_selector_finish
      rcases xs with _ | ⟨third, xs⟩
      · cases head <;> pop_selector_finish
      rcases xs with _ | ⟨fourth, xs⟩
      · cases head <;> pop_selector_finish
      · cases head <;> pop_selector_finish


private theorem pop_kind_test_returns (state : State) (kind : StackKind) (count : Nat)
    (first : Atom) (rest : List Atom) :
    PureReturns program (popBound kind count first rest) state popKindTest state
      (boolean (kind.accepts first)) := by
  obtain ⟨matched, selected⟩ := pop_kind_selected kind count first rest
  apply case_returns program (popBound kind count first rest) matched state state state
    (.expression [.var "kind", .var "first"]) (.expression [kind.value, first]) (boolean (kind.accepts first)) _ _
    popKindCases (read_cases_encoded popKindCases)
  · simpa [popBound, popEnvironment, applySubst, Subst.lookup] using
      tuple_variables_return program (popBound kind count first rest) state ["kind", "first"]
  · exact selected
  · exact grounded_returns program matched state (.bool (kind.accepts first))

private theorem pop_outer_succ (state : State) (kind : StackKind) (count : Nat)
    (stack : List Atom) (answer : Atom)
    (continued : PureReturns program (popEnvironment kind (count + 1) stack) state popElse state answer) :
    PureReturns program (popEnvironment kind (count + 1) stack) state popEquation.body state answer := by
  let bindings := popEnvironment kind (count + 1) stack
  rw [pop_shape]
  apply if_returns program bindings state state state _ (boolean false) _ _ answer
  · apply native_binary_call_returns program bindings state state state state "==" (.var "count") (natural 0)
      (natural (count + 1)) (natural 0) (boolean false)
      (by decide) (by decide) (by decide +kernel) (by decide +kernel) _ _ _ (by decide)
    · exact variable_returns program bindings state "count"
    · exact grounded_returns program bindings state (.int 0)
    · rw [StdLib.structural_equality, beq_eq_false_iff_ne.mpr (by
        intro same
        have countSame := congrArg MMUResolution.decodeNatural same
        simp [MMUResolution.decodeNatural, natural] at countSame)]
  · change PureReturns program bindings state popElse state answer
    exact continued

private theorem pop_else_cons (state : State) (kind : StackKind) (count : Nat)
    (first : Atom) (rest : List Atom) (answer : Atom)
    (continued : PureReturns program (popBound kind count first rest) state popCons state answer) :
    PureReturns program (popEnvironment kind (count + 1) (first :: rest)) state popElse state answer := by
  rw [pop_else_shape]
  apply case_returns program (popEnvironment kind (count + 1) (first :: rest))
    (popBound kind count first rest) state state state (.var "stack") (.expression (first :: rest)) popCons _ _
    popCases (read_cases_encoded popCases)
  · exact variable_returns program _ state "stack"
  · simp [pop_cases_shape, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
      matchAtom, Subst.lookup, popBound, popEnvironment]
  · exact continued

private theorem pop_recursive_from_body (state : State) (kind : StackKind) (count : Nat)
    (first : Atom) (rest : List Atom) (result : Option (List Atom × List Atom))
    (body : PureReturns program (popEnvironment kind count rest) state popEquation.body state (poppedValue result)) :
    PureReturns program (popBound kind count first rest) state
      (.expression [.symbol "mm0:mmb:pop-many", .var "kind", .expression [.symbol "-", .var "count", natural 1],
        .expression [.symbol "MM0:L", .var "rest"]]) state (poppedValue result) := by
  let bindings := popBound kind count first rest
  apply call_returns program bindings state state "mm0:mmb:pop-many"
    [.var "kind", .expression [.symbol "-", .var "count", natural 1], .expression [.symbol "MM0:L", .var "rest"]]
    (poppedValue result) (by decide +kernel) _ (by decide)
  apply raw_argument_answers program bindings state state "mm0:mmb:pop-many" (.var "kind") _ [] 0 [poppedValue result] (by decide +kernel)
  apply evaluated_argument_returns program bindings state state state (.function "mm0:mmb:pop-many")
    (.expression [.symbol "-", .var "count", natural 1]) (natural count) _ _ _ 1 (by decide +kernel)
  · apply native_binary_call_returns program bindings state state state state "-" (.var "count") (natural 1)
      (natural (count + 1)) (natural 1) (natural count)
      (by decide) (by decide) (by decide +kernel) (by decide +kernel) _ _ _ (by decide)
    · exact variable_returns program bindings state "count"
    · exact grounded_returns program bindings state (.int 1)
    · simp [natural]
  · apply raw_argument_answers program bindings state state "mm0:mmb:pop-many"
      (.expression [.symbol "MM0:L", .var "rest"]) [] _ 2 [poppedValue result] (by decide +kernel)
    simpa [bindings, popBound, popEnvironment, applySubst, applySubst.applySubstList, Subst.lookup, listValue] using
      authored_function_arguments_return program bindings (popEnvironment kind count rest) state state "mm0:mmb:pop-many"
        [kind.value, natural count, listValue rest] 3 popEquation.body (poppedValue result)
        (by decide) (by decide) (pop_clause kind count rest) body

private theorem pop_accepted_body_returns (state : State) (kind : StackKind) (count : Nat)
    (first : Atom) (rest : List Atom) (result : Option (List Atom × List Atom))
    (body : PureReturns program (popEnvironment kind count rest) state popEquation.body state (poppedValue result)) :
    PureReturns program (popBound kind count first rest) state popAccepted state
      (poppedValue (result.map fun pair => (pair.1 ++ [first], pair.2))) := by
  let bindings := popBound kind count first rest
  rw [pop_accepted_shape]
  cases result with
  | none =>
      let rejected := ("bad", Atom.symbol "None") :: bindings
      apply case_returns program bindings rejected state state state _ (.symbol "None") (.symbol "None") _ _
        popRecursiveCases (read_cases_encoded popRecursiveCases)
      · exact pop_recursive_from_body state kind count first rest none body
      · simp [pop_recursive_cases_shape, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
          matchAtom, Subst.lookup, rejected, bindings, popBound, popEnvironment]
      · exact symbol_returns program rejected state "None"
  | some pair =>
      obtain ⟨items, remaining⟩ := pair
      let bound := ("remaining", listValue remaining) :: ("earlier", listValue items) :: bindings
      let appended := ("items", listValue (items ++ [first])) :: bound
      apply case_returns program bindings bound state state state _ (poppedValue (some (items, remaining))) popSuccess _ _
        popRecursiveCases (read_cases_encoded popRecursiveCases)
      · exact pop_recursive_from_body state kind count first rest (some (items, remaining)) body
      · simp [pop_recursive_cases_shape, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
          SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup, bound, bindings, popBound,
          popEnvironment, poppedValue, optionValue]
      · rw [pop_success_shape]
        apply let_returns program bound appended state state state (.var "items") _ _ (listValue (items ++ [first])) _
        · exact MMBProofRunExecution.snoc_returns bound state items first "earlier" "first" rfl rfl
        · simp [SpaceSemantics.matchValue, matchAtom, Subst.lookup, appended, bound, bindings, popBound, popEnvironment]
        · apply unary_constructor_of_returns program appended state state "Some" _ _ (by decide +kernel) (by decide)
          simpa [poppedValue, optionValue, appended, bound, applySubst, Subst.lookup] using
            constructor_variables_return program appended state "MM0:MMBPopped" ["items", "remaining"] (by decide +kernel) (by decide)

private theorem pop_body_returns (state : State) {kind : StackKind} {count : Nat} {stack : List Atom}
    {result : Option (List Atom × List Atom)} (popped : Pops kind count stack result) :
    PureReturns program (popEnvironment kind count stack) state popEquation.body state (poppedValue result) := by
  induction popped with
  | zero stack =>
      let bindings := popEnvironment kind 0 stack
      rw [pop_shape]
      apply if_returns program bindings state state state _ (boolean true) _ _ _
      · apply native_binary_call_returns program bindings state state state state "==" (.var "count") (natural 0)
          (natural 0) (natural 0) (boolean true)
          (by decide) (by decide) (by decide +kernel) (by decide +kernel) _ _ _ (by decide)
        · exact variable_returns program bindings state "count"
        · exact grounded_returns program bindings state (.int 0)
        · rfl
      · change PureReturns program bindings state
          (.expression [.symbol "Some", .expression [.symbol "MM0:MMBPopped",
            .expression [.symbol "MM0:L", .expression []], .expression [.symbol "MM0:L", .var "stack"]]]) state _
        apply unary_constructor_of_returns program bindings state state "Some" _ _ (by decide +kernel) (by decide)
        apply binary_constructor_returns program bindings state state state "MM0:MMBPopped" _ _ _ _ (by decide +kernel) (by decide)
        · exact empty_constructor_returns program bindings state "MM0:L" (by decide +kernel) (by decide)
        · exact unary_constructor_returns program bindings state "MM0:L" "stack" (by decide +kernel) (by decide)
  | empty count =>
      apply pop_outer_succ state kind count [] (.symbol "None")
      let bindings := popEnvironment kind (count + 1) []
      let rejected := ("bad", Atom.expression []) :: bindings
      rw [pop_else_shape]
      apply case_returns program bindings rejected state state state (.var "stack") (.expression []) (.symbol "None") _ _
        popCases (read_cases_encoded popCases)
      · exact variable_returns program bindings state "stack"
      · simp [pop_cases_shape, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom,
          Subst.lookup, rejected, bindings, popEnvironment]
      · exact symbol_returns program rejected state "None"
  | wrong count first rest rejected =>
      apply pop_outer_succ state kind count (first :: rest) (.symbol "None")
      apply pop_else_cons state kind count first rest (.symbol "None")
      rw [pop_cons_shape]
      apply if_returns program (popBound kind count first rest) state state state _ (boolean false) _ _ (.symbol "None")
      · simpa [rejected] using pop_kind_test_returns state kind count first rest
      · exact symbol_returns program _ state "None"
  | @failed count first rest accepted earlier ih =>
      apply pop_outer_succ state kind count (first :: rest) (.symbol "None")
      apply pop_else_cons state kind count first rest (.symbol "None")
      rw [pop_cons_shape]
      apply if_returns program (popBound kind count first rest) state state state _ (boolean true) _ _ (.symbol "None")
      · simpa [accepted] using pop_kind_test_returns state kind count first rest
      · exact pop_accepted_body_returns state kind count first rest none ih
  | @next count first rest items remaining accepted earlier ih =>
      apply pop_outer_succ state kind count (first :: rest) (poppedValue (some (items ++ [first], remaining)))
      apply pop_else_cons state kind count first rest _
      rw [pop_cons_shape]
      apply if_returns program (popBound kind count first rest) state state state _ (boolean true) _ _ _
      · simpa [accepted] using pop_kind_test_returns state kind count first rest
      · exact pop_accepted_body_returns state kind count first rest (some (items, remaining)) ih

/-- The unchanged source pop-many operation, including zero-count identity,
ordered multiplicity, wrong-kind refusal and underflow. -/
theorem pop_many_returns (bindings : Subst) (state : State) (kind : StackKind) (count : Nat)
    (stack : List Atom) (result : Option (List Atom × List Atom))
    (kindName countName stackName : String)
    (kindCaptured : applySubst bindings (.var kindName) = kind.value)
    (countCaptured : applySubst bindings (.var countName) = natural count)
    (stackCaptured : applySubst bindings (.var stackName) = listValue stack)
    (popped : Pops kind count stack result) :
    PureReturns program bindings state (.expression [.symbol "mm0:mmb:pop-many", .var kindName, .var countName, .var stackName])
      state (poppedValue result) := by
  apply authored_variable_call_returns program bindings (popEnvironment kind count stack) state state
    "mm0:mmb:pop-many" [kindName, countName, stackName] popEquation.body _
    (by decide +kernel) (by decide +kernel) (by decide +kernel) _ (pop_body_returns state popped) (by decide)
  simpa [kindCaptured, countCaptured, stackCaptured] using pop_clause kind count stack


/-- Every completed original stack-consumption observation has an independent
Pops derivation. Refusal is a result; budget exhaustion is not one. -/
theorem pop_many_result_iff (bindings : Subst) (state : State) (kind : StackKind) (count : Nat)
    (stack : List Atom) (answer : Atom) (kindName countName stackName : String)
    (kindCaptured : applySubst bindings (.var kindName) = kind.value)
    (countCaptured : applySubst bindings (.var countName) = natural count)
    (stackCaptured : applySubst bindings (.var stackName) = listValue stack) :
    (∃ after fuel, Eval.run program fuel {state, control := .evaluate bindings (.expression
        [.symbol "mm0:mmb:pop-many", .var kindName, .var countName, .var stackName])} =
      .complete after [answer] [] []) ↔
    ∃ result, Pops kind count stack result ∧ answer = poppedValue result := by
  obtain ⟨reference, popped⟩ := Pops.total kind count stack
  have returned := pop_many_returns bindings state kind count stack reference kindName countName stackName
    kindCaptured countCaptured stackCaptured popped
  obtain ⟨referenceFuel, completed⟩ := pure_returns_has_sufficient_fuel program bindings state state _ _ returned
  constructor
  · rintro ⟨after, fuel, observed⟩
    have same := completed_result_unique program referenceFuel fuel _ state after _ [] [] _ [] [] completed observed
    exact ⟨reference, popped, (List.singleton_inj.mp same.2.1).symm⟩
  · rintro ⟨result, operation, same⟩
    obtain ⟨fuel, computed⟩ := pure_returns_has_sufficient_fuel program bindings state state _ _
      (pop_many_returns bindings state kind count stack result kindName countName stackName
        kindCaptured countCaptured stackCaptured operation)
    exact ⟨state, fuel, by simpa only [same] using computed⟩

private theorem accepted_proof_fields (first : Atom) (accepted : StackKind.proofs.accepts first = true) :
    ∃ witness target, first = provedValue witness target := by
  unfold StackKind.accepts at accepted
  split at accepted <;> simp_all [provedValue]

/-- A successful original proof pop supplies exactly the original proved-entry
fields required by both projections. It supplies no proof-validity evidence. -/
theorem Pops.proof_fields {count : Nat} {stack items remaining : List Atom}
    (popped : Pops .proofs count stack (some (items, remaining))) :
    ∃ fields : List (Atom × Atom), items = provedEntries fields := by
  generalize resultEq : some (items, remaining) = result at popped
  induction popped generalizing items remaining with
  | zero stack => cases resultEq; exact ⟨[], rfl⟩
  | empty => cases resultEq
  | wrong => cases resultEq
  | failed => cases resultEq
  | @next count first rest earlier leftover accepted popped ih =>
      have same := Option.some.inj resultEq
      cases same
      obtain ⟨fields, represented⟩ := ih rfl
      obtain ⟨witness, target, same⟩ := accepted_proof_fields first accepted
      exact ⟨fields ++ [(witness, target)], by simp [provedEntries, represented, same]⟩

/-- The concrete proof-stack operation and both original projections form one
complete preparation package. Every physical child is retained in declaration
order; future checking must validate these actual projected witnesses. -/
theorem prepared_proofs_returns (bindings : Subst) (state : State) (count : Nat)
    (stack children remaining : List Atom) (kindName countName stackName childrenName : String)
    (kindCaptured : applySubst bindings (.var kindName) = StackKind.proofs.value)
    (countCaptured : applySubst bindings (.var countName) = natural count)
    (stackCaptured : applySubst bindings (.var stackName) = listValue stack)
    (childrenCaptured : applySubst bindings (.var childrenName) = listValue children)
    (popped : Pops .proofs count stack (some (children, remaining))) :
    ∃ fields : List (Atom × Atom), children = provedEntries fields ∧
      PureReturns program bindings state
        (.expression [.symbol "mm0:mmb:pop-many", .var kindName, .var countName, .var stackName]) state
        (poppedValue (some (children, remaining))) ∧
      PureReturns program bindings state (.expression [.symbol "mm0:mmb:proof-values", .var childrenName]) state
        (optionValue (some (listValue (fields.map Prod.fst)))) ∧
      PureReturns program bindings state (.expression [.symbol "mm0:mmb:proof-conclusions", .var childrenName]) state
        (optionValue (some (listValue (fields.map Prod.snd)))) := by
  obtain ⟨fields, represented⟩ := popped.proof_fields
  have captured : applySubst bindings (.var childrenName) = listValue (provedEntries fields) := by
    simpa only [represented] using childrenCaptured
  exact ⟨fields, represented,
    pop_many_returns bindings state .proofs count stack (some (children, remaining)) kindName countName stackName
      kindCaptured countCaptured stackCaptured popped,
    proof_values_returns bindings state fields (.var childrenName) captured,
    proof_conclusions_returns bindings state fields (.var childrenName) captured⟩

end Mettapedia.Languages.MM0.MeTTa.MMBTheoremCommandExecution
