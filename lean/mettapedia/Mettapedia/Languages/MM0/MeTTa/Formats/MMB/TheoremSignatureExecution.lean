import Mettapedia.Languages.MM0.MeTTa.Formats.MMB.TheoremCommandExecution
import Mettapedia.Languages.MM0.MeTTa.Formats.MMB.SlotExecution
import Mettapedia.Languages.MM0.MeTTa.Formats.MMB.MMBInitializationSoundness
import Mathlib.Data.List.Sort
import Mathlib.Data.List.GetD

/-!
# Binary declaration signature execution

These laws follow the original quoted binary declaration operations. Dependency
ranks select only already available bound-variable positions, in their authored
order. The context operations use the actual preceding MMU maps and create
filled argument slots. These laws cover descriptor images with Boolean binder
flags and natural dependency ranks; they do not replace malformed raw calls by
an invented refusal. Filled-reference child streams follow the original recursive continuations,
and fresh dummies are rejected after each hypothesis. Successful mutually recursive Polish term and child decoding preserves saved
slots and physical command suffixes. Complete refusal correspondence and the
whole theorem-signature join remain separate from checking a supplied proof.
-/

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 800000

namespace Mettapedia.Languages.MM0.MeTTa.MMBTheoremSignatureExecution

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst matchAtom)
open Mettapedia.Languages.MeTTa.PeTTa
open Eval
open Effects (State boolean)
open Store (natural)
open ListAccess (listValue optionValue)

abbrev program := MMBTheoremExecution.program

private def sourceEquation (head : String) : SpaceSemantics.Equation :=
  ((MMBExecution.binarySource.program.equations.filter (·.head == head)).head?).getD
    ⟨"", [], .symbol "None"⟩
private def casesOf (body : Atom) : SpaceSemantics.Cases :=
  match body with
  | .expression [_, _, .expression rows] => (readCases rows).getD []
  | _ => []

/-- The original rank selection, including ordered repeated dependencies and
refusal of a rank outside the current bound-variable prefix. -/
def positions : List Nat → List Atom → Option (List Atom)
  | [], _ => some []
  | rank :: rest, bound =>
      match bound[rank]?, positions rest bound with
      | some position, some tail => some (position :: tail)
      | _, _ => none

private def positionsEquation := sourceEquation "mm0:mmb:positions"
private def positionsCases := casesOf positionsEquation.body
private def positionsCons := (positionsCases[1]'(by decide)).2
private def positionsAfter := match positionsCons with
  | .expression [_, _, body] => body
  | _ => .symbol "None"
private def positionsPairCases := casesOf positionsAfter
private def positionsFound := (positionsPairCases[0]'(by decide)).2
private def positionsEnvironment (ranks : List Nat) (bound : List Atom) : Subst :=
  [("bound", listValue bound), ("ranks", .expression (ranks.map natural))]
private theorem positions_unique :
    program.equations.filter (·.head == "mm0:mmb:positions") = [positionsEquation] := by decide +kernel
private theorem positions_formals : positionsEquation.arguments =
    [.expression [.symbol "MM0:L", .var "ranks"], .var "bound"] := by decide
private theorem positions_shape : positionsEquation.body =
    .expression [.symbol "case", .var "ranks",
      .expression (positionsCases.map fun row => .expression [row.1, row.2])] := by decide
private theorem positions_cases_shape : positionsCases =
    [(.expression [], .expression [.symbol "Some", .expression [.symbol "MM0:L", .expression []]]),
     (.expression [.symbol "cons", .var "rank", .var "rest"], positionsCons),
     (.var "bad", .symbol "None")] := by decide
private theorem positions_cons_shape : positionsCons =
    .expression [.symbol "let*", .expression [
      .expression [.var "first", .expression [.symbol "mm0:data-at", .var "bound", .var "rank"]],
      .expression [.var "tail", .expression [.symbol "mm0:mmb:positions",
        .expression [.symbol "MM0:L", .var "rest"], .var "bound"]]], positionsAfter] := by decide
private theorem positions_after_shape : positionsAfter =
    .expression [.symbol "case", .expression [.var "first", .var "tail"],
      .expression (positionsPairCases.map fun row => .expression [row.1, row.2])] := by decide
private theorem positions_pair_cases : positionsPairCases =
    [(.expression [.expression [.symbol "Some", .var "position"],
        .expression [.symbol "Some", .var "positions"]], positionsFound),
      (.var "bad", .symbol "None")] := by decide
private theorem positions_found_shape : positionsFound =
    .expression [.symbol "let", .var "result",
      .expression [.symbol "mm0:list-cons", .var "position", .var "positions"],
      .expression [.symbol "Some", .var "result"]] := by decide
private theorem positions_clause (ranks : List Nat) (bound : List Atom) :
    clauses program "mm0:mmb:positions" [listValue (ranks.map natural), listValue bound] =
      [.evaluate (positionsEnvironment ranks bound) positionsEquation.body] := by
  rw [clauses_use_only_the_named_equations, positions_unique]
  simp [positions_formals, positionsEnvironment, listValue, SpaceSemantics.matchValue,
    SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]

private theorem positions_raw_from_body (bindings : Subst) (state : State)
    (ranks : List Nat) (bound : List Atom) (ranksArgument boundArgument : Atom)
    (ranksCaptured : applySubst bindings ranksArgument = listValue (ranks.map natural))
    (boundCaptured : applySubst bindings boundArgument = listValue bound)
    (body : PureReturns program (positionsEnvironment ranks bound) state positionsEquation.body state
      (optionValue ((positions ranks bound).map listValue))) :
    PureReturns program bindings state
      (.expression [.symbol "mm0:mmb:positions", ranksArgument, boundArgument]) state
      (optionValue ((positions ranks bound).map listValue)) := by
  apply raw_call_returns program bindings state state "mm0:mmb:positions"
    [ranksArgument, boundArgument] _ (by decide +kernel) _ _ (by decide)
  · intro offset bounded
    have range : offset < 2 := by simpa using bounded
    interval_cases offset <;> decide +kernel
  · simp only [List.map_cons, List.map_nil, ranksCaptured, boundCaptured]
    exact authored_function_arguments_return program bindings (positionsEnvironment ranks bound)
      state state "mm0:mmb:positions" [listValue (ranks.map natural), listValue bound] 2
      positionsEquation.body _ (by decide +kernel) (by decide) (positions_clause ranks bound) body

private theorem positions_body_returns (state : State) (ranks : List Nat) (bound : List Atom) :
    PureReturns program (positionsEnvironment ranks bound) state positionsEquation.body state
      (optionValue ((positions ranks bound).map listValue)) := by
  induction ranks with
  | nil =>
      rw [positions_shape]
      apply case_returns program (positionsEnvironment [] bound) (positionsEnvironment [] bound)
        state state state (.var "ranks") (.expression [])
        (.expression [.symbol "Some", .expression [.symbol "MM0:L", .expression []]]) _ _
        positionsCases (read_cases_encoded positionsCases)
      · exact variable_returns program _ state "ranks"
      · simp [positions_cases_shape, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
          SpaceSemantics.matchValue.matchValues, positionsEnvironment]
      · apply unary_constructor_of_returns program _ state state "Some" _ _ (by decide +kernel) (by decide)
        exact empty_constructor_returns program _ state "MM0:L" (by decide +kernel) (by decide)
  | cons rank rest ih =>
      let bindings := positionsEnvironment (rank :: rest) bound
      let selected := ("rest", .expression (rest.map natural)) :: ("rank", natural rank) :: bindings
      let accessed := ("first", optionValue (bound[rank]?)) :: selected
      let tailed := ("tail", optionValue ((positions rest bound).map listValue)) :: accessed
      rw [positions_shape]
      apply case_returns program bindings selected state state state (.var "ranks")
        (.expression ((rank :: rest).map natural)) positionsCons _ _ positionsCases (read_cases_encoded positionsCases)
      · exact variable_returns program bindings state "ranks"
      · simp [positions_cases_shape, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
          SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup, selected, bindings, positionsEnvironment]
      · rw [positions_cons_shape]
        apply let_star_returns program selected state state _ _ _ _ rfl
        apply let_returns program selected accessed state state state (.var "first") _ _
          (optionValue (bound[rank]?)) _
        · apply MMBProofRunExecution.checker_returns (by decide +kernel)
          apply ListAccess.data_at_list_returns selected state bound rank "bound" "rank"
          all_goals simp [selected, bindings, positionsEnvironment, applySubst, Subst.lookup]
        · simp [SpaceSemantics.matchValue, matchAtom, accessed, selected, bindings, positionsEnvironment, Subst.lookup]
        · apply let_returns program accessed tailed state state state (.var "tail") _ _
            (optionValue ((positions rest bound).map listValue)) _
          · apply positions_raw_from_body accessed state rest bound
              (.expression [.symbol "MM0:L", .var "rest"]) (.var "bound") _ _ ih
            · simp [accessed, selected, bindings, positionsEnvironment, applySubst, applySubst.applySubstList,
                Subst.lookup, listValue]
            · simp [accessed, selected, bindings, positionsEnvironment, applySubst, Subst.lookup]
          · simp [SpaceSemantics.matchValue, matchAtom, tailed, accessed, selected, bindings, positionsEnvironment, Subst.lookup]
          · rw [positions_after_shape]
            have pair : PureReturns program tailed state (.expression [.var "first", .var "tail"]) state
                (.expression [optionValue (bound[rank]?), optionValue ((positions rest bound).map listValue)]) := by
              simpa [tailed, accessed, applySubst, Subst.lookup] using
                tuple_variables_return program tailed state ["first", "tail"]
            cases found : bound[rank]? <;> cases remaining : positions rest bound
            · apply case_returns program tailed (("bad", .expression [.symbol "None", .symbol "None"]) :: tailed)
                state state state _ _ (.symbol "None") _ _ positionsPairCases (read_cases_encoded positionsPairCases)
              · simpa [found, remaining, optionValue] using pair
              · simp [positions_pair_cases, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
                  SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup, tailed, accessed, selected, bindings, positionsEnvironment]
              · simpa [positions, found, remaining, optionValue] using symbol_returns program _ state "None"
            · rename_i tail
              apply case_returns program tailed (("bad", .expression [.symbol "None", optionValue (some (listValue tail))]) :: tailed)
                state state state _ _ (.symbol "None") _ _ positionsPairCases (read_cases_encoded positionsPairCases)
              · simpa [found, remaining, optionValue] using pair
              · simp [positions_pair_cases, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
                  SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup, tailed, accessed, selected, bindings, positionsEnvironment, optionValue]
              · simpa [positions, found, remaining, optionValue] using symbol_returns program _ state "None"
            · rename_i position
              apply case_returns program tailed (("bad", .expression [optionValue (some position), .symbol "None"]) :: tailed)
                state state state _ _ (.symbol "None") _ _ positionsPairCases (read_cases_encoded positionsPairCases)
              · simpa [found, remaining, optionValue] using pair
              · simp [positions_pair_cases, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
                  SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup, tailed, accessed, selected, bindings, positionsEnvironment, optionValue]
              · simpa [positions, found, remaining, optionValue] using symbol_returns program _ state "None"
            · rename_i position tail
              let collected := ("positions", listValue tail) :: ("position", position) :: tailed
              let completed := ("result", listValue (position :: tail)) :: collected
              apply case_returns program tailed collected state state state _ _ positionsFound _ _
                positionsPairCases (read_cases_encoded positionsPairCases)
              · simpa [found, remaining, optionValue] using pair
              · simp [positions_pair_cases, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
                  SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup, tailed, collected, optionValue,
                  accessed, selected, bindings, positionsEnvironment]
              · rw [positions_found_shape]
                apply let_returns program collected completed state state state (.var "result") _ _
                  (listValue (position :: tail)) _
                · apply MMBProofRunExecution.checker_returns (by decide +kernel)
                  exact ListAccess.cons_captured_returns collected state position tail "position" "positions" rfl rfl
                · simp [SpaceSemantics.matchValue, matchAtom, completed, collected, tailed, accessed,
                    selected, bindings, positionsEnvironment, Subst.lookup]
                · simpa [positions, found, remaining, optionValue, completed, applySubst, Subst.lookup] using
                    unary_constructor_returns program completed state "Some" "result" (by decide +kernel) (by decide)

/-- Original dependency resolution, with explicit rejection of missing ranks. -/
theorem positions_returns (bindings : Subst) (state : State) (ranks : List Nat) (bound : List Atom)
    (ranksName boundName : String)
    (ranksCaptured : applySubst bindings (.var ranksName) = listValue (ranks.map natural))
    (boundCaptured : applySubst bindings (.var boundName) = listValue bound) :
    PureReturns program bindings state (.expression [.symbol "mm0:mmb:positions", .var ranksName, .var boundName])
      state (optionValue ((positions ranks bound).map listValue)) :=
  positions_raw_from_body bindings state ranks bound (.var ranksName) (.var boundName)
    ranksCaptured boundCaptured
    (positions_body_returns state ranks bound)


/-- The two chronological maps used by binary signature decoding. -/
inductive ResolverField where
  | sort | term
  deriving DecidableEq

def ResolverField.head : ResolverField → String
  | .sort => "mm0:mmu:sort"
  | .term => "mm0:mmu:term"
private def ResolverField.name : ResolverField → String
  | .sort => "sorts"
  | .term => "terms"
def ResolverField.entries (field : ResolverField) (sorts terms : List MMUResolution.Binding) :
    List MMUResolution.Binding :=
  match field with | .sort => sorts | .term => terms

private def resolverEquation (field : ResolverField) :=
  ((MMUResolution.resolverSource.program.equations.filter (·.head == field.head)).head?).getD
    ⟨"", [], .symbol "None"⟩
private def lookupHead (head : String) : Bool :=
  (MMUResolution.checkerHead head && !head.startsWith "mm0:mmb:") || head == "mm0:mmu:lookup"
private theorem lookup_closed : ProgramClosed lookupHead MMUResolution.program := by
  constructor
  · decide
  · intro equation member supported
    have checked : MMUResolution.program.equations.all (fun equation =>
        !lookupHead equation.head || codeWithin lookupHead equation.body) = true := by decide +kernel
    have body := List.all_eq_true.mp checked equation member
    simpa only [supported, Bool.not_true, Bool.false_or] using body
private theorem lookup_agreement : ProgramAgreementOn lookupHead MMUResolution.program program := by
  change ProgramAgreementOn lookupHead MMUResolution.program
    (MMUResolution.program.append MMBExecution.binarySource.program)
  apply appended_program_agreement
  · intro equation member
    have checked : MMBExecution.binarySource.program.equations.all (fun equation => !lookupHead equation.head) = true := by
      decide +kernel
    have fresh := List.all_eq_true.mp checked equation member
    cases result : lookupHead equation.head <;> simp_all
  · intro head types member
    have checked : MMBExecution.binarySource.program.declarations.all
        (fun declaration => match declaration with
          | .expression [.symbol ":", .symbol name, .expression (.symbol "->" :: _)] => !lookupHead name
          | _ => true) = true := by decide +kernel
    have fresh := List.all_eq_true.mp checked _ member
    cases result : lookupHead head <;> simp_all
private theorem lookup_returns (bindings : Subst) (state : State) (entries : List MMUResolution.Binding)
    (key : Atom) (entriesName keyName : String)
    (entriesCaptured : applySubst bindings (.var entriesName) = MMUResolution.bindingsValue entries)
    (keyCaptured : applySubst bindings (.var keyName) = key) :
    PureReturns program bindings state (.expression [.symbol "mm0:mmu:lookup", .var entriesName, .var keyName]) state
      (optionValue (MMUResolution.lookup entries key)) := by
  apply path_of_closed_agreement lookup_closed lookup_agreement ⟨by simp [controlWithin, codeWithin, atomsWithin, expressionHeadWithin, lookupHead], rfl⟩
  exact MMUResolution.lookup_captured_returns bindings state entries key entriesName keyName entriesCaptured keyCaptured

/-- Exact original resolver constructor. The maps retain physical chronology,
including the original first-binding shadowing convention. -/
def resolverValue (published : Atom) (sorts terms theorems : List MMUResolution.Binding)
    (nextSort nextTerm nextTheorem : Nat) (images : Atom) : Atom :=
  MMBTheoremExecution.resolverValue published (MMUResolution.bindingsValue sorts)
    (MMUResolution.bindingsValue terms) theorems nextSort nextTerm nextTheorem images
private def resolverEnvironment (published : Atom) (sorts terms theorems : List MMUResolution.Binding)
    (nextSort nextTerm nextTheorem : Nat) (images key : Atom) : Subst :=
  [("name", key), ("images", images), ("nh", natural nextTheorem), ("nt", natural nextTerm),
    ("ns", natural nextSort), ("theorems", MMUResolution.bindingsValue theorems),
    ("terms", MMUResolution.bindingsValue terms), ("sorts", MMUResolution.bindingsValue sorts), ("public", published)]
private theorem resolver_unique (field : ResolverField) :
    program.equations.filter (·.head == field.head) = [resolverEquation field] := by cases field <;> decide +kernel
private theorem resolver_formals (field : ResolverField) : (resolverEquation field).arguments =
    [.expression [.symbol "MM0:MMUState", .var "public", .var "sorts", .var "terms", .var "theorems",
      .var "ns", .var "nt", .var "nh", .var "images"], .var "name"] := by cases field <;> decide
private theorem resolver_shape (field : ResolverField) : (resolverEquation field).body =
    .expression [.symbol "mm0:mmu:lookup", .var field.name, .var "name"] := by cases field <;> decide
private theorem resolver_clause (field : ResolverField) (published : Atom)
    (sorts terms theorems : List MMUResolution.Binding) (nextSort nextTerm nextTheorem : Nat) (images key : Atom) :
    clauses program field.head [resolverValue published sorts terms theorems nextSort nextTerm nextTheorem images, key] =
      [.evaluate (resolverEnvironment published sorts terms theorems nextSort nextTerm nextTheorem images key)
        (resolverEquation field).body] := by
  rw [clauses_use_only_the_named_equations, resolver_unique]
  simp [resolver_formals, resolverValue, MMBTheoremExecution.resolverValue, resolverEnvironment,
    SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]

/-- Actual sort and term name resolution; supplied public metadata cannot
substitute for an absent declaration in the current map. -/
theorem resolver_returns (field : ResolverField) (bindings : Subst) (state : State) (published : Atom)
    (sorts terms theorems : List MMUResolution.Binding) (nextSort nextTerm nextTheorem : Nat) (images key : Atom)
    (resolverName keyName : String)
    (resolverCaptured : applySubst bindings (.var resolverName) =
      resolverValue published sorts terms theorems nextSort nextTerm nextTheorem images)
    (keyCaptured : applySubst bindings (.var keyName) = key) :
    PureReturns program bindings state (.expression [.symbol field.head, .var resolverName, .var keyName]) state
      (optionValue (MMUResolution.lookup (field.entries sorts terms) key)) := by
  let inner := resolverEnvironment published sorts terms theorems nextSort nextTerm nextTheorem images key
  have returned : PureReturns program inner state (resolverEquation field).body state
      (optionValue (MMUResolution.lookup (field.entries sorts terms) key)) := by
    rw [resolver_shape]
    apply lookup_returns inner state (field.entries sorts terms) key field.name "name"
    · cases field <;> simp [inner, resolverEnvironment, ResolverField.name, ResolverField.entries, applySubst, Subst.lookup]
    · rfl
  apply authored_variable_call_returns program bindings inner state state field.head
    [resolverName, keyName] (resolverEquation field).body _
    (by cases field <;> decide +kernel) (by cases field <;> decide +kernel) (by cases field <;> decide +kernel)
    _ returned (by cases field <;> decide)
  simpa [resolverCaptured, keyCaptured] using
    resolver_clause field published sorts terms theorems nextSort nextTerm nextTheorem images key


/-- The original binary type descriptor. Dependency ranks remain an ordered
list, so its raw wire representation does not silently remove duplicates. -/
def typeValue (sort : Atom) (isBound : Bool) (ranks : List Nat) : Atom :=
  .expression [.symbol "MM0:MMBType", sort, boolean isBound, listValue (ranks.map natural)]

def typeValues (arguments : List (Atom × Bool × List Nat)) : List Atom :=
  arguments.map fun argument => typeValue argument.1 argument.2.1 argument.2.2

def contextValue (context bound : List Atom) : Atom :=
  .expression [.symbol "MM0:MMBContext", listValue context, listValue bound]

/-- Source-exact context construction. Bound ranks must name the next rank;
regular dependencies may name only positions already in the bound prefix. -/
def contextWalk (sorts : List MMUResolution.Binding) :
    List (Atom × Bool × List Nat) → Nat → List Atom → List Atom → Option (List Atom × List Atom)
  | [], _, bound, context => some (context, bound)
  | (sort, isBound, ranks) :: rest, position, bound, context =>
      match MMUResolution.lookup sorts sort with
      | none => none
      | some id =>
          if isBound then
            if ranks = [bound.length] then
              contextWalk sorts rest (position + 1) (bound ++ [natural position])
                (context ++ [listValue [.symbol "MM0:Bound", id]])
            else none
          else
            match positions ranks bound with
            | none => none
            | some dependencies =>
                contextWalk sorts rest (position + 1) bound
                  (context ++ [listValue [.symbol "MM0:Regular", id, listValue dependencies]])

def contextResult (sorts : List MMUResolution.Binding) (arguments : List (Atom × Bool × List Nat))
    (position : Nat) (bound context : List Atom) : Atom :=
  optionValue ((contextWalk sorts arguments position bound context).map fun value => contextValue value.1 value.2)

private def contextEquation := sourceEquation "mm0:mmb:context-walk"
private def contextCases := casesOf contextEquation.body
private def contextCons := (contextCases[1]'(by decide)).2


private def contextSortCases := casesOf contextCons
private def contextSorted := (contextSortCases[0]'(by decide)).2
private def contextBound := match contextSorted with | .expression [_, _, body, _] => body | _ => .symbol "None"
private def contextRegular := match contextSorted with | .expression [_, _, _, body] => body | _ => .symbol "None"
private def contextRanked := match contextBound with | .expression [_, _, _, body] => body | _ => .symbol "None"
private def contextBoundFound := match contextRanked with | .expression [_, _, body, _] => body | _ => .symbol "None"
private def contextRegularCases := casesOf contextRegular
private def contextRegularFound := (contextRegularCases[0]'(by decide)).2
private def contextEnvironment (resolver : Atom) (arguments : List (Atom × Bool × List Nat))
    (position : Nat) (bound context : List Atom) : Subst :=
  [("context", listValue context), ("bound", .expression bound), ("position", natural position),
    ("arguments", .expression (typeValues arguments)), ("state", resolver)]
private theorem context_unique : program.equations.filter (·.head == "mm0:mmb:context-walk") = [contextEquation] := by
  decide +kernel
private theorem context_formals : contextEquation.arguments =
    [.var "state", .expression [.symbol "MM0:L", .var "arguments"], .var "position",
      .expression [.symbol "MM0:L", .var "bound"], .var "context"] := by decide
private theorem context_shape : contextEquation.body =
    .expression [.symbol "case", .var "arguments", .expression (contextCases.map fun row => .expression [row.1, row.2])] := by decide
private theorem context_cases_shape : contextCases =
    [(.expression [], .expression [.symbol "Some", .expression [.symbol "MM0:MMBContext", .var "context",
        .expression [.symbol "MM0:L", .var "bound"]]]),
     (.expression [.symbol "cons", .expression [.symbol "MM0:MMBType", .var "sort", .var "isBound", .var "ranks"], .var "rest"],
        contextCons), (.var "bad", .symbol "None")] := by decide
private theorem context_cons_shape : contextCons =
    .expression [.symbol "case", .expression [.symbol "mm0:mmu:sort", .var "state", .var "sort"],
      .expression (contextSortCases.map fun row => .expression [row.1, row.2])] := by decide
private theorem context_sort_cases : contextSortCases =
    [(.expression [.symbol "Some", .var "id"], contextSorted), (.var "bad", .symbol "None")] := by decide
private theorem context_sorted_shape : contextSorted =
    .expression [.symbol "if", .var "isBound", contextBound, contextRegular] := by decide
private theorem context_bound_shape : contextBound =
    .expression [.symbol "let", .var "rank", .expression [.symbol "size-atom", .var "bound"], contextRanked] := by decide
private theorem context_ranked_shape : contextRanked =
    .expression [.symbol "if", .expression [.symbol "==", .var "ranks",
      .expression [.symbol "MM0:L", .expression [.var "rank"]]], contextBoundFound, .symbol "None"] := by decide
private theorem context_bound_found_shape : contextBoundFound =
    .expression [.symbol "let*", .expression [
      .expression [.var "binder", .expression [.symbol "MM0:L", .expression [.symbol "MM0:Bound", .var "id"]]],
      .expression [.var "nextContext", .expression [.symbol "mm0:mmb:snoc", .var "context", .var "binder"]],
      .expression [.var "nextBound", .expression [.symbol "mm0:mmb:snoc",
        .expression [.symbol "MM0:L", .var "bound"], .var "position"]]],
      .expression [.symbol "mm0:mmb:context-walk", .var "state", .expression [.symbol "MM0:L", .var "rest"],
        .expression [.symbol "+", .var "position", natural 1], .var "nextBound", .var "nextContext"]] := by decide
private theorem context_regular_shape : contextRegular =
    .expression [.symbol "case", .expression [.symbol "mm0:mmb:positions", .var "ranks",
      .expression [.symbol "MM0:L", .var "bound"]],
      .expression (contextRegularCases.map fun row => .expression [row.1, row.2])] := by decide
private theorem context_regular_cases : contextRegularCases =
    [(.expression [.symbol "Some", .var "dependencies"], contextRegularFound), (.var "bad", .symbol "None")] := by decide
private theorem context_regular_found_shape : contextRegularFound =
    .expression [.symbol "let*", .expression [
      .expression [.var "binder", .expression [.symbol "MM0:L",
        .expression [.symbol "MM0:Regular", .var "id", .var "dependencies"]]],
      .expression [.var "nextContext", .expression [.symbol "mm0:mmb:snoc", .var "context", .var "binder"]]],
      .expression [.symbol "mm0:mmb:context-walk", .var "state", .expression [.symbol "MM0:L", .var "rest"],
        .expression [.symbol "+", .var "position", natural 1], .expression [.symbol "MM0:L", .var "bound"],
        .var "nextContext"]] := by decide
private theorem context_clause (resolver : Atom) (arguments : List (Atom × Bool × List Nat))
    (position : Nat) (bound context : List Atom) :
    clauses program "mm0:mmb:context-walk"
      [resolver, listValue (typeValues arguments), natural position, listValue bound, listValue context] =
      [.evaluate (contextEnvironment resolver arguments position bound context) contextEquation.body] := by
  rw [clauses_use_only_the_named_equations, context_unique]
  simp [context_formals, contextEnvironment, listValue, SpaceSemantics.matchValue,
    SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]

private theorem increment_returns (bindings : Subst) (state : State) (position : Nat) (name : String)
    (captured : applySubst bindings (.var name) = natural position) :
    PureReturns program bindings state (.expression [.symbol "+", .var name, natural 1]) state (natural (position + 1)) := by
  apply native_binary_call_returns program bindings state state state state "+" (.var name) (natural 1)
    (natural position) (natural 1) (natural (position + 1))
    (by decide) (by decide) (by decide) (by decide) _ _ _ (by decide)
  · simpa [captured] using variable_returns program bindings state name
  · exact grounded_returns program bindings state (.int 1)
  · change (.ok (state, [.grounded (.int ((position : Int) + 1))]) : Effects.Result) = .ok (state, [natural (position + 1)])
    simp [natural]

private theorem context_call_from_body (bindings : Subst) (state : State) (resolver : Atom)
    (sorts : List MMUResolution.Binding) (arguments : List (Atom × Bool × List Nat))
    (position : Nat) (bound context : List Atom)
    (stateArgument argumentsArgument positionArgument boundArgument contextArgument : Atom)
    (stateCaptured : applySubst bindings stateArgument = resolver)
    (argumentsCaptured : applySubst bindings argumentsArgument = listValue (typeValues arguments))
    (positionReturned : PureReturns program bindings state positionArgument state (natural position))
    (boundCaptured : applySubst bindings boundArgument = listValue bound)
    (contextCaptured : applySubst bindings contextArgument = listValue context)
    (body : PureReturns program (contextEnvironment resolver arguments position bound context) state
      contextEquation.body state (contextResult sorts arguments position bound context)) :
    PureReturns program bindings state (.expression [.symbol "mm0:mmb:context-walk", stateArgument,
      argumentsArgument, positionArgument, boundArgument, contextArgument]) state
      (contextResult sorts arguments position bound context) := by
  apply call_returns program bindings state state "mm0:mmb:context-walk" _ _ (by decide +kernel) _ (by decide)
  apply raw_argument_answers program bindings state state "mm0:mmb:context-walk" stateArgument _ [] 0
    [_] (by decide +kernel)
  apply raw_argument_answers program bindings state state "mm0:mmb:context-walk" argumentsArgument _ _ 1
    [_] (by decide +kernel)
  apply evaluated_argument_returns program bindings state state state (.function "mm0:mmb:context-walk")
    positionArgument (natural position) _ _ _ 2 (by decide +kernel) positionReturned
  apply raw_arguments_return program bindings state state "mm0:mmb:context-walk"
    [boundArgument, contextArgument] _ 3 _
  · intro offset inside
    have range : offset < 2 := by simpa using inside
    interval_cases offset <;> decide +kernel
  · simp only [List.map_cons, List.map_nil, stateCaptured, argumentsCaptured, boundCaptured, contextCaptured]
    exact authored_function_arguments_return program bindings (contextEnvironment resolver arguments position bound context)
      state state "mm0:mmb:context-walk"
      [resolver, listValue (typeValues arguments), natural position, listValue bound, listValue context] 5
      contextEquation.body _ (by decide +kernel) (by decide)
      (context_clause resolver arguments position bound context) body

private theorem ranks_same (ranks : List Nat) (rank : Nat) :
    ((listValue (ranks.map natural)) == listValue [natural rank]) = decide (ranks = [rank]) := by
  apply Bool.eq_iff_iff.mpr
  simp only [beq_eq_decide, decide_eq_true_eq]
  constructor
  · intro same
    have mapped : ranks.map natural = [rank].map natural := by simpa [listValue] using same
    exact (List.map_injective_iff.mpr Data.natural_injective) mapped
  · rintro rfl; rfl


private theorem snoc_captured_returns (bindings : Subst) (state : State) (items : List Atom) (value : Atom)
    (itemsArgument valueArgument : Atom)
    (itemsCaptured : applySubst bindings itemsArgument = listValue items)
    (valueCaptured : applySubst bindings valueArgument = value) :
    PureReturns program bindings state (.expression [.symbol "mm0:mmb:snoc", itemsArgument, valueArgument]) state
      (listValue (items ++ [value])) := by
  let prior : Subst := [("value", value), ("items", listValue items)]
  have returned := MMBProofRunExecution.snoc_returns prior state items value "items" "value" rfl rfl
  apply captured_call_returns program prior bindings state state "mm0:mmb:snoc"
    [.var "items", .var "value"] [itemsArgument, valueArgument] _ (by decide +kernel) (by decide) _ _ _ returned
  · intro offset argument found
    have range : offset < 2 := by
      have inside := (getElem?_eq_some_iff.mp found).choose
      simpa using inside
    left; interval_cases offset <;> decide +kernel
  · intro offset argument found
    have range : offset < 2 := by
      have inside := (getElem?_eq_some_iff.mp found).choose
      simpa using inside
    left; interval_cases offset <;> decide +kernel
  · simp [prior, applySubst, Subst.lookup, itemsCaptured, valueCaptured]

private theorem context_body_returns (state : State) (published : Atom)
    (sorts terms theorems : List MMUResolution.Binding) (nextSort nextTerm nextTheorem : Nat) (images : Atom)
    (arguments : List (Atom × Bool × List Nat)) (position : Nat) (bound context : List Atom) :
    PureReturns program
      (contextEnvironment (resolverValue published sorts terms theorems nextSort nextTerm nextTheorem images)
        arguments position bound context) state contextEquation.body state (contextResult sorts arguments position bound context) := by
  let resolver := resolverValue published sorts terms theorems nextSort nextTerm nextTheorem images
  induction arguments generalizing position bound context with
  | nil =>
      let bindings := contextEnvironment resolver [] position bound context
      rw [context_shape]
      apply case_returns program bindings bindings state state state (.var "arguments") (.expression [])
        (.expression [.symbol "Some", .expression [.symbol "MM0:MMBContext", .var "context",
          .expression [.symbol "MM0:L", .var "bound"]]]) _ _
        contextCases (read_cases_encoded contextCases)
      · exact variable_returns program bindings state "arguments"
      · simp [context_cases_shape, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
          SpaceSemantics.matchValue.matchValues, bindings, contextEnvironment, typeValues]
      · apply unary_constructor_of_returns program bindings state state "Some" _ _ (by decide +kernel) (by decide)
        apply binary_constructor_returns program bindings state state state "MM0:MMBContext" _ _
          (listValue context) (listValue bound) (by decide +kernel) (by decide)
        · exact variable_returns program bindings state "context"
        · simpa [bindings, contextEnvironment, applySubst, Subst.lookup, listValue] using
            unary_constructor_returns program bindings state "MM0:L" "bound" (by decide +kernel) (by decide)
  | cons argument rest ih =>
      rcases argument with ⟨sort, isBound, ranks⟩
      let bindings := contextEnvironment resolver ((sort, isBound, ranks) :: rest) position bound context
      let selected := ("rest", .expression (typeValues rest)) :: ("ranks", listValue (ranks.map natural)) ::
        ("isBound", boolean isBound) :: ("sort", sort) :: bindings
      rw [context_shape]
      apply case_returns program bindings selected state state state (.var "arguments")
        (.expression (typeValues ((sort, isBound, ranks) :: rest))) contextCons _ _ contextCases (read_cases_encoded contextCases)
      · exact variable_returns program bindings state "arguments"
      · simp [context_cases_shape, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
          SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup, selected, bindings, contextEnvironment,
          typeValues, typeValue]
      · rw [context_cons_shape]
        have resolved := resolver_returns .sort selected state published sorts terms theorems
          nextSort nextTerm nextTheorem images sort "state" "sort" (by rfl) (by rfl)
        cases found : MMUResolution.lookup sorts sort with
        | none =>
            apply case_returns program selected (("bad", .symbol "None") :: selected) state state state _
              (.symbol "None") (.symbol "None") _ _ contextSortCases (read_cases_encoded contextSortCases)
            · simpa [ResolverField.head, ResolverField.entries, found, optionValue] using resolved
            · simp [context_sort_cases, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
                matchAtom, Subst.lookup, selected, bindings, contextEnvironment]
            · simpa [contextResult, contextWalk, found, optionValue] using symbol_returns program _ state "None"
        | some id =>
            let sorted := ("id", id) :: selected
            apply case_returns program selected sorted state state state _ (optionValue (some id)) contextSorted _ _
              contextSortCases (read_cases_encoded contextSortCases)
            · simpa [ResolverField.head, ResolverField.entries, found] using resolved
            · simp [context_sort_cases, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
                SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup, sorted, selected, bindings, contextEnvironment, optionValue]
            · rw [context_sorted_shape]
              apply if_returns program sorted state state state (.var "isBound") (boolean isBound) _ _ _
              · exact variable_returns program sorted state "isBound"
              · cases isBound with
                | true =>
                    simp only [boolean]
                    let ranked := ("rank", natural bound.length) :: sorted
                    rw [context_bound_shape]
                    apply let_returns program sorted ranked state state state (.var "rank") _ _ (natural bound.length) _
                    · apply native_variable_call_returns program sorted state state "size-atom" ["bound"]
                        (natural bound.length) (by decide) (by decide) _ (by decide)
                      rfl
                    · simp [SpaceSemantics.matchValue, matchAtom, ranked, sorted, selected, bindings,
                        contextEnvironment, Subst.lookup]
                    · rw [context_ranked_shape]
                      have comparison : PureReturns program ranked state
                          (.expression [.symbol "==", .var "ranks", .expression [.symbol "MM0:L", .expression [.var "rank"]]]) state
                          (boolean (decide (ranks = [bound.length]))) := by
                        apply native_binary_call_returns program ranked state state state state "==" _ _
                          (listValue (ranks.map natural)) (listValue [natural bound.length]) _
                          (by decide) (by decide) (by decide +kernel) (by decide +kernel) _ _ _ (by decide)
                        · exact variable_returns program ranked state "ranks"
                        · apply MMBProofRunExecution.checker_returns (by decide +kernel)
                          simpa [ranked, applySubst, Subst.lookup] using ListAccess.list_variables_return ranked state ["rank"]
                        · simp only [StdLib.structural_equality, ranks_same]
                      apply if_returns program ranked state state state _ _ _ _ _ comparison
                      by_cases correct : ranks = [bound.length]
                      · simp only [correct, decide_true, boolean]
                        let binder := listValue [.symbol "MM0:Bound", id]
                        let boundBinder := ("binder", binder) :: ranked
                        let nextContext := context ++ [binder]
                        let boundContext := ("nextContext", listValue nextContext) :: boundBinder
                        let nextBound := bound ++ [natural position]
                        let extended := ("nextBound", listValue nextBound) :: boundContext
                        rw [context_bound_found_shape]
                        apply let_star_returns program ranked state state _ _ _ _ rfl
                        apply let_returns program ranked boundBinder state state state (.var "binder") _ _ binder _
                        · apply unary_constructor_of_returns program ranked state state "MM0:L" _ _ (by decide +kernel) (by decide)
                          simpa [binder, listValue, ranked, sorted, applySubst, Subst.lookup] using
                            unary_constructor_returns program ranked state "MM0:Bound" "id" (by decide +kernel) (by decide)
                        · simp [SpaceSemantics.matchValue, matchAtom, boundBinder, ranked, sorted, selected,
                            bindings, contextEnvironment, Subst.lookup]
                        · apply let_returns program boundBinder boundContext state state state (.var "nextContext") _ _
                            (listValue nextContext) _
                          · apply snoc_captured_returns boundBinder state context binder (.var "context") (.var "binder")
                            · rfl
                            · rfl
                          · simp [SpaceSemantics.matchValue, matchAtom, boundContext, boundBinder, ranked,
                              sorted, selected, bindings, contextEnvironment, Subst.lookup]
                          · apply let_returns program boundContext extended state state state (.var "nextBound") _ _
                              (listValue nextBound) _
                            · apply snoc_captured_returns boundContext state bound (natural position)
                                (.expression [.symbol "MM0:L", .var "bound"]) (.var "position")
                              · simp [boundContext, boundBinder, ranked, sorted, selected, bindings, contextEnvironment,
                                  applySubst, applySubst.applySubstList, Subst.lookup, listValue]
                              · rfl
                            · simp [SpaceSemantics.matchValue, matchAtom, extended, boundContext, boundBinder, ranked,
                                sorted, selected, bindings, contextEnvironment, Subst.lookup]
                            · have tail := context_call_from_body extended state resolver sorts rest (position + 1) nextBound nextContext
                                (.var "state") (.expression [.symbol "MM0:L", .var "rest"])
                                (.expression [.symbol "+", .var "position", natural 1]) (.var "nextBound") (.var "nextContext")
                                (by rfl) (by simp [extended, boundContext, boundBinder, ranked, sorted, selected, bindings, contextEnvironment,
                                  applySubst, applySubst.applySubstList, Subst.lookup, listValue])
                                (increment_returns extended state position "position" rfl) rfl (by rfl)
                                (ih (position + 1) nextBound nextContext)
                              simpa [contextResult, contextWalk, found, correct, binder, nextContext, nextBound] using tail
                      · simp only [correct, decide_false, boolean]
                        simpa [contextResult, contextWalk, found, correct, optionValue] using symbol_returns program ranked state "None"
                | false =>
                    simp only [boolean]
                    rw [context_regular_shape]
                    have dependencies := positions_raw_from_body sorted state ranks bound (.var "ranks")
                      (.expression [.symbol "MM0:L", .var "bound"]) rfl
                      (by simp [sorted, selected, bindings, contextEnvironment, applySubst, applySubst.applySubstList,
                        Subst.lookup, listValue]) (positions_body_returns state ranks bound)
                    cases available : positions ranks bound with
                    | none =>
                        apply case_returns program sorted (("bad", .symbol "None") :: sorted) state state state _
                          (.symbol "None") (.symbol "None") _ _ contextRegularCases (read_cases_encoded contextRegularCases)
                        · simpa [available, optionValue] using dependencies
                        · simp [context_regular_cases, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
                            matchAtom, Subst.lookup, sorted, selected, bindings, contextEnvironment]
                        · simpa [contextResult, contextWalk, found, available, optionValue] using symbol_returns program _ state "None"
                    | some values =>
                        let dependent := ("dependencies", listValue values) :: sorted
                        let binder := listValue [.symbol "MM0:Regular", id, listValue values]
                        let boundBinder := ("binder", binder) :: dependent
                        let nextContext := context ++ [binder]
                        let extended := ("nextContext", listValue nextContext) :: boundBinder
                        apply case_returns program sorted dependent state state state _ (optionValue (some (listValue values)))
                          contextRegularFound _ _ contextRegularCases (read_cases_encoded contextRegularCases)
                        · simpa [available] using dependencies
                        · simp [context_regular_cases, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
                            SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup, dependent, sorted, selected,
                            bindings, contextEnvironment, optionValue]
                        · rw [context_regular_found_shape]
                          apply let_star_returns program dependent state state _ _ _ _ rfl
                          apply let_returns program dependent boundBinder state state state (.var "binder") _ _ binder _
                          · apply unary_constructor_of_returns program dependent state state "MM0:L" _ _ (by decide +kernel) (by decide)
                            simpa [binder, listValue, dependent, sorted, applySubst, Subst.lookup] using
                              constructor_variables_return program dependent state "MM0:Regular" ["id", "dependencies"]
                                (by decide +kernel) (by decide)
                          · simp [SpaceSemantics.matchValue, matchAtom, boundBinder, dependent, sorted, selected,
                              bindings, contextEnvironment, Subst.lookup]
                          · apply let_returns program boundBinder extended state state state (.var "nextContext") _ _
                              (listValue nextContext) _
                            · apply snoc_captured_returns boundBinder state context binder (.var "context") (.var "binder") rfl rfl
                            · simp [SpaceSemantics.matchValue, matchAtom, extended, boundBinder, dependent, sorted,
                                selected, bindings, contextEnvironment, Subst.lookup]
                            · have tail := context_call_from_body extended state resolver sorts rest (position + 1) bound nextContext
                                (.var "state") (.expression [.symbol "MM0:L", .var "rest"])
                                (.expression [.symbol "+", .var "position", natural 1]) (.expression [.symbol "MM0:L", .var "bound"])
                                (.var "nextContext") rfl
                                (by simp [extended, boundBinder, dependent, sorted, selected, bindings, contextEnvironment,
                                  applySubst, applySubst.applySubstList, Subst.lookup, listValue])
                                (increment_returns extended state position "position" rfl)
                                (by simp [extended, boundBinder, dependent, sorted, selected, bindings, contextEnvironment,
                                  applySubst, applySubst.applySubstList, Subst.lookup, listValue]) rfl
                                (ih (position + 1) bound nextContext)
                              simpa [contextResult, contextWalk, found, available, binder, nextContext] using tail


/-- The original context walker returns exactly the checked declaration prefix,
or its explicit scope/name refusal. No map lookup or rank check is supplied as
an execution callback. -/
theorem context_walk_returns (bindings : Subst) (state : State) (published : Atom)
    (sorts terms theorems : List MMUResolution.Binding) (nextSort nextTerm nextTheorem : Nat) (images : Atom)
    (arguments : List (Atom × Bool × List Nat)) (position : Nat) (bound context : List Atom)
    (stateName argumentsName positionName boundName contextName : String)
    (stateCaptured : applySubst bindings (.var stateName) =
      resolverValue published sorts terms theorems nextSort nextTerm nextTheorem images)
    (argumentsCaptured : applySubst bindings (.var argumentsName) = listValue (typeValues arguments))
    (positionCaptured : applySubst bindings (.var positionName) = natural position)
    (boundCaptured : applySubst bindings (.var boundName) = listValue bound)
    (contextCaptured : applySubst bindings (.var contextName) = listValue context) :
    PureReturns program bindings state
      (.expression [.symbol "mm0:mmb:context-walk", .var stateName, .var argumentsName,
        .var positionName, .var boundName, .var contextName]) state
      (contextResult sorts arguments position bound context) := by
  exact context_call_from_body bindings state _ sorts arguments position bound context
    (.var stateName) (.var argumentsName) (.var positionName) (.var boundName) (.var contextName)
    stateCaptured argumentsCaptured (by simpa [positionCaptured] using variable_returns program bindings state positionName)
    boundCaptured contextCaptured
    (context_body_returns state published sorts terms theorems nextSort nextTerm nextTheorem images arguments position bound context)

private def contextStartEquation := sourceEquation "mm0:mmb:context"
private def contextStartEnvironment (resolver : Atom) (arguments : List (Atom × Bool × List Nat)) : Subst :=
  [("arguments", listValue (typeValues arguments)), ("state", resolver)]
private theorem context_start_unique :
    program.equations.filter (·.head == "mm0:mmb:context") = [contextStartEquation] := by decide +kernel
private theorem context_start_formals : contextStartEquation.arguments = [.var "state", .var "arguments"] := by decide
private theorem context_start_shape : contextStartEquation.body =
    .expression [.symbol "mm0:mmb:context-walk", .var "state", .var "arguments", natural 0,
      .expression [.symbol "MM0:L", .expression []], .expression [.symbol "MM0:L", .expression []]] := by decide
private theorem context_start_clause (resolver : Atom) (arguments : List (Atom × Bool × List Nat)) :
    clauses program "mm0:mmb:context" [resolver, listValue (typeValues arguments)] =
      [.evaluate (contextStartEnvironment resolver arguments) contextStartEquation.body] := by
  rw [clauses_use_only_the_named_equations, context_start_unique]
  simp [context_start_formals, contextStartEnvironment, SpaceSemantics.matchValue,
    SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]

/-- Fresh declaration contexts start with no bound variables and no binders;
all subsequent dependencies are earned by the original context walker. -/
theorem context_returns (bindings : Subst) (state : State) (published : Atom)
    (sorts terms theorems : List MMUResolution.Binding) (nextSort nextTerm nextTheorem : Nat) (images : Atom)
    (arguments : List (Atom × Bool × List Nat)) (stateName argumentsName : String)
    (stateCaptured : applySubst bindings (.var stateName) =
      resolverValue published sorts terms theorems nextSort nextTerm nextTheorem images)
    (argumentsCaptured : applySubst bindings (.var argumentsName) = listValue (typeValues arguments)) :
    PureReturns program bindings state (.expression [.symbol "mm0:mmb:context", .var stateName, .var argumentsName])
      state (contextResult sorts arguments 0 [] []) := by
  let resolver := resolverValue published sorts terms theorems nextSort nextTerm nextTheorem images
  let inner := contextStartEnvironment resolver arguments
  have body : PureReturns program inner state contextStartEquation.body state (contextResult sorts arguments 0 [] []) := by
    rw [context_start_shape]
    exact context_call_from_body inner state resolver sorts arguments 0 [] [] (.var "state") (.var "arguments")
      (natural 0) (listValue []) (listValue []) rfl rfl (grounded_returns program inner state (.int 0)) rfl rfl
      (context_body_returns state published sorts terms theorems nextSort nextTerm nextTheorem images arguments 0 [] [])
  apply authored_variable_call_returns program bindings inner state state "mm0:mmb:context"
    [stateName, argumentsName] contextStartEquation.body _ (by decide +kernel) (by decide +kernel) (by decide +kernel)
    _ body (by decide)
  simpa [stateCaptured, argumentsCaptured] using context_start_clause resolver arguments


/-- Original unification state constructor; empty and filled slots remain
separate source values. -/
def unifyStateValue (slots dummies : List Atom) (arity : Nat) : Atom :=
  .expression [.symbol "MM0:MMBUState", listValue slots, listValue dummies, natural arity]

/-- Filled argument variables at their original physical positions. -/
def filledVariables (index count : Nat) : List Atom :=
  (List.range' index count).map fun position => optionValue (some (Data.preterm (.var position)))

@[simp] theorem filledVariables_length (index count : Nat) : (filledVariables index count).length = count := by
  simp [filledVariables]

@[simp] theorem filledVariables_getElem? (index count position : Nat) :
    (filledVariables index count)[position]? =
      if position < count then some (optionValue (some (Data.preterm (.var (index + position))))) else none := by
  unfold filledVariables
  rw [List.getElem?_map]
  by_cases inside : position < count
  · rw [List.getElem?_range' inside]
    simp [inside]
  · simp [inside]

/-- Initial decoding state agrees with the original independently authored
statement decoder's argument slots. -/
theorem filledVariables_initial (arity : Nat) :
    filledVariables 0 arity = (Formats.MMB.Statements.initial arity).slots.map (fun slot => optionValue (slot.map Data.preterm)) := by
  simp [filledVariables, Formats.MMB.Statements.initial, List.range_eq_range', List.map_map]

private def variablesEquation := sourceEquation "mm0:mmb:unify-variables"
private def variablesMore := match variablesEquation.body with | .expression [_, _, body, _] => body | _ => .symbol "None"
private def variablesEnvironment (index arity : Nat) (slots : List Atom) : Subst :=
  [("slots", listValue slots), ("arity", natural arity), ("index", natural index)]
private theorem variables_unique : program.equations.filter (·.head == "mm0:mmb:unify-variables") = [variablesEquation] := by
  decide +kernel
private theorem variables_formals : variablesEquation.arguments = [.var "index", .var "arity", .var "slots"] := by decide
private theorem variables_shape : variablesEquation.body =
    .expression [.symbol "if", .expression [.symbol "<", .var "index", .var "arity"], variablesMore,
      .expression [.symbol "MM0:MMBUState", .var "slots", .expression [.symbol "MM0:L", .expression []], .var "arity"]] := by decide
private theorem variables_more_shape : variablesMore =
    .expression [.symbol "let*", .expression [
      .expression [.var "variable", .expression [.symbol "mm0:make-var", .var "index"]],
      .expression [.var "slot", .expression [.symbol "Some", .var "variable"]],
      .expression [.var "next", .expression [.symbol "mm0:mmb:snoc", .var "slots", .var "slot"]]],
      .expression [.symbol "mm0:mmb:unify-variables", .expression [.symbol "+", .var "index", natural 1],
        .var "arity", .var "next"]] := by decide
private theorem variables_clause (index arity : Nat) (slots : List Atom) :
    clauses program "mm0:mmb:unify-variables" [natural index, natural arity, listValue slots] =
      [.evaluate (variablesEnvironment index arity slots) variablesEquation.body] := by
  rw [clauses_use_only_the_named_equations, variables_unique]
  simp [variables_formals, variablesEnvironment, SpaceSemantics.matchValue,
    SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]

private def variableEquation : SpaceSemantics.Equation :=
  ((program.equations.filter (·.head == "mm0:make-var")).head?).getD ⟨"", [], .symbol "None"⟩
private theorem variable_unique : program.equations.filter (·.head == "mm0:make-var") = [variableEquation] := by decide +kernel
private theorem variable_formals : variableEquation.arguments = [.var "index"] := by decide
private theorem variable_body : variableEquation.body = .expression [.symbol "MM0:Var", .var "index"] := by decide
private theorem computed_variable_returns (bindings : Subst) (state : State) (index : Nat) (argument : Atom)
    (computed : PureReturns program bindings state argument state (natural index)) :
    PureReturns program bindings state (.expression [.symbol "mm0:make-var", argument]) state (Data.preterm (.var index)) := by
  let callee : Subst := [("index", natural index)]
  apply call_returns program bindings state state "mm0:make-var" [argument] _ (by decide +kernel) _ (by decide)
  apply evaluated_argument_returns program bindings state state state (.function "mm0:make-var")
    argument (natural index) _ [] [] 0 (by decide +kernel) computed
  apply authored_function_arguments_return program bindings callee state state "mm0:make-var" [natural index] 1
    variableEquation.body _ (by decide +kernel) (by decide) _ _
  · rw [clauses_use_only_the_named_equations, variable_unique]
    simp [variable_formals, callee, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]
  · rw [variable_body]
    simpa [callee, Data.preterm, applySubst, Subst.lookup] using
      unary_constructor_returns program callee state "MM0:Var" "index" (by decide +kernel) (by decide)

private theorem make_var_captured_returns (bindings : Subst) (state : State) (index : Nat) (name : String)
    (captured : applySubst bindings (.var name) = natural index) :
    PureReturns program bindings state (.expression [.symbol "mm0:make-var", .var name]) state (Data.preterm (.var index)) := by
  exact computed_variable_returns bindings state index (.var name)
    (by simpa [captured] using variable_returns program bindings state name)

private theorem variables_call_from_body (bindings : Subst) (state : State) (index arity : Nat) (slots : List Atom)
    (indexArgument : Atom) (arityName slotsName : String) (answer : Atom)
    (indexReturned : PureReturns program bindings state indexArgument state (natural index))
    (arityCaptured : applySubst bindings (.var arityName) = natural arity)
    (slotsCaptured : applySubst bindings (.var slotsName) = listValue slots)
    (body : PureReturns program (variablesEnvironment index arity slots) state variablesEquation.body state answer) :
    PureReturns program bindings state (.expression [.symbol "mm0:mmb:unify-variables", indexArgument,
      .var arityName, .var slotsName]) state answer := by
  apply call_returns program bindings state state "mm0:mmb:unify-variables" _ _ (by decide +kernel) _ (by decide)
  apply evaluated_argument_returns program bindings state state state (.function "mm0:mmb:unify-variables")
    indexArgument (natural index) _ _ [] 0 (by decide +kernel) indexReturned
  have returned := authored_function_arguments_return program bindings (variablesEnvironment index arity slots)
    state state "mm0:mmb:unify-variables" [natural index, natural arity, listValue slots] 3
    variablesEquation.body answer (by decide +kernel) (by decide) (variables_clause index arity slots) body
  apply variable_arguments_return program bindings state state (.function "mm0:mmb:unify-variables")
    [arityName, slotsName] [natural index] 1 answer
  simpa [arityCaptured, slotsCaptured] using returned

private theorem variables_body_returns (state : State) (count index arity : Nat) (slots : List Atom)
    (remaining : arity = index + count) :
    PureReturns program (variablesEnvironment index arity slots) state variablesEquation.body state
      (unifyStateValue (slots ++ filledVariables index count) [] arity) := by
  induction count generalizing index slots with
  | zero =>
      let bindings := variablesEnvironment index arity slots
      have same : arity = index := by omega
      rw [variables_shape]
      apply if_returns program bindings state state state _ (boolean false) _ _ _
      · apply native_variable_call_returns program bindings state state "<" ["index", "arity"]
          (boolean false) (by decide) (by decide) _ (by decide)
        change (.ok (state, [boolean ((index : Int) < (arity : Int))]) : Effects.Result) = .ok (state, [boolean false])
        simp [same, boolean]
      · simp only [boolean]
        apply data_call_returns program bindings state state "MM0:MMBUState" _ _ (by decide +kernel) _ (by decide)
        apply evaluated_argument_returns program bindings state state state .data (.symbol "MM0:MMBUState")
          (.symbol "MM0:MMBUState") _ _ [] 0 rfl (symbol_returns program bindings state "MM0:MMBUState")
        apply evaluated_argument_returns program bindings state state state .data (.var "slots") (listValue slots)
          _ _ [.symbol "MM0:MMBUState"] 1 rfl (variable_returns program bindings state "slots")
        apply evaluated_argument_returns program bindings state state state .data (.expression [.symbol "MM0:L", .expression []])
          (listValue []) _ _ _ 2 rfl (empty_constructor_returns program bindings state "MM0:L" (by decide +kernel) (by decide))
        apply evaluated_argument_returns program bindings state state state .data (.var "arity") (natural arity)
          _ [] _ 3 rfl (by exact variable_returns program bindings state "arity")
        simpa [unifyStateValue, filledVariables, listValue] using data_arguments_values_return program bindings state
          [.symbol "MM0:MMBUState", listValue slots, listValue [], natural arity] 4
  | succ count ih =>
      let bindings := variablesEnvironment index arity slots
      let created := ("variable", Data.preterm (.var index)) :: bindings
      let slot := optionValue (some (Data.preterm (.var index)))
      let slotted := ("slot", slot) :: created
      let next := slots ++ [slot]
      let appended := ("next", listValue next) :: slotted
      rw [variables_shape]
      apply if_returns program bindings state state state _ (boolean true) _ _ _
      · apply native_variable_call_returns program bindings state state "<" ["index", "arity"]
          (boolean true) (by decide) (by decide) _ (by decide)
        change (.ok (state, [boolean ((index : Int) < (arity : Int))]) : Effects.Result) = .ok (state, [boolean true])
        have less : (index : Int) < (arity : Int) := by omega
        simp [less, boolean]
      · simp only [boolean]
        rw [variables_more_shape]
        apply let_star_returns program bindings state state _ _ _ _ rfl
        apply let_returns program bindings created state state state (.var "variable") _ _ (Data.preterm (.var index)) _
        · exact make_var_captured_returns bindings state index "index" rfl
        · simp [SpaceSemantics.matchValue, matchAtom, created, bindings, variablesEnvironment, Subst.lookup]
        · apply let_returns program created slotted state state state (.var "slot") _ _ slot _
          · simpa [slot, optionValue, created, applySubst, Subst.lookup] using
              unary_constructor_returns program created state "Some" "variable" (by decide +kernel) (by decide)
          · simp [SpaceSemantics.matchValue, matchAtom, slotted, created, bindings, variablesEnvironment, Subst.lookup]
          · apply let_returns program slotted appended state state state (.var "next") _ _ (listValue next) _
            · exact snoc_captured_returns slotted state slots slot (.var "slots") (.var "slot") rfl rfl
            · simp [SpaceSemantics.matchValue, matchAtom, appended, slotted, created, bindings, variablesEnvironment, Subst.lookup]
            · have tail := variables_call_from_body appended state (index + 1) arity next
                (.expression [.symbol "+", .var "index", natural 1]) "arity" "next" _
                (increment_returns appended state index "index" rfl) rfl rfl (ih (index + 1) next (by omega))
              simpa [next, slot, filledVariables, List.range'_succ, List.append_assoc] using tail

/-- The actual original initializer creates one filled variable slot per formal
argument, in order, with no dummy allocation. -/
theorem unify_variables_returns (bindings : Subst) (state : State) (index count arity : Nat) (slots : List Atom)
    (remaining : arity = index + count) (indexName arityName slotsName : String)
    (indexCaptured : applySubst bindings (.var indexName) = natural index)
    (arityCaptured : applySubst bindings (.var arityName) = natural arity)
    (slotsCaptured : applySubst bindings (.var slotsName) = listValue slots) :
    PureReturns program bindings state
      (.expression [.symbol "mm0:mmb:unify-variables", .var indexName, .var arityName, .var slotsName]) state
      (unifyStateValue (slots ++ filledVariables index count) [] arity) :=
  variables_call_from_body bindings state index arity slots (.var indexName) arityName slotsName _
    (by simpa [indexCaptured] using variable_returns program bindings state indexName)
    arityCaptured slotsCaptured (variables_body_returns state count index arity slots remaining)


private def initialEquation := sourceEquation "mm0:mmb:unify-initial"
private def initialEnvironment (arity : Nat) : Subst := [("arity", natural arity)]
private theorem initial_unique : program.equations.filter (·.head == "mm0:mmb:unify-initial") = [initialEquation] := by
  decide +kernel
private theorem initial_formals : initialEquation.arguments = [.var "arity"] := by decide
private theorem initial_shape : initialEquation.body =
    .expression [.symbol "mm0:mmb:unify-variables", natural 0, .var "arity", .expression [.symbol "MM0:L", .expression []]] := by decide
private theorem initial_clause (arity : Nat) :
    clauses program "mm0:mmb:unify-initial" [natural arity] = [.evaluate (initialEnvironment arity) initialEquation.body] := by
  rw [clauses_use_only_the_named_equations, initial_unique]
  simp [initial_formals, initialEnvironment, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
    matchAtom, Subst.lookup]
private theorem initial_body_returns (state : State) (arity : Nat) :
    PureReturns program (initialEnvironment arity) state initialEquation.body state
      (unifyStateValue (filledVariables 0 arity) [] arity) := by
  rw [initial_shape]
  let prior := variablesEnvironment 0 arity []
  have returned := unify_variables_returns prior state 0 arity arity [] (by omega)
    "index" "arity" "slots" rfl rfl rfl
  apply captured_call_returns program prior (initialEnvironment arity) state state "mm0:mmb:unify-variables"
    [.var "index", .var "arity", .var "slots"] [natural 0, .var "arity", listValue []] _
    (by decide +kernel) (by decide) _ _ _ returned
  · intro offset argument found
    have range : offset < 3 := by
      have inside := (getElem?_eq_some_iff.mp found).choose
      simpa using inside
    interval_cases offset <;> simp at found <;> subst argument <;> right <;> rfl
  · intro offset argument found
    have range : offset < 3 := by
      have inside := (getElem?_eq_some_iff.mp found).choose
      simpa using inside
    interval_cases offset
    · simp at found; subst argument; right; rfl
    · simp at found; subst argument; right; rfl
    · left; decide +kernel
  · simp [prior, variablesEnvironment, initialEnvironment, applySubst, applySubst.applySubstList,
      Subst.lookup, natural, listValue]

/-- Source initializer execution, including the zero-argument context. All
argument slots are filled before declaration expression decoding begins. -/
theorem unify_initial_returns (bindings : Subst) (state : State) (arity : Nat) (arityName : String)
    (arityCaptured : applySubst bindings (.var arityName) = natural arity) :
    PureReturns program bindings state (.expression [.symbol "mm0:mmb:unify-initial", .var arityName]) state
      (unifyStateValue (filledVariables 0 arity) [] arity) := by
  apply authored_variable_call_returns program bindings (initialEnvironment arity) state state "mm0:mmb:unify-initial"
    [arityName] initialEquation.body _ (by decide +kernel) (by decide +kernel) (by decide +kernel)
    _ (initial_body_returns state arity) (by decide)
  simpa [arityCaptured] using initial_clause arity

/-- Future dependency ranks are rejected regardless of the other requested
ranks; this is an explicit source refusal rather than a default position. -/
theorem positions_future_refused (bound : List Atom) (rank : Nat) (rest : List Nat) (future : bound.length ≤ rank) :
    positions (rank :: rest) bound = none := by
  simp [positions, List.getElem?_eq_none future]

/-- Context execution can be resumed with any additional evaluator fuel once
its proved pure computation completes. This is not a physical runtime bound. -/
theorem context_sufficient_fuel (bindings : Subst) (state : State) (published : Atom)
    (sorts terms theorems : List MMUResolution.Binding) (nextSort nextTerm nextTheorem : Nat) (images : Atom)
    (arguments : List (Atom × Bool × List Nat)) (stateName argumentsName : String)
    (stateCaptured : applySubst bindings (.var stateName) =
      resolverValue published sorts terms theorems nextSort nextTerm nextTheorem images)
    (argumentsCaptured : applySubst bindings (.var argumentsName) = listValue (typeValues arguments)) :
    ∃ fuel, ∀ extra, run program (fuel + extra)
      {state, control := .evaluate bindings (.expression [.symbol "mm0:mmb:context", .var stateName, .var argumentsName])} =
      .complete state [contextResult sorts arguments 0 [] []] [] [] := by
  obtain ⟨fuel, completed⟩ := pure_returns_has_sufficient_fuel program bindings state state _ _
    (context_returns bindings state published sorts terms theorems nextSort nextTerm nextTheorem images
      arguments stateName argumentsName stateCaptured argumentsCaptured)
  exact ⟨fuel, fun extra => completed_run_more_fuel program fuel extra _ state _ [] [] completed⟩

/-- The initial filled-slot computation preserves the entire loaded state,
with the original completed/refused/exhausted evaluator observations. -/
theorem unify_initial_sufficient_fuel (bindings : Subst) (state : State) (arity : Nat) (arityName : String)
    (arityCaptured : applySubst bindings (.var arityName) = natural arity) :
    ∃ fuel, ∀ extra, run program (fuel + extra)
      {state, control := .evaluate bindings (.expression [.symbol "mm0:mmb:unify-initial", .var arityName])} =
      .complete state [unifyStateValue (filledVariables 0 arity) [] arity] [] [] := by
  obtain ⟨fuel, completed⟩ := pure_returns_has_sufficient_fuel program bindings state state _ _
    (unify_initial_returns bindings state arity arityName arityCaptured)
  exact ⟨fuel, fun extra => completed_run_more_fuel program fuel extra _ state _ [] [] completed⟩


/-- A regular descriptor cannot obtain a dependency missing from the currently
available bound prefix, even if later descriptors would introduce it. -/
theorem contextWalk_missing_dependency_refused (sorts : List MMUResolution.Binding) (sort : Atom)
    (ranks : List Nat) (rest : List (Atom × Bool × List Nat)) (position : Nat) (bound context : List Atom)
    (missing : positions ranks bound = none) :
    contextWalk sorts ((sort, false, ranks) :: rest) position bound context = none := by
  cases found : MMUResolution.lookup sorts sort <;> simp [contextWalk, found, missing]

/-- A bound descriptor must declare exactly its next bound rank. -/
theorem contextWalk_wrong_bound_rank_refused (sorts : List MMUResolution.Binding) (sort : Atom)
    (ranks : List Nat) (rest : List (Atom × Bool × List Nat)) (position : Nat) (bound context : List Atom)
    (wrong : ranks ≠ [bound.length]) :
    contextWalk sorts ((sort, true, ranks) :: rest) position bound context = none := by
  cases found : MMUResolution.lookup sorts sort <;> simp [contextWalk, found, wrong]


/-- The original table container. Fields remain inert; this operation does not
admit a term declaration or confer authority on an unavailable table row. -/
def tablesValue (sorts terms theorems : Atom) : Atom :=
  .expression [.symbol "MM0:MMBTables", sorts, terms, theorems]

/-- The complete source expression result retains the updated slot state and
the exact unread command tail. -/
def unifyExpressionValue (expression : Atom) (slots dummies : List Atom) (arity : Nat)
    (rest : List Atom) : Atom :=
  .expression [.symbol "MM0:MMBUExpression", expression,
    unifyStateValue slots dummies arity, listValue rest]

private def expressionEquation := sourceEquation "mm0:mmb:unify-expression"
private def expressionThen := match expressionEquation.body with
  | .expression [_, _, body, _] => body
  | _ => .symbol "None"
private def expressionCases := casesOf expressionThen
private def expressionOpcode := (expressionCases[0]'(by decide)).2
private def expressionOpcodeCases := casesOf expressionOpcode
private def expressionReference := (expressionOpcodeCases[2]'(by decide)).2
private def expressionReferenceCases := casesOf expressionReference
private def expressionReferenceFound := (expressionReferenceCases[0]'(by decide)).2
private def expressionNoSave := (expressionOpcodeCases[0]'(by decide)).2
private def expressionSave := (expressionOpcodeCases[1]'(by decide)).2
private def expressionDummy := (expressionOpcodeCases[3]'(by decide)).2
private def expressionEnvironment (resolver sorts terms theorems : Atom) (fuel : Nat)
    (slots dummies : List Atom) (arity : Nat) (codes : List Atom) : Subst :=
  [("codes", .expression codes), ("arity", natural arity), ("dummies", .expression dummies),
   ("slots", .expression slots), ("fuel", natural fuel), ("theorems", theorems),
   ("terms", terms), ("sorts", sorts), ("state", resolver)]
private def expressionReferenceEnvironment (resolver sorts terms theorems : Atom) (fuel index start after : Nat)
    (slots dummies : List Atom) (arity : Nat) (rest : List Atom) : Subst :=
  ("rest", .expression rest) :: ("after", natural after) :: ("start", natural start) ::
  ("data", natural index) :: ("opcode", natural 50) ::
    expressionEnvironment resolver sorts terms theorems (fuel + 1) slots dummies arity
      (MMBExecution.commandValue 50 index start after :: rest)

private theorem expression_unique :
    program.equations.filter (·.head == "mm0:mmb:unify-expression") = [expressionEquation] := by decide +kernel
private theorem expression_formals : expressionEquation.arguments =
    [.var "state", .expression [.symbol "MM0:MMBTables", .var "sorts", .var "terms", .var "theorems"],
     .var "fuel", .expression [.symbol "MM0:MMBUState", .expression [.symbol "MM0:L", .var "slots"],
       .expression [.symbol "MM0:L", .var "dummies"], .var "arity"],
     .expression [.symbol "MM0:L", .var "codes"]] := by decide
private theorem expression_shape : expressionEquation.body =
    .expression [.symbol "if", .expression [.symbol "<", natural 0, .var "fuel"],
      expressionThen, .symbol "None"] := by decide
private theorem expression_then_shape : expressionThen =
    .expression [.symbol "case", .var "codes", .expression (expressionCases.map fun row => .expression [row.1, row.2])] := by decide
private theorem expression_cases_shape : expressionCases =
    [(.expression [.symbol "cons", .expression [.symbol "MM0:MMBCode", .var "opcode", .var "data", .var "start", .var "after"],
      .var "rest"], expressionOpcode), (.var "bad", .symbol "None")] := by decide
private theorem expression_opcode_shape : expressionOpcode =
    .expression [.symbol "case", .var "opcode", .expression (expressionOpcodeCases.map fun row => .expression [row.1, row.2])] := by decide
private theorem expression_opcode_cases : expressionOpcodeCases =
    [(natural 48, expressionNoSave), (natural 49, expressionSave), (natural 50, expressionReference),
      (natural 51, expressionDummy), (.var "bad", .symbol "None")] := by decide
private theorem expression_reference_shape : expressionReference =
    .expression [.symbol "case", .expression [.symbol "mm0:data-at", .expression [.symbol "MM0:L", .var "slots"], .var "data"],
      .expression (expressionReferenceCases.map fun row => .expression [row.1, row.2])] := by decide
private theorem expression_reference_cases : expressionReferenceCases =
    [(.expression [.symbol "Some", .expression [.symbol "Some", .var "expression"]], expressionReferenceFound),
      (.var "bad", .symbol "None")] := by decide
private theorem expression_reference_found_shape : expressionReferenceFound =
    .expression [.symbol "Some", .expression [.symbol "MM0:MMBUExpression", .var "expression",
      .expression [.symbol "MM0:MMBUState", .expression [.symbol "MM0:L", .var "slots"],
        .expression [.symbol "MM0:L", .var "dummies"], .var "arity"],
      .expression [.symbol "MM0:L", .var "rest"]]] := by decide
private theorem expression_clause (resolver sorts terms theorems : Atom) (fuel : Nat)
    (slots dummies : List Atom) (arity : Nat) (codes : List Atom) :
    clauses program "mm0:mmb:unify-expression" [resolver, tablesValue sorts terms theorems, natural fuel,
      unifyStateValue slots dummies arity, listValue codes] =
      [.evaluate (expressionEnvironment resolver sorts terms theorems fuel slots dummies arity codes) expressionEquation.body] := by
  rw [clauses_use_only_the_named_equations, expression_unique]
  simp [expression_formals, expressionEnvironment, tablesValue, unifyStateValue, listValue,
    SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]

private theorem expression_call_from_body (bindings : Subst) (state : State)
    (resolver sorts terms theorems : Atom) (fuel : Nat) (slots dummies : List Atom) (arity : Nat)
    (codes : List Atom) (answer : Atom)
    (resolverArgument tablesArgument fuelArgument unifyArgument codesArgument : Atom)
    (resolverCaptured : applySubst bindings resolverArgument = resolver)
    (tablesCaptured : applySubst bindings tablesArgument = tablesValue sorts terms theorems)
    (fuelReturned : PureReturns program bindings state fuelArgument state (natural fuel))
    (unifyCaptured : applySubst bindings unifyArgument = unifyStateValue slots dummies arity)
    (codesCaptured : applySubst bindings codesArgument = listValue codes)
    (body : PureReturns program (expressionEnvironment resolver sorts terms theorems fuel slots dummies arity codes)
      state expressionEquation.body state answer) :
    PureReturns program bindings state (.expression [.symbol "mm0:mmb:unify-expression", resolverArgument,
      tablesArgument, fuelArgument, unifyArgument, codesArgument]) state answer := by
  apply call_returns program bindings state state "mm0:mmb:unify-expression" _ _ (by decide +kernel) _ (by decide)
  apply raw_argument_answers program bindings state state "mm0:mmb:unify-expression" resolverArgument _ [] 0
    [_] (by decide +kernel)
  apply raw_argument_answers program bindings state state "mm0:mmb:unify-expression" tablesArgument _ _ 1
    [_] (by decide +kernel)
  apply evaluated_argument_returns program bindings state state state (.function "mm0:mmb:unify-expression")
    fuelArgument (natural fuel) _ _ _ 2 (by decide +kernel) fuelReturned
  apply raw_arguments_return program bindings state state "mm0:mmb:unify-expression"
    [unifyArgument, codesArgument] _ 3 _
  · intro offset inside
    have range : offset < 2 := by simpa using inside
    interval_cases offset <;> decide +kernel
  · simp only [List.map_cons, List.map_nil, resolverCaptured, tablesCaptured, unifyCaptured, codesCaptured]
    exact authored_function_arguments_return program bindings
      (expressionEnvironment resolver sorts terms theorems fuel slots dummies arity codes) state state
      "mm0:mmb:unify-expression" [resolver, tablesValue sorts terms theorems, natural fuel,
        unifyStateValue slots dummies arity, listValue codes] 5 expressionEquation.body _
      (by decide +kernel) (by decide)
      (expression_clause resolver sorts terms theorems fuel slots dummies arity codes) body

private theorem expression_from_body (bindings : Subst) (state : State) (resolver sorts terms theorems : Atom) (fuel : Nat)
    (slots dummies : List Atom) (arity : Nat) (codes : List Atom) (answer : Atom)
    (resolverName tablesName fuelName unifyName codesName : String)
    (resolverCaptured : applySubst bindings (.var resolverName) = resolver)
    (tablesCaptured : applySubst bindings (.var tablesName) = tablesValue sorts terms theorems)
    (fuelCaptured : applySubst bindings (.var fuelName) = natural fuel)
    (unifyCaptured : applySubst bindings (.var unifyName) = unifyStateValue slots dummies arity)
    (codesCaptured : applySubst bindings (.var codesName) = listValue codes)
    (body : PureReturns program (expressionEnvironment resolver sorts terms theorems fuel slots dummies arity codes)
      state expressionEquation.body state answer) :
    PureReturns program bindings state (.expression [.symbol "mm0:mmb:unify-expression", .var resolverName,
      .var tablesName, .var fuelName, .var unifyName, .var codesName]) state answer := by
  exact expression_call_from_body bindings state resolver sorts terms theorems fuel slots dummies arity codes answer
    (.var resolverName) (.var tablesName) (.var fuelName) (.var unifyName) (.var codesName)
    resolverCaptured tablesCaptured
    (by simpa [fuelCaptured] using variable_returns program bindings state fuelName)
    unifyCaptured codesCaptured body

private theorem unify_constructor_returns (bindings : Subst) (state : State)
    (slots dummies : List Atom) (arity : Nat)
    (slotsCaptured : applySubst bindings (.var "slots") = .expression slots)
    (dummiesCaptured : applySubst bindings (.var "dummies") = .expression dummies)
    (arityCaptured : applySubst bindings (.var "arity") = natural arity) :
    PureReturns program bindings state (.expression [.symbol "MM0:MMBUState",
      .expression [.symbol "MM0:L", .var "slots"], .expression [.symbol "MM0:L", .var "dummies"], .var "arity"])
      state (unifyStateValue slots dummies arity) := by
  apply data_call_returns program bindings state state "MM0:MMBUState" _ _ (by decide +kernel) _ (by decide)
  apply evaluated_argument_returns program bindings state state state .data (.symbol "MM0:MMBUState")
    (.symbol "MM0:MMBUState") _ _ [] 0 rfl (symbol_returns program bindings state "MM0:MMBUState")
  apply evaluated_argument_returns program bindings state state state .data
    (.expression [.symbol "MM0:L", .var "slots"]) (listValue slots) _ _ [.symbol "MM0:MMBUState"] 1 rfl
  · simpa [slotsCaptured, listValue] using unary_constructor_returns program bindings state "MM0:L" "slots" (by decide +kernel) (by decide)
  · apply evaluated_argument_returns program bindings state state state .data
      (.expression [.symbol "MM0:L", .var "dummies"]) (listValue dummies) _ _ [.symbol "MM0:MMBUState", listValue slots] 2 rfl
    · simpa [dummiesCaptured, listValue] using unary_constructor_returns program bindings state "MM0:L" "dummies" (by decide +kernel) (by decide)
    · simpa [arityCaptured, unifyStateValue] using variable_arguments_return program bindings state state .data ["arity"]
        [.symbol "MM0:MMBUState", listValue slots, listValue dummies] 3 (unifyStateValue slots dummies arity)
        (by simpa [arityCaptured, unifyStateValue] using (data_arguments_values_return program bindings state
          [.symbol "MM0:MMBUState", listValue slots, listValue dummies, natural arity] 4))

private theorem expression_reference_read_returns (state : State) (resolver sorts terms theorems : Atom)
    (fuel index start after : Nat) (slots dummies : List Atom) (arity : Nat) (rest : List Atom) :
    PureReturns program (expressionReferenceEnvironment resolver sorts terms theorems fuel index start after slots dummies arity rest)
      state (.expression [.symbol "mm0:data-at", .expression [.symbol "MM0:L", .var "slots"], .var "data"])
      state (optionValue (slots[index]?)) := by
  let bindings := expressionReferenceEnvironment resolver sorts terms theorems fuel index start after slots dummies arity rest
  let prior : Subst := [("slots", listValue slots), ("index", natural index)]
  have returned := MMBProofRunExecution.checker_returns (by decide +kernel)
    (ListAccess.data_at_list_returns prior state slots index "slots" "index" rfl rfl)
  apply captured_call_returns program prior bindings state state "mm0:data-at"
    [.var "slots", .var "index"] [.expression [.symbol "MM0:L", .var "slots"], .var "data"] _
    (by decide +kernel) (by decide) _ _ _ returned
  · intro offset argument found
    have bounded : offset < 2 := by have inside := (getElem?_eq_some_iff.mp found).choose; simpa using inside
    interval_cases offset <;> simp at found <;> subst argument <;> right <;> rfl
  · intro offset argument found
    have bounded : offset < 2 := by have inside := (getElem?_eq_some_iff.mp found).choose; simpa using inside
    interval_cases offset
    · left; decide +kernel
    · simp at found; subst argument; right; rfl
  · simp [prior, bindings, expressionReferenceEnvironment, expressionEnvironment, applySubst,
      applySubst.applySubstList, Subst.lookup, listValue]

private theorem expression_reference_found_returns (state : State) (resolver sorts terms theorems expression : Atom)
    (fuel index start after : Nat) (slots dummies : List Atom) (arity : Nat) (rest : List Atom) :
    PureReturns program (("expression", expression) ::
      expressionReferenceEnvironment resolver sorts terms theorems fuel index start after slots dummies arity rest)
      state expressionReferenceFound state
      (optionValue (some (unifyExpressionValue expression slots dummies arity rest))) := by
  let bindings := ("expression", expression) ::
    expressionReferenceEnvironment resolver sorts terms theorems fuel index start after slots dummies arity rest
  rw [expression_reference_found_shape]
  apply unary_constructor_of_returns program bindings state state "Some" _ _ (by decide +kernel) (by decide)
  apply data_call_returns program bindings state state "MM0:MMBUExpression" _ _ (by decide +kernel) _ (by decide)
  apply evaluated_argument_returns program bindings state state state .data (.symbol "MM0:MMBUExpression")
    (.symbol "MM0:MMBUExpression") _ _ [] 0 rfl (symbol_returns program bindings state "MM0:MMBUExpression")
  apply evaluated_argument_returns program bindings state state state .data (.var "expression") expression _ _
    [.symbol "MM0:MMBUExpression"] 1 rfl (variable_returns program bindings state "expression")
  apply evaluated_argument_returns program bindings state state state .data
    (.expression [.symbol "MM0:MMBUState", .expression [.symbol "MM0:L", .var "slots"],
      .expression [.symbol "MM0:L", .var "dummies"], .var "arity"])
    (unifyStateValue slots dummies arity) _ _ [.symbol "MM0:MMBUExpression", expression] 2 rfl
  · apply unify_constructor_returns <;> simp [bindings, expressionReferenceEnvironment, expressionEnvironment,
      applySubst, Subst.lookup]
  · apply evaluated_argument_returns program bindings state state state .data
      (.expression [.symbol "MM0:L", .var "rest"]) (listValue rest) _ _
      [.symbol "MM0:MMBUExpression", expression, unifyStateValue slots dummies arity] 3 rfl
    · simpa [bindings, expressionReferenceEnvironment, listValue, applySubst, Subst.lookup] using
        unary_constructor_returns program bindings state "MM0:L" "rest" (by decide +kernel) (by decide)
    · exact data_arguments_values_return program bindings state _ 4


private def expressionCommandEnvironment (resolver sorts terms theorems : Atom) (fuel opcode data start after : Nat)
    (slots dummies : List Atom) (arity : Nat) (rest : List Atom) : Subst :=
  ("rest", .expression rest) :: ("after", natural after) :: ("start", natural start) ::
  ("data", natural data) :: ("opcode", natural opcode) ::
    expressionEnvironment resolver sorts terms theorems (fuel + 1) slots dummies arity
      (MMBExecution.commandValue opcode data start after :: rest)

private theorem expression_command_from_body (state : State) (resolver sorts terms theorems : Atom)
    (fuel opcode data start after : Nat) (slots dummies : List Atom) (arity : Nat) (rest : List Atom) (body answer : Atom)
    (selected : SpaceSemantics.selectCase
      (expressionCommandEnvironment resolver sorts terms theorems fuel opcode data start after slots dummies arity rest)
      (natural opcode) expressionOpcodeCases =
      some (expressionCommandEnvironment resolver sorts terms theorems fuel opcode data start after slots dummies arity rest, body))
    (returned : PureReturns program
      (expressionCommandEnvironment resolver sorts terms theorems fuel opcode data start after slots dummies arity rest)
      state body state answer) :
    PureReturns program
      (expressionEnvironment resolver sorts terms theorems (fuel + 1) slots dummies arity
        (MMBExecution.commandValue opcode data start after :: rest))
      state expressionEquation.body state answer := by
  let bindings := expressionEnvironment resolver sorts terms theorems (fuel + 1) slots dummies arity
    (MMBExecution.commandValue opcode data start after :: rest)
  let command := expressionCommandEnvironment resolver sorts terms theorems fuel opcode data start after slots dummies arity rest
  rw [expression_shape]
  apply if_returns program bindings state state state _ (boolean true) _ _ answer
  · apply native_binary_call_returns program bindings state state state state "<" (natural 0) (.var "fuel")
      (natural 0) (natural (fuel + 1)) (boolean true)
      (by decide) (by decide) (by decide +kernel) (by decide +kernel) _ _ _ (by decide)
    · exact grounded_returns program bindings state (.int 0)
    · exact variable_returns program bindings state "fuel"
    · simp [StdLib.less_comparison, natural, boolean]
  · simp only [boolean]
    rw [expression_then_shape]
    apply case_returns program bindings command state state state (.var "codes")
      (.expression (MMBExecution.commandValue opcode data start after :: rest)) expressionOpcode _ _
      expressionCases (read_cases_encoded expressionCases)
    · exact variable_returns program bindings state "codes"
    · simp [expression_cases_shape, MMBExecution.commandValue, SpaceSemantics.selectCase,
        SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup,
        command, bindings, expressionCommandEnvironment, expressionEnvironment]
    · rw [expression_opcode_shape]
      apply case_returns program command command state state state (.var "opcode") (natural opcode)
        body _ _ expressionOpcodeCases (read_cases_encoded expressionOpcodeCases)
      · exact variable_returns program command state "opcode"
      · exact selected
      · exact returned

private theorem expression_reference_from_body (state : State) (resolver sorts terms theorems : Atom)
    (fuel index start after : Nat) (slots dummies : List Atom) (arity : Nat) (rest : List Atom) (answer : Atom)
    (body : PureReturns program
      (expressionReferenceEnvironment resolver sorts terms theorems fuel index start after slots dummies arity rest)
      state expressionReference state answer) :
    PureReturns program
      (expressionEnvironment resolver sorts terms theorems (fuel + 1) slots dummies arity
        (MMBExecution.commandValue 50 index start after :: rest))
      state expressionEquation.body state answer := by
  apply expression_command_from_body state resolver sorts terms theorems fuel 50 index start after slots dummies arity rest expressionReference answer
  · simp [expression_opcode_cases, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom, natural]
  · exact body

private theorem reference_filled_body_returns (state : State) (resolver sorts terms theorems expression : Atom)
    (fuel index start after : Nat) (slots dummies : List Atom) (arity : Nat) (rest : List Atom)
    (found : slots[index]? = some (optionValue (some expression))) :
    PureReturns program (expressionReferenceEnvironment resolver sorts terms theorems fuel index start after slots dummies arity rest)
      state expressionReference state
      (optionValue (some (unifyExpressionValue expression slots dummies arity rest))) := by
  let bindings := expressionReferenceEnvironment resolver sorts terms theorems fuel index start after slots dummies arity rest
  let selected := ("expression", expression) :: bindings
  rw [expression_reference_shape]
  apply case_returns program bindings selected state state state _
    (optionValue (some (optionValue (some expression)))) expressionReferenceFound _ _
    expressionReferenceCases (read_cases_encoded expressionReferenceCases)
  · simpa only [found] using expression_reference_read_returns state resolver sorts terms theorems fuel index start after slots dummies arity rest
  · simp [expression_reference_cases, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
      SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup, selected, bindings,
      expressionReferenceEnvironment, expressionEnvironment, optionValue]
  · exact expression_reference_found_returns state resolver sorts terms theorems expression fuel index start after slots dummies arity rest

/-- A filled reference returns its original expression without re-evaluation,
retains every slot and dummy, and leaves the exact remaining command stream. -/
theorem unify_reference_filled_returns (bindings : Subst) (state : State)
    (resolver sorts terms theorems expression : Atom) (fuel index start after : Nat)
    (slots dummies : List Atom) (arity : Nat) (rest : List Atom)
    (resolverName tablesName fuelName unifyName codesName : String)
    (resolverCaptured : applySubst bindings (.var resolverName) = resolver)
    (tablesCaptured : applySubst bindings (.var tablesName) = tablesValue sorts terms theorems)
    (fuelCaptured : applySubst bindings (.var fuelName) = natural (fuel + 1))
    (unifyCaptured : applySubst bindings (.var unifyName) = unifyStateValue slots dummies arity)
    (codesCaptured : applySubst bindings (.var codesName) =
      listValue (MMBExecution.commandValue 50 index start after :: rest))
    (found : slots[index]? = some (optionValue (some expression))) :
    PureReturns program bindings state (.expression [.symbol "mm0:mmb:unify-expression", .var resolverName,
      .var tablesName, .var fuelName, .var unifyName, .var codesName]) state
      (optionValue (some (unifyExpressionValue expression slots dummies arity rest))) :=
  expression_from_body bindings state resolver sorts terms theorems (fuel + 1) slots dummies arity
    (MMBExecution.commandValue 50 index start after :: rest) _ resolverName tablesName fuelName unifyName codesName
    resolverCaptured tablesCaptured fuelCaptured unifyCaptured codesCaptured
    (expression_reference_from_body state resolver sorts terms theorems fuel index start after slots dummies arity rest _
      (reference_filled_body_returns state resolver sorts terms theorems expression fuel index start after slots dummies arity rest found))

private theorem reference_unavailable_body_returns (state : State) (resolver sorts terms theorems : Atom)
    (fuel index start after : Nat) (slots dummies : List Atom) (arity : Nat) (rest : List Atom)
    (unavailable : slots[index]? = none ∨ slots[index]? = some (.symbol "None")) :
    PureReturns program (expressionReferenceEnvironment resolver sorts terms theorems fuel index start after slots dummies arity rest)
      state expressionReference state (.symbol "None") := by
  let bindings := expressionReferenceEnvironment resolver sorts terms theorems fuel index start after slots dummies arity rest
  rw [expression_reference_shape]
  rcases unavailable with absent | unfilled
  · apply case_returns program bindings (("bad", .symbol "None") :: bindings) state state state _
      (.symbol "None") (.symbol "None") _ _ expressionReferenceCases (read_cases_encoded expressionReferenceCases)
    · simpa only [absent, optionValue] using expression_reference_read_returns state resolver sorts terms theorems fuel index start after slots dummies arity rest
    · simp [expression_reference_cases, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
        matchAtom, Subst.lookup, bindings, expressionReferenceEnvironment, expressionEnvironment]
    · exact symbol_returns program _ state "None"
  · apply case_returns program bindings (("bad", optionValue (some (.symbol "None"))) :: bindings) state state state _
      (optionValue (some (.symbol "None"))) (.symbol "None") _ _ expressionReferenceCases (read_cases_encoded expressionReferenceCases)
    · simpa only [unfilled] using expression_reference_read_returns state resolver sorts terms theorems fuel index start after slots dummies arity rest
    · simp [expression_reference_cases, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
        SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup, optionValue, bindings, expressionReferenceEnvironment, expressionEnvironment]
    · exact symbol_returns program _ state "None"

/-- Both absent future slots and reserved-but-unfilled slots are refused by the
original reference operation. Merely allocating a slot does not authorize it. -/
theorem unify_reference_unavailable_returns (bindings : Subst) (state : State)
    (resolver sorts terms theorems : Atom) (fuel index start after : Nat)
    (slots dummies : List Atom) (arity : Nat) (rest : List Atom)
    (resolverName tablesName fuelName unifyName codesName : String)
    (resolverCaptured : applySubst bindings (.var resolverName) = resolver)
    (tablesCaptured : applySubst bindings (.var tablesName) = tablesValue sorts terms theorems)
    (fuelCaptured : applySubst bindings (.var fuelName) = natural (fuel + 1))
    (unifyCaptured : applySubst bindings (.var unifyName) = unifyStateValue slots dummies arity)
    (codesCaptured : applySubst bindings (.var codesName) =
      listValue (MMBExecution.commandValue 50 index start after :: rest))
    (unavailable : slots[index]? = none ∨ slots[index]? = some (.symbol "None")) :
    PureReturns program bindings state (.expression [.symbol "mm0:mmb:unify-expression", .var resolverName,
      .var tablesName, .var fuelName, .var unifyName, .var codesName]) state (.symbol "None") :=
  expression_from_body bindings state resolver sorts terms theorems (fuel + 1) slots dummies arity
    (MMBExecution.commandValue 50 index start after :: rest) _ resolverName tablesName fuelName unifyName codesName
    resolverCaptured tablesCaptured fuelCaptured unifyCaptured codesCaptured
    (expression_reference_from_body state resolver sorts terms theorems fuel index start after slots dummies arity rest _
      (reference_unavailable_body_returns state resolver sorts terms theorems fuel index start after slots dummies arity rest unavailable))

private theorem expression_zero_body_returns (state : State) (resolver sorts terms theorems : Atom)
    (slots dummies : List Atom) (arity : Nat) (codes : List Atom) :
    PureReturns program (expressionEnvironment resolver sorts terms theorems 0 slots dummies arity codes)
      state expressionEquation.body state (.symbol "None") := by
  let bindings := expressionEnvironment resolver sorts terms theorems 0 slots dummies arity codes
  rw [expression_shape]
  apply if_returns program bindings state state state _ (boolean false) _ _ (.symbol "None")
  · apply native_binary_call_returns program bindings state state state state "<" (natural 0) (.var "fuel")
      (natural 0) (natural 0) (boolean false)
      (by decide) (by decide) (by decide +kernel) (by decide +kernel) _ _ _ (by decide)
    · exact grounded_returns program bindings state (.int 0)
    · exact variable_returns program bindings state "fuel"
    · simp [StdLib.less_comparison, natural, boolean]
  · exact symbol_returns program bindings state "None"

/-- The source expression budget is tested before inspecting a command or slot.
A zero budget refuses even a valid filled reference. -/
theorem unify_expression_zero_returns (bindings : Subst) (state : State)
    (resolver sorts terms theorems : Atom) (slots dummies : List Atom) (arity : Nat) (codes : List Atom)
    (resolverName tablesName fuelName unifyName codesName : String)
    (resolverCaptured : applySubst bindings (.var resolverName) = resolver)
    (tablesCaptured : applySubst bindings (.var tablesName) = tablesValue sorts terms theorems)
    (fuelCaptured : applySubst bindings (.var fuelName) = natural 0)
    (unifyCaptured : applySubst bindings (.var unifyName) = unifyStateValue slots dummies arity)
    (codesCaptured : applySubst bindings (.var codesName) = listValue codes) :
    PureReturns program bindings state (.expression [.symbol "mm0:mmb:unify-expression", .var resolverName,
      .var tablesName, .var fuelName, .var unifyName, .var codesName]) state (.symbol "None") :=
  expression_from_body bindings state resolver sorts terms theorems 0 slots dummies arity codes _
    resolverName tablesName fuelName unifyName codesName resolverCaptured tablesCaptured fuelCaptured unifyCaptured codesCaptured
    (expression_zero_body_returns state resolver sorts terms theorems slots dummies arity codes)


/-- The original child-list result retains both the exact final unify state and
the unread command tail, independently of the number of returned children. -/
def unifyExpressionsValue (arguments : List Atom) (unify codes : Atom) : Atom :=
  .expression [.symbol "MM0:MMBUExpressions", listValue arguments, unify, codes]

private def expressionsEquation := sourceEquation "mm0:mmb:unify-expressions"
private def expressionsMore := match expressionsEquation.body with
  | .expression [_, _, _, more] => more
  | _ => .symbol "None"
private def expressionsEnvironment (resolver tables : Atom) (fuel count : Nat) (unify codes : Atom) : Subst :=
  [("codes", codes), ("unify", unify), ("count", natural count), ("fuel", natural fuel),
    ("tables", tables), ("state", resolver)]
private theorem expressions_unique :
    program.equations.filter (·.head == "mm0:mmb:unify-expressions") = [expressionsEquation] := by decide +kernel
private theorem expressions_formals : expressionsEquation.arguments =
    [.var "state", .var "tables", .var "fuel", .var "count", .var "unify", .var "codes"] := by decide
private theorem expressions_shape : expressionsEquation.body =
    .expression [.symbol "if", .expression [.symbol "==", .var "count", natural 0],
      .expression [.symbol "Some", .expression [.symbol "MM0:MMBUExpressions",
        .expression [.symbol "MM0:L", .expression []], .var "unify", .var "codes"]], expressionsMore] := by decide
private theorem expressions_clause (resolver tables : Atom) (fuel count : Nat) (unify codes : Atom) :
    clauses program "mm0:mmb:unify-expressions" [resolver, tables, natural fuel, natural count, unify, codes] =
      [.evaluate (expressionsEnvironment resolver tables fuel count unify codes) expressionsEquation.body] := by
  rw [clauses_use_only_the_named_equations, expressions_unique]
  simp [expressions_formals, expressionsEnvironment, SpaceSemantics.matchValue,
    SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]

private theorem expressions_call_from_body (bindings : Subst) (state : State) (resolver tables : Atom)
    (fuel count : Nat) (unify codes answer : Atom)
    (resolverArgument tablesArgument fuelArgument countArgument unifyArgument codesArgument : Atom)
    (resolverCaptured : applySubst bindings resolverArgument = resolver)
    (tablesCaptured : applySubst bindings tablesArgument = tables)
    (fuelReturned : PureReturns program bindings state fuelArgument state (natural fuel))
    (countReturned : PureReturns program bindings state countArgument state (natural count))
    (unifyCaptured : applySubst bindings unifyArgument = unify)
    (codesCaptured : applySubst bindings codesArgument = codes)
    (body : PureReturns program (expressionsEnvironment resolver tables fuel count unify codes)
      state expressionsEquation.body state answer) :
    PureReturns program bindings state (.expression [.symbol "mm0:mmb:unify-expressions", resolverArgument,
      tablesArgument, fuelArgument, countArgument, unifyArgument, codesArgument]) state answer := by
  apply call_returns program bindings state state "mm0:mmb:unify-expressions" _ _ (by decide +kernel) _ (by decide)
  apply raw_argument_answers program bindings state state "mm0:mmb:unify-expressions" resolverArgument _ [] 0
    [_] (by decide +kernel)
  apply raw_argument_answers program bindings state state "mm0:mmb:unify-expressions" tablesArgument _ _ 1
    [_] (by decide +kernel)
  apply evaluated_argument_returns program bindings state state state (.function "mm0:mmb:unify-expressions")
    fuelArgument (natural fuel) _ _ _ 2 (by decide +kernel) fuelReturned
  apply evaluated_argument_returns program bindings state state state (.function "mm0:mmb:unify-expressions")
    countArgument (natural count) _ _ _ 3 (by decide +kernel) countReturned
  apply raw_arguments_return program bindings state state "mm0:mmb:unify-expressions"
    [unifyArgument, codesArgument] _ 4 _
  · intro offset inside
    have range : offset < 2 := by simpa using inside
    interval_cases offset <;> decide +kernel
  · simp only [List.map_cons, List.map_nil, resolverCaptured, tablesCaptured, unifyCaptured, codesCaptured]
    exact authored_function_arguments_return program bindings
      (expressionsEnvironment resolver tables fuel count unify codes) state state "mm0:mmb:unify-expressions"
      [resolver, tables, natural fuel, natural count, unify, codes] 6 expressionsEquation.body _
      (by decide +kernel) (by decide) (expressions_clause resolver tables fuel count unify codes) body

private theorem expressions_empty_body_returns (state : State) (resolver tables : Atom) (fuel : Nat) (unify codes : Atom) :
    PureReturns program (expressionsEnvironment resolver tables fuel 0 unify codes) state expressionsEquation.body state
      (optionValue (some (unifyExpressionsValue [] unify codes))) := by
  let bindings := expressionsEnvironment resolver tables fuel 0 unify codes
  rw [expressions_shape]
  apply if_returns program bindings state state state _ (boolean true) _ _ _
  · apply native_binary_call_returns program bindings state state state state "==" (.var "count") (natural 0)
      (natural 0) (natural 0) (boolean true)
      (by decide) (by decide) (by decide +kernel) (by decide +kernel) _ _ _ (by decide)
    · exact variable_returns program bindings state "count"
    · exact grounded_returns program bindings state (.int 0)
    · simp [StdLib.structural_equality, natural, boolean]
  · apply unary_constructor_of_returns program bindings state state "Some" _ _ (by decide +kernel) (by decide)
    apply data_call_returns program bindings state state "MM0:MMBUExpressions" _ _ (by decide +kernel) _ (by decide)
    apply evaluated_argument_returns program bindings state state state .data (.symbol "MM0:MMBUExpressions")
      (.symbol "MM0:MMBUExpressions") _ _ [] 0 rfl (symbol_returns program bindings state "MM0:MMBUExpressions")
    apply evaluated_argument_returns program bindings state state state .data
      (.expression [.symbol "MM0:L", .expression []]) (listValue []) _ _ [.symbol "MM0:MMBUExpressions"] 1 rfl
    · exact empty_constructor_returns program bindings state "MM0:L" (by decide +kernel) (by decide)
    · simpa [bindings, expressionsEnvironment, unifyExpressionsValue, applySubst, Subst.lookup] using
        variable_arguments_return program bindings state state .data ["unify", "codes"]
          [.symbol "MM0:MMBUExpressions", listValue []] 2 (unifyExpressionsValue [] unify codes)
          (by simpa [bindings, expressionsEnvironment, unifyExpressionsValue, applySubst, Subst.lookup] using (data_arguments_values_return program bindings state
            [.symbol "MM0:MMBUExpressions", listValue [], unify, codes] 4))

/-- A zero child count succeeds even with zero expression fuel, preserving the
original state and unread stream. It does not spend a command or invent a child. -/
theorem unify_expressions_empty_returns (bindings : Subst) (state : State)
    (resolver tables : Atom) (fuel : Nat) (unify codes : Atom)
    (resolverName tablesName fuelName countName unifyName codesName : String)
    (resolverCaptured : applySubst bindings (.var resolverName) = resolver)
    (tablesCaptured : applySubst bindings (.var tablesName) = tables)
    (fuelCaptured : applySubst bindings (.var fuelName) = natural fuel)
    (countCaptured : applySubst bindings (.var countName) = natural 0)
    (unifyCaptured : applySubst bindings (.var unifyName) = unify)
    (codesCaptured : applySubst bindings (.var codesName) = codes) :
    PureReturns program bindings state (.expression [.symbol "mm0:mmb:unify-expressions", .var resolverName,
      .var tablesName, .var fuelName, .var countName, .var unifyName, .var codesName]) state
      (optionValue (some (unifyExpressionsValue [] unify codes))) := by
  exact expressions_call_from_body bindings state resolver tables fuel 0 unify codes _
    (.var resolverName) (.var tablesName) (.var fuelName) (.var countName) (.var unifyName) (.var codesName)
    resolverCaptured tablesCaptured
    (by simpa [fuelCaptured] using variable_returns program bindings state fuelName)
    (by simpa [countCaptured] using variable_returns program bindings state countName)
    unifyCaptured codesCaptured (expressions_empty_body_returns state resolver tables fuel unify codes)

private def hypothesesEquation := sourceEquation "mm0:mmb:unify-hypotheses"
private def hypothesesCases := casesOf hypothesesEquation.body
private def hypothesesCons := (hypothesesCases[1]'(by decide)).2
private theorem hypotheses_cases_shape : hypothesesCases =
    [(.expression [], .expression [.symbol "Some", .expression [.symbol "MM0:L", .expression []]]),
      (.expression [.symbol "cons", .expression [.symbol "MM0:MMBCode", natural 54, .var "data", .var "start", .var "after"],
        .var "rest"], hypothesesCons), (.var "bad", .symbol "None")] := by decide
private def hypothesesEnvironment (resolver tables : Atom) (fuel : Nat) (unify : Atom) (codes : List Atom) : Subst :=
  [("codes", .expression codes), ("unify", unify), ("fuel", natural fuel), ("tables", tables), ("state", resolver)]
private theorem hypotheses_unique :
    program.equations.filter (·.head == "mm0:mmb:unify-hypotheses") = [hypothesesEquation] := by decide +kernel
private theorem hypotheses_formals : hypothesesEquation.arguments =
    [.var "state", .var "tables", .var "fuel", .var "unify", .expression [.symbol "MM0:L", .var "codes"]] := by decide
private theorem hypotheses_shape : hypothesesEquation.body = .expression [.symbol "case", .var "codes",
    .expression (hypothesesCases.map fun row => .expression [row.1, row.2])] := by decide
private theorem hypotheses_clause (resolver tables : Atom) (fuel : Nat) (unify : Atom) (codes : List Atom) :
    clauses program "mm0:mmb:unify-hypotheses" [resolver, tables, natural fuel, unify, listValue codes] =
      [.evaluate (hypothesesEnvironment resolver tables fuel unify codes) hypothesesEquation.body] := by
  rw [clauses_use_only_the_named_equations, hypotheses_unique]
  simp [hypotheses_formals, hypothesesEnvironment, listValue, SpaceSemantics.matchValue,
    SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]
private theorem hypotheses_empty_body_returns (state : State) (resolver tables : Atom) (fuel : Nat) (unify : Atom) :
    PureReturns program (hypothesesEnvironment resolver tables fuel unify []) state hypothesesEquation.body state
      (optionValue (some (listValue []))) := by
  let bindings := hypothesesEnvironment resolver tables fuel unify []
  rw [hypotheses_shape]
  apply case_returns program bindings bindings state state state (.var "codes") (.expression [])
    (.expression [.symbol "Some", .expression [.symbol "MM0:L", .expression []]]) _ _
    hypothesesCases (read_cases_encoded hypothesesCases)
  · exact variable_returns program bindings state "codes"
  · simp [hypotheses_cases_shape, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
      SpaceSemantics.matchValue.matchValues]
  · apply unary_constructor_of_returns program bindings state state "Some" _ _ (by decide +kernel) (by decide)
    exact empty_constructor_returns program bindings state "MM0:L" (by decide +kernel) (by decide)

/-- An empty hypothesis stream succeeds before the source fuel test, including
at zero fuel. The supplied unify state is retained as inert input. -/
theorem unify_hypotheses_empty_returns (bindings : Subst) (state : State) (resolver tables : Atom) (fuel : Nat) (unify : Atom)
    (resolverName tablesName fuelName unifyName codesName : String)
    (resolverCaptured : applySubst bindings (.var resolverName) = resolver)
    (tablesCaptured : applySubst bindings (.var tablesName) = tables)
    (fuelCaptured : applySubst bindings (.var fuelName) = natural fuel)
    (unifyCaptured : applySubst bindings (.var unifyName) = unify)
    (codesCaptured : applySubst bindings (.var codesName) = listValue []) :
    PureReturns program bindings state (.expression [.symbol "mm0:mmb:unify-hypotheses", .var resolverName,
      .var tablesName, .var fuelName, .var unifyName, .var codesName]) state (optionValue (some (listValue []))) := by
  apply authored_variable_call_returns program bindings (hypothesesEnvironment resolver tables fuel unify []) state state
    "mm0:mmb:unify-hypotheses" [resolverName, tablesName, fuelName, unifyName, codesName] hypothesesEquation.body _
    (by decide +kernel) (by decide +kernel) (by decide +kernel) _
    (hypotheses_empty_body_returns state resolver tables fuel unify) (by decide)
  simpa [resolverCaptured, tablesCaptured, fuelCaptured, unifyCaptured, codesCaptured] using
    hypotheses_clause resolver tables fuel unify []


private def dummyCases := casesOf expressionDummy
private def dummyFound := (dummyCases[0]'(by decide)).2
private def dummyResult := match dummyFound with | .expression [_, _, body] => body | _ => .symbol "None"
private theorem dummy_shape : expressionDummy =
    .expression [.symbol "case", .expression [.symbol "mm0:mmu:sort", .var "state", .var "data"],
      .expression (dummyCases.map fun row => .expression [row.1, row.2])] := by decide
private theorem dummy_cases_shape : dummyCases =
    [(.expression [.symbol "Some", .var "sort"], dummyFound), (.var "bad", .symbol "None")] := by decide
private theorem dummy_found_shape : dummyFound =
    .expression [.symbol "let*", .expression [
      .expression [.var "variable", .expression [.symbol "mm0:make-var", .expression [.symbol "+", .var "arity", .expression [.symbol "size-atom", .var "dummies"]]]],
      .expression [.var "slot", .expression [.symbol "Some", .var "variable"]],
      .expression [.var "nextSlots", .expression [.symbol "mm0:mmb:snoc", .expression [.symbol "MM0:L", .var "slots"], .var "slot"]],
      .expression [.var "nextDummies", .expression [.symbol "mm0:mmb:snoc", .expression [.symbol "MM0:L", .var "dummies"], .var "sort"]]], dummyResult] := by decide
private theorem dummy_result_shape : dummyResult =
    .expression [.symbol "Some", .expression [.symbol "MM0:MMBUExpression", .var "variable",
      .expression [.symbol "MM0:MMBUState", .var "nextSlots", .var "nextDummies", .var "arity"],
      .expression [.symbol "MM0:L", .var "rest"]]] := by decide

/-- A source dummy's sort field comes from the preceding MMU sort map. Its
fresh index follows all argument variables and all already recorded dummies. -/
def dummyResultValue (sorts : List MMUResolution.Binding) (binary : Nat)
    (slots dummies : List Atom) (arity : Nat) (rest : List Atom) : Atom :=
  optionValue ((MMUResolution.lookup sorts (natural binary)).map fun sort =>
    let freshTerm := Data.preterm (.var (arity + dummies.length))
    unifyExpressionValue freshTerm (slots ++ [optionValue (some freshTerm)]) (dummies ++ [sort]) arity rest)

private theorem dummy_result_returns (bindings : Subst) (state : State) (freshTerm : Atom)
    (slots dummies : List Atom) (arity : Nat) (rest : List Atom)
    (variableCaptured : applySubst bindings (.var "variable") = freshTerm)
    (slotsCaptured : applySubst bindings (.var "nextSlots") = listValue slots)
    (dummiesCaptured : applySubst bindings (.var "nextDummies") = listValue dummies)
    (arityCaptured : applySubst bindings (.var "arity") = natural arity)
    (restCaptured : applySubst bindings (.var "rest") = .expression rest) :
    PureReturns program bindings state dummyResult state
      (optionValue (some (unifyExpressionValue freshTerm slots dummies arity rest))) := by
  rw [dummy_result_shape]
  apply unary_constructor_of_returns program bindings state state "Some" _ _ (by decide +kernel) (by decide)
  apply data_call_returns program bindings state state "MM0:MMBUExpression" _ _ (by decide +kernel) _ (by decide)
  apply evaluated_argument_returns program bindings state state state .data (.symbol "MM0:MMBUExpression")
    (.symbol "MM0:MMBUExpression") _ _ [] 0 rfl (symbol_returns program bindings state "MM0:MMBUExpression")
  apply evaluated_argument_returns program bindings state state state .data (.var "variable") freshTerm _ _ [.symbol "MM0:MMBUExpression"] 1 rfl
  · simpa [variableCaptured] using variable_returns program bindings state "variable"
  · apply evaluated_argument_returns program bindings state state state .data
      (.expression [.symbol "MM0:MMBUState", .var "nextSlots", .var "nextDummies", .var "arity"])
      (unifyStateValue slots dummies arity) _ _ [.symbol "MM0:MMBUExpression", freshTerm] 2 rfl
    · simpa [slotsCaptured, dummiesCaptured, arityCaptured, unifyStateValue] using
        constructor_variables_return program bindings state "MM0:MMBUState" ["nextSlots", "nextDummies", "arity"] (by decide +kernel) (by decide)
    · apply evaluated_argument_returns program bindings state state state .data
        (.expression [.symbol "MM0:L", .var "rest"]) (listValue rest) _ _
        [.symbol "MM0:MMBUExpression", freshTerm, unifyStateValue slots dummies arity] 3 rfl
      · simpa [restCaptured, listValue] using unary_constructor_returns program bindings state "MM0:L" "rest" (by decide +kernel) (by decide)
      · exact data_arguments_values_return program bindings state _ 4

private theorem dummy_body_returns (state : State) (published : Atom)
    (sorts terms theorems : List MMUResolution.Binding) (nextSort nextTerm nextTheorem : Nat) (images : Atom)
    (tableSorts tableTerms tableTheorems : Atom) (fuel binary start after : Nat)
    (slots dummies : List Atom) (arity : Nat) (rest : List Atom) :
    PureReturns program
      (expressionCommandEnvironment (resolverValue published sorts terms theorems nextSort nextTerm nextTheorem images)
        tableSorts tableTerms tableTheorems fuel 51 binary start after slots dummies arity rest)
      state expressionDummy state (dummyResultValue sorts binary slots dummies arity rest) := by
  let resolver := resolverValue published sorts terms theorems nextSort nextTerm nextTheorem images
  let bindings := expressionCommandEnvironment resolver tableSorts tableTerms tableTheorems fuel 51 binary start after slots dummies arity rest
  have sortReturned := resolver_returns .sort bindings state published sorts terms theorems nextSort nextTerm nextTheorem images
    (natural binary) "state" "data"
    (by simp [resolver, bindings, expressionCommandEnvironment, expressionEnvironment, applySubst, Subst.lookup])
    (by simp [bindings, expressionCommandEnvironment, expressionEnvironment, applySubst, Subst.lookup])
  simp only [ResolverField.head, ResolverField.entries] at sortReturned
  rw [dummy_shape]
  cases found : MMUResolution.lookup sorts (natural binary) with
  | none =>
      apply case_returns program bindings (("bad", .symbol "None") :: bindings) state state state _
        (.symbol "None") (.symbol "None") _ _ dummyCases (read_cases_encoded dummyCases)
      · simpa [found, optionValue] using sortReturned
      · simp [dummy_cases_shape, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom, Subst.lookup,
          bindings, expressionCommandEnvironment, expressionEnvironment]
      · simpa [dummyResultValue, found, optionValue] using symbol_returns program _ state "None"
  | some sort =>
      let selected := ("sort", sort) :: bindings
      let freshTerm := Data.preterm (.var (arity + dummies.length))
      let valued := ("variable", freshTerm) :: selected
      let slot := optionValue (some freshTerm)
      let slotted := ("slot", slot) :: valued
      let nextSlots := slots ++ [slot]
      let stored := ("nextSlots", listValue nextSlots) :: slotted
      let nextDummies := dummies ++ [sort]
      let final := ("nextDummies", listValue nextDummies) :: stored
      apply case_returns program bindings selected state state state _ (optionValue (some sort)) dummyFound _ _
        dummyCases (read_cases_encoded dummyCases)
      · simpa [found] using sortReturned
      · simp [dummy_cases_shape, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
          SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup, selected, bindings,
          expressionCommandEnvironment, expressionEnvironment, optionValue]
      · rw [dummy_found_shape]
        apply let_star_returns program selected state state _ _ _ _ rfl
        apply let_returns program selected valued state state state (.var "variable") _ _ freshTerm _
        · apply computed_variable_returns selected state (arity + dummies.length)
          apply native_binary_call_returns program selected state state state state "+" (.var "arity")
            (.expression [.symbol "size-atom", .var "dummies"]) (natural arity) (natural dummies.length) (natural (arity + dummies.length))
            (by decide) (by decide) (by decide +kernel) (by decide +kernel) _ _ _ (by decide)
          · exact variable_returns program selected state "arity"
          · apply native_variable_call_returns program selected state state "size-atom" ["dummies"] (natural dummies.length) (by decide) (by decide) _ (by decide)
            rfl
          · change (.ok (state, [.grounded (.int ((arity : Int) + dummies.length))]) : Effects.Result) = .ok (state, [natural (arity + dummies.length)])
            simp [natural]
        · simp [SpaceSemantics.matchValue, matchAtom, valued, selected, bindings,
            expressionCommandEnvironment, expressionEnvironment, Subst.lookup]
        · apply let_returns program valued slotted state state state (.var "slot") _ _ slot _
          · simpa [slot, valued, applySubst, Subst.lookup, optionValue] using
              unary_constructor_returns program valued state "Some" "variable" (by decide +kernel) (by decide)
          · simp [SpaceSemantics.matchValue, matchAtom, slotted, valued, selected, bindings,
              expressionCommandEnvironment, expressionEnvironment, Subst.lookup]
          · apply let_returns program slotted stored state state state (.var "nextSlots") _ _ (listValue nextSlots) _
            · apply snoc_captured_returns slotted state slots slot (.expression [.symbol "MM0:L", .var "slots"]) (.var "slot")
              · simp [slotted, valued, selected, bindings, expressionCommandEnvironment, expressionEnvironment,
                  applySubst, applySubst.applySubstList, Subst.lookup, listValue]
              · rfl
            · simp [SpaceSemantics.matchValue, matchAtom, stored, slotted, valued, selected, bindings,
                expressionCommandEnvironment, expressionEnvironment, Subst.lookup]
            · apply let_returns program stored final state state state (.var "nextDummies") _ _ (listValue nextDummies) _
              · apply snoc_captured_returns stored state dummies sort (.expression [.symbol "MM0:L", .var "dummies"]) (.var "sort")
                · simp [stored, slotted, valued, selected, bindings, expressionCommandEnvironment, expressionEnvironment,
                    applySubst, applySubst.applySubstList, Subst.lookup, listValue]
                · rfl
              · simp [SpaceSemantics.matchValue, matchAtom, final, stored, slotted, valued, selected, bindings,
                  expressionCommandEnvironment, expressionEnvironment, Subst.lookup]
              · simpa [dummyResultValue, found, freshTerm, nextSlots, slot, nextDummies] using
                  dummy_result_returns final state freshTerm nextSlots nextDummies arity rest rfl rfl
                    (by rfl) (by simp [final, stored, slotted, valued, selected, bindings, expressionCommandEnvironment,
                      expressionEnvironment, applySubst, Subst.lookup])
                    (by simp [final, stored, slotted, valued, selected, bindings, expressionCommandEnvironment,
                      expressionEnvironment, applySubst, Subst.lookup])

/-- A fresh Polish dummy is resolved through the actual current MMU sort
map. This operation records the source fields; kernel typing is separate. The new filled slot and sort append after the existing entries. -/
theorem unify_dummy_returns (bindings : Subst) (state : State) (published : Atom)
    (sorts terms theorems : List MMUResolution.Binding) (nextSort nextTerm nextTheorem : Nat) (images : Atom)
    (tableSorts tableTerms tableTheorems : Atom) (fuel binary start after : Nat)
    (slots dummies : List Atom) (arity : Nat) (rest : List Atom)
    (resolverName tablesName fuelName unifyName codesName : String)
    (resolverCaptured : applySubst bindings (.var resolverName) = resolverValue published sorts terms theorems nextSort nextTerm nextTheorem images)
    (tablesCaptured : applySubst bindings (.var tablesName) = tablesValue tableSorts tableTerms tableTheorems)
    (fuelCaptured : applySubst bindings (.var fuelName) = natural (fuel + 1))
    (unifyCaptured : applySubst bindings (.var unifyName) = unifyStateValue slots dummies arity)
    (codesCaptured : applySubst bindings (.var codesName) = listValue (MMBExecution.commandValue 51 binary start after :: rest)) :
    PureReturns program bindings state (.expression [.symbol "mm0:mmb:unify-expression", .var resolverName,
      .var tablesName, .var fuelName, .var unifyName, .var codesName]) state
      (dummyResultValue sorts binary slots dummies arity rest) := by
  apply expression_from_body bindings state _ tableSorts tableTerms tableTheorems (fuel + 1) slots dummies arity
    (MMBExecution.commandValue 51 binary start after :: rest) _ resolverName tablesName fuelName unifyName codesName
    resolverCaptured tablesCaptured fuelCaptured unifyCaptured codesCaptured
  apply expression_command_from_body state _ tableSorts tableTerms tableTheorems fuel 51 binary start after slots dummies arity rest expressionDummy _
  · simp [expression_opcode_cases, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom, natural]
  · exact dummy_body_returns state published sorts terms theorems nextSort nextTerm nextTheorem images
      tableSorts tableTerms tableTheorems fuel binary start after slots dummies arity rest


private theorem decrement_returns (bindings : Subst) (state : State) (value : Nat) (name : String)
    (captured : applySubst bindings (.var name) = natural (value + 1)) :
    PureReturns program bindings state (.expression [.symbol "-", .var name, natural 1]) state (natural value) := by
  apply native_binary_call_returns program bindings state state state state "-" (.var name) (natural 1)
    (natural (value + 1)) (natural 1) (natural value)
    (by decide) (by decide) (by decide +kernel) (by decide +kernel) _ _ _ (by decide)
  · simpa [captured] using variable_returns program bindings state name
  · exact grounded_returns program bindings state (.int 1)
  · change (.ok (state, [.grounded (.int (((value + 1 : Nat) : Int) - 1))]) : Effects.Result) = .ok (state, [natural value])
    simp [natural]

private def expressionsFirstCases := casesOf (match expressionsMore with
  | .expression [_, _, more, _] => more | _ => .symbol "None")
private def expressionsFirst := (expressionsFirstCases[0]'(by decide)).2
private def expressionsTailCases := casesOf expressionsFirst
private def expressionsTail := (expressionsTailCases[0]'(by decide)).2
private theorem expressions_more_shape : expressionsMore =
    .expression [.symbol "if", .expression [.symbol "<", natural 0, .var "fuel"],
      .expression [.symbol "case", .expression [.symbol "mm0:mmb:unify-expression", .var "state", .var "tables",
        .expression [.symbol "-", .var "fuel", natural 1], .var "unify", .var "codes"],
        .expression (expressionsFirstCases.map fun row => .expression [row.1, row.2])], .symbol "None"] := by decide
private theorem expressions_first_cases : expressionsFirstCases =
    [(.expression [.symbol "Some", .expression [.symbol "MM0:MMBUExpression", .var "first", .var "after", .var "rest"]],
      expressionsFirst), (.var "bad", .symbol "None")] := by decide
private theorem expressions_first_shape : expressionsFirst =
    .expression [.symbol "case", .expression [.symbol "mm0:mmb:unify-expressions", .var "state", .var "tables",
      .expression [.symbol "-", .var "fuel", natural 1], .expression [.symbol "-", .var "count", natural 1],
      .var "after", .var "rest"], .expression (expressionsTailCases.map fun row => .expression [row.1, row.2])] := by decide
private theorem expressions_tail_cases : expressionsTailCases =
    [(.expression [.symbol "Some", .expression [.symbol "MM0:MMBUExpressions", .var "tail", .var "final", .var "end"]],
      expressionsTail), (.var "bad", .symbol "None")] := by decide
private theorem expressions_tail_shape : expressionsTail =
    .expression [.symbol "let", .var "arguments", .expression [.symbol "mm0:list-cons", .var "first", .var "tail"],
      .expression [.symbol "Some", .expression [.symbol "MM0:MMBUExpressions", .var "arguments", .var "final", .var "end"]]] := by decide

private theorem expressions_success_returns (bindings : Subst) (state : State) (arguments : List Atom) (final ending : Atom)
    (argumentsCaptured : applySubst bindings (.var "arguments") = listValue arguments)
    (finalCaptured : applySubst bindings (.var "final") = final)
    (endCaptured : applySubst bindings (.var "end") = ending) :
    PureReturns program bindings state
      (.expression [.symbol "Some", .expression [.symbol "MM0:MMBUExpressions", .var "arguments", .var "final", .var "end"]])
      state (optionValue (some (unifyExpressionsValue arguments final ending))) := by
  apply unary_constructor_of_returns program bindings state state "Some" _ _ (by decide +kernel) (by decide)
  apply data_call_returns program bindings state state "MM0:MMBUExpressions" _ _ (by decide +kernel) _ (by decide)
  apply evaluated_argument_returns program bindings state state state .data (.symbol "MM0:MMBUExpressions")
    (.symbol "MM0:MMBUExpressions") _ _ [] 0 rfl (symbol_returns program bindings state "MM0:MMBUExpressions")
  simpa [argumentsCaptured, finalCaptured, endCaptured, unifyExpressionsValue] using
    variable_arguments_return program bindings state state .data ["arguments", "final", "end"]
      [.symbol "MM0:MMBUExpressions"] 1 (unifyExpressionsValue arguments final ending)
      (by simpa [argumentsCaptured, finalCaptured, endCaptured, unifyExpressionsValue] using
        (data_arguments_values_return program bindings state
          [.symbol "MM0:MMBUExpressions", listValue arguments, final, ending] 4))

private theorem expressions_cons_body_returns (state : State) (resolver tables : Atom) (fuel count : Nat)
    (unify codes first after rest final ending : Atom) (tail : List Atom)
    (firstReturns : PureReturns program (expressionsEnvironment resolver tables (fuel + 1) (count + 1) unify codes)
      state (.expression [.symbol "mm0:mmb:unify-expression", .var "state", .var "tables",
        .expression [.symbol "-", .var "fuel", natural 1], .var "unify", .var "codes"])
      state (optionValue (some (.expression [.symbol "MM0:MMBUExpression", first, after, rest]))))
    (tailReturns : PureReturns program
      (("rest", rest) :: ("after", after) :: ("first", first) ::
        expressionsEnvironment resolver tables (fuel + 1) (count + 1) unify codes)
      state (.expression [.symbol "mm0:mmb:unify-expressions", .var "state", .var "tables",
        .expression [.symbol "-", .var "fuel", natural 1], .expression [.symbol "-", .var "count", natural 1],
        .var "after", .var "rest"]) state (optionValue (some (unifyExpressionsValue tail final ending)))) :
    PureReturns program (expressionsEnvironment resolver tables (fuel + 1) (count + 1) unify codes)
      state expressionsEquation.body state (optionValue (some (unifyExpressionsValue (first :: tail) final ending))) := by
  let bindings := expressionsEnvironment resolver tables (fuel + 1) (count + 1) unify codes
  let selected := ("rest", rest) :: ("after", after) :: ("first", first) :: bindings
  let tailed := ("end", ending) :: ("final", final) :: ("tail", listValue tail) :: selected
  let valued := ("arguments", listValue (first :: tail)) :: tailed
  rw [expressions_shape]
  apply if_returns program bindings state state state _ (boolean false) _ _ _
  · apply native_binary_call_returns program bindings state state state state "==" (.var "count") (natural 0)
      (natural (count + 1)) (natural 0) (boolean false)
      (by decide) (by decide) (by decide +kernel) (by decide +kernel) _ _ _ (by decide)
    · exact variable_returns program bindings state "count"
    · exact grounded_returns program bindings state (.int 0)
    · simp [StdLib.structural_equality, natural, boolean]
      omega
  · simp only [boolean]
    rw [expressions_more_shape]
    apply if_returns program bindings state state state _ (boolean true) _ _ _
    · apply native_binary_call_returns program bindings state state state state "<" (natural 0) (.var "fuel")
        (natural 0) (natural (fuel + 1)) (boolean true)
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) _ _ _ (by decide)
      · exact grounded_returns program bindings state (.int 0)
      · exact variable_returns program bindings state "fuel"
      · simp [StdLib.less_comparison, natural, boolean]
    · apply case_returns program bindings selected state state state _
        (optionValue (some (.expression [.symbol "MM0:MMBUExpression", first, after, rest]))) expressionsFirst _ _
        expressionsFirstCases (read_cases_encoded expressionsFirstCases)
      · exact firstReturns
      · simp [expressions_first_cases, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
          SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup, selected, bindings, expressionsEnvironment, optionValue]
      · rw [expressions_first_shape]
        apply case_returns program selected tailed state state state _
          (optionValue (some (unifyExpressionsValue tail final ending))) expressionsTail _ _
          expressionsTailCases (read_cases_encoded expressionsTailCases)
        · exact tailReturns
        · simp [expressions_tail_cases, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
            SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup, tailed, selected, bindings,
            expressionsEnvironment, unifyExpressionsValue, optionValue]
        · rw [expressions_tail_shape]
          apply let_returns program tailed valued state state state (.var "arguments") _ _ (listValue (first :: tail)) _
          · apply MMBProofRunExecution.checker_returns (by decide +kernel)
            apply ListAccess.cons_captured_returns tailed state first tail "first" "tail"
            · simp [tailed, selected, bindings, expressionsEnvironment, applySubst, Subst.lookup]
            · rfl
          · simp [SpaceSemantics.matchValue, matchAtom, Subst.lookup, valued, tailed, selected, bindings, expressionsEnvironment]
          · apply expressions_success_returns valued state (first :: tail) final ending rfl <;>
              simp [valued, tailed, applySubst, Subst.lookup]

private def referenceCodes (references : List ((Nat × Nat × Nat) × Atom)) : List Atom :=
  references.map fun reference => MMBExecution.commandValue 50 reference.1.1 reference.1.2.1 reference.1.2.2

private theorem expressions_references_body_returns (state : State) (resolver sorts terms theorems : Atom)
    (slots dummies : List Atom) (arity : Nat) (rest : List Atom) (budget : Nat)
    (references : List ((Nat × Nat × Nat) × Atom))
    (filled : ∀ reference ∈ references, slots[reference.1.1]? = some (optionValue (some reference.2))) :
    PureReturns program
      (expressionsEnvironment resolver (tablesValue sorts terms theorems) (references.length + budget + 1)
        references.length (unifyStateValue slots dummies arity) (listValue (referenceCodes references ++ rest)))
      state expressionsEquation.body state (optionValue (some
        (unifyExpressionsValue (references.map Prod.snd) (unifyStateValue slots dummies arity) (listValue rest)))) := by
  induction references with
  | nil =>
      simpa [referenceCodes] using expressions_empty_body_returns state resolver (tablesValue sorts terms theorems)
        (budget + 1) (unifyStateValue slots dummies arity) (listValue rest)
  | cons reference references ih =>
      let bindings := expressionsEnvironment resolver (tablesValue sorts terms theorems)
        (references.length + budget + 1 + 1) (references.length + 1)
        (unifyStateValue slots dummies arity) (listValue (referenceCodes (reference :: references) ++ rest))
      let selected := ("rest", listValue (referenceCodes references ++ rest)) ::
        ("after", unifyStateValue slots dummies arity) :: ("first", reference.2) :: bindings
      have firstFilled := filled reference (by simp)
      have tailFilled : ∀ entry ∈ references, slots[entry.1.1]? = some (optionValue (some entry.2)) := by
        intro entry inside
        exact filled entry (by simp [inside])
      have firstBody := reference_filled_body_returns state resolver sorts terms theorems reference.2
        (references.length + budget) reference.1.1 reference.1.2.1 reference.1.2.2 slots dummies arity
        (referenceCodes references ++ rest) firstFilled
      have firstReturned : PureReturns program bindings state
          (.expression [.symbol "mm0:mmb:unify-expression", .var "state", .var "tables",
            .expression [.symbol "-", .var "fuel", natural 1], .var "unify", .var "codes"])
          state (optionValue (some (.expression [.symbol "MM0:MMBUExpression", reference.2,
            unifyStateValue slots dummies arity, listValue (referenceCodes references ++ rest)]))) := by
        apply expression_call_from_body bindings state resolver sorts terms theorems
          (references.length + budget + 1) slots dummies arity
          (MMBExecution.commandValue 50 reference.1.1 reference.1.2.1 reference.1.2.2 :: referenceCodes references ++ rest) _
          (.var "state") (.var "tables") (.expression [.symbol "-", .var "fuel", natural 1]) (.var "unify") (.var "codes")
        · rfl
        · rfl
        · exact decrement_returns bindings state (references.length + budget + 1) "fuel" rfl
        · rfl
        · rfl
        · exact expression_reference_from_body state resolver sorts terms theorems
            (references.length + budget) reference.1.1 reference.1.2.1 reference.1.2.2 slots dummies arity
            (referenceCodes references ++ rest) _ firstBody
      have tailReturned : PureReturns program selected state
          (.expression [.symbol "mm0:mmb:unify-expressions", .var "state", .var "tables",
            .expression [.symbol "-", .var "fuel", natural 1], .expression [.symbol "-", .var "count", natural 1],
            .var "after", .var "rest"])
          state (optionValue (some (unifyExpressionsValue (references.map Prod.snd)
            (unifyStateValue slots dummies arity) (listValue rest)))) := by
        apply expressions_call_from_body selected state resolver (tablesValue sorts terms theorems)
          (references.length + budget + 1) references.length (unifyStateValue slots dummies arity)
          (listValue (referenceCodes references ++ rest)) _
          (.var "state") (.var "tables") (.expression [.symbol "-", .var "fuel", natural 1])
          (.expression [.symbol "-", .var "count", natural 1]) (.var "after") (.var "rest")
        · simp [selected, bindings, expressionsEnvironment, applySubst, Subst.lookup]
        · simp [selected, bindings, expressionsEnvironment, applySubst, Subst.lookup]
        · apply decrement_returns selected state (references.length + budget + 1) "fuel"
          simp [selected, bindings, expressionsEnvironment, applySubst, Subst.lookup]
        · apply decrement_returns selected state references.length "count"
          simp [selected, bindings, expressionsEnvironment, applySubst, Subst.lookup]
        · rfl
        · rfl
        · exact ih tailFilled
      simpa only [List.length_cons, List.map_cons, Nat.add_right_comm] using
        expressions_cons_body_returns state resolver (tablesValue sorts terms theorems)
          (references.length + budget + 1) references.length (unifyStateValue slots dummies arity)
          (listValue (referenceCodes (reference :: references) ++ rest)) reference.2
          (unifyStateValue slots dummies arity) (listValue (referenceCodes references ++ rest))
          (unifyStateValue slots dummies arity) (listValue rest) (references.map Prod.snd) firstReturned tailReturned

/-- The original recursive child decoder consumes an arbitrary finite ordered
family of filled references. Physical start/end metadata, repeated references,
inert stored fields and the unread tail survive the actual source execution.
The fuel is the source recursion budget, not a runtime-cost estimate. -/
theorem unify_expressions_references_returns (bindings : Subst) (state : State)
    (resolver sorts terms theorems : Atom) (slots dummies : List Atom) (arity : Nat) (rest : List Atom) (budget : Nat)
    (references : List ((Nat × Nat × Nat) × Atom))
    (filled : ∀ reference ∈ references, slots[reference.1.1]? = some (optionValue (some reference.2)))
    (resolverName tablesName fuelName countName unifyName codesName : String)
    (resolverCaptured : applySubst bindings (.var resolverName) = resolver)
    (tablesCaptured : applySubst bindings (.var tablesName) = tablesValue sorts terms theorems)
    (fuelCaptured : applySubst bindings (.var fuelName) = natural (references.length + budget + 1))
    (countCaptured : applySubst bindings (.var countName) = natural references.length)
    (unifyCaptured : applySubst bindings (.var unifyName) = unifyStateValue slots dummies arity)
    (codesCaptured : applySubst bindings (.var codesName) = listValue
      (references.map (fun reference => MMBExecution.commandValue 50 reference.1.1 reference.1.2.1 reference.1.2.2) ++ rest)) :
    PureReturns program bindings state
      (.expression [.symbol "mm0:mmb:unify-expressions", .var resolverName, .var tablesName, .var fuelName,
        .var countName, .var unifyName, .var codesName]) state
      (optionValue (some (unifyExpressionsValue (references.map Prod.snd) (unifyStateValue slots dummies arity) (listValue rest)))) := by
  apply expressions_call_from_body bindings state resolver (tablesValue sorts terms theorems)
    (references.length + budget + 1) references.length (unifyStateValue slots dummies arity)
    (listValue (referenceCodes references ++ rest)) _ (.var resolverName) (.var tablesName) (.var fuelName)
    (.var countName) (.var unifyName) (.var codesName) resolverCaptured tablesCaptured
    (by simpa [fuelCaptured] using variable_returns program bindings state fuelName)
    (by simpa [countCaptured] using variable_returns program bindings state countName)
    unifyCaptured codesCaptured
  exact expressions_references_body_returns state resolver sorts terms theorems slots dummies arity rest budget references filled

private theorem expressions_zero_body_returns (state : State) (resolver tables : Atom) (count : Nat) (unify codes : Atom) :
    PureReturns program (expressionsEnvironment resolver tables 0 (count + 1) unify codes)
      state expressionsEquation.body state (.symbol "None") := by
  let bindings := expressionsEnvironment resolver tables 0 (count + 1) unify codes
  rw [expressions_shape]
  apply if_returns program bindings state state state _ (boolean false) _ _ _
  · apply native_binary_call_returns program bindings state state state state "==" (.var "count") (natural 0)
      (natural (count + 1)) (natural 0) (boolean false)
      (by decide) (by decide) (by decide +kernel) (by decide +kernel) _ _ _ (by decide)
    · exact variable_returns program bindings state "count"
    · exact grounded_returns program bindings state (.int 0)
    · simp [StdLib.structural_equality, natural, boolean]
      omega
  · simp only [boolean]
    rw [expressions_more_shape]
    apply if_returns program bindings state state state _ (boolean false) _ _ _
    · apply native_binary_call_returns program bindings state state state state "<" (natural 0) (.var "fuel")
        (natural 0) (natural 0) (boolean false)
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) _ _ _ (by decide)
      · exact grounded_returns program bindings state (.int 0)
      · exact variable_returns program bindings state "fuel"
      · simp [StdLib.less_comparison, natural, boolean]
    · exact symbol_returns program bindings state "None"

/-- A positive child count with zero source fuel is refused before inspecting
its supplied state or command fields. This complements the successful empty
child-list law, which bypasses the fuel test. -/
theorem unify_expressions_zero_returns (bindings : Subst) (state : State) (resolver tables : Atom)
    (count : Nat) (unify codes : Atom)
    (resolverName tablesName fuelName countName unifyName codesName : String)
    (resolverCaptured : applySubst bindings (.var resolverName) = resolver)
    (tablesCaptured : applySubst bindings (.var tablesName) = tables)
    (fuelCaptured : applySubst bindings (.var fuelName) = natural 0)
    (countCaptured : applySubst bindings (.var countName) = natural (count + 1))
    (unifyCaptured : applySubst bindings (.var unifyName) = unify)
    (codesCaptured : applySubst bindings (.var codesName) = codes) :
    PureReturns program bindings state (.expression [.symbol "mm0:mmb:unify-expressions", .var resolverName,
      .var tablesName, .var fuelName, .var countName, .var unifyName, .var codesName]) state (.symbol "None") := by
  apply expressions_call_from_body bindings state resolver tables 0 (count + 1) unify codes _
    (.var resolverName) (.var tablesName) (.var fuelName) (.var countName) (.var unifyName) (.var codesName)
    resolverCaptured tablesCaptured
    (by simpa [fuelCaptured] using variable_returns program bindings state fuelName)
    (by simpa [countCaptured] using variable_returns program bindings state countName)
    unifyCaptured codesCaptured
  exact expressions_zero_body_returns state resolver tables count unify codes

private def hypothesesExpressionCases := casesOf (match hypothesesCons with
  | .expression [_, _, body, _] => body | _ => .symbol "None")
private def hypothesesExpressionFound := (hypothesesExpressionCases[0]'(by decide)).2
private theorem hypotheses_cons_shape : hypothesesCons =
    .expression [.symbol "if", .expression [.symbol "<", natural 0, .var "fuel"],
      .expression [.symbol "case", .expression [.symbol "mm0:mmb:unify-expression", .var "state", .var "tables",
        .expression [.symbol "-", .var "fuel", natural 1], .var "unify", .expression [.symbol "MM0:L", .var "rest"]],
        .expression (hypothesesExpressionCases.map fun row => .expression [row.1, row.2])], .symbol "None"] := by decide
private theorem hypotheses_expression_cases : hypothesesExpressionCases =
    [(.expression [.symbol "Some", .expression [.symbol "MM0:MMBUExpression", .var "first",
      .expression [.symbol "MM0:MMBUState", .var "slots", .expression [.symbol "MM0:L", .expression []], .var "arity"], .var "remaining"]],
      hypothesesExpressionFound), (.var "bad", .symbol "None")] := by decide
private def hypothesesCommandEnvironment (resolver tables : Atom) (fuel data start after : Nat)
    (unify : Atom) (codes : List Atom) : Subst :=
  ("rest", .expression codes) :: ("after", natural after) :: ("start", natural start) :: ("data", natural data) ::
    hypothesesEnvironment resolver tables (fuel + 1) unify (MMBExecution.commandValue 54 data start after :: codes)

private theorem hypotheses_dummies_body_returns (state : State) (resolver tables : Atom) (fuel data start after : Nat)
    (unify : Atom) (codes : List Atom) (first : Atom) (slots : List Atom) (dummy : Atom) (dummies : List Atom)
    (arity : Nat) (remaining : List Atom)
    (childReturns : PureReturns program (hypothesesCommandEnvironment resolver tables fuel data start after unify codes)
      state (.expression [.symbol "mm0:mmb:unify-expression", .var "state", .var "tables",
        .expression [.symbol "-", .var "fuel", natural 1], .var "unify", .expression [.symbol "MM0:L", .var "rest"]])
      state (optionValue (some (unifyExpressionValue first slots (dummy :: dummies) arity remaining)))) :
    PureReturns program
      (hypothesesEnvironment resolver tables (fuel + 1) unify (MMBExecution.commandValue 54 data start after :: codes))
      state hypothesesEquation.body state (.symbol "None") := by
  let bindings := hypothesesEnvironment resolver tables (fuel + 1) unify (MMBExecution.commandValue 54 data start after :: codes)
  let selected := hypothesesCommandEnvironment resolver tables fuel data start after unify codes
  let result := optionValue (some (unifyExpressionValue first slots (dummy :: dummies) arity remaining))
  rw [hypotheses_shape]
  apply case_returns program bindings selected state state state (.var "codes")
    (.expression (MMBExecution.commandValue 54 data start after :: codes)) hypothesesCons _ _
    hypothesesCases (read_cases_encoded hypothesesCases)
  · exact variable_returns program bindings state "codes"
  · simp [hypotheses_cases_shape, MMBExecution.commandValue, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
      SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup, selected, bindings,
      hypothesesCommandEnvironment, hypothesesEnvironment, natural]
  · rw [hypotheses_cons_shape]
    apply if_returns program selected state state state _ (boolean true) _ _ _
    · apply native_binary_call_returns program selected state state state state "<" (natural 0) (.var "fuel")
        (natural 0) (natural (fuel + 1)) (boolean true)
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) _ _ _ (by decide)
      · exact grounded_returns program selected state (.int 0)
      · exact variable_returns program selected state "fuel"
      · simp [StdLib.less_comparison, natural, boolean]
    · apply case_returns program selected (("bad", result) :: selected) state state state _ result (.symbol "None") _ _
        hypothesesExpressionCases (read_cases_encoded hypothesesExpressionCases)
      · exact childReturns
      · simp [hypotheses_expression_cases, result, unifyExpressionValue, unifyStateValue, optionValue, listValue,
          SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
          matchAtom, Subst.lookup, selected, hypothesesCommandEnvironment, hypothesesEnvironment]
      · exact symbol_returns program _ state "None"

/-- The actual source refuses a dummy introduced while reading a hypothesis,
even if the current sort map resolves it successfully. The guard follows the
child decoder; it cannot be replaced by a guard only on the conclusion. -/
theorem unify_hypotheses_dummy_refused_returns (bindings : Subst) (state : State) (published : Atom)
    (sorts terms theorems : List MMUResolution.Binding) (nextSort nextTerm nextTheorem : Nat) (images : Atom)
    (tableSorts tableTerms tableTheorems sort : Atom) (fuel data start after binary dummyStart dummyAfter : Nat)
    (slots dummies : List Atom) (arity : Nat) (rest : List Atom)
    (declared : MMUResolution.lookup sorts (natural binary) = some sort)
    (resolverName tablesName fuelName unifyName codesName : String)
    (resolverCaptured : applySubst bindings (.var resolverName) = resolverValue published sorts terms theorems nextSort nextTerm nextTheorem images)
    (tablesCaptured : applySubst bindings (.var tablesName) = tablesValue tableSorts tableTerms tableTheorems)
    (fuelCaptured : applySubst bindings (.var fuelName) = natural (fuel + 1 + 1))
    (unifyCaptured : applySubst bindings (.var unifyName) = unifyStateValue slots dummies arity)
    (codesCaptured : applySubst bindings (.var codesName) = listValue
      (MMBExecution.commandValue 54 data start after :: MMBExecution.commandValue 51 binary dummyStart dummyAfter :: rest)) :
    PureReturns program bindings state (.expression [.symbol "mm0:mmb:unify-hypotheses", .var resolverName,
      .var tablesName, .var fuelName, .var unifyName, .var codesName]) state (.symbol "None") := by
  let resolver := resolverValue published sorts terms theorems nextSort nextTerm nextTheorem images
  let tables := tablesValue tableSorts tableTerms tableTheorems
  let codes := MMBExecution.commandValue 51 binary dummyStart dummyAfter :: rest
  let selected := hypothesesCommandEnvironment resolver tables (fuel + 1) data start after
    (unifyStateValue slots dummies arity) codes
  have freshNonempty : dummies ++ [sort] = (dummies ++ [sort]).head! :: (dummies ++ [sort]).tail := by
    cases dummies <;> simp
  have child : PureReturns program selected state
      (.expression [.symbol "mm0:mmb:unify-expression", .var "state", .var "tables",
        .expression [.symbol "-", .var "fuel", natural 1], .var "unify", .expression [.symbol "MM0:L", .var "rest"]])
      state (optionValue (some (unifyExpressionValue (Data.preterm (.var (arity + dummies.length)))
        (slots ++ [optionValue (some (Data.preterm (.var (arity + dummies.length))))])
        (dummies ++ [sort]) arity rest))) := by
    apply expression_call_from_body selected state resolver tableSorts tableTerms tableTheorems (fuel + 1)
      slots dummies arity codes _ (.var "state") (.var "tables") (.expression [.symbol "-", .var "fuel", natural 1])
      (.var "unify") (.expression [.symbol "MM0:L", .var "rest"])
    · simp [selected, hypothesesCommandEnvironment, hypothesesEnvironment, applySubst, Subst.lookup, tables]
    · simp [selected, hypothesesCommandEnvironment, hypothesesEnvironment, applySubst, Subst.lookup, tables]
    · apply decrement_returns selected state (fuel + 1) "fuel"
      simp [selected, hypothesesCommandEnvironment, hypothesesEnvironment, applySubst, Subst.lookup, tables]
    · simp [selected, hypothesesCommandEnvironment, hypothesesEnvironment, applySubst, Subst.lookup, tables]
    · simp [selected, hypothesesCommandEnvironment, hypothesesEnvironment, applySubst, applySubst.applySubstList, Subst.lookup, listValue, codes]
    · apply expression_command_from_body state resolver tableSorts tableTerms tableTheorems fuel 51 binary dummyStart dummyAfter slots dummies arity rest expressionDummy _
      · simp [expression_opcode_cases, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom, natural]
      · simpa [dummyResultValue, declared, resolver] using dummy_body_returns state published sorts terms theorems
          nextSort nextTerm nextTheorem images tableSorts tableTerms tableTheorems fuel binary dummyStart dummyAfter slots dummies arity rest
  have rejected := hypotheses_dummies_body_returns state resolver tables (fuel + 1) data start after
    (unifyStateValue slots dummies arity) codes (Data.preterm (.var (arity + dummies.length)))
    (slots ++ [optionValue (some (Data.preterm (.var (arity + dummies.length))))])
    (dummies ++ [sort]).head! (dummies ++ [sort]).tail arity rest (by simpa only [← freshNonempty] using child)
  apply authored_variable_call_returns program bindings
    (hypothesesEnvironment resolver tables (fuel + 1 + 1) (unifyStateValue slots dummies arity)
      (MMBExecution.commandValue 54 data start after :: codes)) state state "mm0:mmb:unify-hypotheses"
    [resolverName, tablesName, fuelName, unifyName, codesName] hypothesesEquation.body _
    (by decide +kernel) (by decide +kernel) (by decide +kernel) _ rejected (by decide)
  simpa [resolverCaptured, tablesCaptured, fuelCaptured, unifyCaptured, codesCaptured, resolver, tables, codes] using
    hypotheses_clause resolver tables (fuel + 1 + 1) (unifyStateValue slots dummies arity)
      (MMBExecution.commandValue 54 data start after :: codes)


/-- The declaration decoder retains the original source's per-hypothesis
dummy guard, including a freshly introduced dummy. -/
theorem statements_refuses_dummy_hypothesis (arity sort : Nat) :
    Formats.MMB.Statements.decodeHyps (fun _ => none) arity 2 (Formats.MMB.Statements.initial arity)
      [.hyp, .dummy sort] = none := by
  simp [Formats.MMB.Statements.decodeHyps, Formats.MMB.Statements.decodeExpr,
    Formats.MMB.Statements.initial]


/-- Original binary term-table entry fields; only the child descriptor count
is used by Polish term decoding. Declaration validation is separate. -/
def termEntryValue (sort : Atom) (arguments : List Atom) (ret value : Atom) : Atom :=
  .expression [.symbol "MM0:MMBTerm", sort, listValue arguments, ret, value]

/-- The source fills the reserved physical slot after all children return.
The raw slot update may still fail if a supplied continuation lost that slot. -/
def completedTermResult (identifier : Nat) (arguments : List Kernel.Preterm)
    (slots dummies : List Atom) (arity index : Nat) (save : Bool) (rest : List Atom) : Atom :=
  let expression := Data.preterm (Kernel.Preterm.applyArgs (.term identifier) arguments)
  let final := if save then (slots[index]?).map fun _ => slots.set index (optionValue (some expression)) else some slots
  optionValue (final.map fun final => unifyExpressionValue expression final dummies arity rest)

private def termEquation := sourceEquation "mm0:mmb:unify-term"
private def termCases := casesOf (match termEquation.body with | .expression [_, _, body] => body | _ => .symbol "None")
private def termFound := (termCases[0]'(by decide)).2
private def termChildCases := casesOf (match termFound with | .expression [_, _, body] => body | _ => .symbol "None")
private def termFinish := (termChildCases[0]'(by decide)).2
private def termUpdatedCases := casesOf (match termFinish with | .expression [_, _, body] => body | _ => .symbol "None")
private def termUpdatedFound := (termUpdatedCases[0]'(by decide)).2
private theorem term_finish_shape : termFinish =
    .expression [.symbol "let*", .expression [
      .expression [.var "term", .expression [.symbol "mm0:make-term", .var "id"]],
      .expression [.var "expression", .expression [.symbol "mm0:apply-args", .var "term", .var "arguments"]],
      .expression [.var "updated", .expression [.symbol "if", .var "save",
        .expression [.symbol "mm0:mmb:set-at", .var "afterSlots", .var "index", .expression [.symbol "Some", .var "expression"]],
        .expression [.symbol "Some", .var "afterSlots"]]]],
      .expression [.symbol "case", .var "updated", .expression (termUpdatedCases.map fun row => .expression [row.1, row.2])]] := by decide
private theorem term_updated_cases : termUpdatedCases =
    [(.expression [.symbol "Some", .var "final"], termUpdatedFound), (.var "bad", .symbol "None")] := by decide
private theorem term_updated_found_shape : termUpdatedFound =
    .expression [.symbol "Some", .expression [.symbol "MM0:MMBUExpression", .var "expression",
      .expression [.symbol "MM0:MMBUState", .var "final", .var "extra", .var "count"], .var "rest"]] := by decide

private theorem make_term_captured_returns (bindings : Subst) (state : State) (index : Nat) (name : String)
    (captured : applySubst bindings (.var name) = natural index) :
    PureReturns program bindings state (.expression [.symbol "mm0:make-term", .var name]) state (Data.preterm (.term index)) := by
  have returned := MMBProofRunExecution.checker_returns (by
    simp only [codeWithin, natural, expressionHeadWithin, atomsWithin]
    decide +kernel) (Data.make_term_returns [] state index)
  apply captured_call_returns program [] bindings state state "mm0:make-term" [natural index] [.var name] _
    (by decide +kernel) (by decide) _ _ _ returned
  · intro offset argument found
    simp only [List.getElem?_cons, List.getElem?_nil] at found
    split at found
    · simp only [Option.some.injEq] at found; subst argument; right; rfl
    · contradiction
  · intro offset argument found
    simp only [List.getElem?_cons, List.getElem?_nil] at found
    split at found
    · simp only [Option.some.injEq] at found; subst argument; right; rfl
    · contradiction
  · change [natural index] = [applySubst bindings (.var name)]
    rw [captured]

private theorem term_result_constructor_returns (bindings : Subst) (state : State) (expression : Atom)
    (slots dummies : List Atom) (arity : Nat) (rest : List Atom)
    (expressionCaptured : applySubst bindings (.var "expression") = expression)
    (slotsCaptured : applySubst bindings (.var "final") = listValue slots)
    (dummiesCaptured : applySubst bindings (.var "extra") = listValue dummies)
    (arityCaptured : applySubst bindings (.var "count") = natural arity)
    (restCaptured : applySubst bindings (.var "rest") = listValue rest) :
    PureReturns program bindings state termUpdatedFound state
      (optionValue (some (unifyExpressionValue expression slots dummies arity rest))) := by
  rw [term_updated_found_shape]
  apply unary_constructor_of_returns program bindings state state "Some" _ _ (by decide +kernel) (by decide)
  apply data_call_returns program bindings state state "MM0:MMBUExpression" _ _ (by decide +kernel) _ (by decide)
  apply evaluated_argument_returns program bindings state state state .data (.symbol "MM0:MMBUExpression")
    (.symbol "MM0:MMBUExpression") _ _ [] 0 rfl (symbol_returns program bindings state "MM0:MMBUExpression")
  apply evaluated_argument_returns program bindings state state state .data (.var "expression") expression _ _
    [.symbol "MM0:MMBUExpression"] 1 rfl (by simpa [expressionCaptured] using variable_returns program bindings state "expression")
  apply evaluated_argument_returns program bindings state state state .data
    (.expression [.symbol "MM0:MMBUState", .var "final", .var "extra", .var "count"])
    (unifyStateValue slots dummies arity) _ _ [.symbol "MM0:MMBUExpression", expression] 2 rfl
  · simpa [slotsCaptured, dummiesCaptured, arityCaptured, unifyStateValue] using
      constructor_variables_return program bindings state "MM0:MMBUState" ["final", "extra", "count"] (by decide +kernel) (by decide)
  · simpa [expressionCaptured, restCaptured, unifyExpressionValue] using
      variable_arguments_return program bindings state state .data ["rest"]
        [.symbol "MM0:MMBUExpression", expression, unifyStateValue slots dummies arity] 3
        (unifyExpressionValue expression slots dummies arity rest)
        (by simpa [restCaptured, unifyExpressionValue] using (data_arguments_values_return program bindings state
          [.symbol "MM0:MMBUExpression", expression, unifyStateValue slots dummies arity, listValue rest] 4))

private theorem set_slot_captured_returns (bindings : Subst) (state : State) (slots : List Atom)
    (index : Nat) (expression : Atom)
    (slotsCaptured : applySubst bindings (.var "afterSlots") = listValue slots)
    (indexCaptured : applySubst bindings (.var "index") = natural index)
    (expressionCaptured : applySubst bindings (.var "expression") = expression) :
    PureReturns program bindings state
      (.expression [.symbol "mm0:mmb:set-at", .var "afterSlots", .var "index", .expression [.symbol "Some", .var "expression"]])
      state (MMBSlotExecution.setResult slots index (optionValue (some expression))) := by
  let prior : Subst := [("value", optionValue (some expression)), ("index", natural index), ("slots", listValue slots)]
  have returned := MMBSlotExecution.set_at_returns prior state slots index (optionValue (some expression))
    "slots" "index" "value" rfl rfl rfl
  apply captured_call_returns program prior bindings state state "mm0:mmb:set-at"
    [.var "slots", .var "index", .var "value"] [.var "afterSlots", .var "index", .expression [.symbol "Some", .var "expression"]] _
    (by decide +kernel) (by decide) _ _ _ returned
  · intro offset argument found
    have bounded : offset < 3 := by have inside := (getElem?_eq_some_iff.mp found).choose; simpa using inside
    interval_cases offset <;> simp at found <;> subst argument <;> right <;> rfl
  · intro offset argument found
    have bounded : offset < 3 := by have inside := (getElem?_eq_some_iff.mp found).choose; simpa using inside
    interval_cases offset
    · simp at found; subst argument; right; rfl
    · simp at found; subst argument; right; rfl
    · left; decide +kernel
  · change [listValue slots, natural index, optionValue (some expression)] =
      [applySubst bindings (.var "afterSlots"), applySubst bindings (.var "index"),
        applySubst bindings (.expression [.symbol "Some", .var "expression"])]
    have valueCaptured : applySubst bindings (.expression [.symbol "Some", .var "expression"]) = optionValue (some expression) := by
      change Atom.expression [.symbol "Some", applySubst bindings (.var "expression")] = _
      rw [expressionCaptured]; rfl
    rw [slotsCaptured, indexCaptured, valueCaptured]

private theorem lookup_cons (bindings : Subst) (key name : String) (value : Atom) :
    Subst.lookup ((key, value) :: bindings) name =
      if key == name then some value else Subst.lookup bindings name := by
  simp only [Subst.lookup, List.find?_cons]
  split <;> simp_all
private theorem captured_cons (bindings : Subst) (key name : String) (value : Atom) :
    applySubst ((key, value) :: bindings) (.var name) =
      if key == name then value else applySubst bindings (.var name) := by
  simp only [applySubst, lookup_cons]
  split <;> simp

private theorem term_finish_returns (bindings : Subst) (state : State) (identifier : Nat)
    (arguments : List Kernel.Preterm) (slots dummies : List Atom) (arity index : Nat) (save : Bool) (rest : List Atom)
    (identifierCaptured : applySubst bindings (.var "id") = natural identifier)
    (argumentsCaptured : applySubst bindings (.var "arguments") = listValue (arguments.map Data.preterm))
    (slotsCaptured : applySubst bindings (.var "afterSlots") = listValue slots)
    (dummiesCaptured : applySubst bindings (.var "extra") = listValue dummies)
    (arityCaptured : applySubst bindings (.var "count") = natural arity)
    (indexCaptured : applySubst bindings (.var "index") = natural index)
    (saveCaptured : applySubst bindings (.var "save") = boolean save)
    (restCaptured : applySubst bindings (.var "rest") = listValue rest)
    (fresh : ∀ name ∈ ["term", "expression", "updated", "final", "bad"], Subst.lookup bindings name = none) :
    PureReturns program bindings state termFinish state (completedTermResult identifier arguments slots dummies arity index save rest) := by
  let expression := Data.preterm (Kernel.Preterm.applyArgs (.term identifier) arguments)
  let made := ("term", Data.preterm (.term identifier)) :: bindings
  let applied := ("expression", expression) :: made
  let finalSlots := if save then (slots[index]?).map (fun _ => slots.set index (optionValue (some expression))) else some slots
  let updated := ("updated", optionValue (finalSlots.map listValue)) :: applied
  have termFresh := fresh "term" (by simp)
  have expressionFresh := fresh "expression" (by simp)
  have updatedFresh := fresh "updated" (by simp)
  have finalFresh := fresh "final" (by simp)
  have badFresh := fresh "bad" (by simp)
  rw [term_finish_shape]
  apply let_star_returns program bindings state state _ _ _ _ rfl
  apply let_returns program bindings made state state state (.var "term") _ _ (Data.preterm (.term identifier)) _
  · exact make_term_captured_returns bindings state identifier "id" identifierCaptured
  · simp [SpaceSemantics.matchValue, matchAtom, termFresh, made]
  · apply let_returns program made applied state state state (.var "expression") _ _ expression _
    · apply MMBProofRunExecution.checker_returns (by decide +kernel)
      apply Application.captured_returns made state (.term identifier) arguments "term" "arguments"
      · simp [made, captured_cons]
      · simpa [made, captured_cons] using argumentsCaptured
    · simp [SpaceSemantics.matchValue, matchAtom, expressionFresh, applied, made, lookup_cons]
    · apply let_returns program applied updated state state state (.var "updated") _ _
        (optionValue (finalSlots.map listValue)) _
      · apply if_returns program applied state state state (.var "save") (boolean save) _ _ _
        · simpa [applied, made, captured_cons, saveCaptured] using variable_returns program applied state "save"
        · cases save with
          | false =>
              simpa [finalSlots, optionValue, applied, made, captured_cons, slotsCaptured, boolean] using
                unary_constructor_returns program applied state "Some" "afterSlots" (by decide +kernel) (by decide)
          | true =>
              simpa [finalSlots, MMBSlotExecution.setResult, Function.comp_def] using
                set_slot_captured_returns applied state slots index expression
                  (by simpa [applied, made, captured_cons] using slotsCaptured)
                  (by simpa [applied, made, captured_cons] using indexCaptured)
                  (by simp [applied, captured_cons])
      · simp [SpaceSemantics.matchValue, matchAtom, updatedFresh, updated, applied, made, lookup_cons]
      · cases found : finalSlots with
        | none =>
            apply case_returns program updated (("bad", .symbol "None") :: updated) state state state (.var "updated")
              (.symbol "None") (.symbol "None") _ _ termUpdatedCases (read_cases_encoded termUpdatedCases)
            · simpa [updated, found, captured_cons, optionValue] using variable_returns program updated state "updated"
            · simp [term_updated_cases, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom,
                updated, applied, made, lookup_cons, badFresh]
            · change PureReturns program (("bad", .symbol "None") :: updated) state (.symbol "None") state
                (optionValue (finalSlots.map fun final => unifyExpressionValue expression final dummies arity rest))
              rw [found]
              exact symbol_returns program _ state "None"
        | some final =>
            let completed := ("final", listValue final) :: updated
            apply case_returns program updated completed state state state (.var "updated")
              (optionValue (some (listValue final))) termUpdatedFound _ _ termUpdatedCases (read_cases_encoded termUpdatedCases)
            · simpa [updated, found, captured_cons] using variable_returns program updated state "updated"
            · simp [term_updated_cases, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
                SpaceSemantics.matchValue.matchValues, matchAtom, completed, updated, applied, made,
                lookup_cons, finalFresh, optionValue]
            · simpa [completedTermResult, expression, finalSlots, found] using
                term_result_constructor_returns completed state expression final dummies arity rest
                  (by simp [completed, updated, applied, made, captured_cons])
                  (by simp [completed, captured_cons])
                  (by simpa [completed, updated, applied, made, captured_cons] using dummiesCaptured)
                  (by simpa [completed, updated, applied, made, captured_cons] using arityCaptured)
                  (by simpa [completed, updated, applied, made, captured_cons] using restCaptured)

private def termEnvironment (resolver tableSorts tableTerms tableTheorems : Atom) (fuel : Nat)
    (slots dummies : List Atom) (arity binary : Nat) (save : Bool) (codes : List Atom) : Subst :=
  [("codes", listValue codes), ("save", boolean save), ("binary", natural binary),
   ("arity", natural arity), ("dummies", listValue dummies), ("slots", .expression slots),
   ("fuel", natural fuel), ("theorems", tableTheorems), ("terms", tableTerms),
   ("sorts", tableSorts), ("state", resolver)]
private def termReadEnvironment (resolver tableSorts tableTheorems : Atom) (fuel : Nat)
    (slots dummies : List Atom) (arity binary identifier : Nat) (save : Bool) (codes : List Atom)
    (entries : List Atom) (sort : Atom) (descriptors : List Atom) (ret value : Atom) : Subst :=
  ("entry", optionValue (some (termEntryValue sort descriptors ret value))) ::
    ("found", optionValue (some (natural identifier))) ::
      termEnvironment resolver tableSorts (listValue entries) tableTheorems fuel slots dummies arity binary save codes
private def termSelectedEnvironment (resolver tableSorts tableTheorems : Atom) (fuel : Nat)
    (slots dummies : List Atom) (arity binary identifier : Nat) (save : Bool) (codes : List Atom)
    (entries : List Atom) (sort : Atom) (descriptors : List Atom) (ret value : Atom) : Subst :=
  ("value", value) :: ("ret", ret) :: ("args", .expression descriptors) :: ("sort", sort) ::
    ("id", natural identifier) :: termReadEnvironment resolver tableSorts tableTheorems fuel
      slots dummies arity binary identifier save codes entries sort descriptors ret value
private def termPreparedEnvironment (resolver tableSorts tableTheorems : Atom) (fuel : Nat)
    (slots dummies : List Atom) (arity binary identifier : Nat) (save : Bool) (codes : List Atom)
    (entries : List Atom) (sort : Atom) (descriptors : List Atom) (ret value : Atom) : Subst :=
  ("nextSlots", listValue (if save then slots ++ [.symbol "None"] else slots)) ::
    ("index", natural slots.length) :: termSelectedEnvironment resolver tableSorts tableTheorems fuel
      slots dummies arity binary identifier save codes entries sort descriptors ret value

private theorem term_unique : program.equations.filter (·.head == "mm0:mmb:unify-term") = [termEquation] := by decide +kernel
private theorem term_formals : termEquation.arguments =
    [.var "state", .expression [.symbol "MM0:MMBTables", .var "sorts", .var "terms", .var "theorems"],
     .var "fuel", .expression [.symbol "MM0:MMBUState", .expression [.symbol "MM0:L", .var "slots"], .var "dummies", .var "arity"],
     .var "binary", .var "save", .var "codes"] := by decide
private theorem term_shape : termEquation.body =
    .expression [.symbol "let*", .expression [
      .expression [.var "found", .expression [.symbol "mm0:mmu:term", .var "state", .var "binary"]],
      .expression [.var "entry", .expression [.symbol "mm0:data-at", .var "terms", .var "binary"]]],
      .expression [.symbol "case", .expression [.var "found", .var "entry"],
        .expression (termCases.map fun row => .expression [row.1, row.2])]] := by decide
private theorem term_cases : termCases =
    [(.expression [.expression [.symbol "Some", .var "id"],
      .expression [.symbol "Some", .expression [.symbol "MM0:MMBTerm", .var "sort", .expression [.symbol "MM0:L", .var "args"],
        .var "ret", .var "value"]]], termFound), (.var "bad", .symbol "None")] := by decide
private theorem term_found_shape : termFound =
    .expression [.symbol "let*", .expression [
      .expression [.var "index", .expression [.symbol "size-atom", .var "slots"]],
      .expression [.var "nextSlots", .expression [.symbol "if", .var "save",
        .expression [.symbol "mm0:mmb:snoc", .expression [.symbol "MM0:L", .var "slots"], .symbol "None"],
        .expression [.symbol "MM0:L", .var "slots"]]]],
      .expression [.symbol "case", .expression [.symbol "mm0:mmb:unify-expressions", .var "state",
        .expression [.symbol "MM0:MMBTables", .var "sorts", .var "terms", .var "theorems"],
        .expression [.symbol "-", .var "fuel", natural 1], .expression [.symbol "size-atom", .var "args"],
        .expression [.symbol "MM0:MMBUState", .var "nextSlots", .var "dummies", .var "arity"], .var "codes"],
        .expression (termChildCases.map fun row => .expression [row.1, row.2])]] := by decide
private theorem term_child_cases : termChildCases =
    [(.expression [.symbol "Some", .expression [.symbol "MM0:MMBUExpressions", .var "arguments",
      .expression [.symbol "MM0:MMBUState", .var "afterSlots", .var "extra", .var "count"], .var "rest"]], termFinish),
      (.var "bad", .symbol "None")] := by decide
private theorem term_clause (resolver tableSorts tableTerms tableTheorems : Atom) (fuel : Nat)
    (slots dummies : List Atom) (arity binary : Nat) (save : Bool) (codes : List Atom) :
    clauses program "mm0:mmb:unify-term" [resolver, tablesValue tableSorts tableTerms tableTheorems, natural fuel,
      unifyStateValue slots dummies arity, natural binary, boolean save, listValue codes] =
      [.evaluate (termEnvironment resolver tableSorts tableTerms tableTheorems fuel slots dummies arity binary save codes) termEquation.body] := by
  rw [clauses_use_only_the_named_equations, term_unique]
  simp [term_formals, termEnvironment, tablesValue, unifyStateValue, listValue, boolean,
    SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]

private theorem term_from_body (bindings : Subst) (state : State) (resolver tableSorts tableTerms tableTheorems : Atom)
    (fuel : Nat) (slots dummies : List Atom) (arity binary : Nat) (save : Bool) (codes : List Atom) (answer : Atom)
    (resolverName tablesName fuelName unifyName binaryName saveName codesName : String)
    (resolverCaptured : applySubst bindings (.var resolverName) = resolver)
    (tablesCaptured : applySubst bindings (.var tablesName) = tablesValue tableSorts tableTerms tableTheorems)
    (fuelCaptured : applySubst bindings (.var fuelName) = natural fuel)
    (unifyCaptured : applySubst bindings (.var unifyName) = unifyStateValue slots dummies arity)
    (binaryCaptured : applySubst bindings (.var binaryName) = natural binary)
    (saveCaptured : applySubst bindings (.var saveName) = boolean save)
    (codesCaptured : applySubst bindings (.var codesName) = listValue codes)
    (body : PureReturns program (termEnvironment resolver tableSorts tableTerms tableTheorems fuel slots dummies arity binary save codes)
      state termEquation.body state answer) :
    PureReturns program bindings state (.expression [.symbol "mm0:mmb:unify-term", .var resolverName, .var tablesName,
      .var fuelName, .var unifyName, .var binaryName, .var saveName, .var codesName]) state answer := by
  apply authored_variable_call_returns program bindings
    (termEnvironment resolver tableSorts tableTerms tableTheorems fuel slots dummies arity binary save codes) state state
    "mm0:mmb:unify-term" [resolverName, tablesName, fuelName, unifyName, binaryName, saveName, codesName] termEquation.body _
    (by decide +kernel) (by decide +kernel) (by decide +kernel) _ body (by decide)
  simpa [resolverCaptured, tablesCaptured, fuelCaptured, unifyCaptured, binaryCaptured, saveCaptured, codesCaptured] using
    term_clause resolver tableSorts tableTerms tableTheorems fuel slots dummies arity binary save codes

private def termReadChildren := match termFound with
  | .expression [_, _, body] => body
  | _ => .symbol "None"
private theorem term_read_children_shape : termReadChildren =
    .expression [.symbol "case", .expression [.symbol "mm0:mmb:unify-expressions", .var "state",
      .expression [.symbol "MM0:MMBTables", .var "sorts", .var "terms", .var "theorems"],
      .expression [.symbol "-", .var "fuel", natural 1], .expression [.symbol "size-atom", .var "args"],
      .expression [.symbol "MM0:MMBUState", .var "nextSlots", .var "dummies", .var "arity"], .var "codes"],
      .expression (termChildCases.map fun row => .expression [row.1, row.2]) ] := by decide

private theorem term_prepare_returns (state : State) (resolver tableSorts tableTheorems : Atom) (fuel : Nat)
    (slots dummies : List Atom) (arity binary identifier : Nat) (save : Bool) (codes : List Atom)
    (entries : List Atom) (sort : Atom) (descriptors : List Atom) (ret value : Atom)
    (answer : Atom)
    (continued : PureReturns program
      (termPreparedEnvironment resolver tableSorts tableTheorems fuel slots dummies arity binary identifier save codes entries sort descriptors ret value)
      state termReadChildren state answer) :
    PureReturns program
      (termSelectedEnvironment resolver tableSorts tableTheorems fuel slots dummies arity binary identifier save codes entries sort descriptors ret value)
      state termFound state answer := by
  let selected := termSelectedEnvironment resolver tableSorts tableTheorems fuel slots dummies arity binary identifier save codes entries sort descriptors ret value
  let indexed := ("index", natural slots.length) :: selected
  let reserved := termPreparedEnvironment resolver tableSorts tableTheorems fuel slots dummies arity binary identifier save codes entries sort descriptors ret value
  rw [term_found_shape]
  apply let_star_returns program selected state state _ _ _ _ rfl
  apply let_returns program selected indexed state state state (.var "index") _ _ (natural slots.length) _
  · apply native_variable_call_returns program selected state state "size-atom" ["slots"] (natural slots.length)
      (by decide) (by decide) _ (by decide)
    rfl
  · simp [SpaceSemantics.matchValue, matchAtom, Subst.lookup, indexed, selected,
      termSelectedEnvironment, termReadEnvironment, termEnvironment]
  · apply let_returns program indexed reserved state state state (.var "nextSlots") _ _
      (listValue (if save then slots ++ [.symbol "None"] else slots)) _
    · apply if_returns program indexed state state state (.var "save") (boolean save) _ _ _
      · exact variable_returns program indexed state "save"
      · cases save with
        | false =>
            simpa [boolean, indexed, selected, termSelectedEnvironment, termReadEnvironment, termEnvironment,
              applySubst, Subst.lookup, listValue] using
              unary_constructor_returns program indexed state "MM0:L" "slots" (by decide +kernel) (by decide)
        | true =>
            simpa [boolean] using snoc_captured_returns indexed state slots (.symbol "None")
              (.expression [.symbol "MM0:L", .var "slots"]) (.symbol "None") rfl rfl
    · simp [SpaceSemantics.matchValue, matchAtom, Subst.lookup, reserved, indexed, selected,
        termPreparedEnvironment, termSelectedEnvironment, termReadEnvironment, termEnvironment]
    · exact continued

private theorem term_found_returns (state : State) (resolver tableSorts tableTheorems : Atom) (fuel : Nat)
    (slots dummies : List Atom) (arity binary identifier : Nat) (save : Bool) (codes : List Atom)
    (entries : List Atom) (sort : Atom) (descriptors : List Atom) (ret value : Atom)
    (arguments : List Kernel.Preterm) (afterSlots extra : List Atom) (count : Nat) (rest : List Atom)
    (childReturns : PureReturns program
      (termPreparedEnvironment resolver tableSorts tableTheorems fuel slots dummies arity binary identifier save codes entries sort descriptors ret value)
      state (.expression [.symbol "mm0:mmb:unify-expressions", .var "state",
        .expression [.symbol "MM0:MMBTables", .var "sorts", .var "terms", .var "theorems"],
        .expression [.symbol "-", .var "fuel", natural 1], .expression [.symbol "size-atom", .var "args"],
        .expression [.symbol "MM0:MMBUState", .var "nextSlots", .var "dummies", .var "arity"], .var "codes"])
      state (optionValue (some (unifyExpressionsValue (arguments.map Data.preterm)
        (unifyStateValue afterSlots extra count) (listValue rest))))) :
    PureReturns program
      (termSelectedEnvironment resolver tableSorts tableTheorems fuel slots dummies arity binary identifier save codes entries sort descriptors ret value)
      state termFound state (completedTermResult identifier arguments afterSlots extra count slots.length save rest) := by
  let reserved := termPreparedEnvironment resolver tableSorts tableTheorems fuel slots dummies arity binary identifier save codes entries sort descriptors ret value
  let completed := ("rest", listValue rest) :: ("count", natural count) :: ("extra", listValue extra) ::
    ("afterSlots", listValue afterSlots) :: ("arguments", listValue (arguments.map Data.preterm)) :: reserved
  apply term_prepare_returns state resolver tableSorts tableTheorems fuel slots dummies arity binary identifier save codes entries sort descriptors ret value
  rw [term_read_children_shape]
  apply case_returns program reserved completed state state state _
    (optionValue (some (unifyExpressionsValue (arguments.map Data.preterm)
      (unifyStateValue afterSlots extra count) (listValue rest)))) termFinish _ _
    termChildCases (read_cases_encoded termChildCases)
  · exact childReturns
  · simp [term_child_cases, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
      SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup, completed, reserved,
      termPreparedEnvironment, termSelectedEnvironment, termReadEnvironment, termEnvironment,
      optionValue, unifyExpressionsValue, unifyStateValue, listValue]
  · apply term_finish_returns completed state identifier arguments afterSlots extra count slots.length save rest
    <;> simp [completed, reserved, termPreparedEnvironment, termSelectedEnvironment, termReadEnvironment,
      termEnvironment, applySubst, Subst.lookup]
private theorem term_body_from_found_returns (state : State) (published : Atom)
    (sorts terms theorems : List MMUResolution.Binding) (nextSort nextTerm nextTheorem : Nat) (images : Atom)
    (tableSorts tableTheorems : Atom) (fuel : Nat) (slots dummies : List Atom) (arity binary identifier : Nat)
    (save : Bool) (codes : List Atom) (entries : List Atom) (sort : Atom) (descriptors : List Atom) (ret value : Atom)
    (declared : MMUResolution.lookup terms (natural binary) = some (natural identifier))
    (entryFound : entries[binary]? = some (termEntryValue sort descriptors ret value))
    (answer : Atom)
    (foundReturns : PureReturns program
      (termSelectedEnvironment (resolverValue published sorts terms theorems nextSort nextTerm nextTheorem images)
        tableSorts tableTheorems fuel slots dummies arity binary identifier save codes entries sort descriptors ret value)
      state termFound state answer) :
    PureReturns program
      (termEnvironment (resolverValue published sorts terms theorems nextSort nextTerm nextTheorem images)
        tableSorts (listValue entries) tableTheorems fuel slots dummies arity binary save codes)
      state termEquation.body state answer := by
  let resolver := resolverValue published sorts terms theorems nextSort nextTerm nextTheorem images
  let bindings := termEnvironment resolver tableSorts (listValue entries) tableTheorems fuel slots dummies arity binary save codes
  let found := ("found", optionValue (some (natural identifier))) :: bindings
  let read := termReadEnvironment resolver tableSorts tableTheorems fuel slots dummies arity binary identifier save codes entries sort descriptors ret value
  let selected := termSelectedEnvironment resolver tableSorts tableTheorems fuel slots dummies arity binary identifier save codes entries sort descriptors ret value
  rw [term_shape]
  apply let_star_returns program bindings state state _ _ _ _ rfl
  apply let_returns program bindings found state state state (.var "found") _ _
    (optionValue (some (natural identifier))) _
  · simpa [ResolverField.head, ResolverField.entries, declared] using resolver_returns .term bindings state published sorts terms theorems nextSort nextTerm nextTheorem
      images (natural binary) "state" "binary" rfl rfl
  · simp [SpaceSemantics.matchValue, matchAtom, Subst.lookup, found, bindings, termEnvironment]
  · apply let_returns program found read state state state (.var "entry") _ _
      (optionValue (some (termEntryValue sort descriptors ret value))) _
    · simpa [entryFound] using MMBProofRunExecution.checker_returns (by decide +kernel)
        (ListAccess.data_at_list_returns found state entries binary "terms" "binary" rfl rfl)
    · simp [SpaceSemantics.matchValue, matchAtom, Subst.lookup, read, found, bindings, termReadEnvironment, termEnvironment]
    · apply case_returns program read selected state state state (.expression [.var "found", .var "entry"])
        (.expression [optionValue (some (natural identifier)), optionValue (some (termEntryValue sort descriptors ret value))]) termFound _ _
        termCases (read_cases_encoded termCases)
      · exact tuple_variables_return program read state ["found", "entry"]
      · simp [term_cases, SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
          matchAtom, Subst.lookup, selected, read, termSelectedEnvironment, termReadEnvironment, termEnvironment,
          optionValue, termEntryValue, listValue]
      · exact foundReturns

private theorem term_body_from_children_returns (state : State) (published : Atom)
    (sorts terms theorems : List MMUResolution.Binding) (nextSort nextTerm nextTheorem : Nat) (images : Atom)
    (tableSorts tableTheorems : Atom) (fuel : Nat) (slots dummies : List Atom) (arity binary identifier : Nat)
    (save : Bool) (codes : List Atom) (entries : List Atom) (sort : Atom) (descriptors : List Atom) (ret value : Atom)
    (declared : MMUResolution.lookup terms (natural binary) = some (natural identifier))
    (entryFound : entries[binary]? = some (termEntryValue sort descriptors ret value))
    (arguments : List Kernel.Preterm) (afterSlots extra : List Atom) (count : Nat) (rest : List Atom)
    (childReturns : PureReturns program
      (termPreparedEnvironment (resolverValue published sorts terms theorems nextSort nextTerm nextTheorem images)
        tableSorts tableTheorems fuel slots dummies arity binary identifier save codes entries sort descriptors ret value)
      state (.expression [.symbol "mm0:mmb:unify-expressions", .var "state",
        .expression [.symbol "MM0:MMBTables", .var "sorts", .var "terms", .var "theorems"],
        .expression [.symbol "-", .var "fuel", natural 1], .expression [.symbol "size-atom", .var "args"],
        .expression [.symbol "MM0:MMBUState", .var "nextSlots", .var "dummies", .var "arity"], .var "codes"])
      state (optionValue (some (unifyExpressionsValue (arguments.map Data.preterm)
        (unifyStateValue afterSlots extra count) (listValue rest))))) :
    PureReturns program
      (termEnvironment (resolverValue published sorts terms theorems nextSort nextTerm nextTheorem images)
        tableSorts (listValue entries) tableTheorems fuel slots dummies arity binary save codes)
      state termEquation.body state (completedTermResult identifier arguments afterSlots extra count slots.length save rest) := by
  apply term_body_from_found_returns state published sorts terms theorems nextSort nextTerm nextTheorem images
    tableSorts tableTheorems fuel slots dummies arity binary identifier save codes entries sort descriptors ret value declared entryFound
  exact term_found_returns state _ tableSorts tableTheorems fuel slots dummies arity binary identifier save codes entries
    sort descriptors ret value arguments afterSlots extra count rest childReturns
/-- Filling a saved term's own reservation preserves all earlier physical slots. -/
theorem completedTermResult_reserved (identifier : Nat) (arguments : List Kernel.Preterm)
    (slots dummies : List Atom) (arity : Nat) (rest : List Atom) :
    completedTermResult identifier arguments (slots ++ [.symbol "None"]) dummies arity slots.length true rest =
      optionValue (some (unifyExpressionValue
        (Data.preterm (Kernel.Preterm.applyArgs (.term identifier) arguments))
        (slots ++ [optionValue (some (Data.preterm (Kernel.Preterm.applyArgs (.term identifier) arguments)))])
        dummies arity rest)) := by
  simp [completedTermResult]

private theorem term_nullary_body_returns (state : State) (published : Atom)
    (sorts terms theorems : List MMUResolution.Binding) (nextSort nextTerm nextTheorem : Nat) (images : Atom)
    (tableSorts tableTheorems : Atom) (fuel : Nat) (slots dummies : List Atom) (arity binary identifier : Nat)
    (save : Bool) (codes entries : List Atom) (sort ret value : Atom)
    (declared : MMUResolution.lookup terms (natural binary) = some (natural identifier))
    (entryFound : entries[binary]? = some (termEntryValue sort [] ret value)) :
    PureReturns program
      (termEnvironment (resolverValue published sorts terms theorems nextSort nextTerm nextTheorem images)
        tableSorts (listValue entries) tableTheorems (fuel + 1) slots dummies arity binary save codes)
      state termEquation.body state (completedTermResult identifier []
        (if save then slots ++ [.symbol "None"] else slots) dummies arity slots.length save codes) := by
  let resolver := resolverValue published sorts terms theorems nextSort nextTerm nextTheorem images
  let tables := tablesValue tableSorts (listValue entries) tableTheorems
  let next := if save then slots ++ [.symbol "None"] else slots
  let prepared := termPreparedEnvironment resolver tableSorts tableTheorems (fuel + 1)
    slots dummies arity binary identifier save codes entries sort [] ret value
  apply term_body_from_children_returns state published sorts terms theorems nextSort nextTerm nextTheorem images
    tableSorts tableTheorems (fuel + 1) slots dummies arity binary identifier save codes entries sort [] ret value
    declared entryFound [] next dummies arity codes
  apply expressions_call_from_body prepared state resolver tables fuel 0 (unifyStateValue next dummies arity) (listValue codes) _
    (.var "state") (.expression [.symbol "MM0:MMBTables", .var "sorts", .var "terms", .var "theorems"])
    (.expression [.symbol "-", .var "fuel", natural 1]) (.expression [.symbol "size-atom", .var "args"])
    (.expression [.symbol "MM0:MMBUState", .var "nextSlots", .var "dummies", .var "arity"]) (.var "codes")
  · rfl
  · rfl
  · exact decrement_returns prepared state fuel "fuel" rfl
  · apply native_variable_call_returns program prepared state state "size-atom" ["args"] (natural 0)
      (by decide) (by decide) _ (by decide)
    rfl
  · rfl
  · rfl
  · exact expressions_empty_body_returns state resolver tables fuel _ _

/-- A declared nullary term runs through the original lookup, slot reservation,
child decoder and slot fill. Table indices and logical term identifiers may differ. -/
theorem unify_term_nullary_returns (bindings : Subst) (state : State) (published : Atom)
    (sorts terms theorems : List MMUResolution.Binding) (nextSort nextTerm nextTheorem : Nat) (images : Atom)
    (tableSorts tableTheorems : Atom) (fuel : Nat) (slots dummies : List Atom) (arity binary identifier : Nat)
    (save : Bool) (codes entries : List Atom) (sort ret value : Atom)
    (declared : MMUResolution.lookup terms (natural binary) = some (natural identifier))
    (entryFound : entries[binary]? = some (termEntryValue sort [] ret value))
    (resolverName tablesName fuelName unifyName binaryName saveName codesName : String)
    (resolverCaptured : applySubst bindings (.var resolverName) = resolverValue published sorts terms theorems nextSort nextTerm nextTheorem images)
    (tablesCaptured : applySubst bindings (.var tablesName) = tablesValue tableSorts (listValue entries) tableTheorems)
    (fuelCaptured : applySubst bindings (.var fuelName) = natural (fuel + 1))
    (unifyCaptured : applySubst bindings (.var unifyName) = unifyStateValue slots dummies arity)
    (binaryCaptured : applySubst bindings (.var binaryName) = natural binary)
    (saveCaptured : applySubst bindings (.var saveName) = boolean save)
    (codesCaptured : applySubst bindings (.var codesName) = listValue codes) :
    PureReturns program bindings state (.expression [.symbol "mm0:mmb:unify-term", .var resolverName, .var tablesName,
      .var fuelName, .var unifyName, .var binaryName, .var saveName, .var codesName]) state
      (optionValue (some (unifyExpressionValue (Data.preterm (.term identifier))
        (if save then slots ++ [optionValue (some (Data.preterm (.term identifier)))] else slots) dummies arity codes))) := by
  have returned := term_nullary_body_returns state published sorts terms theorems nextSort nextTerm nextTheorem images
    tableSorts tableTheorems fuel slots dummies arity binary identifier save codes entries sort ret value declared entryFound
  apply term_from_body bindings state _ tableSorts (listValue entries) tableTheorems (fuel + 1) slots dummies arity binary save codes _
    resolverName tablesName fuelName unifyName binaryName saveName codesName resolverCaptured tablesCaptured fuelCaptured
    unifyCaptured binaryCaptured saveCaptured codesCaptured
  cases save with
  | false => simpa [completedTermResult] using returned
  | true => simpa [completedTermResult_reserved] using returned

private theorem expressions_first_refused_body_returns (state : State) (resolver tables : Atom) (fuel count : Nat)
    (unify codes : Atom)
    (firstReturns : PureReturns program (expressionsEnvironment resolver tables (fuel + 1) (count + 1) unify codes)
      state (.expression [.symbol "mm0:mmb:unify-expression", .var "state", .var "tables",
        .expression [.symbol "-", .var "fuel", natural 1], .var "unify", .var "codes"]) state (.symbol "None")) :
    PureReturns program (expressionsEnvironment resolver tables (fuel + 1) (count + 1) unify codes)
      state expressionsEquation.body state (.symbol "None") := by
  let bindings := expressionsEnvironment resolver tables (fuel + 1) (count + 1) unify codes
  rw [expressions_shape]
  apply if_returns program bindings state state state _ (boolean false) _ _ _
  · apply native_binary_call_returns program bindings state state state state "==" (.var "count") (natural 0)
      (natural (count + 1)) (natural 0) (boolean false)
      (by decide) (by decide) (by decide +kernel) (by decide +kernel) _ _ _ (by decide)
    · exact variable_returns program bindings state "count"
    · exact grounded_returns program bindings state (.int 0)
    · simp [StdLib.structural_equality, natural, boolean]; omega
  · simp only [boolean]
    rw [expressions_more_shape]
    apply if_returns program bindings state state state _ (boolean true) _ _ _
    · apply native_binary_call_returns program bindings state state state state "<" (natural 0) (.var "fuel")
        (natural 0) (natural (fuel + 1)) (boolean true)
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) _ _ _ (by decide)
      · exact grounded_returns program bindings state (.int 0)
      · exact variable_returns program bindings state "fuel"
      · simp [StdLib.less_comparison, natural, boolean]
    · apply case_returns program bindings (("bad", .symbol "None") :: bindings) state state state _
        (.symbol "None") (.symbol "None") _ _ expressionsFirstCases (read_cases_encoded expressionsFirstCases)
      · exact firstReturns
      · simp [expressions_first_cases, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom,
          Subst.lookup, bindings, expressionsEnvironment]
      · exact symbol_returns program _ state "None"

private theorem term_self_reference_body_refused_returns (state : State) (published : Atom)
    (sorts terms theorems : List MMUResolution.Binding) (nextSort nextTerm nextTheorem : Nat) (images : Atom)
    (tableSorts tableTheorems : Atom) (fuel : Nat) (slots dummies : List Atom) (arity binary identifier start after : Nat)
    (rest entries : List Atom) (sort descriptor ret value : Atom) (descriptors : List Atom)
    (declared : MMUResolution.lookup terms (natural binary) = some (natural identifier))
    (entryFound : entries[binary]? = some (termEntryValue sort (descriptor :: descriptors) ret value)) :
    PureReturns program
      (termEnvironment (resolverValue published sorts terms theorems nextSort nextTerm nextTheorem images)
        tableSorts (listValue entries) tableTheorems (fuel + 3) slots dummies arity binary true
        (MMBExecution.commandValue 50 slots.length start after :: rest))
      state termEquation.body state (.symbol "None") := by
  let resolver := resolverValue published sorts terms theorems nextSort nextTerm nextTheorem images
  let tables := tablesValue tableSorts (listValue entries) tableTheorems
  let reservedSlots := slots ++ [.symbol "None"]
  let codes := MMBExecution.commandValue 50 slots.length start after :: rest
  let prepared := termPreparedEnvironment resolver tableSorts tableTheorems (fuel + 3) slots dummies arity binary identifier true
    codes entries sort (descriptor :: descriptors) ret value
  let children := expressionsEnvironment resolver tables (fuel + 2) (descriptors.length + 1)
    (unifyStateValue reservedSlots dummies arity) (listValue codes)
  have referenceFailed : PureReturns program children state
      (.expression [.symbol "mm0:mmb:unify-expression", .var "state", .var "tables",
        .expression [.symbol "-", .var "fuel", natural 1], .var "unify", .var "codes"])
      state (.symbol "None") := by
    apply expression_call_from_body children state resolver tableSorts (listValue entries) tableTheorems (fuel + 1)
      reservedSlots dummies arity codes (.symbol "None") (.var "state") (.var "tables")
      (.expression [.symbol "-", .var "fuel", natural 1]) (.var "unify") (.var "codes")
    · rfl
    · rfl
    · exact decrement_returns children state (fuel + 1) "fuel" rfl
    · rfl
    · rfl
    · exact expression_reference_from_body state resolver tableSorts (listValue entries) tableTheorems fuel slots.length start after
        reservedSlots dummies arity rest (.symbol "None")
        (reference_unavailable_body_returns state resolver tableSorts (listValue entries) tableTheorems fuel slots.length start after
          reservedSlots dummies arity rest (Or.inr (by simp [reservedSlots])))
  have childrenFailed : PureReturns program prepared state
      (.expression [.symbol "mm0:mmb:unify-expressions", .var "state",
        .expression [.symbol "MM0:MMBTables", .var "sorts", .var "terms", .var "theorems"],
        .expression [.symbol "-", .var "fuel", natural 1], .expression [.symbol "size-atom", .var "args"],
        .expression [.symbol "MM0:MMBUState", .var "nextSlots", .var "dummies", .var "arity"], .var "codes"])
      state (.symbol "None") := by
    apply expressions_call_from_body prepared state resolver tables (fuel + 2) (descriptors.length + 1)
      (unifyStateValue reservedSlots dummies arity) (listValue codes) (.symbol "None")
      (.var "state") (.expression [.symbol "MM0:MMBTables", .var "sorts", .var "terms", .var "theorems"])
      (.expression [.symbol "-", .var "fuel", natural 1]) (.expression [.symbol "size-atom", .var "args"])
      (.expression [.symbol "MM0:MMBUState", .var "nextSlots", .var "dummies", .var "arity"]) (.var "codes")
    · rfl
    · rfl
    · exact decrement_returns prepared state (fuel + 2) "fuel" rfl
    · apply native_variable_call_returns program prepared state state "size-atom" ["args"] (natural (descriptors.length + 1))
        (by decide) (by decide) _ (by decide)
      rfl
    · rfl
    · rfl
    · exact expressions_first_refused_body_returns state resolver tables (fuel + 1) descriptors.length _ _ referenceFailed
  apply term_body_from_found_returns state published sorts terms theorems nextSort nextTerm nextTheorem images
    tableSorts tableTheorems (fuel + 3) slots dummies arity binary identifier true codes entries sort
    (descriptor :: descriptors) ret value declared entryFound
  apply term_prepare_returns state resolver tableSorts tableTheorems (fuel + 3) slots dummies arity binary identifier true codes entries sort
    (descriptor :: descriptors) ret value
  rw [term_read_children_shape]
  apply case_returns program prepared (("bad", .symbol "None") :: prepared) state state state _ (.symbol "None") (.symbol "None") _ _
    termChildCases (read_cases_encoded termChildCases)
  · exact childrenFailed
  · simp [term_child_cases, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom,
      Subst.lookup, prepared, termPreparedEnvironment, termSelectedEnvironment, termReadEnvironment, termEnvironment]
  · exact symbol_returns program _ state "None"

/-- Saving reserves the parent's physical slot before decoding any child.
A child referencing that reservation is refused, even when all declaration
lookups succeed and more source fuel is available. -/
theorem unify_saved_term_self_reference_refused_returns (bindings : Subst) (state : State) (published : Atom)
    (sorts terms theorems : List MMUResolution.Binding) (nextSort nextTerm nextTheorem : Nat) (images : Atom)
    (tableSorts tableTheorems : Atom) (fuel : Nat) (slots dummies : List Atom) (arity binary identifier start after : Nat)
    (rest entries : List Atom) (sort descriptor ret value : Atom) (descriptors : List Atom)
    (declared : MMUResolution.lookup terms (natural binary) = some (natural identifier))
    (entryFound : entries[binary]? = some (termEntryValue sort (descriptor :: descriptors) ret value))
    (resolverName tablesName fuelName unifyName binaryName saveName codesName : String)
    (resolverCaptured : applySubst bindings (.var resolverName) = resolverValue published sorts terms theorems nextSort nextTerm nextTheorem images)
    (tablesCaptured : applySubst bindings (.var tablesName) = tablesValue tableSorts (listValue entries) tableTheorems)
    (fuelCaptured : applySubst bindings (.var fuelName) = natural (fuel + 3))
    (unifyCaptured : applySubst bindings (.var unifyName) = unifyStateValue slots dummies arity)
    (binaryCaptured : applySubst bindings (.var binaryName) = natural binary)
    (saveCaptured : applySubst bindings (.var saveName) = boolean true)
    (codesCaptured : applySubst bindings (.var codesName) = listValue (MMBExecution.commandValue 50 slots.length start after :: rest)) :
    PureReturns program bindings state (.expression [.symbol "mm0:mmb:unify-term", .var resolverName, .var tablesName,
      .var fuelName, .var unifyName, .var binaryName, .var saveName, .var codesName]) state (.symbol "None") := by
  apply term_from_body bindings state _ tableSorts (listValue entries) tableTheorems (fuel + 3) slots dummies arity binary true
    (MMBExecution.commandValue 50 slots.length start after :: rest) _ resolverName tablesName fuelName unifyName binaryName saveName codesName
    resolverCaptured tablesCaptured fuelCaptured unifyCaptured binaryCaptured saveCaptured codesCaptured
  exact term_self_reference_body_refused_returns state published sorts terms theorems nextSort nextTerm nextTheorem images
    tableSorts tableTheorems fuel slots dummies arity binary identifier start after rest entries sort descriptor ret value descriptors declared entryFound

/-- Ordered reference commands retain both physical byte metadata fields. -/
def termReferenceCodes (references : List ((Nat × Nat × Nat) × Kernel.Preterm)) : List Atom :=
  references.map fun reference => MMBExecution.commandValue 50 reference.1.1 reference.1.2.1 reference.1.2.2

private theorem term_references_body_returns (state : State) (published : Atom)
    (sorts terms theorems : List MMUResolution.Binding) (nextSort nextTerm nextTheorem : Nat) (images : Atom)
    (tableSorts tableTheorems : Atom) (budget : Nat) (slots dummies : List Atom) (arity binary identifier : Nat)
    (save : Bool) (rest entries : List Atom) (sort ret value : Atom) (descriptors : List Atom)
    (references : List ((Nat × Nat × Nat) × Kernel.Preterm))
    (declared : MMUResolution.lookup terms (natural binary) = some (natural identifier))
    (entryFound : entries[binary]? = some (termEntryValue sort descriptors ret value))
    (countMatches : descriptors.length = references.length)
    (filled : ∀ reference ∈ references,
      (if save then slots ++ [.symbol "None"] else slots)[reference.1.1]? =
        some (optionValue (some (Data.preterm reference.2)))) :
    PureReturns program
      (termEnvironment (resolverValue published sorts terms theorems nextSort nextTerm nextTheorem images)
        tableSorts (listValue entries) tableTheorems (references.length + budget + 2) slots dummies arity binary save
        (termReferenceCodes references ++ rest)) state termEquation.body state
      (completedTermResult identifier (references.map Prod.snd)
        (if save then slots ++ [.symbol "None"] else slots) dummies arity slots.length save rest) := by
  let resolver := resolverValue published sorts terms theorems nextSort nextTerm nextTheorem images
  let tables := tablesValue tableSorts (listValue entries) tableTheorems
  let next := if save then slots ++ [.symbol "None"] else slots
  let rawReferences := references.map fun reference => (reference.1, Data.preterm reference.2)
  let prepared := termPreparedEnvironment resolver tableSorts tableTheorems (references.length + budget + 2)
    slots dummies arity binary identifier save (termReferenceCodes references ++ rest) entries sort descriptors ret value
  have filledRaw : ∀ reference ∈ rawReferences, next[reference.1.1]? = some (optionValue (some reference.2)) := by
    intro reference inside
    obtain ⟨original, member, rfl⟩ := List.mem_map.mp inside
    exact filled original member
  have childBody := expressions_references_body_returns state resolver tableSorts (listValue entries) tableTheorems
    next dummies arity rest budget rawReferences filledRaw
  apply term_body_from_children_returns state published sorts terms theorems nextSort nextTerm nextTheorem images
    tableSorts tableTheorems (references.length + budget + 2) slots dummies arity binary identifier save
    (termReferenceCodes references ++ rest) entries sort descriptors ret value declared entryFound
    (references.map Prod.snd) next dummies arity rest
  apply expressions_call_from_body prepared state resolver tables (references.length + budget + 1) references.length
    (unifyStateValue next dummies arity) (listValue (termReferenceCodes references ++ rest)) _
    (.var "state") (.expression [.symbol "MM0:MMBTables", .var "sorts", .var "terms", .var "theorems"])
    (.expression [.symbol "-", .var "fuel", natural 1]) (.expression [.symbol "size-atom", .var "args"])
    (.expression [.symbol "MM0:MMBUState", .var "nextSlots", .var "dummies", .var "arity"]) (.var "codes")
  · rfl
  · rfl
  · exact decrement_returns prepared state (references.length + budget + 1) "fuel" rfl
  · apply native_variable_call_returns program prepared state state "size-atom" ["args"] (natural references.length)
      (by decide) (by decide) _ (by decide)
    change (.ok (state, [natural descriptors.length]) : Effects.Result) = .ok (state, [natural references.length])
    rw [countMatches]
  · rfl
  · rfl
  · simpa [rawReferences, List.map_map, referenceCodes, termReferenceCodes, Function.comp_def] using childBody

/-- A whole original term decoder preserves an arbitrary ordered family of
filled-reference children, including repeated physical references. Saving
uses the same slot reserved before the child sequence. -/
theorem unify_term_references_returns (bindings : Subst) (state : State) (published : Atom)
    (sorts terms theorems : List MMUResolution.Binding) (nextSort nextTerm nextTheorem : Nat) (images : Atom)
    (tableSorts tableTheorems : Atom) (budget : Nat) (slots dummies : List Atom) (arity binary identifier : Nat)
    (save : Bool) (rest entries : List Atom) (sort ret value : Atom) (descriptors : List Atom)
    (references : List ((Nat × Nat × Nat) × Kernel.Preterm))
    (declared : MMUResolution.lookup terms (natural binary) = some (natural identifier))
    (entryFound : entries[binary]? = some (termEntryValue sort descriptors ret value))
    (countMatches : descriptors.length = references.length)
    (filled : ∀ reference ∈ references,
      (if save then slots ++ [.symbol "None"] else slots)[reference.1.1]? =
        some (optionValue (some (Data.preterm reference.2))))
    (resolverName tablesName fuelName unifyName binaryName saveName codesName : String)
    (resolverCaptured : applySubst bindings (.var resolverName) = resolverValue published sorts terms theorems nextSort nextTerm nextTheorem images)
    (tablesCaptured : applySubst bindings (.var tablesName) = tablesValue tableSorts (listValue entries) tableTheorems)
    (fuelCaptured : applySubst bindings (.var fuelName) = natural (references.length + budget + 2))
    (unifyCaptured : applySubst bindings (.var unifyName) = unifyStateValue slots dummies arity)
    (binaryCaptured : applySubst bindings (.var binaryName) = natural binary)
    (saveCaptured : applySubst bindings (.var saveName) = boolean save)
    (codesCaptured : applySubst bindings (.var codesName) = listValue (termReferenceCodes references ++ rest)) :
    PureReturns program bindings state (.expression [.symbol "mm0:mmb:unify-term", .var resolverName, .var tablesName,
      .var fuelName, .var unifyName, .var binaryName, .var saveName, .var codesName]) state
      (optionValue (some (unifyExpressionValue
        (Data.preterm (Kernel.Preterm.applyArgs (.term identifier) (references.map Prod.snd)))
        (if save then slots ++ [optionValue (some (Data.preterm
          (Kernel.Preterm.applyArgs (.term identifier) (references.map Prod.snd))))] else slots) dummies arity rest))) := by
  have returned := term_references_body_returns state published sorts terms theorems nextSort nextTerm nextTheorem images
    tableSorts tableTheorems budget slots dummies arity binary identifier save rest entries sort ret value descriptors references
    declared entryFound countMatches filled
  apply term_from_body bindings state _ tableSorts (listValue entries) tableTheorems (references.length + budget + 2)
    slots dummies arity binary save (termReferenceCodes references ++ rest) _ resolverName tablesName fuelName unifyName binaryName saveName codesName
    resolverCaptured tablesCaptured fuelCaptured unifyCaptured binaryCaptured saveCaptured codesCaptured
  cases save with
  | false => simpa [completedTermResult] using returned
  | true => simpa [completedTermResult_reserved] using returned


private def hypothesesEarlierCases := casesOf hypothesesExpressionFound
private def hypothesesEarlierFound := (hypothesesEarlierCases[0]'(by decide)).2
private theorem hypotheses_found_shape : hypothesesExpressionFound =
    .expression [.symbol "case", .expression [.symbol "mm0:mmb:unify-hypotheses", .var "state", .var "tables",
      .expression [.symbol "-", .var "fuel", natural 1],
      .expression [.symbol "MM0:MMBUState", .var "slots", .expression [.symbol "MM0:L", .expression []], .var "arity"],
      .var "remaining"], .expression (hypothesesEarlierCases.map fun row => .expression [row.1, row.2])] := by decide
private theorem hypotheses_earlier_cases : hypothesesEarlierCases =
    [(.expression [.symbol "Some", .var "earlier"], hypothesesEarlierFound), (.var "bad", .symbol "None")] := by decide
private theorem hypotheses_earlier_found_shape : hypothesesEarlierFound =
    .expression [.symbol "let", .var "hypotheses", .expression [.symbol "mm0:mmb:snoc", .var "earlier", .var "first"],
      .expression [.symbol "Some", .var "hypotheses"]] := by decide

private theorem hypotheses_cons_body_returns (state : State) (resolver tables : Atom) (fuel data start after : Nat)
    (unify : Atom) (codes : List Atom) (first : Atom) (slots : List Atom) (arity : Nat) (remaining earlier : List Atom)
    (childReturns : PureReturns program (hypothesesCommandEnvironment resolver tables fuel data start after unify codes)
      state (.expression [.symbol "mm0:mmb:unify-expression", .var "state", .var "tables",
        .expression [.symbol "-", .var "fuel", natural 1], .var "unify", .expression [.symbol "MM0:L", .var "rest"]])
      state (optionValue (some (unifyExpressionValue first slots [] arity remaining))))
    (tailReturns : PureReturns program
      (("remaining", listValue remaining) :: ("arity", natural arity) :: ("slots", listValue slots) :: ("first", first) ::
        hypothesesCommandEnvironment resolver tables fuel data start after unify codes)
      state (.expression [.symbol "mm0:mmb:unify-hypotheses", .var "state", .var "tables",
        .expression [.symbol "-", .var "fuel", natural 1],
        .expression [.symbol "MM0:MMBUState", .var "slots", .expression [.symbol "MM0:L", .expression []], .var "arity"],
        .var "remaining"]) state (optionValue (some (listValue earlier)))) :
    PureReturns program
      (hypothesesEnvironment resolver tables (fuel + 1) unify (MMBExecution.commandValue 54 data start after :: codes))
      state hypothesesEquation.body state (optionValue (some (listValue (earlier ++ [first])))) := by
  let bindings := hypothesesEnvironment resolver tables (fuel + 1) unify (MMBExecution.commandValue 54 data start after :: codes)
  let selected := hypothesesCommandEnvironment resolver tables fuel data start after unify codes
  let decoded := ("remaining", listValue remaining) :: ("arity", natural arity) :: ("slots", listValue slots) :: ("first", first) :: selected
  let tailed := ("earlier", listValue earlier) :: decoded
  let finished := ("hypotheses", listValue (earlier ++ [first])) :: tailed
  rw [hypotheses_shape]
  apply case_returns program bindings selected state state state (.var "codes")
    (.expression (MMBExecution.commandValue 54 data start after :: codes)) hypothesesCons _ _
    hypothesesCases (read_cases_encoded hypothesesCases)
  · exact variable_returns program bindings state "codes"
  · simp [hypotheses_cases_shape, MMBExecution.commandValue, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
      SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup, selected, bindings,
      hypothesesCommandEnvironment, hypothesesEnvironment, natural]
  · rw [hypotheses_cons_shape]
    apply if_returns program selected state state state _ (boolean true) _ _ _
    · apply native_binary_call_returns program selected state state state state "<" (natural 0) (.var "fuel")
        (natural 0) (natural (fuel + 1)) (boolean true)
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) _ _ _ (by decide)
      · exact grounded_returns program selected state (.int 0)
      · exact variable_returns program selected state "fuel"
      · simp [StdLib.less_comparison, natural, boolean]
    · apply case_returns program selected decoded state state state _
        (optionValue (some (unifyExpressionValue first slots [] arity remaining))) hypothesesExpressionFound _ _
        hypothesesExpressionCases (read_cases_encoded hypothesesExpressionCases)
      · exact childReturns
      · simp [hypotheses_expression_cases, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
          SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup, decoded, selected,
          hypothesesCommandEnvironment, hypothesesEnvironment, optionValue, unifyExpressionValue, unifyStateValue, listValue]
      · rw [hypotheses_found_shape]
        apply case_returns program decoded tailed state state state _ (optionValue (some (listValue earlier))) hypothesesEarlierFound _ _
          hypothesesEarlierCases (read_cases_encoded hypothesesEarlierCases)
        · exact tailReturns
        · simp [hypotheses_earlier_cases, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
            SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup,
            tailed, decoded, selected, hypothesesCommandEnvironment, hypothesesEnvironment, optionValue]
        · rw [hypotheses_earlier_found_shape]
          apply let_returns program tailed finished state state state (.var "hypotheses") _ _ (listValue (earlier ++ [first])) _
          · apply snoc_captured_returns tailed state earlier first (.var "earlier") (.var "first")
            · rfl
            · simp [tailed, decoded, applySubst, Subst.lookup]
          · simp [SpaceSemantics.matchValue, matchAtom, Subst.lookup, finished, tailed, decoded, selected,
              hypothesesCommandEnvironment, hypothesesEnvironment]
          · exact unary_constructor_returns program finished state "Some" "hypotheses" (by decide +kernel) (by decide)

private theorem hypotheses_call_from_body (bindings : Subst) (state : State) (resolver tables : Atom)
    (fuel : Nat) (unify : Atom) (codes : List Atom) (answer : Atom)
    (resolverArgument tablesArgument fuelArgument unifyArgument codesArgument : Atom)
    (resolverCaptured : applySubst bindings resolverArgument = resolver)
    (tablesCaptured : applySubst bindings tablesArgument = tables)
    (fuelReturned : PureReturns program bindings state fuelArgument state (natural fuel))
    (unifyCaptured : applySubst bindings unifyArgument = unify)
    (codesCaptured : applySubst bindings codesArgument = listValue codes)
    (body : PureReturns program (hypothesesEnvironment resolver tables fuel unify codes)
      state hypothesesEquation.body state answer) :
    PureReturns program bindings state (.expression [.symbol "mm0:mmb:unify-hypotheses", resolverArgument,
      tablesArgument, fuelArgument, unifyArgument, codesArgument]) state answer := by
  apply call_returns program bindings state state "mm0:mmb:unify-hypotheses" _ _ (by decide +kernel) _ (by decide)
  apply raw_argument_answers program bindings state state "mm0:mmb:unify-hypotheses" resolverArgument _ [] 0 [_] (by decide +kernel)
  apply raw_argument_answers program bindings state state "mm0:mmb:unify-hypotheses" tablesArgument _ _ 1 [_] (by decide +kernel)
  apply evaluated_argument_returns program bindings state state state (.function "mm0:mmb:unify-hypotheses")
    fuelArgument (natural fuel) _ _ _ 2 (by decide +kernel) fuelReturned
  apply raw_arguments_return program bindings state state "mm0:mmb:unify-hypotheses" [unifyArgument,codesArgument] _ 3 _
  · intro offset inside
    have bounded : offset < 2 := by simpa using inside
    interval_cases offset <;> decide +kernel
  · simp only [List.map_cons,List.map_nil,resolverCaptured,tablesCaptured,unifyCaptured,codesCaptured]
    exact authored_function_arguments_return program bindings (hypothesesEnvironment resolver tables fuel unify codes)
      state state "mm0:mmb:unify-hypotheses" [resolver,tables,natural fuel,unify,listValue codes] 5 hypothesesEquation.body _
      (by decide +kernel) (by decide) (hypotheses_clause resolver tables fuel unify codes) body

/-- Each hypothesis instruction is followed by its original reference command.
Both instructions retain every physical metadata field. -/
def hypothesisReferenceCodes (references : List ((Nat × Nat × Nat) × ((Nat × Nat × Nat) × Atom))) : List Atom :=
  references.flatMap fun reference =>
    [MMBExecution.commandValue 54 reference.1.1 reference.1.2.1 reference.1.2.2,
     MMBExecution.commandValue 50 reference.2.1.1 reference.2.1.2.1 reference.2.1.2.2]

private theorem hypotheses_references_body_returns (state : State) (resolver sorts terms theorems : Atom)
    (slots : List Atom) (arity budget : Nat)
    (references : List ((Nat × Nat × Nat) × ((Nat × Nat × Nat) × Atom)))
    (filled : ∀ reference ∈ references, slots[reference.2.1.1]? = some (optionValue (some reference.2.2))) :
    PureReturns program
      (hypothesesEnvironment resolver (tablesValue sorts terms theorems) (references.length + budget + 1)
        (unifyStateValue slots [] arity) (hypothesisReferenceCodes references))
      state hypothesesEquation.body state (optionValue (some (listValue (references.map (fun reference => reference.2.2)).reverse))) := by
  induction references with
  | nil =>
      simpa [hypothesisReferenceCodes] using hypotheses_empty_body_returns state resolver (tablesValue sorts terms theorems)
        (budget + 1) (unifyStateValue slots [] arity)
  | cons reference references ih =>
      let tables := tablesValue sorts terms theorems
      let codes := MMBExecution.commandValue 50 reference.2.1.1 reference.2.1.2.1 reference.2.1.2.2 :: hypothesisReferenceCodes references
      let selected := hypothesesCommandEnvironment resolver tables (references.length + budget + 1)
        reference.1.1 reference.1.2.1 reference.1.2.2 (unifyStateValue slots [] arity) codes
      let decoded := ("remaining", listValue (hypothesisReferenceCodes references)) :: ("arity", natural arity) ::
        ("slots", listValue slots) :: ("first", reference.2.2) :: selected
      have childReturns : PureReturns program selected state
          (.expression [.symbol "mm0:mmb:unify-expression", .var "state", .var "tables",
            .expression [.symbol "-", .var "fuel", natural 1], .var "unify", .expression [.symbol "MM0:L", .var "rest"]])
          state (optionValue (some (unifyExpressionValue reference.2.2 slots [] arity (hypothesisReferenceCodes references)))) := by
        apply expression_call_from_body selected state resolver sorts terms theorems (references.length + budget + 1)
          slots [] arity codes _ (.var "state") (.var "tables") (.expression [.symbol "-", .var "fuel", natural 1])
          (.var "unify") (.expression [.symbol "MM0:L", .var "rest"])
        · simp [selected,hypothesesCommandEnvironment,hypothesesEnvironment,applySubst,Subst.lookup]
        · simp [selected,hypothesesCommandEnvironment,hypothesesEnvironment,applySubst,Subst.lookup,tables]
        · apply decrement_returns selected state (references.length + budget + 1) "fuel"
          simp [selected,hypothesesCommandEnvironment,hypothesesEnvironment,applySubst,Subst.lookup]
        · simp [selected,hypothesesCommandEnvironment,hypothesesEnvironment,applySubst,Subst.lookup]
        · simp [selected,hypothesesCommandEnvironment,hypothesesEnvironment,applySubst,applySubst.applySubstList,Subst.lookup,listValue]
        · exact expression_reference_from_body state resolver sorts terms theorems (references.length + budget)
            reference.2.1.1 reference.2.1.2.1 reference.2.1.2.2 slots [] arity (hypothesisReferenceCodes references) _
            (reference_filled_body_returns state resolver sorts terms theorems reference.2.2 (references.length + budget)
              reference.2.1.1 reference.2.1.2.1 reference.2.1.2.2 slots [] arity (hypothesisReferenceCodes references)
              (filled reference (by simp)))
      have tailReturns : PureReturns program decoded state
          (.expression [.symbol "mm0:mmb:unify-hypotheses", .var "state", .var "tables",
            .expression [.symbol "-", .var "fuel", natural 1],
            .expression [.symbol "MM0:MMBUState", .var "slots", .expression [.symbol "MM0:L", .expression []], .var "arity"],
            .var "remaining"]) state (optionValue (some (listValue (references.map (fun entry => entry.2.2)).reverse))) := by
        apply hypotheses_call_from_body decoded state resolver tables (references.length + budget + 1)
          (unifyStateValue slots [] arity) (hypothesisReferenceCodes references) _ (.var "state") (.var "tables")
          (.expression [.symbol "-", .var "fuel", natural 1])
          (.expression [.symbol "MM0:MMBUState", .var "slots", .expression [.symbol "MM0:L", .expression []], .var "arity"])
          (.var "remaining")
        · simp [decoded,selected,hypothesesCommandEnvironment,hypothesesEnvironment,applySubst,Subst.lookup]
        · simp [decoded,selected,hypothesesCommandEnvironment,hypothesesEnvironment,applySubst,Subst.lookup]
        · apply decrement_returns decoded state (references.length + budget + 1) "fuel"
          simp [decoded,selected,hypothesesCommandEnvironment,hypothesesEnvironment,applySubst,Subst.lookup]
        · simp [decoded,applySubst,applySubst.applySubstList,Subst.lookup,unifyStateValue,listValue]
        · simp [decoded,applySubst,Subst.lookup]
        · exact ih (fun entry member => filled entry (by simp [member]))
      have done := hypotheses_cons_body_returns state resolver tables (references.length + budget + 1)
        reference.1.1 reference.1.2.1 reference.1.2.2 (unifyStateValue slots [] arity) codes reference.2.2 slots arity
        (hypothesisReferenceCodes references) (references.map (fun entry => entry.2.2)).reverse childReturns tailReturns
      have fuelEq : references.length + budget + 1 + 1 = (reference :: references).length + budget + 1 := by
        simp only [List.length_cons]
        omega
      rw [fuelEq] at done
      simpa [hypothesisReferenceCodes, codes, tables] using done

/-- Whole hypothesis recursion follows the original snoc order: the Polish
stream is consumed from its head and the completed hypotheses are reversed.
Every child is checked against the original filled slot, and every source
empty-dummy guard is discharged after that child. -/
theorem unify_hypotheses_references_returns (bindings : Subst) (state : State)
    (resolver sorts terms theorems : Atom) (slots : List Atom) (arity budget : Nat)
    (references : List ((Nat × Nat × Nat) × ((Nat × Nat × Nat) × Atom)))
    (filled : ∀ reference ∈ references, slots[reference.2.1.1]? = some (optionValue (some reference.2.2)))
    (resolverName tablesName fuelName unifyName codesName : String)
    (resolverCaptured : applySubst bindings (.var resolverName) = resolver)
    (tablesCaptured : applySubst bindings (.var tablesName) = tablesValue sorts terms theorems)
    (fuelCaptured : applySubst bindings (.var fuelName) = natural (references.length + budget + 1))
    (unifyCaptured : applySubst bindings (.var unifyName) = unifyStateValue slots [] arity)
    (codesCaptured : applySubst bindings (.var codesName) = listValue (hypothesisReferenceCodes references)) :
    PureReturns program bindings state (.expression [.symbol "mm0:mmb:unify-hypotheses", .var resolverName, .var tablesName,
      .var fuelName, .var unifyName, .var codesName]) state
      (optionValue (some (listValue (references.map (fun reference => reference.2.2)).reverse))) := by
  apply hypotheses_call_from_body bindings state resolver (tablesValue sorts terms theorems) (references.length + budget + 1)
    (unifyStateValue slots [] arity) (hypothesisReferenceCodes references) _
    (.var resolverName) (.var tablesName) (.var fuelName) (.var unifyName) (.var codesName)
    resolverCaptured tablesCaptured (by simpa [fuelCaptured] using variable_returns program bindings state fuelName)
    unifyCaptured codesCaptured
  exact hypotheses_references_body_returns state resolver sorts terms theorems slots arity budget references filled

open Formats.MMB

/-- Resolve a numerical binary position through the current working map and
retain only its original numerical namespace identifier. -/
def resolvedIds (entries : List MMUResolution.Binding) (binary : Nat) : Option Nat :=
  (MMUResolution.lookup entries (natural binary)).bind MMUResolution.decodeNatural

theorem resolvedIds_eq_some_iff (entries : List MMUResolution.Binding) (binary logical : Nat) :
    resolvedIds entries binary = some logical ↔
      MMUResolution.lookup entries (natural binary) = some (natural logical) := by
  constructor
  · intro found
    obtain ⟨value, read, decoded⟩ := Option.bind_eq_some_iff.mp found
    rw [MMUResolution.decodeNatural_reflects value logical decoded] at read
    exact read
  · intro found
    simp [resolvedIds, found]


/-- A missing numerical projection is exactly an absent current-map lookup
when the original map's admitted values are numerical. -/
theorem resolvedIds_eq_none_iff (entries : List MMUResolution.Binding) (binary : Nat)
    (numerical : MMUResolution.NumericalMap entries) :
    resolvedIds entries binary = none ↔ MMUResolution.lookup entries (natural binary) = none := by
  cases found : MMUResolution.lookup entries (natural binary) with
  | none => simp [resolvedIds,found]
  | some value =>
      obtain ⟨logical,rfl⟩ := MMUResolution.numerical_lookup entries (natural binary) value numerical found
      simp [resolvedIds,found]


theorem decoded_nullary (entries sorts : List MMUResolution.Binding)
    (arity : Nat → Option Nat) (arguments fuel binary logical : Nat)
    (state : Statements.Decoding) (tail : List Formats.MMB.UnifyCmd)
    (declared : MMUResolution.lookup entries (natural binary) = some (natural logical))
    (nullary : arity binary = some 0) :
    Statements.decodeExpr arity arguments (fuel + 1) state (.term binary :: tail)
      (resolvedIds entries) (resolvedIds sorts) = some (.term logical, state, tail) := by
  simp [Statements.decodeExpr, Statements.decodeExprs, resolvedIds, declared, nullary,
    Kernel.Preterm.applyArgs]

theorem decoded_dummy (entries sorts : List MMUResolution.Binding)
    (arity : Nat → Option Nat) (arguments fuel binary logical : Nat)
    (state : Statements.Decoding) (tail : List Formats.MMB.UnifyCmd)
    (declared : MMUResolution.lookup sorts (natural binary) = some (natural logical)) :
    Statements.decodeExpr arity arguments (fuel + 1) state (.dummy binary :: tail)
      (resolvedIds entries) (resolvedIds sorts) =
      some (.var (arguments + state.dummies.length),
        ⟨state.slots ++ [some (.var (arguments + state.dummies.length))], state.dummies ++ [logical]⟩,tail) := by
  simp [Statements.decodeExpr, resolvedIds, declared]

/-- Numerical positions are selected only from the preceding bound-variable prefix. -/
theorem positions_natural (ranks bound : List Nat)
    (within : ∀ rank ∈ ranks, rank < bound.length) :
    positions ranks (bound.map natural) =
      some ((ranks.map (fun rank => bound.getD rank rank)).map natural) := by
  induction ranks with
  | nil => rfl
  | cons rank rest ih =>
      have inside := within rank (by simp)
      have restInside : ∀ value ∈ rest, value < bound.length := by
        intro value member
        exact within value (by simp [member])
      simp [positions, List.getElem?_map, List.getElem?_eq_getElem inside,
        ih restInside]

/-- Original bound positions remain in strictly increasing authored order. -/
theorem boundPositions_pairwise (arguments : List ExprType) :
    (Statements.boundPositions arguments).Pairwise (· < ·) := by
  have retained : List.Sublist (Statements.boundPositions arguments) (List.range' 0 arguments.length) := by
    simpa [Statements.boundPositions, List.zipIdx_map_snd] using
      (List.filter_sublist (p := fun row : ExprType × Nat => row.1.bound)
        (l := arguments.zipIdx)).map Prod.snd
  exact (List.pairwise_lt_range' (s := 0) (n := arguments.length)).sublist retained

/-- Sorting the finite rank set and selecting the bound-variable prefix gives exactly
its canonical finite set of context positions. -/
theorem mapped_ranks_sort (dependencies : Finset Nat) (bound : List Nat)
    (ordered : bound.Pairwise (· < ·))
    (within : ∀ rank ∈ dependencies, rank < bound.length) :
    (dependencies.sort (· ≤ ·)).map (fun rank => bound.getD rank rank) =
      (dependencies.image (fun rank => bound.getD rank rank)).sort (· ≤ ·) := by
  let select := fun rank => bound.getD rank rank
  have monotone : ∀ left ∈ dependencies, ∀ right ∈ dependencies,
      left < right → select left < select right := by
    intro left leftMember right rightMember less
    have leftInside := within left leftMember
    have rightInside := within right rightMember
    simpa only [select, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem leftInside,
      List.getElem?_eq_getElem rightInside, Option.getD_some, List.get_eq_getElem] using
      ordered.rel_get_of_lt (a := ⟨left, leftInside⟩) (b := ⟨right, rightInside⟩) less
  have strict : ((dependencies.sort (· ≤ ·)).map select).Pairwise (· < ·) := by
    rw [List.pairwise_map]
    exact (Finset.sortedLT_sort dependencies).pairwise.imp_of_mem fun {left right} leftMember rightMember less =>
      monotone left ((Finset.mem_sort (· ≤ ·)).mp leftMember)
        right ((Finset.mem_sort (· ≤ ·)).mp rightMember) less
  have setEqual : ((dependencies.sort (· ≤ ·)).map select).toFinset = dependencies.image select := by
    ext value
    simp [List.mem_toFinset, Finset.mem_image]
  rw [← setEqual]
  exact ((List.toFinset_sort (· ≤ ·) strict.nodup).mpr (strict.imp Nat.le_of_lt)).symm

/-- Raw argument descriptors use the original finite dependency bitset's
canonical rank order. -/
def canonicalTypes (arguments : List ExprType) : List (Atom × Bool × List Nat) :=
  arguments.map fun argument => (natural argument.sort, argument.bound, argument.deps.sort (· ≤ ·))

/-- The metadata constraints tested by the source context walker. This does
not assert sort declaration admission or a successful context execution. -/
def PrefixValid (arguments : List ExprType) : Prop :=
  ∀ position : Fin arguments.length,
    if arguments[position].bound then
      arguments[position].deps = {(Statements.boundPositions (arguments.take position)).length}
    else ∀ rank ∈ arguments[position].deps, rank < (Statements.boundPositions (arguments.take position)).length


open MMUResolution (NumericalMap numerical_lookup)

theorem boundPositions_append_single (earlier : List ExprType) (argument : ExprType) :
    Statements.boundPositions (earlier ++ [argument]) =
      if argument.bound then Statements.boundPositions earlier ++ [earlier.length]
      else Statements.boundPositions earlier := by
  cases flag : argument.bound <;>
    simp [Statements.boundPositions, List.zipIdx_append, flag]

theorem boundPositions_append_prefix (earlier remaining : List ExprType) :
    ∃ suffix, Statements.boundPositions (earlier ++ remaining) =
      Statements.boundPositions earlier ++ suffix := by
  have retained := MMBDependencySoundness.boundPositions_take_prefix (earlier ++ remaining) earlier.length
  simpa using retained

theorem boundPositions_getD_prefix (earlier remaining : List ExprType) (rank : Nat)
    (within : rank < (Statements.boundPositions earlier).length) :
    (Statements.boundPositions (earlier ++ remaining)).getD rank rank =
      (Statements.boundPositions earlier).getD rank rank := by
  obtain ⟨suffix, retained⟩ := boundPositions_append_prefix earlier remaining
  simp only [retained, List.getD_eq_getElem?_getD, List.getElem?_append_left within]

theorem prefixValid_head (earlier remaining : List ExprType) (argument : ExprType)
    (valid : PrefixValid (earlier ++ argument :: remaining)) :
    if argument.bound then argument.deps = {(Statements.boundPositions earlier).length}
    else ∀ rank ∈ argument.deps, rank < (Statements.boundPositions earlier).length := by
  have found : (earlier ++ argument :: remaining)[earlier.length]? = some argument := by simp
  obtain ⟨within, same⟩ := List.getElem?_eq_some_iff.mp found
  have checked := valid ⟨earlier.length, within⟩
  simpa only [same, Fin.getElem_fin, List.take_append, List.take_length, Nat.sub_self,
    List.take_zero, List.append_nil] using checked

/-- Original earlier-rank checks earn a relocation of the original kernel
binder; finite-set ordering is proved rather than supplied as output data. -/
theorem regular_dependencies (earlier remaining : List ExprType) (argument : ExprType)
    (within : ∀ rank ∈ argument.deps, rank < (Statements.boundPositions earlier).length) :
    positions (argument.deps.sort (· ≤ ·)) ((Statements.boundPositions earlier).map natural) =
      some ((argument.deps.image (fun rank =>
        (Statements.boundPositions (earlier ++ remaining)).getD rank rank)).sort (· ≤ ·) |>.map natural) := by
  have rankBound : ∀ rank ∈ argument.deps.sort (· ≤ ·),
      rank < (Statements.boundPositions earlier).length := by
    simpa using within
  rw [positions_natural _ _ rankBound, mapped_ranks_sort _ _ (boundPositions_pairwise earlier) within]
  congr 3
  apply Finset.image_congr
  intro rank member
  exact (boundPositions_getD_prefix earlier remaining rank (within rank member)).symm



/-- The actual source walk of canonical descriptors agrees with relocation
of the original context projection, including absent numerical sort IDs. -/
theorem contextWalk_canonical (sorts : List MMUResolution.Binding)
    (numerical : NumericalMap sorts) (arguments earlier : List ExprType) (accumulated : List Atom)
    (valid : PrefixValid (earlier ++ arguments)) :
    contextWalk sorts (canonicalTypes arguments) earlier.length
      ((Statements.boundPositions earlier).map natural) accumulated =
    (Kernel.Context.relocateSorts? (resolvedIds sorts)
      (arguments.map (Statements.binder (Statements.boundPositions (earlier ++ arguments))))).map
      (fun context => (accumulated ++ context.map Data.binder,
        (Statements.boundPositions (earlier ++ arguments)).map natural)) := by
  induction arguments generalizing earlier accumulated with
  | nil => simp [canonicalTypes, contextWalk, Kernel.Context.relocateSorts?]
  | cons first rest ih =>
      have headValid := prefixValid_head earlier rest first valid
      cases lookup : MMUResolution.lookup sorts (natural first.sort) with
      | none =>
          cases flag : first.bound <;>
            simp [canonicalTypes, contextWalk, lookup, Kernel.Context.relocateSorts?, List.mapM_cons,
              Kernel.Binder.relocateSort?, Statements.binder, flag, resolvedIds]
      | some value =>
          obtain ⟨logical, same⟩ := numerical_lookup sorts (natural first.sort) value numerical lookup
          subst value
          let target : Kernel.Binder := if first.bound then .bound logical else
            .regular logical (first.deps.image fun rank =>
              (Statements.boundPositions (earlier ++ first :: rest)).getD rank rank)
          have relocated : Kernel.Binder.relocateSort? (resolvedIds sorts)
              (Statements.binder (Statements.boundPositions (earlier ++ first :: rest)) first) =
              some target := by
            cases flag : first.bound <;>
              simp [Kernel.Binder.relocateSort?, Statements.binder, target, flag, resolvedIds, lookup]
          have step : contextWalk sorts (canonicalTypes (first :: rest)) earlier.length
              ((Statements.boundPositions earlier).map natural) accumulated =
              contextWalk sorts (canonicalTypes rest) (earlier ++ [first]).length
                ((Statements.boundPositions (earlier ++ [first])).map natural)
                (accumulated ++ [Data.binder target]) := by
            cases flag : first.bound with
            | false =>
                have within : ∀ rank ∈ first.deps, rank < (Statements.boundPositions earlier).length := by
                  simpa only [flag, Bool.false_eq_true, if_false] using headValid
                have selected := regular_dependencies earlier (first :: rest) first within
                simp only [canonicalTypes, List.map_cons, contextWalk, lookup, flag,
                  Bool.false_eq_true, if_false]
                rw [selected]
                simp [target, Data.binder, Data.dependencies, flag, boundPositions_append_single]
            | true =>
                have singleton : first.deps = {(Statements.boundPositions earlier).length} := by
                  simpa only [flag, if_true] using headValid
                simp [canonicalTypes, contextWalk, lookup, flag, singleton,
                  target, Data.binder, boundPositions_append_single]
          have restValid : PrefixValid ((earlier ++ [first]) ++ rest) := by
            simpa only [List.append_assoc, List.singleton_append] using valid
          rw [step, ih _ _ restValid]
          simp only [List.append_assoc, List.singleton_append]
          simp only [Kernel.Context.relocateSorts?, List.map_cons, List.mapM_cons, relocated]
          cases completed : (rest.map
              (Statements.binder (Statements.boundPositions (earlier ++ first :: rest)))).mapM
              (Kernel.Binder.relocateSort? (resolvedIds sorts)) with
          | none => rfl
          | some added => simp



/-- Complete canonical context construction preserves the original global
context projection while relocating only its sort IDs through the current map. -/
theorem context_canonical (sorts : List MMUResolution.Binding) (arguments : List ExprType)
    (numerical : NumericalMap sorts) (valid : PrefixValid arguments) :
    contextWalk sorts (canonicalTypes arguments) 0 [] [] =
      (Kernel.Context.relocateSorts? (resolvedIds sorts) (Statements.context arguments)).map
        (fun context => (context.map Data.binder, (Statements.boundPositions arguments).map natural)) := by
  simpa [Statements.context, Statements.boundPositions] using contextWalk_canonical sorts numerical arguments [] [] (by simpa using valid)

theorem context_canonical_accepts_iff (sorts : List MMUResolution.Binding)
    (arguments : List ExprType) (context : Kernel.Context)
    (numerical : NumericalMap sorts) (valid : PrefixValid arguments) :
    contextWalk sorts (canonicalTypes arguments) 0 [] [] =
      some (context.map Data.binder, (Statements.boundPositions arguments).map natural) ↔
      Kernel.Context.relocateSorts? (resolvedIds sorts) (Statements.context arguments) = some context := by
  rw [context_canonical sorts arguments numerical valid]
  constructor
  · intro found
    obtain ⟨actual, read, same⟩ := Option.map_eq_some_iff.mp found
    have contextSame : actual.map Data.binder = context.map Data.binder := congrArg Prod.fst same
    have exactContext := (List.map_injective_iff.mpr Data.binder_injective) contextSame
    simpa [exactContext] using read
  · intro found
    simp [found]


instance prefixValidDecidable (arguments : List ExprType) : Decidable (PrefixValid arguments) := by
  unfold PrefixValid
  infer_instance

theorem context_canonical_refused_iff (sorts : List MMUResolution.Binding)
    (arguments : List ExprType) (numerical : NumericalMap sorts) (valid : PrefixValid arguments) :
    contextWalk sorts (canonicalTypes arguments) 0 [] [] = none ↔
      Kernel.Context.relocateSorts? (resolvedIds sorts) (Statements.context arguments) = none := by
  rw [context_canonical sorts arguments numerical valid]
  exact Option.map_eq_none_iff

/-- Captured execution of the unchanged source context operation returns the
relocated original context, with the same scope/name refusal boundary. -/
theorem context_canonical_returns (bindings : Mettapedia.Languages.ProcessCalculi.MORK.Subst)
    (state : Mettapedia.Languages.MeTTa.PeTTa.Effects.State) (published : Atom) (sorts terms theorems : List MMUResolution.Binding)
    (nextSort nextTerm nextTheorem : Nat) (images : Atom) (arguments : List ExprType)
    (stateName argumentsName : String) (numerical : NumericalMap sorts) (valid : PrefixValid arguments)
    (stateCaptured : Mettapedia.Languages.ProcessCalculi.MORK.applySubst bindings (.var stateName) =
      resolverValue published sorts terms theorems nextSort nextTerm nextTheorem images)
    (argumentsCaptured : Mettapedia.Languages.ProcessCalculi.MORK.applySubst bindings (.var argumentsName) =
      listValue (typeValues (canonicalTypes arguments))) :
    Mettapedia.Languages.MeTTa.PeTTa.Eval.PureReturns MMBTheoremSignatureExecution.program bindings state
      (.expression [.symbol "mm0:mmb:context", .var stateName, .var argumentsName]) state
      (ListAccess.optionValue
        ((Kernel.Context.relocateSorts? (resolvedIds sorts) (Statements.context arguments)).map
          (fun context => contextValue (context.map Data.binder) ((Statements.boundPositions arguments).map natural)))) := by
  have run := context_returns bindings state published sorts terms theorems nextSort nextTerm nextTheorem
    images (canonicalTypes arguments) stateName argumentsName stateCaptured argumentsCaptured
  simpa only [contextResult, context_canonical sorts arguments numerical valid,
    Option.map_map, Function.comp_def] using run

private def fallbackArguments : List ExprType :=
  [⟨0, false, ∅⟩, ⟨0, true, {0}⟩, ⟨0, false, {1}⟩]

/-- A total context projection can hide an invalid raw dependency rank by
its out-of-range fallback. Kernel well-formedness does not earn source metadata. -/
theorem fallback_context_wellFormed :
    Kernel.Context.WellFormed (fun _ => some ({} : Kernel.SortInfo)) (Statements.context fallbackArguments) := by
  exact (Kernel.Context.check_iff _ _).mp (by decide)

theorem fallback_metadata_refused : ¬ PrefixValid fallbackArguments ∧
    contextWalk [⟨natural 0, natural 0⟩] (canonicalTypes fallbackArguments) 0 [] [] = none := by
  decide +kernel


/-- The arity at a physical table position is read from the original term
constructor's complete argument-list payload. The source's behavior on a
malformed non-list payload is not identified with this partial projection. -/
def tableArity (entries : List Atom) (binary : Nat) : Option Nat :=
  (entries[binary]?).bind fun entry => match entry with
    | .expression [.symbol "MM0:MMBTerm", _, .expression [.symbol "MM0:L", .expression arguments], _, _] =>
        some arguments.length
    | _ => none

@[simp] theorem tableArity_termEntry (entries : List Atom) (binary : Nat)
    (sort : Atom) (arguments : List Atom) (ret value : Atom)
    (read : entries[binary]? = some (termEntryValue sort arguments ret value)) :
    tableArity entries binary = some arguments.length := by
  simp [tableArity, read, termEntryValue, listValue]

theorem tableArity_eq_some_iff (entries : List Atom) (binary count : Nat) :
    tableArity entries binary = some count ↔
      ∃ sort arguments ret value, entries[binary]? = some (termEntryValue sort arguments ret value) ∧
        arguments.length = count := by
  constructor
  · intro found
    obtain ⟨entry, read, projected⟩ := Option.bind_eq_some_iff.mp found
    split at projected
    · rename_i sort arguments ret value
      exact ⟨sort, arguments, ret, value, read, Option.some.inj projected⟩
    · simp at projected
  · rintro ⟨sort, arguments, ret, value, read, rfl⟩
    exact tableArity_termEntry entries binary sort arguments ret value read


/-- The original argument initializer earns all prefix metadata constraints;
no caller needs to provide the context walk's rank checks as a callback. -/
theorem prefixValid_of_loadArgs (sorts : List Kernel.SortInfo) (arguments : List ExprType)
    (loaded : Formats.MMB.State) (accepted : Formats.MMB.loadArgs sorts arguments = some loaded) :
    PrefixValid arguments := by
  intro position
  have checked := MMBInitializationSoundness.loadArgs_descriptor_checked sorts arguments loaded accepted
    position arguments[position] (List.getElem?_eq_getElem position.isLt)
  cases flag : arguments[position].bound with
  | false =>
      simp only [flag, Bool.false_eq_true, if_false] at checked ⊢
      intro rank member
      exact Finset.mem_range.mp (checked member)
  | true => simpa only [flag, if_true] using checked

theorem context_canonical_of_loadArgs (sorts : List MMUResolution.Binding) (arguments : List ExprType)
    (information : List Kernel.SortInfo) (loaded : Formats.MMB.State)
    (numerical : NumericalMap sorts) (accepted : Formats.MMB.loadArgs information arguments = some loaded) :
    contextWalk sorts (canonicalTypes arguments) 0 [] [] =
      (Kernel.Context.relocateSorts? (resolvedIds sorts) (Statements.context arguments)).map
        (fun context => (context.map Data.binder, (Statements.boundPositions arguments).map natural)) :=
  context_canonical sorts arguments numerical (prefixValid_of_loadArgs information arguments loaded accepted)


/-- The source term-table row has exactly these constructor fields. The argument
payload is kept raw here: a wrapped non-list is a separate admission issue. -/
def DeclarationShape (entry : Atom) : Prop :=
  ∃ sort arguments ret value,
    entry = .expression [.symbol "MM0:MMBTerm", sort,
      .expression [.symbol "MM0:L", arguments], ret, value]

/-- Syntactic admission of the argument payload in each matching original
term-table row. A malformed raw wrapper is not claimed to return None. -/
def ArgumentListRows (tableTerms : List Atom) : Prop :=
  ∀ entry ∈ tableTerms, DeclarationShape entry →
    ∃ sort arguments ret value,
      entry = .expression [.symbol "MM0:MMBTerm", sort, listValue arguments, ret, value]

/-- Complete parsed declaration images admit their original argument lists;
existing rows are retained, including unused declarations. -/
theorem ArgumentListRows.nil : ArgumentListRows [] := by
  intro entry absent
  cases absent

theorem ArgumentListRows.prepend {tableTerms : List Atom} (rows : ArgumentListRows tableTerms)
    (sort ret value : Atom) (arguments : List Atom) :
    ArgumentListRows (.expression [.symbol "MM0:MMBTerm", sort, listValue arguments, ret, value] :: tableTerms) := by
  intro entry member shape
  rcases List.mem_cons.mp member with rfl | member
  · exact ⟨sort, arguments, ret, value, rfl⟩
  · exact rows entry member shape

/-- A Polish instruction image retains its original physical byte metadata.
The hypothesis data field is ignored by the original source operation. -/
def CommandImage : Formats.MMB.UnifyCmd → Atom → Prop
  | .term index, atom => ∃ start after, atom = MMBExecution.commandValue 48 index start after
  | .termSave index, atom => ∃ start after, atom = MMBExecution.commandValue 49 index start after
  | .ref index, atom => ∃ start after, atom = MMBExecution.commandValue 50 index start after
  | .dummy index, atom => ∃ start after, atom = MMBExecution.commandValue 51 index start after
  | .hyp, atom => ∃ data start after, atom = MMBExecution.commandValue 54 data start after

/-- Filled and reserved slots use the original source option representation. -/
def decodingSlots (decoded : Statements.Decoding) : List Atom :=
  decoded.slots.map (fun slot => optionValue (slot.map Data.preterm))

def decodingValue (decoded : Statements.Decoding) (arity : Nat) : Atom :=
  unifyStateValue (decodingSlots decoded) (decoded.dummies.map natural) arity

@[simp] theorem decodingSlots_initial (arity : Nat) :
    decodingSlots (Statements.initial arity) = filledVariables 0 arity :=
  (filledVariables_initial arity).symm

@[simp] theorem decodingSlots_length (decoded : Statements.Decoding) :
    (decodingSlots decoded).length = decoded.slots.length := by simp [decodingSlots]

@[simp] theorem decodingSlots_set (decoded : Statements.Decoding) (index : Nat) (expression : Kernel.Preterm) :
    decodingSlots {decoded with slots := decoded.slots.set index (some expression)} =
      (decodingSlots decoded).set index (optionValue (some (Data.preterm expression))) := by
  simp [decodingSlots, List.map_set]

@[simp] theorem decodingSlots_reserve (decoded : Statements.Decoding) :
    decodingSlots {decoded with slots := decoded.slots ++ [none]} =
      decodingSlots decoded ++ [.symbol "None"] := by simp [decodingSlots, optionValue]

private theorem term_call_from_body (bindings : Subst) (state : Effects.State)
    (resolver tableSorts tableTerms tableTheorems : Atom) (fuel : Nat)
    (slots dummies : List Atom) (arity binary : Nat) (save : Bool) (codes : List Atom) (answer : Atom)
    (resolverArgument tablesArgument fuelArgument unifyArgument binaryArgument saveArgument codesArgument : Atom)
    (resolverCaptured : applySubst bindings resolverArgument = resolver)
    (tablesCaptured : applySubst bindings tablesArgument = tablesValue tableSorts tableTerms tableTheorems)
    (fuelReturned : PureReturns program bindings state fuelArgument state (natural fuel))
    (unifyCaptured : applySubst bindings unifyArgument = unifyStateValue slots dummies arity)
    (binaryReturned : PureReturns program bindings state binaryArgument state (natural binary))
    (saveCaptured : applySubst bindings saveArgument = boolean save)
    (codesCaptured : applySubst bindings codesArgument = listValue codes)
    (body : PureReturns program
      (termEnvironment resolver tableSorts tableTerms tableTheorems fuel slots dummies arity binary save codes)
      state termEquation.body state answer) :
    PureReturns program bindings state (.expression [.symbol "mm0:mmb:unify-term", resolverArgument,
      tablesArgument, fuelArgument, unifyArgument, binaryArgument, saveArgument, codesArgument]) state answer := by
  apply call_returns program bindings state state "mm0:mmb:unify-term" _ _ (by decide +kernel) _ (by decide)
  apply raw_argument_answers program bindings state state "mm0:mmb:unify-term" resolverArgument _ [] 0
    [_] (by decide +kernel)
  apply raw_argument_answers program bindings state state "mm0:mmb:unify-term" tablesArgument _ _ 1
    [_] (by decide +kernel)
  apply evaluated_argument_returns program bindings state state state (.function "mm0:mmb:unify-term")
    fuelArgument (natural fuel) _ _ _ 2 (by decide +kernel) fuelReturned
  apply raw_argument_answers program bindings state state "mm0:mmb:unify-term" unifyArgument _ _ 3
    [_] (by decide +kernel)
  apply evaluated_argument_returns program bindings state state state (.function "mm0:mmb:unify-term")
    binaryArgument (natural binary) _ _ _ 4 (by decide +kernel) binaryReturned
  apply raw_arguments_return program bindings state state "mm0:mmb:unify-term"
    [saveArgument, codesArgument] _ 5 _
  · intro offset inside
    have range : offset < 2 := by simpa using inside
    interval_cases offset <;> decide +kernel
  · simp only [List.map_cons, List.map_nil, resolverCaptured, tablesCaptured, unifyCaptured,
      saveCaptured, codesCaptured]
    exact authored_function_arguments_return program bindings
      (termEnvironment resolver tableSorts tableTerms tableTheorems fuel slots dummies arity binary save codes)
      state state "mm0:mmb:unify-term" [resolver,tablesValue tableSorts tableTerms tableTheorems,
        natural fuel,unifyStateValue slots dummies arity,natural binary,boolean save,listValue codes]
      7 termEquation.body answer (by decide +kernel) (by decide +kernel)
      (term_clause resolver tableSorts tableTerms tableTheorems fuel slots dummies arity binary save codes) body

private theorem expression_term_shape (save : Bool) :
    (if save then expressionSave else expressionNoSave) =
      .expression [.symbol "mm0:mmb:unify-term", .var "state",
        .expression [.symbol "MM0:MMBTables", .var "sorts", .var "terms", .var "theorems"], .var "fuel",
        .expression [.symbol "MM0:MMBUState", .expression [.symbol "MM0:L", .var "slots"],
          .expression [.symbol "MM0:L", .var "dummies"], .var "arity"], .var "data", boolean save,
        .expression [.symbol "MM0:L", .var "rest"]] := by
  cases save <;> decide +kernel

private theorem expression_term_from_body (state : Effects.State) (resolver sorts terms theorems : Atom)
    (fuel binary start after : Nat) (save : Bool) (slots dummies : List Atom) (arity : Nat)
    (rest : List Atom) (answer : Atom)
    (body : PureReturns program (termEnvironment resolver sorts terms theorems (fuel + 1)
      slots dummies arity binary save rest) state termEquation.body state answer) :
    PureReturns program
      (expressionEnvironment resolver sorts terms theorems (fuel + 1) slots dummies arity
        (MMBExecution.commandValue (if save then 49 else 48) binary start after :: rest))
      state expressionEquation.body state answer := by
  apply expression_command_from_body state resolver sorts terms theorems fuel
    (if save then 49 else 48) binary start after slots dummies arity rest
    (if save then expressionSave else expressionNoSave) answer
  · cases save <;>
      simp [expression_opcode_cases, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom, natural]
  · rw [expression_term_shape]
    apply term_call_from_body _ state resolver sorts terms theorems (fuel + 1)
      slots dummies arity binary save rest answer (.var "state")
      (.expression [.symbol "MM0:MMBTables", .var "sorts", .var "terms", .var "theorems"])
      (.var "fuel")
      (.expression [.symbol "MM0:MMBUState", .expression [.symbol "MM0:L", .var "slots"],
        .expression [.symbol "MM0:L", .var "dummies"], .var "arity"])
      (.var "data") (boolean save) (.expression [.symbol "MM0:L", .var "rest"])
    · simp [expressionCommandEnvironment, expressionEnvironment, applySubst, Subst.lookup]
    · simp [expressionCommandEnvironment, expressionEnvironment, applySubst,
        applySubst.applySubstList, Subst.lookup, tablesValue]
    · simpa [expressionCommandEnvironment, expressionEnvironment, applySubst, Subst.lookup] using
        variable_returns program
          (expressionCommandEnvironment resolver sorts terms theorems fuel
            (if save then 49 else 48) binary start after slots dummies arity rest) state "fuel"
    · simp [expressionCommandEnvironment, expressionEnvironment, applySubst,
        applySubst.applySubstList, Subst.lookup, unifyStateValue, listValue]
    · simpa [expressionCommandEnvironment, expressionEnvironment, applySubst, Subst.lookup] using
        variable_returns program
          (expressionCommandEnvironment resolver sorts terms theorems fuel
            (if save then 49 else 48) binary start after slots dummies arity rest) state "data"
    · cases save <;> rfl
    · simp [expressionCommandEnvironment, expressionEnvironment, applySubst,
        applySubst.applySubstList, Subst.lookup, listValue]
    · exact body

/-- A successful original child decoder retains the parent's reservation.
Completing the source term then fills precisely that earlier physical slot,
while retaining all slots and dummies introduced by its children. -/
theorem completedTermResult_decodeExprs (entries : List Atom) (terms sorts : List MMUResolution.Binding)
    (arity fuel count identifier : Nat) (save : Bool) (before after : Statements.Decoding)
    (commands remaining : List Formats.MMB.UnifyCmd) (arguments : List Kernel.Preterm) (rest : List Atom)
    (decoded : Statements.decodeExprs (tableArity entries) arity fuel count
      (if save then {before with slots := before.slots ++ [none]} else before)
      commands (resolvedIds terms) (resolvedIds sorts) = some (arguments,after,remaining)) :
    completedTermResult identifier arguments (decodingSlots after) (after.dummies.map natural)
      arity before.slots.length save rest =
      optionValue (some (unifyExpressionValue
        (Data.preterm (Kernel.Preterm.applyArgs (.term identifier) arguments))
        (decodingSlots (if save then {after with slots := (after.slots.set before.slots.length
          (some (Kernel.Preterm.applyArgs (.term identifier) arguments)))} else after))
        (after.dummies.map natural) arity rest)) := by
  cases save with
  | false => simp [completedTermResult]
  | true =>
      obtain ⟨suffix,consumed,extended,_,_⟩ := Formats.MMB.Soundness.decodeExprs_resolved_source_order
        (resolvedIds terms) (resolvedIds sorts) (tableArity entries) arity fuel count
        {before with slots := before.slots ++ [none]} after commands remaining arguments decoded
      have present : before.slots.length < (decodingSlots after).length := by
        simp only [decodingSlots_length,extended,List.length_append,List.length_cons,List.length_nil]
        omega
      simp [completedTermResult,List.getElem?_eq_getElem present]

private theorem term_decoded_from_children (state : Effects.State) (published : Atom)
    (sorts terms theorems : List MMUResolution.Binding) (nextSort nextTerm nextTheorem : Nat) (images : Atom)
    (tableSorts tableTheorems : Atom) (entries : List Atom) (fuel arity binary identifier count : Nat)
    (save : Bool) (before after : Statements.Decoding) (commands remaining : List Formats.MMB.UnifyCmd)
    (rawCommands rawRemaining : List Atom) (arguments : List Kernel.Preterm)
    (declared : MMUResolution.lookup terms (natural binary) = some (natural identifier))
    (arityFound : tableArity entries binary = some count)
    (decoded : Statements.decodeExprs (tableArity entries) arity fuel count
      (if save then {before with slots := before.slots ++ [none]} else before)
      commands (resolvedIds terms) (resolvedIds sorts) = some (arguments,after,remaining))
    (childBody : PureReturns program
      (expressionsEnvironment (resolverValue published sorts terms theorems nextSort nextTerm nextTheorem images)
        (tablesValue tableSorts (listValue entries) tableTheorems) fuel count
        (decodingValue (if save then {before with slots := before.slots ++ [none]} else before) arity)
        (listValue rawCommands))
      state expressionsEquation.body state (optionValue (some (unifyExpressionsValue (arguments.map Data.preterm)
        (decodingValue after arity) (listValue rawRemaining))))) :
    PureReturns program
      (termEnvironment (resolverValue published sorts terms theorems nextSort nextTerm nextTheorem images)
        tableSorts (listValue entries) tableTheorems (fuel + 1) (decodingSlots before)
        (before.dummies.map natural) arity binary save rawCommands)
      state termEquation.body state
        (optionValue (some (unifyExpressionValue
          (Data.preterm (Kernel.Preterm.applyArgs (.term identifier) arguments))
          (decodingSlots (if save then {after with slots := (after.slots.set before.slots.length
            (some (Kernel.Preterm.applyArgs (.term identifier) arguments)))} else after))
          (after.dummies.map natural) arity rawRemaining))) := by
  obtain ⟨sort,descriptors,ret,value,entryFound,countMatches⟩ := (tableArity_eq_some_iff entries binary count).mp arityFound
  let resolver := resolverValue published sorts terms theorems nextSort nextTerm nextTheorem images
  let prepared := termPreparedEnvironment resolver tableSorts tableTheorems (fuel + 1)
    (decodingSlots before) (before.dummies.map natural) arity binary identifier save rawCommands entries sort descriptors ret value
  have actualChildren : PureReturns program prepared state
      (.expression [.symbol "mm0:mmb:unify-expressions", .var "state",
        .expression [.symbol "MM0:MMBTables", .var "sorts", .var "terms", .var "theorems"],
        .expression [.symbol "-", .var "fuel", natural 1], .expression [.symbol "size-atom", .var "args"],
        .expression [.symbol "MM0:MMBUState", .var "nextSlots", .var "dummies", .var "arity"], .var "codes"])
      state (optionValue (some (unifyExpressionsValue (arguments.map Data.preterm)
        (decodingValue after arity) (listValue rawRemaining)))) := by
    apply expressions_call_from_body prepared state resolver
      (tablesValue tableSorts (listValue entries) tableTheorems) fuel count
      (decodingValue (if save then {before with slots := before.slots ++ [none]} else before) arity)
      (listValue rawCommands) _ (.var "state")
      (.expression [.symbol "MM0:MMBTables", .var "sorts", .var "terms", .var "theorems"])
      (.expression [.symbol "-", .var "fuel", natural 1]) (.expression [.symbol "size-atom", .var "args"])
      (.expression [.symbol "MM0:MMBUState", .var "nextSlots", .var "dummies", .var "arity"]) (.var "codes")
    · rfl
    · rfl
    · exact decrement_returns prepared state fuel "fuel" rfl
    · apply native_variable_call_returns program prepared state state "size-atom" ["args"] (natural count)
        (by decide) (by decide) _ (by decide)
      change (.ok (state,[natural descriptors.length]) : Effects.Result) = .ok (state,[natural count])
      rw [countMatches]
    · cases save <;> simp [decodingValue,decodingSlots,prepared,termPreparedEnvironment,
        termSelectedEnvironment,termReadEnvironment,termEnvironment,applySubst,applySubst.applySubstList,Subst.lookup,
        unifyStateValue,optionValue]
    · rfl
    · exact childBody
  have completed := term_body_from_children_returns state published sorts terms theorems nextSort nextTerm nextTheorem images
    tableSorts tableTheorems (fuel + 1) (decodingSlots before) (before.dummies.map natural) arity binary identifier save
    rawCommands entries sort descriptors ret value declared entryFound arguments (decodingSlots after)
    (after.dummies.map natural) arity rawRemaining actualChildren
  simpa only [decodingSlots_length,
    completedTermResult_decodeExprs entries terms sorts arity fuel count identifier save before after
      commands remaining arguments rawRemaining decoded] using completed

private theorem decoded_bodies (state : Effects.State) (published : Atom)
    (sorts terms theorems : List MMUResolution.Binding) (nextSort nextTerm nextTheorem : Nat) (images : Atom)
    (tableSorts tableTheorems : Atom) (entries : List Atom) (arity fuel : Nat) :
    (∀ (before after : Statements.Decoding) (commands remaining : List Formats.MMB.UnifyCmd)
      (rawCommands : List Atom) (expression : Kernel.Preterm),
      List.Forall₂ CommandImage commands rawCommands →
      Statements.decodeExpr (tableArity entries) arity fuel before commands (resolvedIds terms) (resolvedIds sorts) =
        some (expression,after,remaining) →
      ∃ rawRemaining, List.Forall₂ CommandImage remaining rawRemaining ∧
        List.IsSuffix rawRemaining rawCommands ∧
        PureReturns program
          (expressionEnvironment (resolverValue published sorts terms theorems nextSort nextTerm nextTheorem images)
            tableSorts (listValue entries) tableTheorems fuel (decodingSlots before) (before.dummies.map natural) arity rawCommands)
          state expressionEquation.body state (optionValue (some (unifyExpressionValue (Data.preterm expression)
            (decodingSlots after) (after.dummies.map natural) arity rawRemaining)))) ∧
    (∀ (count : Nat) (before after : Statements.Decoding) (commands remaining : List Formats.MMB.UnifyCmd)
      (rawCommands : List Atom) (arguments : List Kernel.Preterm),
      List.Forall₂ CommandImage commands rawCommands →
      Statements.decodeExprs (tableArity entries) arity fuel count before commands (resolvedIds terms) (resolvedIds sorts) =
        some (arguments,after,remaining) →
      ∃ rawRemaining, List.Forall₂ CommandImage remaining rawRemaining ∧
        List.IsSuffix rawRemaining rawCommands ∧
        PureReturns program
          (expressionsEnvironment (resolverValue published sorts terms theorems nextSort nextTerm nextTheorem images)
            (tablesValue tableSorts (listValue entries) tableTheorems) fuel count (decodingValue before arity)
            (listValue rawCommands)) state expressionsEquation.body state
          (optionValue (some (unifyExpressionsValue (arguments.map Data.preterm) (decodingValue after arity)
            (listValue rawRemaining))))) := by
  let resolver := resolverValue published sorts terms theorems nextSort nextTerm nextTheorem images
  let tables := tablesValue tableSorts (listValue entries) tableTheorems
  induction fuel with
  | zero =>
      constructor
      · intro before after commands remaining raw expression encoded decoded
        simp [Statements.decodeExpr] at decoded
      · intro count before after commands remaining raw arguments encoded decoded
        cases count with
        | zero =>
            have same : ([],before,commands) = (arguments,after,remaining) := by
              simpa [Statements.decodeExprs] using decoded
            cases same
            exact ⟨raw,encoded,List.suffix_refl raw,expressions_empty_body_returns state resolver tables 0
              (decodingValue before arity) (listValue raw)⟩
        | succ count => simp [Statements.decodeExprs] at decoded
  | succ fuel ih =>
      obtain ⟨expressionIH,argumentsIH⟩ := ih
      constructor
      · intro before after commands remaining raw expression encoded decoded
        cases commands with
        | nil => simp [Statements.decodeExpr] at decoded
        | cons command commands =>
            cases encoded with
            | cons firstImage restImages =>
                cases command with
                | hyp => simp [Statements.decodeExpr] at decoded
                | ref index =>
                    rcases firstImage with ⟨start,finish,rfl⟩
                    change ((before.slots[index]?).bind id).bind (fun value => some (value,before,commands)) =
                      some (expression,after,remaining) at decoded
                    obtain ⟨value,read,same⟩ := Option.bind_eq_some_iff.mp decoded
                    obtain ⟨slot,slotRead,filled⟩ := Option.bind_eq_some_iff.mp read
                    change slot = some value at filled
                    subst slot
                    cases Option.some.inj same
                    have sourceRead : (decodingSlots before)[index]? =
                        some (optionValue (some (Data.preterm expression))) := by
                      simp [decodingSlots,List.getElem?_map,slotRead]
                    refine ⟨_,restImages,List.suffix_cons _ _,?_⟩
                    apply expression_reference_from_body state resolver tableSorts (listValue entries) tableTheorems
                      fuel index start finish (decodingSlots before) (before.dummies.map natural) arity _ _
                    exact reference_filled_body_returns state resolver tableSorts (listValue entries)
                      tableTheorems (Data.preterm expression) fuel index start finish (decodingSlots before)
                      (before.dummies.map natural) arity _ sourceRead
                | dummy binary =>
                    rcases firstImage with ⟨start,finish,rfl⟩
                    change (resolvedIds sorts binary).bind (fun logical =>
                      some (Kernel.Preterm.var (arity + before.dummies.length),
                        ⟨before.slots ++ [some (.var (arity + before.dummies.length))], before.dummies ++ [logical]⟩,
                        commands)) = some (expression,after,remaining) at decoded
                    obtain ⟨logical,read,same⟩ := Option.bind_eq_some_iff.mp decoded
                    cases Option.some.inj same
                    have declared := (resolvedIds_eq_some_iff sorts binary logical).mp read
                    refine ⟨_,restImages,List.suffix_cons _ _,?_⟩
                    apply expression_command_from_body state resolver tableSorts (listValue entries) tableTheorems
                      fuel 51 binary start finish (decodingSlots before) (before.dummies.map natural) arity _ expressionDummy _
                    · simp [expression_opcode_cases,SpaceSemantics.selectCase,SpaceSemantics.matchValue,matchAtom,natural]
                    · simpa [dummyResultValue,declared,decodingSlots,unifyExpressionValue] using
                        dummy_body_returns state published sorts terms theorems nextSort nextTerm nextTheorem images
                          tableSorts (listValue entries) tableTheorems fuel binary start finish
                          (decodingSlots before) (before.dummies.map natural) arity _
                | term binary =>
                    rcases firstImage with ⟨start,finish,rfl⟩
                    simp only [Statements.decodeExpr] at decoded
                    obtain ⟨logical,readLogical,more⟩ := Option.bind_eq_some_iff.mp decoded
                    obtain ⟨count,readCount,more⟩ := Option.bind_eq_some_iff.mp more
                    obtain ⟨result,children,same⟩ := Option.bind_eq_some_iff.mp more
                    rcases result with ⟨arguments,next,tail⟩
                    cases Option.some.inj same
                    obtain ⟨rawTail,tailImages,tailSuffix,childrenBody⟩ := argumentsIH count before next commands tail _ arguments restImages children
                    refine ⟨rawTail,tailImages,tailSuffix.trans (List.suffix_cons _ _),?_⟩
                    apply expression_term_from_body state resolver tableSorts (listValue entries) tableTheorems
                      fuel binary start finish false (decodingSlots before) (before.dummies.map natural) arity _ _
                    simpa using term_decoded_from_children state published sorts terms theorems nextSort nextTerm nextTheorem images
                      tableSorts tableTheorems entries fuel arity binary logical count false before next commands tail _ rawTail arguments
                      ((resolvedIds_eq_some_iff terms binary logical).mp readLogical) readCount children childrenBody
                | termSave binary =>
                    rcases firstImage with ⟨start,finish,rfl⟩
                    simp only [Statements.decodeExpr] at decoded
                    obtain ⟨logical,readLogical,more⟩ := Option.bind_eq_some_iff.mp decoded
                    obtain ⟨count,readCount,more⟩ := Option.bind_eq_some_iff.mp more
                    obtain ⟨result,children,same⟩ := Option.bind_eq_some_iff.mp more
                    rcases result with ⟨arguments,next,tail⟩
                    cases Option.some.inj same
                    obtain ⟨rawTail,tailImages,tailSuffix,childrenBody⟩ := argumentsIH count
                      {before with slots := before.slots ++ [none]} next commands tail _ arguments restImages children
                    refine ⟨rawTail,tailImages,tailSuffix.trans (List.suffix_cons _ _),?_⟩
                    apply expression_term_from_body state resolver tableSorts (listValue entries) tableTheorems
                      fuel binary start finish true (decodingSlots before) (before.dummies.map natural) arity _ _
                    simpa [decodingSlots_set] using term_decoded_from_children state published sorts terms theorems
                      nextSort nextTerm nextTheorem images tableSorts tableTheorems entries fuel arity binary logical count true
                      before next commands tail _ rawTail arguments
                      ((resolvedIds_eq_some_iff terms binary logical).mp readLogical) readCount children childrenBody
      · intro count before after commands remaining raw arguments encoded decoded
        cases count with
        | zero =>
            have same : ([],before,commands) = (arguments,after,remaining) := by
              simpa [Statements.decodeExprs] using decoded
            cases same
            exact ⟨raw,encoded,List.suffix_refl raw,expressions_empty_body_returns state resolver tables (fuel + 1)
              (decodingValue before arity) (listValue raw)⟩
        | succ count =>
            simp only [Statements.decodeExprs] at decoded
            obtain ⟨firstResult,firstDecoded,more⟩ := Option.bind_eq_some_iff.mp decoded
            rcases firstResult with ⟨first,middle,middleCommands⟩
            obtain ⟨tailResult,tailDecoded,same⟩ := Option.bind_eq_some_iff.mp more
            rcases tailResult with ⟨tail,final,finalCommands⟩
            cases Option.some.inj same
            obtain ⟨rawMiddle,middleImages,firstSuffix,firstBody⟩ := expressionIH before middle commands middleCommands raw first encoded firstDecoded
            obtain ⟨rawTail,tailImages,tailSuffix,tailBody⟩ := argumentsIH count middle final middleCommands finalCommands
              rawMiddle tail middleImages tailDecoded
            let bindings := expressionsEnvironment resolver tables (fuel + 1) (count + 1)
              (decodingValue before arity) (listValue raw)
            let selected := ("rest",listValue rawMiddle) :: ("after",decodingValue middle arity) ::
              ("first",Data.preterm first) :: bindings
            have firstReturns : PureReturns program bindings state
                (.expression [.symbol "mm0:mmb:unify-expression", .var "state", .var "tables",
                  .expression [.symbol "-", .var "fuel", natural 1], .var "unify", .var "codes"])
                state (optionValue (some (unifyExpressionValue (Data.preterm first)
                  (decodingSlots middle) (middle.dummies.map natural) arity rawMiddle))) := by
              apply expression_call_from_body bindings state resolver tableSorts (listValue entries) tableTheorems fuel
                (decodingSlots before) (before.dummies.map natural) arity raw _
                (.var "state") (.var "tables") (.expression [.symbol "-", .var "fuel", natural 1])
                (.var "unify") (.var "codes")
              · rfl
              · rfl
              · exact decrement_returns bindings state fuel "fuel" rfl
              · rfl
              · rfl
              · exact firstBody
            have tailReturns : PureReturns program selected state
                (.expression [.symbol "mm0:mmb:unify-expressions", .var "state", .var "tables",
                  .expression [.symbol "-", .var "fuel", natural 1], .expression [.symbol "-", .var "count", natural 1],
                  .var "after", .var "rest"])
                state (optionValue (some (unifyExpressionsValue (tail.map Data.preterm)
                  (decodingValue final arity) (listValue rawTail)))) := by
              apply expressions_call_from_body selected state resolver tables fuel count (decodingValue middle arity)
                (listValue rawMiddle) _ (.var "state") (.var "tables")
                (.expression [.symbol "-", .var "fuel", natural 1]) (.expression [.symbol "-", .var "count", natural 1])
                (.var "after") (.var "rest")
              · rfl
              · rfl
              · exact decrement_returns selected state fuel "fuel" rfl
              · exact decrement_returns selected state count "count" rfl
              · rfl
              · rfl
              · exact tailBody
            refine ⟨rawTail,tailImages,tailSuffix.trans firstSuffix,?_⟩
            simpa only [List.map_cons,decodingValue,unifyExpressionValue] using
              expressions_cons_body_returns state resolver tables fuel count (decodingValue before arity) (listValue raw)
                (Data.preterm first) (decodingValue middle arity) (listValue rawMiddle)
                (decodingValue final arity) (listValue rawTail) (tail.map Data.preterm) firstReturns tailReturns

/-- Every successful original resolved expression decode has an actual quoted
source execution with exactly the original expression, filled/reserved slots,
dummies and unread physical command images. No completed child trace is
supplied: nested term and sibling execution is earned by the fuel induction. -/
theorem unify_expression_decoded_returns (bindings : Subst) (state : Effects.State) (published : Atom)
    (sorts terms theorems : List MMUResolution.Binding) (nextSort nextTerm nextTheorem : Nat) (images : Atom)
    (tableSorts tableTheorems : Atom) (entries : List Atom) (arity fuel : Nat)
    (before after : Statements.Decoding) (commands remaining : List Formats.MMB.UnifyCmd)
    (rawCommands : List Atom) (expression : Kernel.Preterm)
    (encoded : List.Forall₂ CommandImage commands rawCommands)
    (decoded : Statements.decodeExpr (tableArity entries) arity fuel before commands
      (resolvedIds terms) (resolvedIds sorts) = some (expression,after,remaining))
    (resolverName tablesName fuelName unifyName codesName : String)
    (resolverCaptured : applySubst bindings (.var resolverName) =
      resolverValue published sorts terms theorems nextSort nextTerm nextTheorem images)
    (tablesCaptured : applySubst bindings (.var tablesName) =
      tablesValue tableSorts (listValue entries) tableTheorems)
    (fuelCaptured : applySubst bindings (.var fuelName) = natural fuel)
    (unifyCaptured : applySubst bindings (.var unifyName) = decodingValue before arity)
    (codesCaptured : applySubst bindings (.var codesName) = listValue rawCommands) :
    ∃ rawRemaining, List.Forall₂ CommandImage remaining rawRemaining ∧
      List.IsSuffix rawRemaining rawCommands ∧
      PureReturns program bindings state
        (.expression [.symbol "mm0:mmb:unify-expression", .var resolverName, .var tablesName,
          .var fuelName, .var unifyName, .var codesName]) state
        (optionValue (some (unifyExpressionValue (Data.preterm expression) (decodingSlots after)
          (after.dummies.map natural) arity rawRemaining))) := by
  obtain ⟨rawRemaining,tailImages,tailSuffix,body⟩ :=
    (decoded_bodies state published sorts terms theorems nextSort nextTerm nextTheorem images
      tableSorts tableTheorems entries arity fuel).1 before after commands remaining rawCommands expression encoded decoded
  refine ⟨rawRemaining,tailImages,tailSuffix,?_⟩
  exact expression_from_body bindings state _ tableSorts (listValue entries) tableTheorems fuel
    (decodingSlots before) (before.dummies.map natural) arity rawCommands _
    resolverName tablesName fuelName unifyName codesName resolverCaptured tablesCaptured fuelCaptured
    unifyCaptured codesCaptured body

/-- Ordered child decoding preserves all nested saved slots, repeated reference
occurrences, dummy extensions and exact unread source command images. -/
theorem unify_expressions_decoded_returns (bindings : Subst) (state : Effects.State) (published : Atom)
    (sorts terms theorems : List MMUResolution.Binding) (nextSort nextTerm nextTheorem : Nat) (images : Atom)
    (tableSorts tableTheorems : Atom) (entries : List Atom) (arity fuel count : Nat)
    (before after : Statements.Decoding) (commands remaining : List Formats.MMB.UnifyCmd)
    (rawCommands : List Atom) (arguments : List Kernel.Preterm)
    (encoded : List.Forall₂ CommandImage commands rawCommands)
    (decoded : Statements.decodeExprs (tableArity entries) arity fuel count before commands
      (resolvedIds terms) (resolvedIds sorts) = some (arguments,after,remaining))
    (resolverName tablesName fuelName countName unifyName codesName : String)
    (resolverCaptured : applySubst bindings (.var resolverName) =
      resolverValue published sorts terms theorems nextSort nextTerm nextTheorem images)
    (tablesCaptured : applySubst bindings (.var tablesName) =
      tablesValue tableSorts (listValue entries) tableTheorems)
    (fuelCaptured : applySubst bindings (.var fuelName) = natural fuel)
    (countCaptured : applySubst bindings (.var countName) = natural count)
    (unifyCaptured : applySubst bindings (.var unifyName) = decodingValue before arity)
    (codesCaptured : applySubst bindings (.var codesName) = listValue rawCommands) :
    ∃ rawRemaining, List.Forall₂ CommandImage remaining rawRemaining ∧
      List.IsSuffix rawRemaining rawCommands ∧
      PureReturns program bindings state
        (.expression [.symbol "mm0:mmb:unify-expressions", .var resolverName, .var tablesName,
          .var fuelName, .var countName, .var unifyName, .var codesName]) state
        (optionValue (some (unifyExpressionsValue (arguments.map Data.preterm) (decodingValue after arity)
          (listValue rawRemaining)))) := by
  obtain ⟨rawRemaining,tailImages,tailSuffix,body⟩ :=
    (decoded_bodies state published sorts terms theorems nextSort nextTerm nextTheorem images
      tableSorts tableTheorems entries arity fuel).2 count before after commands remaining rawCommands arguments encoded decoded
  refine ⟨rawRemaining,tailImages,tailSuffix,?_⟩
  apply expressions_call_from_body bindings state _ (tablesValue tableSorts (listValue entries) tableTheorems)
    fuel count (decodingValue before arity) (listValue rawCommands) _
    (.var resolverName) (.var tablesName) (.var fuelName) (.var countName) (.var unifyName) (.var codesName)
    resolverCaptured tablesCaptured
  · simpa [fuelCaptured] using variable_returns program bindings state fuelName
  · simpa [countCaptured] using variable_returns program bindings state countName
  · exact unifyCaptured
  · exact codesCaptured
  · exact body

private theorem hypotheses_decoded_body_returns (state : Effects.State) (published : Atom)
    (sorts terms theorems : List MMUResolution.Binding) (nextSort nextTerm nextTheorem : Nat) (images : Atom)
    (tableSorts tableTheorems : Atom) (entries : List Atom) (arity fuel : Nat)
    (before : Statements.Decoding) (commands : List Formats.MMB.UnifyCmd) (rawCommands : List Atom)
    (hypotheses : List Kernel.Preterm) (encoded : List.Forall₂ CommandImage commands rawCommands)
    (accepted : Statements.decodeHyps (tableArity entries) arity fuel before commands
      (resolvedIds terms) (resolvedIds sorts) = some hypotheses) :
    PureReturns program
      (hypothesesEnvironment (resolverValue published sorts terms theorems nextSort nextTerm nextTheorem images)
        (tablesValue tableSorts (listValue entries) tableTheorems) fuel (decodingValue before arity) rawCommands)
      state hypothesesEquation.body state (optionValue (some (listValue (hypotheses.map Data.preterm)))) := by
  let resolver := resolverValue published sorts terms theorems nextSort nextTerm nextTheorem images
  let tables := tablesValue tableSorts (listValue entries) tableTheorems
  induction fuel generalizing before commands rawCommands hypotheses with
  | zero =>
      cases commands with
      | nil =>
          cases encoded
          have same : [] = hypotheses := by simpa [Statements.decodeHyps] using accepted
          cases same
          exact hypotheses_empty_body_returns state resolver tables 0 (decodingValue before arity)
      | cons command commands => simp [Statements.decodeHyps] at accepted
  | succ fuel ih =>
      cases commands with
      | nil =>
          cases encoded
          have same : [] = hypotheses := by simpa [Statements.decodeHyps] using accepted
          cases same
          exact hypotheses_empty_body_returns state resolver tables (fuel + 1) (decodingValue before arity)
      | cons command commands =>
          cases encoded with
          | cons firstImage restImages =>
              rename_i rawFirst rawRest
              cases command with
              | term binary => simp [Statements.decodeHyps] at accepted
              | termSave binary => simp [Statements.decodeHyps] at accepted
              | ref index => simp [Statements.decodeHyps] at accepted
              | dummy sort => simp [Statements.decodeHyps] at accepted
              | hyp =>
                  rcases firstImage with ⟨data,start,finish,rfl⟩
                  simp only [Statements.decodeHyps] at accepted
                  obtain ⟨firstResult,firstDecoded,more⟩ := Option.bind_eq_some_iff.mp accepted
                  rcases firstResult with ⟨first,middle,remaining⟩
                  split at more
                  · simp at more
                  · rename_i noDummies
                    have empty : middle.dummies = [] := by simpa using noDummies
                    obtain ⟨earlier,tailDecoded,same⟩ := Option.bind_eq_some_iff.mp more
                    cases Option.some.inj same
                    obtain ⟨rawRemaining,remainingImages,_,firstBody⟩ :=
                      (decoded_bodies state published sorts terms theorems nextSort nextTerm nextTheorem images
                        tableSorts tableTheorems entries arity fuel).1
                        before middle commands remaining _ first restImages firstDecoded
                    have tailBody := ih middle remaining rawRemaining earlier remainingImages tailDecoded
                    let selected := hypothesesCommandEnvironment resolver tables fuel data start finish
                      (decodingValue before arity) rawRest
                    let decoded := ("remaining",listValue rawRemaining) :: ("arity",natural arity) ::
                      ("slots",listValue (decodingSlots middle)) :: ("first",Data.preterm first) :: selected
                    have childReturns : PureReturns program selected state
                        (.expression [.symbol "mm0:mmb:unify-expression", .var "state", .var "tables",
                          .expression [.symbol "-", .var "fuel",natural 1],.var "unify",
                          .expression [.symbol "MM0:L",.var "rest"]]) state
                        (optionValue (some (unifyExpressionValue (Data.preterm first)
                          (decodingSlots middle) [] arity rawRemaining))) := by
                      apply expression_call_from_body selected state resolver tableSorts (listValue entries) tableTheorems
                        fuel (decodingSlots before) (before.dummies.map natural) arity rawRest _
                        (.var "state") (.var "tables") (.expression [.symbol "-",.var "fuel",natural 1])
                        (.var "unify") (.expression [.symbol "MM0:L",.var "rest"])
                      · rfl
                      · rfl
                      · exact decrement_returns selected state fuel "fuel" rfl
                      · rfl
                      · simp [selected,hypothesesCommandEnvironment,hypothesesEnvironment,
                          applySubst,applySubst.applySubstList,Subst.lookup,listValue]
                      · simpa only [empty,List.map_nil] using firstBody
                    have tailReturns : PureReturns program decoded state
                        (.expression [.symbol "mm0:mmb:unify-hypotheses",.var "state",.var "tables",
                          .expression [.symbol "-",.var "fuel",natural 1],
                          .expression [.symbol "MM0:MMBUState",.var "slots",.expression [.symbol "MM0:L",.expression []],.var "arity"],
                          .var "remaining"]) state (optionValue (some (listValue (earlier.map Data.preterm)))) := by
                      apply hypotheses_call_from_body decoded state resolver tables fuel (decodingValue middle arity)
                        rawRemaining _ (.var "state") (.var "tables") (.expression [.symbol "-",.var "fuel",natural 1])
                        (.expression [.symbol "MM0:MMBUState",.var "slots",.expression [.symbol "MM0:L",.expression []],.var "arity"])
                        (.var "remaining")
                      · rfl
                      · rfl
                      · exact decrement_returns decoded state fuel "fuel" rfl
                      · simp [decoded,applySubst,applySubst.applySubstList,Subst.lookup,decodingValue,unifyStateValue,listValue,empty]
                      · rfl
                      · exact tailBody
                    simpa only [List.map_append,List.map_cons,List.map_nil] using
                      hypotheses_cons_body_returns state resolver tables fuel data start finish
                        (decodingValue before arity) rawRest (Data.preterm first) (decodingSlots middle) arity
                        rawRemaining (earlier.map Data.preterm) childReturns tailReturns

/-- Every successful original hypothesis decode runs the quoted source
recursion. Nested saved terms may be used by later hypotheses; each completed
child discharges the source's empty-dummy guard, and snoc preserves the original
hypothesis order and repeated occurrences. -/
theorem unify_hypotheses_decoded_returns (bindings : Subst) (state : Effects.State) (published : Atom)
    (sorts terms theorems : List MMUResolution.Binding) (nextSort nextTerm nextTheorem : Nat) (images : Atom)
    (tableSorts tableTheorems : Atom) (entries : List Atom) (arity fuel : Nat)
    (before : Statements.Decoding) (commands : List Formats.MMB.UnifyCmd) (rawCommands : List Atom)
    (hypotheses : List Kernel.Preterm) (encoded : List.Forall₂ CommandImage commands rawCommands)
    (accepted : Statements.decodeHyps (tableArity entries) arity fuel before commands
      (resolvedIds terms) (resolvedIds sorts) = some hypotheses)
    (resolverName tablesName fuelName unifyName codesName : String)
    (resolverCaptured : applySubst bindings (.var resolverName) =
      resolverValue published sorts terms theorems nextSort nextTerm nextTheorem images)
    (tablesCaptured : applySubst bindings (.var tablesName) = tablesValue tableSorts (listValue entries) tableTheorems)
    (fuelCaptured : applySubst bindings (.var fuelName) = natural fuel)
    (unifyCaptured : applySubst bindings (.var unifyName) = decodingValue before arity)
    (codesCaptured : applySubst bindings (.var codesName) = listValue rawCommands) :
    PureReturns program bindings state
      (.expression [.symbol "mm0:mmb:unify-hypotheses",.var resolverName,.var tablesName,
        .var fuelName,.var unifyName,.var codesName]) state
      (optionValue (some (listValue (hypotheses.map Data.preterm)))) := by
  apply hypotheses_call_from_body bindings state _ _ fuel (decodingValue before arity) rawCommands _
    (.var resolverName) (.var tablesName) (.var fuelName) (.var unifyName) (.var codesName)
    resolverCaptured tablesCaptured
  · simpa [fuelCaptured] using variable_returns program bindings state fuelName
  · exact unifyCaptured
  · exact codesCaptured
  · exact hypotheses_decoded_body_returns state published sorts terms theorems nextSort nextTerm nextTheorem images
      tableSorts tableTheorems entries arity fuel before commands rawCommands hypotheses encoded accepted

private def signatureEquation := sourceEquation "mm0:mmb:theorem-signature"
private def signatureCases := casesOf (match signatureEquation.body with
  | .expression [_,_,body] => body | _ => .symbol "None")
private def signatureFound := (signatureCases[0]'(by decide)).2
private def signatureConclusionCases := casesOf signatureFound
private def signatureConclusionFound := (signatureConclusionCases[0]'(by decide)).2
private def signatureHypothesesCases := casesOf signatureConclusionFound
private def signatureHypothesesFound := (signatureHypothesesCases[0]'(by decide)).2
private def signatureEnvironment (resolver tables : Atom) (types : List (Atom × Bool × List Nat))
    (codes : List Atom) (ending : Atom) : Subst :=
  [("end",ending),("codes",.expression codes),("arguments",.expression (typeValues types)),
    ("tables",tables),("state",resolver)]
private theorem signature_unique :
    program.equations.filter (·.head == "mm0:mmb:theorem-signature") = [signatureEquation] := by decide +kernel
private theorem signature_formals : signatureEquation.arguments =
    [.var "state",.var "tables",.expression [.symbol "MM0:MMBTheorem",
      .expression [.symbol "MM0:L",.var "arguments"],
      .expression [.symbol "MM0:MMBStream",.expression [.symbol "MM0:L",.var "codes"],.var "end"]]] := by decide
private theorem signature_shape : signatureEquation.body =
    .expression [.symbol "let*",.expression [
      .expression [.var "context",.expression [.symbol "mm0:mmb:context",.var "state",
        .expression [.symbol "MM0:L",.var "arguments"]]],
      .expression [.var "initial",.expression [.symbol "mm0:mmb:unify-initial",
        .expression [.symbol "size-atom",.var "arguments"]]],
      .expression [.var "fuel",.expression [.symbol "+",.expression [.symbol "*",natural 2,
        .expression [.symbol "size-atom",.var "codes"]],natural 2]]],
      .expression [.symbol "case",.var "context",
        .expression (signatureCases.map fun row => .expression [row.1,row.2])]] := by decide
private theorem signature_cases : signatureCases =
    [(.expression [.symbol "Some",.expression [.symbol "MM0:MMBContext",.var "ctx",.var "bound"]],signatureFound),
      (.var "bad",.symbol "None")] := by decide
private theorem signature_found_shape : signatureFound =
    .expression [.symbol "case",.expression [.symbol "mm0:mmb:unify-expression",.var "state",.var "tables",.var "fuel",
      .var "initial",.expression [.symbol "MM0:L",.var "codes"]],
      .expression (signatureConclusionCases.map fun row => .expression [row.1,row.2])] := by decide
private theorem signature_conclusion_cases : signatureConclusionCases =
    [(.expression [.symbol "Some",.expression [.symbol "MM0:MMBUExpression",.var "conclusion",
      .expression [.symbol "MM0:MMBUState",.var "slots",.expression [.symbol "MM0:L",.expression []],.var "arity"],
      .var "rest"]],signatureConclusionFound),(.var "bad",.symbol "None")] := by decide
private theorem signature_conclusion_found_shape : signatureConclusionFound =
    .expression [.symbol "case",.expression [.symbol "mm0:mmb:unify-hypotheses",.var "state",.var "tables",.var "fuel",
      .expression [.symbol "MM0:MMBUState",.var "slots",.expression [.symbol "MM0:L",.expression []],.var "arity"],.var "rest"],
      .expression (signatureHypothesesCases.map fun row => .expression [row.1,row.2])] := by decide
private theorem signature_hypotheses_cases : signatureHypothesesCases =
    [(.expression [.symbol "Some",.var "hyps"],signatureHypothesesFound),(.var "bad",.symbol "None")] := by decide
private theorem signature_hypotheses_found_shape : signatureHypothesesFound =
    .expression [.symbol "Some",.expression [.symbol "MM0:L",.expression [.symbol "MM0:Theorem",
      .var "ctx",.var "hyps",.var "conclusion"]]] := by decide

private theorem signature_clause (resolver tables : Atom) (types : List (Atom × Bool × List Nat))
    (codes : List Atom) (ending : Atom) :
    clauses program "mm0:mmb:theorem-signature" [resolver,tables,
      .expression [.symbol "MM0:MMBTheorem",listValue (typeValues types),
        .expression [.symbol "MM0:MMBStream",listValue codes,ending]]] =
      [.evaluate (signatureEnvironment resolver tables types codes ending) signatureEquation.body] := by
  rw [clauses_use_only_the_named_equations,signature_unique]
  simp [signature_formals,signatureEnvironment,SpaceSemantics.matchValue,
    SpaceSemantics.matchValue.matchValues,matchAtom,Subst.lookup,listValue]

private theorem signature_context_returns (bindings : Subst) (state : Effects.State) (published : Atom)
    (sorts terms theorems : List MMUResolution.Binding) (nextSort nextTerm nextTheorem : Nat) (images : Atom)
    (types : List (Atom × Bool × List Nat))
    (resolverCaptured : applySubst bindings (.var "state") =
      resolverValue published sorts terms theorems nextSort nextTerm nextTheorem images)
    (typesCaptured : applySubst bindings (.var "arguments") = .expression (typeValues types)) :
    PureReturns program bindings state
      (.expression [.symbol "mm0:mmb:context",.var "state",.expression [.symbol "MM0:L",.var "arguments"]]) state
      (contextResult sorts types 0 [] []) := by
  let prior : Subst := [("r",resolverValue published sorts terms theorems nextSort nextTerm nextTheorem images),
    ("a",listValue (typeValues types))]
  have returned := context_returns prior state published sorts terms theorems nextSort nextTerm nextTheorem images
    types "r" "a" rfl rfl
  apply captured_call_returns program prior bindings state state "mm0:mmb:context" [.var "r",.var "a"]
    [.var "state",.expression [.symbol "MM0:L",.var "arguments"]] _ (by decide +kernel) (by decide) _ _ _ returned
  · intro offset argument found
    have bounded : offset < 2 := by have inside := (getElem?_eq_some_iff.mp found).choose; simpa using inside
    interval_cases offset <;> simp at found <;> subst argument <;> right <;> rfl
  · intro offset argument found
    have bounded : offset < 2 := by have inside := (getElem?_eq_some_iff.mp found).choose; simpa using inside
    interval_cases offset
    · simp at found; subst argument; right; rfl
    · simp at found; subst argument; left; decide +kernel
  · change [resolverValue published sorts terms theorems nextSort nextTerm nextTheorem images,
        listValue (typeValues types)] = [applySubst bindings (.var "state"),
        applySubst bindings (.expression [.symbol "MM0:L",.var "arguments"])]
    rw [resolverCaptured]
    have wrapped : applySubst bindings (.expression [.symbol "MM0:L",.var "arguments"]) =
        listValue (typeValues types) := by
      change Atom.expression [.symbol "MM0:L",applySubst bindings (.var "arguments")] = _
      rw [typesCaptured]
      rfl
    rw [wrapped]

private theorem signature_initial_returns (bindings : Subst) (state : Effects.State) (types : List (Atom × Bool × List Nat))
    (typesCaptured : applySubst bindings (.var "arguments") = .expression (typeValues types)) :
    PureReturns program bindings state
      (.expression [.symbol "mm0:mmb:unify-initial",.expression [.symbol "size-atom",.var "arguments"]]) state
      (decodingValue (Statements.initial types.length) types.length) := by
  apply call_returns program bindings state state "mm0:mmb:unify-initial" _ _ (by decide +kernel) _ (by decide)
  apply evaluated_argument_returns program bindings state state state (.function "mm0:mmb:unify-initial")
    (.expression [.symbol "size-atom",.var "arguments"]) (natural types.length) _ _ [] 0 (by decide +kernel)
  · apply native_unary_call_returns program bindings state state state "size-atom" (.var "arguments")
      (.expression (typeValues types)) (natural types.length) (by decide) (by decide) (by decide +kernel) _ _ (by decide)
    · simpa [typesCaptured] using variable_returns program bindings state "arguments"
    · simp [natural,typeValues]
  · exact authored_function_arguments_return program bindings (initialEnvironment types.length) state state
      "mm0:mmb:unify-initial" [natural types.length] 1 initialEquation.body _
      (by decide +kernel) (by decide) (initial_clause types.length)
      (by simpa only [decodingValue,decodingSlots_initial,
        show (Statements.initial types.length).dummies = [] from rfl,List.map_nil]
          using initial_body_returns state types.length)

private theorem signature_fuel_returns (bindings : Subst) (state : Effects.State) (codes : List Atom)
    (codesCaptured : applySubst bindings (.var "codes") = .expression codes) :
    PureReturns program bindings state
      (.expression [.symbol "+",.expression [.symbol "*",natural 2,
        .expression [.symbol "size-atom",.var "codes"]],natural 2]) state (natural (2*codes.length+2)) := by
  apply native_binary_call_returns program bindings state state state state "+" _ (natural 2)
    (natural (2*codes.length)) (natural 2) _
    (by decide) (by decide) (by decide +kernel) (by decide +kernel) _ _ _ (by decide)
  · apply native_binary_call_returns program bindings state state state state "*" (natural 2) _
      (natural 2) (natural codes.length) (natural (2*codes.length))
      (by decide) (by decide) (by decide +kernel) (by decide +kernel) _ _ _ (by decide)
    · exact grounded_returns program bindings state (.int 2)
    · apply native_unary_call_returns program bindings state state state "size-atom" (.var "codes")
        (.expression codes) (natural codes.length) (by decide) (by decide) (by decide +kernel) _ _ (by decide)
      · simpa [codesCaptured] using variable_returns program bindings state "codes"
      · simp [natural]
    · simp [natural]
  · exact grounded_returns program bindings state (.int 2)
  · simp [natural]

private theorem signature_prepare_returns (state : Effects.State) (published : Atom)
    (sorts terms theorems : List MMUResolution.Binding) (nextSort nextTerm nextTheorem : Nat) (images : Atom)
    (tables : Atom) (types : List (Atom × Bool × List Nat)) (codes : List Atom) (ending contextAnswer answer : Atom)
    (computed : contextResult sorts types 0 [] [] = contextAnswer)
    (continued : PureReturns program
      (("fuel",natural (2*codes.length+2)) ::
        ("initial",decodingValue (Statements.initial types.length) types.length) ::
        ("context",contextAnswer) ::
        signatureEnvironment (resolverValue published sorts terms theorems nextSort nextTerm nextTheorem images)
          tables types codes ending)
      state (.expression [.symbol "case",.var "context",
        .expression (signatureCases.map fun row => .expression [row.1,row.2])]) state answer) :
    PureReturns program
      (signatureEnvironment (resolverValue published sorts terms theorems nextSort nextTerm nextTheorem images)
        tables types codes ending) state signatureEquation.body state answer := by
  let bound := signatureEnvironment (resolverValue published sorts terms theorems nextSort nextTerm nextTheorem images)
    tables types codes ending
  let contextChecked := ("context",contextAnswer) :: bound
  let initialized := ("initial",decodingValue (Statements.initial types.length) types.length) :: contextChecked
  let fueled := ("fuel",natural (2*codes.length+2)) :: initialized
  rw [signature_shape]
  apply let_star_returns program bound state state _ _ _ _ rfl
  apply let_returns program bound contextChecked state state state (.var "context") _ _ contextAnswer _
  · simpa only [computed] using signature_context_returns bound state published sorts terms theorems
      nextSort nextTerm nextTheorem images types rfl rfl
  · simp [SpaceSemantics.matchValue,matchAtom,Subst.lookup,contextChecked,bound,signatureEnvironment]
  · apply let_returns program contextChecked initialized state state state (.var "initial") _ _
      (decodingValue (Statements.initial types.length) types.length) _
    · exact signature_initial_returns contextChecked state types rfl
    · simp [SpaceSemantics.matchValue,matchAtom,Subst.lookup,initialized,contextChecked,bound,signatureEnvironment]
    · apply let_returns program initialized fueled state state state (.var "fuel") _ _
        (natural (2*codes.length+2)) _
      · exact signature_fuel_returns initialized state codes rfl
      · simp [SpaceSemantics.matchValue,matchAtom,Subst.lookup,fueled,initialized,contextChecked,bound,signatureEnvironment]
      · exact continued

private theorem signature_success_body_returns (state : Effects.State) (published : Atom)
    (sorts terms theorems : List MMUResolution.Binding) (nextSort nextTerm nextTheorem : Nat) (images : Atom)
    (tableSorts tableTheorems : Atom) (entries : List Atom) (types : List (Atom × Bool × List Nat))
    (commands remaining : List Formats.MMB.UnifyCmd) (rawCommands : List Atom) (ending : Atom)
    (context bound : List Atom) (conclusion : Kernel.Preterm) (after : Statements.Decoding)
    (hypotheses : List Kernel.Preterm) (encoded : List.Forall₂ CommandImage commands rawCommands)
    (contextChecked : contextWalk sorts types 0 [] [] = some (context,bound))
    (decoded : Statements.decodeExpr (tableArity entries) types.length (2*rawCommands.length+2)
      (Statements.initial types.length) commands (resolvedIds terms) (resolvedIds sorts) =
      some (conclusion,after,remaining))
    (noDummies : after.dummies = [])
    (decodedHypotheses : Statements.decodeHyps (tableArity entries) types.length (2*rawCommands.length+2)
      after remaining (resolvedIds terms) (resolvedIds sorts) = some hypotheses) :
    PureReturns program
      (signatureEnvironment (resolverValue published sorts terms theorems nextSort nextTerm nextTheorem images)
        (tablesValue tableSorts (listValue entries) tableTheorems) types rawCommands ending)
      state signatureEquation.body state
      (optionValue (some (listValue [.symbol "MM0:Theorem",listValue context,
        listValue (hypotheses.map Data.preterm),Data.preterm conclusion]))) := by
  let resolver := resolverValue published sorts terms theorems nextSort nextTerm nextTheorem images
  let tables := tablesValue tableSorts (listValue entries) tableTheorems
  let fuel := 2*rawCommands.length+2
  let before := signatureEnvironment resolver tables types rawCommands ending
  let prepared := ("fuel",natural fuel) ::
    ("initial",decodingValue (Statements.initial types.length) types.length) ::
    ("context",optionValue (some (contextValue context bound))) :: before
  let selected := ("bound",listValue bound) :: ("ctx",listValue context) :: prepared
  obtain ⟨rawRemaining,remainingImages,_,conclusionBody⟩ :=
    (decoded_bodies state published sorts terms theorems nextSort nextTerm nextTheorem images
      tableSorts tableTheorems entries types.length fuel).1 (Statements.initial types.length) after commands remaining
      rawCommands conclusion encoded decoded
  let decodedEnv := ("rest",listValue rawRemaining) :: ("arity",natural types.length) ::
    ("slots",listValue (decodingSlots after)) :: ("conclusion",Data.preterm conclusion) :: selected
  let finished := ("hyps",listValue (hypotheses.map Data.preterm)) :: decodedEnv
  apply signature_prepare_returns state published sorts terms theorems nextSort nextTerm nextTheorem images
    tables types rawCommands ending (optionValue (some (contextValue context bound))) _
    (by simp [contextResult,contextChecked])
  apply case_returns program prepared selected state state state (.var "context")
    (optionValue (some (contextValue context bound))) signatureFound _ _ signatureCases (read_cases_encoded signatureCases)
  · exact variable_returns program prepared state "context"
  · simp [signature_cases,SpaceSemantics.selectCase,SpaceSemantics.matchValue,
      SpaceSemantics.matchValue.matchValues,matchAtom,Subst.lookup,selected,prepared,before,
      signatureEnvironment,optionValue,contextValue,listValue]
  · rw [signature_found_shape]
    apply case_returns program selected decodedEnv state state state _
      (optionValue (some (unifyExpressionValue (Data.preterm conclusion) (decodingSlots after) [] types.length rawRemaining)))
      signatureConclusionFound _ _ signatureConclusionCases (read_cases_encoded signatureConclusionCases)
    · apply expression_call_from_body selected state resolver tableSorts (listValue entries) tableTheorems
        fuel (decodingSlots (Statements.initial types.length)) [] types.length rawCommands _
        (.var "state") (.var "tables") (.var "fuel") (.var "initial") (.expression [.symbol "MM0:L",.var "codes"])
      · rfl
      · rfl
      · exact variable_returns program selected state "fuel"
      · simp [selected,prepared,decodingValue,Statements.initial,applySubst,Subst.lookup,unifyStateValue]
      · simp [selected,prepared,before,signatureEnvironment,applySubst,applySubst.applySubstList,Subst.lookup,listValue]
      · simpa only [noDummies,List.map_nil,resolver,
          show (Statements.initial types.length).dummies = [] from rfl] using conclusionBody
    · simp [signature_conclusion_cases,SpaceSemantics.selectCase,SpaceSemantics.matchValue,
        SpaceSemantics.matchValue.matchValues,matchAtom,Subst.lookup,decodedEnv,selected,prepared,before,
        signatureEnvironment,optionValue,unifyExpressionValue,unifyStateValue,listValue]
    · rw [signature_conclusion_found_shape]
      apply case_returns program decodedEnv finished state state state _
        (optionValue (some (listValue (hypotheses.map Data.preterm)))) signatureHypothesesFound _ _
        signatureHypothesesCases (read_cases_encoded signatureHypothesesCases)
      · apply hypotheses_call_from_body decodedEnv state resolver tables fuel (decodingValue after types.length)
          rawRemaining _ (.var "state") (.var "tables") (.var "fuel")
          (.expression [.symbol "MM0:MMBUState",.var "slots",.expression [.symbol "MM0:L",.expression []],.var "arity"])
          (.var "rest")
        · rfl
        · rfl
        · exact variable_returns program decodedEnv state "fuel"
        · simp [decodedEnv,decodingValue,noDummies,unifyStateValue,applySubst,applySubst.applySubstList,Subst.lookup,listValue]
        · rfl
        · exact hypotheses_decoded_body_returns state published sorts terms theorems nextSort nextTerm nextTheorem images
            tableSorts tableTheorems entries types.length fuel after remaining rawRemaining hypotheses remainingImages decodedHypotheses
      · simp [signature_hypotheses_cases,SpaceSemantics.selectCase,SpaceSemantics.matchValue,
          SpaceSemantics.matchValue.matchValues,matchAtom,Subst.lookup,finished,decodedEnv,selected,
          prepared,before,signatureEnvironment,optionValue]
      · rw [signature_hypotheses_found_shape]
        apply unary_constructor_of_returns program finished state state "Some" _ _ (by decide +kernel) (by decide)
        apply unary_constructor_of_returns program finished state state "MM0:L" _ _ (by decide +kernel) (by decide)
        simpa [finished,decodedEnv,selected,applySubst,Subst.lookup,listValue] using
          constructor_variables_return program finished state "MM0:Theorem" ["ctx","hyps","conclusion"]
            (by decide +kernel) (by decide)

/-- Successful independent context, conclusion and hypothesis decoding is
realized by the whole original theorem-signature entry operation. Its fuel is
computed from the physical code count; initialization and every child guard
are executed by the source. This constructs a declaration, not a checked proof. -/
theorem theorem_signature_decoded_returns (bindings : Subst) (state : Effects.State) (published : Atom)
    (sorts terms theorems : List MMUResolution.Binding) (nextSort nextTerm nextTheorem : Nat) (images : Atom)
    (tableSorts tableTheorems : Atom) (entries : List Atom) (arguments : List ExprType)
    (commands remaining : List Formats.MMB.UnifyCmd) (rawCommands : List Atom) (ending : Atom)
    (context : Kernel.Context) (conclusion : Kernel.Preterm) (after : Statements.Decoding)
    (hypotheses : List Kernel.Preterm) (encoded : List.Forall₂ CommandImage commands rawCommands)
    (numerical : NumericalMap sorts) (valid : PrefixValid arguments)
    (contextChecked : Kernel.Context.relocateSorts? (resolvedIds sorts) (Statements.context arguments) = some context)
    (decoded : Statements.decodeExpr (tableArity entries) arguments.length (2*commands.length+2)
      (Statements.initial arguments.length) commands (resolvedIds terms) (resolvedIds sorts) = some (conclusion,after,remaining))
    (noDummies : after.dummies = [])
    (decodedHypotheses : Statements.decodeHyps (tableArity entries) arguments.length (2*commands.length+2)
      after remaining (resolvedIds terms) (resolvedIds sorts) = some hypotheses)
    (resolverName tablesName declarationName : String)
    (resolverCaptured : applySubst bindings (.var resolverName) =
      resolverValue published sorts terms theorems nextSort nextTerm nextTheorem images)
    (tablesCaptured : applySubst bindings (.var tablesName) = tablesValue tableSorts (listValue entries) tableTheorems)
    (declarationCaptured : applySubst bindings (.var declarationName) =
      .expression [.symbol "MM0:MMBTheorem",listValue (typeValues (canonicalTypes arguments)),
        .expression [.symbol "MM0:MMBStream",listValue rawCommands,ending]]) :
    PureReturns program bindings state
      (.expression [.symbol "mm0:mmb:theorem-signature",.var resolverName,.var tablesName,.var declarationName]) state
      (optionValue (some (listValue [.symbol "MM0:Theorem",Data.context context,
        listValue (hypotheses.map Data.preterm),Data.preterm conclusion]))) := by
  have contextComputed : contextWalk sorts (canonicalTypes arguments) 0 [] [] =
      some (context.map Data.binder,(Statements.boundPositions arguments).map natural) := by
    rw [context_canonical sorts arguments numerical valid,contextChecked]
    rfl
  have sourceBody := signature_success_body_returns state published sorts terms theorems
    nextSort nextTerm nextTheorem images tableSorts tableTheorems entries (canonicalTypes arguments)
    commands remaining rawCommands ending (context.map Data.binder) ((Statements.boundPositions arguments).map natural)
    conclusion after hypotheses encoded contextComputed
    (by simpa only [canonicalTypes,List.length_map,← encoded.length_eq] using decoded)
    noDummies (by simpa only [canonicalTypes,List.length_map,← encoded.length_eq] using decodedHypotheses)
  apply authored_variable_call_returns program bindings
    (signatureEnvironment (resolverValue published sorts terms theorems nextSort nextTerm nextTheorem images)
      (tablesValue tableSorts (listValue entries) tableTheorems) (canonicalTypes arguments) rawCommands ending)
    state state "mm0:mmb:theorem-signature" [resolverName,tablesName,declarationName] signatureEquation.body _
    (by decide +kernel) (by decide +kernel) (by decide +kernel) _
    (by simpa only [Data.context] using sourceBody) (by decide)
  simpa [resolverCaptured,tablesCaptured,declarationCaptured] using
    signature_clause (resolverValue published sorts terms theorems nextSort nextTerm nextTheorem images)
      (tablesValue tableSorts (listValue entries) tableTheorems) (canonicalTypes arguments) rawCommands ending

private theorem signature_context_refused_body_returns (state : Effects.State) (published : Atom)
    (sorts terms theorems : List MMUResolution.Binding) (nextSort nextTerm nextTheorem : Nat) (images : Atom)
    (tables : Atom) (types : List (Atom × Bool × List Nat)) (codes : List Atom) (ending : Atom)
    (refused : contextWalk sorts types 0 [] [] = none) :
    PureReturns program
      (signatureEnvironment (resolverValue published sorts terms theorems nextSort nextTerm nextTheorem images)
        tables types codes ending) state signatureEquation.body state (.symbol "None") := by
  let prepared := ("fuel",natural (2*codes.length+2)) ::
    ("initial",decodingValue (Statements.initial types.length) types.length) :: ("context",.symbol "None") ::
    signatureEnvironment (resolverValue published sorts terms theorems nextSort nextTerm nextTheorem images)
      tables types codes ending
  apply signature_prepare_returns state published sorts terms theorems nextSort nextTerm nextTheorem images
    tables types codes ending (.symbol "None") (.symbol "None") (by simp [contextResult,refused,optionValue])
  apply case_returns program prepared (("bad",.symbol "None") :: prepared) state state state
    (.var "context") (.symbol "None") (.symbol "None") _ _ signatureCases (read_cases_encoded signatureCases)
  · exact variable_returns program prepared state "context"
  · simp [signature_cases,SpaceSemantics.selectCase,SpaceSemantics.matchValue,matchAtom,Subst.lookup,prepared,signatureEnvironment]
  · exact symbol_returns program _ state "None"

/-- Refusal of the original context phase is also realized by the whole entry
operation. The source still executes argument-slot initialization and computes
its code-derived fuel before selecting this refusal branch. Code payloads need
not be well-shaped because the expression phase is not entered. -/
theorem theorem_signature_context_refused_returns (bindings : Subst) (state : Effects.State) (published : Atom)
    (sorts terms theorems : List MMUResolution.Binding) (nextSort nextTerm nextTheorem : Nat) (images : Atom)
    (tables : Atom) (types : List (Atom × Bool × List Nat)) (codes : List Atom) (ending : Atom)
    (refused : contextWalk sorts types 0 [] [] = none)
    (resolverName tablesName declarationName : String)
    (resolverCaptured : applySubst bindings (.var resolverName) =
      resolverValue published sorts terms theorems nextSort nextTerm nextTheorem images)
    (tablesCaptured : applySubst bindings (.var tablesName) = tables)
    (declarationCaptured : applySubst bindings (.var declarationName) =
      .expression [.symbol "MM0:MMBTheorem",listValue (typeValues types),
        .expression [.symbol "MM0:MMBStream",listValue codes,ending]]) :
    PureReturns program bindings state
      (.expression [.symbol "mm0:mmb:theorem-signature",.var resolverName,.var tablesName,.var declarationName]) state
      (.symbol "None") := by
  apply authored_variable_call_returns program bindings
    (signatureEnvironment (resolverValue published sorts terms theorems nextSort nextTerm nextTheorem images)
      tables types codes ending)
    state state "mm0:mmb:theorem-signature" [resolverName,tablesName,declarationName] signatureEquation.body _
    (by decide +kernel) (by decide +kernel) (by decide +kernel) _
    (signature_context_refused_body_returns state published sorts terms theorems nextSort nextTerm nextTheorem images
      tables types codes ending refused) (by decide)
  simpa [resolverCaptured,tablesCaptured,declarationCaptured] using
    signature_clause (resolverValue published sorts terms theorems nextSort nextTerm nextTheorem images)
      tables types codes ending


private theorem signature_dummy_refused_body_returns (state : Effects.State) (published : Atom)
    (sorts terms theorems : List MMUResolution.Binding) (nextSort nextTerm nextTheorem : Nat) (images : Atom)
    (tableSorts tableTheorems : Atom) (entries : List Atom) (types : List (Atom × Bool × List Nat))
    (commands remaining : List Formats.MMB.UnifyCmd) (rawCommands : List Atom) (ending : Atom)
    (context bound : List Atom) (conclusion : Kernel.Preterm) (after : Statements.Decoding)
    (encoded : List.Forall₂ CommandImage commands rawCommands)
    (contextChecked : contextWalk sorts types 0 [] [] = some (context,bound))
    (decoded : Statements.decodeExpr (tableArity entries) types.length (2*rawCommands.length+2)
      (Statements.initial types.length) commands (resolvedIds terms) (resolvedIds sorts) =
      some (conclusion,after,remaining))
    (hasDummies : after.dummies ≠ []) :
    PureReturns program
      (signatureEnvironment (resolverValue published sorts terms theorems nextSort nextTerm nextTheorem images)
        (tablesValue tableSorts (listValue entries) tableTheorems) types rawCommands ending)
      state signatureEquation.body state (.symbol "None") := by
  let resolver := resolverValue published sorts terms theorems nextSort nextTerm nextTheorem images
  let tables := tablesValue tableSorts (listValue entries) tableTheorems
  let fuel := 2*rawCommands.length+2
  let before := signatureEnvironment resolver tables types rawCommands ending
  let prepared := ("fuel",natural fuel) ::
    ("initial",decodingValue (Statements.initial types.length) types.length) ::
    ("context",optionValue (some (contextValue context bound))) :: before
  let selected := ("bound",listValue bound) :: ("ctx",listValue context) :: prepared
  obtain ⟨rawRemaining,_,_,conclusionBody⟩ :=
    (decoded_bodies state published sorts terms theorems nextSort nextTerm nextTheorem images
      tableSorts tableTheorems entries types.length fuel).1 (Statements.initial types.length) after commands remaining
      rawCommands conclusion encoded decoded
  let observation := optionValue (some (unifyExpressionValue (Data.preterm conclusion)
    (decodingSlots after) (after.dummies.map natural) types.length rawRemaining))
  apply signature_prepare_returns state published sorts terms theorems nextSort nextTerm nextTheorem images
    tables types rawCommands ending (optionValue (some (contextValue context bound))) (.symbol "None")
    (by simp [contextResult,contextChecked])
  apply case_returns program prepared selected state state state (.var "context")
    (optionValue (some (contextValue context bound))) signatureFound _ _ signatureCases (read_cases_encoded signatureCases)
  · exact variable_returns program prepared state "context"
  · simp [signature_cases,SpaceSemantics.selectCase,SpaceSemantics.matchValue,
      SpaceSemantics.matchValue.matchValues,matchAtom,Subst.lookup,selected,prepared,before,
      signatureEnvironment,optionValue,contextValue,listValue]
  · rw [signature_found_shape]
    apply case_returns program selected (("bad",observation) :: selected) state state state _
      observation (.symbol "None") _ _ signatureConclusionCases (read_cases_encoded signatureConclusionCases)
    · apply expression_call_from_body selected state resolver tableSorts (listValue entries) tableTheorems
        fuel (decodingSlots (Statements.initial types.length)) [] types.length rawCommands _
        (.var "state") (.var "tables") (.var "fuel") (.var "initial") (.expression [.symbol "MM0:L",.var "codes"])
      · rfl
      · rfl
      · exact variable_returns program selected state "fuel"
      · simp [selected,prepared,decodingValue,Statements.initial,applySubst,Subst.lookup,unifyStateValue]
      · simp [selected,prepared,before,signatureEnvironment,applySubst,applySubst.applySubstList,Subst.lookup,listValue]
      · simpa only [resolver,show (Statements.initial types.length).dummies = [] from rfl,List.map_nil] using conclusionBody
    · cases dummies : after.dummies with
      | nil => exact (hasDummies dummies).elim
      | cons first rest =>
          simp [signature_conclusion_cases,SpaceSemantics.selectCase,SpaceSemantics.matchValue,
            SpaceSemantics.matchValue.matchValues,matchAtom,Subst.lookup,observation,dummies,selected,prepared,before,
            signatureEnvironment,optionValue,unifyExpressionValue,unifyStateValue,listValue]
    · exact symbol_returns program _ state "None"

/-- The whole original signature operation refuses a decoded conclusion with
fresh dummies, before entering the hypothesis phase. -/
theorem theorem_signature_dummy_refused_returns (bindings : Subst) (state : Effects.State) (published : Atom)
    (sorts terms theorems : List MMUResolution.Binding) (nextSort nextTerm nextTheorem : Nat) (images : Atom)
    (tableSorts tableTheorems : Atom) (entries : List Atom) (arguments : List ExprType)
    (commands remaining : List Formats.MMB.UnifyCmd) (rawCommands : List Atom) (ending : Atom)
    (context : Kernel.Context) (conclusion : Kernel.Preterm) (after : Statements.Decoding)
    (encoded : List.Forall₂ CommandImage commands rawCommands)
    (numerical : NumericalMap sorts) (valid : PrefixValid arguments)
    (contextChecked : Kernel.Context.relocateSorts? (resolvedIds sorts) (Statements.context arguments) = some context)
    (decoded : Statements.decodeExpr (tableArity entries) arguments.length (2*commands.length+2)
      (Statements.initial arguments.length) commands (resolvedIds terms) (resolvedIds sorts) = some (conclusion,after,remaining))
    (hasDummies : after.dummies ≠ [])
    (resolverName tablesName declarationName : String)
    (resolverCaptured : applySubst bindings (.var resolverName) =
      resolverValue published sorts terms theorems nextSort nextTerm nextTheorem images)
    (tablesCaptured : applySubst bindings (.var tablesName) = tablesValue tableSorts (listValue entries) tableTheorems)
    (declarationCaptured : applySubst bindings (.var declarationName) =
      .expression [.symbol "MM0:MMBTheorem",listValue (typeValues (canonicalTypes arguments)),
        .expression [.symbol "MM0:MMBStream",listValue rawCommands,ending]]) :
    PureReturns program bindings state
      (.expression [.symbol "mm0:mmb:theorem-signature",.var resolverName,.var tablesName,.var declarationName]) state
      (.symbol "None") := by
  have contextComputed : contextWalk sorts (canonicalTypes arguments) 0 [] [] =
      some (context.map Data.binder,(Statements.boundPositions arguments).map natural) := by
    rw [context_canonical sorts arguments numerical valid,contextChecked]
    rfl
  have sourceBody := signature_dummy_refused_body_returns state published sorts terms theorems
    nextSort nextTerm nextTheorem images tableSorts tableTheorems entries (canonicalTypes arguments)
    commands remaining rawCommands ending (context.map Data.binder) ((Statements.boundPositions arguments).map natural)
    conclusion after encoded contextComputed
    (by simpa only [canonicalTypes,List.length_map,← encoded.length_eq] using decoded) hasDummies
  apply authored_variable_call_returns program bindings
    (signatureEnvironment (resolverValue published sorts terms theorems nextSort nextTerm nextTheorem images)
      (tablesValue tableSorts (listValue entries) tableTheorems) (canonicalTypes arguments) rawCommands ending)
    state state "mm0:mmb:theorem-signature" [resolverName,tablesName,declarationName] signatureEquation.body _
    (by decide +kernel) (by decide +kernel) (by decide +kernel) _ sourceBody (by decide)
  simpa [resolverCaptured,tablesCaptured,declarationCaptured] using
    signature_clause (resolverValue published sorts terms theorems nextSort nextTerm nextTheorem images)
      (tablesValue tableSorts (listValue entries) tableTheorems) (canonicalTypes arguments) rawCommands ending

end Mettapedia.Languages.MM0.MeTTa.MMBTheoremSignatureExecution
