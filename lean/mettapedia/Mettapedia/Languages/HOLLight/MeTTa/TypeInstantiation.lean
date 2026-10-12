import Mettapedia.Languages.HOLLight.MeTTa.TermInstantiation
import Mettapedia.Languages.HOLLight.MeTTa.TypeMapletValidation
import Mettapedia.Languages.HOLLight.MeTTa.InferenceExecution

/-!
# Executed theorem type instantiation

The source traverses its hypothesis occurrences, instantiates each checked
term and performs its actual insertion operation. Type substitution can make
distinct hypotheses equal; the retained result follows that operation while
its logical support is the shared calculus's extensional hypothesis image.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.HOLLight.MeTTa.TypeInstantiation

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst matchAtom)
open Mettapedia.Languages.MeTTa.PeTTa
open Mettapedia.Languages.OpenTheory
open SourceSubstitution (typeOnlySubstitution)
open Eval
open Effects (State boolean)
open Representation (registeredOperatorAtom termAtom)
open TypeSubstitution (typeAtom maplets)

namespace Hypotheses

def imageOccurrences (constants : Const → Atom) (entries : List (Ty × Ty)) : List CanonicalTerm → List Atom
  | [] => []
  | first :: rest =>
      let value := TheoremMetadata.hypothesisAtom constants ((typeOnlySubstitution entries).apply first)
      let tail := imageOccurrences constants entries rest
      if value ∈ tail then tail else value :: tail

private theorem insert_support (item : Atom) (items : List Atom) :
    (if item ∈ items then items else item :: items).toFinset = insert item items.toFinset := by
  by_cases member : item ∈ items
  · simp [member, Finset.insert_eq_of_mem (List.mem_toFinset.mpr member)]
  · simp [member]

/-- The actual source occurrence list has exactly the support of the shared
substituted hypotheses. This law does not reconstruct order from support. -/
theorem image_support (constants : Const → Atom) (entries : List (Ty × Ty)) (items : List CanonicalTerm) :
    (imageOccurrences constants entries items).toFinset =
      ((typeOnlySubstitution entries).applyHypotheses items.toFinset).image (TheoremMetadata.hypothesisAtom constants) := by
  induction items with
  | nil => simp [imageOccurrences, TypeCorrectTermSubstitution.applyHypotheses]
  | cons first rest ih =>
      simp only [imageOccurrences]
      rw [insert_support, ih]
      simp only [List.toFinset_cons, TypeCorrectTermSubstitution.applyHypotheses, Finset.image_insert]

private def equation : SpaceSemantics.Equation :=
  (syntaxSource.program.equations.filter (fun row => row.head == "hol-light:inst-types"))[0]'(by decide)
private def consBody : Atom := .expression [.symbol "hol-light:insert",
  .expression [.symbol "hol-light:term-inst-type", .var "entries", .var "first"],
  .expression [.symbol "hol-light:inst-types", .var "entries", .var "rest"]]
private def cases : SpaceSemantics.Cases :=
  [(.symbol "HOL:Nil", .symbol "HOL:Nil"),
   (.expression [.symbol "HOL:Cons", .var "first", .var "rest"], consBody), (.var "malformed", .symbol "None")]
private def environment (constants : Const → Atom) (entries : List (Ty × Ty)) (items : List CanonicalTerm) : Subst :=
  [("terms", Premises.keys (items.map (TheoremMetadata.hypothesisAtom constants))),
   ("entries", maplets registeredOperatorAtom entries)]
private theorem shape : equation.body = .expression [.symbol "case", .var "terms",
    .expression (cases.map fun row => .expression [row.1, row.2])] := by decide
private theorem clause (constants : Const → Atom) (entries : List (Ty × Ty)) (items : List CanonicalTerm) :
    clauses program "hol-light:inst-types" [maplets registeredOperatorAtom entries,
      Premises.keys (items.map (TheoremMetadata.hypothesisAtom constants))] =
      [.evaluate (environment constants entries items) equation.body] := by
  rw [clauses_use_only_the_named_equations]
  have unique : program.equations.filter (fun row => row.head == "hol-light:inst-types") = [equation] := by rfl
  rw [unique]
  have formals : equation.arguments = [.var "entries", .var "terms"] := by decide
  simp [formals, environment, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]

private theorem body_returns (constants : Const → Atom) (entries : List (Ty × Ty)) (items : List CanonicalTerm) (state : State) :
    PureReturns program (environment constants entries items) state equation.body state
      (Premises.keys (imageOccurrences constants entries items)) := by
  induction items with
  | nil =>
      let before := environment constants entries []
      rw [shape]
      apply case_returns program before before state state state (.var "terms") (.symbol "HOL:Nil") (.symbol "HOL:Nil")
        _ _ cases (read_cases_encoded cases)
      · simpa [before, environment, Premises.keys, applySubst, Subst.lookup] using variable_returns program before state "terms"
      · simp [cases, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
      · exact symbol_returns program before state "HOL:Nil"
  | cons first rest ih =>
      let before := environment constants entries (first :: rest)
      let bound := [("rest", Premises.keys (rest.map (TheoremMetadata.hypothesisAtom constants))),
        ("first", TheoremMetadata.hypothesisAtom constants first)] ++ before
      rw [shape]
      apply case_returns program before bound state state state (.var "terms")
        (Premises.keys ((first :: rest).map (TheoremMetadata.hypothesisAtom constants))) consBody _ _ cases
        (read_cases_encoded cases)
      · simpa [before, environment, applySubst, Subst.lookup] using variable_returns program before state "terms"
      · simp [cases, Premises.keys, bound, before, environment, SpaceSemantics.selectCase,
          SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]
      · unfold consBody
        apply ListOperations.Insertion.authored_insert_computed_return bound state
          (TheoremMetadata.hypothesisAtom constants ((typeOnlySubstitution entries).apply first))
          (imageOccurrences constants entries rest)
        · simpa only [TheoremMetadata.hypothesisAtom, TypeCorrectTermSubstitution.apply, TermSubst.applyChecked,
            List.map_nil] using
            TermInstantiation.authored_type_instantiation_return registeredOperatorAtom constants bound state entries []
              first.term first.ty first.checked "entries" "first"
              (by simp [bound, before, environment, applySubst, Subst.lookup])
              (by simp [bound, TheoremMetadata.hypothesisAtom, applySubst, Subst.lookup])
        · apply authored_variable_call_returns program bound (environment constants entries rest)
            state state "hol-light:inst-types" ["entries", "rest"] equation.body _
            (by decide) (by decide) (by decide) _ ih (by decide)
          simpa [bound, before, environment, applySubst, Subst.lookup] using clause constants entries rest

/-- The traversal executes its actual term instantiations and insertion
comparisons, retaining precisely the source's hypothesis occurrence result. -/
theorem authored_hypotheses_return (constants : Const → Atom) (entries : List (Ty × Ty))
    (items : List CanonicalTerm) (bindings : Subst) (state : State) (entriesKey itemsKey : String)
    (entriesCaptured : applySubst bindings (.var entriesKey) = maplets registeredOperatorAtom entries)
    (itemsCaptured : applySubst bindings (.var itemsKey) = Premises.keys (items.map (TheoremMetadata.hypothesisAtom constants))) :
    PureReturns program bindings state (.expression [.symbol "hol-light:inst-types", .var entriesKey, .var itemsKey]) state
      (Premises.keys (imageOccurrences constants entries items)) := by
  apply authored_variable_call_returns program bindings (environment constants entries items) state state
    "hol-light:inst-types" [entriesKey, itemsKey] equation.body _ (by decide) (by decide) (by decide) _
    (body_returns constants entries items state) (by decide)
  simpa only [List.map_cons, List.map_nil, entriesCaptured, itemsCaptured] using clause constants entries items

end Hypotheses

namespace Primitive

def result (constants : Const → Atom) (entries : List (Ty × Ty)) (hypotheses : List CanonicalTerm)
    (conclusion : CanonicalTerm) (dependencies : List Atom) : Atom :=
  .expression [.symbol "Some", Representation.theoremAtom constants []
    ((typeOnlySubstitution entries).apply conclusion).term
    (Hypotheses.imageOccurrences constants entries hypotheses) dependencies (.symbol "INST_TYPE")]

private def equation : SpaceSemantics.Equation :=
  (kernelSource.program.equations.filter (fun row => row.head == "hol-light:inst-type"))[0]'(by decide)
private def selected : Atom := .expression [.symbol "Some", .expression [.symbol "HOL:Thm",
  .expression [.symbol "hol-light:inst-types", .var "entries", .var "hyps"],
  .expression [.symbol "hol-light:term-inst-type", .var "entries", .var "conclusion"],
  .var "dependencies", .symbol "INST_TYPE"]]
private def cases : SpaceSemantics.Cases :=
  [(.expression [.symbol "Some", .expression [.symbol "HOL:Thm", .var "hyps", .var "conclusion",
      .var "dependencies", .var "origin"]], selected), (.var "malformed", .symbol "None")]
private def environment (entries premise : Atom) : Subst := [("premise", premise), ("entries", entries)]
private theorem shape : equation.body = .expression [.symbol "case", .var "premise",
    .expression (cases.map fun row => .expression [row.1, row.2])] := by decide
private theorem clause (entries premise : Atom) : clauses program "hol-light:inst-type" [entries, premise] =
    [.evaluate (environment entries premise) equation.body] := by
  rw [clauses_use_only_the_named_equations]
  have unique : program.equations.filter (fun row => row.head == "hol-light:inst-type") = [equation] := by rfl
  rw [unique]
  have formals : equation.arguments = [.var "entries", .var "premise"] := by decide
  simp [formals, environment, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]

private theorem body_returns (constants : Const → Atom) (entries : List (Ty × Ty))
    (hypotheses : List CanonicalTerm) (conclusion : CanonicalTerm) (dependencies : List Atom)
    (origin : Atom) (state : State) :
    PureReturns program (environment (maplets registeredOperatorAtom entries)
      (.expression [.symbol "Some", Representation.theoremAtom constants [] conclusion.term
        (hypotheses.map (TheoremMetadata.hypothesisAtom constants)) dependencies origin]))
      state equation.body state (result constants entries hypotheses conclusion dependencies) := by
  let premise := Atom.expression [.symbol "Some", Representation.theoremAtom constants [] conclusion.term
    (hypotheses.map (TheoremMetadata.hypothesisAtom constants)) dependencies origin]
  let before := environment (maplets registeredOperatorAtom entries) premise
  let bound := [("origin", origin), ("dependencies", Premises.keys dependencies),
    ("conclusion", termAtom registeredOperatorAtom constants [] conclusion.term),
    ("hyps", Premises.keys (hypotheses.map (TheoremMetadata.hypothesisAtom constants)))] ++ before
  rw [shape]
  apply case_returns program before bound state state state (.var "premise") premise selected _ _ cases
    (read_cases_encoded cases)
  · exact variable_returns program before state "premise"
  · simp [premise, before, environment, bound, cases, Representation.theoremAtom, SpaceSemantics.selectCase,
      SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]
  · unfold selected result
    apply unary_constructor_of_returns program bound state state "Some" _ _ (by decide) (by decide)
    apply PureData.constructor_return program bound state "HOL:Thm" _ _ (by decide) (by decide)
    refine .cons ?_ (.cons ?_ (.cons ?_ (.cons ?_ .nil)))
    · exact Hypotheses.authored_hypotheses_return constants entries hypotheses bound state "entries" "hyps"
        (by simp [bound, before, environment, applySubst, Subst.lookup])
        (by simp [bound, applySubst, Subst.lookup])
    · simpa only [TypeCorrectTermSubstitution.apply, TermSubst.applyChecked, List.map_nil] using
        TermInstantiation.authored_type_instantiation_return registeredOperatorAtom constants bound state entries []
          conclusion.term conclusion.ty conclusion.checked "entries" "conclusion"
          (by simp [bound, before, environment, applySubst, Subst.lookup])
          (by simp [bound, applySubst, Subst.lookup])
    · simpa [bound, applySubst, Subst.lookup] using variable_returns program bound state "dependencies"
    · exact symbol_returns program bound state "INST_TYPE"

/-- The actual helper applies the shared substitution to the current sequent
and retains its input dependency occurrences. Admission of maplets and of
the cached premise is handled by the surrounding inference dispatcher. -/
theorem authored_inst_type_computed_return (constants : Const → Atom) (entries : List (Ty × Ty))
    (hypotheses : List CanonicalTerm) (conclusion : CanonicalTerm) (dependencies : List Atom) (origin : Atom)
    (bindings : Subst) (state : State) (entriesExpression premiseExpression : Atom)
    (entriesReturned : PureReturns program bindings state entriesExpression state (maplets registeredOperatorAtom entries))
    (premiseReturned : PureReturns program bindings state premiseExpression state
      (.expression [.symbol "Some", Representation.theoremAtom constants [] conclusion.term
        (hypotheses.map (TheoremMetadata.hypothesisAtom constants)) dependencies origin])) :
    PureReturns program bindings state (.expression [.symbol "hol-light:inst-type", entriesExpression, premiseExpression]) state
      (result constants entries hypotheses conclusion dependencies) :=
  authored_binary_call_returns program bindings
    (environment (maplets registeredOperatorAtom entries)
      (.expression [.symbol "Some", Representation.theoremAtom constants [] conclusion.term
        (hypotheses.map (TheoremMetadata.hypothesisAtom constants)) dependencies origin]))
    state state state state "hol-light:inst-type" entriesExpression premiseExpression _ _ equation.body _
    (by decide) (by decide) (by decide) (by decide) (by decide) entriesReturned premiseReturned
    (clause _ _) (body_returns constants entries hypotheses conclusion dependencies origin state) (by decide)

end Primitive

namespace Dispatcher

private def equation : SpaceSemantics.Equation :=
  (kernelSource.program.equations.filter (fun row => row.head == "hol-light:infer"))[0]'(by decide)
private def cases : SpaceSemantics.Cases :=
  match equation.body with
  | .expression [_, _, .expression rows] => (readCases rows).getD []
  | _ => []
private def selected : Atom := .expression [.symbol "if",
  .expression [.symbol "hol-light:type-maplets-valid", .var "state", .var "entries"],
  .expression [.symbol "hol-light:inst-type", .var "entries",
    .expression [.symbol "hol-light:known", .var "state", .var "premise"]], .symbol "None"]
private def environment (source request : Atom) : Subst := [("request", request), ("state", source)]
private theorem shape : equation.body = .expression [.symbol "case", .var "request",
    .expression (cases.map fun row => .expression [row.1, row.2])] := by decide
private theorem clause (source request : Atom) : clauses program "hol-light:infer" [source, request] =
    [.evaluate (environment source request) equation.body] := by
  rw [clauses_use_only_the_named_equations]
  have unique : program.equations.filter (fun row => row.head == "hol-light:infer") = [equation] := by rfl
  rw [unique]
  have formals : equation.arguments = [.var "state", .var "request"] := by decide
  simp [formals, environment, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]
private theorem selection (source entries premise : Atom) :
    SpaceSemantics.selectCase (environment source (.expression [.symbol "INST_TYPE", entries, premise]))
      (.expression [.symbol "INST_TYPE", entries, premise]) cases =
      some ([("premise", premise), ("entries", entries)] ++
        environment source (.expression [.symbol "INST_TYPE", entries, premise]), selected) := by
  have patterns : cases = [
      (.expression [.symbol "REFL", .var "term"], (cases[0]'(by decide)).2),
      (.expression [.symbol "TRANS", .var "first", .var "second"], (cases[1]'(by decide)).2),
      (.expression [.symbol "MK_COMB", .var "first", .var "second"], (cases[2]'(by decide)).2),
      (.expression [.symbol "ABS", .var "variable", .var "premise"], (cases[3]'(by decide)).2),
      (.expression [.symbol "BETA", .var "term"], (cases[4]'(by decide)).2),
      (.expression [.symbol "ASSUME", .var "term"], (cases[5]'(by decide)).2),
      (.expression [.symbol "EQ_MP", .var "first", .var "second"], (cases[6]'(by decide)).2),
      (.expression [.symbol "DEDUCT_ANTISYM_RULE", .var "first", .var "second"], (cases[7]'(by decide)).2),
      (.expression [.symbol "INST", .var "entries", .var "premise"], (cases[8]'(by decide)).2),
      (.expression [.symbol "INST_TYPE", .var "entries", .var "premise"], selected),
      (.var "unsupported", .symbol "None")] := by decide
  rw [patterns]
  simp [environment, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
    SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]

private theorem captured_dispatch_return (bindings : Subst) (state : State) (source entries key answer : Atom)
    (stateKey requestKey : String)
    (stateCaptured : applySubst bindings (.var stateKey) = source)
    (requestCaptured : applySubst bindings (.var requestKey) = .expression [.symbol "INST_TYPE", entries, key])
    (returned : PureReturns program ([("premise", key), ("entries", entries)] ++
      environment source (.expression [.symbol "INST_TYPE", entries, key])) state selected state answer) :
    PureReturns program bindings state (.expression [.symbol "hol-light:infer", .var stateKey, .var requestKey]) state answer := by
  let request := Atom.expression [.symbol "INST_TYPE", entries, key]
  let before := environment source request
  let bound := [("premise", key), ("entries", entries)] ++ before
  apply authored_variable_call_returns program bindings before state state "hol-light:infer" [stateKey, requestKey]
    equation.body _ (by decide) (by decide) (by decide) _ _ (by decide)
  · simpa only [List.map_cons, List.map_nil, stateCaptured, requestCaptured] using clause source request
  · rw [shape]
    apply case_returns program before bound state state state (.var "request") request selected _ _ cases
      (read_cases_encoded cases)
    · exact variable_returns program before state "request"
    · exact selection source entries key
    · exact returned

/-- The source dispatcher checks both maplet components in its signature
before obtaining the actual cached premise and substituting the sequent.
Resolved types of incorrect arity yield the source refusal. -/
theorem authored_infer_inst_type_return (world : DefinitionAdapters.TheoryContext)
    (table : DeclarationTable.Table world) (origins : TypeOp → Atom) (constants : Const → Atom)
    (entries : List (Ty × Ty))
    (resolved : ∀ entry ∈ entries, TypeFormation.Resolved world.signature entry.1 ∧
      TypeFormation.Resolved world.signature entry.2)
    (hypotheses : List CanonicalTerm) (conclusion : CanonicalTerm) (dependencies : List Atom)
    (origin axioms receipts key : Atom) (cache : List (Atom × Atom))
    (found : cache.lookup key = some (Representation.theoremAtom constants [] conclusion.term
      (hypotheses.map (TheoremMetadata.hypothesisAtom constants)) dependencies origin))
    (bindings : Subst) (state : State) (stateKey requestKey : String)
    (stateCaptured : applySubst bindings (.var stateKey) = ProofLookup.sourceState
      (OperatorTable.tableAtom table.operators origins) (DeclarationTable.tableAtom table constants) axioms receipts cache)
    (requestCaptured : applySubst bindings (.var requestKey) =
      .expression [.symbol "INST_TYPE", maplets registeredOperatorAtom entries, key]) :
    PureReturns program bindings state (.expression [.symbol "hol-light:infer", .var stateKey, .var requestKey]) state
      (if TypeMapletValidation.admittedB world.signature entries then
        Primitive.result constants entries hypotheses conclusion dependencies else .symbol "None") := by
  let source := ProofLookup.sourceState (OperatorTable.tableAtom table.operators origins)
    (DeclarationTable.tableAtom table constants) axioms receipts cache
  let request := Atom.expression [.symbol "INST_TYPE", maplets registeredOperatorAtom entries, key]
  let before := environment source request
  let bound := [("premise", key), ("entries", maplets registeredOperatorAtom entries)] ++ before
  have validated := TypeMapletValidation.authored_type_maplets_valid_return world table.operators origins
    (DeclarationTable.tableAtom table constants) axioms receipts cache entries resolved bound state "state" "entries"
    (by simp [bound, before, environment, source, applySubst, Subst.lookup])
    (by simp [bound, applySubst, Subst.lookup])
  apply authored_variable_call_returns program bindings before state state "hol-light:infer" [stateKey, requestKey]
    equation.body _ (by decide) (by decide) (by decide) _ _ (by decide)
  · simpa only [List.map_cons, List.map_nil, stateCaptured, requestCaptured] using clause source request
  · rw [shape]
    apply case_returns program before bound state state state (.var "request") request selected _ _ cases
      (read_cases_encoded cases)
    · exact variable_returns program before state "request"
    · exact selection source (maplets registeredOperatorAtom entries) key
    · unfold selected
      apply if_returns program bound state state state _
        (boolean (TypeMapletValidation.admittedB world.signature entries)) _ _ _ validated
      cases admitted : TypeMapletValidation.admittedB world.signature entries with
      | false => simpa [boolean] using symbol_returns program bound state "None"
      | true =>
          simp only [boolean, BEq.rfl, ↓reduceIte]
          apply Primitive.authored_inst_type_computed_return constants entries hypotheses conclusion dependencies origin bound state
          · simpa [bound, applySubst, Subst.lookup] using variable_returns program bound state "entries"
          · simpa only [found, Lookup.answer] using ProofLookup.authored_known_return bound state
              (OperatorTable.tableAtom table.operators origins) (DeclarationTable.tableAtom table constants)
              axioms receipts key cache "state" "premise"
              (by simp [bound, before, environment, source, applySubst, Subst.lookup])
              (by simp [bound, applySubst, Subst.lookup])

/-- An invalid resolved maplet is refused before looking up its alleged
premise. The cache and key are arbitrary, including a missing or forged entry. -/
theorem authored_infer_invalid_type_maplets_refused (world : DefinitionAdapters.TheoryContext)
    (table : OperatorTable.Table world) (origins : TypeOp → Atom)
    (entries : List (Ty × Ty))
    (resolved : ∀ entry ∈ entries, TypeFormation.Resolved world.signature entry.1 ∧
      TypeFormation.Resolved world.signature entry.2)
    (invalid : ¬ ∀ entry ∈ entries, SignatureFormation.TypeFormed world.signature entry.1 ∧
      SignatureFormation.TypeFormed world.signature entry.2)
    (constants axioms receipts key : Atom) (cache : List (Atom × Atom))
    (bindings : Subst) (state : State) (stateKey requestKey : String)
    (stateCaptured : applySubst bindings (.var stateKey) =
      ProofLookup.sourceState (OperatorTable.tableAtom table origins) constants axioms receipts cache)
    (requestCaptured : applySubst bindings (.var requestKey) =
      .expression [.symbol "INST_TYPE", maplets registeredOperatorAtom entries, key]) :
    PureReturns program bindings state (.expression [.symbol "hol-light:infer", .var stateKey, .var requestKey]) state
      (.symbol "None") := by
  let source := ProofLookup.sourceState (OperatorTable.tableAtom table origins) constants axioms receipts cache
  let bound := [("premise", key), ("entries", maplets registeredOperatorAtom entries)] ++
    environment source (.expression [.symbol "INST_TYPE", maplets registeredOperatorAtom entries, key])
  have rejected : TypeMapletValidation.admittedB world.signature entries = false :=
    Bool.eq_false_of_not_eq_true (fun admitted => invalid
      ((TypeMapletValidation.admittedB_eq_true_iff world.signature entries).mp admitted))
  apply captured_dispatch_return bindings state source _ key _ stateKey requestKey stateCaptured requestCaptured
  unfold selected
  apply if_returns program bound state state state _ (boolean false) _ _ _
  · simpa only [rejected] using TypeMapletValidation.authored_type_maplets_valid_return world table origins
      constants axioms receipts cache entries resolved bound state "state" "entries"
      (by simp [bound, environment, source, applySubst, Subst.lookup])
      (by simp [bound, applySubst, Subst.lookup])
  · simpa [boolean] using symbol_returns program bound state "None"

end Dispatcher

/-- The executed source rule earns the shared type-substitution derivation
from an admitted cached premise. Hypothesis support follows its extensional
image, while the executed list and dependency occurrences remain available.
This is rule preservation, not whole cache-history authorization. -/
theorem authored_inst_type_shared_derivation (world : DefinitionAdapters.TheoryContext)
    (table : DeclarationTable.Table world) (origins : TypeOp → Atom) (constants : Const → Atom)
    (axiomAtom : Sequent → Atom) (entries : List (Ty × Ty))
    (resolved : ∀ entry ∈ entries, TypeFormation.Resolved world.signature entry.1 ∧
      TypeFormation.Resolved world.signature entry.2)
    (formed : ∀ entry ∈ entries, SignatureFormation.TypeFormed world.signature entry.1 ∧
      SignatureFormation.TypeFormed world.signature entry.2)
    (policy : AxiomPolicy) (input : Theorem)
    (inputDerives : Mettapedia.Logic.Derives (PolicyPrimitiveRule policy) input)
    (hypotheses : List CanonicalTerm) (dependencies : List Sequent)
    (hypothesisSupport : hypotheses.toFinset = input.sequent.hyp)
    (dependencySupport : dependencies.toFinset = input.axioms)
    (origin axioms receipts key : Atom) (cache : List (Atom × Atom))
    (found : cache.lookup key = some (Representation.theoremAtom constants [] input.sequent.concl.term
      (hypotheses.map (TheoremMetadata.hypothesisAtom constants)) (dependencies.map axiomAtom) origin))
    (bindings : Subst) (state : State) (stateKey requestKey : String)
    (stateCaptured : applySubst bindings (.var stateKey) = ProofLookup.sourceState
      (OperatorTable.tableAtom table.operators origins) (DeclarationTable.tableAtom table constants) axioms receipts cache)
    (requestCaptured : applySubst bindings (.var requestKey) =
      .expression [.symbol "INST_TYPE", maplets registeredOperatorAtom entries, key]) :
    ∃ out : Theorem, InferenceRequest.Semantics (.instType entries input) out ∧
      Mettapedia.Logic.Derives (PolicyPrimitiveRule policy) out ∧ out.axioms = input.axioms ∧
      (Hypotheses.imageOccurrences constants entries hypotheses).toFinset =
        out.sequent.hyp.image (TheoremMetadata.hypothesisAtom constants) ∧
      (dependencies.map axiomAtom).toFinset = out.axioms.image axiomAtom ∧
      PureReturns program bindings state (.expression [.symbol "hol-light:infer", .var stateKey, .var requestKey]) state
        (.expression [.symbol "Some", Representation.theoremAtom constants [] out.sequent.concl.term
          (Hypotheses.imageOccurrences constants entries hypotheses) (dependencies.map axiomAtom) (.symbol "INST_TYPE")]) := by
  let out := substituteTheorem (typeOnlySubstitution entries) input
  have semantics : InferenceRequest.Semantics (.instType entries input) out :=
    substituteTheorem_semantics (typeOnlySubstitution entries) input
  have derivation := semantics.shared_derivation policy (fun premise member => by
    have same : premise = input := by simpa [InferenceRequest.premises] using member
    simpa only [same] using inputDerives)
  refine ⟨out, semantics, derivation, rfl, ?_, ?_, ?_⟩
  · simpa only [out, substituteTheorem, Theorem.preserveAxiomsResult, hypothesisSupport]
      using Hypotheses.image_support constants entries hypotheses
  · simp only [out, substituteTheorem, Theorem.preserveAxiomsResult, List.toFinset_map, dependencySupport]
  · have admitted := (TypeMapletValidation.admittedB_eq_true_iff world.signature entries).mpr formed
    simpa only [out, substituteTheorem, Theorem.preserveAxiomsResult, admitted, ↓reduceIte, Primitive.result] using
      Dispatcher.authored_infer_inst_type_return world table origins constants entries resolved hypotheses input.sequent.concl
        (dependencies.map axiomAtom) origin axioms receipts key cache found bindings state
        stateKey requestKey stateCaptured requestCaptured

end Mettapedia.Languages.HOLLight.MeTTa.TypeInstantiation
