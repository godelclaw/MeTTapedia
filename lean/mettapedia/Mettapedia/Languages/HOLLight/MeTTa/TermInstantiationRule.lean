import Mettapedia.Languages.HOLLight.MeTTa.TermMapletReading
import Mettapedia.Languages.HOLLight.MeTTa.ListOperations
import Mettapedia.Languages.HOLLight.MeTTa.TheoremMetadata

/-!
# Authored HOL Light term instantiation

The source reader, substitution traversal and retained theorem metadata use
the existing shared term-substitution rule. Replacements are read once and
retain free occurrences beneath binders; they are not substituted again.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.HOLLight.MeTTa.TermInstantiationRule

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst matchAtom)
open Mettapedia.Languages.MeTTa.PeTTa
open Mettapedia.Languages.OpenTheory
open SignatureFormation
open Eval
open Effects (State)
open Representation (registeredOperatorAtom termAtom)

namespace Hypotheses

def imageOccurrences (constants : Const → Atom) (substitution : TypeCorrectTermSubstitution) : List CanonicalTerm → List Atom
  | [] => []
  | first :: rest =>
      let value := TheoremMetadata.hypothesisAtom constants (substitution.apply first)
      let tail := imageOccurrences constants substitution rest
      if value ∈ tail then tail else value :: tail

private theorem insert_support (item : Atom) (items : List Atom) :
    (if item ∈ items then items else item :: items).toFinset = insert item items.toFinset := by
  by_cases member : item ∈ items
  · simp [member, Finset.insert_eq_of_mem (List.mem_toFinset.mpr member)]
  · simp [member]

theorem image_support (constants : Const → Atom) (substitution : TypeCorrectTermSubstitution) (items : List CanonicalTerm) :
    (imageOccurrences constants substitution items).toFinset =
      (substitution.applyHypotheses items.toFinset).image (TheoremMetadata.hypothesisAtom constants) := by
  induction items with
  | nil => simp [imageOccurrences, TypeCorrectTermSubstitution.applyHypotheses]
  | cons first rest ih =>
      simp only [imageOccurrences]
      rw [insert_support, ih]
      simp only [List.toFinset_cons, TypeCorrectTermSubstitution.applyHypotheses, Finset.image_insert]

private def equation : SpaceSemantics.Equation :=
  (syntaxSource.program.equations.filter (fun row => row.head == "hol-light:inst-terms"))[0]'(by decide)
private def consBody : Atom := .expression [.symbol "hol-light:insert",
  .expression [.symbol "hol-light:term-subst", .var "entries", .var "first"],
  .expression [.symbol "hol-light:inst-terms", .var "entries", .var "rest"]]
private def cases : SpaceSemantics.Cases :=
  [(.symbol "HOL:Nil", .symbol "HOL:Nil"),
   (.expression [.symbol "HOL:Cons", .var "first", .var "rest"], consBody), (.var "malformed", .symbol "None")]
private def encodedTable (constants : Const → Atom) (entries : List TermMapletReading.Entry) : Atom :=
  TermSubstitution.table registeredOperatorAtom constants (TermMapletReading.substitutionEntries entries)
private def environment (constants : Const → Atom) (entries : List TermMapletReading.Entry) (items : List CanonicalTerm) : Subst :=
  [("terms", Premises.keys (items.map (TheoremMetadata.hypothesisAtom constants))), ("entries", encodedTable constants entries)]
private theorem shape : equation.body = .expression [.symbol "case", .var "terms",
    .expression (cases.map fun row => .expression [row.1, row.2])] := by decide
private theorem clause (constants : Const → Atom) (entries : List TermMapletReading.Entry) (items : List CanonicalTerm) :
    clauses program "hol-light:inst-terms" [encodedTable constants entries,
      Premises.keys (items.map (TheoremMetadata.hypothesisAtom constants))] =
      [.evaluate (environment constants entries items) equation.body] := by
  rw [clauses_use_only_the_named_equations]
  have unique : program.equations.filter (fun row => row.head == "hol-light:inst-terms") = [equation] := by rfl
  rw [unique]
  have formals : equation.arguments = [.var "entries", .var "terms"] := by decide
  simp [formals, environment, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]

private theorem body_returns (world : DefinitionAdapters.TheoryContext) (constants : Const → Atom)
    (entries : List TermMapletReading.Entry) (admitted : TermMapletReading.admittedB entries = true)
    (formed : ∀ entry ∈ entries, TermMapletReading.EntryFormed world.signature entry)
    (items : List CanonicalTerm) (annotations : ∀ item ∈ items, AnnotationsFormed world.signature item.term) (state : State) :
    PureReturns program (environment constants entries items) state equation.body state
      (Premises.keys (imageOccurrences constants (TermMapletReading.substitution entries admitted) items)) := by
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
          (TheoremMetadata.hypothesisAtom constants ((TermMapletReading.substitution entries admitted).apply first))
          (imageOccurrences constants (TermMapletReading.substitution entries admitted) rest)
        · simpa only [TheoremMetadata.hypothesisAtom, TypeCorrectTermSubstitution.apply, TermSubst.applyChecked,
            TermMapletReading.substitution_raw] using
            TermSubstitution.authored_registered_term_substitution_return world constants bound state
              (TermMapletReading.substitutionEntries entries) (TermMapletReading.substitution_keys_formed _ entries formed)
              [] first.term (annotations first (by simp)) "entries" "first"
              (by simp [bound, before, environment, encodedTable, applySubst, Subst.lookup])
              (by simp [bound, TheoremMetadata.hypothesisAtom, applySubst, Subst.lookup])
        · apply authored_variable_call_returns program bound (environment constants entries rest)
            state state "hol-light:inst-terms" ["entries", "rest"] equation.body _
            (by decide) (by decide) (by decide) _ (ih (fun item member => annotations item (by simp [member]))) (by decide)
          simpa [bound, before, environment, applySubst, Subst.lookup] using clause constants entries rest

theorem authored_hypotheses_return (world : DefinitionAdapters.TheoryContext) (constants : Const → Atom)
    (entries : List TermMapletReading.Entry) (admitted : TermMapletReading.admittedB entries = true)
    (formed : ∀ entry ∈ entries, TermMapletReading.EntryFormed world.signature entry)
    (items : List CanonicalTerm) (annotations : ∀ item ∈ items, AnnotationsFormed world.signature item.term)
    (bindings : Subst) (state : State) (entriesKey itemsKey : String)
    (entriesCaptured : applySubst bindings (.var entriesKey) = encodedTable constants entries)
    (itemsCaptured : applySubst bindings (.var itemsKey) = Premises.keys (items.map (TheoremMetadata.hypothesisAtom constants))) :
    PureReturns program bindings state (.expression [.symbol "hol-light:inst-terms", .var entriesKey, .var itemsKey]) state
      (Premises.keys (imageOccurrences constants (TermMapletReading.substitution entries admitted) items)) := by
  apply authored_variable_call_returns program bindings (environment constants entries items) state state
    "hol-light:inst-terms" [entriesKey, itemsKey] equation.body _ (by decide) (by decide) (by decide) _
    (body_returns world constants entries admitted formed items annotations state) (by decide)
  simpa only [List.map_cons, List.map_nil, entriesCaptured, itemsCaptured] using clause constants entries items

end Hypotheses

namespace Primitive

def result (constants : Const → Atom) (entries : List TermMapletReading.Entry) (admitted : TermMapletReading.admittedB entries = true)
    (hypotheses : List CanonicalTerm) (conclusion : CanonicalTerm) (dependencies : List Atom) : Atom :=
  .expression [.symbol "Some", Representation.theoremAtom constants []
    ((TermMapletReading.substitution entries admitted).apply conclusion).term
    (Hypotheses.imageOccurrences constants (TermMapletReading.substitution entries admitted) hypotheses)
    dependencies (.symbol "INST")]
private def equation : SpaceSemantics.Equation :=
  (kernelSource.program.equations.filter (fun row => row.head == "hol-light:inst"))[0]'(by decide)
private def selected : Atom := .expression [.symbol "Some", .expression [.symbol "HOL:Thm",
  .expression [.symbol "hol-light:inst-terms", .var "entries", .var "hyps"],
  .expression [.symbol "hol-light:term-subst", .var "entries", .var "conclusion"],
  .var "dependencies", .symbol "INST"]]
private def cases : SpaceSemantics.Cases :=
  [(.expression [.symbol "Some", .expression [.symbol "HOL:Thm", .var "hyps", .var "conclusion",
      .var "dependencies", .var "origin"]], selected), (.var "malformed", .symbol "None")]
private def environment (entries premise : Atom) : Subst := [("premise", premise), ("entries", entries)]
private theorem shape : equation.body = .expression [.symbol "case", .var "premise",
    .expression (cases.map fun row => .expression [row.1, row.2])] := by decide
private theorem clause (entries premise : Atom) : clauses program "hol-light:inst" [entries, premise] =
    [.evaluate (environment entries premise) equation.body] := by
  rw [clauses_use_only_the_named_equations]
  have unique : program.equations.filter (fun row => row.head == "hol-light:inst") = [equation] := by rfl
  rw [unique]
  have formals : equation.arguments = [.var "entries", .var "premise"] := by decide
  simp [formals, environment, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]

private theorem body_returns (world : DefinitionAdapters.TheoryContext) (constants : Const → Atom)
    (entries : List TermMapletReading.Entry) (admitted : TermMapletReading.admittedB entries = true)
    (formed : ∀ entry ∈ entries, TermMapletReading.EntryFormed world.signature entry)
    (hypotheses : List CanonicalTerm) (hypothesesFormed : ∀ item ∈ hypotheses, AnnotationsFormed world.signature item.term)
    (conclusion : CanonicalTerm) (conclusionFormed : AnnotationsFormed world.signature conclusion.term)
    (dependencies : List Atom) (origin : Atom) (state : State) :
    PureReturns program (environment
      (TermSubstitution.table registeredOperatorAtom constants (TermMapletReading.substitutionEntries entries))
      (.expression [.symbol "Some", Representation.theoremAtom constants [] conclusion.term
        (hypotheses.map (TheoremMetadata.hypothesisAtom constants)) dependencies origin]))
      state equation.body state (result constants entries admitted hypotheses conclusion dependencies) := by
  let encoded := TermSubstitution.table registeredOperatorAtom constants (TermMapletReading.substitutionEntries entries)
  let premise := Atom.expression [.symbol "Some", Representation.theoremAtom constants [] conclusion.term
    (hypotheses.map (TheoremMetadata.hypothesisAtom constants)) dependencies origin]
  let before := environment encoded premise
  let bound := [("origin", origin), ("dependencies", Premises.keys dependencies),
    ("conclusion", termAtom registeredOperatorAtom constants [] conclusion.term),
    ("hyps", Premises.keys (hypotheses.map (TheoremMetadata.hypothesisAtom constants)))] ++ before
  rw [shape]
  apply case_returns program before bound state state state (.var "premise") premise selected _ _ cases (read_cases_encoded cases)
  · exact variable_returns program before state "premise"
  · simp [premise, before, environment, bound, cases, Representation.theoremAtom, SpaceSemantics.selectCase,
      SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]
  · unfold selected result
    apply unary_constructor_of_returns program bound state state "Some" _ _ (by decide) (by decide)
    apply PureData.constructor_return program bound state "HOL:Thm" _ _ (by decide) (by decide)
    refine .cons ?_ (.cons ?_ (.cons ?_ (.cons ?_ .nil)))
    · exact Hypotheses.authored_hypotheses_return world constants entries admitted formed hypotheses hypothesesFormed bound state
        "entries" "hyps" (by simp [bound, before, environment, encoded, Hypotheses.encodedTable, applySubst, Subst.lookup])
        (by simp [bound, applySubst, Subst.lookup])
    · simpa only [TypeCorrectTermSubstitution.apply, TermSubst.applyChecked, TermMapletReading.substitution_raw] using
        TermSubstitution.authored_registered_term_substitution_return world constants bound state
          (TermMapletReading.substitutionEntries entries) (TermMapletReading.substitution_keys_formed _ entries formed)
          [] conclusion.term conclusionFormed "entries" "conclusion"
          (by simp [bound, before, environment, encoded, applySubst, Subst.lookup])
          (by simp [bound, applySubst, Subst.lookup])
    · simpa [bound, applySubst, Subst.lookup] using variable_returns program bound state "dependencies"
    · exact symbol_returns program bound state "INST"

theorem authored_inst_computed_return (world : DefinitionAdapters.TheoryContext) (constants : Const → Atom)
    (entries : List TermMapletReading.Entry) (admitted : TermMapletReading.admittedB entries = true)
    (formed : ∀ entry ∈ entries, TermMapletReading.EntryFormed world.signature entry)
    (hypotheses : List CanonicalTerm) (hypothesesFormed : ∀ item ∈ hypotheses, AnnotationsFormed world.signature item.term)
    (conclusion : CanonicalTerm) (conclusionFormed : AnnotationsFormed world.signature conclusion.term)
    (dependencies : List Atom) (origin : Atom) (bindings : Subst) (state : State) (entriesExpression premiseExpression : Atom)
    (entriesReturned : PureReturns program bindings state entriesExpression state
      (TermSubstitution.table registeredOperatorAtom constants (TermMapletReading.substitutionEntries entries)))
    (premiseReturned : PureReturns program bindings state premiseExpression state
      (.expression [.symbol "Some", Representation.theoremAtom constants [] conclusion.term
        (hypotheses.map (TheoremMetadata.hypothesisAtom constants)) dependencies origin])) :
    PureReturns program bindings state (.expression [.symbol "hol-light:inst", entriesExpression, premiseExpression]) state
      (result constants entries admitted hypotheses conclusion dependencies) :=
  authored_binary_call_returns program bindings (environment
    (TermSubstitution.table registeredOperatorAtom constants (TermMapletReading.substitutionEntries entries))
    (.expression [.symbol "Some", Representation.theoremAtom constants [] conclusion.term
      (hypotheses.map (TheoremMetadata.hypothesisAtom constants)) dependencies origin])) state state state state
    "hol-light:inst" entriesExpression premiseExpression _ _ equation.body _
    (by decide) (by decide) (by decide) (by decide) (by decide) entriesReturned premiseReturned (clause _ _)
    (body_returns world constants entries admitted formed hypotheses hypothesesFormed conclusion conclusionFormed dependencies origin state)
    (by decide)

end Primitive

namespace Dispatcher

private def equation : SpaceSemantics.Equation :=
  (kernelSource.program.equations.filter (fun row => row.head == "hol-light:infer"))[0]'(by decide)
private def cases : SpaceSemantics.Cases :=
  match equation.body with
  | .expression [_, _, .expression rows] => (readCases rows).getD []
  | _ => []
private def selected : Atom := .expression [.symbol "case",
  .expression [.symbol "hol-light:read-maplets", .var "state", .var "entries"],
  .expression [
    .expression [.expression [.symbol "Some", .var "substitution"],
      .expression [.symbol "hol-light:inst", .var "substitution",
        .expression [.symbol "hol-light:known", .var "state", .var "premise"]]],
    .expression [.var "malformed", .symbol "None"]]]
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
    SpaceSemantics.selectCase (environment source (.expression [.symbol "INST", entries, premise]))
      (.expression [.symbol "INST", entries, premise]) cases =
      some ([("premise", premise), ("entries", entries)] ++
        environment source (.expression [.symbol "INST", entries, premise]), selected) := by
  have patterns : cases = [
      (.expression [.symbol "REFL", .var "term"], (cases[0]'(by decide)).2),
      (.expression [.symbol "TRANS", .var "first", .var "second"], (cases[1]'(by decide)).2),
      (.expression [.symbol "MK_COMB", .var "first", .var "second"], (cases[2]'(by decide)).2),
      (.expression [.symbol "ABS", .var "variable", .var "premise"], (cases[3]'(by decide)).2),
      (.expression [.symbol "BETA", .var "term"], (cases[4]'(by decide)).2),
      (.expression [.symbol "ASSUME", .var "term"], (cases[5]'(by decide)).2),
      (.expression [.symbol "EQ_MP", .var "first", .var "second"], (cases[6]'(by decide)).2),
      (.expression [.symbol "DEDUCT_ANTISYM_RULE", .var "first", .var "second"], (cases[7]'(by decide)).2),
      (.expression [.symbol "INST", .var "entries", .var "premise"], selected),
      (.expression [.symbol "INST_TYPE", .var "entries", .var "premise"], (cases[9]'(by decide)).2),
      (.var "unsupported", .symbol "None")] := by decide
  rw [patterns]
  simp [environment, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
    SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]

private theorem captured_dispatch_return (bindings : Subst) (state : State) (source entries key answer : Atom)
    (stateKey requestKey : String)
    (stateCaptured : applySubst bindings (.var stateKey) = source)
    (requestCaptured : applySubst bindings (.var requestKey) = .expression [.symbol "INST", entries, key])
    (returned : PureReturns program ([("premise", key), ("entries", entries)] ++
      environment source (.expression [.symbol "INST", entries, key])) state selected state answer) :
    PureReturns program bindings state (.expression [.symbol "hol-light:infer", .var stateKey, .var requestKey]) state answer := by
  let request := Atom.expression [.symbol "INST", entries, key]
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

private def substitutionBody : Atom := .expression [.symbol "hol-light:inst", .var "substitution",
  .expression [.symbol "hol-light:known", .var "state", .var "premise"]]
private def substitutionCases : SpaceSemantics.Cases :=
  [(.expression [.symbol "Some", .var "substitution"], substitutionBody), (.var "malformed", .symbol "None")]
private theorem selected_shape : selected = .expression [.symbol "case",
    .expression [.symbol "hol-light:read-maplets", .var "state", .var "entries"],
    .expression (substitutionCases.map fun row => .expression [row.1,row.2])] := by decide

/-- The actual dispatcher reads the complete maplet list before obtaining
the cache premise and performing admitted simultaneous substitution. -/
theorem authored_infer_inst_return (world : DefinitionAdapters.TheoryContext) (table : DeclarationTable.Table world)
    (origins : TypeOp → Atom) (constants : Const → Atom) (entries : List TermMapletReading.Entry)
    (admitted : TermMapletReading.admittedB entries = true)
    (formed : ∀ entry ∈ entries, TermMapletReading.EntryFormed world.signature entry)
    (hypotheses : List CanonicalTerm) (hypothesesFormed : ∀ item ∈ hypotheses, AnnotationsFormed world.signature item.term)
    (conclusion : CanonicalTerm) (conclusionFormed : AnnotationsFormed world.signature conclusion.term)
    (dependencies : List Atom) (origin axioms receipts key : Atom) (cache : List (Atom × Atom))
    (found : cache.lookup key = some (Representation.theoremAtom constants [] conclusion.term
      (hypotheses.map (TheoremMetadata.hypothesisAtom constants)) dependencies origin))
    (bindings : Subst) (state : State) (stateKey requestKey : String)
    (stateCaptured : applySubst bindings (.var stateKey) = ProofLookup.sourceState
      (OperatorTable.tableAtom table.operators origins) (DeclarationTable.tableAtom table constants) axioms receipts cache)
    (requestCaptured : applySubst bindings (.var requestKey) =
      .expression [.symbol "INST", TermMapletReading.sourceAtom entries, key]) :
    PureReturns program bindings state (.expression [.symbol "hol-light:infer", .var stateKey, .var requestKey]) state
      (Primitive.result constants entries admitted hypotheses conclusion dependencies) := by
  let source := ProofLookup.sourceState (OperatorTable.tableAtom table.operators origins)
    (DeclarationTable.tableAtom table constants) axioms receipts cache
  let bound := [("premise", key), ("entries", TermMapletReading.sourceAtom entries)] ++
    environment source (.expression [.symbol "INST", TermMapletReading.sourceAtom entries, key])
  let encoded := TermSubstitution.table registeredOperatorAtom constants (TermMapletReading.substitutionEntries entries)
  let operands := ("substitution", encoded) :: bound
  apply captured_dispatch_return bindings state source _ key _ stateKey requestKey stateCaptured requestCaptured
  rw [selected_shape]
  apply case_returns program bound operands state state state
    (.expression [.symbol "hol-light:read-maplets", .var "state", .var "entries"])
    (.expression [.symbol "Some", encoded]) substitutionBody _ _ substitutionCases (read_cases_encoded substitutionCases)
  · simpa only [TermMapletReading.result, admitted, ↓reduceIte] using
      TermMapletReading.authored_read_maplets_return world table origins constants axioms receipts cache entries formed
        bound state "state" "entries"
        (by simp [bound, environment, source, applySubst, Subst.lookup])
        (by simp [bound, applySubst, Subst.lookup])
  · simp [substitutionCases, operands, bound, environment, SpaceSemantics.selectCase,
      SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]
  · unfold substitutionBody
    apply Primitive.authored_inst_computed_return world constants entries admitted formed hypotheses hypothesesFormed
      conclusion conclusionFormed dependencies origin operands state
    · simpa [operands, encoded, applySubst, Subst.lookup] using variable_returns program operands state "substitution"
    · simpa only [found, Lookup.answer] using ProofLookup.authored_known_return operands state
        (OperatorTable.tableAtom table.operators origins) (DeclarationTable.tableAtom table constants)
        axioms receipts key cache "state" "premise"
        (by simp [operands, bound, environment, source, applySubst, Subst.lookup])
        (by simp [operands, bound, applySubst, Subst.lookup])

/-- An ill-typed maplet anywhere in the complete list is refused before
looking up a premise. The cache and alleged premise key are arbitrary. -/
theorem authored_infer_invalid_maplets_refused (world : DefinitionAdapters.TheoryContext) (table : DeclarationTable.Table world)
    (origins : TypeOp → Atom) (constants : Const → Atom) (entries : List TermMapletReading.Entry)
    (formed : ∀ entry ∈ entries, TermMapletReading.EntryFormed world.signature entry)
    (invalid : ¬ SourceSubstitution.TermMapletsAdmissible (TermMapletReading.sourceEntries entries))
    (axioms receipts key : Atom) (cache : List (Atom × Atom)) (bindings : Subst) (state : State) (stateKey requestKey : String)
    (stateCaptured : applySubst bindings (.var stateKey) = ProofLookup.sourceState
      (OperatorTable.tableAtom table.operators origins) (DeclarationTable.tableAtom table constants) axioms receipts cache)
    (requestCaptured : applySubst bindings (.var requestKey) =
      .expression [.symbol "INST", TermMapletReading.sourceAtom entries, key]) :
    PureReturns program bindings state (.expression [.symbol "hol-light:infer", .var stateKey, .var requestKey]) state
      (.symbol "None") := by
  let source := ProofLookup.sourceState (OperatorTable.tableAtom table.operators origins)
    (DeclarationTable.tableAtom table constants) axioms receipts cache
  let bound := [("premise", key), ("entries", TermMapletReading.sourceAtom entries)] ++
    environment source (.expression [.symbol "INST", TermMapletReading.sourceAtom entries, key])
  let refused := ("malformed", Atom.symbol "None") :: bound
  apply captured_dispatch_return bindings state source _ key _ stateKey requestKey stateCaptured requestCaptured
  rw [selected_shape]
  apply case_returns program bound refused state state state
    (.expression [.symbol "hol-light:read-maplets", .var "state", .var "entries"]) (.symbol "None") (.symbol "None")
    _ _ substitutionCases (read_cases_encoded substitutionCases)
  · exact TermMapletReading.authored_invalid_maplets_refused world table origins constants axioms receipts cache entries formed
      invalid bound state "state" "entries"
      (by simp [bound, environment, source, applySubst, Subst.lookup]) (by simp [bound, applySubst, Subst.lookup])
  · simp [substitutionCases, refused, bound, environment, SpaceSemantics.selectCase,
      SpaceSemantics.matchValue, matchAtom, Subst.lookup]
  · exact symbol_returns program refused state "None"

end Dispatcher

/-- Admitted source execution earns the existing shared HOL substitution
derivation, retaining the actual hypothesis image and dependency occurrences.
The matching input premise is already derived; cache history is not assumed. -/
theorem authored_inst_shared_derivation (world : DefinitionAdapters.TheoryContext) (table : DeclarationTable.Table world)
    (origins : TypeOp → Atom) (constants : Const → Atom) (axiomAtom : Sequent → Atom)
    (entries : List TermMapletReading.Entry) (admitted : TermMapletReading.admittedB entries = true)
    (formed : ∀ entry ∈ entries, TermMapletReading.EntryFormed world.signature entry)
    (policy : AxiomPolicy) (input : Theorem)
    (inputDerives : Mettapedia.Logic.Derives (PolicyPrimitiveRule policy) input)
    (hypotheses : List CanonicalTerm) (hypothesesFormed : ∀ item ∈ hypotheses, AnnotationsFormed world.signature item.term)
    (conclusionFormed : AnnotationsFormed world.signature input.sequent.concl.term)
    (dependencies : List Sequent) (hypothesisSupport : hypotheses.toFinset = input.sequent.hyp)
    (dependencySupport : dependencies.toFinset = input.axioms)
    (origin axioms receipts key : Atom) (cache : List (Atom × Atom))
    (found : cache.lookup key = some (Representation.theoremAtom constants [] input.sequent.concl.term
      (hypotheses.map (TheoremMetadata.hypothesisAtom constants)) (dependencies.map axiomAtom) origin))
    (bindings : Subst) (state : State) (stateKey requestKey : String)
    (stateCaptured : applySubst bindings (.var stateKey) = ProofLookup.sourceState
      (OperatorTable.tableAtom table.operators origins) (DeclarationTable.tableAtom table constants) axioms receipts cache)
    (requestCaptured : applySubst bindings (.var requestKey) =
      .expression [.symbol "INST", TermMapletReading.sourceAtom entries, key]) :
    ∃ out : Theorem, InferenceRequest.Semantics (.inst (TermMapletReading.sourceEntries entries) input) out ∧
      Mettapedia.Logic.Derives (PolicyPrimitiveRule policy) out ∧ out.axioms = input.axioms ∧
      (Hypotheses.imageOccurrences constants (TermMapletReading.substitution entries admitted) hypotheses).toFinset =
        out.sequent.hyp.image (TheoremMetadata.hypothesisAtom constants) ∧
      (dependencies.map axiomAtom).toFinset = out.axioms.image axiomAtom ∧
      PureReturns program bindings state (.expression [.symbol "hol-light:infer", .var stateKey, .var requestKey]) state
        (.expression [.symbol "Some", Representation.theoremAtom constants [] out.sequent.concl.term
          (Hypotheses.imageOccurrences constants (TermMapletReading.substitution entries admitted) hypotheses)
          (dependencies.map axiomAtom) (.symbol "INST")]) := by
  let substitution := TermMapletReading.substitution entries admitted
  let out := substituteTheorem substitution input
  have semantics : InferenceRequest.Semantics (.inst (TermMapletReading.sourceEntries entries) input) out :=
    ⟨substitution, TermMapletReading.substitution_admitted entries admitted, substituteTheorem_semantics substitution input⟩
  have derivation := semantics.shared_derivation policy (fun premise member => by
    have same : premise = input := by simpa [InferenceRequest.premises] using member
    simpa only [same] using inputDerives)
  refine ⟨out, semantics, derivation, rfl, ?_, ?_, ?_⟩
  · simpa only [out, substituteTheorem, Theorem.preserveAxiomsResult, hypothesisSupport] using
      Hypotheses.image_support constants substitution hypotheses
  · simp only [out, substituteTheorem, Theorem.preserveAxiomsResult, List.toFinset_map, dependencySupport]
  · simpa only [out, substituteTheorem, Theorem.preserveAxiomsResult, Primitive.result] using
      Dispatcher.authored_infer_inst_return world table origins constants entries admitted formed hypotheses hypothesesFormed
        input.sequent.concl conclusionFormed (dependencies.map axiomAtom) origin axioms receipts key cache found
        bindings state stateKey requestKey stateCaptured requestCaptured

end Mettapedia.Languages.HOLLight.MeTTa.TermInstantiationRule
