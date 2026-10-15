import Mettapedia.Languages.HOLLight.MeTTa.InferenceExecution
import Mettapedia.Languages.HOLLight.MeTTa.TermSubstitution

/-!
# Actual source term-maplet reading

Each replacement and variable key is read in the retained declaration context.
The complete list is checked before first-match substitution can use it.
Well-formed source terms may still have mismatched maplet types; their reader
result is refusal. Successful reading retains every entry in source order.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.HOLLight.MeTTa.TermMapletReading

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst matchAtom)
open Mettapedia.Languages.MeTTa.PeTTa
open Mettapedia.Languages.OpenTheory
open SignatureFormation
open Representation (registeredOperatorAtom termAtom variableAtom)
open TypeSubstitution (typeAtom nameAtom)
open Eval
open Effects (State boolean)

abbrev Entry := CheckedSourceTerm × SourceVar

structure EntryFormed (signature : Signature) (entry : Entry) : Prop where
  replacementResolved : TermReading.SourceResolved signature entry.1.source
  replacementAnnotations : AnnotationsFormed signature entry.1.canonical.term
  replacementType : TypeFormed signature entry.1.ty
  keyGlobal : entry.2.name.namespaceComponents = []
  keyResolved : TypeFormation.Resolved signature entry.2.ty
  keyType : TypeFormed signature entry.2.ty

def sourceEntries (entries : List Entry) : List SourceSubstitution.TermMaplet :=
  entries.map fun entry => (entry.1, .var entry.2.name entry.2.ty)

def sourceAtom (entries : List Entry) : Atom :=
  Premises.keys (entries.map fun entry => .expression [.symbol "HOL:Maplet",
    TermReading.sourceAtom entry.1.source,
    TermReading.sourceAtom (.var entry.2.name entry.2.ty)])

def substitutionEntries (entries : List Entry) : List (SourceVar × CheckedSourceTerm) :=
  entries.map fun entry => (entry.2, entry.1)

def admittedB (entries : List Entry) : Bool :=
  entries.all fun entry => Ty.same entry.1.ty entry.2.ty

@[simp] theorem admittedB_cons (entry : Entry) (rest : List Entry) :
    admittedB (entry :: rest) = (Ty.same entry.1.ty entry.2.ty && admittedB rest) := rfl

theorem admittedB_eq_true_iff (entries : List Entry) :
    admittedB entries = true ↔ SourceSubstitution.TermMapletsAdmissible (sourceEntries entries) := by
  simp only [admittedB, List.all_eq_true, Ty.same_eq_true_iff,
    SourceSubstitution.TermMapletsAdmissible, sourceEntries, List.mem_map]
  constructor
  · intro valid entry member
    obtain ⟨original, member, rfl⟩ := member
    exact valid original member
  · intro valid entry member
    exact valid (entry.1, .var entry.2.name entry.2.ty) ⟨entry, member, rfl⟩

theorem source_entries_substitution (entries : List Entry) :
    SourceSubstitution.termEntries (sourceEntries entries) = substitutionEntries entries := by
  simp [sourceEntries, SourceSubstitution.termEntries, substitutionEntries, List.filterMap_map]

/-- Successful source admission constructs the existing shared substitution
with the source's complete, ordered maplets. -/
def substitution (entries : List Entry) (admitted : admittedB entries = true) : TypeCorrectTermSubstitution :=
  ⟨SourceSubstitution.termSubstitution (sourceEntries entries),
    SourceSubstitution.termSubstitution_typeCorrect (sourceEntries entries) ((admittedB_eq_true_iff entries).mp admitted)⟩

theorem substitution_admitted (entries : List Entry) (admitted : admittedB entries = true) :
    SourceSubstitution.admitTermSubstitution (sourceEntries entries) = some (substitution entries admitted) := by
  have valid := (SourceSubstitution.all_termMapletB_eq_true_iff (sourceEntries entries)).mpr
    ((admittedB_eq_true_iff entries).mp admitted)
  simp [SourceSubstitution.admitTermSubstitution, valid, substitution]

theorem substitution_raw (entries : List Entry) (admitted : admittedB entries = true) :
    (substitution entries admitted).raw = TermSubst.mk TypeSubst.empty (substitutionEntries entries) := by
  simp only [substitution, SourceSubstitution.termSubstitution, source_entries_substitution]

theorem substitution_keys_formed (signature : Signature) (entries : List Entry)
    (formed : ∀ entry ∈ entries, EntryFormed signature entry) :
    ∀ entry ∈ substitutionEntries entries, TypeFormed signature entry.1.ty := by
  intro entry member
  obtain ⟨original, originalMember, equality⟩ :=
    (List.mem_map (f := fun entry : Entry => (entry.2, entry.1)) (l := entries)).mp member
  have keyEquality : original.2 = entry.1 := congrArg Prod.fst equality
  rw [← keyEquality]
  exact (formed original originalMember).keyType

def result (constants : Const → Atom) (entries : List Entry) : Atom :=
  if admittedB entries then .expression [.symbol "Some",
    TermSubstitution.table registeredOperatorAtom constants (substitutionEntries entries)] else .symbol "None"

private def equation : SpaceSemantics.Equation :=
  (kernelSource.program.equations.filter (fun row => row.head == "hol-light:read-maplets"))[0]'(by decide)
private def pending : Atom := .expression [
  .expression [.symbol "hol-light:read", .var "state", .var "replacement"],
  .expression [.symbol "hol-light:read", .var "state", .expression [.symbol "Var", .var "name", .var "type"]],
  .expression [.symbol "hol-light:read-maplets", .var "state", .var "rest"]]
private def selected : Atom := .expression [.symbol "if", .expression [.symbol "==",
  .expression [.symbol "hol-light:term-type", .var "value"], .expression [.symbol "Some", .var "type"]],
  .expression [.symbol "Some", .expression [.symbol "HOL:Cons",
    .expression [.symbol "HOL:Entry", .var "variable", .var "value"], .var "tail"]], .symbol "None"]
private def innerCases : SpaceSemantics.Cases :=
  [(.expression [.expression [.symbol "Some", .var "value"],
    .expression [.symbol "Some", .var "variable"], .expression [.symbol "Some", .var "tail"]], selected),
   (.var "malformed", .symbol "None")]
private def consBody : Atom := .expression [.symbol "case", pending,
  .expression (innerCases.map fun row => .expression [row.1, row.2])]
private def cases : SpaceSemantics.Cases :=
  [(.symbol "HOL:Nil", .expression [.symbol "Some", .symbol "HOL:Nil"]),
   (.expression [.symbol "HOL:Cons", .expression [.symbol "HOL:Maplet", .var "replacement",
     .expression [.symbol "Var", .var "name", .var "type"]], .var "rest"], consBody),
   (.var "malformed", .symbol "None")]
private def environment (source entries : Atom) : Subst := [("entries", entries), ("state", source)]
private theorem shape : equation.body = .expression [.symbol "case", .var "entries",
    .expression (cases.map fun row => .expression [row.1, row.2])] := by decide
private theorem clause (source entries : Atom) : clauses program "hol-light:read-maplets" [source, entries] =
    [.evaluate (environment source entries) equation.body] := by
  rw [clauses_use_only_the_named_equations]
  have unique : program.equations.filter (fun row => row.head == "hol-light:read-maplets") = [equation] := by rfl
  rw [unique]
  have formals : equation.arguments = [.var "state", .var "entries"] := by decide
  simp [formals, environment, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]

private theorem body_returns (world : DefinitionAdapters.TheoryContext) (table : DeclarationTable.Table world)
    (origins : TypeOp → Atom) (constants : Const → Atom) (axioms receipts : Atom) (cache : List (Atom × Atom))
    (entries : List Entry) (formed : ∀ entry ∈ entries, EntryFormed world.signature entry) (state : State) :
    PureReturns program (environment (ProofLookup.sourceState (OperatorTable.tableAtom table.operators origins)
      (DeclarationTable.tableAtom table constants) axioms receipts cache) (sourceAtom entries))
      state equation.body state (result constants entries) := by
  let source := ProofLookup.sourceState (OperatorTable.tableAtom table.operators origins)
    (DeclarationTable.tableAtom table constants) axioms receipts cache
  induction entries with
  | nil =>
      let before := environment source (sourceAtom [])
      rw [shape]
      apply case_returns program before before state state state (.var "entries") (.symbol "HOL:Nil")
        (.expression [.symbol "Some", .symbol "HOL:Nil"]) _ _ cases (read_cases_encoded cases)
      · simpa [before, environment, sourceAtom, Premises.keys, applySubst, Subst.lookup] using
          variable_returns program before state "entries"
      · simp [cases, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
      · simpa [result, admittedB, substitutionEntries, TermSubstitution.table, TermSubstitution.encodedEntries, Lookup.table,
          Premises.keys] using unary_constructor_of_returns program before state state "Some" (.symbol "HOL:Nil")
            (.symbol "HOL:Nil") (by decide) (by decide) (symbol_returns program before state "HOL:Nil")
  | cons entry rest ih =>
      rcases entry with ⟨replacement, key⟩
      have entryFormed := formed (replacement,key) (by simp)
      let before := environment source (sourceAtom ((replacement,key)::rest))
      let bound := [("rest", sourceAtom rest), ("type", typeAtom registeredOperatorAtom key.ty),
        ("name", nameAtom key.name), ("replacement", TermReading.sourceAtom replacement.source)] ++ before
      let replacementValue := termAtom registeredOperatorAtom constants [] replacement.canonical.term
      let keyValue := variableAtom registeredOperatorAtom key
      let tail := TermSubstitution.table registeredOperatorAtom constants (substitutionEntries rest)
      have replacementRead := InferenceExecution.authored_state_read_return world table origins constants
        replacement.source entryFormed.replacementResolved entryFormed.replacementAnnotations replacement.ty replacement.checked
        bound state axioms receipts cache "state" "replacement"
        (by simp [bound, before, environment, source, applySubst, Subst.lookup])
        (by simp [bound, applySubst, Subst.lookup])
      have keyRead : PureReturns program bound state
          (.expression [.symbol "hol-light:read", .var "state", .expression [.symbol "Var", .var "name", .var "type"]]) state
          (.expression [.symbol "Some", keyValue]) := by
        have resolvedKey : TermReading.SourceResolved world.signature (.var key.name key.ty) := by
          simpa only [TermReading.SourceResolved] using And.intro entryFormed.keyGlobal entryFormed.keyResolved
        have keyAnnotations : AnnotationsFormed world.signature ((SourceTerm.var key.name key.ty).toDB []) := by
          simpa [SourceTerm.toDB, boundIndex] using AnnotationsFormed.free entryFormed.keyType
        have read := InferenceExecution.authored_state_read_computed_return world table origins constants
          (.var key.name key.ty) resolvedKey keyAnnotations key.ty (by simp) bound state axioms receipts cache
          (.var "state") (.expression [.symbol "Var", .var "name", .var "type"])
          (by simpa [bound, before, environment, source, applySubst, Subst.lookup] using
            variable_returns program bound state "state")
          (by simpa [TermReading.sourceAtom, Representation.sourceVariableAtom, bound, applySubst, Subst.lookup] using
            constructor_variables_return program bound state "Var" ["name","type"] (by decide) (by decide))
        simpa [SourceTerm.toDB, boundIndex, termAtom, keyValue] using read
      have recursive := ih (fun entry member => formed entry (by simp [member]))
      have tailRead : PureReturns program bound state
          (.expression [.symbol "hol-light:read-maplets", .var "state", .var "rest"]) state (result constants rest) := by
        apply authored_variable_call_returns program bound (environment source (sourceAtom rest)) state state
          "hol-light:read-maplets" ["state","rest"] equation.body _ (by decide) (by decide) (by decide) _ recursive (by decide)
        simpa [bound, before, environment, applySubst, Subst.lookup] using clause source (sourceAtom rest)
      have pendingRead : PureReturns program bound state pending state
          (.expression [.expression [.symbol "Some", replacementValue], .expression [.symbol "Some", keyValue],
            result constants rest]) := by
        refine .step (u := ({ state, control := .arguments bound .data _ [] 0 } : Configuration)) (step_transition rfl) ?_
        apply PureData.arguments_return
        exact .cons replacementRead (.cons keyRead (.cons tailRead .nil))
      rw [shape]
      apply case_returns program before bound state state state (.var "entries")
        (sourceAtom ((replacement,key)::rest)) consBody _ _ cases (read_cases_encoded cases)
      · simpa [before, environment, applySubst, Subst.lookup] using variable_returns program before state "entries"
      · simp [cases, sourceAtom, TermReading.sourceAtom, Representation.sourceVariableAtom, Premises.keys, bound, before,
          environment, SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]
      · unfold consBody
        cases restAdmitted : admittedB rest with
        | false =>
            let failed := ("malformed", Atom.expression [.expression [.symbol "Some", replacementValue],
              .expression [.symbol "Some", keyValue], .symbol "None"]) :: bound
            apply case_returns program bound failed state state state pending
              (.expression [.expression [.symbol "Some", replacementValue], .expression [.symbol "Some", keyValue], .symbol "None"])
              (.symbol "None") _ _ innerCases (read_cases_encoded innerCases)
            · simpa [result, restAdmitted] using pendingRead
            · simp [innerCases, failed, bound, before, environment, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
                SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]
            · simpa [result, admittedB_cons, restAdmitted] using symbol_returns program failed state "None"
        | true =>
            let operands := [("tail", tail), ("variable", keyValue), ("value", replacementValue)] ++ bound
            apply case_returns program bound operands state state state pending
              (.expression [.expression [.symbol "Some", replacementValue], .expression [.symbol "Some", keyValue],
                .expression [.symbol "Some", tail]]) selected _ _ innerCases (read_cases_encoded innerCases)
            · simpa [result, restAdmitted, tail] using pendingRead
            · simp [innerCases, operands, bound, before, environment, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
                SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]
            · have equality : ((Atom.expression [.symbol "Some", typeAtom registeredOperatorAtom replacement.ty]) ==
                  (.expression [.symbol "Some", typeAtom registeredOperatorAtom key.ty])) = Ty.same replacement.ty key.ty := by
                apply Bool.eq_iff_iff.mpr
                simp only [beq_iff_eq, Ty.same_eq_true_iff, Atom.expression.injEq, List.cons.injEq, true_and, and_true]
                constructor
                · exact Representation.registered_typeAtom_injective world _ _ entryFormed.replacementType entryFormed.keyType
                · exact congrArg (typeAtom registeredOperatorAtom)
              unfold selected
              apply if_returns program operands state state state _ (boolean (Ty.same replacement.ty key.ty)) _ _ _
              · apply native_binary_call_returns program operands state state state state "==" _ _
                  (.expression [.symbol "Some", typeAtom registeredOperatorAtom replacement.ty])
                  (.expression [.symbol "Some", typeAtom registeredOperatorAtom key.ty]) _
                  (by decide) (by decide) (by decide) (by decide) _ _ _ (by decide)
                · exact TermJudgment.authored_term_type_return constants operands state [] replacement.canonical.term replacement.ty
                    replacement.canonical.checked "value" (by simp [operands, replacementValue, applySubst, Subst.lookup])
                · apply unary_constructor_of_returns program operands state state "Some" _ _ (by decide) (by decide)
                  simpa [operands, bound, applySubst, Subst.lookup] using variable_returns program operands state "type"
                · simp only [StdLib.structural_equality, equality]
              · cases mapletAdmitted : Ty.same replacement.ty key.ty with
                | false =>
                    simpa [result, admittedB_cons, mapletAdmitted, boolean] using symbol_returns program operands state "None"
                | true =>
                    simp only [boolean, BEq.rfl, ↓reduceIte]
                    have constructed : PureReturns program operands state
                        (.expression [.symbol "Some", .expression [.symbol "HOL:Cons",
                          .expression [.symbol "HOL:Entry", .var "variable", .var "value"], .var "tail"]]) state
                        (.expression [.symbol "Some", .expression [.symbol "HOL:Cons",
                          .expression [.symbol "HOL:Entry", keyValue, replacementValue], tail]]) := by
                      apply unary_constructor_of_returns program operands state state "Some" _ _ (by decide) (by decide)
                      apply binary_constructor_returns program operands state state state "HOL:Cons" _ _ _ _ (by decide) (by decide)
                      · simpa [operands, applySubst, Subst.lookup] using constructor_variables_return program operands state
                          "HOL:Entry" ["variable","value"] (by decide) (by decide)
                      · simpa [operands, applySubst, Subst.lookup] using variable_returns program operands state "tail"
                    simpa [result, admittedB_cons, mapletAdmitted, restAdmitted, substitutionEntries, TermSubstitution.table,
                      TermSubstitution.encodedEntries, Lookup.table, Premises.keys, replacementValue, keyValue, tail] using constructed

/-- The actual finite reader decides source maplet admission and retains its
ordered first-match table. Well-formed mismatched maplets return refusal. -/
theorem authored_read_maplets_return (world : DefinitionAdapters.TheoryContext) (table : DeclarationTable.Table world)
    (origins : TypeOp → Atom) (constants : Const → Atom) (axioms receipts : Atom) (cache : List (Atom × Atom))
    (entries : List Entry) (formed : ∀ entry ∈ entries, EntryFormed world.signature entry)
    (bindings : Subst) (state : State) (stateKey entriesKey : String)
    (stateCaptured : applySubst bindings (.var stateKey) = ProofLookup.sourceState
      (OperatorTable.tableAtom table.operators origins) (DeclarationTable.tableAtom table constants) axioms receipts cache)
    (entriesCaptured : applySubst bindings (.var entriesKey) = sourceAtom entries) :
    PureReturns program bindings state (.expression [.symbol "hol-light:read-maplets", .var stateKey, .var entriesKey]) state
      (result constants entries) := by
  apply authored_variable_call_returns program bindings
    (environment (ProofLookup.sourceState (OperatorTable.tableAtom table.operators origins)
      (DeclarationTable.tableAtom table constants) axioms receipts cache) (sourceAtom entries)) state state
    "hol-light:read-maplets" [stateKey, entriesKey] equation.body _ (by decide) (by decide) (by decide) _
    (body_returns world table origins constants axioms receipts cache entries formed state) (by decide)
  simpa only [List.map_cons, List.map_nil, stateCaptured, entriesCaptured] using clause _ (sourceAtom entries)

/-- A mismatched maplet anywhere in the complete list earns an actual
refusal, even when a prior entry would shadow it during substitution. -/
theorem authored_invalid_maplets_refused (world : DefinitionAdapters.TheoryContext) (table : DeclarationTable.Table world)
    (origins : TypeOp → Atom) (constants : Const → Atom) (axioms receipts : Atom) (cache : List (Atom × Atom))
    (entries : List Entry) (formed : ∀ entry ∈ entries, EntryFormed world.signature entry)
    (invalid : ¬ SourceSubstitution.TermMapletsAdmissible (sourceEntries entries))
    (bindings : Subst) (state : State) (stateKey entriesKey : String)
    (stateCaptured : applySubst bindings (.var stateKey) = ProofLookup.sourceState
      (OperatorTable.tableAtom table.operators origins) (DeclarationTable.tableAtom table constants) axioms receipts cache)
    (entriesCaptured : applySubst bindings (.var entriesKey) = sourceAtom entries) :
    PureReturns program bindings state (.expression [.symbol "hol-light:read-maplets", .var stateKey, .var entriesKey]) state
      (.symbol "None") := by
  have rejected : admittedB entries = false := Bool.eq_false_of_not_eq_true
    (fun accepted => invalid ((admittedB_eq_true_iff entries).mp accepted))
  simpa only [result, rejected, Bool.false_eq_true, ↓reduceIte] using authored_read_maplets_return world table origins
    constants axioms receipts cache entries formed bindings state stateKey entriesKey stateCaptured entriesCaptured

end Mettapedia.Languages.HOLLight.MeTTa.TermMapletReading
