import Mettapedia.Languages.HOLLight.MeTTa.Representation

/-!
# Capture-free term substitution by the authored HOL Light library

The input syntax and substitution action are those of the existing shared HOL
calculus. The execution theorem uses the quoted MeTTa body, finite first-match
lookup and contextual representations. Stored checked replacements retain their
free variables beneath abstractions and are not substituted a second time.
Type correctness of maplets is a separate admission obligation.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.HOLLight.MeTTa.TermSubstitution

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst matchAtom)
open Mettapedia.Languages.MeTTa.PeTTa
open Mettapedia.Languages.OpenTheory
open Eval
open Representation (termAtom variableAtom)
open TypeSubstitution (nameAtom typeAtom)
open Effects (State)
open SignatureFormation

private theorem free_annotation {signature : Signature} {sourceVar : SourceVar}
    (formed : AnnotationsFormed signature (.free sourceVar)) : TypeFormed signature sourceVar.ty := by
  cases formed with
  | free typeFormed => exact typeFormed

private theorem application_annotations {signature : Signature} {function argument : DBTerm}
    (formed : AnnotationsFormed signature (.app function argument)) :
    AnnotationsFormed signature function ∧ AnnotationsFormed signature argument := by
  cases formed with
  | app functionFormed argumentFormed => exact ⟨functionFormed, argumentFormed⟩

private theorem abstraction_annotations {signature : Signature} {domain : Ty} {body : DBTerm}
    (formed : AnnotationsFormed signature (.abs domain body)) :
    TypeFormed signature domain ∧ AnnotationsFormed signature body := by
  cases formed with
  | abs domainFormed bodyFormed => exact ⟨domainFormed, bodyFormed⟩

def encodedEntries (operators : TypeOp → Atom) (constants : Const → Atom)
    (entries : List (SourceVar × CheckedSourceTerm)) : List (Atom × Atom) :=
  entries.map fun entry => (variableAtom operators entry.1,
    termAtom operators constants [] entry.2.canonical.term)

def table (operators : TypeOp → Atom) (constants : Const → Atom)
    (entries : List (SourceVar × CheckedSourceTerm)) : Atom :=
  Lookup.table (encodedEntries operators constants entries)

/-- Representation changes preserve first-match lookup on the complete typed
variable identity, including duplicate maplets and exact identity maplets. -/
theorem lookup_encoded (operators : TypeOp → Atom) (constants : Const → Atom)
    (signature : Signature)
    (faithful : ∀ left right : SourceVar, TypeFormed signature left.ty → TypeFormed signature right.ty →
      (variableAtom operators left = variableAtom operators right ↔ left = right))
    (entries : List (SourceVar × CheckedSourceTerm))
    (entriesFormed : ∀ entry ∈ entries, TypeFormed signature entry.1.ty)
    (sourceVar : SourceVar) (variableFormed : TypeFormed signature sourceVar.ty) :
    (encodedEntries operators constants entries).lookup (variableAtom operators sourceVar) =
      ((TermSubst.mk TypeSubst.empty entries).lookup sourceVar).map
        (fun replacement => termAtom operators constants [] replacement.canonical.term) := by
  induction entries with
  | nil => rfl
  | cons entry rest ih =>
      rcases entry with ⟨key, replacement⟩
      simp only [encodedEntries, List.map_cons, List.lookup_cons, TermSubst.lookup,
        List.find?_cons, TermSubst.keySame, Option.map]
      have keys : (variableAtom operators sourceVar == variableAtom operators key) =
          sourceVarSame key sourceVar := by
        have keyFormed := entriesFormed (key, replacement) (by simp)
        apply Bool.eq_iff_iff.mpr
        simp only [beq_iff_eq, faithful sourceVar key variableFormed keyFormed,
          sourceVarSame_eq_true_iff]
        exact eq_comm
      rw [keys]
      have restFormed : ∀ entry ∈ rest, TypeFormed signature entry.1.ty :=
        fun entry member => entriesFormed entry (by simp [member])
      cases matched : sourceVarSame key sourceVar
      · simpa only [matched, Bool.false_eq_true, ↓reduceIte, encodedEntries,
          TermSubst.lookup, TermSubst.keySame, Option.map] using ih restFormed
      · rfl

private def equation : SpaceSemantics.Equation :=
  (syntaxSource.program.equations.filter
    (fun row => row.head == "hol-light:term-subst"))[0]'(by decide)

private def cases : SpaceSemantics.Cases :=
  match equation.body with
  | .expression [_, _, .expression rows] => (readCases rows).getD []
  | _ => []

private def freeBody : Atom :=
  .expression [.symbol "case", .expression [.symbol "hol-light:lookup", .var "term", .var "entries"],
    .expression [.expression [.expression [.symbol "Some", .var "replacement"], .var "replacement"],
      .expression [.var "absent", .var "term"]]]

private def freeCases : SpaceSemantics.Cases :=
  [(.expression [.symbol "Some", .var "replacement"], .var "replacement"), (.var "absent", .var "term")]

private def lambdaBody : Atom :=
  .expression [.symbol "HOL:Lam", .var "type",
    .expression [.symbol "hol-light:term-subst", .var "entries", .var "body"]]

private def applicationBody : Atom :=
  .expression [.symbol "HOL:App",
    .expression [.symbol "hol-light:term-subst", .var "entries", .var "function"],
    .expression [.symbol "hol-light:term-subst", .var "entries", .var "argument"]]

private def environment (operators : TypeOp → Atom) (constants : Const → Atom)
    (entries : List (SourceVar × CheckedSourceTerm)) (context : List Ty) (term : DBTerm) : Subst :=
  [("term", termAtom operators constants context term), ("entries", table operators constants entries)]

private theorem equation_unique :
    program.equations.filter (fun row => row.head == "hol-light:term-subst") = [equation] := by rfl

private theorem formals : equation.arguments = [.var "entries", .var "term"] := by decide

private theorem body_shape : equation.body =
    .expression [.symbol "case", .var "term",
      .expression (cases.map fun row => .expression [row.1, row.2])] := by decide

private theorem cases_shape : cases =
    [(.expression [.symbol "HOL:Free", .var "name", .var "type"], freeBody),
     (.expression [.symbol "HOL:Bound", .var "index", .var "type"], .var "term"),
     (.expression [.symbol "HOL:C", .var "identity", .var "type"], .var "term"),
     (.expression [.symbol "HOL:Lam", .var "type", .var "body"], lambdaBody),
     (.expression [.symbol "HOL:App", .var "function", .var "argument"], applicationBody),
     (.var "malformed", .symbol "None")] := by decide

private theorem free_body_shape : freeBody =
    .expression [.symbol "case", .expression [.symbol "hol-light:lookup", .var "term", .var "entries"],
      .expression (freeCases.map fun row => .expression [row.1, row.2])] := rfl

private theorem clause (operators : TypeOp → Atom) (constants : Const → Atom)
    (entries : List (SourceVar × CheckedSourceTerm)) (context : List Ty) (term : DBTerm) :
    clauses program "hol-light:term-subst" [table operators constants entries, termAtom operators constants context term] =
      [.evaluate (environment operators constants entries context term) equation.body] := by
  rw [clauses_use_only_the_named_equations, equation_unique]
  simp [formals, environment, SpaceSemantics.matchValue,
    SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]

private theorem body_returns (operators : TypeOp → Atom) (constants : Const → Atom)
    (signature : Signature)
    (faithful : ∀ left right : SourceVar, TypeFormed signature left.ty → TypeFormed signature right.ty →
      (variableAtom operators left = variableAtom operators right ↔ left = right))
    (entries : List (SourceVar × CheckedSourceTerm))
    (entriesFormed : ∀ entry ∈ entries, TypeFormed signature entry.1.ty)
    (term : DBTerm) (formed : AnnotationsFormed signature term) (context : List Ty) (state : State) :
    PureReturns program (environment operators constants entries context term) state equation.body state
      (termAtom operators constants context ((TermSubst.mk TypeSubst.empty entries).applyDB term)) := by
  rw [body_shape]
  cases term with
  | free sourceVar =>
      let bound := [("type", typeAtom operators sourceVar.ty), ("name", nameAtom sourceVar.name)] ++
        environment operators constants entries context (.free sourceVar)
      apply case_returns program (environment operators constants entries context (.free sourceVar)) bound
        state state state (.var "term") (variableAtom operators sourceVar) freeBody
        _ _ cases (read_cases_encoded cases)
      · simpa [environment, termAtom, applySubst, Subst.lookup] using
          variable_returns program (environment operators constants entries context (.free sourceVar)) state "term"
      · simp [cases_shape, bound, environment, termAtom, variableAtom,
          SpaceSemantics.selectCase, SpaceSemantics.matchValue,
          SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]
      · rw [free_body_shape]
        have lookupRun := Lookup.authored_lookup_return bound state (variableAtom operators sourceVar)
          (encodedEntries operators constants entries) "term" "entries"
          (by simp [bound, environment, termAtom, applySubst, Subst.lookup])
          (by simp [bound, environment, table, applySubst, Subst.lookup])
        rw [lookup_encoded operators constants signature faithful entries entriesFormed sourceVar
          (free_annotation formed)] at lookupRun
        cases found : (TermSubst.mk TypeSubst.empty entries).lookup sourceVar with
        | none =>
            let selected := ("absent", Atom.symbol "None") :: bound
            apply case_returns program bound selected state state state
              (.expression [.symbol "hol-light:lookup", .var "term", .var "entries"])
              (.symbol "None") (.var "term") _ _ freeCases (read_cases_encoded freeCases)
            · simpa [found, Lookup.answer] using lookupRun
            · simp [freeCases, selected, bound, environment,
                SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom, Subst.lookup]
            · simpa [TermSubst.applyDB, TypeSubst.applyVar, found, termAtom,
                selected, bound, environment, applySubst, Subst.lookup] using
                variable_returns program selected state "term"
        | some replacement =>
            let value := termAtom operators constants [] replacement.canonical.term
            let selected := ("replacement", value) :: bound
            apply case_returns program bound selected state state state
              (.expression [.symbol "hol-light:lookup", .var "term", .var "entries"])
              (.expression [.symbol "Some", value]) (.var "replacement") _ _ freeCases (read_cases_encoded freeCases)
            · simpa [found, Lookup.answer, value] using lookupRun
            · simp [freeCases, selected, value, bound, environment,
                SpaceSemantics.selectCase, SpaceSemantics.matchValue,
                SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]
            · rw [TermSubst.applyDB_free_of_lookup_some _ _ replacement
                (by simpa [TypeSubst.applyVar] using found),
                Representation.checked_replacement_context_independent]
              simpa [selected, bound, environment, applySubst, Subst.lookup, value] using
                variable_returns program selected state "replacement"
  | bound index =>
      let annotation := ((context[index]?).map (typeAtom operators)).getD (.symbol "None")
      let bound := [("type", annotation), ("index", Atom.grounded (.int index))] ++
        environment operators constants entries context (.bound index)
      apply case_returns program (environment operators constants entries context (.bound index)) bound
        state state state (.var "term") (termAtom operators constants context (.bound index)) (.var "term")
        _ _ cases (read_cases_encoded cases)
      · exact variable_returns program _ state "term"
      · simp [cases_shape, bound, annotation, environment, termAtom,
          SpaceSemantics.selectCase, SpaceSemantics.matchValue,
          SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]
      · simpa [bound, environment, applySubst, Subst.lookup] using variable_returns program bound state "term"
  | const constant type =>
      let bound := [("type", typeAtom operators type), ("identity", constants constant)] ++
        environment operators constants entries context (.const constant type)
      apply case_returns program (environment operators constants entries context (.const constant type)) bound
        state state state (.var "term") (termAtom operators constants context (.const constant type)) (.var "term")
        _ _ cases (read_cases_encoded cases)
      · exact variable_returns program _ state "term"
      · simp [cases_shape, bound, environment, termAtom,
          SpaceSemantics.selectCase, SpaceSemantics.matchValue,
          SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]
      · simpa [bound, environment, applySubst, Subst.lookup] using variable_returns program bound state "term"
  | abs domain body =>
      let bound := [("body", termAtom operators constants (domain :: context) body), ("type", typeAtom operators domain)] ++
        environment operators constants entries context (.abs domain body)
      apply case_returns program (environment operators constants entries context (.abs domain body)) bound
        state state state (.var "term") (termAtom operators constants context (.abs domain body)) lambdaBody
        _ _ cases (read_cases_encoded cases)
      · exact variable_returns program _ state "term"
      · simp [cases_shape, bound, environment, termAtom,
          SpaceSemantics.selectCase, SpaceSemantics.matchValue,
          SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]
      · simp only [TermSubst.applyDB_abs, TypeSubst.apply_empty, termAtom]
        unfold lambdaBody
        apply binary_constructor_returns program bound state state state "HOL:Lam" (.var "type")
          (.expression [.symbol "hol-light:term-subst", .var "entries", .var "body"])
          (typeAtom operators domain)
          (termAtom operators constants (domain :: context) ((TermSubst.mk TypeSubst.empty entries).applyDB body))
          (by decide) (by decide)
        · simpa [bound, environment, applySubst, Subst.lookup] using variable_returns program bound state "type"
        · apply authored_variable_call_returns program bound
            (environment operators constants entries (domain :: context) body) state state "hol-light:term-subst"
            ["entries", "body"] equation.body _ (by decide) (by decide) (by decide) _
            (body_returns operators constants signature faithful entries entriesFormed body
              (abstraction_annotations formed).2 (domain :: context) state) (by decide)
          simpa [bound, environment, applySubst, Subst.lookup] using clause operators constants entries (domain :: context) body
  | app function argument =>
      let bound := [("argument", termAtom operators constants context argument), ("function", termAtom operators constants context function)] ++
        environment operators constants entries context (.app function argument)
      apply case_returns program (environment operators constants entries context (.app function argument)) bound
        state state state (.var "term") (termAtom operators constants context (.app function argument)) applicationBody
        _ _ cases (read_cases_encoded cases)
      · exact variable_returns program _ state "term"
      · simp [cases_shape, bound, environment, termAtom,
          SpaceSemantics.selectCase, SpaceSemantics.matchValue,
          SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]
      · simp only [TermSubst.applyDB_app, termAtom]
        unfold applicationBody
        apply binary_constructor_returns program bound state state state "HOL:App"
          (.expression [.symbol "hol-light:term-subst", .var "entries", .var "function"])
          (.expression [.symbol "hol-light:term-subst", .var "entries", .var "argument"])
          (termAtom operators constants context ((TermSubst.mk TypeSubst.empty entries).applyDB function))
          (termAtom operators constants context ((TermSubst.mk TypeSubst.empty entries).applyDB argument))
          (by decide) (by decide)
        · apply authored_variable_call_returns program bound (environment operators constants entries context function)
            state state "hol-light:term-subst" ["entries", "function"] equation.body _
            (by decide) (by decide) (by decide) _
            (body_returns operators constants signature faithful entries entriesFormed function
              (application_annotations formed).1 context state) (by decide)
          simpa [bound, environment, applySubst, Subst.lookup] using clause operators constants entries context function
        · apply authored_variable_call_returns program bound (environment operators constants entries context argument)
            state state "hol-light:term-subst" ["entries", "argument"] equation.body _
            (by decide) (by decide) (by decide) _
            (body_returns operators constants signature faithful entries entriesFormed argument
              (application_annotations formed).2 context state) (by decide)
          simpa [bound, environment, applySubst, Subst.lookup] using clause operators constants entries context argument
termination_by sizeOf term

/-- Every finite declaration-formed canonical term is substituted by execution of the quoted
library. This law alone does not authorize an unchecked substitution map. -/
theorem authored_term_substitution_return (operators : TypeOp → Atom) (constants : Const → Atom)
    (signature : Signature)
    (faithful : ∀ left right : SourceVar, TypeFormed signature left.ty → TypeFormed signature right.ty →
      (variableAtom operators left = variableAtom operators right ↔ left = right))
    (bindings : Subst) (state : State) (entries : List (SourceVar × CheckedSourceTerm))
    (entriesFormed : ∀ entry ∈ entries, TypeFormed signature entry.1.ty)
    (context : List Ty) (term : DBTerm) (formed : AnnotationsFormed signature term)
    (entriesKey termKey : String)
    (capturedEntries : applySubst bindings (.var entriesKey) = table operators constants entries)
    (capturedTerm : applySubst bindings (.var termKey) = termAtom operators constants context term) :
    PureReturns program bindings state
      (.expression [.symbol "hol-light:term-subst", .var entriesKey, .var termKey]) state
      (termAtom operators constants context ((TermSubst.mk TypeSubst.empty entries).applyDB term)) := by
  apply authored_variable_call_returns program bindings (environment operators constants entries context term)
    state state "hol-light:term-subst" [entriesKey, termKey] equation.body _
    (by decide) (by decide) (by decide) _
    (body_returns operators constants signature faithful entries entriesFormed term formed context state) (by decide)
  simpa only [List.map_cons, List.map_nil, capturedEntries, capturedTerm] using clause operators constants entries context term

/-- The registered HOL Light context discharges key faithfulness by its actual
name uniqueness laws. No representation-soundness interface is assumed. -/
theorem authored_registered_term_substitution_return (theory : DefinitionAdapters.TheoryContext)
    (constants : Const → Atom) (bindings : Subst) (state : State)
    (entries : List (SourceVar × CheckedSourceTerm))
    (entriesFormed : ∀ entry ∈ entries, TypeFormed theory.signature entry.1.ty)
    (context : List Ty) (term : DBTerm) (formed : AnnotationsFormed theory.signature term)
    (entriesKey termKey : String)
    (capturedEntries : applySubst bindings (.var entriesKey) = table Representation.registeredOperatorAtom constants entries)
    (capturedTerm : applySubst bindings (.var termKey) = termAtom Representation.registeredOperatorAtom constants context term) :
    PureReturns program bindings state
      (.expression [.symbol "hol-light:term-subst", .var entriesKey, .var termKey]) state
      (termAtom Representation.registeredOperatorAtom constants context
        ((TermSubst.mk TypeSubst.empty entries).applyDB term)) := by
  exact authored_term_substitution_return Representation.registeredOperatorAtom constants theory.signature
    (Representation.registered_variableAtom_eq_iff theory) bindings state entries entriesFormed context term formed
    entriesKey termKey capturedEntries capturedTerm

/-- Execution and the existing strict substitution admission meet on the
same result. Every maplet, including a shadowed or unused maplet, is subject
to the source's type-correctness obligation. -/
theorem authored_admitted_substitution_preserves_typing
    (theory : DefinitionAdapters.TheoryContext) (constants : Const → Atom)
    (bindings : Subst) (state : State) (maplets : List SourceSubstitution.TermMaplet)
    (admitted : SourceSubstitution.TermMapletsAdmissible maplets)
    (keysFormed : ∀ entry ∈ SourceSubstitution.termEntries maplets, TypeFormed theory.signature entry.1.ty)
    (context : List Ty) (term : DBTerm) (type : Ty)
    (formed : AnnotationsFormed theory.signature term) (checked : term.inferType context = some type)
    (entriesKey termKey : String)
    (capturedEntries : applySubst bindings (.var entriesKey) =
      table Representation.registeredOperatorAtom constants (SourceSubstitution.termEntries maplets))
    (capturedTerm : applySubst bindings (.var termKey) =
      termAtom Representation.registeredOperatorAtom constants context term) :
    PureReturns program bindings state
      (.expression [.symbol "hol-light:term-subst", .var entriesKey, .var termKey]) state
      (termAtom Representation.registeredOperatorAtom constants context
        ((SourceSubstitution.termSubstitution maplets).applyDB term)) ∧
    ((SourceSubstitution.termSubstitution maplets).applyDB term).inferType context = some type := by
  constructor
  · exact authored_registered_term_substitution_return theory constants bindings state
      (SourceSubstitution.termEntries maplets) keysFormed context term formed entriesKey termKey capturedEntries capturedTerm
  · have identity : TypeSubst.empty.apply = id := funext TypeSubst.apply_empty
    simpa only [SourceSubstitution.termSubstitution, identity, List.map_id, id_eq] using
      TermSubst.inferType_applyDB (SourceSubstitution.termSubstitution_typeCorrect maplets admitted) checked

end Mettapedia.Languages.HOLLight.MeTTa.TermSubstitution
