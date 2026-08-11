import Mettapedia.Logic.Prolog.ReaderUnit

namespace Mettapedia.Logic.Prolog.ReaderUnitRegression

open ReaderOperator ReaderUnit SourceSignature

private def emptyImports : ReaderDirective.ImportProfile _root_.Unit :=
  fun _ => .ok []

private def load (source : String) : Option ReaderUnit.Unit :=
  match ReaderUnit.loadSourceWith
      (ReaderDirective.effectWith emptyImports) defaults source with
  | .ok unit => some unit
  | .error _ => none

private def atomName? : SourceSignature.Term -> Option String
  | .const (.atom name) => some name
  | _ => none

private def compoundName? : SourceSignature.Term -> Option String
  | .app indicator _ => some indicator.name
  | _ => none

/-- Module metadata, import requests, declarations, initializers, ordinary
load goals, and expanded clauses all survive in source order. -/
def sourceOrderAndObligationsAreRetained : Bool :=
  match load
      ":- module(parser, [run/1]).\n\
       :- use_module(library(dcg/basics)).\n\
       :- dynamic cache/1.\n\
       :- initialization(setup).\n\
       :- set_prolog_flag(answer_write_options, []).\n\
       token --> [a].\n\
       run(X) :- token(X, [])." with
  | none => false
  | some unit =>
      match unit.items with
      | [ .directive (.moduleDecl moduleDecl),
          .directive (.import request),
          .directive (.declaration _),
          .directive (.initialization _),
          .directive (.loadGoal _),
          .clause dcgClause,
          .clause runClause ] =>
          atomName? moduleDecl.name == some "parser" &&
            request.kind == .useModule &&
            compoundName? request.source == some "library" &&
            request.options.isEmpty &&
            dcgClause.head.symbol.name == "token" &&
            dcgClause.head.symbol.arity == 2 &&
            runClause.head.symbol.name == "run" &&
            runClause.head.symbol.arity == 1 &&
            unit.program.length == 2 &&
            unit.imports.length == 1 &&
            unit.declarations.length == 1 &&
            match unit.pendingGoals with
            | [.call initialization, .call loadGoal] =>
                initialization.symbol.name == "setup" &&
                  loadGoal.symbol.name == "set_prolog_flag"
            | _ => false
      | _ => false

#guard sourceOrderAndObligationsAreRetained

/-- Extracting the executable initializer does not discard the optional SWI
loader-timing argument. -/
def initializationTimingIsRetained : Bool :=
  match load ":- initialization(setup, after_load)." with
  | some unit =>
      match unit.directives, unit.pendingGoals with
      | [.initialization value], [.call goal] =>
          value.when.bind atomName? == some "after_load" &&
            goal.symbol.name == "setup"
      | _, _ => false
  | none => false

#guard initializationTimingIsRetained

/-- A query is an execution request and cannot be laundered into a source
unit.  Its exact source-form position remains visible. -/
def queryFailsAtItsSourcePosition : Bool :=
  match ReaderUnit.loadSourceWith
      (ReaderDirective.effectWith emptyImports) defaults
      "p. ?- p." with
  | .error (.query 1) => true
  | _ => false

#guard queryFailsAtItsSourcePosition

/-- A recognized loader directive with the wrong arity is an error, not an
ordinary load goal that could later be ignored. -/
def malformedRecognizedDirectiveFailsClosed : Bool :=
  match ReaderUnit.loadSourceWith
      (ReaderDirective.effectWith emptyImports) defaults
      ":- ensure_loaded(a, b)." with
  | .error (.malformedDirective 0 "ensure_loaded") => true
  | _ => false

#guard malformedRecognizedDirectiveFailsClosed

def excessiveImportArityFailsClosed : Bool :=
  match ReaderUnit.loadSourceWith
      (ReaderDirective.effectWith emptyImports) defaults
      ":- use_module(a, b, c)." with
  | .error (.malformedDirective 0 "use_module") => true
  | _ => false

#guard excessiveImportArityFailsClosed

def groupedDeclarationsRemainDeclarations : Bool :=
  match load
      ":- meta_predicate first(0), second(1)." with
  | some unit => unit.declarations.length == 1 && unit.pendingGoals.isEmpty
  | none => false

#guard groupedDeclarationsRemainDeclarations

end Mettapedia.Logic.Prolog.ReaderUnitRegression
