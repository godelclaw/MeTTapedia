import Mettapedia.Logic.Prolog.ReaderProgram

namespace Mettapedia.Logic.Prolog.ReaderProgramRegression

open ReaderOperator ReaderProgram SourceSignature

private def emptyImports : ReaderDirective.ImportProfile Unit :=
  fun _ => .ok []

private def clauseNames (program : SourceSignature.Program) : List String :=
  program.map fun clause => clause.head.symbol.name

/-- Strict loading connects reader output to the executable program without
reordering or deduplicating source clauses. -/
def clausesEnterCanonicalProgram : Bool :=
  match ReaderProgram.loadSourceWith
      (ReaderDirective.effectWith emptyImports) defaults
      "p(a). p(b). choose(X) :- p(X), !." with
  | .ok result => clauseNames result.program == ["p", "p", "choose"]
  | .error _ => false

/-- A directive may affect later parsing, but it cannot disappear across the
executable-program boundary before directive execution exists. -/
def directiveIsNotSilentlyDiscarded : Bool :=
  match ReaderProgram.loadSourceWith
      (ReaderDirective.effectWith emptyImports) defaults
      ":- op(500, xfy, likes). a likes b." with
  | .error (.nonClause 0 .directive) => true
  | _ => false

/-- A DCG rule is expanded in place to an ordinary predicate with two added
difference-list arguments. -/
def dcgEntersCanonicalProgram : Bool :=
  match ReaderProgram.loadSourceWith
      (ReaderDirective.effectWith emptyImports) defaults
      "sequence --> item, sequence." with
  | .ok result =>
      match result.program with
      | [clause] =>
          clause.head.symbol.name = "sequence" &&
            clause.head.symbol.arity = 2
      | _ => false
  | _ => false

/-- Queries are requests to execute, not database clauses. -/
def queryIsNotSilentlyInserted : Bool :=
  match ReaderProgram.loadSourceWith
      (ReaderDirective.effectWith emptyImports) defaults
      "?- p(X)." with
  | .error (.nonClause 0 .query) => true
  | _ => false

#guard clausesEnterCanonicalProgram
#guard directiveIsNotSilentlyDiscarded
#guard dcgEntersCanonicalProgram
#guard queryIsNotSilentlyInserted

end Mettapedia.Logic.Prolog.ReaderProgramRegression
