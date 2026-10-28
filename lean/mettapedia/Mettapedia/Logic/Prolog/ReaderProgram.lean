import Mettapedia.Logic.Prolog.ReaderDirective
import Mettapedia.Logic.Prolog.ReaderDCG

/-!
# Strict Prolog program loading and DCG expansion

`ReaderLoader` returns classified source forms in source order. This module
connects its clause-only fragment directly to the canonical
`Logic.Prolog.Program` consumed by the shared runtime.

DCG rules are expanded to ordinary canonical clauses before admission.
Directives and queries remain deliberately strict: they are reported with
their source-form position rather than silently discarded.
-/

namespace Mettapedia.Logic.Prolog.ReaderProgram

open ReaderOperator ReaderSource SourceSignature

/-- The kind of non-clause form that prevented strict program admission. -/
inductive NonClauseKind where
  | directive
  | query
deriving DecidableEq, Repr

/-- Strict loading distinguishes reader failure from a successfully read form
that still needs a loader phase. -/
inductive Error (epsilon : Type) where
  | reader (error : ReaderLoader.Error epsilon)
  | nonClause (position : Nat) (kind : NonClauseKind)
  | dcg (position : Nat) (error : ReaderDCG.Error)

/-- A clause-only source buffer and the final read-time operator table. -/
structure Result where
  program : SourceSignature.Program
  operators : ReaderOperator.Table

private def clausesAux : Nat -> List ReaderSource.Form ->
    Except (Error epsilon) SourceSignature.Program
  | _, [] => .ok []
  | position, .clause clause :: rest => do
      let tail <- clausesAux (position + 1) rest
      pure (clause :: tail)
  | position, .directive _ :: _ =>
      .error (.nonClause position .directive)
  | position, .query _ :: _ =>
      .error (.nonClause position .query)
  | position, .dcg head body :: rest => do
      let clause <- (ReaderDCG.expand head body).mapError (.dcg position)
      let tail <- clausesAux (position + 1) rest
      pure (clause :: tail)

/-- Admit ordinary clauses directly and DCG rules through canonical
expansion. Clause order is unchanged. -/
def ofForms (forms : List ReaderSource.Form) :
    Except (Error epsilon) SourceSignature.Program :=
  clausesAux 0 forms

/-- Sequentially read one source buffer and admit its clause/DCG fragment.
Read-time effects may update operators, but do not consume or execute ordinary
directives. -/
def loadSourceWith (effect : ReaderLoader.Effect epsilon)
    (operators : ReaderOperator.Table) (source : String) :
    Except (Error epsilon) Result := do
  let loaded <- (ReaderLoader.loadSourceWith effect operators source).mapError
    .reader
  let program <- ofForms loaded.forms
  pure { program, operators := loaded.operators }

private theorem clausesAux_clause_map (position : Nat)
    (clauses : SourceSignature.Program) :
    clausesAux (epsilon := epsilon) position
        (clauses.map ReaderSource.Form.clause) = .ok clauses := by
  induction clauses generalizing position with
  | nil => rfl
  | cons clause rest inductionHypothesis =>
      simp only [List.map_cons, clausesAux]
      rw [inductionHypothesis (position + 1)]
      rfl

@[simp]
theorem ofForms_clause_map (clauses : SourceSignature.Program) :
    ofForms (epsilon := epsilon) (clauses.map ReaderSource.Form.clause) =
      .ok clauses :=
  clausesAux_clause_map 0 clauses

end Mettapedia.Logic.Prolog.ReaderProgram
