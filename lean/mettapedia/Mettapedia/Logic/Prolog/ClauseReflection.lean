import Mettapedia.Logic.Prolog.ReaderSource

/-!
# Checked reflection of canonical Prolog clauses

Database predicates need the ordinary clause term that preceded typed control
classification. `Clause.sourceTerm` retains that term, but it is deliberately
optional and public: hand-built LP fixtures need not pretend to have source
provenance. This module is the fail-closed consumer boundary. It reclassifies
the retained term through `ReaderSource` and compares a complete finite code of
the result with the executable clause before returning any reflective data.

The codes below are not another syntax or evaluator. They are prefix-token
observations of the one canonical `Logic.LP`/`Logic.Prolog` values, used only
to obtain executable equality at this boundary. Every compound/control marker
carries or determines its child count, so no constructor, symbol, argument,
or variable identity is omitted.
-/

namespace Mettapedia.Logic.Prolog.ClauseReflection

open SourceSignature

/-- One token in a complete prefix observation of a concrete source term.
The application symbol carries its declared arity, which determines exactly
how many following term encodings belong to it. -/
inductive TermToken where
  | var (identity : Variable)
  | const (value : Constant)
  | app (symbol : CompoundIndicator)
deriving DecidableEq, Repr

/-- Prefix encoding of the dependent canonical term. -/
def termCode : SourceSignature.Term → List TermToken
  | .var identity => [.var identity]
  | .const value => [.const value]
  | .app symbol arguments =>
      .app symbol ::
        (List.ofFn fun index => termCode (arguments index)).flatten

/-- Complete finite observation of one canonical atom. Argument boundaries
remain explicit as a list of term-token lists. -/
structure AtomCode where
  symbol : PredicateIndicator
  arguments : List (List TermToken)
deriving DecidableEq, Repr

def atomCode (atom : SourceSignature.Atom) : AtomCode := {
  symbol := atom.symbol
  arguments := List.ofFn fun index => termCode (atom.args index)
}

/-- One token in a complete prefix observation of typed Prolog control.
Recursive control markers have fixed child counts. Data-bearing constructors
carry complete term/atom codes directly. -/
inductive GoalToken where
  | call (atom : AtomCode)
  | succeed
  | fail
  | cut
  | conj
  | disj
  | ifThenElse
  | softIfThenElse
  | once
  | neg
  | unify (left right : List TermToken)
  | notUnify (left right : List TermToken)
  | isVar (term : List TermToken)
  | findall (template bag : List TermToken)
  | catch (catcher : List TermToken)
  | throw (ball : List TermToken)
deriving DecidableEq, Repr

def goalCode : SourceSignature.Goal → List GoalToken
  | .call atom => [.call (atomCode atom)]
  | .succeed => [.succeed]
  | .fail => [.fail]
  | .cut => [.cut]
  | .conj left right => .conj :: goalCode left ++ goalCode right
  | .disj left right => .disj :: goalCode left ++ goalCode right
  | .ifThenElse condition thenBranch elseBranch =>
      .ifThenElse :: goalCode condition ++ goalCode thenBranch ++
        goalCode elseBranch
  | .softIfThenElse condition thenBranch elseBranch =>
      .softIfThenElse :: goalCode condition ++ goalCode thenBranch ++
        goalCode elseBranch
  | .once goal => .once :: goalCode goal
  | .neg goal => .neg :: goalCode goal
  | .unify left right => [.unify (termCode left) (termCode right)]
  | .notUnify left right => [.notUnify (termCode left) (termCode right)]
  | .isVar term => [.isVar (termCode term)]
  | .findall template generator bag =>
      .findall (termCode template) (termCode bag) :: goalCode generator
  | .catch guarded catcher recovery =>
      .catch (termCode catcher) :: goalCode guarded ++ goalCode recovery
  | .throw ball => [.throw (termCode ball)]

/-- Complete finite observation of the executable part of one clause.
The optional provenance field is intentionally excluded: it is the data being
checked, not part of the claimed agreement. -/
structure ClauseCode where
  head : AtomCode
  body : List GoalToken
deriving DecidableEq, Repr

def clauseCode (clause : SourceSignature.Clause) : ClauseCode := {
  head := atomCode clause.head
  body := goalCode clause.body
}

/-- Reclassify retained source data and release it only when its complete
executable code agrees with the clause that would be affected. -/
def reflect? (clause : SourceSignature.Clause) : Option SourceSignature.Term :=
  match clause.sourceTerm with
  | none => none
  | some source =>
      match ReaderSource.classify source with
      | .ok (.clause replayed) =>
          if clauseCode replayed = clauseCode clause then some source else none
      | _ => none

/-- A clause built from a successful head/body classification passes the
reflection check for that exact normalized source term. -/
theorem reflect?_normalizedClause
    {head body : SourceSignature.Term}
    {parsedHead : SourceSignature.Atom}
    {parsedBody : SourceSignature.Goal}
    (hHead : ReaderSource.toHead head = .ok parsedHead)
    (hBody : ReaderSource.toGoal body = .ok parsedBody) :
    reflect? {
      head := parsedHead
      body := parsedBody
      sourceTerm := some (ReaderSource.normalizedClauseTerm head body)
    } = some (ReaderSource.normalizedClauseTerm head body) := by
  simp [reflect?, ReaderSource.classify_normalizedClauseTerm hHead hBody,
    clauseCode]

/-- Successful reflection exposes both the retained field and a real
reclassification whose complete executable code agrees with the clause. -/
theorem reflect?_eq_some {clause : SourceSignature.Clause}
    {source : SourceSignature.Term}
    (hReflect : reflect? clause = some source) :
    clause.sourceTerm = some source ∧
      ∃ replayed, ReaderSource.classify source = .ok (.clause replayed) ∧
        clauseCode replayed = clauseCode clause := by
  unfold reflect? at hReflect
  cases hSource : clause.sourceTerm with
  | none => simp [hSource] at hReflect
  | some retained =>
      cases hClassify : ReaderSource.classify retained with
      | error error => simp [hSource, hClassify] at hReflect
      | ok form =>
          cases form with
          | clause replayed =>
              by_cases hCode : clauseCode replayed = clauseCode clause
              · simp [hSource, hClassify, hCode] at hReflect
                cases hReflect
                exact ⟨rfl, replayed, hClassify, hCode⟩
              · simp [hSource, hClassify, hCode] at hReflect
          | directive goal => simp [hSource, hClassify] at hReflect
          | query goal => simp [hSource, hClassify] at hReflect
          | dcg head body => simp [hSource, hClassify] at hReflect

end Mettapedia.Logic.Prolog.ClauseReflection
