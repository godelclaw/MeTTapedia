import Mettapedia.Logic.Prolog.ReaderSource
import Mettapedia.Logic.Prolog.ReaderTermRegression

namespace Mettapedia.Logic.Prolog.ReaderSourceRegression

open ReaderOperator ReaderSource SourceSignature

inductive GoalShape where
  | call (name : String) (arity : Nat)
  | succeed | fail | cut
  | conj (left right : GoalShape)
  | disj (left right : GoalShape)
  | ifThenElse (condition thenBranch elseBranch : GoalShape)
  | softIfThenElse (condition thenBranch elseBranch : GoalShape)
  | once (goal : GoalShape)
  | neg (goal : GoalShape)
  | unify | notUnify | isVar
  | findall (generator : GoalShape)
  | catch (guarded recovery : GoalShape)
  | throw
deriving BEq, Repr

def goalShape : SourceSignature.Goal -> GoalShape
  | .call atom => .call atom.symbol.name atom.symbol.arity
  | .succeed => .succeed
  | .fail => .fail
  | .cut => .cut
  | .conj left right => .conj (goalShape left) (goalShape right)
  | .disj left right => .disj (goalShape left) (goalShape right)
  | .ifThenElse condition thenBranch elseBranch =>
      .ifThenElse (goalShape condition) (goalShape thenBranch)
        (goalShape elseBranch)
  | .softIfThenElse condition thenBranch elseBranch =>
      .softIfThenElse (goalShape condition) (goalShape thenBranch)
        (goalShape elseBranch)
  | .once goal => .once (goalShape goal)
  | .neg goal => .neg (goalShape goal)
  | .unify _ _ => .unify
  | .notUnify _ _ => .notUnify
  | .isVar _ => .isVar
  | .findall _ generator _ => .findall (goalShape generator)
  | .catch guarded _ recovery => .catch (goalShape guarded) (goalShape recovery)
  | .throw _ => .throw

inductive FormShape where
  | clause (name : String) (arity : Nat) (body : GoalShape)
  | directive (goal : GoalShape)
  | query (goal : GoalShape)
  | dcg
deriving BEq, Repr

def formShape : Form -> FormShape
  | .clause clause =>
      .clause clause.head.symbol.name clause.head.symbol.arity
        (goalShape clause.body)
  | .directive goal => .directive (goalShape goal)
  | .query goal => .query (goalShape goal)
  | .dcg _ _ => .dcg

def readShape (source : String) : Option FormShape :=
  match ReaderTerm.readOne defaults source with
  | .error _ => none
  | .ok result =>
      match classify result.term with
      | .error _ => none
      | .ok form => some (formShape form)

#guard readShape "p(X) :- q(X), !." == some (.clause "p" 1
  (.conj (.call "q" 1) .cut))

#guard readShape "fact(a)." == some (.clause "fact" 1 .succeed)

#guard readShape ":- use_module(library(clpfd))." == some
  (.directive (.call "use_module" 1))

#guard readShape "?- p(X)." == some (.query (.call "p" 1))

#guard readShape "sequence --> item, sequence." == some .dcg

#guard readShape "p :- (a -> b ; c)." == some (.clause "p" 0
  (.ifThenElse (.call "a" 0) (.call "b" 0) (.call "c" 0)))

#guard readShape "p :- (a *-> b ; c)." == some (.clause "p" 0
  (.softIfThenElse (.call "a" 0) (.call "b" 0) (.call "c" 0)))

#guard readShape "p :- once(a), \\+ b, X = y, X \\= z, var(X)." == some
  (.clause "p" 0 (.conj (.once (.call "a" 0))
    (.conj (.neg (.call "b" 0))
      (.conj .unify (.conj .notUnify .isVar)))))

#guard readShape "p :- findall(X, q(X), Xs), catch(r, E, throw(E))." == some
  (.clause "p" 0 (.conj (.findall (.call "q" 1))
    (.catch (.call "r" 0) .throw)))

-- A variable in goal position is the ISO meta-call `call/1`, represented as
-- an ordinary canonical predicate call until that builtin executes.
#guard readShape "p :- Goal." == some (.clause "p" 0 (.call "call" 1))

#guard readShape "1." == none

def readClauseSourceTerm (source : String) : Option SourceSignature.Term := do
  let result <- (ReaderTerm.readOne defaults source).toOption
  let form <- (classify result.term).toOption
  match form with
  | .clause clause => clause.sourceTerm
  | _ => none

def sourceTermExact (source : String) (expected : SourceSignature.Term) : Bool :=
  match readClauseSourceTerm source with
  | some actual =>
      ReaderTermRegression.shape actual == ReaderTermRegression.shape expected
  | none => false

-- Facts are normalized to the same explicit `Head :- true` data shape that
-- `retract/1` matches in SWI, rather than retaining an execution-only AST.
#guard sourceTermExact "fact(a)." (normalizedClauseTerm
  (compound "fact" [atom "a"]) (atom "true"))

-- The original control spelling is retained before typed classification
-- forgets that the left child of `;/2` was syntactically `->/2`.
#guard sourceTermExact "p :- (a -> b ; c)." (normalizedClauseTerm
  (atom "p")
  (compound ";" [compound "->" [atom "a", atom "b"], atom "c"]))

def sourceTermReclassifies (source : String) : Bool :=
  match ReaderTerm.readOne defaults source with
  | .error _ => false
  | .ok result =>
      match classify result.term with
      | .ok (.clause original) =>
          match original.sourceTerm with
          | none => false
          | some normalized =>
              match classify normalized with
              | .ok (.clause replayed) =>
                  formShape (.clause original) == formShape (.clause replayed) &&
                    replayed.sourceTerm.map ReaderTermRegression.shape ==
                      some (ReaderTermRegression.shape normalized)
              | _ => false
      | _ => false

#guard sourceTermReclassifies
  "p(X) :- (q(X), ! ; catch(r(X), E, throw(E)))."

def ambiguousControlShape : Option GoalShape :=
  match toGoal (compound ";" [
      compound "->" [atom "a", atom "b"], atom "c"]) with
  | .ok goal => some (goalShape goal)
  | .error _ => none

-- A total typed-AST reifier would be unsound: this ordinary term is
-- necessarily classified as hard if-then-else, not as a `disj` whose left
-- call happens to be named `->/2`. Retaining the source term is therefore
-- load-bearing rather than duplicate data.
#guard ambiguousControlShape == some
  (.ifThenElse (.call "a" 0) (.call "b" 0) (.call "c" 0))
#guard ambiguousControlShape != some
  (.disj (.call "->" 2) (.call "c" 0))

end Mettapedia.Logic.Prolog.ReaderSourceRegression
