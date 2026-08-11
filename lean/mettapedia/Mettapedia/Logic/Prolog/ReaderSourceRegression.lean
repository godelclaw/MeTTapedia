import Mettapedia.Logic.Prolog.ReaderSource

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

end Mettapedia.Logic.Prolog.ReaderSourceRegression
