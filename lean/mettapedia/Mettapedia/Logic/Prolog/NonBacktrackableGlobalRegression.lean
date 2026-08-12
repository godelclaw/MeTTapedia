import Mettapedia.Logic.Prolog.SourceRuntime

/-!
# Non-backtrackable global regressions on the canonical runtime

These source-shaped programs discriminate the three independent parts of
SWI-Prolog's `nb_setval/2` contract: the set duplicates its source, repeated
gets share the stored residual variables, and the stored graph survives a
choice point that predates the set while ordinary bindings to that graph still
undo on backtracking.
-/

namespace Mettapedia.Logic.Prolog.NonBacktrackableGlobalRegression

open Mettapedia.Logic
open SourceSignature SourceRuntime

private def sourceVar (name : String) (occurrence : Nat) :
    SourceSignature.Term :=
  var name occurrence

private def setGlobal (name : String) (value : SourceSignature.Term) :
    SourceSignature.Goal :=
  SourceSignature.call "nb_setval" [atom name, value]

private def getGlobal (name : String) (value : SourceSignature.Term) :
    SourceSignature.Goal :=
  SourceSignature.call "nb_getval" [atom name, value]

private def deleteGlobal (name : String) : SourceSignature.Goal :=
  SourceSignature.call "nb_delete" [atom name]

private def identical (left right : SourceSignature.Term) :
    SourceSignature.Goal :=
  SourceSignature.call "==" [left, right]

private def hasAnswer (goal : SourceSignature.Goal) : Bool :=
  match SourceRuntime.openEmpty [] goal with
  | .error _ => false
  | .ok session =>
      match SourceRuntime.pullSession 4096 session with
      | .answer _ _ => true
      | _ => false

private def catchesUndefinedGlobal (name : String)
    (guarded : SourceSignature.Goal) : SourceSignature.Goal :=
  let contextVariable := sourceVar "Context" 0
  let catcher := compound "error" [
    compound "existence_error" [atom "variable", atom name],
    compound "context" [
      compound ":" [atom "system", compound "/" [atom "nb_getval", integer 2]],
      contextVariable
    ]
  ]
  .catch guarded catcher (.isVar contextVariable)

private def y := sourceVar "Y" 0
private def first := sourceVar "First" 0
private def second := sourceVar "Second" 0

/-- `nb_setval/2` copies before the caller binds its source variable. -/
def setDuplicatesSource : Bool :=
  hasAnswer <|
    .conj (setGlobal "copy" (compound "f" [y]))
      (.conj (.unify y (atom "source"))
        (.conj (getGlobal "copy" first)
          (.unify first (compound "f" [atom "stored"]))))

#guard setDuplicatesSource

/-- Two gets expose the same stored graph, not two independently freshened
copies.  Strict identity makes that distinction observable. -/
def repeatedGetsShareStoredVariables : Bool :=
  hasAnswer <|
    .conj (setGlobal "shared" (compound "f" [y]))
      (.conj (getGlobal "shared" first)
        (.conj (getGlobal "shared" second) (identical first second)))

#guard repeatedGetsShareStoredVariables

/-- A binding made through one get is ordinary trailed state: failure of the
left branch undoes it, so the right branch can bind the same stored variable
differently. -/
def storedBindingsBacktrack : Bool :=
  hasAnswer <|
    .conj (setGlobal "trailed" (compound "f" [y]))
      (.conj
        (.disj
          (.conj (getGlobal "trailed" first)
            (.conj (.unify first (compound "f" [atom "left"])) .fail))
          .succeed)
        (.conj (getGlobal "trailed" second)
          (.unify second (compound "f" [atom "right"]))))

#guard storedBindingsBacktrack

/-- The choice point is older than the set.  Its rollback must retain the
new protected graph and the non-backtrackable name update. -/
def setSurvivesOlderChoice : Bool :=
  hasAnswer <|
    .conj
      (.disj
        (.conj (setGlobal "persistent" (compound "f" [y])) .fail)
        .succeed)
      (.conj (getGlobal "persistent" first)
        (.unify first (compound "f" [atom "after"])))

#guard setSurvivesOlderChoice

/-- Deletion itself is non-backtrackable, while deleting an absent atom is a
successful no-op. -/
def deleteSurvivesOlderChoice : Bool :=
  hasAnswer <| catchesUndefinedGlobal "deleted" <|
    .conj (setGlobal "deleted" (atom "value"))
      (.conj
        (.disj (.conj (deleteGlobal "deleted") .fail) .succeed)
        (getGlobal "deleted" first))

#guard deleteSurvivesOlderChoice

/-- Reading a name that was never installed raises SWI's catchable
`existence_error(variable, Name)` packet rather than a fatal runtime error.
The handler additionally requires the context's final field to remain a
variable, pinning the complete normalized packet shape. -/
def missingGetRaisesCatchableExistenceError : Bool :=
  hasAnswer <| catchesUndefinedGlobal "never_installed" <|
    getGlobal "never_installed" first

#guard missingGetRaisesCatchableExistenceError

def deleteMissingSucceeds : Bool :=
  hasAnswer (deleteGlobal "already_absent")

#guard deleteMissingSucceeds

/-- A committed first solution exports the complete world, so a later fresh
top-level query sees both the stored graph and the advanced scope frontier. -/
def globalsCrossTopLevelQueries : Bool :=
  match SourceRuntime.openEmpty []
      (setGlobal "between_queries" (compound "f" [y])) with
  | .error _ => false
  | .ok session =>
      match SourceRuntime.pullSession 4096 session with
      | .answer _ resumed =>
          match SourceRuntime.openWorld resumed.commitWorld
              (.conj (getGlobal "between_queries" first)
                (.unify first (compound "f" [atom "later"]))) with
          | .error _ => false
          | .ok later =>
              match SourceRuntime.pullSession 4096 later with
              | .answer _ _ => true
              | _ => false
      | _ => false

#guard globalsCrossTopLevelQueries

end Mettapedia.Logic.Prolog.NonBacktrackableGlobalRegression
