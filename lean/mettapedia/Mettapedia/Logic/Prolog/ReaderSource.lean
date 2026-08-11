import Mettapedia.Logic.Prolog.ReaderTerm

/-!
# Prolog source forms on the canonical LP representation

The term reader deliberately produces `Logic.LP.Term` directly. This module
classifies those same terms as clauses, directives, queries, DCG rules, and
typed Prolog goals; it introduces no second term or clause language.

Control functors are interpreted only at callable goal positions. All other
functors remain ordinary data, and unrecognized callable terms become
ordinary predicate calls over `SourceSignature`.
-/

namespace Mettapedia.Logic.Prolog.ReaderSource

open SourceSignature

inductive Error where
  | nonCallableHead
  | nonCallableGoal
  | exhaustedInputMeasure
deriving DecidableEq, Repr

/-- One source-level item before directive execution and DCG expansion. DCG
payloads remain canonical LP terms until the loader's expansion phase. -/
inductive Form where
  | clause (value : SourceSignature.Clause)
  | directive (goal : SourceSignature.Goal)
  | query (goal : SourceSignature.Goal)
  | dcg (head body : SourceSignature.Term)

private def application? : SourceSignature.Term ->
    Option (String × List SourceSignature.Term)
  | .const (.atom name) => some (name, [])
  | .app indicator arguments =>
      some (indicator.name, List.ofFn arguments)
  | _ => none

private def ordinaryCall (name : String)
    (arguments : List SourceSignature.Term) : SourceSignature.Goal :=
  .call (SourceSignature.predicate name arguments)

private def toGoalAux : Nat -> SourceSignature.Term ->
    Except Error SourceSignature.Goal
  | 0, _ => .error .exhaustedInputMeasure
  | fuel + 1, term =>
      match term with
      | .var _ => .ok (ordinaryCall "call" [term])
      | _ =>
          match application? term with
          | none => .error .nonCallableGoal
          | some (name, arguments) =>
              match name, arguments with
              | "true", [] => .ok .succeed
              | "fail", [] => .ok .fail
              | "!", [] => .ok .cut
              | ",", [left, right] => do
                  let parsedLeft <- toGoalAux fuel left
                  let parsedRight <- toGoalAux fuel right
                  pure (.conj parsedLeft parsedRight)
              | ";", [choice, elseBranch] =>
                  match application? choice with
                  | some ("->", [condition, thenBranch]) => do
                      let parsedCondition <- toGoalAux fuel condition
                      let parsedThen <- toGoalAux fuel thenBranch
                      let parsedElse <- toGoalAux fuel elseBranch
                      pure (.ifThenElse parsedCondition parsedThen parsedElse)
                  | some ("*->", [condition, thenBranch]) => do
                      let parsedCondition <- toGoalAux fuel condition
                      let parsedThen <- toGoalAux fuel thenBranch
                      let parsedElse <- toGoalAux fuel elseBranch
                      pure (.softIfThenElse parsedCondition parsedThen parsedElse)
                  | _ => do
                      let parsedLeft <- toGoalAux fuel choice
                      let parsedRight <- toGoalAux fuel elseBranch
                      pure (.disj parsedLeft parsedRight)
              | "->", [condition, thenBranch] => do
                  let parsedCondition <- toGoalAux fuel condition
                  let parsedThen <- toGoalAux fuel thenBranch
                  pure (.ifThenElse parsedCondition parsedThen .fail)
              | "*->", [condition, thenBranch] => do
                  let parsedCondition <- toGoalAux fuel condition
                  let parsedThen <- toGoalAux fuel thenBranch
                  pure (.softIfThenElse parsedCondition parsedThen .fail)
              | "once", [goal] => .once <$> toGoalAux fuel goal
              | "\\+", [goal] => .neg <$> toGoalAux fuel goal
              | "=", [left, right] => .ok (.unify left right)
              | "\\=", [left, right] => .ok (.notUnify left right)
              | "var", [argument] => .ok (.isVar argument)
              | "nonvar", [argument] => .ok (.neg (.isVar argument))
              | "forall", [condition, action] => do
                  let parsedCondition <- toGoalAux fuel condition
                  let parsedAction <- toGoalAux fuel action
                  pure (.neg (.conj parsedCondition (.neg parsedAction)))
              | "findall", [template, generator, bag] => do
                  let parsedGenerator <- toGoalAux fuel generator
                  pure (.findall template parsedGenerator bag)
              | "catch", [guarded, catcher, recovery] => do
                  let parsedGuarded <- toGoalAux fuel guarded
                  let parsedRecovery <- toGoalAux fuel recovery
                  pure (.catch parsedGuarded catcher parsedRecovery)
              | "throw", [ball] => .ok (.throw ball)
              | _, _ => .ok (ordinaryCall name arguments)

/-- Interpret one canonical term in callable goal position. -/
def toGoal (term : SourceSignature.Term) : Except Error SourceSignature.Goal :=
  toGoalAux (term.size + 1) term

/-- Convert a callable source term into the canonical LP atom used as a
clause head. -/
def toHead (term : SourceSignature.Term) :
    Except Error SourceSignature.Atom :=
  match application? term with
  | some (name, arguments) => .ok (SourceSignature.predicate name arguments)
  | none => .error .nonCallableHead

/-- Normalize a source clause to the ordinary `(:-)/2` data shape used by
ISO database reflection.  A fact receives the explicit body `true`; rules
retain their original head and body terms verbatim, including variable
sharing and control spelling. -/
def normalizedClauseTerm (head body : SourceSignature.Term) :
    SourceSignature.Term :=
  SourceSignature.compound ":-" [head, body]

@[simp]
private theorem except_pure_eq_ok {alpha epsilon : Type*} (value : alpha) :
    (pure value : Except epsilon alpha) = .ok value := rfl

/-- Classify one terminated source term without executing it. -/
def classify (term : SourceSignature.Term) : Except Error Form :=
  match application? term with
  | some (":-", [directive]) => .directive <$> toGoal directive
  | some ("?-", [query]) => .query <$> toGoal query
  | some ("-->", [head, body]) => .ok (.dcg head body)
  | some (":-", [head, body]) => do
      let parsedHead <- toHead head
      let parsedBody <- toGoal body
      pure (.clause {
        head := parsedHead
        body := parsedBody
        sourceTerm := some (normalizedClauseTerm head body)
      })
  | _ => do
      let parsedHead <- toHead term
      pure (.clause {
        head := parsedHead
        body := .succeed
        sourceTerm := some (normalizedClauseTerm term (SourceSignature.atom "true"))
      })

/-- Reclassifying the normalized data representation uses the same parsed
head and body and retains that representation exactly.  This is the local
agreement check later consumed by reflective database operations. -/
theorem classify_normalizedClauseTerm
    {head body : SourceSignature.Term}
    {parsedHead : SourceSignature.Atom}
    {parsedBody : SourceSignature.Goal}
    (hHead : toHead head = .ok parsedHead)
    (hBody : toGoal body = .ok parsedBody) :
    classify (normalizedClauseTerm head body) = .ok (.clause {
      head := parsedHead
      body := parsedBody
      sourceTerm := some (normalizedClauseTerm head body)
    }) := by
  simp [classify, normalizedClauseTerm, SourceSignature.compound,
    application?, hHead, hBody, Bind.bind, Except.bind]

private def sourceTermPresent : Except Error Form -> Prop
  | .error _ => True
  | .ok (.clause clause) => clause.sourceTerm.isSome
  | .ok _ => True

private theorem sourceTermPresent_directive
    (result : Except Error SourceSignature.Goal) :
    sourceTermPresent (.directive <$> result) := by
  cases result <;> simp [sourceTermPresent]

private theorem sourceTermPresent_query
    (result : Except Error SourceSignature.Goal) :
    sourceTermPresent (.query <$> result) := by
  cases result <;> simp [sourceTermPresent]

private theorem sourceTermPresent_rule (head body : SourceSignature.Term) :
    sourceTermPresent (do
      let parsedHead <- toHead head
      let parsedBody <- toGoal body
      pure (.clause {
        head := parsedHead
        body := parsedBody
        sourceTerm := some (normalizedClauseTerm head body)
      })) := by
  cases hHead : toHead head with
  | error error =>
      simp [Bind.bind, Except.bind, sourceTermPresent]
  | ok parsedHead =>
      cases hBody : toGoal body with
      | error error =>
          simp [Bind.bind, Except.bind, sourceTermPresent]
      | ok parsedBody =>
          exact (show sourceTermPresent (Except.ok (.clause {
            head := parsedHead
            body := parsedBody
            sourceTerm := some (normalizedClauseTerm head body)
          })) from by simp [sourceTermPresent])

private theorem sourceTermPresent_fact (term : SourceSignature.Term) :
    sourceTermPresent (do
      let parsedHead <- toHead term
      pure (.clause {
        head := parsedHead
        body := .succeed
        sourceTerm := some
          (normalizedClauseTerm term (SourceSignature.atom "true"))
      })) := by
  cases hHead : toHead term with
  | error error =>
      simp [Bind.bind, Except.bind, sourceTermPresent]
  | ok parsedHead =>
      exact (show sourceTermPresent (Except.ok (.clause {
        head := parsedHead
        body := .succeed
        sourceTerm := some
          (normalizedClauseTerm term (SourceSignature.atom "true"))
      })) from by simp [sourceTermPresent])

private theorem classify_sourceTermPresent (term : SourceSignature.Term) :
    sourceTermPresent (classify term) := by
  unfold classify
  split
  case h_1 directive _ =>
    exact sourceTermPresent_directive (toGoal directive)
  case h_2 query _ =>
    exact sourceTermPresent_query (toGoal query)
  case h_3 => trivial
  case h_4 head body _ =>
    exact sourceTermPresent_rule head body
  case h_5 =>
    exact sourceTermPresent_fact term

/-- Every successfully classified clause carries database-reflection data;
the reader never manufactures a provenance-free executable clause. -/
theorem classify_clause_sourceTerm_present
    {term : SourceSignature.Term} {clause : SourceSignature.Clause}
    (hClassify : classify term = .ok (.clause clause)) :
    clause.sourceTerm.isSome := by
  have present := classify_sourceTermPresent term
  rw [hClassify] at present
  exact present

end Mettapedia.Logic.Prolog.ReaderSource
