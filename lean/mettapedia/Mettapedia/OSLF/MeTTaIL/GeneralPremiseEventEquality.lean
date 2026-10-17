import Mettapedia.OSLF.MeTTaIL.GeneralPremiseSemantics

/-!
# Exact executable comparison of complete premise histories

Provider positions, matcher alternatives, quantified occurrences and complete
recursive child histories are compared structurally. Equal targets never
replace these retained histories with an endpoint-only comparison.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.GeneralPremise

/-- Premise citations identify the selected source/provider occurrences and
child applications. Scoped matching permutations are replay guidance rather
than application identity. Quantified lists retain every element occurrence. -/
inductive Citation where
  | query (premiseIndex quantifierDepth rowIndex : Nat)
  | freshness (premiseIndex quantifierDepth : Nat) (atom : String) (subject : Syntax.Pattern)
  | quantified (premiseIndex quantifierDepth : Nat) (kind : Syntax.CollType)
      (elements : List (Syntax.Pattern × List Citation))
  | child (premiseIndex quantifierDepth declarationIndex : Nat)
      (bound : List Syntax.TypeExpr) (source target : Syntax.Pattern)
      (captured completed : ScopedRuleMatching.Assignment) (history : List Citation)
  deriving Repr

mutual
  def Event.citation : Event → Citation
    | .query p q row _ => .query p q row
    | .freshness p q atom subject => .freshness p q atom subject
    | .quantified p q kind elements => .quantified p q kind (quantifiedCitations elements)
    | .child p q index bound source target _ _ captured completed history =>
        .child p q index bound source target captured completed (citations history)

  def citations : List Event → List Citation
    | [] => []
    | event :: rest => event.citation :: citations rest

  def quantifiedCitations : List (Nat × Syntax.Pattern × List Event) →
      List (Syntax.Pattern × List Citation)
    | [] => []
    | (_, element, history) :: rest => (element, citations history) :: quantifiedCitations rest
end

@[simp] theorem citations_length (history : List Event) : (citations history).length = history.length := by
  induction history with
  | nil => rfl
  | cons event rest ih => exact congrArg Nat.succ ih

@[simp] theorem quantifiedCitations_length (history : List (Nat × Syntax.Pattern × List Event)) :
    (quantifiedCitations history).length = history.length := by
  induction history with
  | nil => rfl
  | cons event rest ih => cases event; exact congrArg Nat.succ ih

mutual
  def eventDecEq : (first second : Event) → Decidable (first = second)
    | .query p q row origins, .query p' q' row' origins' =>
        decidable_of_iff (p = p' ∧ q = q' ∧ row = row' ∧ origins = origins') (by simp only [Event.query.injEq])
    | .freshness p q atom subject, .freshness p' q' atom' subject' =>
        decidable_of_iff (p = p' ∧ q = q' ∧ atom = atom' ∧ subject = subject') (by simp only [Event.freshness.injEq])
    | .quantified p q kind elements, .quantified p' q' kind' elements' =>
        letI : Decidable (elements = elements') := quantifiedEventsDecEq elements elements'
        decidable_of_iff (p = p' ∧ q = q' ∧ kind = kind' ∧ elements = elements') (by simp only [Event.quantified.injEq])
    | .child p q index bound source target trace targetTrace captured completed history,
        .child p' q' index' bound' source' target' trace' targetTrace' captured' completed' history' =>
        letI : Decidable (history = history') := eventsDecEq history history'
        decidable_of_iff (p = p' ∧ q = q' ∧ index = index' ∧ bound = bound' ∧ source = source' ∧
          target = target' ∧ trace = trace' ∧ targetTrace = targetTrace' ∧ captured = captured' ∧
          completed = completed' ∧ history = history') (by simp only [Event.child.injEq])
    | .query _ _ _ _, .freshness _ _ _ _ => isFalse Event.noConfusion
    | .query _ _ _ _, .quantified _ _ _ _ => isFalse Event.noConfusion
    | .query _ _ _ _, .child _ _ _ _ _ _ _ _ _ _ _ => isFalse Event.noConfusion
    | .freshness _ _ _ _, .query _ _ _ _ => isFalse Event.noConfusion
    | .freshness _ _ _ _, .quantified _ _ _ _ => isFalse Event.noConfusion
    | .freshness _ _ _ _, .child _ _ _ _ _ _ _ _ _ _ _ => isFalse Event.noConfusion
    | .quantified _ _ _ _, .query _ _ _ _ => isFalse Event.noConfusion
    | .quantified _ _ _ _, .freshness _ _ _ _ => isFalse Event.noConfusion
    | .quantified _ _ _ _, .child _ _ _ _ _ _ _ _ _ _ _ => isFalse Event.noConfusion
    | .child _ _ _ _ _ _ _ _ _ _ _, .query _ _ _ _ => isFalse Event.noConfusion
    | .child _ _ _ _ _ _ _ _ _ _ _, .freshness _ _ _ _ => isFalse Event.noConfusion
    | .child _ _ _ _ _ _ _ _ _ _ _, .quantified _ _ _ _ => isFalse Event.noConfusion

  def eventsDecEq : (first second : List Event) → Decidable (first = second)
    | [], [] => isTrue rfl
    | [], _ :: _ => isFalse (by intro same; cases same)
    | _ :: _, [] => isFalse (by intro same; cases same)
    | first :: rest, second :: remaining =>
        letI : Decidable (first = second) := eventDecEq first second
        letI : Decidable (rest = remaining) := eventsDecEq rest remaining
        decidable_of_iff (first = second ∧ rest = remaining) (by simp only [List.cons.injEq])

  def quantifiedEventsDecEq :
      (first second : List (Nat × Syntax.Pattern × List Event)) → Decidable (first = second)
    | [], [] => isTrue rfl
    | [], _ :: _ => isFalse (by intro same; cases same)
    | _ :: _, [] => isFalse (by intro same; cases same)
    | (index, element, history) :: rest, (index', element', history') :: remaining =>
        letI : Decidable (history = history') := eventsDecEq history history'
        letI : Decidable (rest = remaining) := quantifiedEventsDecEq rest remaining
        decidable_of_iff (index = index' ∧ element = element' ∧ history = history' ∧ rest = remaining)
          (by simp only [List.cons.injEq, Prod.mk.injEq, and_assoc])
end

instance : DecidableEq Event := eventDecEq

end Mettapedia.OSLF.MeTTaIL.GeneralPremise
