import Mettapedia.OSLF.MeTTaIL.GeneralPremiseSemantics

/-!
# Exact executable comparison of complete premise histories

Provider positions, matcher alternatives, quantified occurrences and complete
recursive child histories are compared structurally. Equal targets never
replace these retained histories with an endpoint-only comparison.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.GeneralPremise

/-- A validation citation forgets matcher traces and quantified ordinal
labels while retaining provider declarations and the child/body event tree.
It is not a policy for logical derivation identity. Full allocation evidence
remains in `Event`; quantified lists preserve their order and duplicates. -/
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
  def Event.citation {Choice : Type} : Event Choice → Citation
    | .query p q row _ => .query p q row
    | .freshness p q atom subject => .freshness p q atom subject
    | .quantified p q kind elements => .quantified p q kind (quantifiedCitations elements)
    | .child p q index bound source target _ _ captured completed history =>
        .child p q index bound source target captured completed (citations history)

  def citations {Choice : Type} : List (Event Choice) → List Citation
    | [] => []
    | event :: rest => event.citation :: citations rest

  def quantifiedCitations {Choice : Type} : List (Nat × Syntax.Pattern × List (Event Choice)) →
      List (Syntax.Pattern × List Citation)
    | [] => []
    | (_, element, history) :: rest => (element, citations history) :: quantifiedCitations rest
end

@[simp] theorem citations_length {Choice : Type} (history : List (Event Choice)) : (citations history).length = history.length := by
  induction history with
  | nil => rfl
  | cons event rest ih => exact congrArg Nat.succ ih

@[simp] theorem quantifiedCitations_length {Choice : Type} (history : List (Nat × Syntax.Pattern × List (Event Choice))) :
    (quantifiedCitations history).length = history.length := by
  induction history with
  | nil => rfl
  | cons event rest ih => cases event; exact congrArg Nat.succ ih

mutual
/-- Changing the matcher evidence carrier does not change this validation
readout. This does not identify the underlying allocation receipts. -/
theorem Event.citation_mapTraces {Left Right : Type} (trace : List Left → List Right)
    (event : Event Left) : (event.mapTraces trace).citation = event.citation :=
  match event with
  | .query _ _ _ _ => by simp only [Event.mapTraces, Event.citation]
  | .freshness _ _ _ _ => by simp only [Event.mapTraces, Event.citation]
  | .quantified index depth kind elements => by
      simpa only [Event.mapTraces, Event.citation] using
        congrArg (Citation.quantified index depth kind) (quantifiedCitations_mapElements trace elements)
  | .child index depth declaration bound source target _ _ captured completed history => by
      simpa only [Event.mapTraces, Event.citation] using
        congrArg (Citation.child index depth declaration bound source target captured completed)
          (citations_mapHistory trace history)
termination_by sizeOf event

theorem citations_mapHistory {Left Right : Type} (trace : List Left → List Right)
    (history : List (Event Left)) : citations (Event.mapHistory trace history) = citations history :=
  match history with
  | [] => by simp only [Event.mapHistory, citations]
  | event :: rest => by
      simp only [Event.mapHistory, citations]
      rw [Event.citation_mapTraces trace event, citations_mapHistory trace rest]
termination_by sizeOf history

theorem quantifiedCitations_mapElements {Left Right : Type} (trace : List Left → List Right)
    (history : List (Nat × Syntax.Pattern × List (Event Left))) :
    quantifiedCitations (Event.mapElements trace history) = quantifiedCitations history :=
  match history with
  | [] => by simp only [Event.mapElements, quantifiedCitations]
  | (index, element, events) :: rest => by
      simp only [Event.mapElements, quantifiedCitations]
      rw [citations_mapHistory trace events, quantifiedCitations_mapElements trace rest]
termination_by sizeOf history
end

mutual
  def eventDecEq {Choice : Type} [DecidableEq Choice] : (first second : Event Choice) → Decidable (first = second)
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
    | .query _ _ _ _, .freshness _ _ _ _ => isFalse (by intro same; cases same)
    | .query _ _ _ _, .quantified _ _ _ _ => isFalse (by intro same; cases same)
    | .query _ _ _ _, .child _ _ _ _ _ _ _ _ _ _ _ => isFalse (by intro same; cases same)
    | .freshness _ _ _ _, .query _ _ _ _ => isFalse (by intro same; cases same)
    | .freshness _ _ _ _, .quantified _ _ _ _ => isFalse (by intro same; cases same)
    | .freshness _ _ _ _, .child _ _ _ _ _ _ _ _ _ _ _ => isFalse (by intro same; cases same)
    | .quantified _ _ _ _, .query _ _ _ _ => isFalse (by intro same; cases same)
    | .quantified _ _ _ _, .freshness _ _ _ _ => isFalse (by intro same; cases same)
    | .quantified _ _ _ _, .child _ _ _ _ _ _ _ _ _ _ _ => isFalse (by intro same; cases same)
    | .child _ _ _ _ _ _ _ _ _ _ _, .query _ _ _ _ => isFalse (by intro same; cases same)
    | .child _ _ _ _ _ _ _ _ _ _ _, .freshness _ _ _ _ => isFalse (by intro same; cases same)
    | .child _ _ _ _ _ _ _ _ _ _ _, .quantified _ _ _ _ => isFalse (by intro same; cases same)

  def eventsDecEq {Choice : Type} [DecidableEq Choice] : (first second : List (Event Choice)) → Decidable (first = second)
    | [], [] => isTrue rfl
    | [], _ :: _ => isFalse (by intro same; cases same)
    | _ :: _, [] => isFalse (by intro same; cases same)
    | first :: rest, second :: remaining =>
        letI : Decidable (first = second) := eventDecEq first second
        letI : Decidable (rest = remaining) := eventsDecEq rest remaining
        decidable_of_iff (first = second ∧ rest = remaining) (by simp only [List.cons.injEq])

  def quantifiedEventsDecEq {Choice : Type} [DecidableEq Choice] :
      (first second : List (Nat × Syntax.Pattern × List (Event Choice))) → Decidable (first = second)
    | [], [] => isTrue rfl
    | [], _ :: _ => isFalse (by intro same; cases same)
    | _ :: _, [] => isFalse (by intro same; cases same)
    | (index, element, history) :: rest, (index', element', history') :: remaining =>
        letI : Decidable (history = history') := eventsDecEq history history'
        letI : Decidable (rest = remaining) := quantifiedEventsDecEq rest remaining
        decidable_of_iff (index = index' ∧ element = element' ∧ history = history' ∧ rest = remaining)
          (by simp only [List.cons.injEq, Prod.mk.injEq, and_assoc])
end

instance {Choice : Type} [DecidableEq Choice] : DecidableEq (Event Choice) := eventDecEq

/-! Query identity is an optional observation policy. Exact event equality
and the existing validation-citation readout remain unchanged. -/

inductive QueryIdentity where
  | evidence
  | allocationValidation
  | factValidation
  deriving DecidableEq

mutual
  def validationEventReadout {Choice : Type} (event : Event Choice)
      (queryIdentity : QueryIdentity := .allocationValidation) : List (Event Choice) :=
    match event with
    | .query p q row origins =>
        match queryIdentity with
        | .evidence => [.query p q row origins]
        | .allocationValidation => [.query p q 0 origins]
        | .factValidation => []
    | .freshness .. => []
    | .quantified p q kind elements =>
        [.quantified p q kind (validationElementsReadout elements queryIdentity)]
    | .child p q index bound source target trace targetTrace captured completed history =>
        [.child p q index bound source target trace targetTrace captured completed
          (validationHistoryReadout history queryIdentity)]

  def validationHistoryReadout {Choice : Type} (history : List (Event Choice))
      (queryIdentity : QueryIdentity := .allocationValidation) : List (Event Choice) :=
    match history with
    | [] => []
    | event :: rest => validationEventReadout event queryIdentity ++ validationHistoryReadout rest queryIdentity

  def validationElementsReadout {Choice : Type}
      (elements : List (Nat × Syntax.Pattern × List (Event Choice)))
      (queryIdentity : QueryIdentity := .allocationValidation) :
      List (Nat × Syntax.Pattern × List (Event Choice)) :=
    match elements with
    | [] => []
    | (index, element, history) :: rest =>
        (index, element, validationHistoryReadout history queryIdentity) :: validationElementsReadout rest queryIdentity
end

theorem validationHistoryReadout_append {Choice : Type}
    (first second : List (Event Choice)) :
    validationHistoryReadout (first ++ second) =
      validationHistoryReadout first ++ validationHistoryReadout second := by
  induction first with
  | nil => rfl
  | cons event rest ih => simp only [List.cons_append, validationHistoryReadout, ih, List.append_assoc]

theorem query_validation_row_erases {Choice : Type} (p q first second : Nat)
    (origins : List (Nat × List Choice)) :
    validationEventReadout (.query p q first origins) =
      validationEventReadout (.query p q second origins) := rfl

theorem freshness_validation_erases {Choice : Type} (p q : Nat) (atom : String) (subject : Syntax.Pattern) :
    validationEventReadout (Choice := Choice) (.freshness p q atom subject) = [] := rfl

end Mettapedia.OSLF.MeTTaIL.GeneralPremise
