import Mettapedia.Languages.MeTTa.HE.RecursiveMachine
import Mettapedia.Languages.MeTTa.HE.NativeSelectedTypeScan
import Mettapedia.Languages.MeTTa.HE.Spec.Type.Conformance

/-!
# First-success strategy for retained recursive HE requests

This strategy reuses the existing recursive request and continuation vocabulary.
Only expression dispatch and function-candidate scanning change. Every nested
recursive request is expanded by the same strategy, so a selected overload
does not acquire the old all-candidate policy inside its arguments or body.

The classification parser is connected to the independent arrow grammar. The
applicability callback is the existing fuel-indexed source function; its exact
outputs retain their order; the first successful binding is selected. Full correspondence of
that callback with the independent type service remains separate from the
constructed dispatch strategy.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.HE.FirstSuccessRecursiveStrategy

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open RecursiveTasks Spec.Eval Spec.Type

/-- Parse one complete arrow, retaining its original argument domains and return
projection together. A bare arrow has no result type and is rejected. -/
def readPolicy : Atom → Option SelectedTypePolicy
  | .expression (.symbol "->" :: first :: remaining) =>
      some ⟨.expression (.symbol "->" :: first :: remaining),
        (first :: remaining).dropLast,
        (first :: remaining).getLast (by simp), by
          change Atom.expression (.symbol "->" :: first :: remaining) =
            Atom.expression (.symbol "->" ::
              ((first :: remaining).dropLast ++
                [(first :: remaining).getLast (by simp)]))
          rw [List.dropLast_append_getLast]⟩
  | _ => none

theorem readPolicy_sound {candidate : Atom} {policy : SelectedTypePolicy}
    (parsed : readPolicy candidate = some policy) : policy.functionType = candidate := by
  unfold readPolicy at parsed
  split at parsed
  · cases Option.some.inj parsed
    rfl
  · cases parsed

theorem readPolicy_complete {candidate : Atom} {arguments : List Atom} {returned : Atom}
    (arrow : FunctionTypeRel candidate arguments returned) :
    ∃ policy, readPolicy candidate = some policy ∧ policy.functionType = candidate ∧
      policy.argumentTypes = arguments ∧ policy.returnType = returned := by
  change candidate = .expression (.symbol "->" :: (arguments ++ [returned])) at arrow
  subst candidate
  cases arguments with
  | nil => exact ⟨_, rfl, rfl, rfl, rfl⟩
  | cons first remaining =>
      refine ⟨_, rfl, rfl, ?_, ?_⟩
      · change ((first :: remaining) ++ [returned]).dropLast = first :: remaining
        exact List.dropLast_concat
      · change ((first :: remaining) ++ [returned]).getLast _ = returned
        exact List.getLast_concat

theorem readPolicy_none_iff (candidate : Atom) :
    readPolicy candidate = none ↔ ¬∃ arguments returned,
      FunctionTypeRel candidate arguments returned := by
  constructor
  · rintro missing ⟨arguments, returned, arrow⟩
    obtain ⟨policy, parsed, _⟩ := readPolicy_complete arrow
    rw [missing] at parsed
    cases parsed
  · intro nonFunction
    cases parsed : readPolicy candidate with
    | none => rfl
    | some policy =>
        have exactType := readPolicy_sound parsed
        exact (nonFunction ⟨policy.argumentTypes, policy.returnType,
          exactType ▸ policy.isFunction⟩).elim

inductive Selection where
  | selected (policy : SelectedTypePolicy) (alternatives : List Bindings)
  | exhausted (errors : List Atom) (tupleEligible : Bool)

def noteNonFunction : Selection → Selection
  | .selected policy alternatives => .selected policy alternatives
  | .exhausted errors _ => .exhausted errors true

def noteErrors (earlier : List Atom) : Selection → Selection
  | .selected policy alternatives => .selected policy alternatives
  | .exhausted errors eligible => .exhausted (earlier ++ errors) eligible

/-- Select the first successful binding in the flattened arrow/callback order.
Later bindings of that arrow and later arrow candidates are not evaluated. -/
def select (space : Space) (expression expected : Atom) (incoming : Bindings)
    (fuel : Nat) (candidates : List Atom)
    (lookup : TypeLookup := rawTypeLookup space) : Selection :=
  match candidates with
  | [] => .exhausted [] false
  | candidate :: remaining =>
      match readPolicy candidate with
      | none => noteNonFunction (select (lookup := lookup) space expression expected incoming fuel remaining)
      | some policy =>
          match checkIfFunctionTypeIsApplicable (lookup := lookup) expression candidate expected space incoming fuel with
          | .inl errors => noteErrors errors (select (lookup := lookup) space expression expected incoming fuel remaining)
          | .inr alternatives => .selected policy (alternatives.take 1)

/-- Source control judgment. Arrow shape is independent syntax evidence; the
existing applicability source function remains an explicitly named leaf. -/
inductive SelectionRel (space : Space) (expression expected : Atom)
    (incoming : Bindings) (fuel : Nat) :
    (candidates : List Atom) → (result : Selection) →
      (lookup : TypeLookup := rawTypeLookup space) → Prop where
  | nil {lookup : TypeLookup} : SelectionRel (lookup := lookup) space expression expected incoming fuel [] (.exhausted [] false)
  | nonFunction {lookup : TypeLookup} {candidate remaining result} :
      (¬∃ arguments returned, FunctionTypeRel candidate arguments returned) →
      SelectionRel (lookup := lookup) space expression expected incoming fuel remaining result →
      SelectionRel (lookup := lookup) space expression expected incoming fuel (candidate :: remaining)
        (noteNonFunction result)
  | failed {lookup : TypeLookup} {candidate remaining policy errors result} :
      readPolicy candidate = some policy →
      checkIfFunctionTypeIsApplicable (lookup := lookup) expression candidate expected space incoming fuel = .inl errors →
      SelectionRel (lookup := lookup) space expression expected incoming fuel remaining result →
      SelectionRel (lookup := lookup) space expression expected incoming fuel (candidate :: remaining)
        (noteErrors errors result)
  | selected {lookup : TypeLookup} {candidate remaining policy alternatives} :
      readPolicy candidate = some policy →
      checkIfFunctionTypeIsApplicable (lookup := lookup) expression candidate expected space incoming fuel = .inr alternatives →
      SelectionRel (lookup := lookup) space expression expected incoming fuel (candidate :: remaining)
        (.selected policy (alternatives.take 1))

theorem select_sound (space : Space) (expression expected : Atom)
    (incoming : Bindings) (fuel : Nat) (candidates : List Atom)
    (lookup : TypeLookup := rawTypeLookup space) :
    SelectionRel (lookup := lookup) space expression expected incoming fuel candidates
      (select (lookup := lookup) space expression expected incoming fuel candidates) := by
  induction candidates with
  | nil => exact .nil
  | cons candidate remaining ih =>
      cases parsed : readPolicy candidate with
      | none =>
          simpa only [select, parsed] using
            SelectionRel.nonFunction ((readPolicy_none_iff candidate).mp parsed) ih
      | some policy =>
          cases checked : checkIfFunctionTypeIsApplicable (lookup := lookup) expression candidate expected space incoming fuel with
          | inl errors => simpa only [select, parsed, checked] using .failed parsed checked ih
          | inr alternatives => simpa only [select, parsed, checked] using
              (SelectionRel.selected (remaining := remaining) parsed checked)

theorem select_complete {space : Space} {lookup : TypeLookup} {expression expected : Atom}
    {incoming : Bindings} {fuel : Nat} {candidates : List Atom} {result : Selection}
    (derivation : SelectionRel (lookup := lookup) space expression expected incoming fuel candidates result) :
    select (lookup := lookup) space expression expected incoming fuel candidates = result := by
  induction derivation with
  | nil => rfl
  | nonFunction missing _ ih => simp [select, (readPolicy_none_iff _).mpr missing, ih]
  | failed parsed checked _ ih => simp [select, parsed, checked, ih]
  | selected parsed checked => simp [select, parsed, checked]

theorem select_iff (space : Space) (expression expected : Atom) (incoming : Bindings)
    (fuel : Nat) (candidates : List Atom) (result : Selection)
    (lookup : TypeLookup := rawTypeLookup space) :
    select (lookup := lookup) space expression expected incoming fuel candidates = result ↔
      SelectionRel (lookup := lookup) space expression expected incoming fuel candidates result := by
  constructor
  · rintro rfl
    exact select_sound space expression expected incoming fuel candidates lookup
  · exact select_complete

theorem selected_suffix_irrelevant (space : Space) {lookup : TypeLookup} (expression expected candidate : Atom)
    (incoming : Bindings) (fuel : Nat) (policy : SelectedTypePolicy)
    (alternatives : List Bindings) (first second : List Atom)
    (parsed : readPolicy candidate = some policy)
    (checked : checkIfFunctionTypeIsApplicable (lookup := lookup) expression candidate expected space incoming fuel =
      .inr alternatives) :
    select (lookup := lookup) space expression expected incoming fuel (candidate :: first) =
      select (lookup := lookup) space expression expected incoming fuel (candidate :: second) := by
  simp [select, parsed, checked]


/-- A successful callback has a physical first binding; the checker never
reports an empty success list. -/
theorem applicability_success_nonempty {space : Space} {lookup : TypeLookup} {expression candidate expected : Atom}
    {incoming : Bindings} {fuel : Nat} {alternatives : List Bindings}
    (checked : checkIfFunctionTypeIsApplicable (lookup := lookup) expression candidate expected space incoming fuel =
      .inr alternatives) : alternatives ≠ [] := by
  cases fuel with
  | zero => simp [checkIfFunctionTypeIsApplicable] at checked
  | succ fuel =>
      simp only [checkIfFunctionTypeIsApplicable] at checked
      split_ifs at checked with arity argumentEmpty returnEmpty
      intro empty
      have same := Sum.inr.inj checked
      rw [same, empty] at returnEmpty
      exact returnEmpty rfl

/-- Only the first binding from the first successful callback is selected. -/
theorem select_success_first {space : Space} {lookup : TypeLookup} {expression candidate expected : Atom}
    {incoming first : Bindings} {fuel : Nat} {remaining : List Bindings}
    {policy : SelectedTypePolicy} (suffix : List Atom)
    (parsed : readPolicy candidate = some policy)
    (checked : checkIfFunctionTypeIsApplicable (lookup := lookup) expression candidate expected space incoming fuel =
      .inr (first :: remaining)) :
    select (lookup := lookup) space expression expected incoming fuel (candidate :: suffix) =
      .selected policy [first] := by
  simp [select, parsed, checked]

theorem select_success_replicate {space : Space} {lookup : TypeLookup} {expression candidate expected : Atom}
    {incoming : Bindings} {fuel count : Nat} {policy : SelectedTypePolicy}
    (suffix : List Atom) (parsed : readPolicy candidate = some policy)
    (checked : checkIfFunctionTypeIsApplicable (lookup := lookup) expression candidate expected space incoming fuel =
      .inr (List.replicate count incoming)) (positive : 0 < count) :
    select (lookup := lookup) space expression expected incoming fuel (candidate :: suffix) =
      .selected policy [incoming] := by
  cases count with
  | zero => omega
  | succ count =>
      exact select_success_first suffix parsed checked

/-- The selector cannot multiply execution by successful type-binding paths. -/
theorem selected_is_singleton {space : Space} {lookup : TypeLookup} {expression expected : Atom}
    {incoming : Bindings} {fuel : Nat} {candidates : List Atom}
    {policy : SelectedTypePolicy} {alternatives : List Bindings}
    (selected : select (lookup := lookup) space expression expected incoming fuel candidates =
      .selected policy alternatives) : ∃ binding, alternatives = [binding] := by
  induction candidates with
  | nil => simp [select] at selected
  | cons candidate remaining ih =>
      cases parsed : readPolicy candidate with
      | none =>
          cases tail : select (lookup := lookup) space expression expected incoming fuel remaining with
          | selected next bindings =>
              simp only [select, parsed, noteNonFunction, tail, Selection.selected.injEq] at selected
              obtain ⟨rfl, rfl⟩ := selected
              exact ih tail
          | exhausted errors eligible => simp [select, parsed, noteNonFunction, tail] at selected
      | some next =>
          cases checked : checkIfFunctionTypeIsApplicable (lookup := lookup) expression candidate expected space incoming fuel with
          | inl errors =>
              cases tail : select (lookup := lookup) space expression expected incoming fuel remaining with
              | selected next bindings =>
                  simp only [select, parsed, checked, noteErrors, tail, Selection.selected.injEq] at selected
                  obtain ⟨rfl, rfl⟩ := selected
                  exact ih tail
              | exhausted later eligible => simp [select, parsed, checked, noteErrors, tail] at selected
          | inr bindings =>
              have nonempty := applicability_success_nonempty checked
              cases bindings with
              | nil => exact (nonempty rfl).elim
              | cons binding rest =>
                  simp only [select, parsed, checked, List.take_succ_cons, List.take_zero,
                    Selection.selected.injEq] at selected
                  exact ⟨binding, selected.2.symm⟩

/-- All recursive requests reuse the old control expansion except these two
strategy sites. The old all-candidate profile is unchanged. -/
def enter (space : Space) (dispatch : HE.GroundedDispatch) (task : Task)
    (lookup : TypeLookup := rawTypeLookup space) : Control × List Frame :=
  match task with
  | .expression value expected bindings (fuel + 1) live =>
      match value with
      | .expression (operator :: _) =>
          (.work (.functions value expected bindings fuel (lookup bindings operator expected) live), [])
      | _ => (.returning [], [])
  | .functions value expected bindings fuel candidates live =>
      match select (lookup := lookup) space value expected bindings fuel candidates with
      | .selected policy alternatives =>
          (.work (.bindingAlternatives value policy.functionType
            (if policy.returnType = Atom.expressionType then Atom.undefinedType else policy.returnType)
            fuel alternatives live), [])
      | .exhausted errors eligible =>
          if eligible then
            (.work (.tupleCalls value expected bindings fuel live),
              [.prepend (errors.map fun error => (error, bindings))])
          else (.returning (errors.map fun error => (error, bindings)), [])
  | task => RecursiveMachine.enter (lookup := lookup) space dispatch task

theorem selected_enter (space : Space) {lookup : TypeLookup} (dispatch : HE.GroundedDispatch)
    (expression expected : Atom) (incoming : Bindings) (fuel : Nat)
    (candidates : List Atom) (live : List Atom) (policy : SelectedTypePolicy)
    (alternatives : List Bindings)
    (selected : select (lookup := lookup) space expression expected incoming fuel candidates =
      .selected policy alternatives) :
    enter (lookup := lookup) space dispatch (.functions expression expected incoming fuel candidates live) =
      (.work (.bindingAlternatives expression policy.functionType
        (if policy.returnType = Atom.expressionType then Atom.undefinedType else policy.returnType)
        fuel alternatives live), []) := by
  simp only [enter, selected]

/-- Only applicability leaves visited by the first-success selector need
coverage. A successful arrow cuts off the unselected suffix. -/
def selectionReady (space : Space) (expression expected : Atom) (incoming : Bindings)
    (fuel : Nat) (candidates : List Atom)
    (lookup : TypeLookup := rawTypeLookup space) : Bool :=
  match candidates with
  | [] => true
  | candidate :: remaining =>
      match readPolicy candidate with
      | none => selectionReady (lookup := lookup) space expression expected incoming fuel remaining
      | some _ =>
          functionTypeCovered (lookup := lookup) expression candidate expected space incoming fuel &&
            match checkIfFunctionTypeIsApplicable (lookup := lookup) expression candidate expected space incoming fuel with
            | .inl _ => selectionReady (lookup := lookup) space expression expected incoming fuel remaining
            | .inr _ => true

theorem selectionReady_selected {space : Space} {lookup : TypeLookup} {expression expected candidate : Atom}
    {incoming : Bindings} {fuel : Nat} {policy : SelectedTypePolicy} {alternatives : List Bindings}
    (parsed : readPolicy candidate = some policy)
    (covered : functionTypeCovered (lookup := lookup) expression candidate expected space incoming fuel = true)
    (selected : checkIfFunctionTypeIsApplicable (lookup := lookup) expression candidate expected space incoming fuel =
      .inr alternatives) (remaining : List Atom) :
    selectionReady (lookup := lookup) space expression expected incoming fuel (candidate :: remaining) = true := by
  simp [selectionReady, parsed, covered, selected]

/-- Coverage of the visited prefix makes the actual selector independent of
additional leaf depth. No equality of two approximations is an admission. -/
theorem select_deepen (space : Space) {lookup : TypeLookup} (expression expected : Atom) (incoming : Bindings)
    (depth extra : Nat) (candidates : List Atom)
    (ready : selectionReady (lookup := lookup) space expression expected incoming depth candidates = true) :
    select (lookup := lookup) space expression expected incoming (depth + extra) candidates =
      select (lookup := lookup) space expression expected incoming depth candidates := by
  induction candidates with
  | nil => rfl
  | cons candidate remaining ih =>
      cases parsed : readPolicy candidate with
      | none =>
          have tail : selectionReady (lookup := lookup) space expression expected incoming depth remaining = true := by
            simpa [selectionReady, parsed] using ready
          simp [select, parsed, ih tail]
      | some policy =>
          have covered : functionTypeCovered (lookup := lookup) expression candidate expected space incoming depth = true := by
            exact (Bool.and_eq_true_iff.mp (by simpa only [selectionReady, parsed] using ready)).1
          have same := functionTypeCovered_stable expression candidate expected space incoming depth extra covered
          cases checked : checkIfFunctionTypeIsApplicable (lookup := lookup) expression candidate expected space incoming depth with
          | inl errors =>
              have tail : selectionReady (lookup := lookup) space expression expected incoming depth remaining = true := by
                simpa [selectionReady, parsed, covered, checked] using ready
              simp [select, parsed, same, checked, ih tail]
          | inr alternatives => simp [select, parsed, same, checked]

/-- Strategy-specific readiness changes only the atomic overload scan. The
other operations retain the common coverage guards. -/
def taskReady (space : Space) (dispatch : HE.GroundedDispatch) (task : Task)
    (lookup : TypeLookup := rawTypeLookup space) : Bool :=
  match task with
  | .functions value expected incoming depth candidates _ =>
      selectionReady (lookup := lookup) space value expected incoming depth candidates
  | task => RecursiveMachine.Checked.taskReady (lookup := lookup) space dispatch task

theorem enter_deepen (space : Space) {lookup : TypeLookup} (dispatch : HE.GroundedDispatch)
    (task : Task) (extra : Nat) (ready : taskReady (lookup := lookup) space dispatch task = true) :
    enter (lookup := lookup) space dispatch (task.replenish extra) =
      RecursiveMachine.Checked.deepenExpansion extra (enter (lookup := lookup) space dispatch task) := by
  have common := RecursiveMachine.Checked.enter_deepen (lookup := lookup) space dispatch task extra
  cases task with
  | functions value expected incoming depth candidates live =>
      have same := select_deepen space value expected incoming depth extra candidates ready
      simp only [Task.replenish, enter, same]
      cases select (lookup := lookup) space value expected incoming depth candidates with
      | selected policy alternatives => rfl
      | exhausted errors eligible => cases eligible <;> rfl
  | expression value expected incoming depth live =>
      cases depth with
      | zero => simp [taskReady, RecursiveMachine.Checked.taskReady] at ready
      | succ depth =>
          simp only [Task.replenish, Nat.succ_add, enter]
          cases value with
          | expression atoms => cases atoms <;> rfl
          | _ => rfl
  | _ =>
      simpa only [Task.replenish, enter] using
        common ready



end Mettapedia.Languages.MeTTa.HE.FirstSuccessRecursiveStrategy
