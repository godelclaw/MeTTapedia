import Mettapedia.Languages.MeTTa.HE.FirstSuccessSourceReplies
import Mettapedia.Languages.MeTTa.HE.FirstSuccessPreparedArguments
import Mettapedia.Languages.MeTTa.HE.DeclMatchSpec

/-!
# Actual-source applicability witnesses and retained path multiplicity

The raw-domain traversal is connected to independent applicability judgments
for arbitrary argument syntax and binding environments. The existing source
type checker visits every actual-type occurrence, even when Atom demand accepts
each unchanged. Its complete binding reply therefore retains that product of
occurrences. Wrong arity produces the independent error and excludes success.

Closed type casts are also connected to the independent match and merge
judgments. Earlier closed types that do not fit are rejected at every fuel;
the selected fitting type is realized at a derived sufficient budget.
The general polymorphic matcher, native freshening and Need materialization
remain separate correspondence obligations.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.HE.FirstSuccessSourceApplicability

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Spec.Type Spec.Eval FirstSuccessSourceReplies

theorem arrow_arguments (arguments : List Atom) (returned : Atom) :
    getFunctionArgTypes (.expression (.symbol "->" :: (arguments ++ [returned]))) =
      some arguments := by
  simp [getFunctionArgTypes]

theorem arrow_return (arguments : List Atom) (returned : Atom) :
    getFunctionRetType (.expression (.symbol "->" :: (arguments ++ [returned]))) =
      some returned := by
  simp [getFunctionRetType]

/-- One actual type occurrence supplies one unchanged raw binding occurrence. -/
theorem raw_argument_check (space : Space) (argument : Atom) (bindings : Bindings)
    (fuel : Nat) :
    checkArgumentType space argument Atom.atomType bindings fuel =
      List.replicate (getAtomTypes space argument).length (.inr bindings) := by
  simp [checkArgumentType, matchTypes, List.flatMap_def]

private theorem checked_successes (bindings : Bindings)
    (count : Nat) (failure : Atom → Atom)
    (errors : List Atom) (successes : List Bindings) :
    (List.replicate count (Sum.inr bindings : Sum Atom Bindings)).foldl
      (fun previous result => match result with
        | .inl actual => (previous.1 ++ [failure actual], previous.2)
        | .inr next => (previous.1, previous.2 ++ [next]))
      (errors, successes) = (errors, successes ++ List.replicate count bindings) := by
  induction count generalizing successes with
  | zero => simp
  | succ count ih =>
      simp only [List.replicate_succ, List.foldl_cons]
      rw [ih]
      simp [List.append_assoc]

private theorem argument_fold (space : Space) (argument expression : Atom)
    (bindings : Bindings) (fuel index count : Nat)
    (errors : List Atom) (successes : List Bindings) :
    (List.replicate count bindings).foldl (fun previous selected =>
      (checkArgumentType space argument Atom.atomType selected fuel).foldl
        (fun previous checked => match checked with
          | .inl actual =>
              (previous.1 ++ [mkError expression (.badArgType index Atom.atomType actual)], previous.2)
          | .inr next => (previous.1, previous.2 ++ [next])) (previous.1, previous.2))
      (errors, successes) =
        (errors, successes ++ List.replicate
          (count * (getAtomTypes space argument).length) bindings) := by
  simp only [raw_argument_check]
  induction count generalizing successes with
  | zero => simp
  | succ count ih =>
      simp only [List.replicate_succ, List.foldl_cons]
      rw [checked_successes, ih]
      simp only [List.append_assoc, ← List.replicate_add, Nat.succ_mul]
      rw [Nat.add_comm]

private theorem pair_append_fold (values : List Bindings)
    (errors : List Atom) (successes : List Bindings) :
    values.foldl (fun previous selected => (previous.1, previous.2 ++ [selected]))
      (errors, successes) = (errors, successes ++ values) := by
  induction values generalizing successes with
  | nil => simp
  | cons value values ih =>
      simp only [List.foldl_cons]
      rw [ih]
      simp [List.append_assoc]

def pathCount (space : Space) : List Atom → Nat
  | [] => 1
  | argument :: arguments => (getAtomTypes space argument).length * pathCount space arguments

theorem pathCount_positive (space : Space) (arguments : List Atom) :
    0 < pathCount space arguments := by
  induction arguments with
  | nil => exact Nat.zero_lt_one
  | cons argument arguments ih =>
      exact Nat.mul_pos (List.length_pos_iff.mpr (getAtomTypes_nonempty space argument)) ih

/-- The source traverses the complete cross-product of raw actual-type
occurrences. No support quotient erases repeated binding paths. -/
theorem raw_argument_loop (space : Space) (arguments : List Atom)
    (expression : Atom) (bindings : Bindings) (fuel index count : Nat)
    (errors : List Atom) :
    checkIfFunctionTypeIsApplicable.checkArgLoop arguments
      (List.replicate arguments.length Atom.atomType) expression
      (List.replicate count bindings) errors space fuel index =
        (errors, List.replicate (count * pathCount space arguments) bindings) := by
  induction arguments generalizing index count with
  | nil => simp [checkIfFunctionTypeIsApplicable.checkArgLoop, pathCount]
  | cons argument arguments ih =>
      simp only [List.length_cons, List.replicate_succ,
        checkIfFunctionTypeIsApplicable.checkArgLoop]
      let checked := (List.replicate count bindings).foldl
        (fun previous selected => (checkArgumentType space argument Atom.atomType selected fuel).foldl
          (fun previous result => match result with
            | .inl actual =>
                (previous.1 ++ [mkError expression (.badArgType index Atom.atomType actual)], previous.2)
            | .inr next => (previous.1, previous.2 ++ [next]))
          (previous.1, previous.2)) (errors, [])
      have folded : checked =
          (errors, List.replicate (count * (getAtomTypes space argument).length) bindings) := by
        simpa only [List.nil_append] using
          argument_fold space argument expression bindings fuel index count errors []
      change checkIfFunctionTypeIsApplicable.checkArgLoop arguments
        (List.replicate arguments.length Atom.atomType) expression checked.2 checked.1
        space fuel (index + 1) = _
      rw [folded, ih]
      simp only [pathCount, Nat.mul_assoc]

theorem source_raw_applicability (space : Space) (operator returned : Atom)
    (arguments : List Atom) (bindings : Bindings) (fuel : Nat) :
    checkIfFunctionTypeIsApplicable (.expression (operator :: arguments))
      (.expression (.symbol "->" ::
        (List.replicate arguments.length Atom.atomType ++ [returned])))
      Atom.undefinedType space bindings (fuel + 1) =
        .inr (List.replicate (pathCount space arguments) bindings) := by
  simp only [checkIfFunctionTypeIsApplicable, arrow_arguments, arrow_return,
    List.length_replicate, bne_self_eq_false, Bool.false_eq_true, if_false]
  have loop := raw_argument_loop space arguments (.expression (operator :: arguments))
    bindings fuel 1 1 []
  rw [show [bindings] = List.replicate 1 bindings from rfl, loop]
  simp only [Nat.one_mul]
  have nonempty : (List.replicate (pathCount space arguments) bindings).isEmpty = false := by
    simp [pathCount_positive space arguments |>.ne']
  simp only [nonempty, Bool.false_eq_true, if_false]
  simp only [matchTypes, beq_self_eq_true, Bool.true_or, if_true,
    List.isEmpty_cons, Bool.false_eq_true, if_false]
  rw [pair_append_fold]
  simp only [List.nil_append, nonempty, Bool.false_eq_true, if_false]

theorem independent_raw_arguments (space : Space) (arguments : List Atom)
    (bindings : Bindings) :
    ArgumentsApplicableRel space arguments (List.replicate arguments.length Atom.atomType)
      bindings bindings := by
  induction arguments with
  | nil => exact .nil bindings
  | cons argument arguments ih =>
      obtain ⟨actual, member⟩ := List.exists_mem_of_ne_nil (getAtomTypes space argument)
        (getAtomTypes_nonempty space argument)
      exact .cons ((Conformance.typeOfRel_iff_mem_getAtomTypes space argument actual).mpr member)
        (.atomLeft actual bindings) ih

/-- Every occurrence in the actual source reply has a separately constructed
independent application derivation, including its exact original arrow. -/
theorem source_raw_applicability_sound (space : Space) (operator returned : Atom)
    (arguments : List Atom) (bindings output : Bindings)
    (member : output ∈ List.replicate (pathCount space arguments) bindings) :
    ApplicationSuccessRel space (.expression (operator :: arguments))
      (.expression (.symbol "->" ::
        (List.replicate arguments.length Atom.atomType ++ [returned])))
      Atom.undefinedType bindings output := by
  have equal : output = bindings := List.eq_of_mem_replicate member
  subst output
  exact .mk rfl rfl (independent_raw_arguments space arguments bindings)
    (.undefinedLeft returned bindings)

theorem source_wrong_arity (space : Space) (operator returned expected : Atom)
    (arguments domains : List Atom) (bindings : Bindings) (fuel : Nat)
    (different : arguments.length ≠ domains.length) :
    checkIfFunctionTypeIsApplicable (.expression (operator :: arguments))
      (.expression (.symbol "->" :: (domains ++ [returned]))) expected space bindings (fuel + 1) =
        .inl [mkError (.expression (operator :: arguments)) .incorrectNumberOfArguments] := by
  simp [checkIfFunctionTypeIsApplicable, arrow_arguments, different]

theorem independent_wrong_arity (space : Space) (operator returned expected : Atom)
    (arguments domains : List Atom) (bindings : Bindings)
    (different : arguments.length ≠ domains.length) :
    ApplicabilityRel space (.expression (operator :: arguments))
      (.expression (.symbol "->" :: (domains ++ [returned]))) expected bindings
      (.error (mkError (.expression (operator :: arguments)) .incorrectNumberOfArguments)) :=
  .wrongArity rfl rfl different

open Spec.Type.Presentation (TypeSubst)

attribute [local simp] Atom.symbolType Atom.variableType Atom.expressionType Atom.groundedType

private theorem match_list_empty_acc (left right : List Atom) (fuel : Nat) :
    matchAtomsList left right [] fuel = [] := by
  induction fuel generalizing left right with
  | zero => rfl
  | succ fuel ih => cases left <;> cases right <;> simp [matchAtomsList, ih]

/-- The existing matcher checks variable-free types structurally, at every
depth. The stated bound accounts for the actual mutual recursion; it does not
alter the evaluator's fuel or introduce a different matching algorithm. -/
theorem closed_match_exact (fuel : Nat) :
    (∀ left right : Atom, TypeSubst.typeVars left = [] → TypeSubst.typeVars right = [] →
      sizeOf left + sizeOf right + 2 ≤ fuel →
      matchAtoms left right fuel = if left = right then [Bindings.empty] else []) ∧
    (∀ left right : List Atom, TypeSubst.typeVarsList left = [] →
      TypeSubst.typeVarsList right = [] → sizeOf left + sizeOf right + 2 ≤ fuel →
      matchAtomsList left right [Bindings.empty] fuel =
        if left = right then [Bindings.empty] else []) := by
  induction fuel with
  | zero =>
      constructor <;> intro left right _ _ enough <;> omega
  | succ fuel ih =>
      constructor
      · intro left right leftClosed rightClosed enough
        cases left with
        | var name => simp [TypeSubst.typeVars] at leftClosed
        | symbol name =>
            cases right with
            | var name => simp [TypeSubst.typeVars] at rightClosed
            | symbol other =>
                by_cases same : name = other
                · subst other
                  simp [matchAtoms, getMetaType, Bindings.hasLoop, Bindings.empty]
                · simp [matchAtoms, getMetaType, same]
            | grounded value => simp [matchAtoms, getMetaType]
            | expression children => simp [matchAtoms, getMetaType]
        | grounded value =>
            cases right with
            | var name => simp [TypeSubst.typeVars] at rightClosed
            | symbol name => simp [matchAtoms, getMetaType]
            | expression children => simp [matchAtoms, getMetaType]
            | grounded other =>
                by_cases same : value = other
                · subst other
                  simp [matchAtoms, getMetaType, Bindings.hasLoop, Bindings.empty]
                · simp [matchAtoms, getMetaType, same]
        | expression children =>
            cases right with
            | var name => simp [TypeSubst.typeVars] at rightClosed
            | symbol name => simp [matchAtoms, getMetaType]
            | grounded value => simp [matchAtoms, getMetaType]
            | expression others =>
                have enough' : sizeOf children + sizeOf others + 2 ≤ fuel := by
                  simp only [Atom.expression.sizeOf_spec] at enough
                  omega
                have checked := ih.2 children others leftClosed rightClosed enough'
                by_cases lengths : children.length = others.length
                · have unfolded : matchAtoms (.expression children) (.expression others) (fuel + 1) =
                      (matchAtomsList children others [Bindings.empty] fuel).filter
                        (fun bindings => !bindings.hasLoop) := by
                    simp [matchAtoms, getMetaType, lengths]
                  rw [unfolded, checked]
                  by_cases same : children = others <;> simp [same, Bindings.hasLoop, Bindings.empty]
                · have different : children ≠ others := fun same => lengths (same ▸ rfl)
                  simp [matchAtoms, getMetaType, lengths, different]
      · intro left right leftClosed rightClosed enough
        cases left with
        | nil => cases right <;> simp [matchAtomsList]
        | cons head tail =>
            cases right with
            | nil => simp [matchAtomsList]
            | cons other rest =>
                have closedLeft : TypeSubst.typeVars head = [] ∧
                    TypeSubst.typeVarsList tail = [] := by
                  simpa only [TypeSubst.typeVarsList, List.append_eq_nil_iff] using leftClosed
                have closedRight : TypeSubst.typeVars other = [] ∧
                    TypeSubst.typeVarsList rest = [] := by
                  simpa only [TypeSubst.typeVarsList, List.append_eq_nil_iff] using rightClosed
                have enoughHead : sizeOf head + sizeOf other + 2 ≤ fuel := by
                  simp only [List.cons.sizeOf_spec] at enough
                  omega
                have enoughTail : sizeOf tail + sizeOf rest + 2 ≤ fuel := by
                  simp only [List.cons.sizeOf_spec] at enough
                  omega
                have positive : 0 < fuel := by omega
                have merged : mergeBindings Bindings.empty Bindings.empty fuel =
                    [Bindings.empty] := by
                  cases fuel with
                  | zero => omega
                  | succ fuel => simp [mergeBindings, Bindings.empty]
                rw [matchAtomsList, ih.1 head other closedLeft.1 closedRight.1 enoughHead]
                by_cases same : head = other
                · subst other
                  simp only [ite_true, List.flatMap_cons, List.flatMap_nil,
                    List.append_nil, merged]
                  rw [ih.2 tail rest closedLeft.2 closedRight.2 enoughTail]
                  simp
                · simp [same, match_list_empty_acc]

private theorem independent_empty_merge (bindings : Bindings) :
    Spec.Match.Merge.MergeRel Spec.Match.Merge.equalityGroundedSemantic
      bindings Bindings.empty bindings :=
  .mk (by rfl) .nil

private theorem typeVarsList_closed {children : List Atom}
    (closed : TypeSubst.typeVarsList children = []) :
    ∀ child ∈ children, TypeSubst.typeVars child = [] := by
  induction children with
  | nil => simp
  | cons child children ih =>
      have parts : TypeSubst.typeVars child = [] ∧ TypeSubst.typeVarsList children = [] := by
        simpa only [TypeSubst.typeVarsList, List.append_eq_nil_iff] using closed
      intro element member
      rcases List.mem_cons.mp member with rfl | member
      · exact parts.1
      · exact ih parts.2 _ member

private theorem independent_closed_self_aux (type : Atom)
    (closed : TypeSubst.typeVars type = []) :
    Spec.Match.Merge.MatchRel Spec.Match.Merge.equalityGroundedSemantic
      type type Bindings.empty := by
  have closedAt := closed
  cases shape : type with
  | symbol name => exact .symSym name Spec.Match.Merge.semanticLoopFree_empty
  | var name => simp [shape, TypeSubst.typeVars] at closed
  | grounded value =>
      exact .groundedLeftCustom rfl (by trivial) ⟨rfl, rfl⟩
        Spec.Match.Merge.semanticLoopFree_empty
  | expression children =>
      apply Spec.Match.Merge.MatchRel.expression _ Spec.Match.Merge.semanticLoopFree_empty
      have allClosed : ∀ child ∈ children, TypeSubst.typeVars child = [] :=
        typeVarsList_closed (by simpa only [shape, TypeSubst.typeVars] using closedAt)
      have build : ∀ values : List Atom, (∀ child ∈ values, child ∈ children) →
          Spec.Match.Merge.MatchListAccRel Spec.Match.Merge.equalityGroundedSemantic
            values values Bindings.empty Bindings.empty := by
        intro values
        induction values with
        | nil => intro _; exact .nil
        | cons child values ih =>
            intro included
            exact .cons (independent_closed_self_aux child
              (allClosed child (included child (by simp))))
              (independent_empty_merge Bindings.empty)
              (ih (fun value member => included value (by simp [member])))
      exact build children (fun _ member => member)
termination_by sizeOf type
decreasing_by
  rw [shape, Atom.expression.sizeOf_spec]
  exact Nat.lt_of_lt_of_le (List.sizeOf_lt_of_mem (included child (by simp)))
    (Nat.le_add_left _ _)

/-- Structural matching of a closed type constructs the independent match
and merge judgments, while retaining arbitrary incoming binding records. -/
theorem closed_type_match (type : Atom) (bindings : Bindings) (fuel : Nat)
    (closed : TypeSubst.typeVars type = [])
    (enough : sizeOf type + sizeOf type + 2 ≤ fuel) :
    matchTypes type type bindings fuel = [bindings] ∧
      TypeMatchRel type type bindings bindings := by
  constructor
  · unfold matchTypes
    split
    · rfl
    · rw [(closed_match_exact fuel).1 type type closed closed enough]
      have positive : 0 < fuel := by omega
      cases fuel with
      | zero => omega
      | succ fuel => simp [mergeBindings, Bindings.empty]
  · by_cases undefined : type = Atom.undefinedType
    · subst type; exact .undefinedLeft _ _
    · by_cases raw : type = Atom.atomType
      · subst type; exact .atomLeft _ _
      · exact .structural undefined raw undefined raw
          (independent_closed_self_aux type closed) (independent_empty_merge bindings)

private theorem independent_closed_match_unique (left right : Atom) (output : Bindings)
    (leftClosed : TypeSubst.typeVars left = []) (rightClosed : TypeSubst.typeVars right = [])
    (matched : Spec.Match.Merge.MatchRel Spec.Match.Merge.equalityGroundedSemantic left right output) :
    left = right ∧ output = Bindings.empty := by
  induction left using (measure (sizeOf (α := Atom))).wf.induction generalizing right output with
  | h left recur =>
    cases matched with
    | symSym => exact ⟨rfl, rfl⟩
    | varVar => simp [TypeSubst.typeVars] at leftClosed
    | varNonVar => simp [TypeSubst.typeVars] at leftClosed
    | nonVarVar => simp [TypeSubst.typeVars] at rightClosed
    | @expression children others output items _ =>
        have allLeft := typeVarsList_closed leftClosed
        have allRight := typeVarsList_closed rightClosed
        have solve : ∀ xs ys : List Atom, ∀ seed result : Bindings,
            (∀ child ∈ xs, child ∈ children) → (∀ child ∈ ys, child ∈ others) →
            Spec.Match.Merge.MatchListAccRel Spec.Match.Merge.equalityGroundedSemantic
              xs ys seed result → xs = ys ∧ result = seed := by
          intro xs
          induction xs with
          | nil =>
              intro ys seed result _ _ derivation
              cases derivation
              exact ⟨rfl, rfl⟩
          | cons child xs ih =>
              intro ys seed result includedLeft includedRight derivation
              cases derivation with
              | @cons _ other _ rest _ matched next _ head merge tail =>
                  obtain ⟨same, empty⟩ := recur child (by
                    change sizeOf child < sizeOf (Atom.expression children)
                    rw [Atom.expression.sizeOf_spec]
                    exact Nat.lt_of_lt_of_le
                      (List.sizeOf_lt_of_mem (includedLeft child (by simp)))
                      (Nat.le_add_left _ _)) other matched
                    (allLeft child (includedLeft child (by simp)))
                    (allRight other (includedRight other (by simp))) head
                  subst other
                  subst matched
                  have nextSame := Spec.Match.Merge.mergeRel_empty_right_eq merge
                  subst next
                  obtain ⟨tails, finished⟩ := ih rest seed result
                    (fun value member => includedLeft value (by simp [member]))
                    (fun value member => includedRight value (by simp [member])) tail
                  exact ⟨congrArg (List.cons child) tails, finished⟩
        obtain ⟨same, empty⟩ := solve children others Bindings.empty output
          (fun _ member => member) (fun _ member => member) items
        exact ⟨congrArg Atom.expression same, empty⟩
    | groundedLeftCustom _ _ custom _ =>
        obtain ⟨rfl, rfl⟩ := custom
        exact ⟨rfl, rfl⟩
    | groundedRightCustom _ notCustom _ custom _ =>
        obtain ⟨rfl, rfl⟩ := custom
        exact (notCustom (by trivial)).elim
    | groundedFallback notCustom _ _ => exact (notCustom (by trivial)).elim
  /-- Closed structural types have exactly the published outer wildcard cases
and ordinary equality. This predicate does not replace variable matching. -/
def ClosedTypeFits (expected actual : Atom) : Prop :=
  expected = Atom.undefinedType ∨ expected = Atom.atomType ∨
    actual = Atom.undefinedType ∨ actual = Atom.atomType ∨ expected = actual

/-- Both directions connect independently specified closed matching to the
existing executable matcher. Failure excludes every independent output. -/
theorem closed_type_match_iff (expected actual : Atom) (incoming output : Bindings)
    (expectedClosed : TypeSubst.typeVars expected = [])
    (actualClosed : TypeSubst.typeVars actual = []) :
    TypeMatchRel expected actual incoming output ↔ ClosedTypeFits expected actual ∧ output = incoming := by
  constructor
  · intro matched
    cases matched with
    | undefinedLeft => exact ⟨Or.inl rfl, rfl⟩
    | atomLeft => exact ⟨Or.inr (Or.inl rfl), rfl⟩
    | undefinedRight => exact ⟨Or.inr (Or.inr (Or.inl rfl)), rfl⟩
    | atomRight => exact ⟨Or.inr (Or.inr (Or.inr (Or.inl rfl))), rfl⟩
    | structural _ _ _ _ matched merged =>
        obtain ⟨same, empty⟩ := independent_closed_match_unique expected actual _
          expectedClosed actualClosed matched
        subst empty
        exact ⟨Or.inr (Or.inr (Or.inr (Or.inr same))),
          Spec.Match.Merge.mergeRel_empty_right_eq merged⟩
  · rintro ⟨fits, rfl⟩
    rcases fits with undefined | raw | undefined | raw | same
    · subst expected; exact .undefinedLeft _ _
    · subst expected; exact .atomLeft _ _
    · subst actual; exact .undefinedRight _ _
    · subst actual; exact .atomRight _ _
    · subst actual
      by_cases undefined : expected = Atom.undefinedType
      · subst expected; exact .undefinedLeft _ _
      · by_cases raw : expected = Atom.atomType
        · subst expected; exact .atomLeft _ _
        · exact .structural undefined raw undefined raw
            (independent_closed_self_aux expected expectedClosed) (independent_empty_merge _)

instance (expected actual : Atom) : Decidable (ClosedTypeFits expected actual) :=
  inferInstanceAs (Decidable (_ ∨ _ ∨ _ ∨ _ ∨ _))

theorem closed_matchTypes_exact (expected actual : Atom) (bindings : Bindings) (fuel : Nat)
    (expectedClosed : TypeSubst.typeVars expected = [])
    (actualClosed : TypeSubst.typeVars actual = [])
    (enough : sizeOf expected + sizeOf actual + 2 ≤ fuel) :
    matchTypes expected actual bindings fuel =
      if ClosedTypeFits expected actual then [bindings] else [] := by
  unfold matchTypes
  by_cases wildcard : expected = Atom.undefinedType ∨ expected = Atom.atomType ∨
      actual = Atom.undefinedType ∨ actual = Atom.atomType
  · have fits : ClosedTypeFits expected actual := by
      rcases wildcard with h | h | h | h <;> simp [ClosedTypeFits, h]
    have gate : (expected == Atom.undefinedType || expected == Atom.atomType ||
        actual == Atom.undefinedType || actual == Atom.atomType) = true := by
      simpa only [Bool.or_eq_true, beq_iff_eq, or_assoc] using wildcard
    rw [if_pos gate, if_pos fits]
  · have notWildcard : expected ≠ Atom.undefinedType ∧ expected ≠ Atom.atomType ∧
        actual ≠ Atom.undefinedType ∧ actual ≠ Atom.atomType := by simpa using wildcard
    simp only [beq_iff_eq, Bool.or_eq_true, notWildcard.1, notWildcard.2.1,
      notWildcard.2.2.1, notWildcard.2.2.2, or_self, ite_false]
    rw [(closed_match_exact fuel).1 expected actual expectedClosed actualClosed enough]
    by_cases same : expected = actual
    · have positive : 0 < fuel := by omega
      cases fuel with
      | zero => omega
      | succ fuel => simp [same, ClosedTypeFits, mergeBindings, Bindings.empty]
    · have fits : ¬ClosedTypeFits expected actual := by simp [ClosedTypeFits, notWildcard, same]
      simp [same, fits]

/-- Incompatible closed types cannot acquire a match at a smaller budget.
This uses the existing matcher's proved monotonicity, rather than interpreting
fuel exhaustion as a semantic rejection. -/
theorem closed_matchTypes_failure (expected actual : Atom) (bindings : Bindings) (fuel : Nat)
    (expectedClosed : TypeSubst.typeVars expected = [])
    (actualClosed : TypeSubst.typeVars actual = [])
    (incompatible : ¬ClosedTypeFits expected actual) :
    matchTypes expected actual bindings fuel = [] := by
  have different : expected ≠ actual := fun same => incompatible (by simp [ClosedTypeFits, same])
  have notWildcard : expected ≠ Atom.undefinedType ∧ expected ≠ Atom.atomType ∧
      actual ≠ Atom.undefinedType ∧ actual ≠ Atom.atomType := by
    have excluded : expected ≠ Atom.undefinedType ∧ expected ≠ Atom.atomType ∧
        actual ≠ Atom.undefinedType ∧ actual ≠ Atom.atomType ∧ expected ≠ actual := by
      simpa [ClosedTypeFits] using incompatible
    exact ⟨excluded.1, excluded.2.1, excluded.2.2.1, excluded.2.2.2.1⟩
  have noMatch : matchAtoms expected actual fuel = [] := by
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro output matched
    let larger := max fuel (sizeOf expected + sizeOf actual + 2)
    have retained := DeclMatchSpec.matchAtoms_mono expected actual fuel (larger - fuel) matched
    have total : fuel + (larger - fuel) = larger := Nat.add_sub_of_le (Nat.le_max_left _ _)
    rw [total] at retained
    have exactMatch := (closed_match_exact larger).1 expected actual expectedClosed actualClosed
      (Nat.le_max_right _ _)
    rw [exactMatch, if_neg different] at retained
    exact List.not_mem_nil retained
  simp [matchTypes, notWildcard.1, notWildcard.2.1, notWildcard.2.2.1,
    notWildcard.2.2.2, noMatch]

theorem cast_first_fit_source (_space : Space) (value expected : Atom) (bindings : Bindings)
    (fuel : Nat) (earlier : List Atom) (actual : Atom) (later : List Atom)
    (expectedClosed : TypeSubst.typeVars expected = [])
    (earlierClosed : ∀ type ∈ earlier, TypeSubst.typeVars type = [])
    (earlierFailed : ∀ type ∈ earlier, ¬ClosedTypeFits expected type)
    (actualClosed : TypeSubst.typeVars actual = []) (actualFits : ClosedTypeFits expected actual)
    (enough : sizeOf expected + sizeOf actual + 2 ≤ fuel) (failures : List Atom) :
    typeCast.typeCastLoop (earlier ++ actual :: later) value expected bindings fuel failures =
      [(value, bindings)] := by
  induction earlier generalizing failures with
  | nil =>
      simp only [List.nil_append, typeCast.typeCastLoop,
        closed_matchTypes_exact expected actual bindings fuel expectedClosed actualClosed enough,
        if_pos actualFits, List.isEmpty_cons, Bool.false_eq_true, ite_false,
        List.map_cons, List.map_nil]
  | cons type earlier ih =>
      rw [List.cons_append, typeCast.typeCastLoop,
        closed_matchTypes_failure expected type bindings fuel expectedClosed
          (earlierClosed type (by simp)) (earlierFailed type (by simp))]
      exact ih (fun type member => earlierClosed type (by simp [member]))
        (fun type member => earlierFailed type (by simp [member])) (failures ++ [type])

/-- A selected cast is earned from the actual ordered annotation list. The
source returns one binding occurrence; the independent rule records absence
of every earlier match and therefore the same first-success position. -/
theorem closed_cast_reply (space : Space) (value expected : Atom) (bindings : Bindings)
    (fuel : Nat) (earlier : List Atom) (actual : Atom) (later : List Atom)
    (types : getAtomTypes space value = earlier ++ actual :: later)
    (expectedClosed : TypeSubst.typeVars expected = [])
    (earlierClosed : ∀ type ∈ earlier, TypeSubst.typeVars type = [])
    (earlierFailed : ∀ type ∈ earlier, ¬ClosedTypeFits expected type)
    (actualClosed : TypeSubst.typeVars actual = []) (actualFits : ClosedTypeFits expected actual)
    (enough : sizeOf expected + sizeOf actual + 2 ≤ fuel) :
    typeCast value expected space bindings fuel = [(value, bindings)] ∧
      TypeCastRel space value expected bindings (value, bindings) := by
  constructor
  · unfold typeCast
    rw [types]
    exact cast_first_fit_source space value expected bindings fuel earlier actual later
      expectedClosed earlierClosed earlierFailed actualClosed actualFits enough []
  · exact .success (source_types space value) types
      (fun type member output matched => earlierFailed type member
        ((closed_type_match_iff expected type bindings output expectedClosed
          (earlierClosed type member)).mp matched).1)
      ((closed_type_match_iff expected actual bindings bindings expectedClosed actualClosed).mpr
        ⟨actualFits, rfl⟩)

def WildcardDomain (domain : Atom) : Prop := domain = Atom.atomType ∨ domain = Atom.undefinedType

instance (domain : Atom) : Decidable (WildcardDomain domain) :=
  inferInstanceAs (Decidable (_ ∨ _))

theorem wildcard_type_match (domain actual : Atom) (bindings : Bindings) (fuel : Nat)
    (wildcard : WildcardDomain domain) :
    matchTypes domain actual bindings fuel = [bindings] ∧ TypeMatchRel domain actual bindings bindings := by
  rcases wildcard with rfl | rfl
  · exact ⟨by simp [matchTypes, Atom.atomType], .atomLeft _ _⟩
  · exact ⟨by simp [matchTypes, Atom.undefinedType], .undefinedLeft _ _⟩

theorem wildcard_argument_check (space : Space) (argument domain : Atom) (bindings : Bindings)
    (fuel : Nat) (wildcard : WildcardDomain domain) :
    checkArgumentType space argument domain bindings fuel =
      List.replicate (getAtomTypes space argument).length (.inr bindings) := by
  unfold checkArgumentType
  simp only [(wildcard_type_match domain _ bindings fuel wildcard).1,
    List.isEmpty_cons, Bool.false_eq_true, ite_false, List.map_cons, List.map_nil]
  induction getAtomTypes space argument <;> simp_all [List.replicate_succ]

private theorem wildcard_argument_fold (space : Space) (argument domain expression : Atom)
    (bindings : Bindings) (fuel index count : Nat) (errors : List Atom) (successes : List Bindings)
    (wildcard : WildcardDomain domain) :
    (List.replicate count bindings).foldl (fun previous selected =>
      (checkArgumentType space argument domain selected fuel).foldl
        (fun previous checked => match checked with
          | .inl actual =>
              (previous.1 ++ [mkError expression (.badArgType index domain actual)], previous.2)
          | .inr next => (previous.1, previous.2 ++ [next])) (previous.1, previous.2))
      (errors, successes) =
        (errors, successes ++ List.replicate
          (count * (getAtomTypes space argument).length) bindings) := by
  simp only [wildcard_argument_check space argument domain _ fuel wildcard]
  induction count generalizing successes with
  | zero => simp
  | succ count ih =>
      simp only [List.replicate_succ, List.foldl_cons]
      rw [checked_successes, ih]
      simp only [List.append_assoc, ← List.replicate_add, Nat.succ_mul]
      rw [Nat.add_comm]

theorem wildcard_argument_loop (space : Space) (arguments domains : List Atom)
    (expression : Atom) (bindings : Bindings) (fuel index count : Nat) (errors : List Atom)
    (wildcards : List.Forall₂ (fun _ domain => WildcardDomain domain) arguments domains) :
    checkIfFunctionTypeIsApplicable.checkArgLoop arguments domains expression
      (List.replicate count bindings) errors space fuel index =
        (errors, List.replicate (count * pathCount space arguments) bindings) := by
  induction wildcards generalizing index count with
  | nil => simp [checkIfFunctionTypeIsApplicable.checkArgLoop, pathCount]
  | @cons argument domain arguments domains wildcard _ ih =>
      simp only [checkIfFunctionTypeIsApplicable.checkArgLoop]
      let checked := (List.replicate count bindings).foldl
        (fun previous selected => (checkArgumentType space argument domain selected fuel).foldl
          (fun previous result => match result with
            | .inl actual =>
                (previous.1 ++ [mkError expression (.badArgType index domain actual)], previous.2)
            | .inr next => (previous.1, previous.2 ++ [next]))
          (previous.1, previous.2)) (errors, [])
      have folded : checked = (errors, List.replicate
          (count * (getAtomTypes space argument).length) bindings) := by
        exact wildcard_argument_fold space argument domain expression bindings fuel index count errors [] wildcard
      change checkIfFunctionTypeIsApplicable.checkArgLoop arguments domains expression
        checked.2 checked.1 space fuel (index + 1) = _
      rw [folded]
      rw [ih]
      simp [pathCount, Nat.mul_assoc]

theorem independent_wildcard_arguments (space : Space) (arguments domains : List Atom)
    (bindings : Bindings)
    (wildcards : List.Forall₂ (fun _ domain => WildcardDomain domain) arguments domains) :
    ArgumentsApplicableRel space arguments domains bindings bindings := by
  induction wildcards with
  | nil => exact .nil bindings
  | @cons argument domain arguments domains wildcard _ ih =>
      obtain ⟨actual, member⟩ := List.exists_mem_of_ne_nil _ (getAtomTypes_nonempty space argument)
      exact .cons ((Conformance.typeOfRel_iff_mem_getAtomTypes space argument actual).mpr member)
        (wildcard_type_match domain actual bindings 0 wildcard).2 ih

private theorem failed_return_fold (bindings : Bindings) (error : Atom) (count : Nat)
    (errors : List Atom) (successes : List Bindings) :
    (List.replicate count bindings).foldl (fun previous _ =>
      (previous.1 ++ [error], previous.2)) (errors, successes) =
        (errors ++ List.replicate count error, successes) := by
  induction count generalizing errors with
  | zero => simp
  | succ count ih =>
      simp only [List.replicate_succ, List.foldl_cons]
      rw [ih]
      simp [List.append_assoc]

/-- A wildcard argument policy still checks its declared return type. A
closed return mismatch rejects the whole selected type, with one retained
error occurrence for every actual-type path. -/
theorem wildcard_applicability_failure (space : Space) (operator expected returned : Atom)
    (arguments domains : List Atom) (bindings : Bindings) (fuel : Nat)
    (wildcards : List.Forall₂ (fun _ domain => WildcardDomain domain) arguments domains)
    (expectedClosed : TypeSubst.typeVars expected = [])
    (returnedClosed : TypeSubst.typeVars returned = [])
    (incompatible : ¬ClosedTypeFits expected returned) :
    checkIfFunctionTypeIsApplicable (.expression (operator :: arguments))
      (.expression (.symbol "->" :: (domains ++ [returned]))) expected space bindings (fuel + 1) =
      .inl (List.replicate (pathCount space arguments)
        (mkError (.expression (operator :: arguments)) (.badType expected returned))) := by
  have sameLength := List.Forall₂.length_eq wildcards
  have checked : checkIfFunctionTypeIsApplicable.checkArgLoop arguments domains
      (.expression (operator :: arguments)) [bindings] [] space fuel 1 =
        ([], List.replicate (pathCount space arguments) bindings) := by
    simpa using wildcard_argument_loop space arguments domains (.expression (operator :: arguments))
      bindings fuel 1 1 [] wildcards
  have nonempty : (List.replicate (pathCount space arguments) bindings).isEmpty = false := by
    simp [pathCount_positive space arguments |>.ne']
  simp only [checkIfFunctionTypeIsApplicable, arrow_arguments, arrow_return]
  rw [show (arguments.length != domains.length) = false from by simp [sameLength]]
  simp only [Bool.false_eq_true, ite_false]
  rw [checked]
  simp only [nonempty, Bool.false_eq_true, ite_false]
  simp only [closed_matchTypes_failure expected returned _ fuel expectedClosed returnedClosed incompatible,
    List.isEmpty_nil, ite_true]
  rw [failed_return_fold]
  simp

theorem wildcard_applicability_success (space : Space) (operator expected returned : Atom)
    (arguments domains : List Atom) (bindings : Bindings) (fuel : Nat)
    (wildcards : List.Forall₂ (fun _ domain => WildcardDomain domain) arguments domains)
    (expectedClosed : TypeSubst.typeVars expected = [])
    (returnedClosed : TypeSubst.typeVars returned = [])
    (fits : ClosedTypeFits expected returned)
    (enough : sizeOf expected + sizeOf returned + 2 ≤ fuel) :
    checkIfFunctionTypeIsApplicable (.expression (operator :: arguments))
      (.expression (.symbol "->" :: (domains ++ [returned]))) expected space bindings (fuel + 1) =
      .inr (List.replicate (pathCount space arguments) bindings) := by
  have sameLength := List.Forall₂.length_eq wildcards
  have checked : checkIfFunctionTypeIsApplicable.checkArgLoop arguments domains
      (.expression (operator :: arguments)) [bindings] [] space fuel 1 =
        ([], List.replicate (pathCount space arguments) bindings) := by
    simpa using wildcard_argument_loop space arguments domains (.expression (operator :: arguments))
      bindings fuel 1 1 [] wildcards
  have nonempty : (List.replicate (pathCount space arguments) bindings).isEmpty = false := by
    simp [pathCount_positive space arguments |>.ne']
  simp only [checkIfFunctionTypeIsApplicable, arrow_arguments, arrow_return]
  rw [show (arguments.length != domains.length) = false from by simp [sameLength]]
  simp only [Bool.false_eq_true, ite_false]
  rw [checked]
  simp only [nonempty, Bool.false_eq_true, ite_false]
  simp only [closed_matchTypes_exact expected returned _ fuel expectedClosed returnedClosed enough,
    if_pos fits, List.isEmpty_cons, Bool.false_eq_true, ite_false]
  rw [pair_append_fold]
  simp [nonempty]

theorem closed_return_excludes_success (space : Space) (operator expected returned : Atom)
    (arguments domains : List Atom) (incoming output : Bindings)
    (expectedClosed : TypeSubst.typeVars expected = [])
    (returnedClosed : TypeSubst.typeVars returned = [])
    (incompatible : ¬ClosedTypeFits expected returned) :
    ¬ApplicationSuccessRel space (.expression (operator :: arguments))
      (.expression (.symbol "->" :: (domains ++ [returned]))) expected incoming output := by
  intro success
  cases success with
  | mk shape arrow _ matchReturn =>
      have returnSame := (FunctionTypeRel.unique arrow (show FunctionTypeRel
        (.expression (.symbol "->" :: (domains ++ [returned]))) domains returned from rfl)).2
      rw [returnSame] at matchReturn
      exact incompatible ((closed_type_match_iff expected returned _ _ expectedClosed returnedClosed).mp
        matchReturn).1

theorem independent_bad_return (space : Space) (operator expected returned : Atom)
    (arguments domains : List Atom) (bindings : Bindings)
    (wildcards : List.Forall₂ (fun _ domain => WildcardDomain domain) arguments domains)
    (expectedClosed : TypeSubst.typeVars expected = [])
    (returnedClosed : TypeSubst.typeVars returned = [])
    (incompatible : ¬ClosedTypeFits expected returned) :
    ApplicabilityRel space (.expression (operator :: arguments))
      (.expression (.symbol "->" :: (domains ++ [returned]))) expected bindings
      (.error (mkError (.expression (operator :: arguments)) (.badType expected returned))) :=
  .badReturn rfl rfl (independent_wildcard_arguments space arguments domains bindings wildcards)
    (fun output matchReturn => incompatible
      ((closed_type_match_iff expected returned bindings output expectedClosed returnedClosed).mp matchReturn).1)
    (fun output => closed_return_excludes_success space operator expected returned arguments domains
      bindings output expectedClosed returnedClosed incompatible)

theorem independent_wildcard_application (space : Space) (operator expected returned : Atom)
    (arguments domains : List Atom) (bindings : Bindings)
    (wildcards : List.Forall₂ (fun _ domain => WildcardDomain domain) arguments domains)
    (expectedClosed : TypeSubst.typeVars expected = [])
    (returnedClosed : TypeSubst.typeVars returned = [])
    (fits : ClosedTypeFits expected returned) :
    ApplicationSuccessRel space (.expression (operator :: arguments))
      (.expression (.symbol "->" :: (domains ++ [returned]))) expected bindings bindings :=
  .mk rfl rfl (independent_wildcard_arguments space arguments domains bindings wildcards)
    ((closed_type_match_iff expected returned bindings bindings expectedClosed returnedClosed).mpr ⟨fits, rfl⟩)

end Mettapedia.Languages.MeTTa.HE.FirstSuccessSourceApplicability
