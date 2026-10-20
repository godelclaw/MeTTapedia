import Mettapedia.Languages.MeTTa.HE.FirstSuccessSourceReplies
import Mettapedia.Languages.MeTTa.HE.FirstSuccessPreparedArguments
import Mettapedia.Languages.MeTTa.HE.DeclMatchSpec

/-!
# Actual-source applicability witnesses and retained path multiplicity

Wildcard and closed argument domains are connected to independent applicability
judgments for arbitrary argument syntax and binding environments. The existing
source type checker visits every actual-type occurrence. Its complete binding
reply retains the product of accepted occurrences, including duplicates, while
rejected paths retain their source positions and error chronology. Wrong arity
and exhausted argument checks produce independent errors and exclude success.

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
  simp [checkArgumentType, rawTypeLookup, matchTypes, List.flatMap_def]

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
                  simp [matchAtoms, getMetaType, Bindings.hasLoop_empty]
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
                  simp [matchAtoms, getMetaType, Bindings.hasLoop_empty]
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
                  by_cases same : children = others <;> simp [same, Bindings.hasLoop_empty]
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

section StructuralCoverage
open Mettapedia.Machines.ReadOnlyQuery

theorem merge_empty_covered (bindings : Bindings) (depth : Nat) :
    matchCovered (depth + 1) (.merge bindings Bindings.empty) = true := by
  simp [matchCovered, depthCovered, MatchDepth.body, Bindings.empty, run_bind,
    foldQueries, run]

/-- Closed structural matching earns its recursion coverage from the size
of the two syntax trees. The accumulator may retain any incoming bindings. -/
theorem closed_match_covered (fuel : Nat) :
    (∀ left right : Atom, TypeSubst.typeVars left = [] → TypeSubst.typeVars right = [] →
      sizeOf left + sizeOf right + 2 ≤ fuel →
      matchCovered fuel (.atoms left right) = true) ∧
    (∀ left right : List Atom, TypeSubst.typeVarsList left = [] →
      TypeSubst.typeVarsList right = [] → sizeOf left + sizeOf right + 2 ≤ fuel →
      ∀ acc, matchCovered fuel (.lists left right acc) = true) := by
  induction fuel with
  | zero => constructor <;> intro left right _ _ enough <;> omega
  | succ fuel ih =>
      constructor
      · intro left right leftClosed rightClosed enough
        cases left with
        | var name => simp [TypeSubst.typeVars] at leftClosed
        | symbol name =>
            cases right with
            | var name => simp [TypeSubst.typeVars] at rightClosed
            | symbol other =>
                by_cases same : name = other <;>
                  simp [matchCovered, depthCovered, MatchDepth.body, MatchDepth.rawAtoms,
                    getMetaType, run_map, run, same]
            | grounded value => simp [matchCovered, depthCovered, MatchDepth.body, MatchDepth.rawAtoms,
                getMetaType, run_map, run]
            | expression children => simp [matchCovered, depthCovered, MatchDepth.body, MatchDepth.rawAtoms,
                getMetaType, run_map, run]
        | grounded value =>
            cases right with
            | var name => simp [TypeSubst.typeVars] at rightClosed
            | symbol name => simp [matchCovered, depthCovered, MatchDepth.body, MatchDepth.rawAtoms,
                getMetaType, run_map, run]
            | expression children => simp [matchCovered, depthCovered, MatchDepth.body, MatchDepth.rawAtoms,
                getMetaType, run_map, run]
            | grounded other => simp [matchCovered, depthCovered, MatchDepth.body, MatchDepth.rawAtoms,
                getMetaType, run_map, run]
        | expression children =>
            cases right with
            | var name => simp [TypeSubst.typeVars] at rightClosed
            | symbol name => simp [matchCovered, depthCovered, MatchDepth.body, MatchDepth.rawAtoms,
                getMetaType, run_map, run]
            | grounded value => simp [matchCovered, depthCovered, MatchDepth.body, MatchDepth.rawAtoms,
                getMetaType, run_map, run]
            | expression others =>
                have enough' : sizeOf children + sizeOf others + 2 ≤ fuel := by
                  simp only [Atom.expression.sizeOf_spec] at enough
                  omega
                have checked := ih.2 children others leftClosed rightClosed enough' [Bindings.empty]
                by_cases lengths : children.length = others.length
                · simpa [matchCovered, depthCovered, MatchDepth.body, MatchDepth.rawAtoms,
                    getMetaType, run_map, run, lengths] using checked
                · simp [matchCovered, depthCovered, MatchDepth.body, MatchDepth.rawAtoms,
                    getMetaType, run_map, run, lengths]
      · intro left right leftClosed rightClosed enough acc
        cases left with
        | nil => cases right <;> simp [matchCovered, depthCovered, MatchDepth.body, run]
        | cons head tail =>
            cases right with
            | nil => simp [matchCovered, depthCovered, MatchDepth.body, run]
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
                have checkedHead := ih.1 head other closedLeft.1 closedRight.1 enoughHead
                have checkedTail := ih.2 tail rest closedLeft.2 closedRight.2 enoughTail
                have matched := (closed_match_exact fuel).1 head other
                  closedLeft.1 closedRight.1 enoughHead
                have positive : 0 < fuel := by omega
                have merged : ∀ b, mergeBindings b Bindings.empty fuel = [b] := by
                  intro b
                  cases fuel with
                  | zero => omega
                  | succ fuel => simp [mergeBindings, Bindings.empty]
                have mergeReady : ∀ b, matchCovered fuel (.merge b Bindings.empty) = true := by
                  intro b
                  cases fuel with
                  | zero => omega
                  | succ fuel => exact merge_empty_covered b fuel
                rw [matchCovered, depthCovered]
                simp only [MatchDepth.body, run_bind, run, run_flatTraverse, evalMatch,
                  matched]
                unfold matchCovered at checkedHead checkedTail mergeReady
                by_cases same : head = other
                · subst other
                  simp [checkedHead, checkedTail, merged, mergeReady, run_flatTraverse_reads,
                    flatTraverse, run_bind, run_map, run]
                · simp [same, checkedHead, checkedTail, run_flatTraverse_reads, flatTraverse, run]


/-- The native cast matcher needs no arbitrary merge admission for closed
types: every successful structural match has the empty added environment. -/
theorem closed_matchTypes_covered (expected actual : Atom) (bindings : Bindings)
    (fuel : Nat) (expectedClosed : TypeSubst.typeVars expected = [])
    (actualClosed : TypeSubst.typeVars actual = [])
    (enough : sizeOf expected + sizeOf actual + 2 ≤ fuel) :
    matchTypesCovered expected actual bindings fuel = true := by
  have structural := (closed_match_covered fuel).1 expected actual expectedClosed actualClosed enough
  have matched := (closed_match_exact fuel).1 expected actual expectedClosed actualClosed enough
  have merged : matchCovered fuel (.merge bindings Bindings.empty) = true := by
    cases fuel with
    | zero => omega
    | succ fuel => exact merge_empty_covered bindings fuel
  simp only [matchTypesCovered, MatchDepth.queryCovered, MatchDepth.typesQuery]
  split
  · rfl
  · simp only [run, evalMatch, matched]
    by_cases same : expected = actual
    · subst actual
      simp [run_flatTraverse_reads, run, structural, merged]
    · simp [same, flatTraverse, run, structural]

theorem closed_castLoop_covered (types : List Atom) (atom expected : Atom)
    (bindings : Bindings) (fuel : Nat) (errors : List Atom)
    (expectedClosed : TypeSubst.typeVars expected = [])
    (allClosed : ∀ actual ∈ types, TypeSubst.typeVars actual = [])
    (enough : ∀ actual ∈ types, sizeOf expected + sizeOf actual + 2 ≤ fuel) :
    MatchDepth.queryCovered fuel
      (TypeCheckDepth.castLoopQuery types atom expected bindings errors) = true := by
  induction types generalizing errors with
  | nil => rfl
  | cons actual remaining ih =>
      have head := closed_matchTypes_covered expected actual bindings fuel expectedClosed
        (allClosed actual (by simp)) (enough actual (by simp))
      have tail := fun errors => ih errors (fun t h => allClosed t (List.mem_cons_of_mem _ h))
        (fun t h => enough t (List.mem_cons_of_mem _ h))
      change MatchDepth.queryCovered fuel (bind (MatchDepth.typesQuery expected actual bindings)
        (fun matched => if matched.isEmpty then
          TypeCheckDepth.castLoopQuery remaining atom expected bindings (errors ++ [actual])
          else .pure (matched.map fun m => (atom, m)))) = true
      simp only [MatchDepth.queryCovered, run_bind, List.all_append, Bool.and_eq_true]
      refine ⟨head, ?_⟩
      split
      · exact tail (errors ++ [actual])
      · rfl

/-- A finite syntax-size bound covers every cast lookup, including failed
source type occurrences. Incoming bindings may be open and nonempty. -/
theorem closed_typeCast_covered (space : Space) (atom expected : Atom)
    (bindings : Bindings) (fuel : Nat)
    (expectedClosed : TypeSubst.typeVars expected = [])
    (allClosed : ∀ actual ∈ getAtomTypes space atom, TypeSubst.typeVars actual = [])
    (enough : sizeOf expected + sizeOf (getAtomTypes space atom) + 2 ≤ fuel) :
    typeCastCovered atom expected space bindings fuel = true := by
  apply closed_castLoop_covered _ _ _ _ _ [] expectedClosed allClosed
  intro actual member
  have smaller := List.sizeOf_lt_of_mem member
  omega


end StructuralCoverage

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
    simp only [rawTypeLookup]
    rw [types]
    exact cast_first_fit_source space value expected bindings fuel earlier actual later
      expectedClosed earlierClosed earlierFailed actualClosed actualFits enough []
  · exact .success (source_types space value) types
      (fun type member output matched => earlierFailed type member
        ((closed_type_match_iff expected type bindings output expectedClosed
          (earlierClosed type member)).mp matched).1)
      ((closed_type_match_iff expected actual bindings bindings expectedClosed actualClosed).mpr
        ⟨actualFits, rfl⟩)

/-- A completely rejected closed cast retains one error for each physical type
occurrence. Rejection is proved semantically at every matching depth. -/
theorem cast_all_rejected_source (value expected : Atom) (bindings : Bindings)
    (fuel : Nat) (types failures : List Atom)
    (expectedClosed : TypeSubst.typeVars expected = [])
    (closed : ∀ actual ∈ types, TypeSubst.typeVars actual = [])
    (rejected : ∀ actual ∈ types, ¬ClosedTypeFits expected actual) :
    typeCast.typeCastLoop types value expected bindings fuel failures =
      (failures ++ types).map (fun actual => (mkError value (.badType expected actual), bindings)) := by
  induction types generalizing failures with
  | nil => simp [typeCast.typeCastLoop]
  | cons actual rest ih =>
      rw [typeCast.typeCastLoop,
        closed_matchTypes_failure expected actual bindings fuel expectedClosed
          (closed actual (List.mem_cons_self)) (rejected actual (List.mem_cons_self))]
      simp only [List.isEmpty_nil, if_true]
      rw [ih (failures ++ [actual])
        (fun next member => closed next (List.mem_cons_of_mem _ member))
        (fun next member => rejected next (List.mem_cons_of_mem _ member))]
      simp only [List.append_assoc, List.singleton_append]

/-- Actual closed-type rejection supplies independent error derivations. No
empty bounded matcher run is accepted as an independent no-match proof. -/
theorem closed_cast_failure_reply (space : Space) (value expected : Atom) (bindings : Bindings)
    (fuel : Nat)
    (expectedClosed : TypeSubst.typeVars expected = [])
    (closed : ∀ actual ∈ getAtomTypes space value, TypeSubst.typeVars actual = [])
    (rejected : ∀ actual ∈ getAtomTypes space value, ¬ClosedTypeFits expected actual) :
    typeCast value expected space bindings fuel =
      (getAtomTypes space value).map (fun actual => (mkError value (.badType expected actual), bindings)) ∧
    ∀ actual ∈ getAtomTypes space value,
      TypeCastRel space value expected bindings (mkError value (.badType expected actual), bindings) := by
  refine ⟨?_, ?_⟩
  · simpa only [typeCast, rawTypeLookup, List.nil_append] using
      cast_all_rejected_source value expected bindings fuel (getAtomTypes space value) []
        expectedClosed closed rejected
  · intro actual present
    apply TypeCastRel.failure (source_types space value) present
    intro candidate member output matched
    exact rejected candidate member
      ((closed_type_match_iff expected candidate bindings output expectedClosed
        (closed candidate member)).mp matched).1


/-- For a completely rejected closed cast, the computed list and independent
source relation agree in both directions. The list retains multiplicity. -/
theorem closed_cast_failure_iff (space : Space) (value expected : Atom) (bindings : Bindings)
    (fuel : Nat)
    (expectedClosed : TypeSubst.typeVars expected = [])
    (closed : ∀ actual ∈ getAtomTypes space value, TypeSubst.typeVars actual = [])
    (rejected : ∀ actual ∈ getAtomTypes space value, ¬ClosedTypeFits expected actual)
    (result : ResultPair) :
    result ∈ typeCast value expected space bindings fuel ↔
      TypeCastRel space value expected bindings result := by
  obtain ⟨computed, errors⟩ := closed_cast_failure_reply space value expected bindings fuel
    expectedClosed closed rejected
  rw [computed]
  constructor
  · intro member
    obtain ⟨actual, present, rfl⟩ := List.mem_map.mp member
    exact errors actual present
  · intro source
    cases source with
    | @success _ types earlier later actual output inferred selected _ matched =>
        have actualMember : actual ∈ getAtomTypes space value := by
          rw [Conformance.typesOfRel_eq_getAtomTypes inferred, selected]
          simp
        exact (rejected actual actualMember
          ((closed_type_match_iff expected actual bindings output expectedClosed
            (closed actual actualMember)).mp matched).1).elim
    | @failure _ types actual inferred member _ =>
        exact List.mem_map.mpr ⟨actual,
          (by simpa only [Conformance.typesOfRel_eq_getAtomTypes inferred] using member), rfl⟩

def WildcardDomain (domain : Atom) : Prop := domain = Atom.atomType ∨ domain = Atom.undefinedType

instance (domain : Atom) : Decidable (WildcardDomain domain) :=
  inferInstanceAs (Decidable (_ ∨ _))

theorem wildcard_type_match (domain actual : Atom) (bindings : Bindings) (fuel : Nat)
    (wildcard : WildcardDomain domain) :
    matchTypes domain actual bindings fuel = [bindings] ∧ TypeMatchRel domain actual bindings bindings := by
  rcases wildcard with rfl | rfl
  · exact ⟨by simp [matchTypes, Atom.atomType], .atomLeft _ _⟩
  · exact ⟨by simp [matchTypes, Atom.undefinedType], .undefinedLeft _ _⟩

/-- Type-side evidence for an argument check which preserves the incoming
binding frame. Closed domains may accept some actual type occurrences and
reject others; wildcard domains also admit schematic actual types. -/
inductive ArgumentDomainEvidence (space : Space) (argument domain : Atom) (fuel : Nat) : Prop where
  | wildcard : WildcardDomain domain → ArgumentDomainEvidence space argument domain fuel
  | closed : TypeSubst.typeVars domain = [] →
      (∀ actual ∈ getAtomTypes space argument, TypeSubst.typeVars actual = []) →
      (∀ actual ∈ getAtomTypes space argument, sizeOf domain + sizeOf actual + 2 ≤ fuel) →
      ArgumentDomainEvidence space argument domain fuel

theorem wildcard_arguments_evidence (space : Space) (arguments domains : List Atom) (fuel : Nat)
    (wildcards : List.Forall₂ (fun _ domain => WildcardDomain domain) arguments domains) :
    List.Forall₂ (fun argument domain => ArgumentDomainEvidence space argument domain fuel)
      arguments domains :=
  List.Forall₂.imp (fun _ _ wildcard => .wildcard wildcard) wildcards

theorem ArgumentDomainEvidence.match_exact
    {space : Space} {argument domain : Atom} {fuel : Nat}
    (checked : ArgumentDomainEvidence space argument domain fuel)
    (actual : Atom) (member : actual ∈ getAtomTypes space argument) (bindings : Bindings) :
    matchTypes domain actual bindings fuel =
      if ClosedTypeFits domain actual then [bindings] else [] := by
  cases checked with
  | wildcard wildcard =>
      obtain ⟨matched, _⟩ := wildcard_type_match domain actual bindings fuel wildcard
      rw [matched]
      rcases wildcard with rfl | rfl <;> simp [ClosedTypeFits]
  | closed domainClosed actualClosed enough =>
      exact closed_matchTypes_exact domain actual bindings fuel domainClosed
        (actualClosed actual member) (enough actual member)

theorem ArgumentDomainEvidence.match_iff
    {space : Space} {argument domain : Atom} {fuel : Nat}
    (checked : ArgumentDomainEvidence space argument domain fuel)
    (actual : Atom) (member : actual ∈ getAtomTypes space argument) (incoming output : Bindings) :
    TypeMatchRel domain actual incoming output ↔
      ClosedTypeFits domain actual ∧ output = incoming := by
  cases checked with
  | wildcard wildcard =>
      constructor
      · intro matched
        have fits : ClosedTypeFits domain actual := by
          rcases wildcard with rfl | rfl <;> simp [ClosedTypeFits]
        refine ⟨fits, ?_⟩
        cases matched with
        | undefinedLeft => rfl
        | atomLeft => rfl
        | undefinedRight => rfl
        | atomRight => rfl
        | structural notUndefined notAtom _ _ _ _ =>
            rcases wildcard with raw | unknown
            · exact (notAtom raw).elim
            · exact (notUndefined unknown).elim
      · rintro ⟨_, rfl⟩
        rcases wildcard with rfl | rfl
        · exact .atomLeft _ _
        · exact .undefinedLeft _ _
  | closed domainClosed actualClosed _ =>
      exact closed_type_match_iff domain actual incoming output domainClosed (actualClosed actual member)

/-- A list presentation of every accepted and rejected actual-type occurrence.
The check's independently justified closed fit test is distinct from the
source matcher and its binding-merge implementation. -/
def argumentTypeOutcomes (space : Space) (argument domain : Atom) (bindings : Bindings) :
    List (Sum Atom Bindings) :=
  (getAtomTypes space argument).map fun actual =>
    if ClosedTypeFits domain actual then .inr bindings else .inl actual

theorem argument_check_exact {space : Space} {argument domain : Atom} {fuel : Nat}
    (checked : ArgumentDomainEvidence space argument domain fuel) (bindings : Bindings) :
    checkArgumentType space argument domain bindings fuel =
      argumentTypeOutcomes space argument domain bindings := by
  unfold checkArgumentType argumentTypeOutcomes
  calc
    _ = (getAtomTypes space argument).flatMap (fun actual =>
        [if ClosedTypeFits domain actual then (Sum.inr bindings : Sum Atom Bindings) else .inl actual]) := by
      apply List.flatMap_congr
      intro actual member
      rw [checked.match_exact actual member bindings]
      by_cases fits : ClosedTypeFits domain actual <;> simp [fits]
    _ = _ := by rw [← List.map_eq_flatMap]

def acceptedTypes (space : Space) (argument domain : Atom) : List Atom :=
  (getAtomTypes space argument).filter fun actual => decide (ClosedTypeFits domain actual)

/-- The successful type-path count, rather than the unfiltered raw-path
count. Duplicate fitting declarations remain separate occurrences. -/
def admittedPathCount (space : Space) : List Atom → List Atom → Nat
  | [], [] => 1
  | argument :: arguments, domain :: domains =>
      (acceptedTypes space argument domain).length * admittedPathCount space arguments domains
  | _, _ => 0

private theorem type_outcomes_fold (domain : Atom) (types : List Atom) (bindings : Bindings)
    (failure : Atom → Atom) (errors : List Atom) (successes : List Bindings) :
    (types.map fun actual => if ClosedTypeFits domain actual then
      (Sum.inr bindings : Sum Atom Bindings) else .inl actual).foldl
      (fun previous result => match result with
        | .inl actual => (previous.1 ++ [failure actual], previous.2)
        | .inr next => (previous.1, previous.2 ++ [next]))
      (errors, successes) =
        (errors ++ (types.filter fun actual => decide (¬ClosedTypeFits domain actual)).map failure,
          successes ++ List.replicate
            (types.filter fun actual => decide (ClosedTypeFits domain actual)).length bindings) := by
  induction types generalizing errors successes with
  | nil => simp
  | cons actual types ih =>
      by_cases fits : ClosedTypeFits domain actual
      · simp [fits, ih, List.replicate_succ, List.append_assoc]
      · simp [fits, ih, List.append_assoc]

/-- Error occurrences at one argument position, in actual-type order. -/
def argumentTypeErrors (space : Space) (argument domain expression : Atom) (index : Nat) : List Atom :=
  ((getAtomTypes space argument).filter fun actual => decide (¬ClosedTypeFits domain actual)).map
    fun actual => mkError expression (.badArgType index domain actual)

/-- Earlier binding paths repeat a position's complete error block before
the next position is visited. Zero successful paths stop later errors. -/
def argumentErrorBlocks (space : Space) (expression : Atom) :
    List Atom → List Atom → Nat → Nat → List Atom
  | argument :: arguments, domain :: domains, index, count =>
      (List.replicate count (argumentTypeErrors space argument domain expression index)).flatten ++
        argumentErrorBlocks space expression arguments domains (index + 1)
          (count * (acceptedTypes space argument domain).length)
  | _, _, _, _ => []

private theorem checked_argument_fold {space : Space} {argument domain : Atom} {fuel : Nat}
    (checked : ArgumentDomainEvidence space argument domain fuel)
    (expression : Atom) (bindings : Bindings) (index count : Nat)
    (errors : List Atom) (successes : List Bindings) :
    (List.replicate count bindings).foldl (fun previous selected =>
      (checkArgumentType space argument domain selected fuel).foldl
        (fun previous result => match result with
          | .inl actual => (previous.1 ++ [mkError expression (.badArgType index domain actual)], previous.2)
          | .inr next => (previous.1, previous.2 ++ [next])) (previous.1, previous.2))
      (errors, successes) =
        (errors ++ (List.replicate count (argumentTypeErrors space argument domain expression index)).flatten,
          successes ++ List.replicate (count * (acceptedTypes space argument domain).length) bindings) := by
  simp only [argument_check_exact checked, argumentTypeOutcomes]
  induction count generalizing errors successes with
  | zero => simp
  | succ count ih =>
      simp only [List.replicate_succ, List.foldl_cons]
      rw [type_outcomes_fold, ih]
      simp [argumentTypeErrors, acceptedTypes, List.append_assoc, Nat.succ_mul,
        Nat.add_comm]

/-- The complete applicability traversal retains successful path multiplicity
and the chronology of rejected actual types, under arbitrary prior errors and
incoming occurrence counts. -/
theorem argument_loop_exact (space : Space) (arguments domains : List Atom)
    (expression : Atom) (bindings : Bindings) (fuel index count : Nat) (errors : List Atom)
    (checked : List.Forall₂ (fun argument domain =>
      ArgumentDomainEvidence space argument domain fuel) arguments domains) :
    checkIfFunctionTypeIsApplicable.checkArgLoop arguments domains expression
      (List.replicate count bindings) errors space fuel index =
        (errors ++ argumentErrorBlocks space expression arguments domains index count,
          List.replicate (count * admittedPathCount space arguments domains) bindings) := by
  induction checked generalizing index count errors with
  | nil => simp [checkIfFunctionTypeIsApplicable.checkArgLoop, argumentErrorBlocks, admittedPathCount]
  | @cons argument domain arguments domains first rest ih =>
      simp only [checkIfFunctionTypeIsApplicable.checkArgLoop]
      let folded := (List.replicate count bindings).foldl (fun previous selected =>
        (checkArgumentType space argument domain selected fuel).foldl
          (fun previous result => match result with
            | .inl actual => (previous.1 ++ [mkError expression (.badArgType index domain actual)], previous.2)
            | .inr next => (previous.1, previous.2 ++ [next])) (previous.1, previous.2)) (errors, [])
      have computed : folded =
          (errors ++ (List.replicate count (argumentTypeErrors space argument domain expression index)).flatten,
            List.replicate (count * (acceptedTypes space argument domain).length) bindings) := by
        simpa only [List.nil_append] using checked_argument_fold first expression bindings index count errors []
      change checkIfFunctionTypeIsApplicable.checkArgLoop arguments domains expression
        folded.2 folded.1 space fuel (index + 1) = _
      rw [computed, ih]
      simp [argumentErrorBlocks, admittedPathCount, List.append_assoc, Nat.mul_assoc]

theorem acceptedTypes_wildcard (space : Space) (argument domain : Atom)
    (wildcard : WildcardDomain domain) : acceptedTypes space argument domain = getAtomTypes space argument := by
  apply List.filter_eq_self.mpr
  intro actual _
  rcases wildcard with rfl | rfl <;> simp [ClosedTypeFits]

theorem admittedPathCount_wildcards (space : Space) (arguments domains : List Atom)
    (wildcards : List.Forall₂ (fun _ domain => WildcardDomain domain) arguments domains) :
    admittedPathCount space arguments domains = pathCount space arguments := by
  induction wildcards with
  | nil => rfl
  | cons first _ ih =>
      simp only [admittedPathCount, acceptedTypes_wildcard _ _ _ first, ih, pathCount]

theorem argumentErrorBlocks_wildcards (space : Space) (expression : Atom) (arguments domains : List Atom)
    (index count : Nat)
    (wildcards : List.Forall₂ (fun _ domain => WildcardDomain domain) arguments domains) :
    argumentErrorBlocks space expression arguments domains index count = [] := by
  induction wildcards generalizing index count with
  | nil => rfl
  | @cons argument domain arguments domains first _ ih =>
      have noErrors : argumentTypeErrors space argument domain expression index = [] := by
        unfold argumentTypeErrors
        have rejected : (getAtomTypes space argument).filter
            (fun actual => decide (¬ClosedTypeFits domain actual)) = [] := by
          apply List.filter_eq_nil_iff.mpr
          intro actual _
          rcases first with rfl | rfl <;> simp [ClosedTypeFits]
        rw [rejected]
        rfl
      simp [argumentErrorBlocks, noErrors, ih]

/-- Independent applicability exists exactly when a successful type path
exists. The source order may contain several copies of that same frame. -/
theorem arguments_applicable_iff (space : Space) (arguments domains : List Atom) (fuel : Nat)
    (checked : List.Forall₂ (fun argument domain =>
      ArgumentDomainEvidence space argument domain fuel) arguments domains)
    (incoming output : Bindings) :
    ArgumentsApplicableRel space arguments domains incoming output ↔
      0 < admittedPathCount space arguments domains ∧ output = incoming := by
  induction checked generalizing incoming output with
  | nil =>
      constructor
      · intro related
        cases related
        exact ⟨Nat.zero_lt_one, rfl⟩
      · rintro ⟨_, same⟩
        subst output
        exact .nil incoming
  | @cons argument domain arguments domains first rest ih =>
      constructor
      · intro related
        cases related with
        | @cons _ _ _ actual _ _ _ next _ inferred matched tail =>
            have member := (Conformance.typeOfRel_iff_mem_getAtomTypes space argument actual).mp inferred
            obtain ⟨fits, same⟩ := (first.match_iff actual member incoming next).mp matched
            subst next
            obtain ⟨positive, sameOutput⟩ := ih incoming output |>.mp tail
            have accepted : actual ∈ acceptedTypes space argument domain := by
              simp only [acceptedTypes, List.mem_filter, decide_eq_true_eq]
              exact ⟨member, fits⟩
            exact ⟨Nat.mul_pos (List.length_pos_of_mem accepted) positive, sameOutput⟩
      · rintro ⟨positive, same⟩
        subst output
        have headPositive : 0 < (acceptedTypes space argument domain).length :=
          Nat.pos_of_mul_pos_right positive
        have tailPositive : 0 < admittedPathCount space arguments domains :=
          Nat.pos_of_mul_pos_left positive
        obtain ⟨actual, accepted⟩ := List.exists_mem_of_ne_nil _ (List.ne_nil_of_length_pos headPositive)
        obtain ⟨member, fits⟩ := List.mem_filter.mp accepted
        exact .cons ((Conformance.typeOfRel_iff_mem_getAtomTypes space argument actual).mpr member)
          ((first.match_iff actual member incoming incoming).mpr ⟨of_decide_eq_true fits, rfl⟩)
          ((ih incoming incoming).mpr ⟨tailPositive, rfl⟩)

theorem argumentErrorBlocks_zero (space : Space) (expression : Atom)
    (arguments domains : List Atom) (index : Nat) :
    argumentErrorBlocks space expression arguments domains index 0 = [] := by
  induction arguments generalizing domains index with
  | nil => cases domains <;> rfl
  | cons argument arguments ih =>
      cases domains with
      | nil => rfl
      | cons domain domains => simp [argumentErrorBlocks, ih]

/-- Every retained argument error is earned at an actual rejected type after
an independently applicable prefix. Its position is measured in source
arguments, and its untouched suffix has the right arity. -/
theorem argument_error_witness (space : Space) (arguments domains : List Atom) (fuel : Nat)
    (checked : List.Forall₂ (fun argument domain =>
      ArgumentDomainEvidence space argument domain fuel) arguments domains)
    (expression : Atom) (incoming : Bindings) (index count : Nat) (error : Atom)
    (member : error ∈ argumentErrorBlocks space expression arguments domains index count) :
    0 < count ∧ ∃ before typesBefore badArgument badDomain actual after typesAfter,
      arguments = before ++ badArgument :: after ∧
      domains = typesBefore ++ badDomain :: typesAfter ∧
      after.length = typesAfter.length ∧
      ArgumentsApplicableRel space before typesBefore incoming incoming ∧
      TypeOfRel space badArgument actual ∧
      (∀ candidate, ¬TypeMatchRel badDomain actual incoming candidate) ∧
      error = mkError expression (.badArgType (index + before.length) badDomain actual) := by
  induction checked generalizing index count with
  | nil => simp [argumentErrorBlocks] at member
  | @cons argument domain arguments domains first rest ih =>
      rcases List.mem_append.mp member with here | later
      · obtain ⟨block, repeated, inBlock⟩ := List.mem_flatten.mp here
        obtain ⟨countNonzero, sameBlock⟩ := List.mem_replicate.mp repeated
        subst block
        obtain ⟨actual, rejected, sameError⟩ := List.mem_map.mp inBlock
        obtain ⟨actualMember, incompatible⟩ := List.mem_filter.mp rejected
        refine ⟨Nat.pos_of_ne_zero countNonzero, [], [], argument, domain, actual,
          arguments, domains, rfl, rfl, List.Forall₂.length_eq rest, .nil incoming,
          (Conformance.typeOfRel_iff_mem_getAtomTypes space argument actual).mpr actualMember, ?_, ?_⟩
        · intro candidate matched
          exact of_decide_eq_true incompatible ((first.match_iff actual actualMember incoming candidate).mp matched).1
        · simpa only [List.length_nil, Nat.add_zero] using sameError.symm
      · obtain ⟨positive, before, typesBefore, badArgument, badDomain, actual, after, typesAfter,
            argumentsSame, domainsSame, arity, priorPath, inferred, rejected, errorSame⟩ :=
          ih (index + 1) (count * (acceptedTypes space argument domain).length) later
        have headPositive : 0 < (acceptedTypes space argument domain).length :=
          Nat.pos_of_mul_pos_left positive
        obtain ⟨accepted, acceptedMember⟩ := List.exists_mem_of_ne_nil _ (List.ne_nil_of_length_pos headPositive)
        obtain ⟨actualMember, fits⟩ := List.mem_filter.mp acceptedMember
        refine ⟨Nat.pos_of_mul_pos_right positive, argument :: before, domain :: typesBefore,
          badArgument, badDomain, actual, after, typesAfter, ?_, ?_, arity, ?_, inferred, rejected, ?_⟩
        · simp only [List.cons_append, argumentsSame]
        · simp only [List.cons_append, domainsSame]
        · exact .cons ((Conformance.typeOfRel_iff_mem_getAtomTypes space argument accepted).mpr actualMember)
            ((first.match_iff accepted actualMember incoming incoming).mpr ⟨of_decide_eq_true fits, rfl⟩) priorPath
        · simpa only [List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using errorSame

theorem argument_errors_nonempty (space : Space) (arguments domains : List Atom) (fuel : Nat)
    (checked : List.Forall₂ (fun argument domain =>
      ArgumentDomainEvidence space argument domain fuel) arguments domains)
    (expression : Atom) (index count : Nat) (positive : 0 < count)
    (exhausted : admittedPathCount space arguments domains = 0) :
    argumentErrorBlocks space expression arguments domains index count ≠ [] := by
  induction checked generalizing index count with
  | nil => simp [admittedPathCount] at exhausted
  | @cons argument domain arguments domains first rest ih =>
      by_cases headEmpty : (acceptedTypes space argument domain).length = 0
      · obtain ⟨actual, actualMember⟩ := List.exists_mem_of_ne_nil _ (getAtomTypes_nonempty space argument)
        have incompatible : ¬ClosedTypeFits domain actual := by
          intro fits
          have accepted : actual ∈ acceptedTypes space argument domain :=
            List.mem_filter.mpr ⟨actualMember, by simpa using fits⟩
          have nonempty := List.length_pos_of_mem accepted
          omega
        apply List.ne_nil_of_mem (a := mkError expression (.badArgType index domain actual))
        apply List.mem_append_left
        apply List.mem_flatten.mpr
        refine ⟨argumentTypeErrors space argument domain expression index,
          List.mem_replicate.mpr ⟨Nat.ne_of_gt positive, rfl⟩, ?_⟩
        exact List.mem_map.mpr ⟨actual, List.mem_filter.mpr ⟨actualMember, by simpa using incompatible⟩, rfl⟩
      · have headPositive : 0 < (acceptedTypes space argument domain).length := Nat.pos_of_ne_zero headEmpty
        have tailEmpty : admittedPathCount space arguments domains = 0 := by
          simpa only [admittedPathCount, Nat.mul_eq_zero, headEmpty, false_or] using exhausted
        obtain ⟨error, errorMember⟩ := List.exists_mem_of_ne_nil _
          (ih (index + 1) (count * (acceptedTypes space argument domain).length)
            (Nat.mul_pos positive headPositive) tailEmpty)
        exact List.ne_nil_of_mem (List.mem_append_right _ errorMember)

theorem checked_arguments_exclude_success (space : Space) (operator expected returned : Atom)
    (arguments domains : List Atom) (incoming output : Bindings) (fuel : Nat)
    (checked : List.Forall₂ (fun argument domain =>
      ArgumentDomainEvidence space argument domain fuel) arguments domains)
    (exhausted : admittedPathCount space arguments domains = 0) :
    ¬ApplicationSuccessRel space (.expression (operator :: arguments))
      (.expression (.symbol "->" :: (domains ++ [returned]))) expected incoming output := by
  intro success
  cases success with
  | mk shape arrow applicable _ =>
      obtain ⟨rfl, rfl⟩ := List.cons.inj (Atom.expression.inj shape)
      have sameDomains := (FunctionTypeRel.unique arrow (show FunctionTypeRel
        (.expression (.symbol "->" :: (domains ++ [returned]))) domains returned from rfl)).1
      rw [sameDomains] at applicable
      have positive := ((arguments_applicable_iff space arguments domains fuel checked incoming _).mp applicable).1
      omega

/-- A rejected callback's complete error list has independent applicability
evidence at every occurrence. The no-success premise belongs to the whole
candidate, so successful paths cannot expose these otherwise masked errors. -/
theorem checked_argument_errors_sound (space : Space) (operator expected returned : Atom)
    (arguments domains : List Atom) (incoming : Bindings) (fuel : Nat)
    (checked : List.Forall₂ (fun argument domain =>
      ArgumentDomainEvidence space argument domain fuel) arguments domains)
    (noSuccess : ∀ output, ¬ApplicationSuccessRel space (.expression (operator :: arguments))
      (.expression (.symbol "->" :: (domains ++ [returned]))) expected incoming output)
    (error : Atom)
    (member : error ∈ argumentErrorBlocks space (.expression (operator :: arguments)) arguments domains 1 1) :
    ApplicabilityRel space (.expression (operator :: arguments))
      (.expression (.symbol "->" :: (domains ++ [returned]))) expected incoming (.error error) := by
  obtain ⟨_, before, typesBefore, badArgument, badDomain, actual, after, typesAfter,
      argumentsSame, domainsSame, arity, priorPath, inferred, rejected, errorSame⟩ :=
    argument_error_witness space arguments domains fuel checked (.expression (operator :: arguments))
      incoming 1 1 error member
  rw [errorSame]
  have position : 1 + before.length = before.length + 1 := Nat.add_comm _ _
  rw [position]
  exact .badArgument (by rw [argumentsSame]) (by rw [domainsSame]; rfl) arity priorPath inferred rejected noSuccess

theorem wildcard_argument_check (space : Space) (argument domain : Atom) (bindings : Bindings)
    (fuel : Nat) (wildcard : WildcardDomain domain) :
    checkArgumentType space argument domain bindings fuel =
      List.replicate (getAtomTypes space argument).length (.inr bindings) := by
  unfold checkArgumentType
  simp only [rawTypeLookup, (wildcard_type_match domain _ bindings fuel wildcard).1,
    List.isEmpty_cons, Bool.false_eq_true, ite_false, List.map_cons, List.map_nil]
  induction getAtomTypes space argument <;> simp_all [List.replicate_succ]

theorem wildcard_argument_loop (space : Space) (arguments domains : List Atom)
    (expression : Atom) (bindings : Bindings) (fuel index count : Nat) (errors : List Atom)
    (wildcards : List.Forall₂ (fun _ domain => WildcardDomain domain) arguments domains) :
    checkIfFunctionTypeIsApplicable.checkArgLoop arguments domains expression
      (List.replicate count bindings) errors space fuel index =
        (errors, List.replicate (count * pathCount space arguments) bindings) := by
  have computed := argument_loop_exact space arguments domains expression bindings fuel index count errors
    (wildcard_arguments_evidence space arguments domains fuel wildcards)
  rw [argumentErrorBlocks_wildcards space expression arguments domains index count wildcards,
    admittedPathCount_wildcards space arguments domains wildcards] at computed
  simpa only [List.append_nil] using computed

theorem independent_wildcard_arguments (space : Space) (arguments domains : List Atom)
    (bindings : Bindings)
    (wildcards : List.Forall₂ (fun _ domain => WildcardDomain domain) arguments domains) :
    ArgumentsApplicableRel space arguments domains bindings bindings := by
  have sameCount := admittedPathCount_wildcards space arguments domains wildcards
  exact (arguments_applicable_iff space arguments domains 0
    (wildcard_arguments_evidence space arguments domains 0 wildcards) bindings bindings).mpr
      ⟨sameCount ▸ pathCount_positive space arguments, rfl⟩

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

/-- The actual callback keeps its complete argument-error chronology, but
returns the successful paths whenever any survive the final return check. -/
theorem checked_applicability_exact (space : Space) (operator expected returned : Atom)
    (arguments domains : List Atom) (bindings : Bindings) (fuel : Nat)
    (checked : List.Forall₂ (fun argument domain =>
      ArgumentDomainEvidence space argument domain fuel) arguments domains)
    (expectedClosed : TypeSubst.typeVars expected = [])
    (returnedClosed : TypeSubst.typeVars returned = [])
    (enough : sizeOf expected + sizeOf returned + 2 ≤ fuel) :
    checkIfFunctionTypeIsApplicable (.expression (operator :: arguments))
      (.expression (.symbol "->" :: (domains ++ [returned]))) expected space bindings (fuel + 1) =
      if admittedPathCount space arguments domains = 0 then
        .inl (argumentErrorBlocks space (.expression (operator :: arguments)) arguments domains 1 1)
      else if ClosedTypeFits expected returned then
        .inr (List.replicate (admittedPathCount space arguments domains) bindings)
      else .inl (argumentErrorBlocks space (.expression (operator :: arguments)) arguments domains 1 1 ++
        List.replicate (admittedPathCount space arguments domains)
          (mkError (.expression (operator :: arguments)) (.badType expected returned))) := by
  have sameLength := List.Forall₂.length_eq checked
  have argumentsChecked := argument_loop_exact space arguments domains
    (.expression (operator :: arguments)) bindings fuel 1 1 [] checked
  simp only [List.replicate_one, List.nil_append, Nat.one_mul] at argumentsChecked
  simp only [checkIfFunctionTypeIsApplicable, arrow_arguments, arrow_return]
  rw [show (arguments.length != domains.length) = false from by simp [sameLength]]
  simp only [Bool.false_eq_true, if_false]
  rw [argumentsChecked]
  by_cases empty : admittedPathCount space arguments domains = 0
  · simp [empty]
  · have nonempty : (List.replicate (admittedPathCount space arguments domains) bindings).isEmpty = false := by
      simp [empty]
    simp only [nonempty, Bool.false_eq_true, if_false, empty]
    simp only [closed_matchTypes_exact expected returned _ fuel expectedClosed returnedClosed enough]
    by_cases fits : ClosedTypeFits expected returned
    · simp only [fits, if_true, List.isEmpty_cons, Bool.false_eq_true, if_false]
      rw [pair_append_fold]
      simp [nonempty]
    · simp only [fits, if_false, List.isEmpty_nil, if_true]
      rw [failed_return_fold]
      simp

theorem checked_applicability_success (space : Space) (operator expected returned : Atom)
    (arguments domains : List Atom) (bindings : Bindings) (fuel : Nat)
    (checked : List.Forall₂ (fun argument domain =>
      ArgumentDomainEvidence space argument domain fuel) arguments domains)
    (positive : 0 < admittedPathCount space arguments domains)
    (expectedClosed : TypeSubst.typeVars expected = [])
    (returnedClosed : TypeSubst.typeVars returned = [])
    (fits : ClosedTypeFits expected returned)
    (enough : sizeOf expected + sizeOf returned + 2 ≤ fuel) :
    checkIfFunctionTypeIsApplicable (.expression (operator :: arguments))
      (.expression (.symbol "->" :: (domains ++ [returned]))) expected space bindings (fuel + 1) =
        .inr (List.replicate (admittedPathCount space arguments domains) bindings) := by
  rw [checked_applicability_exact space operator expected returned arguments domains bindings fuel
    checked expectedClosed returnedClosed enough, if_neg (by omega), if_pos fits]

/-- The independent application rule and the retained callback share a
constructed successful argument path, without assuming worker realization. -/
theorem independent_checked_application (space : Space) (operator expected returned : Atom)
    (arguments domains : List Atom) (bindings : Bindings) (fuel : Nat)
    (checked : List.Forall₂ (fun argument domain =>
      ArgumentDomainEvidence space argument domain fuel) arguments domains)
    (positive : 0 < admittedPathCount space arguments domains)
    (expectedClosed : TypeSubst.typeVars expected = [])
    (returnedClosed : TypeSubst.typeVars returned = [])
    (fits : ClosedTypeFits expected returned) :
    ApplicationSuccessRel space (.expression (operator :: arguments))
      (.expression (.symbol "->" :: (domains ++ [returned]))) expected bindings bindings :=
  .mk rfl rfl ((arguments_applicable_iff space arguments domains fuel checked bindings bindings).mpr
    ⟨positive, rfl⟩)
    ((closed_type_match_iff expected returned bindings bindings expectedClosed returnedClosed).mpr ⟨fits, rfl⟩)

theorem checked_applicability_argument_failure (space : Space) (operator expected returned : Atom)
    (arguments domains : List Atom) (bindings : Bindings) (fuel : Nat)
    (checked : List.Forall₂ (fun argument domain =>
      ArgumentDomainEvidence space argument domain fuel) arguments domains)
    (exhausted : admittedPathCount space arguments domains = 0) :
    checkIfFunctionTypeIsApplicable (.expression (operator :: arguments))
      (.expression (.symbol "->" :: (domains ++ [returned]))) expected space bindings (fuel + 1) =
        .inl (argumentErrorBlocks space (.expression (operator :: arguments)) arguments domains 1 1) := by
  have sameLength := List.Forall₂.length_eq checked
  have argumentsChecked := argument_loop_exact space arguments domains
    (.expression (operator :: arguments)) bindings fuel 1 1 [] checked
  simp only [List.replicate_one, List.nil_append, Nat.one_mul, exhausted,
    List.replicate_zero] at argumentsChecked
  simp only [checkIfFunctionTypeIsApplicable, arrow_arguments, arrow_return]
  rw [show (arguments.length != domains.length) = false from by simp [sameLength]]
  simp only [Bool.false_eq_true, if_false]
  rw [argumentsChecked]
  rfl

theorem checked_applicability_return_failure (space : Space) (operator expected returned : Atom)
    (arguments domains : List Atom) (bindings : Bindings) (fuel : Nat)
    (checked : List.Forall₂ (fun argument domain =>
      ArgumentDomainEvidence space argument domain fuel) arguments domains)
    (positive : 0 < admittedPathCount space arguments domains)
    (expectedClosed : TypeSubst.typeVars expected = [])
    (returnedClosed : TypeSubst.typeVars returned = [])
    (incompatible : ¬ClosedTypeFits expected returned) :
    checkIfFunctionTypeIsApplicable (.expression (operator :: arguments))
      (.expression (.symbol "->" :: (domains ++ [returned]))) expected space bindings (fuel + 1) =
        .inl (argumentErrorBlocks space (.expression (operator :: arguments)) arguments domains 1 1 ++
          List.replicate (admittedPathCount space arguments domains)
            (mkError (.expression (operator :: arguments)) (.badType expected returned))) := by
  have sameLength := List.Forall₂.length_eq checked
  have argumentsChecked := argument_loop_exact space arguments domains
    (.expression (operator :: arguments)) bindings fuel 1 1 [] checked
  simp only [List.replicate_one, List.nil_append, Nat.one_mul] at argumentsChecked
  have nonempty : (List.replicate (admittedPathCount space arguments domains) bindings).isEmpty = false := by
    simp [Nat.ne_of_gt positive]
  simp only [checkIfFunctionTypeIsApplicable, arrow_arguments, arrow_return]
  rw [show (arguments.length != domains.length) = false from by simp [sameLength]]
  simp only [Bool.false_eq_true, if_false]
  rw [argumentsChecked]
  simp only [nonempty, Bool.false_eq_true, if_false,
    closed_matchTypes_failure expected returned _ fuel expectedClosed returnedClosed incompatible,
    List.isEmpty_nil, if_true]
  rw [failed_return_fold]
  simp

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
  have sameCount := admittedPathCount_wildcards space arguments domains wildcards
  have checked := checked_applicability_return_failure space operator expected returned arguments domains
    bindings fuel (wildcard_arguments_evidence space arguments domains fuel wildcards)
    (sameCount ▸ pathCount_positive space arguments) expectedClosed returnedClosed incompatible
  simpa only [sameCount, argumentErrorBlocks_wildcards space (.expression (operator :: arguments))
    arguments domains 1 1 wildcards, List.nil_append] using checked

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
  have sameCount := admittedPathCount_wildcards space arguments domains wildcards
  have checked := checked_applicability_success space operator expected returned arguments domains
    bindings fuel (wildcard_arguments_evidence space arguments domains fuel wildcards)
    (sameCount ▸ pathCount_positive space arguments) expectedClosed returnedClosed fits enough
  simpa only [sameCount] using checked

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

theorem independent_checked_bad_return (space : Space) (operator expected returned : Atom)
    (arguments domains : List Atom) (bindings : Bindings) (fuel : Nat)
    (checked : List.Forall₂ (fun argument domain =>
      ArgumentDomainEvidence space argument domain fuel) arguments domains)
    (positive : 0 < admittedPathCount space arguments domains)
    (expectedClosed : TypeSubst.typeVars expected = [])
    (returnedClosed : TypeSubst.typeVars returned = [])
    (incompatible : ¬ClosedTypeFits expected returned) :
    ApplicabilityRel space (.expression (operator :: arguments))
      (.expression (.symbol "->" :: (domains ++ [returned]))) expected bindings
      (.error (mkError (.expression (operator :: arguments)) (.badType expected returned))) :=
  .badReturn rfl rfl ((arguments_applicable_iff space arguments domains fuel checked bindings bindings).mpr
    ⟨positive, rfl⟩)
    (fun output matchReturn => incompatible
      ((closed_type_match_iff expected returned bindings output expectedClosed returnedClosed).mp matchReturn).1)
    (fun output => closed_return_excludes_success space operator expected returned arguments domains
      bindings output expectedClosed returnedClosed incompatible)

theorem independent_bad_return (space : Space) (operator expected returned : Atom)
    (arguments domains : List Atom) (bindings : Bindings)
    (wildcards : List.Forall₂ (fun _ domain => WildcardDomain domain) arguments domains)
    (expectedClosed : TypeSubst.typeVars expected = [])
    (returnedClosed : TypeSubst.typeVars returned = [])
    (incompatible : ¬ClosedTypeFits expected returned) :
    ApplicabilityRel space (.expression (operator :: arguments))
      (.expression (.symbol "->" :: (domains ++ [returned]))) expected bindings
      (.error (mkError (.expression (operator :: arguments)) (.badType expected returned))) := by
  have sameCount := admittedPathCount_wildcards space arguments domains wildcards
  exact independent_checked_bad_return space operator expected returned arguments domains bindings 0
    (wildcard_arguments_evidence space arguments domains 0 wildcards)
    (sameCount ▸ pathCount_positive space arguments) expectedClosed returnedClosed incompatible

theorem independent_wildcard_application (space : Space) (operator expected returned : Atom)
    (arguments domains : List Atom) (bindings : Bindings)
    (wildcards : List.Forall₂ (fun _ domain => WildcardDomain domain) arguments domains)
    (expectedClosed : TypeSubst.typeVars expected = [])
    (returnedClosed : TypeSubst.typeVars returned = [])
    (fits : ClosedTypeFits expected returned) :
    ApplicationSuccessRel space (.expression (operator :: arguments))
      (.expression (.symbol "->" :: (domains ++ [returned]))) expected bindings bindings := by
  have sameCount := admittedPathCount_wildcards space arguments domains wildcards
  exact independent_checked_application space operator expected returned arguments domains bindings 0
    (wildcard_arguments_evidence space arguments domains 0 wildcards)
    (sameCount ▸ pathCount_positive space arguments) expectedClosed returnedClosed fits

end Mettapedia.Languages.MeTTa.HE.FirstSuccessSourceApplicability



set_option autoImplicit false
namespace Mettapedia.Languages.MeTTa.HE.FirstSuccessSourceApplicability
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Machines.ReadOnlyQuery
open Spec.Type.Presentation (TypeSubst)

private theorem query_covered_bind {A B : Type} (fuel : Nat)
    (first : MatchDepth.Query A) (next : A → MatchDepth.Query B)
    (covered : MatchDepth.queryCovered fuel first = true)
    (continued : ∀ value, MatchDepth.queryCovered fuel (next value) = true) :
    MatchDepth.queryCovered fuel (bind first next) = true := by
  simp only [MatchDepth.queryCovered, run_bind, List.all_append, Bool.and_eq_true]
  exact ⟨covered, continued _⟩

private theorem query_covered_map {A B : Type} (fuel : Nat)
    (f : A → B) (query : MatchDepth.Query A)
    (covered : MatchDepth.queryCovered fuel query = true) :
    MatchDepth.queryCovered fuel (map f query) = true := by
  simpa only [MatchDepth.queryCovered, run_map] using covered

private theorem query_covered_flatTraverse {A B : Type} (fuel : Nat)
    (values : List A) (next : A → MatchDepth.Query (List B))
    (covered : ∀ value ∈ values, MatchDepth.queryCovered fuel (next value) = true) :
    MatchDepth.queryCovered fuel (flatTraverse values next) = true := by
  induction values with
  | nil => rfl
  | cons value values ih =>
      apply query_covered_bind
      · exact covered value (by simp)
      · intro head
        exact query_covered_map fuel _ _ (ih (fun item member => covered item (by simp [member])))

private theorem query_covered_fold {A B : Type} (fuel : Nat)
    (values : List A) (initial : B) (next : B → A → MatchDepth.Query B)
    (covered : ∀ state, ∀ value ∈ values, MatchDepth.queryCovered fuel (next state value) = true) :
    MatchDepth.queryCovered fuel (foldQueries values initial next) = true := by
  induction values generalizing initial with
  | nil => rfl
  | cons value values ih =>
      apply query_covered_bind
      · exact covered initial value (by simp)
      · intro state
        exact ih state (fun state item member => covered state item (by simp [member]))

/-- The admitted domain evidence also earns the actual bounded matcher reads.
Wildcard domains require no structural matching; closed domains use the
existing syntax-size coverage theorem. -/
theorem ArgumentDomainEvidence.match_covered
    {space : Space} {argument domain : Atom} {fuel : Nat}
    (checked : ArgumentDomainEvidence space argument domain fuel)
    (actual : Atom) (member : actual ∈ getAtomTypes space argument) (bindings : Bindings) :
    matchTypesCovered domain actual bindings fuel = true := by
  cases checked with
  | wildcard wildcard =>
      rcases wildcard with rfl | rfl <;>
        simp [matchTypesCovered, MatchDepth.queryCovered, MatchDepth.typesQuery, run]
  | closed domainClosed actualClosed enough =>
      exact closed_matchTypes_covered domain actual bindings fuel
        domainClosed (actualClosed actual member) (enough actual member)

theorem ArgumentDomainEvidence.argument_covered
    {space : Space} {argument domain : Atom} {fuel : Nat}
    (checked : ArgumentDomainEvidence space argument domain fuel) (bindings : Bindings) :
    MatchDepth.queryCovered fuel (TypeCheckDepth.argumentQuery space argument domain bindings) = true := by
  unfold TypeCheckDepth.argumentQuery
  apply query_covered_flatTraverse
  intro actual member
  exact query_covered_map fuel _ _ (checked.match_covered actual member bindings)

/-- Coverage follows every reached binding alternative in the actual argument
fold; no cardinality or unchanged-binding hypothesis is used by this law. -/
theorem checked_arguments_covered (space : Space) (arguments domains : List Atom)
    (expression : Atom) (fuel : Nat)
    (checked : List.Forall₂ (fun argument domain =>
      ArgumentDomainEvidence space argument domain fuel) arguments domains)
    (results : List Bindings) (errors : List Atom) (index : Nat) :
    MatchDepth.queryCovered fuel
      (TypeCheckDepth.argumentsQuery arguments domains expression results errors space index) = true := by
  induction checked generalizing results errors index with
  | nil => rfl
  | @cons argument domain arguments domains head rest ih =>
      apply query_covered_bind
      · apply query_covered_fold
        intro state bindings member
        exact query_covered_map fuel _ _ (head.argument_covered bindings)
      · intro reached
        exact ih reached.2 reached.1 (index + 1)

/-- Existing applicability evidence earns all visited native matcher calls,
including the final return-type check at every reached argument binding. -/
theorem checked_applicability_covered (space : Space) (operator expected returned : Atom)
    (arguments domains : List Atom) (bindings : Bindings) (fuel : Nat)
    (checked : List.Forall₂ (fun argument domain =>
      ArgumentDomainEvidence space argument domain fuel) arguments domains)
    (expectedClosed : TypeSubst.typeVars expected = [])
    (returnedClosed : TypeSubst.typeVars returned = [])
    (enough : sizeOf expected + sizeOf returned + 2 ≤ fuel) :
    functionTypeCovered (.expression (operator :: arguments))
      (.expression (.symbol "->" :: (domains ++ [returned]))) expected space bindings (fuel + 1) = true := by
  simp only [functionTypeCovered, TypeCheckDepth.functionQuery, arrow_arguments, arrow_return]
  rw [show (arguments.length != domains.length) = false from by simp [List.Forall₂.length_eq checked]]
  simp only [Bool.false_eq_true, if_false]
  apply query_covered_bind
  · exact checked_arguments_covered space arguments domains _ fuel checked [bindings] [] 1
  · intro reached
    split
    · rfl
    · apply query_covered_map
      apply query_covered_fold
      intro state bindings member
      exact query_covered_map fuel _ _
        (closed_matchTypes_covered expected returned bindings fuel
          expectedClosed returnedClosed enough)

end Mettapedia.Languages.MeTTa.HE.FirstSuccessSourceApplicability

/-! ## Fresh polymorphic invocation instances

A schematic annotation such as `(-> $t $t)` is a scheme. Each invocation
needs its own instance whose variables avoid the complete call-site scope;
otherwise the binding from one call constrains an independent second call.
The laws below give one fresh instance its applicability, selection and
retained entry, and construct the specification's alpha-variant witnesses
from the existing fresh-name generator. -/

namespace Mettapedia.Languages.MeTTa.HE.FirstSuccessSourceApplicability

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Spec.Type Spec.Match.Merge
open Mettapedia.Machines.ReadOnlyQuery

attribute [local simp] Atom.variableType Atom.symbolType

theorem fresh_symbol_match (name actual : String) (depth : Nat) :
    matchAtoms (.var name) (.symbol actual) (depth + 1) =
      [Bindings.empty.assign name (.symbol actual)] := by
  have noLoop : (Bindings.empty.assign name (.symbol actual)).hasLoop = false :=
    hasLoop_single_assignment_eq_false_iff.mpr (by intro occurs; cases occurs)
  simp [matchAtoms, getMetaType, noLoop]

/-- A fresh unvalued class accepts one concrete type, without constraining
unrelated caller assignments or requiring an equality-free caller. -/
theorem fresh_symbol_type_match (name actual : String) (bindings : Bindings)
    (depth : Nat) (notUndefined : actual ≠ "%Undefined%") (notAtom : actual ≠ "Atom")
    (fresh : bindings.classValues name = []) :
    matchTypes (.var name) (.symbol actual) bindings (depth + 2) =
      [bindings.assign name (.symbol actual)] := by
  have notWildcard :
      ((Atom.var name == Atom.undefinedType || Atom.var name == Atom.atomType ||
        Atom.symbol actual == Atom.undefinedType || Atom.symbol actual == Atom.atomType)) = false := by
    simp [Atom.undefinedType, Atom.atomType, notUndefined, notAtom]
  rw [matchTypes, notWildcard]
  simp only [Bool.false_eq_true, if_false]
  rw [fresh_symbol_match]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
  rw [mergeBindings_single_assign]
  simp [addVarBinding, fresh]

/-- Independent source evidence for the same newly constrained type class. -/
theorem independent_fresh_symbol_type_match (name actual : String) (bindings : Bindings)
    (notUndefined : actual ≠ "%Undefined%") (notAtom : actual ≠ "Atom")
    (fresh : bindings.classValues name = []) :
    TypeMatchRel (.var name) (.symbol actual) bindings
      (bindings.assign name (.symbol actual)) := by
  apply TypeMatchRel.structural (matched := Bindings.empty.assign name (.symbol actual))
  · intro equal; cases equal
  · intro equal; cases equal
  · simpa [Atom.undefinedType] using notUndefined
  · simpa [Atom.atomType] using notAtom
  · exact .varNonVar rfl (semanticLoopFree_single_assignment (by intro occurs; cases occurs))
  · apply MergeRel.mk (order := [.value name (.symbol actual)])
    · change [Constraint.value name (.symbol actual)].Perm [Constraint.value name (.symbol actual)]
      exact List.Perm.refl _
    · exact .value (.fresh fresh) .nil

theorem fresh_symbol_type_match_covered (name actual : String) (bindings : Bindings)
    (depth : Nat) (fresh : bindings.classValues name = []) :
    matchTypesCovered (.var name) (.symbol actual) bindings (depth + 2) = true := by
  have atomCovered : matchCovered (depth + 2) (.atoms (.var name) (.symbol actual)) = true := by
    simp [matchCovered, depthCovered, MatchDepth.body, MatchDepth.rawAtoms, getMetaType,
      run_map, run]
  have mergeCovered : matchCovered (depth + 2)
      (.merge bindings (Bindings.empty.assign name (.symbol actual))) = true := by
    simp [matchCovered, depthCovered, MatchDepth.body, Bindings.empty, Bindings.assign,
      Bindings.isBound, Bindings.lookup, foldQueries, flatTraverse, run_bind, run_map,
      run, fresh]
  unfold matchTypesCovered MatchDepth.queryCovered MatchDepth.typesQuery
  split
  · rfl
  · simp [run, evalMatch, fresh_symbol_match, run_flatTraverse_reads, atomCovered, mergeCovered]

end Mettapedia.Languages.MeTTa.HE.FirstSuccessSourceApplicability

namespace Mettapedia.Languages.MeTTa.HE.FirstSuccessSourceApplicability

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Spec.Type
open Mettapedia.Machines.ReadOnlyQuery

/-- An actual singleton argument-type query gives a fresh polymorphic arrow
one changed binding. The complete arrow shares the same variable. -/
theorem fresh_polymorphic_applicability (space : Space) (operator argument : Atom)
    (name actual : String) (bindings : Bindings) (depth : Nat)
    (lookup : TypeLookup := rawTypeLookup space)
    (types : lookup bindings argument (.var name) = [.symbol actual])
    (notUndefined : actual ≠ "%Undefined%") (notAtom : actual ≠ "Atom")
    (fresh : bindings.classValues name = []) :
    checkIfFunctionTypeIsApplicable (.expression [operator, argument])
      (.expression [.symbol "->", .var name, .var name]) Atom.undefinedType
      space bindings (depth + 3) lookup = .inr [bindings.assign name (.symbol actual)] := by
  have matched := fresh_symbol_type_match name actual bindings depth notUndefined notAtom fresh
  have returned : ∀ next, matchTypes Atom.undefinedType (.var name) next (depth + 2) = [next] := by
    intro next
    simp [matchTypes]
  simp [checkIfFunctionTypeIsApplicable, getFunctionArgTypes, getFunctionRetType,
    checkIfFunctionTypeIsApplicable.checkArgLoop, checkArgumentType, types, matched,
    returned]

/-- The source judgment is constructed from the actual type occurrence and
the independent matcher/merge rules, not from an assumed evaluator result. -/
theorem independent_fresh_polymorphic_applicability (space : Space)
    (operator argument : Atom) (name actual : String) (bindings : Bindings)
    (lookup : TypeLookupRel := rawTypeLookupRel space)
    (actualType : TypeAtRel lookup bindings argument (.var name) (.symbol actual))
    (notUndefined : actual ≠ "%Undefined%") (notAtom : actual ≠ "Atom")
    (fresh : bindings.classValues name = []) :
    ApplicationSuccessRel space (lookup := lookup) (.expression [operator, argument])
      (.expression [.symbol "->", .var name, .var name]) Atom.undefinedType
      bindings (bindings.assign name (.symbol actual)) := by
  exact .mk (argumentTypes := [.var name]) (returnType := .var name) rfl rfl (.cons actualType
    (independent_fresh_symbol_type_match name actual bindings notUndefined notAtom fresh)
    (.nil _)) (.undefinedLeft _ _)

theorem fresh_polymorphic_applicability_covered (space : Space) (operator argument : Atom)
    (name actual : String) (bindings : Bindings) (depth : Nat)
    (lookup : TypeLookup := rawTypeLookup space)
    (types : lookup bindings argument (.var name) = [.symbol actual])
    (fresh : bindings.classValues name = []) :
    functionTypeCovered (.expression [operator, argument])
      (.expression [.symbol "->", .var name, .var name]) Atom.undefinedType
      space bindings (depth + 3) lookup = true := by
  simp only [functionTypeCovered, TypeCheckDepth.functionQuery, getFunctionArgTypes,
    getFunctionRetType, List.length_cons, List.length_nil]
  apply query_covered_bind
  · unfold TypeCheckDepth.argumentsQuery
    apply query_covered_bind
    · apply query_covered_fold
      intro state selected member
      have equal : selected = bindings := by simpa using member
      subst selected
      apply query_covered_map
      unfold TypeCheckDepth.argumentQuery
      apply query_covered_flatTraverse
      intro found member
      change found ∈ lookup bindings argument (.var name) at member
      rw [types] at member
      have equal : found = .symbol actual := by simpa using member
      subst found
      apply query_covered_map
      exact fresh_symbol_type_match_covered name actual bindings depth fresh
    · intro next
      rfl
  · intro next
    split
    · rfl
    · apply query_covered_map
      apply query_covered_fold
      intro state selected member
      apply query_covered_map
      simp [MatchDepth.queryCovered, MatchDepth.typesQuery, run]

end Mettapedia.Languages.MeTTa.HE.FirstSuccessSourceApplicability

namespace Mettapedia.Languages.MeTTa.HE.FirstSuccessSourceApplicability

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Spec.Eval Spec.Type FirstSuccessRecursiveStrategy

def freshPolymorphicPolicy (name : String) : SelectedTypePolicy :=
  ⟨.expression [.symbol "->", .var name, .var name], [.var name], .var name, rfl⟩

/-- Assigning one fresh instance and linking a second fresh instance retains
the assigned value as their sole class value. Unrelated incoming constraints
are retained, including repeated edges and open values. -/
theorem fresh_instance_alias_values (bindings : Bindings) (left right : String)
    (value : Atom) (leftFresh : left ∉ bindings.names)
    (rightFresh : right ∉ bindings.names) (different : left ≠ right) :
    ((bindings.assign left value).addEquality left right).classValues left = [value] := by
  have unbound (name : String) (fresh : name ∉ bindings.names) :
      bindings.lookup name = none := by
    apply List.lookup_eq_none_iff.mpr
    intro entry stored
    apply bne_iff_ne.mpr
    intro same
    apply fresh
    apply List.mem_append_left
    exact List.mem_flatMap.mpr ⟨entry, stored, by simp [same]⟩
  have noEdge (name : String) (fresh : name ∉ bindings.names) :
      name ∉ bindings.eqVarsInOrder := by
    intro stored
    apply fresh
    apply List.mem_append_right
    exact EqualityClosure.mem_eqVarsInOrder_iff.mp stored
  apply EqualityClosure.classValues_addEquality_of_fresh
  · exact noEdge left leftFresh
  · exact noEdge right rightFresh
  · exact different
  · exact lookup_assign_of_lookup_none bindings left value (unbound left leftFresh)
  · rw [assign_lookup_ne bindings left value right different.symm (unbound left leftFresh)]
    exact unbound right rightFresh

/-- A singleton actual-type query earns the first flattened success and cuts
off every later arrow. No scan coverage callback is assumed. -/
theorem fresh_polymorphic_selection (space : Space) (operator argument : Atom)
    (name actual : String) (bindings : Bindings) (depth : Nat) (later : List Atom)
    (lookup : TypeLookup := rawTypeLookup space)
    (types : lookup bindings argument (.var name) = [.symbol actual])
    (notUndefined : actual ≠ "%Undefined%") (notAtom : actual ≠ "Atom")
    (fresh : bindings.classValues name = []) :
    select space (.expression [operator, argument]) Atom.undefinedType bindings (depth + 3)
      (.expression [.symbol "->", .var name, .var name] :: later) lookup =
      .selected (freshPolymorphicPolicy name) [bindings.assign name (.symbol actual)] := by
  have applies := fresh_polymorphic_applicability space operator argument name actual
    bindings depth lookup types notUndefined notAtom fresh
  simp only [select, readPolicy, applies, List.take_succ_cons, List.take_zero]
  rfl

theorem fresh_polymorphic_selection_source (space : Space) (operator argument : Atom)
    (name actual : String) (bindings : Bindings) (later : List Atom)
    (lookup : Space → TypeLookupRel := rawTypeLookupRel)
    (actualType : TypeAtRel (lookup space) bindings argument (.var name) (.symbol actual))
    (notUndefined : actual ≠ "%Undefined%") (notAtom : actual ≠ "Atom")
    (fresh : bindings.classValues name = []) :
    FunctionCandidateScanRel
      (fun context subject candidate expected incoming outcome =>
        PublishedCandidateApplicabilityRel context (lookup := lookup context)
          subject candidate expected incoming outcome) space
      (.expression [operator, argument]) Atom.undefinedType bindings
      (.expression [.symbol "->", .var name, .var name] :: later)
      (.success (freshPolymorphicPolicy name) (bindings.assign name (.symbol actual))) := by
  apply FunctionCandidateScanRel.functionSuccess
    (argumentTypes := [.var name]) (returnType := .var name) rfl
  exact .success rfl (.success
    (independent_fresh_polymorphic_applicability space operator argument name actual bindings
      (lookup space) actualType notUndefined notAtom fresh))

theorem fresh_polymorphic_selection_ready (space : Space) (operator argument : Atom)
    (name actual : String) (bindings : Bindings) (depth : Nat) (later : List Atom)
    (lookup : TypeLookup := rawTypeLookup space)
    (types : lookup bindings argument (.var name) = [.symbol actual])
    (notUndefined : actual ≠ "%Undefined%") (notAtom : actual ≠ "Atom")
    (fresh : bindings.classValues name = []) :
    selectionReady space (.expression [operator, argument]) Atom.undefinedType bindings (depth + 3)
      (.expression [.symbol "->", .var name, .var name] :: later) lookup = true := by
  have applies := fresh_polymorphic_applicability space operator argument name actual
    bindings depth lookup types notUndefined notAtom fresh
  have covered := fresh_polymorphic_applicability_covered space operator argument name actual
    bindings depth lookup types fresh
  simp [selectionReady, readPolicy, applies, covered]

/-- The existing retained task saves the instantiated whole signature, changed
bindings, selected demand and live syntax. -/
theorem fresh_polymorphic_retained_entry (space : Space) (dispatch : GroundedDispatch)
    (operator argument : Atom) (name actual : String) (bindings : Bindings) (depth : Nat)
    (later live : List Atom) (lookup : TypeLookup := rawTypeLookup space)
    (types : lookup bindings argument (.var name) = [.symbol actual])
    (notUndefined : actual ≠ "%Undefined%") (notAtom : actual ≠ "Atom")
    (fresh : bindings.classValues name = []) :
    enter space dispatch (.functions (.expression [operator, argument]) Atom.undefinedType
      bindings (depth + 3) (.expression [.symbol "->", .var name, .var name] :: later) live) lookup =
      (.work (.bindingAlternatives (.expression [operator, argument])
        (.expression [.symbol "->", .var name, .var name]) (.var name)
        (depth + 3) [bindings.assign name (.symbol actual)] live), []) := by
  rw [selected_enter _ _ _ _ _ _ _ _ _ _
    (fresh_polymorphic_selection space operator argument name actual bindings depth later
      lookup types notUndefined notAtom fresh)]
  simp [freshPolymorphicPolicy, Atom.expressionType]

/-- The configuration-scoped worker and the independent scoped service select
the same fresh arrow and reached binding. The argument query is proved from
its literal singleton declaration; the operator's selected instance is retained
explicitly rather than regenerated under a different saved scope. -/
theorem fresh_polymorphic_scoped_selection (state : RecursiveTasks.Configuration)
    (operator argument : Atom) (name actual : String) (bindings : Bindings)
    (depth : Nat) (later : List Atom) (protectedScope : List String)
    (types : getAtomTypes state.space argument = [.symbol actual])
    (notUndefined : actual ≠ "%Undefined%") (notAtom : actual ≠ "Atom")
    (fresh : bindings.classValues name = []) :
    select state.space (.expression [operator, argument]) Atom.undefinedType bindings (depth + 3)
        (.expression [.symbol "->", .var name, .var name] :: later)
        (FirstSuccessRecursiveExecution.invocationTypes state) =
      .selected (freshPolymorphicPolicy name) [bindings.assign name (.symbol actual)] ∧
    selectionReady state.space (.expression [operator, argument]) Atom.undefinedType bindings (depth + 3)
        (.expression [.symbol "->", .var name, .var name] :: later)
        (FirstSuccessRecursiveExecution.invocationTypes state) = true ∧
    scopedStorageTypeService.candidateScan protectedScope state.space
      (.expression [operator, argument]) Atom.undefinedType bindings
      (.expression [.symbol "->", .var name, .var name] :: later)
      (.success (freshPolymorphicPolicy name) (bindings.assign name (.symbol actual))) := by
  have queried : FirstSuccessRecursiveExecution.invocationTypes state bindings argument (.var name) =
      [.symbol actual] := by
    unfold FirstSuccessRecursiveExecution.invocationTypes getAtomTypesScoped
    rw [types]
    simp [instantiateTypeSignatures, instantiateTypeSignature, renameAtom]
  have source : TypeAtRel (scopedTypeLookup protectedScope state.space)
      bindings argument (.var name) (.symbol actual) := by
    refine ⟨[.symbol actual], ⟨[.symbol actual], ?_, .cons ?_ (.nil _)⟩, by simp⟩
    · rw [← types]
      exact FirstSuccessSourceReplies.source_types _ _
    · exact ⟨id, Function.injective_id, by simp,
        by simp [Spec.Type.Presentation.TypeSubst.typeVars]⟩
  exact ⟨fresh_polymorphic_selection _ _ _ _ _ _ _ _ _ queried notUndefined notAtom fresh,
    fresh_polymorphic_selection_ready _ _ _ _ _ _ _ _ _ queried notUndefined notAtom fresh,
    fresh_polymorphic_selection_source _ _ _ _ _ _ _ (scopedTypeLookup protectedScope)
      source notUndefined notAtom fresh⟩

/-- One actual checked transition consumes the selected signature, preserving
the saved continuation and emitted prefix. Its matcher coverage is constructed
by the same query that justifies the independent source selection. -/
theorem fresh_polymorphic_scoped_step (state : RecursiveTasks.Configuration)
    (dispatch : GroundedDispatch) (operator argument : Atom) (name actual : String)
    (bindings : Bindings) (depth : Nat) (later live : List Atom)
    (pending : state.control = .work (.functions (.expression [operator, argument])
      Atom.undefinedType bindings (depth + 3)
      (.expression [.symbol "->", .var name, .var name] :: later) live))
    (types : getAtomTypes state.space argument = [.symbol actual])
    (notUndefined : actual ≠ "%Undefined%") (notAtom : actual ≠ "Atom")
    (fresh : bindings.classValues name = []) :
    (FirstSuccessRecursiveExecution.Checked.machine dispatch
      FirstSuccessRecursiveExecution.scopedTypes).step state =
      some (.silent {state with control := .work (.bindingAlternatives
        (.expression [operator, argument]) (.expression [.symbol "->", .var name, .var name])
        (.var name) (depth + 3) [bindings.assign name (.symbol actual)] live)}) := by
  obtain ⟨selected, ready, _⟩ := fresh_polymorphic_scoped_selection
    state operator argument name actual bindings depth later [] types notUndefined notAtom fresh
  have entered := selected_enter state.space dispatch _ _ _ _ _ live _ _ selected
  have unblocked : FirstSuccessRecursiveExecution.Checked.blocked dispatch state
      FirstSuccessRecursiveExecution.scopedTypes = none := by
    simp only [FirstSuccessRecursiveExecution.Checked.blocked, pending,
      FirstSuccessRecursiveStrategy.taskReady, FirstSuccessRecursiveExecution.scopedTypes, ready]
    rfl
  simp only [FirstSuccessRecursiveExecution.Checked.machine, RecursiveMachine.Checked.guardMachine]
  rw [unblocked]
  simp only [FirstSuccessRecursiveExecution.machine, FirstSuccessRecursiveExecution.next, pending,
    FirstSuccessRecursiveExecution.scopedTypes, entered]
  simp [freshPolymorphicPolicy, Atom.expressionType,
    Mettapedia.GSLT.Distinction.ProductiveBlocks.Transition.relabel]

namespace ScopedSelectionControls

private def incoming : Bindings := Bindings.empty.assign "t" (.symbol "Number")
private def argument : Atom := .grounded (.bool true)
private def call : Atom := .expression [.symbol "ident", argument]
private def candidates : List Atom := [(.expression [.symbol "->", .var "private", .var "private"])]
private def saved : RecursiveTasks.Configuration :=
  ⟨Space.empty, .work (.functions call Atom.undefinedType incoming 8 candidates []),
    [.filter], [(.symbol "AlreadyPublished", incoming)]⟩

/-- A fresh signature accepts Bool despite the caller's unrelated Number
assignment. The actual transition retains its filter and published prefix. -/
theorem scoped_step_preserves_caller_and_continuation :
    (FirstSuccessRecursiveExecution.Checked.machine GroundedDispatch.none
      FirstSuccessRecursiveExecution.scopedTypes).step saved =
      some (.silent {saved with control := .work (.bindingAlternatives call
        (.expression [.symbol "->", .var "private", .var "private"])
        (.var "private") 8 [incoming.assign "private" (.symbol "Bool")] [])}) :=
  fresh_polymorphic_scoped_step saved GroundedDispatch.none (.symbol "ident") argument
    "private" "Bool" incoming 5 [] [] rfl rfl (by decide) (by decide) (by decide)

/-- The same changed binding is justified independently by the scoped source
service; caller and private type variables are separate constraints. -/
theorem scoped_source_selects_the_changed_binding :
    scopedStorageTypeService.candidateScan ["t"] Space.empty call Atom.undefinedType incoming
      candidates (.success (freshPolymorphicPolicy "private")
        (incoming.assign "private" (.symbol "Bool"))) :=
  (fresh_polymorphic_scoped_selection saved (.symbol "ident") argument "private" "Bool"
    incoming 5 [] ["t"] rfl (by decide) (by decide) (by decide)).2.2

/-- Reusing the caller's schematic name makes the independent Bool call fail
under the literal policy. This is the contrasting profile, not HE's choice. -/
theorem literal_name_reuse_rejects_the_call :
    select Space.empty call Atom.undefinedType incoming 8
      [.expression [.symbol "->", .var "t", .var "t"]] =
      .exhausted [mkError call (.badArgType 1 (.var "t") (.symbol "Bool"))] false := by
  rfl

end ScopedSelectionControls

end Mettapedia.Languages.MeTTa.HE.FirstSuccessSourceApplicability

namespace Mettapedia.Languages.MeTTa.HE.FirstSuccessSourceApplicability.InvocationSignature

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Spec.Type.Presentation Spec.Type.Presentation.Exact
open Spec.Type.RuntimeRefinement
open Spec.Type.Presentation.ScopeObservation Spec.Bindings.ScopeObservation

/-- One finite call-site scope includes retained syntax, the complete call,
its demand, discovered argument types, and every incoming constraint name. -/
def avoid (live : List Atom) (call expected : Atom) (argumentTypes : List Atom)
    (bindings : Bindings) : List String :=
  TypeSubst.typeVarsList (live ++ call :: expected :: argumentTypes) ++ specBindingVars bindings

/-- Reuse the existing total injective fresh-name generator for one complete
signature. Its physical type-list position is explicit. -/
def instantiate (scope : List String) (position : Nat) (signature : Atom) : Atom :=
  renameTypeVars (instanceName scope (TypeSubst.typeVars signature).eraseDups position) signature

theorem instance_variant (scope : List String) (position : Nat) (signature : Atom) :
    TypeCandidateAlphaVariantRel scope signature (instantiate scope position signature) := by
  exact ⟨instanceName scope (TypeSubst.typeVars signature).eraseDups position,
    instanceName_injective _ _ _, rfl, fun name _ => instanceName_not_mem _ _ _ name⟩

theorem instance_avoids (scope : List String) (position : Nat) (signature : Atom)
    {name : String} (occurs : name ∈ TypeSubst.typeVars (instantiate scope position signature)) :
    name ∉ scope := by
  rw [instantiate, typeVars_renameTypeVars] at occurs
  obtain ⟨original, _, rfl⟩ := List.mem_map.mp occurs
  exact instanceName_not_mem _ _ _ original

theorem instance_protects_call (live : List Atom) (call expected : Atom)
    (argumentTypes : List Atom) (bindings : Bindings) (position : Nat) (signature : Atom)
    {name : String}
    (occurs : name ∈ TypeSubst.typeVars
      (instantiate (avoid live call expected argumentTypes bindings) position signature)) :
    name ∉ specBindingVars bindings ∧
      name ∉ TypeSubst.typeVarsList (live ++ call :: expected :: argumentTypes) := by
  have fresh := instance_avoids _ position signature occurs
  have separated : name ∉ TypeSubst.typeVarsList (live ++ call :: expected :: argumentTypes) ∧
      name ∉ specBindingVars bindings := by
    simpa only [avoid, List.mem_append, not_or] using fresh
  exact ⟨separated.2, separated.1⟩

theorem instance_unvalued (live : List Atom) (call expected : Atom)
    (argumentTypes : List Atom) (bindings : Bindings) (position : Nat) (signature : Atom)
    {name : String}
    (occurs : name ∈ TypeSubst.typeVars
      (instantiate (avoid live call expected argumentTypes bindings) position signature)) :
    bindings.classValues name = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro value member
  exact (instance_protects_call live call expected argumentTypes bindings position signature occurs).1
    (FreshPrivateMerge.class_key_support member)

/-- The same map acts on all arrow domains and its return. Freshening does not
split repeated variables into independent operands. -/
theorem instance_arrow (scope : List String) (position : Nat) (domains : List Atom)
    (returned : Atom) :
    let signature := Atom.expression (.symbol "->" :: (domains ++ [returned]))
    let rename := instanceName scope (TypeSubst.typeVars signature).eraseDups position
    instantiate scope position signature =
      .expression (.symbol "->" :: (domains.map (renameTypeVars rename) ++
        [renameTypeVars rename returned])) := by
  simp [instantiate, renameTypeVars]

theorem repeated_variable (scope : List String) (position : Nat) (name : String) :
    ∃ fresh,
      instantiate scope position (.expression [.symbol "->", .var name, .var name]) =
        .expression [.symbol "->", .var fresh, .var fresh] ∧ fresh ∉ scope := by
  let signature := Atom.expression [.symbol "->", .var name, .var name]
  let fresh := instanceName scope (TypeSubst.typeVars signature).eraseDups position name
  refine ⟨fresh, ?_, instanceName_not_mem _ _ _ name⟩
  simp only [instantiate, renameTypeVars, List.map_cons, List.map_nil, fresh, signature]

theorem instantiate_closed (scope : List String) (position : Nat) (signature : Atom)
    (closed : TypeSubst.typeVars signature = []) :
    instantiate scope position signature = signature := by
  unfold instantiate
  calc
    _ = renameTypeVars id signature := by
      apply renameTypeVars_congr_on_typeVars
      simp [closed]
    _ = signature := renameTypeVars_id signature

/-- Finite candidate-list mapping, preserving every physical position. -/
def instantiateAll (scope : List String) : Nat → List Atom → List Atom
  | _, [] => []
  | position, signature :: rest =>
      instantiate scope position signature :: instantiateAll scope (position + 1) rest

theorem instantiateAll_variants (scope : List String) (position : Nat) (signatures : List Atom) :
    OperatorAlphaVariantsRel scope signatures (instantiateAll scope position signatures) := by
  induction signatures generalizing position with
  | nil => exact .nil
  | cons signature rest ih => exact .cons (instance_variant _ _ _) (ih _)

theorem instantiateAll_length (scope : List String) (position : Nat) (signatures : List Atom) :
    (instantiateAll scope position signatures).length = signatures.length := by
  induction signatures generalizing position with
  | nil => rfl
  | cons signature rest ih => simp [instantiateAll, ih]

theorem instantiateAll_occurrence (scope : List String) (position index : Nat)
    (signatures : List Atom) :
    (instantiateAll scope position signatures)[index]? =
      signatures[index]?.map (instantiate scope (position + index)) := by
  induction signatures generalizing position index with
  | nil => simp [instantiateAll]
  | cons signature rest ih =>
      cases index with
      | zero => simp [instantiateAll]
      | succ index =>
          simpa [instantiateAll, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
            (ih (position + 1) index)

theorem instantiateAll_closed (scope : List String) (position : Nat) (signatures : List Atom)
    (closed : ∀ signature ∈ signatures, TypeSubst.typeVars signature = []) :
    instantiateAll scope position signatures = signatures := by
  induction signatures generalizing position with
  | nil => rfl
  | cons signature rest ih =>
      simp only [instantiateAll]
      rw [instantiate_closed _ _ _ (closed _ (by simp)), ih]
      intro atom member
      exact closed atom (by simp [member])

end Mettapedia.Languages.MeTTa.HE.FirstSuccessSourceApplicability.InvocationSignature
